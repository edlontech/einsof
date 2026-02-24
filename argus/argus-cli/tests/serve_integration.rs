use std::fs;
use std::net::TcpListener;
use std::time::Duration;

use tempfile::TempDir;

fn find_free_port() -> u16 {
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    listener.local_addr().unwrap().port()
}

fn cargo_bin_path() -> std::path::PathBuf {
    std::env::current_exe()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("argus")
}

struct TestDaemon {
    grpc_port: u16,
    proxy_port: u16,
    child: Option<std::process::Child>,
    _tmp: TempDir,
}

impl TestDaemon {
    fn start(grpc_enabled: bool, proxy_enabled: bool) -> Self {
        let tmp = TempDir::new().unwrap();
        let grpc_port = find_free_port();
        let proxy_port = find_free_port();

        let registry_dir = tmp.path().join("registry");
        fs::create_dir_all(&registry_dir).unwrap();

        let policy_dir = tmp.path().join("policies");
        fs::create_dir_all(&policy_dir).unwrap();
        fs::write(
            policy_dir.join("default.cedar"),
            r#"permit(principal, action, resource);"#,
        )
        .unwrap();

        let config_content = format!(
            "[server]\n\
             registry_path = \"{registry}\"\n\
             policy_path = \"{policy}\"\n\
             log_level = \"warn\"\n\
             shutdown_timeout_secs = 2\n\
             \n\
             [grpc]\n\
             enabled = {grpc_enabled}\n\
             address = \"127.0.0.1:{grpc_port}\"\n\
             \n\
             [proxy]\n\
             enabled = {proxy_enabled}\n\
             address = \"127.0.0.1:{proxy_port}\"\n\
             max_tool_rounds = 5\n",
            registry = registry_dir.display(),
            policy = policy_dir.display(),
        );

        let config_path = tmp.path().join("argus.toml");
        fs::write(&config_path, config_content).unwrap();

        let child = std::process::Command::new(cargo_bin_path())
            .arg("serve")
            .arg("--config")
            .arg(&config_path)
            .stdout(std::process::Stdio::piped())
            .stderr(std::process::Stdio::piped())
            .spawn()
            .expect("failed to spawn argus daemon");

        TestDaemon {
            grpc_port,
            proxy_port,
            child: Some(child),
            _tmp: tmp,
        }
    }

    fn proxy_url(&self, path: &str) -> String {
        format!("http://127.0.0.1:{}{}", self.proxy_port, path)
    }

    fn shutdown(&mut self) {
        if let Some(mut child) = self.child.take() {
            let _ = child.kill();
            let _ = child.wait();
        }
    }
}

impl Drop for TestDaemon {
    fn drop(&mut self) {
        self.shutdown();
    }
}

async fn wait_for_port(port: u16, max_wait: Duration) -> bool {
    let start = std::time::Instant::now();
    while start.elapsed() < max_wait {
        if tokio::net::TcpStream::connect(format!("127.0.0.1:{port}"))
            .await
            .is_ok()
        {
            return true;
        }
        tokio::time::sleep(Duration::from_millis(50)).await;
    }
    false
}

fn port_is_closed(port: u16) -> bool {
    TcpListener::bind(format!("127.0.0.1:{port}")).is_ok()
}

#[tokio::test]
async fn daemon_starts_and_binds_grpc_port() {
    let mut daemon = TestDaemon::start(true, false);
    assert!(
        wait_for_port(daemon.grpc_port, Duration::from_secs(10)).await,
        "gRPC port did not open"
    );
    daemon.shutdown();
}

#[tokio::test]
async fn daemon_starts_and_binds_proxy_port() {
    let mut daemon = TestDaemon::start(false, true);
    assert!(
        wait_for_port(daemon.proxy_port, Duration::from_secs(10)).await,
        "proxy port did not open"
    );
    daemon.shutdown();
}

#[tokio::test]
async fn daemon_starts_both_listeners() {
    let mut daemon = TestDaemon::start(true, true);
    let grpc_ready = wait_for_port(daemon.grpc_port, Duration::from_secs(10));
    let proxy_ready = wait_for_port(daemon.proxy_port, Duration::from_secs(10));
    let (grpc_ok, proxy_ok) = tokio::join!(grpc_ready, proxy_ready);
    assert!(grpc_ok, "gRPC port did not open");
    assert!(proxy_ok, "proxy port did not open");
    daemon.shutdown();
}

#[tokio::test]
async fn daemon_shuts_down_cleanly() {
    let mut daemon = TestDaemon::start(true, false);
    assert!(wait_for_port(daemon.grpc_port, Duration::from_secs(10)).await);
    let port = daemon.grpc_port;
    daemon.shutdown();
    tokio::time::sleep(Duration::from_millis(200)).await;
    assert!(port_is_closed(port), "port should be freed after shutdown");
}

#[tokio::test]
async fn proxy_returns_401_without_agent_header() {
    let mut daemon = TestDaemon::start(false, true);
    assert!(wait_for_port(daemon.proxy_port, Duration::from_secs(10)).await);

    let client = reqwest::Client::new();
    let resp = client
        .post(daemon.proxy_url("/v1/chat/completions"))
        .json(&serde_json::json!({"model": "test", "messages": []}))
        .send()
        .await
        .unwrap();

    assert_eq!(resp.status(), 401);
    daemon.shutdown();
}

#[tokio::test]
async fn proxy_returns_404_for_unknown_path() {
    let mut daemon = TestDaemon::start(false, true);
    assert!(wait_for_port(daemon.proxy_port, Duration::from_secs(10)).await);

    let client = reqwest::Client::new();
    let resp = client
        .post(daemon.proxy_url("/v2/unknown"))
        .json(&serde_json::json!({}))
        .send()
        .await
        .unwrap();

    assert_eq!(resp.status(), 404);
    daemon.shutdown();
}

#[tokio::test]
async fn daemon_starts_with_os_sandbox_initialization() {
    // Validates that OsSandbox::new() (or NoopSandbox fallback) doesn't
    // prevent daemon startup. The sandbox provider is initialized inside
    // run_serve() before binding listeners.
    let mut daemon = TestDaemon::start(true, false);
    assert!(
        wait_for_port(daemon.grpc_port, Duration::from_secs(10)).await,
        "daemon should start with sandbox provider initialized"
    );
    daemon.shutdown();
}

#[tokio::test]
async fn invalid_config_exits_nonzero() {
    let tmp = TempDir::new().unwrap();
    let config_path = tmp.path().join("bad.toml");
    fs::write(&config_path, "not valid toml [[[").unwrap();

    let output = std::process::Command::new(cargo_bin_path())
        .arg("serve")
        .arg("--config")
        .arg(&config_path)
        .output()
        .expect("failed to run argus");

    assert!(!output.status.success());
}
