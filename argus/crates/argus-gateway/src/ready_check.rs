use std::time::Duration;

use argus_registry::toml_types::ReadyCheck;
use tokio::net::TcpStream;
use tokio::process::Child;
use tokio::time::{Instant, sleep, timeout};
use tracing::debug;

#[derive(Debug, PartialEq, Eq)]
pub enum ReadyOutcome {
    Ready,
    Timeout,
    ProcessDied,
}

pub async fn poll_ready(
    check: &ReadyCheck,
    timeout_secs: u64,
    interval_ms: u64,
    child: &mut Child,
) -> ReadyOutcome {
    let deadline = Duration::from_secs(timeout_secs);
    let interval = Duration::from_millis(interval_ms);
    let start = Instant::now();
    let mut attempt = 0u32;

    let http_client = match check {
        ReadyCheck::Http { .. } => reqwest::Client::builder()
            .timeout(Duration::from_secs(5))
            .build()
            .ok(),
        _ => None,
    };

    loop {
        match child.try_wait() {
            Ok(Some(_)) | Err(_) => return ReadyOutcome::ProcessDied,
            Ok(None) => {}
        }

        if start.elapsed() >= deadline {
            return ReadyOutcome::Timeout;
        }

        attempt += 1;
        debug!(attempt, "polling ready check");

        if check_once(check, http_client.as_ref()).await {
            return ReadyOutcome::Ready;
        }

        sleep(interval).await;

        if start.elapsed() >= deadline {
            return ReadyOutcome::Timeout;
        }
    }
}

async fn check_once(check: &ReadyCheck, http_client: Option<&reqwest::Client>) -> bool {
    match check {
        ReadyCheck::Http { url } => check_http(url, http_client).await,
        ReadyCheck::Tcp { host, port } => check_tcp(host, *port).await,
        ReadyCheck::Command { run } => check_command(run).await,
    }
}

async fn check_http(url: &str, client: Option<&reqwest::Client>) -> bool {
    let owned;
    let client = match client {
        Some(c) => c,
        None => {
            owned = reqwest::Client::builder()
                .timeout(Duration::from_secs(5))
                .build()
                .unwrap_or_default();
            &owned
        }
    };
    client
        .get(url)
        .send()
        .await
        .is_ok_and(|r| r.status().is_success())
}

async fn check_tcp(host: &str, port: u16) -> bool {
    timeout(Duration::from_secs(2), TcpStream::connect((host, port)))
        .await
        .is_ok_and(|r| r.is_ok())
}

async fn check_command(run: &str) -> bool {
    let parts: Vec<&str> = run.split_whitespace().collect();
    if parts.is_empty() {
        return false;
    }
    tokio::process::Command::new(parts[0])
        .args(&parts[1..])
        .stdout(std::process::Stdio::null())
        .stderr(std::process::Stdio::null())
        .status()
        .await
        .is_ok_and(|s| s.success())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[tokio::test]
    async fn tcp_check_succeeds_on_open_port() {
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let port = listener.local_addr().unwrap().port();
        assert!(check_tcp("127.0.0.1", port).await);
    }

    #[tokio::test]
    async fn tcp_check_fails_on_closed_port() {
        assert!(!check_tcp("127.0.0.1", 1).await);
    }

    #[tokio::test]
    async fn command_check_succeeds_on_true() {
        assert!(check_command("true").await);
    }

    #[tokio::test]
    async fn command_check_fails_on_false() {
        assert!(!check_command("false").await);
    }

    #[tokio::test]
    async fn command_check_fails_on_empty() {
        assert!(!check_command("").await);
    }

    #[tokio::test]
    async fn poll_ready_detects_process_death() {
        let mut child = tokio::process::Command::new("false").spawn().unwrap();
        let _ = child.wait().await;
        let check = ReadyCheck::Command {
            run: "true".into(),
        };
        let result = poll_ready(&check, 5, 100, &mut child).await;
        assert_eq!(result, ReadyOutcome::ProcessDied);
    }

    #[tokio::test]
    async fn poll_ready_succeeds_on_open_port() {
        let listener = tokio::net::TcpListener::bind("127.0.0.1:0").await.unwrap();
        let port = listener.local_addr().unwrap().port();
        let mut child = tokio::process::Command::new("sleep")
            .arg("10")
            .spawn()
            .unwrap();
        let check = ReadyCheck::Tcp {
            host: "127.0.0.1".into(),
            port,
        };
        let result = poll_ready(&check, 5, 100, &mut child).await;
        assert_eq!(result, ReadyOutcome::Ready);
        let _ = child.kill().await;
    }

    #[tokio::test]
    async fn poll_ready_times_out_when_check_never_passes() {
        let mut child = tokio::process::Command::new("sleep")
            .arg("10")
            .spawn()
            .unwrap();
        let check = ReadyCheck::Command {
            run: "false".into(),
        };
        let result = poll_ready(&check, 1, 100, &mut child).await;
        assert_eq!(result, ReadyOutcome::Timeout);
        let _ = child.kill().await;
    }
}
