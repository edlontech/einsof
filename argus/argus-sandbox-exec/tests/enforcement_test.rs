use std::path::PathBuf;
use std::process::Command;

use argus_sandbox::{NetPolicy, SandboxProfile};

fn wrapper_binary() -> PathBuf {
    let path = PathBuf::from(env!("CARGO_BIN_EXE_argus-sandbox-exec"));
    assert!(path.exists(), "wrapper binary not found at {}", path.display());
    path
}

fn write_profile(profile: &SandboxProfile) -> PathBuf {
    let dir = std::env::temp_dir();
    let path = dir.join(format!(
        "test-profile-{}-{}.json",
        std::process::id(),
        std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .unwrap()
            .as_nanos()
    ));
    std::fs::write(&path, serde_json::to_string(profile).unwrap()).unwrap();
    path
}

#[test]
fn wrapper_rejects_missing_profile_arg() {
    let output = Command::new(wrapper_binary())
        .arg("--")
        .arg("echo")
        .arg("hello")
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("--profile is required"));
}

#[test]
fn wrapper_rejects_missing_command() {
    let profile = SandboxProfile::default();
    let path = write_profile(&profile);
    let output = Command::new(wrapper_binary())
        .arg("--profile")
        .arg(path.to_str().unwrap())
        .arg("--")
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("no command specified"));
    std::fs::remove_file(&path).ok();
}

#[test]
fn wrapper_rejects_unknown_argument() {
    let output = Command::new(wrapper_binary())
        .arg("--unknown")
        .output()
        .unwrap();
    assert!(!output.status.success());
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(stderr.contains("unknown argument"));
}

#[test]
fn wrapper_reads_and_deletes_profile() {
    let profile = SandboxProfile::default();
    let path = write_profile(&profile);
    assert!(path.exists());

    let _ = Command::new(wrapper_binary())
        .arg("--profile")
        .arg(path.to_str().unwrap())
        .arg("--")
        .arg("/bin/echo")
        .arg("test")
        .output();

    assert!(!path.exists(), "profile should be deleted after reading");
}

#[cfg(target_os = "macos")]
mod macos_tests {
    use serial_test::serial;

    use super::*;

    #[test]
    #[serial]
    fn seatbelt_allows_permitted_read() {
        let profile = SandboxProfile {
            allowed_read_paths: vec![
                PathBuf::from("/usr/lib"),
                PathBuf::from("/usr/share"),
                PathBuf::from("/dev/null"),
                PathBuf::from("/bin"),
                PathBuf::from("/usr/bin"),
                PathBuf::from("/private/var"),
                PathBuf::from("/System/Library"),
            ],
            net_policy: NetPolicy::Blocked,
            ..Default::default()
        };
        let path = write_profile(&profile);
        let output = Command::new(wrapper_binary())
            .arg("--profile")
            .arg(path.to_str().unwrap())
            .arg("--")
            .arg("/bin/cat")
            .arg("/dev/null")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "expected success, stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    #[serial]
    fn seatbelt_blocks_network_when_blocked() {
        let profile = SandboxProfile {
            allowed_read_paths: vec![
                PathBuf::from("/usr"),
                PathBuf::from("/bin"),
                PathBuf::from("/dev"),
                PathBuf::from("/private"),
                PathBuf::from("/etc"),
            ],
            net_policy: NetPolicy::Blocked,
            ..Default::default()
        };
        let path = write_profile(&profile);
        let output = Command::new(wrapper_binary())
            .arg("--profile")
            .arg(path.to_str().unwrap())
            .arg("--")
            .arg("/usr/bin/curl")
            .arg("--max-time")
            .arg("2")
            .arg("https://httpbin.org/get")
            .output()
            .unwrap();
        assert!(
            !output.status.success(),
            "network should be blocked, stdout: {}",
            String::from_utf8_lossy(&output.stdout)
        );
    }

    #[test]
    #[serial]
    #[ignore = "requires network access, may be flaky in CI"]
    fn seatbelt_allows_egress_only() {
        let profile = SandboxProfile {
            allowed_read_paths: vec![
                PathBuf::from("/usr"),
                PathBuf::from("/bin"),
                PathBuf::from("/dev"),
                PathBuf::from("/private"),
                PathBuf::from("/etc"),
                PathBuf::from("/System"),
                PathBuf::from("/Library"),
            ],
            net_policy: NetPolicy::EgressOnly,
            ..Default::default()
        };
        let path = write_profile(&profile);
        let output = Command::new(wrapper_binary())
            .arg("--profile")
            .arg(path.to_str().unwrap())
            .arg("--")
            .arg("/usr/bin/curl")
            .arg("--max-time")
            .arg("5")
            .arg("https://httpbin.org/get")
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "egress should be allowed, stderr: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }

    #[test]
    #[serial]
    fn seatbelt_blocks_unpermitted_read() {
        let profile = SandboxProfile {
            allowed_read_paths: vec![
                PathBuf::from("/usr/lib"),
                PathBuf::from("/bin"),
                PathBuf::from("/usr/bin"),
            ],
            net_policy: NetPolicy::Blocked,
            ..Default::default()
        };
        let path = write_profile(&profile);
        let output = Command::new(wrapper_binary())
            .arg("--profile")
            .arg(path.to_str().unwrap())
            .arg("--")
            .arg("/bin/cat")
            .arg("/etc/passwd")
            .output()
            .unwrap();
        assert!(
            !output.status.success(),
            "reading /etc/passwd should be blocked"
        );
    }
}

#[cfg(target_os = "linux")]
mod linux_tests {
    // Linux Landlock enforcement tests require a kernel with Landlock ABI v5.
    // These will be implemented when CI has a suitable Linux environment.
}
