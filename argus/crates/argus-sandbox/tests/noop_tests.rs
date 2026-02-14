#![cfg(feature = "runtime")]

use argus_sandbox::{NetPolicy, NoopSandbox, SandboxProfile, SandboxProvider};
use tokio::process::Command;

#[test]
fn noop_sandbox_returns_command_unchanged() {
    let sandbox = NoopSandbox;
    let cmd = Command::new("echo");
    let profile = SandboxProfile::default();

    let result = sandbox.prepare_command(cmd, &profile);
    assert!(result.is_ok());
}

#[test]
fn default_profile_denies_everything() {
    let profile = SandboxProfile::default();
    assert_eq!(profile.net_policy, NetPolicy::Blocked);
    assert!(profile.allowed_read_paths.is_empty());
    assert!(profile.allowed_write_paths.is_empty());
    assert!(profile.resolved_env.is_empty());
}
