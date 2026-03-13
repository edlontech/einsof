use std::path::PathBuf;

use tokio::process::Command;

use crate::{SandboxError, SandboxProfile, SandboxProvider};

pub struct OsSandbox {
    wrapper_path: PathBuf,
}

impl OsSandbox {
    pub fn new() -> Result<Self, SandboxError> {
        let wrapper_path = find_wrapper()?;
        Ok(Self { wrapper_path })
    }

    fn write_profile(&self, profile: &SandboxProfile) -> Result<PathBuf, SandboxError> {
        use std::fs::Permissions;
        use std::io::Write;
        use std::os::unix::fs::PermissionsExt;

        let mut file = tempfile::Builder::new()
            .prefix("argus-sandbox-")
            .suffix(".json")
            .permissions(Permissions::from_mode(0o600))
            .tempfile()
            .map_err(SandboxError::ProfileWriteFailed)?;

        let json = serde_json::to_vec(profile).map_err(|e| SandboxError::ProfileError {
            reason: e.to_string(),
        })?;
        file.write_all(&json)
            .map_err(SandboxError::ProfileWriteFailed)?;

        let path = file
            .into_temp_path()
            .keep()
            .map_err(|e| SandboxError::ProfileWriteFailed(e.error))?;
        Ok(path)
    }
}

impl SandboxProvider for OsSandbox {
    fn prepare_command(
        &self,
        command: Command,
        profile: &SandboxProfile,
    ) -> Result<Command, SandboxError> {
        let profile_path = self.write_profile(profile)?;

        let inner = command.as_std();
        let program = inner.get_program().to_os_string();
        let args: Vec<_> = inner.get_args().map(|a| a.to_os_string()).collect();

        let mut wrapped = Command::new(&self.wrapper_path);
        wrapped.env_clear();
        wrapped.arg("--profile");
        wrapped.arg(&profile_path);
        wrapped.arg("--");
        wrapped.arg(&program);
        wrapped.args(&args);

        for (k, v) in &profile.resolved_env {
            wrapped.env(k, v);
        }

        Ok(wrapped)
    }
}

fn find_wrapper() -> Result<PathBuf, SandboxError> {
    if let Ok(exe) = std::env::current_exe()
        && let Some(dir) = exe.parent()
    {
        let candidate = dir.join("argus-sandbox-exec");
        if candidate.is_file() {
            return Ok(candidate);
        }
    }

    if let Ok(output) = std::process::Command::new("which")
        .arg("argus-sandbox-exec")
        .output()
        && output.status.success()
    {
        let path = String::from_utf8_lossy(&output.stdout).trim().to_string();
        if !path.is_empty() {
            return Ok(PathBuf::from(path));
        }
    }

    Err(SandboxError::WrapperNotFound {
        reason: "argus-sandbox-exec not found next to binary or in $PATH".into(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::NetPolicy;

    #[test]
    fn write_profile_creates_file_with_valid_json() {
        let sandbox = OsSandbox {
            wrapper_path: PathBuf::from("/usr/bin/true"),
        };
        let mut resolved = std::collections::HashMap::new();
        resolved.insert("HOME".into(), "/home/test".into());
        let profile = SandboxProfile {
            allowed_read_paths: vec![PathBuf::from("/tmp")],
            allowed_write_paths: vec![],
            net_policy: NetPolicy::Blocked,
            resolved_env: resolved,
        };
        let path = sandbox.write_profile(&profile).unwrap();
        let contents = std::fs::read_to_string(&path).unwrap();
        let parsed: SandboxProfile = serde_json::from_str(&contents).unwrap();
        assert_eq!(parsed.allowed_read_paths, vec![PathBuf::from("/tmp")]);
        std::fs::remove_file(path).ok();
    }

    #[test]
    fn prepare_command_wraps_with_sandbox_exec() {
        let sandbox = OsSandbox {
            wrapper_path: PathBuf::from("/usr/bin/argus-sandbox-exec"),
        };
        let mut original = Command::new("node");
        original.arg("server.js");
        original.env("API_KEY", "secret");

        let profile = SandboxProfile::default();
        let wrapped = sandbox.prepare_command(original, &profile).unwrap();

        let std_cmd = wrapped.as_std();
        assert_eq!(
            std_cmd.get_program().to_str().unwrap(),
            "/usr/bin/argus-sandbox-exec"
        );
        let args: Vec<_> = std_cmd.get_args().map(|a| a.to_str().unwrap()).collect();
        assert_eq!(args[0], "--profile");
        assert!(args[1].contains("argus-sandbox-"));
        assert_eq!(args[2], "--");
        assert_eq!(args[3], "node");
        assert_eq!(args[4], "server.js");

        std::fs::remove_file(args[1]).ok();
    }

    #[test]
    fn prepare_command_clears_original_env_vars() {
        let sandbox = OsSandbox {
            wrapper_path: PathBuf::from("/usr/bin/argus-sandbox-exec"),
        };
        let mut original = Command::new("node");
        original.arg("server.js");
        original.env("LEAKED_SECRET", "should-not-appear");

        let profile = SandboxProfile::default();
        let wrapped = sandbox.prepare_command(original, &profile).unwrap();

        let std_cmd = wrapped.as_std();
        let has_leak = std_cmd
            .get_envs()
            .any(|(k, _)| k.to_str() == Some("LEAKED_SECRET"));
        assert!(!has_leak, "env vars from original command should not leak");

        let args: Vec<_> = std_cmd.get_args().map(|a| a.to_str().unwrap()).collect();
        std::fs::remove_file(args[1]).ok();
    }

    #[test]
    fn prepare_command_injects_resolved_env() {
        let sandbox = OsSandbox {
            wrapper_path: PathBuf::from("/usr/bin/argus-sandbox-exec"),
        };
        let original = Command::new("node");

        let mut resolved = std::collections::HashMap::new();
        resolved.insert("INJECTED_VAR".to_string(), "injected_value".to_string());

        let profile = SandboxProfile {
            resolved_env: resolved,
            ..Default::default()
        };
        let wrapped = sandbox.prepare_command(original, &profile).unwrap();

        let std_cmd = wrapped.as_std();
        let has_injected = std_cmd.get_envs().any(|(k, v)| {
            k.to_str() == Some("INJECTED_VAR")
                && v.and_then(|v| v.to_str()) == Some("injected_value")
        });
        assert!(has_injected, "resolved_env values should be injected");

        let args: Vec<_> = std_cmd.get_args().map(|a| a.to_str().unwrap()).collect();
        std::fs::remove_file(args[1]).ok();
    }
}
