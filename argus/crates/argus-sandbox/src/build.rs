use std::collections::HashMap;
use std::path::PathBuf;

use crate::sensitive::validate_path_not_sensitive;
use crate::{NetPolicy, SandboxError, SandboxProfile};

const SYSTEM_READ_ESSENTIALS: &[&str] = &[
    "/usr/lib",
    "/usr/share",
    "/dev/null",
    "/dev/urandom",
    "/etc/resolv.conf",
    "/etc/ssl/certs",
    "/etc/hosts",
];

#[cfg(target_os = "macos")]
const PLATFORM_READ_ESSENTIALS: &[&str] = &[
    "/usr/local/lib",
    "/opt/homebrew",
    "/Library/Frameworks",
    "/System/Library/Frameworks",
    "/private/etc/ssl",
];

#[cfg(target_os = "linux")]
const PLATFORM_READ_ESSENTIALS: &[&str] = &[
    "/lib",
    "/lib64",
    "/usr/local/lib",
    "/etc/ld.so.cache",
    "/etc/ssl/certs",
    "/usr/share/ca-certificates",
];

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
const PLATFORM_READ_ESSENTIALS: &[&str] = &[];

pub struct ProfileBuilder {
    extra_read: Vec<String>,
    extra_write: Vec<String>,
    resolved_env: HashMap<String, String>,
    net_policy: NetPolicy,
    command_path: Option<PathBuf>,
}

impl ProfileBuilder {
    pub fn new() -> Self {
        Self {
            extra_read: Vec::new(),
            extra_write: Vec::new(),
            resolved_env: HashMap::new(),
            net_policy: NetPolicy::Blocked,
            command_path: None,
        }
    }

    pub fn extra_read(mut self, paths: Vec<String>) -> Self {
        self.extra_read = paths;
        self
    }

    pub fn extra_write(mut self, paths: Vec<String>) -> Self {
        self.extra_write = paths;
        self
    }

    pub fn resolved_env(mut self, vars: HashMap<String, String>) -> Self {
        self.resolved_env = vars;
        self
    }

    pub fn net_policy(mut self, policy: NetPolicy) -> Self {
        self.net_policy = policy;
        self
    }

    pub fn command_path(mut self, path: PathBuf) -> Self {
        self.command_path = Some(path);
        self
    }

    pub fn build(self) -> Result<SandboxProfile, SandboxError> {
        let mut read_paths: Vec<PathBuf> = SYSTEM_READ_ESSENTIALS
            .iter()
            .chain(PLATFORM_READ_ESSENTIALS.iter())
            .map(PathBuf::from)
            .collect();

        if let Some(cmd) = &self.command_path {
            read_paths.push(cmd.clone());
        }

        for raw in &self.extra_read {
            let expanded = expand_env_vars(raw);
            let path = PathBuf::from(&expanded);
            validate_path_not_sensitive(&path)?;
            read_paths.push(path);
        }

        let mut write_paths = Vec::new();
        for raw in &self.extra_write {
            let expanded = expand_env_vars(raw);
            let path = PathBuf::from(&expanded);
            validate_path_not_sensitive(&path)?;
            write_paths.push(path);
        }

        Ok(SandboxProfile {
            allowed_read_paths: read_paths,
            allowed_write_paths: write_paths,
            net_policy: self.net_policy,
            resolved_env: self.resolved_env,
        })
    }
}

impl Default for ProfileBuilder {
    fn default() -> Self {
        Self::new()
    }
}

fn expand_env_vars(s: &str) -> String {
    let home = std::env::var("HOME").ok();
    let mut result = s.to_string();
    if let Some(ref home) = home {
        result = result.replace("$HOME", home);
    }
    if let Ok(tmpdir) = std::env::var("TMPDIR") {
        result = result.replace("$TMPDIR", &tmpdir);
    }
    if let Some(ref home) = home
        && result.starts_with("~/")
    {
        result = format!("{}{}", home, &result[1..]);
    }
    result
}

#[cfg(test)]
mod tests {
    use std::path::Path;

    use super::*;

    #[test]
    fn default_builder_produces_deny_all_with_essentials() {
        let profile = ProfileBuilder::new().build().unwrap();
        assert_eq!(profile.net_policy, NetPolicy::Blocked);
        assert!(profile.allowed_write_paths.is_empty());
        assert!(profile.resolved_env.is_empty());
        assert!(profile.allowed_read_paths.iter().any(|p| p == Path::new("/dev/null")));
        assert!(profile.allowed_read_paths.iter().any(|p| p == Path::new("/usr/lib")));
    }

    #[test]
    fn builder_adds_extra_read_paths() {
        let profile = ProfileBuilder::new()
            .extra_read(vec!["/tmp/data".into()])
            .build()
            .unwrap();
        assert!(profile.allowed_read_paths.iter().any(|p| p == Path::new("/tmp/data")));
    }

    #[test]
    fn builder_rejects_sensitive_read_path() {
        let home = std::env::var("HOME").unwrap_or_else(|_| "/root".into());
        let result = ProfileBuilder::new()
            .extra_read(vec![format!("{home}/.ssh")])
            .build();
        assert!(result.is_err());
    }

    #[test]
    fn builder_rejects_sensitive_write_path() {
        let home = std::env::var("HOME").unwrap_or_else(|_| "/root".into());
        let result = ProfileBuilder::new()
            .extra_write(vec![format!("{home}/.aws")])
            .build();
        assert!(result.is_err());
    }

    #[test]
    fn builder_expands_home_variable() {
        let profile = ProfileBuilder::new()
            .extra_read(vec!["$HOME/projects".into()])
            .build()
            .unwrap();
        let home = std::env::var("HOME").unwrap_or_else(|_| "/root".into());
        let expected = PathBuf::from(format!("{home}/projects"));
        assert!(profile.allowed_read_paths.contains(&expected));
    }

    #[test]
    fn builder_sets_net_policy() {
        let profile = ProfileBuilder::new()
            .net_policy(NetPolicy::EgressWithDomains(vec!["api.github.com".into()]))
            .build()
            .unwrap();
        assert_eq!(
            profile.net_policy,
            NetPolicy::EgressWithDomains(vec!["api.github.com".into()])
        );
    }

    #[test]
    fn builder_includes_command_path() {
        let profile = ProfileBuilder::new()
            .command_path(PathBuf::from("/usr/bin/node"))
            .build()
            .unwrap();
        assert!(profile.allowed_read_paths.iter().any(|p| p == Path::new("/usr/bin/node")));
    }

    #[test]
    fn builder_sets_resolved_env() {
        let mut vars = HashMap::new();
        vars.insert("API_KEY".into(), "secret123".into());
        vars.insert("PORT".into(), "8080".into());

        let profile = ProfileBuilder::new()
            .resolved_env(vars)
            .build()
            .unwrap();
        assert_eq!(profile.resolved_env.len(), 2);
        assert_eq!(profile.resolved_env["API_KEY"], "secret123");
    }
}
