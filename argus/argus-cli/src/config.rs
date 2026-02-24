use std::collections::HashMap;
use std::path::Path;

use anyhow::Context;
use serde::Deserialize;

#[derive(Debug, Deserialize)]
pub struct DaemonConfig {
    pub server: ServerConfig,
    pub grpc: Option<GrpcConfig>,
    pub proxy: Option<ProxyCfg>,
}

#[derive(Debug, Deserialize)]
pub struct ServerConfig {
    pub registry_path: String,
    pub policy_path: String,
    #[serde(default = "default_log_level")]
    pub log_level: String,
    #[serde(default = "default_shutdown_timeout")]
    pub shutdown_timeout_secs: u64,
}

#[derive(Debug, Deserialize)]
pub struct GrpcConfig {
    #[serde(default = "default_true")]
    pub enabled: bool,
    #[serde(default = "default_grpc_address")]
    pub address: String,
}

#[derive(Debug, Deserialize)]
pub struct ProxyCfg {
    #[serde(default = "default_true")]
    pub enabled: bool,
    #[serde(default = "default_proxy_address")]
    pub address: String,
    #[serde(default = "default_max_tool_rounds")]
    pub max_tool_rounds: usize,
    #[serde(default)]
    pub upstreams: HashMap<String, UpstreamEntry>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum UpstreamFormat {
    Openai,
    Anthropic,
}

#[derive(Debug, Clone, Deserialize)]
pub struct UpstreamEntry {
    pub url: String,
    pub format: UpstreamFormat,
    #[serde(default)]
    #[allow(dead_code)]
    pub api_key_env: Option<String>,
}

fn default_log_level() -> String {
    "info".into()
}

fn default_shutdown_timeout() -> u64 {
    5
}

fn default_true() -> bool {
    true
}

fn default_grpc_address() -> String {
    "127.0.0.1:9090".into()
}

fn default_proxy_address() -> String {
    "127.0.0.1:8080".into()
}

fn default_max_tool_rounds() -> usize {
    25
}

impl DaemonConfig {
    pub fn load(path: &Path) -> anyhow::Result<Self> {
        let content = std::fs::read_to_string(path)
            .with_context(|| format!("failed to read config: {}", path.display()))?;
        let config: Self = toml::from_str(&content)
            .with_context(|| format!("failed to parse config: {}", path.display()))?;
        config.validate()?;
        Ok(config)
    }

    fn validate(&self) -> anyhow::Result<()> {
        let grpc_on = self.grpc.as_ref().is_some_and(|g| g.enabled);
        let proxy_on = self.proxy.as_ref().is_some_and(|p| p.enabled);
        anyhow::ensure!(
            grpc_on || proxy_on,
            "at least one listener (grpc or proxy) must be enabled"
        );
        Ok(())
    }
}

pub fn expand_tilde(s: &str) -> String {
    if let Some(rest) = s.strip_prefix("~/")
        && let Ok(home) = std::env::var("HOME")
    {
        return format!("{home}/{rest}");
    }
    s.to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn write_config(dir: &Path, content: &str) -> std::path::PathBuf {
        let path = dir.join("argus.toml");
        fs::write(&path, content).unwrap();
        path
    }

    #[test]
    fn parses_full_config() {
        let tmp = tempfile::tempdir().unwrap();
        let path = write_config(
            tmp.path(),
            r#"
[server]
registry_path = "/tmp/registry"
policy_path = "/tmp/policies"

[grpc]
enabled = true
address = "127.0.0.1:9090"

[proxy]
enabled = true
address = "127.0.0.1:8080"
max_tool_rounds = 30

[proxy.upstreams.openai]
url = "https://api.openai.com"
format = "openai"
api_key_env = "OPENAI_API_KEY"

[proxy.upstreams.anthropic]
url = "https://api.anthropic.com"
format = "anthropic"
"#,
        );
        let config = DaemonConfig::load(&path).unwrap();
        assert_eq!(config.server.registry_path, "/tmp/registry");
        assert_eq!(config.server.policy_path, "/tmp/policies");
        assert!(config.grpc.as_ref().unwrap().enabled);
        let proxy = config.proxy.as_ref().unwrap();
        assert_eq!(proxy.max_tool_rounds, 30);
        assert_eq!(proxy.upstreams.len(), 2);
    }

    #[test]
    fn applies_defaults() {
        let tmp = tempfile::tempdir().unwrap();
        let path = write_config(
            tmp.path(),
            r#"
[server]
registry_path = "/tmp/reg"
policy_path = "/tmp/pol"

[grpc]
"#,
        );
        let config = DaemonConfig::load(&path).unwrap();
        assert_eq!(config.server.log_level, "info");
        assert_eq!(config.server.shutdown_timeout_secs, 5);
        let grpc = config.grpc.as_ref().unwrap();
        assert!(grpc.enabled);
        assert_eq!(grpc.address, "127.0.0.1:9090");
    }

    #[test]
    fn validates_no_listeners_enabled() {
        let tmp = tempfile::tempdir().unwrap();
        let path = write_config(
            tmp.path(),
            r#"
[server]
registry_path = "/tmp/reg"
policy_path = "/tmp/pol"

[grpc]
enabled = false

[proxy]
enabled = false
"#,
        );
        let result = DaemonConfig::load(&path);
        assert!(result.is_err());
        let msg = result.unwrap_err().to_string();
        assert!(msg.contains("at least one listener"));
    }

    #[test]
    fn validates_no_listener_sections() {
        let tmp = tempfile::tempdir().unwrap();
        let path = write_config(
            tmp.path(),
            r#"
[server]
registry_path = "/tmp/reg"
policy_path = "/tmp/pol"
"#,
        );
        let result = DaemonConfig::load(&path);
        assert!(result.is_err());
    }

    #[test]
    fn grpc_only_config_valid() {
        let tmp = tempfile::tempdir().unwrap();
        let path = write_config(
            tmp.path(),
            r#"
[server]
registry_path = "/tmp/reg"
policy_path = "/tmp/pol"

[grpc]
enabled = true
"#,
        );
        let config = DaemonConfig::load(&path).unwrap();
        assert!(config.grpc.is_some());
        assert!(config.proxy.is_none());
    }

    #[test]
    fn proxy_only_config_valid() {
        let tmp = tempfile::tempdir().unwrap();
        let path = write_config(
            tmp.path(),
            r#"
[server]
registry_path = "/tmp/reg"
policy_path = "/tmp/pol"

[proxy]
enabled = true

[proxy.upstreams.openai]
url = "https://api.openai.com"
format = "openai"
"#,
        );
        let config = DaemonConfig::load(&path).unwrap();
        assert!(config.grpc.is_none());
        assert!(config.proxy.is_some());
    }

    #[test]
    fn invalid_toml_returns_error() {
        let tmp = tempfile::tempdir().unwrap();
        let path = write_config(tmp.path(), "this is not valid toml [[[");
        assert!(DaemonConfig::load(&path).is_err());
    }

    #[test]
    fn missing_file_returns_error() {
        assert!(DaemonConfig::load(Path::new("/nonexistent/argus.toml")).is_err());
    }

    #[test]
    fn expand_tilde_with_home() {
        let result = expand_tilde("~/foo/bar");
        assert!(!result.starts_with('~'));
        assert!(result.ends_with("foo/bar"));
    }

    #[test]
    fn expand_tilde_no_tilde() {
        assert_eq!(expand_tilde("/absolute/path"), "/absolute/path");
    }
}
