use serde::{Deserialize, Serialize};
use std::collections::{BTreeSet, HashMap};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct McpMetadata {
    pub name: String,
    pub description: String,
    pub repository: Option<String>,
    pub source: String,
    pub integrity: String,
    pub capabilities: Vec<String>,
    pub schema_hash: Option<String>,
    #[serde(default)]
    pub pinned_ref: Option<String>,
    #[serde(default)]
    pub track: Option<bool>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "lowercase")]
pub enum InstallConfig {
    Npm {
        package: String,
        version: String,
    },
    Pip {
        package: String,
        version: String,
        python_version: Option<String>,
    },
    Cargo {
        #[serde(rename = "crate")]
        crate_name: String,
        version: String,
    },
    Docker {
        image: String,
        tag: String,
        ports: Option<Vec<u16>>,
    },
    Binary {
        url: String,
        checksum: String,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InstallEnvVar {
    pub required: bool,
    pub description: String,
    #[serde(default)]
    pub default: Option<String>,
}

#[derive(Debug, Clone, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SandboxNetPolicy {
    Blocked,
    Egress,
    EgressDomains(Vec<String>),
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SandboxConfig {
    #[serde(default)]
    pub extra_read: Vec<String>,
    #[serde(default)]
    pub extra_write: Vec<String>,
    #[serde(default)]
    pub require_sandbox: bool,
    #[serde(default)]
    pub net_policy: Option<SandboxNetPolicy>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct McpEntry {
    pub metadata: McpMetadata,
    pub install: InstallConfig,
    #[serde(default)]
    pub env: HashMap<String, InstallEnvVar>,
    #[serde(default)]
    pub args: McpArgs,
    #[serde(default)]
    pub sandbox: Option<SandboxConfig>,
    #[serde(default, rename = "sidecar")]
    pub sidecars: Vec<SidecarEntry>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct McpArgs {
    #[serde(default)]
    pub default: Vec<String>,
}

fn default_ready_timeout() -> u64 {
    30
}

fn default_ready_interval() -> u64 {
    500
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SidecarEntry {
    pub name: String,
    pub command: String,
    #[serde(default)]
    pub args: Vec<String>,
    pub lifecycle: SidecarLifecycle,
    #[serde(default)]
    pub ready_check: Option<ReadyCheck>,
    #[serde(default = "default_ready_timeout")]
    pub ready_timeout: u64,
    #[serde(default = "default_ready_interval")]
    pub ready_interval: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "lowercase")]
pub enum SidecarLifecycle {
    Daemon,
    Init,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "lowercase")]
pub enum ReadyCheck {
    Http { url: String },
    Tcp { host: String, port: u16 },
    Command { run: String },
}

#[derive(Debug, thiserror::Error)]
pub enum SidecarValidationError {
    #[error("daemon sidecar '{name}' must have a ready_check")]
    DaemonMissingReadyCheck { name: String },
    #[error("init sidecar '{name}' must not have a ready_check")]
    InitWithReadyCheck { name: String },
    #[error("duplicate sidecar name '{name}'")]
    DuplicateName { name: String },
}

pub fn validate_sidecars(sidecars: &[SidecarEntry]) -> Result<(), SidecarValidationError> {
    let mut seen = BTreeSet::new();
    for s in sidecars {
        if !seen.insert(&s.name) {
            return Err(SidecarValidationError::DuplicateName {
                name: s.name.clone(),
            });
        }
        match s.lifecycle {
            SidecarLifecycle::Daemon if s.ready_check.is_none() => {
                return Err(SidecarValidationError::DaemonMissingReadyCheck {
                    name: s.name.clone(),
                });
            }
            SidecarLifecycle::Init if s.ready_check.is_some() => {
                return Err(SidecarValidationError::InitWithReadyCheck {
                    name: s.name.clone(),
                });
            }
            _ => {}
        }
    }
    Ok(())
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SkillMetadata {
    pub name: String,
    pub description: String,
    pub tools_used: Vec<String>,
    #[serde(default)]
    pub capabilities: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SkillEntry {
    pub metadata: SkillMetadata,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CapabilityTaxonomy {
    pub capabilities: HashMap<String, CapabilityInfo>,
    pub integrity_levels: HashMap<String, IntegrityInfo>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CapabilityInfo {
    pub description: String,
    pub scope_type: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct IntegrityInfo {
    pub description: String,
    pub level: u8,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_npm_mcp_entry() {
        let toml_str = r#"
[metadata]
name = "filesystem-server"
description = "Provides filesystem access tools"
repository = "https://github.com/modelcontextprotocol/servers"
source = "community"
integrity = "observed"
capabilities = ["filesystem:read(/tmp/**)", "filesystem:write(./project/**)"]

[install]
type = "npm"
package = "@modelcontextprotocol/server-filesystem"
version = "1.2.3"
"#;
        let entry: McpEntry = toml::from_str(toml_str).unwrap();
        assert_eq!(entry.metadata.name, "filesystem-server");
        assert_eq!(entry.metadata.integrity, "observed");
        assert_eq!(entry.metadata.capabilities.len(), 2);
        match &entry.install {
            InstallConfig::Npm { package, version } => {
                assert_eq!(package, "@modelcontextprotocol/server-filesystem");
                assert_eq!(version, "1.2.3");
            }
            _ => panic!("Expected npm install config"),
        }
    }

    #[test]
    fn parse_pip_mcp_entry() {
        let toml_str = r#"
[metadata]
name = "sqlite-server"
description = "SQLite database access"
source = "community"
integrity = "verified"
capabilities = ["database:read", "database:write"]

[install]
type = "pip"
package = "mcp-server-sqlite"
version = "0.3.0"
python_version = ">=3.10"
"#;
        let entry: McpEntry = toml::from_str(toml_str).unwrap();
        match &entry.install {
            InstallConfig::Pip { python_version, .. } => {
                assert_eq!(python_version.as_deref(), Some(">=3.10"));
            }
            _ => panic!("Expected pip install config"),
        }
    }

    #[test]
    fn parse_cargo_mcp_entry() {
        let toml_str = r#"
[metadata]
name = "cargo-mcp"
description = "Rust MCP server"
source = "community"
integrity = "observed"
capabilities = ["filesystem:read"]

[install]
type = "cargo"
crate = "some-mcp-server"
version = "0.5.0"
"#;
        let entry: McpEntry = toml::from_str(toml_str).unwrap();
        match &entry.install {
            InstallConfig::Cargo {
                crate_name,
                version,
            } => {
                assert_eq!(crate_name, "some-mcp-server");
                assert_eq!(version, "0.5.0");
            }
            _ => panic!("Expected cargo install config"),
        }
    }

    #[test]
    fn parse_docker_mcp_entry() {
        let toml_str = r#"
[metadata]
name = "docker-mcp"
description = "Dockerized MCP"
source = "community"
integrity = "verified"
capabilities = ["network:egress"]

[install]
type = "docker"
image = "org/some-mcp"
tag = "1.2.3"
ports = [8080]
"#;
        let entry: McpEntry = toml::from_str(toml_str).unwrap();
        match &entry.install {
            InstallConfig::Docker { image, tag, ports } => {
                assert_eq!(image, "org/some-mcp");
                assert_eq!(tag, "1.2.3");
                assert_eq!(ports.as_deref(), Some(&[8080][..]));
            }
            _ => panic!("Expected docker install config"),
        }
    }

    #[test]
    fn parse_binary_mcp_entry() {
        let toml_str = r#"
[metadata]
name = "binary-mcp"
description = "Binary MCP"
source = "community"
integrity = "proven"
capabilities = ["execution:shell"]

[install]
type = "binary"
url = "https://github.com/org/repo/releases/download/v1.2.3/mcp-linux-amd64"
checksum = "sha256:def456"
"#;
        let entry: McpEntry = toml::from_str(toml_str).unwrap();
        match &entry.install {
            InstallConfig::Binary { url, checksum } => {
                assert!(url.contains("github.com"));
                assert!(checksum.starts_with("sha256:"));
            }
            _ => panic!("Expected binary install config"),
        }
    }

    #[test]
    fn parse_mcp_with_env_and_args() {
        let toml_str = r#"
[metadata]
name = "db-server"
description = "Database MCP"
source = "community"
integrity = "verified"
capabilities = ["database:read", "network:egress"]

[install]
type = "npm"
package = "@org/db-mcp"
version = "1.0.0"

[env]
DATABASE_URL = { required = true, description = "Connection string" }
LOG_LEVEL = { required = false, description = "Logging verbosity" }

[args]
default = ["--port", "8080"]
"#;
        let entry: McpEntry = toml::from_str(toml_str).unwrap();
        assert_eq!(entry.env.len(), 2);
        assert!(entry.env["DATABASE_URL"].required);
        assert!(!entry.env["LOG_LEVEL"].required);
        assert_eq!(entry.args.default, vec!["--port", "8080"]);
    }

    #[test]
    fn parse_skill_entry() {
        let toml_str = r#"
[metadata]
name = "deploy-app"
description = "Deploy application workflow"
tools_used = ["bash", "read_file", "write_file"]
capabilities = ["execution:shell(git, npm, docker)", "filesystem:write(./dist/**)"]
"#;
        let entry: SkillEntry = toml::from_str(toml_str).unwrap();
        assert_eq!(entry.metadata.name, "deploy-app");
        assert_eq!(entry.metadata.tools_used.len(), 3);
        assert_eq!(entry.metadata.capabilities.len(), 2);
    }

    #[test]
    fn parse_mcp_with_sandbox_section() {
        let toml_str = r#"
[metadata]
name = "github-mcp"
description = "GitHub API access"
source = "community"
integrity = "observed"
capabilities = ["network:egress(api.github.com)", "filesystem:read($WORKDIR)", "credentials"]

[install]
type = "npm"
package = "@mcp/github"
version = "1.0.0"

[sandbox]
extra_read = ["$HOME/.config/gh"]
extra_write = ["$TMPDIR/gh-cache"]
require_sandbox = true
"#;
        let entry: McpEntry = toml::from_str(toml_str).unwrap();
        let sandbox = entry.sandbox.unwrap();
        assert_eq!(sandbox.extra_read, vec!["$HOME/.config/gh"]);
        assert_eq!(sandbox.extra_write, vec!["$TMPDIR/gh-cache"]);
        assert!(sandbox.require_sandbox);
    }

    #[test]
    fn parse_mcp_without_sandbox_section() {
        let toml_str = r#"
[metadata]
name = "simple-mcp"
description = "Simple"
source = "community"
integrity = "untrusted"
capabilities = ["filesystem:read"]

[install]
type = "binary"
url = "builtin"
checksum = "builtin"
"#;
        let entry: McpEntry = toml::from_str(toml_str).unwrap();
        assert!(entry.sandbox.is_none());
    }

    #[test]
    fn sandbox_config_defaults_are_sensible() {
        let config = SandboxConfig::default();
        assert!(config.extra_read.is_empty());
        assert!(config.extra_write.is_empty());
        assert!(!config.require_sandbox);
    }

    #[test]
    fn mcp_entry_with_pinned_ref_and_track() {
        let toml_str = r#"
[metadata]
name = "claude-mem"
description = "Persistent memory for Claude Code"
repository = "https://github.com/thedotmack/claude-mem"
source = "npm"
integrity = "untrusted"
capabilities = ["filesystem:read(~/.claude-mem/)"]
pinned_ref = "abc123def"
track = true

[install]
type = "npm"
package = "@thedotmack/claude-mem"
version = "1.0.0"
"#;
        let entry: McpEntry = toml::from_str(toml_str).unwrap();
        assert_eq!(entry.metadata.pinned_ref.as_deref(), Some("abc123def"));
        assert_eq!(entry.metadata.track, Some(true));
    }

    #[test]
    fn mcp_entry_without_pinned_ref_and_track_defaults_to_none() {
        let toml_str = r#"
[metadata]
name = "test-tool"
description = "A test tool"
source = "npm"
integrity = "untrusted"
capabilities = []

[install]
type = "npm"
package = "test-tool"
version = "0.1.0"
"#;
        let entry: McpEntry = toml::from_str(toml_str).unwrap();
        assert!(entry.metadata.pinned_ref.is_none());
        assert!(entry.metadata.track.is_none());
    }

    #[test]
    fn parse_env_with_defaults() {
        let toml_str = r#"
[metadata]
name = "test-mcp"
description = "Test"
source = "community"
integrity = "observed"
capabilities = []

[install]
type = "npm"
package = "test"
version = "1.0.0"

[env]
WORKER_PORT = { required = false, default = "37777", description = "Worker port" }
DATA_DIR = { required = false, default = "$HOME/.data", description = "Data directory" }
API_KEY = { required = true, description = "API key (no default, must be provided)" }
"#;
        let entry: McpEntry = toml::from_str(toml_str).unwrap();
        assert_eq!(entry.env["WORKER_PORT"].default.as_deref(), Some("37777"));
        assert_eq!(
            entry.env["DATA_DIR"].default.as_deref(),
            Some("$HOME/.data")
        );
        assert!(entry.env["API_KEY"].default.is_none());
    }

    #[test]
    fn parse_mcp_with_daemon_sidecar() {
        let toml_str = r#"
[metadata]
name = "db-server"
description = "Database MCP"
source = "community"
integrity = "observed"
capabilities = ["database:read"]

[install]
type = "npm"
package = "@test/db"
version = "1.0.0"

[[sidecar]]
name = "postgres"
command = "postgres"
args = ["-D", "/var/lib/postgresql/data"]
lifecycle = "daemon"
ready_timeout = 60
ready_interval = 1000

[sidecar.ready_check]
type = "tcp"
host = "127.0.0.1"
port = 5432
"#;
        let entry: McpEntry = toml::from_str(toml_str).unwrap();
        assert_eq!(entry.sidecars.len(), 1);
        let sc = &entry.sidecars[0];
        assert_eq!(sc.name, "postgres");
        assert_eq!(sc.command, "postgres");
        assert_eq!(sc.args, vec!["-D", "/var/lib/postgresql/data"]);
        assert_eq!(sc.lifecycle, SidecarLifecycle::Daemon);
        assert_eq!(sc.ready_timeout, 60);
        assert_eq!(sc.ready_interval, 1000);
        assert!(sc.ready_check.is_some());
    }

    #[test]
    fn parse_mcp_with_init_sidecar() {
        let toml_str = r#"
[metadata]
name = "init-server"
description = "Init MCP"
source = "community"
integrity = "observed"
capabilities = []

[install]
type = "binary"
url = "builtin"
checksum = "builtin"

[[sidecar]]
name = "migrate"
command = "db-migrate"
args = ["--up"]
lifecycle = "init"
"#;
        let entry: McpEntry = toml::from_str(toml_str).unwrap();
        assert_eq!(entry.sidecars.len(), 1);
        let sc = &entry.sidecars[0];
        assert_eq!(sc.name, "migrate");
        assert_eq!(sc.lifecycle, SidecarLifecycle::Init);
        assert!(sc.ready_check.is_none());
        assert_eq!(sc.ready_timeout, 30);
        assert_eq!(sc.ready_interval, 500);
    }

    #[test]
    fn parse_mcp_without_sidecars_backward_compat() {
        let toml_str = r#"
[metadata]
name = "simple"
description = "No sidecars"
source = "community"
integrity = "untrusted"
capabilities = []

[install]
type = "binary"
url = "builtin"
checksum = "builtin"
"#;
        let entry: McpEntry = toml::from_str(toml_str).unwrap();
        assert!(entry.sidecars.is_empty());
    }

    #[test]
    fn parse_mcp_with_http_ready_check() {
        let toml_str = r#"
[metadata]
name = "http-check"
description = "HTTP ready check"
source = "community"
integrity = "observed"
capabilities = []

[install]
type = "binary"
url = "builtin"
checksum = "builtin"

[[sidecar]]
name = "web"
command = "web-server"
lifecycle = "daemon"

[sidecar.ready_check]
type = "http"
url = "http://localhost:8080/health"
"#;
        let entry: McpEntry = toml::from_str(toml_str).unwrap();
        match &entry.sidecars[0].ready_check {
            Some(ReadyCheck::Http { url }) => {
                assert_eq!(url, "http://localhost:8080/health");
            }
            other => panic!("Expected Http ready check, got: {other:?}"),
        }
    }

    #[test]
    fn parse_mcp_with_command_ready_check() {
        let toml_str = r#"
[metadata]
name = "cmd-check"
description = "Command ready check"
source = "community"
integrity = "observed"
capabilities = []

[install]
type = "binary"
url = "builtin"
checksum = "builtin"

[[sidecar]]
name = "service"
command = "my-service"
lifecycle = "daemon"

[sidecar.ready_check]
type = "command"
run = "pg_isready -h localhost"
"#;
        let entry: McpEntry = toml::from_str(toml_str).unwrap();
        match &entry.sidecars[0].ready_check {
            Some(ReadyCheck::Command { run }) => {
                assert_eq!(run, "pg_isready -h localhost");
            }
            other => panic!("Expected Command ready check, got: {other:?}"),
        }
    }

    #[test]
    fn validate_daemon_without_ready_check_fails() {
        let sidecars = vec![SidecarEntry {
            name: "broken".into(),
            command: "broken-daemon".into(),
            args: vec![],
            lifecycle: SidecarLifecycle::Daemon,
            ready_check: None,
            ready_timeout: 30,
            ready_interval: 500,
        }];
        let err = validate_sidecars(&sidecars).unwrap_err();
        assert!(err.to_string().contains("broken"));
        assert!(err.to_string().contains("must have a ready_check"));
    }

    #[test]
    fn validate_init_with_ready_check_fails() {
        let sidecars = vec![SidecarEntry {
            name: "bad-init".into(),
            command: "init-cmd".into(),
            args: vec![],
            lifecycle: SidecarLifecycle::Init,
            ready_check: Some(ReadyCheck::Http {
                url: "http://localhost".into(),
            }),
            ready_timeout: 30,
            ready_interval: 500,
        }];
        let err = validate_sidecars(&sidecars).unwrap_err();
        assert!(err.to_string().contains("bad-init"));
        assert!(err.to_string().contains("must not have a ready_check"));
    }

    #[test]
    fn validate_duplicate_names_fails() {
        let sidecars = vec![
            SidecarEntry {
                name: "dup".into(),
                command: "cmd1".into(),
                args: vec![],
                lifecycle: SidecarLifecycle::Init,
                ready_check: None,
                ready_timeout: 30,
                ready_interval: 500,
            },
            SidecarEntry {
                name: "dup".into(),
                command: "cmd2".into(),
                args: vec![],
                lifecycle: SidecarLifecycle::Init,
                ready_check: None,
                ready_timeout: 30,
                ready_interval: 500,
            },
        ];
        let err = validate_sidecars(&sidecars).unwrap_err();
        assert!(err.to_string().contains("duplicate sidecar name 'dup'"));
    }

    #[test]
    fn validate_valid_mixed_sidecars_passes() {
        let sidecars = vec![
            SidecarEntry {
                name: "db".into(),
                command: "postgres".into(),
                args: vec![],
                lifecycle: SidecarLifecycle::Daemon,
                ready_check: Some(ReadyCheck::Tcp {
                    host: "127.0.0.1".into(),
                    port: 5432,
                }),
                ready_timeout: 30,
                ready_interval: 500,
            },
            SidecarEntry {
                name: "migrate".into(),
                command: "migrate".into(),
                args: vec!["--up".into()],
                lifecycle: SidecarLifecycle::Init,
                ready_check: None,
                ready_timeout: 30,
                ready_interval: 500,
            },
        ];
        validate_sidecars(&sidecars).unwrap();
    }

    #[test]
    fn validate_empty_sidecars_passes() {
        validate_sidecars(&[]).unwrap();
    }

    #[test]
    fn parse_capability_taxonomy() {
        let toml_str = r#"
[capabilities.filesystem_read]
description = "Read files and directories"
scope_type = "path_glob"

[capabilities.network_egress]
description = "Make outbound network requests"
scope_type = "domain_glob"

[integrity_levels.untrusted]
description = "Unvetted, no network"
level = 1

[integrity_levels.proven]
description = "Formally verified"
level = 4
"#;
        let taxonomy: CapabilityTaxonomy = toml::from_str(toml_str).unwrap();
        assert_eq!(taxonomy.capabilities.len(), 2);
        assert_eq!(taxonomy.integrity_levels.len(), 2);
        assert_eq!(taxonomy.integrity_levels["proven"].level, 4);
    }
}
