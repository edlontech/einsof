use std::collections::HashMap;

use crate::toml_types::{InstallEnvVar, SandboxConfig, SandboxNetPolicy};

#[derive(Debug, Clone, PartialEq)]
pub enum ParsedCapability {
    FilesystemRead(String),
    FilesystemWrite(String),
    NetworkEgress(String),
    NetworkListen(String),
    ProcessExec(String),
    SecretEnv(String),
    Unknown(String),
}

pub fn parse_capability(s: &str) -> ParsedCapability {
    if let Some(scope) = s
        .strip_prefix("filesystem:read(")
        .and_then(|s| s.strip_suffix(')'))
    {
        ParsedCapability::FilesystemRead(scope.to_string())
    } else if let Some(scope) = s
        .strip_prefix("filesystem:write(")
        .and_then(|s| s.strip_suffix(')'))
    {
        ParsedCapability::FilesystemWrite(scope.to_string())
    } else if let Some(scope) = s
        .strip_prefix("network:egress(")
        .and_then(|s| s.strip_suffix(')'))
    {
        ParsedCapability::NetworkEgress(scope.to_string())
    } else if let Some(scope) = s
        .strip_prefix("network:listen(")
        .and_then(|s| s.strip_suffix(')'))
    {
        ParsedCapability::NetworkListen(scope.to_string())
    } else if let Some(scope) = s
        .strip_prefix("process:exec(")
        .and_then(|s| s.strip_suffix(')'))
    {
        ParsedCapability::ProcessExec(scope.to_string())
    } else if let Some(scope) = s
        .strip_prefix("secret:env(")
        .and_then(|s| s.strip_suffix(')'))
    {
        ParsedCapability::SecretEnv(scope.to_string())
    } else {
        ParsedCapability::Unknown(s.to_string())
    }
}

pub fn generate_sandbox_config(capability_strings: &[String]) -> SandboxConfig {
    let mut extra_read = Vec::new();
    let mut extra_write = Vec::new();
    let mut egress_domains = Vec::new();

    for cap_str in capability_strings {
        match parse_capability(cap_str) {
            ParsedCapability::FilesystemRead(path) => {
                if !extra_read.contains(&path) {
                    extra_read.push(path);
                }
            }
            ParsedCapability::FilesystemWrite(path) => {
                if !extra_write.contains(&path) {
                    extra_write.push(path.clone());
                }
                if !extra_read.contains(&path) {
                    extra_read.push(path);
                }
            }
            ParsedCapability::NetworkEgress(domain) => {
                if !egress_domains.contains(&domain) {
                    egress_domains.push(domain);
                }
            }
            ParsedCapability::SecretEnv(_)
            | ParsedCapability::NetworkListen(_)
            | ParsedCapability::ProcessExec(_)
            | ParsedCapability::Unknown(_) => {}
        }
    }

    let net_policy = if egress_domains.is_empty() {
        Some(SandboxNetPolicy::Blocked)
    } else {
        Some(SandboxNetPolicy::EgressDomains(egress_domains))
    };

    SandboxConfig {
        extra_read,
        extra_write,
        require_sandbox: true,
        net_policy,
    }
}

pub fn generate_env_declarations(capability_strings: &[String]) -> HashMap<String, InstallEnvVar> {
    let mut env = HashMap::new();
    for cap_str in capability_strings {
        if let ParsedCapability::SecretEnv(var) = parse_capability(cap_str) {
            env.entry(var.clone()).or_insert_with(|| InstallEnvVar {
                required: true,
                description: format!("Required by secret:env({var}) capability"),
                default: None,
            });
        }
    }
    env
}

pub fn extract_env_defaults(env: &HashMap<String, InstallEnvVar>) -> HashMap<String, String> {
    env.iter()
        .filter_map(|(key, var)| var.default.as_ref().map(|d| (key.clone(), d.clone())))
        .collect()
}

pub fn required_env_keys(env: &HashMap<String, InstallEnvVar>) -> Vec<String> {
    let mut keys: Vec<String> = env
        .iter()
        .filter(|(_, var)| var.required)
        .map(|(key, _)| key.clone())
        .collect();
    keys.sort();
    keys
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_filesystem_read_capability() {
        assert_eq!(
            parse_capability("filesystem:read(~/.claude-mem/)"),
            ParsedCapability::FilesystemRead("~/.claude-mem/".to_string())
        );
    }

    #[test]
    fn parse_network_egress_capability() {
        assert_eq!(
            parse_capability("network:egress(api.anthropic.com)"),
            ParsedCapability::NetworkEgress("api.anthropic.com".to_string())
        );
    }

    #[test]
    fn parse_secret_env_capability() {
        assert_eq!(
            parse_capability("secret:env(ANTHROPIC_API_KEY)"),
            ParsedCapability::SecretEnv("ANTHROPIC_API_KEY".to_string())
        );
    }

    #[test]
    fn parse_unknown_capability() {
        assert_eq!(
            parse_capability("custom:something"),
            ParsedCapability::Unknown("custom:something".to_string())
        );
    }

    #[test]
    fn generate_sandbox_from_claude_mem_capabilities() {
        let caps = vec![
            "filesystem:read(~/.claude-mem/)".to_string(),
            "filesystem:write(~/.claude-mem/)".to_string(),
            "filesystem:read(.claude/)".to_string(),
            "network:egress(api.anthropic.com)".to_string(),
            "secret:env(ANTHROPIC_API_KEY)".to_string(),
        ];

        let config = generate_sandbox_config(&caps);

        assert!(config.extra_read.contains(&"~/.claude-mem/".to_string()));
        assert!(config.extra_read.contains(&".claude/".to_string()));
        assert!(config.extra_write.contains(&"~/.claude-mem/".to_string()));
        assert!(config.require_sandbox);

        match &config.net_policy {
            Some(SandboxNetPolicy::EgressDomains(domains)) => {
                assert_eq!(domains, &vec!["api.anthropic.com".to_string()]);
            }
            other => panic!("Expected EgressDomains, got {:?}", other),
        }

        let env_decls = generate_env_declarations(&caps);
        assert_eq!(env_decls.len(), 1);
        assert!(env_decls["ANTHROPIC_API_KEY"].required);
    }

    #[test]
    fn generate_sandbox_with_no_network_defaults_to_blocked() {
        let caps = vec!["filesystem:read(/tmp/)".to_string()];
        let config = generate_sandbox_config(&caps);
        assert_eq!(config.net_policy, Some(SandboxNetPolicy::Blocked));
    }

    #[test]
    fn write_implies_read() {
        let caps = vec!["filesystem:write(/data/)".to_string()];
        let config = generate_sandbox_config(&caps);
        assert!(config.extra_read.contains(&"/data/".to_string()));
        assert!(config.extra_write.contains(&"/data/".to_string()));
    }

    #[test]
    fn extract_defaults_from_env_map() {
        let mut env = HashMap::new();
        env.insert(
            "PORT".into(),
            InstallEnvVar {
                required: false,
                description: "Port".into(),
                default: Some("8080".into()),
            },
        );
        env.insert(
            "API_KEY".into(),
            InstallEnvVar {
                required: true,
                description: "API key".into(),
                default: None,
            },
        );

        let defaults = extract_env_defaults(&env);
        assert_eq!(defaults.len(), 1);
        assert_eq!(defaults["PORT"], "8080");

        let required = required_env_keys(&env);
        assert_eq!(required, vec!["API_KEY"]);
    }

    #[test]
    fn deduplicates_capabilities() {
        let caps = vec![
            "filesystem:read(/tmp/)".to_string(),
            "filesystem:read(/tmp/)".to_string(),
            "network:egress(example.com)".to_string(),
            "network:egress(example.com)".to_string(),
        ];
        let config = generate_sandbox_config(&caps);
        assert_eq!(config.extra_read.len(), 1);
        match &config.net_policy {
            Some(SandboxNetPolicy::EgressDomains(d)) => assert_eq!(d.len(), 1),
            _ => panic!("Expected EgressDomains"),
        }
    }
}
