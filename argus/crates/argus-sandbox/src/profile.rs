use std::collections::HashMap;
use std::path::PathBuf;

use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Default, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum NetPolicy {
    #[default]
    Blocked,
    EgressOnly,
    EgressWithDomains(Vec<String>),
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct SandboxProfile {
    pub allowed_read_paths: Vec<PathBuf>,
    pub allowed_write_paths: Vec<PathBuf>,
    pub net_policy: NetPolicy,
    #[serde(default)]
    pub resolved_env: HashMap<String, String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn default_profile_is_deny_all() {
        let profile = SandboxProfile::default();
        assert!(profile.allowed_read_paths.is_empty());
        assert!(profile.allowed_write_paths.is_empty());
        assert_eq!(profile.net_policy, NetPolicy::Blocked);
        assert!(profile.resolved_env.is_empty());
    }

    #[test]
    fn net_policy_default_is_blocked() {
        assert_eq!(NetPolicy::default(), NetPolicy::Blocked);
    }

    #[test]
    fn profile_serialization_roundtrip() {
        let mut resolved = HashMap::new();
        resolved.insert("GITHUB_TOKEN".to_string(), "ghp_abc123".to_string());
        resolved.insert("HOME".to_string(), "/home/user".to_string());

        let profile = SandboxProfile {
            allowed_read_paths: vec![PathBuf::from("/usr/lib"), PathBuf::from("/tmp/data")],
            allowed_write_paths: vec![PathBuf::from("/tmp/output")],
            net_policy: NetPolicy::EgressWithDomains(vec![
                "api.github.com".into(),
                "*.openai.com".into(),
            ]),
            resolved_env: resolved,
        };
        let json = serde_json::to_string(&profile).unwrap();
        let deserialized: SandboxProfile = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized.allowed_read_paths, profile.allowed_read_paths);
        assert_eq!(deserialized.net_policy, profile.net_policy);
        assert_eq!(deserialized.resolved_env, profile.resolved_env);
    }

    #[test]
    fn net_policy_blocked_serializes_as_string() {
        let json = serde_json::to_string(&NetPolicy::Blocked).unwrap();
        assert_eq!(json, "\"blocked\"");
    }

    #[test]
    fn net_policy_egress_only_serializes_as_string() {
        let json = serde_json::to_string(&NetPolicy::EgressOnly).unwrap();
        assert_eq!(json, "\"egress_only\"");
    }

    #[test]
    fn net_policy_egress_with_domains_serializes_as_object() {
        let policy = NetPolicy::EgressWithDomains(vec!["api.github.com".into()]);
        let json = serde_json::to_string(&policy).unwrap();
        let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
        assert!(parsed.get("egress_with_domains").is_some());
    }
}
