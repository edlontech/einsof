#![cfg(feature = "runtime")]

use std::collections::HashMap;

use argus_sandbox::{
    NetPolicy, ProfileBuilder, SandboxProfile, SecretProvider, StaticProvider,
};
use secrecy::ExposeSecret;

#[tokio::test]
async fn full_env_isolation_chain() {
    let mut defaults = HashMap::new();
    defaults.insert("WORKER_PORT".into(), "37777".into());
    defaults.insert("LOG_LEVEL".into(), "INFO".into());

    let mut overrides = HashMap::new();
    overrides.insert("LOG_LEVEL".into(), "DEBUG".into());

    let provider = StaticProvider::new(defaults, overrides);

    let keys = ["WORKER_PORT", "LOG_LEVEL"];
    let resolved = provider.resolve_batch(&keys).await.unwrap();

    let env_map: HashMap<String, String> = resolved
        .iter()
        .map(|(k, v)| (k.clone(), v.value.expose_secret().to_string()))
        .collect();

    let profile = ProfileBuilder::new()
        .extra_read(vec!["/tmp/test".into()])
        .resolved_env(env_map)
        .net_policy(NetPolicy::Blocked)
        .build()
        .unwrap();

    assert_eq!(profile.resolved_env["WORKER_PORT"], "37777");
    assert_eq!(profile.resolved_env["LOG_LEVEL"], "DEBUG");

    let json = serde_json::to_string(&profile).unwrap();
    let deserialized: SandboxProfile = serde_json::from_str(&json).unwrap();
    assert_eq!(deserialized.resolved_env["WORKER_PORT"], "37777");
    assert_eq!(deserialized.resolved_env["LOG_LEVEL"], "DEBUG");
}

#[tokio::test]
async fn missing_required_env_var_is_caught() {
    let provider = StaticProvider::new(HashMap::new(), HashMap::new());
    let result = provider.resolve("MISSING_REQUIRED_KEY").await;
    assert!(result.is_err());
}

#[tokio::test]
async fn override_file_integration() {
    let dir = tempfile::TempDir::new().unwrap();
    let override_path = dir.path().join("test-mcp.toml");
    std::fs::write(&override_path, "API_KEY = \"sk-from-file\"\nPORT = \"9999\"\n").unwrap();

    let mut defaults = HashMap::new();
    defaults.insert("PORT".into(), "8080".into());

    let provider = StaticProvider::from_defaults(defaults)
        .with_override_file(&override_path)
        .unwrap();

    let api_key = provider.resolve("API_KEY").await.unwrap();
    assert_eq!(api_key.value.expose_secret(), "sk-from-file");

    let port = provider.resolve("PORT").await.unwrap();
    assert_eq!(port.value.expose_secret(), "9999");
}

#[test]
fn empty_profile_serializes_without_env() {
    let profile = SandboxProfile::default();
    let json = serde_json::to_string(&profile).unwrap();
    let parsed: serde_json::Value = serde_json::from_str(&json).unwrap();
    let env = parsed.get("resolved_env").unwrap();
    assert!(env.as_object().unwrap().is_empty());
}
