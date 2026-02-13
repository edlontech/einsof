use std::collections::HashMap;
use std::fmt;
use std::path::PathBuf;

use secrecy::{ExposeSecret, SecretString};
use thiserror::Error;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum SecretSource {
    Static,
    Sops { file: PathBuf },
    OnePassword { vault: String, item: String },
    Keychain,
    Vault { path: String },
}

impl fmt::Display for SecretSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Static => write!(f, "static"),
            Self::Sops { file } => write!(f, "sops({})", file.display()),
            Self::OnePassword { vault, item } => write!(f, "1password({vault}/{item})"),
            Self::Keychain => write!(f, "keychain"),
            Self::Vault { path } => write!(f, "vault({path})"),
        }
    }
}

pub struct SecretValue {
    pub value: SecretString,
    pub source: SecretSource,
}

impl fmt::Debug for SecretValue {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("SecretValue")
            .field("value", &"[REDACTED]")
            .field("source", &self.source)
            .finish()
    }
}

impl SecretValue {
    pub fn new_static(value: &str) -> Self {
        Self {
            value: SecretString::from(value.to_string()),
            source: SecretSource::Static,
        }
    }

    pub fn new(value: String, source: SecretSource) -> Self {
        Self {
            value: SecretString::from(value),
            source,
        }
    }
}

#[derive(Error, Debug, Clone, PartialEq, Eq)]
pub enum SecretError {
    #[error("secret not found: {key}")]
    NotFound { key: String },
    #[error("failed to resolve secret '{key}': {reason}")]
    ProviderError { key: String, reason: String },
}

#[async_trait::async_trait]
pub trait SecretProvider: Send + Sync {
    async fn resolve(&self, key: &str) -> Result<SecretValue, SecretError>;

    async fn resolve_batch(
        &self,
        keys: &[&str],
    ) -> Result<HashMap<String, SecretValue>, SecretError> {
        let mut result = HashMap::new();
        for key in keys {
            result.insert(key.to_string(), self.resolve(key).await?);
        }
        Ok(result)
    }
}

pub struct ResolvedEnv {
    vars: HashMap<String, SecretValue>,
}

impl ResolvedEnv {
    pub fn new() -> Self {
        Self {
            vars: HashMap::new(),
        }
    }

    pub fn insert(&mut self, key: String, value: SecretValue) {
        self.vars.insert(key, value);
    }

    pub fn len(&self) -> usize {
        self.vars.len()
    }

    pub fn is_empty(&self) -> bool {
        self.vars.is_empty()
    }

    pub fn contains_key(&self, key: &str) -> bool {
        self.vars.contains_key(key)
    }

    pub fn to_string_map(&self) -> HashMap<String, String> {
        self.vars
            .iter()
            .map(|(k, v)| (k.clone(), v.value.expose_secret().to_string()))
            .collect()
    }
}

impl Default for ResolvedEnv {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn secret_value_from_static() {
        let sv = SecretValue::new_static("sk-12345");
        assert_eq!(sv.source, SecretSource::Static);
        assert_eq!(sv.value.expose_secret(), "sk-12345");
    }

    #[test]
    fn secret_source_display() {
        assert_eq!(SecretSource::Static.to_string(), "static");
        assert_eq!(
            SecretSource::Sops {
                file: PathBuf::from("secrets.yaml")
            }
            .to_string(),
            "sops(secrets.yaml)"
        );
    }

    #[test]
    fn resolved_env_builds_from_pairs() {
        let mut env = ResolvedEnv::new();
        env.insert("API_KEY".into(), SecretValue::new_static("val1"));
        env.insert("PORT".into(), SecretValue::new_static("8080"));
        assert_eq!(env.len(), 2);
        assert!(env.contains_key("API_KEY"));
    }

    #[test]
    fn resolved_env_to_string_map_exposes_values() {
        let mut env = ResolvedEnv::new();
        env.insert("KEY".into(), SecretValue::new_static("secret"));
        let map = env.to_string_map();
        assert_eq!(map.get("KEY").unwrap(), "secret");
    }
}
