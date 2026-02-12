use std::collections::HashMap;

use crate::secret::{SecretError, SecretProvider, SecretSource, SecretValue};

pub struct StaticProvider {
    defaults: HashMap<String, String>,
    overrides: HashMap<String, String>,
}

impl StaticProvider {
    pub fn new(defaults: HashMap<String, String>, overrides: HashMap<String, String>) -> Self {
        Self {
            defaults,
            overrides,
        }
    }

    pub fn from_defaults(defaults: HashMap<String, String>) -> Self {
        Self::new(defaults, HashMap::new())
    }

    pub fn with_override_file(mut self, path: &std::path::Path) -> Result<Self, String> {
        if path.is_file() {
            let contents = std::fs::read_to_string(path)
                .map_err(|e| format!("failed to read override file {}: {e}", path.display()))?;
            let parsed = parse_override_toml(&contents)?;
            self.overrides.extend(parsed);
        }
        Ok(self)
    }
}

#[async_trait::async_trait]
impl SecretProvider for StaticProvider {
    async fn resolve(&self, key: &str) -> Result<SecretValue, SecretError> {
        if let Some(val) = self.overrides.get(key) {
            return Ok(SecretValue::new(val.clone(), SecretSource::Static));
        }
        if let Some(val) = self.defaults.get(key) {
            return Ok(SecretValue::new(val.clone(), SecretSource::Static));
        }
        Err(SecretError::NotFound {
            key: key.to_string(),
        })
    }
}

pub fn parse_override_toml(content: &str) -> Result<HashMap<String, String>, String> {
    let table: HashMap<String, String> =
        toml::from_str(content).map_err(|e| format!("invalid override TOML: {e}"))?;
    Ok(table)
}

#[cfg(test)]
mod tests {
    use super::*;
    use secrecy::ExposeSecret;

    #[tokio::test]
    async fn resolves_from_defaults() {
        let mut defaults = HashMap::new();
        defaults.insert("PORT".to_string(), "8080".to_string());

        let provider = StaticProvider::new(defaults, HashMap::new());
        let val = provider.resolve("PORT").await.unwrap();
        assert_eq!(val.value.expose_secret(), "8080");
        assert_eq!(val.source, SecretSource::Static);
    }

    #[tokio::test]
    async fn overrides_take_precedence() {
        let mut defaults = HashMap::new();
        defaults.insert("PORT".to_string(), "8080".to_string());

        let mut overrides = HashMap::new();
        overrides.insert("PORT".to_string(), "9090".to_string());

        let provider = StaticProvider::new(defaults, overrides);
        let val = provider.resolve("PORT").await.unwrap();
        assert_eq!(val.value.expose_secret(), "9090");
    }

    #[tokio::test]
    async fn not_found_returns_error() {
        let provider = StaticProvider::new(HashMap::new(), HashMap::new());
        let err = provider.resolve("MISSING").await.unwrap_err();
        assert!(matches!(err, SecretError::NotFound { .. }));
    }

    #[tokio::test]
    async fn resolve_batch_returns_all() {
        let mut defaults = HashMap::new();
        defaults.insert("A".to_string(), "1".to_string());
        defaults.insert("B".to_string(), "2".to_string());

        let provider = StaticProvider::new(defaults, HashMap::new());
        let result = provider.resolve_batch(&["A", "B"]).await.unwrap();
        assert_eq!(result.len(), 2);
        assert_eq!(result["A"].value.expose_secret(), "1");
    }

    #[test]
    fn loads_overrides_from_toml_string() {
        let toml_str = r#"
PORT = "9090"
API_KEY = "sk-override"
"#;
        let overrides = parse_override_toml(toml_str).unwrap();
        assert_eq!(overrides["PORT"], "9090");
        assert_eq!(overrides["API_KEY"], "sk-override");
    }
}
