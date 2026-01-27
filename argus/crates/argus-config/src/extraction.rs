use serde::{Deserialize, Serialize};

const fn default_max_turns() -> usize {
    15
}

const fn default_max_tokens() -> u64 {
    16384
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExtractionConfig {
    pub enabled: bool,
    pub cache_ttl_seconds: u64,
    pub mode: ExtractionMode,
    pub provider: ExtractionProviderConfig,
    #[serde(default = "default_max_turns")]
    pub max_turns: usize,
    #[serde(default = "default_max_tokens")]
    pub max_tokens: u64,
}

impl Default for ExtractionConfig {
    fn default() -> Self {
        Self {
            enabled: false,
            cache_ttl_seconds: 3600,
            mode: ExtractionMode::DryRun,
            provider: ExtractionProviderConfig::default(),
            max_turns: default_max_turns(),
            max_tokens: default_max_tokens(),
        }
    }
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum ExtractionMode {
    #[default]
    DryRun,
    Enforce,
}

fn default_extraction_timeout() -> u64 {
    5000
}

fn default_ollama_base_url() -> String {
    "http://localhost:11434".to_string()
}

#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "lowercase")]
pub enum ExtractionProviderConfig {
    OpenRouter {
        model: String,
        api_key_env: String,
        #[serde(default = "default_extraction_timeout")]
        timeout_ms: u64,
    },
    Ollama {
        model: String,
        #[serde(default = "default_ollama_base_url")]
        base_url: String,
        #[serde(default = "default_extraction_timeout")]
        timeout_ms: u64,
    },
    OpenAI {
        model: String,
        api_key_env: String,
        #[serde(default = "default_extraction_timeout")]
        timeout_ms: u64,
    },
    Anthropic {
        model: String,
        api_key_env: String,
        #[serde(default = "default_extraction_timeout")]
        timeout_ms: u64,
    },
    Gemini {
        model: String,
        api_key_env: String,
        #[serde(default = "default_extraction_timeout")]
        timeout_ms: u64,
    },
}

impl Default for ExtractionProviderConfig {
    fn default() -> Self {
        Self::Ollama {
            model: "llama3.2:3b".to_string(),
            base_url: default_ollama_base_url(),
            timeout_ms: default_extraction_timeout(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn extraction_config_defaults_to_disabled() {
        let config = ExtractionConfig::default();
        assert!(!config.enabled);
        assert_eq!(config.mode, ExtractionMode::DryRun);
        assert_eq!(config.max_turns, 15);
        assert_eq!(config.max_tokens, 16384);
    }

    #[test]
    fn extraction_mode_serializes_kebab_case() {
        let mode = ExtractionMode::DryRun;
        let json = serde_json::to_string(&mode).unwrap();
        assert_eq!(json, "\"dry-run\"");
    }

    #[test]
    fn extraction_provider_serializes_with_type_tag() {
        let provider = ExtractionProviderConfig::Ollama {
            model: "llama3.2:3b".to_string(),
            base_url: "http://localhost:11434".to_string(),
            timeout_ms: 5000,
        };
        let json = serde_json::to_string(&provider).unwrap();
        assert!(json.contains("\"type\":\"ollama\""));
    }

    #[test]
    fn openai_provider_serializes_correctly() {
        let provider = ExtractionProviderConfig::OpenAI {
            model: "gpt-4o-mini".to_string(),
            api_key_env: "OPENAI_API_KEY".to_string(),
            timeout_ms: 5000,
        };
        let json = serde_json::to_string(&provider).unwrap();
        assert!(json.contains("\"type\":\"openai\""));
        assert!(json.contains("\"model\":\"gpt-4o-mini\""));
    }

    #[test]
    fn anthropic_provider_serializes_correctly() {
        let provider = ExtractionProviderConfig::Anthropic {
            model: "claude-3-haiku-20240307".to_string(),
            api_key_env: "ANTHROPIC_API_KEY".to_string(),
            timeout_ms: 5000,
        };
        let json = serde_json::to_string(&provider).unwrap();
        assert!(json.contains("\"type\":\"anthropic\""));
    }
}
