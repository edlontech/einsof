use argus_kernel::{AgentId, BackgroundTheory, ContentGateOracle, KernelState, ToolId};
use secretscan::patterns::{
    analyze_base64_for_secrets, analyze_hex_for_secrets, analyze_url_encoded_for_secrets,
    get_all_patterns,
};

pub struct SentinelContentGate {
    _private: (),
}

impl Default for SentinelContentGate {
    fn default() -> Self {
        Self::new()
    }
}

impl SentinelContentGate {
    pub fn new() -> Self {
        Self { _private: () }
    }

    pub fn scan_strings(&self, value: &serde_json::Value) -> Vec<Detection> {
        let mut detections = Vec::new();
        self.scan_value(value, &mut detections);
        detections
    }

    fn scan_value(&self, value: &serde_json::Value, detections: &mut Vec<Detection>) {
        match value {
            serde_json::Value::String(s) => {
                self.scan_text(s, detections);
            }
            serde_json::Value::Array(arr) => {
                for v in arr {
                    self.scan_value(v, detections);
                }
            }
            serde_json::Value::Object(map) => {
                for v in map.values() {
                    self.scan_value(v, detections);
                }
            }
            _ => {}
        }
    }

    fn scan_text(&self, text: &str, detections: &mut Vec<Detection>) {
        for (pattern_name, regex) in get_all_patterns().iter() {
            if let Some(m) = regex.find(text) {
                detections.push(Detection {
                    kind: DetectionKind::SecretPattern,
                    pattern_name: pattern_name.clone(),
                    matched_text: m.as_str().to_owned(),
                });
            }
        }

        for (pattern_name, matched) in analyze_base64_for_secrets(text) {
            detections.push(Detection {
                kind: DetectionKind::ObfuscatedSecret,
                pattern_name,
                matched_text: matched,
            });
        }

        for (pattern_name, matched) in analyze_hex_for_secrets(text) {
            detections.push(Detection {
                kind: DetectionKind::ObfuscatedSecret,
                pattern_name,
                matched_text: matched,
            });
        }

        if text.contains('%') {
            for (pattern_name, matched) in analyze_url_encoded_for_secrets(text) {
                detections.push(Detection {
                    kind: DetectionKind::ObfuscatedSecret,
                    pattern_name,
                    matched_text: matched,
                });
            }
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Detection {
    pub kind: DetectionKind,
    pub pattern_name: String,
    pub matched_text: String,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DetectionKind {
    SecretPattern,
    ObfuscatedSecret,
}

impl ContentGateOracle for SentinelContentGate {
    fn passes(
        &self,
        agent: &AgentId,
        tool: &ToolId,
        _state: &KernelState,
        _bg: &BackgroundTheory,
    ) -> bool {
        tracing::debug!(agent = %agent, tool = %tool, "content gate evaluated");
        true
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use argus_kernel::BackgroundTheoryBuilder;
    use serde_json::json;

    fn gate() -> SentinelContentGate {
        SentinelContentGate::new()
    }

    #[test]
    fn detects_aws_access_key() {
        let input = json!({"key": "AKIAIOSFODNN7EXAMPLE"});
        let detections = gate().scan_strings(&input);
        assert!(
            !detections.is_empty(),
            "expected detection for AWS access key"
        );
        assert!(
            detections
                .iter()
                .any(|d| d.kind == DetectionKind::SecretPattern)
        );
    }

    #[test]
    fn detects_github_token() {
        let input = json!({"token": "ghp_ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghij12"});
        let detections = gate().scan_strings(&input);
        assert!(
            !detections.is_empty(),
            "expected detection for GitHub token"
        );
    }

    #[test]
    fn detects_openai_api_key() {
        let input = json!({"api_key": "sk-aBcDeFgHiJkLmNoPqRsTuVwXyZ0123456789"});
        let detections = gate().scan_strings(&input);
        assert!(
            !detections.is_empty(),
            "expected detection for OpenAI API key"
        );
    }

    #[test]
    fn clean_input_produces_no_detections() {
        let input = json!({
            "message": "Hello world",
            "count": 42,
            "items": ["apple", "banana"]
        });
        let detections = gate().scan_strings(&input);
        assert!(
            detections.is_empty(),
            "expected no detections for clean input, got: {detections:?}"
        );
    }

    #[test]
    fn scans_nested_json_recursively() {
        let input = json!({
            "outer": {
                "inner": {
                    "deep": "AKIAIOSFODNN7EXAMPLE"
                }
            }
        });
        let detections = gate().scan_strings(&input);
        assert!(!detections.is_empty(), "expected detection in nested JSON");
    }

    #[test]
    fn detects_base64_obfuscated_secret() {
        // "AKIAIOSFODNN7EXAMPLE" base64-encoded
        let encoded = "QUtJQUlPU0ZPRE5ON0VYQU1QTEU=";
        let input = json!({"payload": encoded});
        let detections = gate().scan_strings(&input);
        assert!(
            detections
                .iter()
                .any(|d| d.kind == DetectionKind::ObfuscatedSecret),
            "expected ObfuscatedSecret detection for base64-encoded AWS key, got: {detections:?}"
        );
    }

    #[test]
    fn content_gate_oracle_always_passes() {
        let gate = gate();
        let state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        assert!(gate.passes(
            &AgentId::new("any-agent"),
            &ToolId::new("any-tool"),
            &state,
            &bg,
        ));
    }
}
