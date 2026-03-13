use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[schemars(inline)]
pub struct RegistryEvidenceEntry {
    #[schemars(description = "Relative file path where the capability was observed")]
    pub file: String,
    #[schemars(description = "Line number in the file")]
    pub line: usize,
    #[schemars(description = "Relevant code snippet")]
    pub snippet: String,
    #[schemars(description = "Why this code implies the capability")]
    pub reasoning: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[schemars(inline)]
pub struct RegistryCapabilityEntry {
    #[schemars(
        description = "Scoped capability string, e.g. 'filesystem:read(~/.config/)' or 'network:egress(api.github.com)'"
    )]
    pub capability: String,
    #[schemars(description = "Evidence from source code supporting this inference")]
    pub evidence: Vec<RegistryEvidenceEntry>,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[schemars(description = "Result of analyzing a tool's source code for registry capabilities")]
pub struct RegistryCapabilityResult {
    #[schemars(description = "Inferred capabilities with evidence")]
    pub capabilities: Vec<RegistryCapabilityEntry>,
    #[schemars(description = "Security concerns or warnings")]
    pub warnings: Vec<String>,
    #[schemars(description = "Files explored during analysis")]
    pub files_explored: Vec<String>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn registry_capability_result_has_valid_schema() {
        let schema = schemars::schema_for!(RegistryCapabilityResult);
        let json = serde_json::to_string_pretty(&schema).unwrap();
        assert!(
            !json.contains("\"$ref\""),
            "Schema must be inlined, no $ref"
        );
    }

    #[test]
    fn registry_capability_result_round_trips() {
        let result = RegistryCapabilityResult {
            capabilities: vec![RegistryCapabilityEntry {
                capability: "network:egress(api.anthropic.com)".to_string(),
                evidence: vec![RegistryEvidenceEntry {
                    file: "src/client.ts".to_string(),
                    line: 10,
                    snippet: "fetch('https://api.anthropic.com')".to_string(),
                    reasoning: "Direct HTTP call to Anthropic API".to_string(),
                }],
            }],
            warnings: vec!["Broad file system access".to_string()],
            files_explored: vec!["src/client.ts".to_string()],
        };
        let json = serde_json::to_string(&result).unwrap();
        let deser: RegistryCapabilityResult = serde_json::from_str(&json).unwrap();
        assert_eq!(deser.capabilities.len(), 1);
        assert_eq!(deser.warnings.len(), 1);
    }
}
