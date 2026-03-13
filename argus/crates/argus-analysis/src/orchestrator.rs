use crate::delegation::{
    DelegateCapabilityInferenceTool, DelegateSecurityReviewTool, build_capability_extractor,
    build_security_extractor,
};
use crate::sandbox::ToolContext;
use crate::specialists::{CapabilityEntryResult, SecurityFindingEntry, format_capability_list};
use crate::tools::{ListDirectoryTool, ReadFileTool, ReadManifestTool, SearchCodeTool};
use async_trait::async_trait;
use rig::agent::{Agent, AgentBuilder};
use rig::completion::CompletionModel;
use rig::extractor::ExtractorBuilder;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};
use std::sync::Arc;

#[derive(Debug, Clone)]
pub struct OrchestratorConfig {
    pub max_turns: usize,
    pub max_tokens: u64,
}

impl Default for OrchestratorConfig {
    fn default() -> Self {
        Self {
            max_turns: 15,
            max_tokens: 16384,
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[schemars(description = "Complete analysis result synthesized by the orchestrator")]
pub struct OrchestratorResult {
    #[schemars(description = "Inferred capabilities with confidence scores and evidence")]
    pub capabilities: Vec<CapabilityEntryResult>,
    #[schemars(description = "Security vulnerabilities found during analysis")]
    pub security_findings: Vec<SecurityFindingEntry>,
    #[schemars(description = "Warnings or concerns about the analysis")]
    pub warnings: Vec<String>,
    #[schemars(description = "Files that were explored during analysis")]
    pub files_explored: Vec<String>,
}

const RESULT_EXTRACTOR_PREAMBLE: &str = r#"You are a structured data extractor. Given a security analysis report, extract all findings into the structured format.

Extract every capability, security finding, all warnings, and the complete list of files explored. Be thorough and do not omit any findings from the report."#;

#[async_trait]
pub(crate) trait ResultExtract: Send + Sync {
    async fn extract(&self, text: &str) -> Result<OrchestratorResult, String>;
}

#[async_trait]
impl<M> ResultExtract for rig::extractor::Extractor<M, OrchestratorResult>
where
    M: CompletionModel + Send + Sync,
{
    async fn extract(&self, text: &str) -> Result<OrchestratorResult, String> {
        rig::extractor::Extractor::extract(self, text)
            .await
            .map_err(|e| e.to_string())
    }
}

pub fn build_result_extractor<M: CompletionModel>(model: M) -> impl ResultExtract {
    ExtractorBuilder::<M, OrchestratorResult>::new(model)
        .preamble(RESULT_EXTRACTOR_PREAMBLE)
        .build()
}

pub fn system_prompt() -> String {
    format!(
        r#"You are a security analysis orchestrator. Your job is to thoroughly analyze a tool or MCP server for security risks and capabilities.

You have filesystem tools to explore the codebase:
- list_directory: List files in a directory
- read_file: Read a file's content (supports offset/limit for large files)
- search_code: Regex search across all source files
- read_manifest: Read the project manifest (package.json, Cargo.toml, etc.)

Once you understand the codebase, delegate to specialist agents:
- delegate_security_review: Analyze files for security vulnerabilities
- delegate_capability_inference: Infer capabilities

When delegating, always provide:
1. The actual file contents you've read (not just paths)
2. Context notes explaining what you found (entry points, data flow, concerning patterns)

Strategy:
1. Read the manifest to understand what the tool does and its dependencies
2. List the root directory to see the project structure
3. Read entry points and follow imports to understand the architecture
4. Search for dangerous patterns: exec, eval, spawn, fetch, fs.write, child_process, subprocess, etc.
5. Delegate to the security specialist with the most relevant files and your observations
6. Delegate to the capability specialist with key files and context
7. After both specialists respond, write a thorough summary of your complete findings

Known capability taxonomy:
{capabilities}

Your final message must be a thorough summary covering:
- Every capability detected with its confidence level and supporting evidence
- Every security finding with severity, file location, and explanation
- Any warnings or concerns
- A complete list of all files you explored"#,
        capabilities = format_capability_list(),
    )
}

pub fn build_user_prompt(target_path: &str) -> String {
    format!(
        "Analyze the tool/MCP at: {target_path}\n\n\
        Explore the codebase, understand its structure and purpose, \
        then delegate to specialist agents for detailed security and capability analysis. \
        Synthesize their results into your final assessment."
    )
}

pub fn build_orchestrator<M>(
    model: M,
    ctx: Arc<ToolContext>,
    config: &OrchestratorConfig,
) -> (Agent<M>, usize)
where
    M: CompletionModel + Clone + 'static,
{
    let security_extractor = Arc::new(build_security_extractor(model.clone()));
    let capability_extractor = Arc::new(build_capability_extractor(model.clone()));

    let agent = AgentBuilder::new(model)
        .preamble(&system_prompt())
        .max_tokens(config.max_tokens)
        .tool(ListDirectoryTool { ctx: ctx.clone() })
        .tool(ReadFileTool { ctx: ctx.clone() })
        .tool(SearchCodeTool { ctx: ctx.clone() })
        .tool(ReadManifestTool { ctx })
        .tool(DelegateSecurityReviewTool {
            extractor: security_extractor,
        })
        .tool(DelegateCapabilityInferenceTool {
            extractor: capability_extractor,
        })
        .build();

    (agent, config.max_turns)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn orchestrator_config_defaults() {
        let config = OrchestratorConfig::default();
        assert_eq!(config.max_turns, 15);
        assert_eq!(config.max_tokens, 16384);
    }

    #[test]
    fn orchestrator_config_custom_values() {
        let config = OrchestratorConfig {
            max_turns: 30,
            max_tokens: 100_000,
        };
        assert_eq!(config.max_turns, 30);
        assert_eq!(config.max_tokens, 100_000);
    }

    #[test]
    fn system_prompt_covers_exploration_tools() {
        let prompt = system_prompt();
        assert!(prompt.contains("list_directory"));
        assert!(prompt.contains("read_file"));
        assert!(prompt.contains("search_code"));
        assert!(prompt.contains("read_manifest"));
    }

    #[test]
    fn system_prompt_covers_delegation_tools() {
        let prompt = system_prompt();
        assert!(prompt.contains("delegate_security_review"));
        assert!(prompt.contains("delegate_capability_inference"));
    }

    #[test]
    fn system_prompt_includes_capability_catalog() {
        let prompt = system_prompt();
        assert!(prompt.contains("filesystem_read"));
        assert!(prompt.contains("network_egress"));
        assert!(prompt.contains("execution_shell"));
    }

    #[test]
    fn system_prompt_describes_expected_output() {
        let prompt = system_prompt();
        assert!(prompt.contains("capability"));
        assert!(prompt.contains("security finding"));
        assert!(prompt.contains("files you explored"));
    }

    #[test]
    fn user_prompt_includes_target_path() {
        let prompt = build_user_prompt("/path/to/tool");
        assert!(prompt.contains("/path/to/tool"));
    }

    #[test]
    fn user_prompt_mentions_delegation() {
        let prompt = build_user_prompt("/test");
        assert!(prompt.contains("delegate"));
        assert!(prompt.contains("specialist"));
    }

    #[test]
    fn orchestrator_result_deserializes() {
        let json = r#"{
            "capabilities": [
                {"name": "filesystem_read", "confidence": 0.9, "evidence": "fs.readFile call"}
            ],
            "security_findings": [
                {
                    "severity": "high",
                    "category": "command_injection",
                    "file": "index.js",
                    "line": 42,
                    "evidence": "exec(input)",
                    "explanation": "User input flows to exec"
                }
            ],
            "warnings": ["Uses deprecated API"],
            "files_explored": ["index.js", "package.json"]
        }"#;
        let result: OrchestratorResult = serde_json::from_str(json).unwrap();
        assert_eq!(result.capabilities.len(), 1);
        assert_eq!(result.capabilities[0].name, "filesystem_read");
        assert_eq!(result.security_findings.len(), 1);
        assert_eq!(result.security_findings[0].category, "command_injection");
        assert_eq!(result.warnings.len(), 1);
        assert_eq!(result.files_explored.len(), 2);
    }

    #[test]
    fn orchestrator_result_empty() {
        let json = r#"{
            "capabilities": [],
            "security_findings": [],
            "warnings": [],
            "files_explored": []
        }"#;
        let result: OrchestratorResult = serde_json::from_str(json).unwrap();
        assert!(result.capabilities.is_empty());
        assert!(result.security_findings.is_empty());
    }

    #[test]
    fn orchestrator_result_serializes_roundtrip() {
        let result = OrchestratorResult {
            capabilities: vec![CapabilityEntryResult {
                name: "network_egress".to_string(),
                confidence: 0.85,
                evidence: "fetch() call".to_string(),
            }],
            security_findings: vec![],
            warnings: vec!["No tests found".to_string()],
            files_explored: vec!["src/main.ts".to_string()],
        };
        let json = serde_json::to_string(&result).unwrap();
        let deserialized: OrchestratorResult = serde_json::from_str(&json).unwrap();
        assert_eq!(deserialized.capabilities[0].name, "network_egress");
    }

    #[test]
    fn orchestrator_result_schema_generated() {
        let schema = schemars::schema_for!(OrchestratorResult);
        let json = serde_json::to_string(&schema).unwrap();
        assert!(json.contains("capabilities"));
        assert!(json.contains("security_findings"));
        assert!(json.contains("files_explored"));
    }

    #[test]
    fn result_extractor_preamble_describes_task() {
        assert!(RESULT_EXTRACTOR_PREAMBLE.contains("extract"));
        assert!(RESULT_EXTRACTOR_PREAMBLE.contains("structured"));
    }

    #[tokio::test]
    async fn result_extract_trait_with_mock() {
        struct MockExtractor;
        #[async_trait]
        impl ResultExtract for MockExtractor {
            async fn extract(&self, text: &str) -> Result<OrchestratorResult, String> {
                assert!(text.contains("test input"));
                Ok(OrchestratorResult {
                    capabilities: vec![],
                    security_findings: vec![],
                    warnings: vec![],
                    files_explored: vec![],
                })
            }
        }

        let extractor = MockExtractor;
        let result = extractor.extract("test input").await.unwrap();
        assert!(result.capabilities.is_empty());
    }

    #[tokio::test]
    async fn result_extract_trait_error_propagation() {
        struct FailingExtractor;
        #[async_trait]
        impl ResultExtract for FailingExtractor {
            async fn extract(&self, _text: &str) -> Result<OrchestratorResult, String> {
                Err("extraction failed".to_string())
            }
        }

        let extractor = FailingExtractor;
        let result = extractor.extract("anything").await;
        assert!(result.is_err());
        assert!(result.unwrap_err().contains("extraction failed"));
    }
}
