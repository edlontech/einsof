use crate::specialists::{
    CapabilityExtractionResult, SECURITY_PREAMBLE, SecurityExtractionResult,
    build_capability_prompt, build_capability_system_prompt, build_security_prompt,
};
use async_trait::async_trait;
use rig::completion::{CompletionModel, ToolDefinition};
use rig::extractor::ExtractorBuilder;
use rig::tool::Tool;
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::sync::Arc;

#[derive(Debug, thiserror::Error)]
#[error("{0}")]
pub struct DelegationError(String);

#[async_trait]
pub(crate) trait SecurityExtract: Send + Sync {
    async fn extract(&self, prompt: &str) -> Result<SecurityExtractionResult, String>;
}

#[async_trait]
impl<M> SecurityExtract for rig::extractor::Extractor<M, SecurityExtractionResult>
where
    M: CompletionModel + Send + Sync,
{
    async fn extract(&self, prompt: &str) -> Result<SecurityExtractionResult, String> {
        rig::extractor::Extractor::extract(self, prompt)
            .await
            .map_err(|e| e.to_string())
    }
}

#[async_trait]
pub(crate) trait CapabilityExtract: Send + Sync {
    async fn extract(&self, prompt: &str) -> Result<CapabilityExtractionResult, String>;
}

#[async_trait]
impl<M> CapabilityExtract for rig::extractor::Extractor<M, CapabilityExtractionResult>
where
    M: CompletionModel + Send + Sync,
{
    async fn extract(&self, prompt: &str) -> Result<CapabilityExtractionResult, String> {
        rig::extractor::Extractor::extract(self, prompt)
            .await
            .map_err(|e| e.to_string())
    }
}

pub fn build_security_extractor<M: CompletionModel>(model: M) -> impl SecurityExtract {
    ExtractorBuilder::<M, SecurityExtractionResult>::new(model)
        .preamble(SECURITY_PREAMBLE)
        .build()
}

pub fn build_capability_extractor<M: CompletionModel>(model: M) -> impl CapabilityExtract {
    ExtractorBuilder::<M, CapabilityExtractionResult>::new(model)
        .preamble(&build_capability_system_prompt())
        .build()
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FileEntry {
    pub path: String,
    pub content: String,
}

fn into_tuples(files: Vec<FileEntry>) -> Vec<(String, String)> {
    files.into_iter().map(|f| (f.path, f.content)).collect()
}

#[derive(Deserialize)]
pub struct DelegateSecurityArgs {
    pub files: Vec<FileEntry>,
    pub context: String,
}

pub struct DelegateSecurityReviewTool {
    pub(crate) extractor: Arc<dyn SecurityExtract>,
}

impl Tool for DelegateSecurityReviewTool {
    const NAME: &'static str = "delegate_security_review";
    type Error = DelegationError;
    type Args = DelegateSecurityArgs;
    type Output = String;

    async fn definition(&self, _prompt: String) -> ToolDefinition {
        ToolDefinition {
            name: "delegate_security_review".to_string(),
            description: "Delegate security analysis to a specialist. Provide the relevant source files you've read and context notes about what you observed. Returns structured security findings.".to_string(),
            parameters: json!({
                "type": "object",
                "properties": {
                    "files": {
                        "type": "array",
                        "description": "Source files to analyze",
                        "items": {
                            "type": "object",
                            "properties": {
                                "path": { "type": "string", "description": "File path" },
                                "content": { "type": "string", "description": "File content" }
                            },
                            "required": ["path", "content"]
                        }
                    },
                    "context": {
                        "type": "string",
                        "description": "Context notes: what the tool does, entry points, data flow observations, concerning patterns"
                    }
                },
                "required": ["files", "context"]
            }),
        }
    }

    async fn call(&self, args: Self::Args) -> Result<Self::Output, Self::Error> {
        let prompt = build_security_prompt(&into_tuples(args.files), &args.context);

        let result = self
            .extractor
            .extract(&prompt)
            .await
            .map_err(|e| DelegationError(format!("Security analysis failed: {e}")))?;

        serde_json::to_string_pretty(&result).map_err(|e| DelegationError(e.to_string()))
    }
}

#[derive(Deserialize)]
pub struct DelegateCapabilityArgs {
    pub files: Vec<FileEntry>,
    pub context: String,
}

pub struct DelegateCapabilityInferenceTool {
    pub(crate) extractor: Arc<dyn CapabilityExtract>,
}

impl Tool for DelegateCapabilityInferenceTool {
    const NAME: &'static str = "delegate_capability_inference";
    type Error = DelegationError;
    type Args = DelegateCapabilityArgs;
    type Output = String;

    async fn definition(&self, _prompt: String) -> ToolDefinition {
        ToolDefinition {
            name: "delegate_capability_inference".to_string(),
            description: "Delegate capability inference to a specialist. Provide source files and context. Returns inferred capabilities with confidence scores.".to_string(),
            parameters: json!({
                "type": "object",
                "properties": {
                    "files": {
                        "type": "array",
                        "description": "Source files to analyze",
                        "items": {
                            "type": "object",
                            "properties": {
                                "path": { "type": "string", "description": "File path" },
                                "content": { "type": "string", "description": "File content" }
                            },
                            "required": ["path", "content"]
                        }
                    },
                    "context": {
                        "type": "string",
                        "description": "Context notes: what the tool does, key observations about its behavior"
                    }
                },
                "required": ["files", "context"]
            }),
        }
    }

    async fn call(&self, args: Self::Args) -> Result<Self::Output, Self::Error> {
        let prompt = build_capability_prompt(&into_tuples(args.files), &args.context);

        let result = self
            .extractor
            .extract(&prompt)
            .await
            .map_err(|e| DelegationError(format!("Capability inference failed: {e}")))?;

        serde_json::to_string_pretty(&result).map_err(|e| DelegationError(e.to_string()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn delegate_security_args_deserializes() {
        let json = r#"{
            "files": [{"path": "index.js", "content": "exec()"}],
            "context": "Server with exec"
        }"#;
        let args: DelegateSecurityArgs = serde_json::from_str(json).unwrap();
        assert_eq!(args.files.len(), 1);
        assert_eq!(args.files[0].path, "index.js");
        assert_eq!(args.context, "Server with exec");
    }

    #[test]
    fn delegate_capability_args_deserializes() {
        let json = r#"{
            "files": [{"path": "main.py", "content": "import os"}],
            "context": "Reads env vars"
        }"#;
        let args: DelegateCapabilityArgs = serde_json::from_str(json).unwrap();
        assert_eq!(args.files.len(), 1);
        assert_eq!(args.files[0].path, "main.py");
    }

    #[test]
    fn delegate_security_tool_has_correct_name() {
        assert_eq!(DelegateSecurityReviewTool::NAME, "delegate_security_review");
    }

    #[test]
    fn delegate_capability_tool_has_correct_name() {
        assert_eq!(
            DelegateCapabilityInferenceTool::NAME,
            "delegate_capability_inference"
        );
    }

    #[test]
    fn file_entry_serializes() {
        let entry = FileEntry {
            path: "test.js".to_string(),
            content: "code".to_string(),
        };
        let json = serde_json::to_string(&entry).unwrap();
        assert!(json.contains("test.js"));
        assert!(json.contains("code"));
    }

    #[test]
    fn delegate_security_args_with_multiple_files() {
        let json = r#"{
            "files": [
                {"path": "a.js", "content": "exec()"},
                {"path": "b.js", "content": "spawn()"}
            ],
            "context": "Two files with dangerous calls"
        }"#;
        let args: DelegateSecurityArgs = serde_json::from_str(json).unwrap();
        assert_eq!(args.files.len(), 2);
        assert_eq!(args.files[1].path, "b.js");
    }

    #[tokio::test]
    async fn delegate_security_tool_definition_is_valid() {
        struct FakeExtractor;
        #[async_trait]
        impl SecurityExtract for FakeExtractor {
            async fn extract(&self, _prompt: &str) -> Result<SecurityExtractionResult, String> {
                Ok(SecurityExtractionResult { findings: vec![] })
            }
        }

        let tool = DelegateSecurityReviewTool {
            extractor: Arc::new(FakeExtractor),
        };
        let def = tool.definition(String::new()).await;
        assert_eq!(def.name, "delegate_security_review");
        assert!(!def.description.is_empty());
    }

    #[tokio::test]
    async fn delegate_capability_tool_definition_is_valid() {
        struct FakeExtractor;
        #[async_trait]
        impl CapabilityExtract for FakeExtractor {
            async fn extract(&self, _prompt: &str) -> Result<CapabilityExtractionResult, String> {
                Ok(CapabilityExtractionResult {
                    capabilities: vec![],
                    warnings: vec![],
                })
            }
        }

        let tool = DelegateCapabilityInferenceTool {
            extractor: Arc::new(FakeExtractor),
        };
        let def = tool.definition(String::new()).await;
        assert_eq!(def.name, "delegate_capability_inference");
        assert!(!def.description.is_empty());
    }

    fn mock_security_finding() -> crate::specialists::SecurityFindingEntry {
        crate::specialists::SecurityFindingEntry {
            severity: "high".to_string(),
            category: "command_injection".to_string(),
            file: "index.js".to_string(),
            line: Some(1),
            evidence: "exec()".to_string(),
            explanation: "Dangerous".to_string(),
        }
    }

    #[tokio::test]
    async fn delegate_security_calls_extractor() {
        struct MockExtractor;
        #[async_trait]
        impl SecurityExtract for MockExtractor {
            async fn extract(&self, prompt: &str) -> Result<SecurityExtractionResult, String> {
                assert!(prompt.contains("index.js"));
                assert!(prompt.contains("exec()"));
                Ok(SecurityExtractionResult {
                    findings: vec![mock_security_finding()],
                })
            }
        }

        let tool = DelegateSecurityReviewTool {
            extractor: Arc::new(MockExtractor),
        };
        let result = tool
            .call(DelegateSecurityArgs {
                files: vec![FileEntry {
                    path: "index.js".to_string(),
                    content: "exec()".to_string(),
                }],
                context: "test".to_string(),
            })
            .await;
        assert!(result.is_ok());
        let output = result.unwrap();
        assert!(output.contains("command_injection"));
    }

    #[tokio::test]
    async fn delegate_capability_calls_extractor() {
        struct MockExtractor;
        #[async_trait]
        impl CapabilityExtract for MockExtractor {
            async fn extract(&self, prompt: &str) -> Result<CapabilityExtractionResult, String> {
                assert!(prompt.contains("main.py"));
                Ok(CapabilityExtractionResult {
                    capabilities: vec![crate::specialists::CapabilityEntryResult {
                        name: "filesystem_read".to_string(),
                        confidence: 0.9,
                        evidence: "open() call".to_string(),
                    }],
                    warnings: vec![],
                })
            }
        }

        let tool = DelegateCapabilityInferenceTool {
            extractor: Arc::new(MockExtractor),
        };
        let result = tool
            .call(DelegateCapabilityArgs {
                files: vec![FileEntry {
                    path: "main.py".to_string(),
                    content: "open('file.txt')".to_string(),
                }],
                context: "reads files".to_string(),
            })
            .await;
        assert!(result.is_ok());
        let output = result.unwrap();
        assert!(output.contains("filesystem_read"));
    }
}
