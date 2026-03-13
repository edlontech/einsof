use std::path::Path;
use std::sync::Arc;

use argus_config::ExtractionProviderConfig;
use async_trait::async_trait;
use rig::agent::AgentBuilder;
use rig::client::{CompletionClient, Nothing};
use rig::completion::CompletionModel;
use rig::extractor::ExtractorBuilder;
use rig::providers::{anthropic, gemini, ollama, openai, openrouter};
use tracing::info;

use crate::error::{AnalysisError, Result, client_error, get_env_var};
use crate::orchestrator::OrchestratorConfig;
use crate::registry_extraction::RegistryCapabilityResult;
use crate::registry_types::{CapabilityFinding, Evidence};
use crate::sandbox::ToolContext;
use crate::tools::{ListDirectoryTool, ReadFileTool, ReadManifestTool, SearchCodeTool};

const REGISTRY_SYSTEM_PROMPT: &str = r#"You are a security analyst evaluating an MCP tool for inclusion in a curated registry.

Your job is to determine exactly what capabilities this tool requires to operate. Analyze the source code to find every:

1. **File system access**: What paths does it read from or write to? Look for fs operations, database files, config directories.
2. **Network access**: What domains/endpoints does it connect to? Look for HTTP clients, API SDKs, WebSocket connections.
3. **Network listening**: Does it bind to any ports? Look for server creation, express/http.listen, bind calls.
4. **Process execution**: Does it spawn child processes? Look for exec, spawn, child_process, Command.
5. **Secret/credential usage**: What API keys or tokens does it need? Look for env var reads, config file key references.

For each capability, use the scoped capability format:
- filesystem:read(<path>)
- filesystem:write(<path>)
- network:egress(<domain>)
- network:listen(<host:port>)
- process:exec(<binary>)
- secret:env(<VAR_NAME>)

For EVERY capability, you MUST provide evidence: the exact file, line number, code snippet, and reasoning.

Use the exploration tools to read the manifest first, then entry points, then search for patterns like 'http', 'fetch', 'fs.', 'exec', 'spawn', 'listen', 'bind', 'env', 'secret', 'key', 'token'.

Be thorough. Missing a capability means the sandbox will block the tool at runtime."#;

const REGISTRY_EXTRACTOR_PREAMBLE: &str = r#"You are a structured data extractor. Given a security analysis report about an MCP tool, extract all inferred capabilities with their evidence into the structured format.

Be thorough: extract every capability mentioned with full evidence chains. Each capability must have at least one evidence entry with file path, line number, code snippet, and reasoning."#;

fn build_registry_user_prompt(target_path: &str) -> String {
    format!(
        "Analyze the tool source code at: {target_path}\n\n\
        Explore the codebase systematically:\n\
        1. Read the manifest (package.json, Cargo.toml, etc.)\n\
        2. List the root directory structure\n\
        3. Read entry points and main modules\n\
        4. Search for network, filesystem, process, and secret patterns\n\
        5. Provide your complete findings with evidence for each capability."
    )
}

#[async_trait]
pub(crate) trait RegistryCapabilityExtract: Send + Sync {
    async fn extract(&self, text: &str) -> std::result::Result<RegistryCapabilityResult, String>;
}

#[async_trait]
impl<M> RegistryCapabilityExtract for rig::extractor::Extractor<M, RegistryCapabilityResult>
where
    M: CompletionModel + Send + Sync,
{
    async fn extract(&self, text: &str) -> std::result::Result<RegistryCapabilityResult, String> {
        rig::extractor::Extractor::extract(self, text)
            .await
            .map_err(|e| e.to_string())
    }
}

fn build_registry_extractor<M: CompletionModel>(model: M) -> impl RegistryCapabilityExtract {
    ExtractorBuilder::<M, RegistryCapabilityResult>::new(model)
        .preamble(REGISTRY_EXTRACTOR_PREAMBLE)
        .build()
}

#[async_trait]
trait RegistryAnalyzeOrchestrate: Send + Sync {
    async fn orchestrate(
        &self,
        ctx: Arc<ToolContext>,
        config: &OrchestratorConfig,
    ) -> Result<Vec<CapabilityFinding>>;
}

struct RegistryOrchestrateImpl<M: CompletionModel> {
    model: M,
}

#[async_trait]
impl<M> RegistryAnalyzeOrchestrate for RegistryOrchestrateImpl<M>
where
    M: CompletionModel + Clone + Send + Sync + 'static,
{
    async fn orchestrate(
        &self,
        ctx: Arc<ToolContext>,
        config: &OrchestratorConfig,
    ) -> Result<Vec<CapabilityFinding>> {
        use rig::completion::Prompt;

        let target_path = ctx.target_root().to_string_lossy().into_owned();

        let agent = AgentBuilder::new(self.model.clone())
            .preamble(REGISTRY_SYSTEM_PROMPT)
            .max_tokens(config.max_tokens)
            .tool(ListDirectoryTool { ctx: ctx.clone() })
            .tool(ReadFileTool { ctx: ctx.clone() })
            .tool(SearchCodeTool { ctx: ctx.clone() })
            .tool(ReadManifestTool { ctx })
            .build();

        let user_prompt = build_registry_user_prompt(&target_path);

        info!(
            max_turns = config.max_turns,
            "Starting registry analysis orchestrator"
        );
        let response = agent
            .prompt(&user_prompt)
            .multi_turn(config.max_turns)
            .await
            .map_err(|e| AnalysisError::LlmInference(e.to_string()))?;

        let extractor = build_registry_extractor(self.model.clone());
        let result = extractor
            .extract(&response)
            .await
            .map_err(AnalysisError::LlmInference)?;

        Ok(result
            .capabilities
            .into_iter()
            .map(|c| CapabilityFinding {
                capability: c.capability,
                evidence: c
                    .evidence
                    .into_iter()
                    .map(|e| Evidence {
                        file: e.file,
                        line: e.line,
                        snippet: e.snippet,
                        reasoning: e.reasoning,
                    })
                    .collect(),
            })
            .collect())
    }
}

pub struct RegistryAnalyzer {
    inner: Arc<dyn RegistryAnalyzeOrchestrate>,
    config: OrchestratorConfig,
}

impl std::fmt::Debug for RegistryAnalyzer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("RegistryAnalyzer").finish_non_exhaustive()
    }
}

macro_rules! make_registry_orchestrate {
    ($client:expr, $model:expr) => {
        Arc::new(RegistryOrchestrateImpl {
            model: $client.completion_model($model),
        })
    };
}

impl RegistryAnalyzer {
    pub fn new<M>(model: M) -> Self
    where
        M: CompletionModel + Clone + Send + Sync + 'static,
    {
        Self {
            inner: Arc::new(RegistryOrchestrateImpl { model }),
            config: OrchestratorConfig::default(),
        }
    }

    pub fn from_config(config: &ExtractionProviderConfig) -> Result<Self> {
        let inner: Arc<dyn RegistryAnalyzeOrchestrate> = match config {
            ExtractionProviderConfig::OpenRouter {
                model, api_key_env, ..
            } => {
                let api_key = get_env_var(api_key_env)?;
                let client: openrouter::Client =
                    openrouter::Client::new(&api_key).map_err(|e| client_error("OpenRouter", e))?;
                let completion_model = client.completion_model(model).with_strict_tools();
                Arc::new(RegistryOrchestrateImpl {
                    model: completion_model,
                })
            }
            ExtractionProviderConfig::Ollama {
                model, base_url, ..
            } => {
                let client: ollama::Client = ollama::Client::builder()
                    .api_key(Nothing)
                    .base_url(base_url)
                    .build()
                    .map_err(|e| client_error("Ollama", e))?;
                make_registry_orchestrate!(client, model)
            }
            ExtractionProviderConfig::OpenAI {
                model, api_key_env, ..
            } => {
                let api_key = get_env_var(api_key_env)?;
                let client: openai::Client =
                    openai::Client::new(&api_key).map_err(|e| client_error("OpenAI", e))?;
                make_registry_orchestrate!(client, model)
            }
            ExtractionProviderConfig::Anthropic {
                model, api_key_env, ..
            } => {
                let api_key = get_env_var(api_key_env)?;
                let client: anthropic::Client = anthropic::Client::builder()
                    .api_key(&api_key)
                    .anthropic_version(anthropic::completion::ANTHROPIC_VERSION_LATEST)
                    .build()
                    .map_err(|e| client_error("Anthropic", e))?;
                make_registry_orchestrate!(client, model)
            }
            ExtractionProviderConfig::Gemini {
                model, api_key_env, ..
            } => {
                let api_key = get_env_var(api_key_env)?;
                let client: gemini::Client =
                    gemini::Client::new(&api_key).map_err(|e| client_error("Gemini", e))?;
                make_registry_orchestrate!(client, model)
            }
        };

        Ok(Self {
            inner,
            config: OrchestratorConfig::default(),
        })
    }

    pub fn with_orchestrator_config(mut self, config: OrchestratorConfig) -> Self {
        self.config = config;
        self
    }

    pub async fn infer_capabilities(&self, source_dir: &Path) -> Result<Vec<CapabilityFinding>> {
        if !source_dir.exists() {
            return Err(AnalysisError::InvalidPath(format!(
                "Path does not exist: {}",
                source_dir.display()
            )));
        }
        let ctx = Arc::new(ToolContext::new(source_dir)?);
        self.inner.orchestrate(ctx, &self.config).await
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn registry_system_prompt_covers_capability_types() {
        assert!(REGISTRY_SYSTEM_PROMPT.contains("filesystem:read"));
        assert!(REGISTRY_SYSTEM_PROMPT.contains("network:egress"));
        assert!(REGISTRY_SYSTEM_PROMPT.contains("process:exec"));
        assert!(REGISTRY_SYSTEM_PROMPT.contains("secret:env"));
    }

    #[test]
    fn registry_user_prompt_includes_target_path() {
        let prompt = build_registry_user_prompt("/path/to/tool");
        assert!(prompt.contains("/path/to/tool"));
    }

    #[test]
    fn registry_user_prompt_describes_exploration_strategy() {
        let prompt = build_registry_user_prompt("/test");
        assert!(prompt.contains("manifest"));
        assert!(prompt.contains("entry points"));
        assert!(prompt.contains("Search for"));
    }

    #[tokio::test]
    async fn infer_capabilities_rejects_missing_path() {
        struct MockOrchestrate;
        #[async_trait]
        impl RegistryAnalyzeOrchestrate for MockOrchestrate {
            async fn orchestrate(
                &self,
                _ctx: Arc<ToolContext>,
                _config: &OrchestratorConfig,
            ) -> Result<Vec<CapabilityFinding>> {
                Ok(vec![])
            }
        }

        let analyzer = RegistryAnalyzer {
            inner: Arc::new(MockOrchestrate),
            config: OrchestratorConfig::default(),
        };

        let result = analyzer
            .infer_capabilities(Path::new("/nonexistent/path/99999"))
            .await;
        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), AnalysisError::InvalidPath(_)));
    }

    #[tokio::test]
    async fn infer_capabilities_with_mock_orchestrator() {
        struct MockOrchestrate;
        #[async_trait]
        impl RegistryAnalyzeOrchestrate for MockOrchestrate {
            async fn orchestrate(
                &self,
                _ctx: Arc<ToolContext>,
                _config: &OrchestratorConfig,
            ) -> Result<Vec<CapabilityFinding>> {
                Ok(vec![CapabilityFinding {
                    capability: "network:egress(api.anthropic.com)".to_string(),
                    evidence: vec![Evidence {
                        file: "src/client.ts".to_string(),
                        line: 10,
                        snippet: "new Anthropic()".to_string(),
                        reasoning: "Creates API client".to_string(),
                    }],
                }])
            }
        }

        let analyzer = RegistryAnalyzer {
            inner: Arc::new(MockOrchestrate),
            config: OrchestratorConfig::default(),
        };

        let temp_dir = tempfile::TempDir::new().unwrap();
        std::fs::write(temp_dir.path().join("index.js"), "// placeholder").unwrap();

        let caps = analyzer.infer_capabilities(temp_dir.path()).await.unwrap();
        assert_eq!(caps.len(), 1);
        assert_eq!(caps[0].capability, "network:egress(api.anthropic.com)");
        assert_eq!(caps[0].evidence.len(), 1);
    }

    #[tokio::test]
    async fn infer_capabilities_handles_orchestrator_failure() {
        struct FailingOrchestrate;
        #[async_trait]
        impl RegistryAnalyzeOrchestrate for FailingOrchestrate {
            async fn orchestrate(
                &self,
                _ctx: Arc<ToolContext>,
                _config: &OrchestratorConfig,
            ) -> Result<Vec<CapabilityFinding>> {
                Err(AnalysisError::LlmInference("timeout".to_string()))
            }
        }

        let analyzer = RegistryAnalyzer {
            inner: Arc::new(FailingOrchestrate),
            config: OrchestratorConfig::default(),
        };

        let temp_dir = tempfile::TempDir::new().unwrap();
        std::fs::write(temp_dir.path().join("main.py"), "import os").unwrap();

        let result = analyzer.infer_capabilities(temp_dir.path()).await;
        assert!(result.is_err());
    }

    #[test]
    fn registry_analyzer_with_config() {
        struct MockOrchestrate;
        #[async_trait]
        impl RegistryAnalyzeOrchestrate for MockOrchestrate {
            async fn orchestrate(
                &self,
                _ctx: Arc<ToolContext>,
                _config: &OrchestratorConfig,
            ) -> Result<Vec<CapabilityFinding>> {
                Ok(vec![])
            }
        }

        let analyzer = RegistryAnalyzer {
            inner: Arc::new(MockOrchestrate),
            config: OrchestratorConfig::default(),
        }
        .with_orchestrator_config(OrchestratorConfig {
            max_turns: 30,
            max_tokens: 32768,
        });

        assert_eq!(analyzer.config.max_turns, 30);
        assert_eq!(analyzer.config.max_tokens, 32768);
    }
}
