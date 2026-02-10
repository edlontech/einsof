use crate::error::{AnalysisError, Result, client_error, get_env_var};
use crate::orchestrator::{
    OrchestratorConfig, OrchestratorResult, ResultExtract, build_orchestrator,
    build_result_extractor, build_user_prompt,
};
use crate::sandbox::ToolContext;
use crate::types::{
    AnalysisReport, FindingSeverity, InferredCapability, SecurityFinding,
};
use argus_config::ExtractionProviderConfig;
use async_trait::async_trait;
use rig::client::{CompletionClient, Nothing};
use rig::completion::{CompletionModel, Prompt};
use rig::providers::{anthropic, gemini, ollama, openai, openrouter};
use std::path::{Path, PathBuf};
use std::sync::Arc;
use std::time::Instant;
use tracing::{debug, info};

#[async_trait]
trait AnalyzeOrchestrate: Send + Sync {
    async fn orchestrate(
        &self,
        ctx: Arc<ToolContext>,
        config: &OrchestratorConfig,
    ) -> Result<OrchestratorResult>;
}

struct OrchestrateImpl<M: CompletionModel> {
    model: M,
}

#[async_trait]
impl<M> AnalyzeOrchestrate for OrchestrateImpl<M>
where
    M: CompletionModel + Clone + Send + Sync + 'static,
{
    async fn orchestrate(
        &self,
        ctx: Arc<ToolContext>,
        config: &OrchestratorConfig,
    ) -> Result<OrchestratorResult> {
        let target_path = ctx.target_root().to_string_lossy().into_owned();
        let (agent, max_turns) = build_orchestrator(self.model.clone(), ctx, config);
        let user_prompt = build_user_prompt(&target_path);

        info!(max_turns, "Starting orchestrator agent");
        let response = agent
            .prompt(&user_prompt)
            .multi_turn(max_turns)
            .await
            .map_err(|e| AnalysisError::LlmInference(e.to_string()))?;

        let extractor = build_result_extractor(self.model.clone());
        extractor
            .extract(&response)
            .await
            .map_err(AnalysisError::LlmInference)
    }
}

pub struct Analyzer {
    inner: Arc<dyn AnalyzeOrchestrate>,
    config: OrchestratorConfig,
}

impl std::fmt::Debug for Analyzer {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("Analyzer").finish_non_exhaustive()
    }
}

macro_rules! make_orchestrate {
    ($client:expr, $model:expr) => {
        Arc::new(OrchestrateImpl {
            model: $client.completion_model($model),
        })
    };
}

impl Analyzer {
    pub fn new(config: &ExtractionProviderConfig) -> Result<Self> {
        let inner: Arc<dyn AnalyzeOrchestrate> = match config {
            ExtractionProviderConfig::OpenRouter {
                model, api_key_env, ..
            } => {
                let api_key = get_env_var(api_key_env)?;
                let client: openrouter::Client = openrouter::Client::new(&api_key)
                    .map_err(|e| client_error("OpenRouter", e))?;
                let completion_model = client
                    .completion_model(model)
                    .with_strict_tools();
                Arc::new(OrchestrateImpl {
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
                make_orchestrate!(client, model)
            }
            ExtractionProviderConfig::OpenAI {
                model, api_key_env, ..
            } => {
                let api_key = get_env_var(api_key_env)?;
                let client: openai::Client = openai::Client::new(&api_key)
                    .map_err(|e| client_error("OpenAI", e))?;
                make_orchestrate!(client, model)
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
                make_orchestrate!(client, model)
            }
            ExtractionProviderConfig::Gemini {
                model, api_key_env, ..
            } => {
                let api_key = get_env_var(api_key_env)?;
                let client: gemini::Client = gemini::Client::new(&api_key)
                    .map_err(|e| client_error("Gemini", e))?;
                make_orchestrate!(client, model)
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

    pub async fn analyze(&self, path: &Path) -> Result<AnalysisReport> {
        if !path.exists() {
            return Err(AnalysisError::InvalidPath(format!(
                "Path does not exist: {}",
                path.display()
            )));
        }

        let start = Instant::now();
        let mut report = AnalysisReport::new(path.to_path_buf());

        let root = if path.is_file() {
            path.parent()
                .ok_or_else(|| {
                    AnalysisError::InvalidPath("Cannot determine parent directory".to_string())
                })?
                .to_path_buf()
        } else {
            path.to_path_buf()
        };

        let ctx = Arc::new(ToolContext::new(&root)?);

        let entries = ctx.list_directory(".")?;
        if entries.is_empty() {
            report.warnings.push("No source code found to analyze".to_string());
            return Ok(report);
        }

        info!("Running orchestrator analysis on {}", path.display());
        match self.inner.orchestrate(ctx, &self.config).await {
            Ok(result) => apply_result(&mut report, result),
            Err(e) => {
                debug!(error = %e, "Orchestrator analysis failed");
                report.warnings.push(format!("Analysis failed: {}", e));
            }
        }

        report.metadata.duration_ms = start.elapsed().as_millis() as u64;
        Ok(report)
    }
}

fn apply_result(report: &mut AnalysisReport, result: OrchestratorResult) {
    report.inferred_capabilities = result
        .capabilities
        .into_iter()
        .map(|c| InferredCapability {
            name: c.name,
            confidence: c.confidence,
            evidence: c.evidence,
        })
        .collect();

    report.security_findings = result
        .security_findings
        .into_iter()
        .map(|f| SecurityFinding {
            severity: parse_severity(&f.severity),
            category: f.category,
            file: f.file,
            line: f.line,
            evidence: f.evidence,
            explanation: f.explanation,
        })
        .collect();

    report.warnings = result.warnings;
    report.metadata.files_explored = result.files_explored.into_iter().map(PathBuf::from).collect();
    report.metadata.specialists_invoked =
        vec!["security".to_string(), "capability".to_string()];
}

fn parse_severity(s: &str) -> FindingSeverity {
    match s.to_lowercase().as_str() {
        "critical" => FindingSeverity::Critical,
        "high" => FindingSeverity::High,
        "medium" => FindingSeverity::Medium,
        _ => FindingSeverity::Low,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::orchestrator::OrchestratorResult;
    use crate::specialists::{CapabilityEntryResult, SecurityFindingEntry};
    use argus_config::ExtractionProviderConfig;

    #[test]
    fn parse_severity_all_levels() {
        assert_eq!(parse_severity("low"), FindingSeverity::Low);
        assert_eq!(parse_severity("medium"), FindingSeverity::Medium);
        assert_eq!(parse_severity("high"), FindingSeverity::High);
        assert_eq!(parse_severity("critical"), FindingSeverity::Critical);
    }

    #[test]
    fn parse_severity_case_insensitive() {
        assert_eq!(parse_severity("HIGH"), FindingSeverity::High);
        assert_eq!(parse_severity("Critical"), FindingSeverity::Critical);
    }

    #[test]
    fn parse_severity_unknown_defaults_to_low() {
        assert_eq!(parse_severity("unknown"), FindingSeverity::Low);
        assert_eq!(parse_severity(""), FindingSeverity::Low);
    }

    #[test]
    fn apply_result_maps_capabilities() {
        let mut report = AnalysisReport::new(PathBuf::from("/test"));
        let result = OrchestratorResult {
            capabilities: vec![CapabilityEntryResult {
                name: "filesystem_read".to_string(),
                confidence: 0.9,
                evidence: "fs.readFile".to_string(),
            }],
            security_findings: vec![],
            warnings: vec![],
            files_explored: vec![],
        };

        apply_result(&mut report, result);
        assert_eq!(report.inferred_capabilities.len(), 1);
        assert_eq!(report.inferred_capabilities[0].name, "filesystem_read");
        assert_eq!(report.inferred_capabilities[0].confidence, 0.9);
    }

    #[test]
    fn apply_result_maps_security_findings() {
        let mut report = AnalysisReport::new(PathBuf::from("/test"));
        let result = OrchestratorResult {
            capabilities: vec![],
            security_findings: vec![SecurityFindingEntry {
                severity: "high".to_string(),
                category: "command_injection".to_string(),
                file: "index.js".to_string(),
                line: Some(42),
                evidence: "exec(input)".to_string(),
                explanation: "User input flows to exec".to_string(),
            }],
            warnings: vec![],
            files_explored: vec![],
        };

        apply_result(&mut report, result);
        assert_eq!(report.security_findings.len(), 1);
        assert_eq!(report.security_findings[0].severity, FindingSeverity::High);
        assert_eq!(report.security_findings[0].category, "command_injection");
        assert_eq!(report.security_findings[0].line, Some(42));
    }

    #[test]
    fn apply_result_maps_metadata() {
        let mut report = AnalysisReport::new(PathBuf::from("/test"));
        let result = OrchestratorResult {
            capabilities: vec![],
            security_findings: vec![],
            warnings: vec!["danger".to_string()],
            files_explored: vec!["src/main.js".to_string(), "package.json".to_string()],
        };

        apply_result(&mut report, result);
        assert_eq!(report.warnings, vec!["danger"]);
        assert_eq!(report.metadata.files_explored.len(), 2);
        assert_eq!(
            report.metadata.specialists_invoked,
            vec!["security", "capability"]
        );
    }

    #[test]
    fn apply_result_handles_empty() {
        let mut report = AnalysisReport::new(PathBuf::from("/test"));
        let result = OrchestratorResult {
            capabilities: vec![],
            security_findings: vec![],
            warnings: vec![],
            files_explored: vec![],
        };

        apply_result(&mut report, result);
        assert!(report.inferred_capabilities.is_empty());
        assert!(report.security_findings.is_empty());
    }

    #[tokio::test]
    async fn analyze_rejects_missing_path() {
        let config = ExtractionProviderConfig::Ollama {
            model: "llama3.2:3b".to_string(),
            base_url: "http://localhost:11434".to_string(),
            timeout_ms: 5000,
        };
        let analyzer = Analyzer::new(&config).unwrap();
        let result = analyzer.analyze(Path::new("/nonexistent/path/12345")).await;

        assert!(result.is_err());
        assert!(matches!(result.unwrap_err(), AnalysisError::InvalidPath(_)));
    }

    #[tokio::test]
    async fn analyze_with_mock_orchestrator() {
        struct MockOrchestrate;

        #[async_trait]
        impl AnalyzeOrchestrate for MockOrchestrate {
            async fn orchestrate(
                &self,
                _ctx: Arc<ToolContext>,
                _config: &OrchestratorConfig,
            ) -> Result<OrchestratorResult> {
                Ok(OrchestratorResult {
                    capabilities: vec![CapabilityEntryResult {
                        name: "network_egress".to_string(),
                        confidence: 0.8,
                        evidence: "fetch() call".to_string(),
                    }],
                    security_findings: vec![],
                    warnings: vec![],
                    files_explored: vec!["index.js".to_string()],
                })
            }
        }

        let analyzer = Analyzer {
            inner: Arc::new(MockOrchestrate),
            config: OrchestratorConfig::default(),
        };

        let temp_dir = tempfile::TempDir::new().unwrap();
        std::fs::write(temp_dir.path().join("index.js"), "fetch('http://example.com')").unwrap();
        let report = analyzer.analyze(temp_dir.path()).await.unwrap();

        assert_eq!(report.inferred_capabilities.len(), 1);
        assert_eq!(report.inferred_capabilities[0].name, "network_egress");
    }

    #[tokio::test]
    async fn analyze_handles_orchestrator_failure() {
        struct FailingOrchestrate;

        #[async_trait]
        impl AnalyzeOrchestrate for FailingOrchestrate {
            async fn orchestrate(
                &self,
                _ctx: Arc<ToolContext>,
                _config: &OrchestratorConfig,
            ) -> Result<OrchestratorResult> {
                Err(AnalysisError::LlmInference("model timeout".to_string()))
            }
        }

        let analyzer = Analyzer {
            inner: Arc::new(FailingOrchestrate),
            config: OrchestratorConfig::default(),
        };

        let temp_dir = tempfile::TempDir::new().unwrap();
        std::fs::write(temp_dir.path().join("main.py"), "import os").unwrap();
        let report = analyzer.analyze(temp_dir.path()).await.unwrap();

        assert!(report
            .warnings
            .iter()
            .any(|w| w.contains("model timeout")));
        assert!(report.inferred_capabilities.is_empty());
    }

    #[test]
    fn new_with_ollama_config() {
        let config = ExtractionProviderConfig::Ollama {
            model: "llama3.2:3b".to_string(),
            base_url: "http://localhost:11434".to_string(),
            timeout_ms: 5000,
        };
        let analyzer = Analyzer::new(&config);
        assert!(analyzer.is_ok());
    }

    #[test]
    fn new_fails_without_env_var() {
        let config = ExtractionProviderConfig::OpenAI {
            model: "gpt-4".to_string(),
            api_key_env: "NONEXISTENT_KEY_99999".to_string(),
            timeout_ms: 5000,
        };
        let result = Analyzer::new(&config);
        assert!(result.is_err());
    }

    #[test]
    fn with_orchestrator_config_overrides_defaults() {
        let config = ExtractionProviderConfig::Ollama {
            model: "llama3.2:3b".to_string(),
            base_url: "http://localhost:11434".to_string(),
            timeout_ms: 5000,
        };
        let analyzer = Analyzer::new(&config)
            .unwrap()
            .with_orchestrator_config(OrchestratorConfig {
                max_turns: 30,
                max_tokens: 100_000,
            });
        assert_eq!(analyzer.config.max_turns, 30);
        assert_eq!(analyzer.config.max_tokens, 100_000);
    }

    #[test]
    fn analyzer_debug_format() {
        let config = ExtractionProviderConfig::Ollama {
            model: "llama3.2:3b".to_string(),
            base_url: "http://localhost:11434".to_string(),
            timeout_ms: 5000,
        };
        let analyzer = Analyzer::new(&config).unwrap();
        let debug_str = format!("{:?}", analyzer);
        assert!(debug_str.contains("Analyzer"));
    }
}
