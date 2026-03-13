mod analyzer;
mod delegation;
mod dep_audit;
mod error;
mod install_detect;
mod orchestrator;
mod registry_analysis;
mod registry_extraction;
mod registry_types;
mod sandbox;
mod specialists;
mod tools;
mod types;

pub use analyzer::Analyzer;
pub use dep_audit::{ParsedDependency, audit_dependencies, parse_dependencies};
pub use error::{AnalysisError, Result};
pub use install_detect::detect_install;
pub use orchestrator::{OrchestratorConfig, OrchestratorResult};
pub use registry_analysis::RegistryAnalyzer;
pub use registry_extraction::RegistryCapabilityResult;
pub use registry_types::{
    CapabilityFinding, DependencyReport, DependencyVulnerability, Evidence, FlaggedDependency,
    InstallDetection, RegistryAnalysisReport,
};
pub use sandbox::{DirEntry, ManifestKind, SearchResult, ToolContext};
pub use types::{
    AnalysisMetadata, AnalysisReport, DependencyFinding, FindingSeverity, InferredCapability,
    SecurityFinding,
};
