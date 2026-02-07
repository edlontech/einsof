mod analyzer;
mod delegation;
mod dep_audit;
mod error;
mod install_detect;
mod orchestrator;
mod sandbox;
mod specialists;
mod tools;
mod registry_analysis;
mod registry_extraction;
mod registry_types;
mod types;

pub use analyzer::Analyzer;
pub use error::{AnalysisError, Result};
pub use orchestrator::{OrchestratorConfig, OrchestratorResult};
pub use dep_audit::{audit_dependencies, parse_dependencies, ParsedDependency};
pub use install_detect::detect_install;
pub use registry_analysis::RegistryAnalyzer;
pub use registry_extraction::RegistryCapabilityResult;
pub use registry_types::{
    CapabilityFinding, DependencyReport, DependencyVulnerability, Evidence,
    FlaggedDependency, InstallDetection, RegistryAnalysisReport,
};
pub use sandbox::{DirEntry, ManifestKind, SearchResult, ToolContext};
pub use types::{
    AnalysisMetadata, AnalysisReport, DependencyFinding, FindingSeverity,
    InferredCapability, SecurityFinding,
};
