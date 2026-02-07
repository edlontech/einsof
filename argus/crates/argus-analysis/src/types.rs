use serde::{Deserialize, Serialize};
use std::path::PathBuf;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum FindingSeverity {
    Low,
    Medium,
    High,
    Critical,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SecurityFinding {
    pub severity: FindingSeverity,
    pub category: String,
    pub file: String,
    pub line: Option<u32>,
    pub evidence: String,
    pub explanation: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DependencyFinding {
    pub package: String,
    pub severity: FindingSeverity,
    pub advisory: Option<String>,
    pub recommendation: String,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct AnalysisMetadata {
    pub files_explored: Vec<PathBuf>,
    pub orchestrator_turns: u32,
    pub specialists_invoked: Vec<String>,
    pub total_llm_calls: u32,
    pub duration_ms: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InferredCapability {
    pub name: String,
    pub confidence: f32,
    pub evidence: String,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct AnalysisReport {
    pub path: PathBuf,
    pub inferred_capabilities: Vec<InferredCapability>,
    pub security_findings: Vec<SecurityFinding>,
    pub dependency_findings: Vec<DependencyFinding>,
    pub warnings: Vec<String>,
    pub approved: bool,
    pub metadata: AnalysisMetadata,
}

impl AnalysisReport {
    pub fn new(path: PathBuf) -> Self {
        Self {
            path,
            ..Default::default()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn inferred_capability_serializes() {
        let cap = InferredCapability {
            name: "filesystem_write".to_string(),
            confidence: 0.95,
            evidence: "Uses fs.writeFile".to_string(),
        };
        let json = serde_json::to_string(&cap).unwrap();
        assert!(json.contains("filesystem_write"));
        assert!(json.contains("0.95"));
    }

    #[test]
    fn security_finding_serializes() {
        let finding = SecurityFinding {
            severity: FindingSeverity::High,
            category: "command_injection".to_string(),
            file: "index.js".to_string(),
            line: Some(47),
            evidence: "exec(user_input)".to_string(),
            explanation: "User input flows to exec".to_string(),
        };
        let json = serde_json::to_string(&finding).unwrap();
        assert!(json.contains("command_injection"));
        assert!(json.contains("47"));
    }

    #[test]
    fn dependency_finding_serializes() {
        let finding = DependencyFinding {
            package: "lodash".to_string(),
            severity: FindingSeverity::Medium,
            advisory: Some("CVE-2021-23337".to_string()),
            recommendation: "Upgrade to 4.17.21".to_string(),
        };
        let json = serde_json::to_string(&finding).unwrap();
        assert!(json.contains("lodash"));
        assert!(json.contains("CVE-2021-23337"));
    }

    #[test]
    fn finding_severity_ordering() {
        assert!(FindingSeverity::Critical > FindingSeverity::High);
        assert!(FindingSeverity::High > FindingSeverity::Medium);
        assert!(FindingSeverity::Medium > FindingSeverity::Low);
    }

    #[test]
    fn analysis_metadata_default() {
        let meta = AnalysisMetadata::default();
        assert_eq!(meta.orchestrator_turns, 0);
        assert!(meta.files_explored.is_empty());
        assert!(meta.specialists_invoked.is_empty());
    }

    #[test]
    fn report_with_security_findings() {
        let mut report = AnalysisReport::new(PathBuf::from("/test"));
        report.security_findings.push(SecurityFinding {
            severity: FindingSeverity::Critical,
            category: "rce".to_string(),
            file: "main.js".to_string(),
            line: None,
            evidence: "eval()".to_string(),
            explanation: "Remote code execution".to_string(),
        });
        assert!(!report.security_findings.is_empty());
    }
}
