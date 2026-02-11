use serde::{Deserialize, Serialize};

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct Evidence {
    pub file: String,
    pub line: usize,
    pub snippet: String,
    pub reasoning: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct CapabilityFinding {
    pub capability: String,
    pub evidence: Vec<Evidence>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DependencyVulnerability {
    pub package: String,
    pub id: String,
    pub severity: String,
    pub description: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct FlaggedDependency {
    pub package: String,
    pub reason: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DependencyReport {
    pub total: usize,
    pub vulnerabilities: Vec<DependencyVulnerability>,
    pub flagged: Vec<FlaggedDependency>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InstallDetection {
    pub method: String,
    pub package: String,
    pub version: String,
    pub source: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegistryAnalysisReport {
    pub tool: String,
    pub analyzed_at: String,
    pub pinned_ref: String,
    pub capabilities: Vec<CapabilityFinding>,
    pub dependencies: DependencyReport,
    pub install_detection: InstallDetection,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn capability_finding_serializes_to_json() {
        let finding = CapabilityFinding {
            capability: "network:egress(api.anthropic.com)".to_string(),
            evidence: vec![Evidence {
                file: "src/services/compress.ts".to_string(),
                line: 42,
                snippet: "const client = new Anthropic({apiKey})".to_string(),
                reasoning: "Instantiates Anthropic SDK client".to_string(),
            }],
        };
        let json = serde_json::to_string(&finding).unwrap();
        let deser: CapabilityFinding = serde_json::from_str(&json).unwrap();
        assert_eq!(deser.capability, "network:egress(api.anthropic.com)");
        assert_eq!(deser.evidence.len(), 1);
        assert_eq!(deser.evidence[0].line, 42);
    }

    #[test]
    fn registry_analysis_report_round_trips() {
        let report = RegistryAnalysisReport {
            tool: "claude-mem".to_string(),
            analyzed_at: "2026-03-02T12:00:00Z".to_string(),
            pinned_ref: "abc123".to_string(),
            capabilities: vec![],
            dependencies: DependencyReport {
                total: 0,
                vulnerabilities: vec![],
                flagged: vec![],
            },
            install_detection: InstallDetection {
                method: "npm".to_string(),
                package: "@thedotmack/claude-mem".to_string(),
                version: "1.0.0".to_string(),
                source: "package.json".to_string(),
            },
        };
        let json = serde_json::to_string_pretty(&report).unwrap();
        let deser: RegistryAnalysisReport = serde_json::from_str(&json).unwrap();
        assert_eq!(deser.tool, "claude-mem");
        assert_eq!(deser.install_detection.method, "npm");
    }

    #[test]
    fn dependency_report_with_vulnerabilities() {
        let report = DependencyReport {
            total: 28,
            vulnerabilities: vec![DependencyVulnerability {
                package: "lodash".to_string(),
                id: "CVE-2021-23337".to_string(),
                severity: "high".to_string(),
                description: "Prototype pollution".to_string(),
            }],
            flagged: vec![FlaggedDependency {
                package: "@anthropic-ai/claude-agent-sdk".to_string(),
                reason: "Network-capable SDK".to_string(),
            }],
        };
        let json = serde_json::to_string(&report).unwrap();
        let deser: DependencyReport = serde_json::from_str(&json).unwrap();
        assert_eq!(deser.total, 28);
        assert_eq!(deser.vulnerabilities.len(), 1);
        assert_eq!(deser.flagged.len(), 1);
    }
}
