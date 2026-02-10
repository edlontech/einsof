use argus_kernel::CapKind;
use schemars::JsonSchema;
use serde::{Deserialize, Serialize};

pub const SECURITY_PREAMBLE: &str = r#"You are a security specialist analyzing source code for vulnerabilities and risks.

Focus on:
- Injection vectors: command injection (exec, spawn, system), SQL injection, XSS, template injection
- Dangerous data flows: user input reaching exec/eval/spawn, unsanitized path construction
- Credential exposure: hardcoded secrets, API keys in source, insecure storage
- File system risks: path traversal, arbitrary file write, symlink attacks
- Network risks: SSRF, open redirects, insecure TLS configuration
- Deserialization: unsafe deserialization of untrusted data (pickle, yaml.load, JSON.parse with eval)
- Privilege escalation: setuid, capability manipulation, sudo invocation

For each finding, provide:
- Severity: low, medium, high, or critical
- Category: a short label (e.g. "command_injection", "path_traversal", "hardcoded_secret")
- The exact file and line where the issue occurs
- Evidence: the specific code snippet
- Explanation: why this is a risk and how it could be exploited

Be precise. Only report findings you have concrete evidence for."#;

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[schemars(description = "Result of security analysis on source code")]
pub struct SecurityExtractionResult {
    #[schemars(description = "List of security findings with severity, evidence, and explanation")]
    pub findings: Vec<SecurityFindingEntry>,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[schemars(inline)]
pub struct SecurityFindingEntry {
    #[schemars(description = "Severity: low, medium, high, or critical")]
    pub severity: String,
    #[schemars(description = "Short category label (e.g. command_injection, path_traversal)")]
    pub category: String,
    #[schemars(description = "File path where the finding occurs")]
    pub file: String,
    #[schemars(description = "Line number if known")]
    pub line: Option<u32>,
    #[schemars(description = "The specific code snippet as evidence")]
    pub evidence: String,
    #[schemars(description = "Why this is a risk and how it could be exploited")]
    pub explanation: String,
}

fn build_file_prompt(header: &str, files: &[(String, String)], context: &str) -> String {
    let mut prompt = String::from(header);
    prompt.push_str("\n\n");

    if !context.is_empty() {
        prompt.push_str(&format!("Context from orchestrator: {context}\n\n"));
    }

    for (path, content) in files {
        prompt.push_str(&format!("=== {path} ===\n{content}\n\n"));
    }

    prompt
}

pub fn build_security_prompt(files: &[(String, String)], context: &str) -> String {
    build_file_prompt(
        "Analyze these source files for security vulnerabilities.",
        files,
        context,
    )
}

pub fn format_capability_list() -> String {
    CapKind::all()
        .iter()
        .map(|k: &CapKind| format!("- {}", k.as_str()))
        .collect::<Vec<_>>()
        .join("\n")
}

pub fn build_capability_system_prompt() -> String {
    format!(
        r#"You are a capability analysis specialist inferring what permissions a tool or MCP requires.

Analyze the provided source code and determine what capabilities the tool needs.

Capability taxonomy:
{capabilities}

For each capability:
- Provide a confidence score (0.0-1.0) based on how certain the evidence is
- Cite specific code as evidence"#,
        capabilities = format_capability_list(),
    )
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[schemars(description = "Result of capability inference from source code")]
pub struct CapabilityExtractionResult {
    #[schemars(description = "List of inferred capabilities with confidence and evidence")]
    pub capabilities: Vec<CapabilityEntryResult>,
    #[schemars(description = "Security warnings or concerns")]
    pub warnings: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, JsonSchema)]
#[schemars(inline)]
pub struct CapabilityEntryResult {
    #[schemars(description = "Capability name from the taxonomy (e.g. filesystem_read, network_egress)")]
    pub name: String,
    #[schemars(description = "Confidence score from 0.0 to 1.0")]
    pub confidence: f32,
    #[schemars(description = "Code evidence supporting this capability")]
    pub evidence: String,
}

pub fn build_capability_prompt(files: &[(String, String)], context: &str) -> String {
    build_file_prompt(
        "Analyze these source files to infer required capabilities.",
        files,
        context,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn security_extraction_result_deserializes() {
        let json = r#"{
            "findings": [
                {
                    "severity": "high",
                    "category": "command_injection",
                    "file": "index.js",
                    "line": 47,
                    "evidence": "exec(req.body.cmd)",
                    "explanation": "User input passed to exec without sanitization"
                }
            ]
        }"#;
        let result: SecurityExtractionResult = serde_json::from_str(json).unwrap();
        assert_eq!(result.findings.len(), 1);
        assert_eq!(result.findings[0].category, "command_injection");
        assert_eq!(result.findings[0].severity, "high");
        assert_eq!(result.findings[0].line, Some(47));
    }

    #[test]
    fn security_extraction_empty_findings() {
        let json = r#"{"findings": []}"#;
        let result: SecurityExtractionResult = serde_json::from_str(json).unwrap();
        assert!(result.findings.is_empty());
    }

    #[test]
    fn capability_extraction_result_deserializes() {
        let json = r#"{
            "capabilities": [
                {"name": "network_egress", "confidence": 0.9, "evidence": "fetch() call in api.js:12"}
            ],
            "warnings": ["Makes external API calls to unknown domains"]
        }"#;
        let result: CapabilityExtractionResult = serde_json::from_str(json).unwrap();
        assert_eq!(result.capabilities.len(), 1);
        assert_eq!(result.capabilities[0].name, "network_egress");
        assert_eq!(result.warnings.len(), 1);
    }

    #[test]
    fn capability_extraction_empty() {
        let json = r#"{
            "capabilities": [],
            "warnings": []
        }"#;
        let result: CapabilityExtractionResult = serde_json::from_str(json).unwrap();
        assert!(result.capabilities.is_empty());
    }

    #[test]
    fn security_prompt_includes_context_and_files() {
        let files = vec![
            ("index.js".to_string(), "exec(input)".to_string()),
            ("util.js".to_string(), "spawn('sh')".to_string()),
        ];
        let prompt = build_security_prompt(&files, "Express server with exec calls");
        assert!(prompt.contains("index.js"));
        assert!(prompt.contains("exec(input)"));
        assert!(prompt.contains("util.js"));
        assert!(prompt.contains("spawn('sh')"));
        assert!(prompt.contains("Express server"));
    }

    #[test]
    fn security_prompt_handles_empty_context() {
        let files = vec![("main.py".to_string(), "os.system(cmd)".to_string())];
        let prompt = build_security_prompt(&files, "");
        assert!(!prompt.contains("Context from orchestrator"));
        assert!(prompt.contains("main.py"));
    }

    #[test]
    fn capability_prompt_includes_context_and_files() {
        let files = vec![(
            "main.py".to_string(),
            "import os\nos.environ['KEY']".to_string(),
        )];
        let prompt = build_capability_prompt(&files, "Python script reading env vars");
        assert!(prompt.contains("main.py"));
        assert!(prompt.contains("import os"));
        assert!(prompt.contains("Python script"));
    }

    #[test]
    fn capability_prompt_handles_empty_context() {
        let files = vec![("lib.rs".to_string(), "use std::fs;".to_string())];
        let prompt = build_capability_prompt(&files, "");
        assert!(!prompt.contains("Context from orchestrator"));
        assert!(prompt.contains("lib.rs"));
    }

    #[test]
    fn security_preamble_covers_key_categories() {
        assert!(SECURITY_PREAMBLE.contains("command injection"));
        assert!(SECURITY_PREAMBLE.contains("path traversal"));
        assert!(SECURITY_PREAMBLE.contains("SSRF"));
        assert!(SECURITY_PREAMBLE.contains("deserialization"));
        assert!(SECURITY_PREAMBLE.contains("Credential"));
    }

    #[test]
    fn capability_system_prompt_uses_kernel_capkinds() {
        let prompt = build_capability_system_prompt();
        assert!(prompt.contains("filesystem_read"));
        assert!(prompt.contains("filesystem_write"));
        assert!(prompt.contains("network_egress"));
        assert!(prompt.contains("execution_shell"));
        assert!(prompt.contains("credentials"));
        assert!(prompt.contains("database_read"));
    }

    #[test]
    fn format_capability_list_contains_all_capkinds() {
        let list = format_capability_list();
        for kind in CapKind::all() {
            assert!(
                list.contains(kind.as_str()),
                "Missing capability: {}",
                kind.as_str()
            );
        }
    }

    #[test]
    fn security_finding_entry_schema_generated() {
        let schema = schemars::schema_for!(SecurityExtractionResult);
        let json = serde_json::to_string(&schema).unwrap();
        assert!(json.contains("findings"));
        assert!(json.contains("severity"));
        assert!(json.contains("category"));
    }

    #[test]
    fn capability_extraction_schema_generated() {
        let schema = schemars::schema_for!(CapabilityExtractionResult);
        let json = serde_json::to_string(&schema).unwrap();
        assert!(json.contains("capabilities"));
        assert!(json.contains("warnings"));
    }
}
