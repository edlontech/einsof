use std::fs;
use std::path::Path;

use crate::toml_types::{McpArgs, McpEntry, McpMetadata, SandboxConfig};

pub struct AssemblyInput {
    pub name: String,
    pub description: String,
    pub repository: String,
    pub pinned_ref: String,
    pub track: bool,
    pub capabilities: Vec<String>,
    pub install: crate::toml_types::InstallConfig,
    pub sandbox: SandboxConfig,
}

pub fn assemble_mcp_entry(input: AssemblyInput) -> McpEntry {
    let source = match &input.install {
        crate::toml_types::InstallConfig::Npm { .. } => "npm",
        crate::toml_types::InstallConfig::Pip { .. } => "pip",
        crate::toml_types::InstallConfig::Cargo { .. } => "cargo",
        crate::toml_types::InstallConfig::Docker { .. } => "docker",
        crate::toml_types::InstallConfig::Binary { .. } => "binary",
    };

    McpEntry {
        metadata: McpMetadata {
            name: input.name,
            description: input.description,
            repository: Some(input.repository),
            source: source.to_string(),
            integrity: "untrusted".to_string(),
            capabilities: input.capabilities,
            schema_hash: None,
            pinned_ref: Some(input.pinned_ref),
            track: Some(input.track),
        },
        install: input.install,
        env: Default::default(),
        args: McpArgs { default: vec![] },
        sandbox: Some(input.sandbox),
        sidecars: vec![],
    }
}

pub fn write_registry_entry(
    registry_dir: &Path,
    name: &str,
    entry: &McpEntry,
    report_json: &str,
) -> std::io::Result<()> {
    let mcps_dir = registry_dir.join("mcps");
    fs::create_dir_all(&mcps_dir)?;

    let toml_content = toml::to_string_pretty(entry)
        .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;
    fs::write(mcps_dir.join(format!("{name}.toml")), toml_content)?;

    let reports_dir = registry_dir.join("reports");
    fs::create_dir_all(&reports_dir)?;
    fs::write(reports_dir.join(format!("{name}.json")), report_json)?;

    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::toml_types::{InstallConfig, SandboxNetPolicy};

    fn sample_input() -> AssemblyInput {
        AssemblyInput {
            name: "claude-mem".to_string(),
            description: "Persistent memory for Claude Code".to_string(),
            repository: "https://github.com/thedotmack/claude-mem".to_string(),
            pinned_ref: "abc123".to_string(),
            track: false,
            capabilities: vec![
                "filesystem:read(~/.claude-mem/)".to_string(),
                "network:egress(api.anthropic.com)".to_string(),
            ],
            install: InstallConfig::Npm {
                package: "@thedotmack/claude-mem".to_string(),
                version: "1.0.0".to_string(),
            },
            sandbox: SandboxConfig {
                extra_read: vec!["~/.claude-mem/".to_string()],
                extra_write: vec!["~/.claude-mem/".to_string()],
                require_sandbox: true,
                net_policy: Some(SandboxNetPolicy::EgressDomains(vec![
                    "api.anthropic.com".to_string(),
                ])),
            },
        }
    }

    #[test]
    fn assemble_mcp_entry_sets_untrusted_integrity() {
        let entry = assemble_mcp_entry(sample_input());
        assert_eq!(entry.metadata.integrity, "untrusted");
    }

    #[test]
    fn assemble_mcp_entry_sets_source_from_install() {
        let entry = assemble_mcp_entry(sample_input());
        assert_eq!(entry.metadata.source, "npm");
    }

    #[test]
    fn assemble_mcp_entry_preserves_pinned_ref() {
        let entry = assemble_mcp_entry(sample_input());
        assert_eq!(entry.metadata.pinned_ref.as_deref(), Some("abc123"));
        assert_eq!(entry.metadata.track, Some(false));
    }

    #[test]
    fn assembled_entry_serializes_to_valid_toml() {
        let entry = assemble_mcp_entry(sample_input());
        let toml_str = toml::to_string_pretty(&entry).unwrap();
        let deser: McpEntry = toml::from_str(&toml_str).unwrap();
        assert_eq!(deser.metadata.name, "claude-mem");
        assert_eq!(deser.metadata.capabilities.len(), 2);
    }

    #[test]
    fn write_registry_entry_creates_files() {
        let dir = tempfile::tempdir().unwrap();
        let entry = assemble_mcp_entry(sample_input());
        let report = r#"{"tool": "claude-mem"}"#;

        write_registry_entry(dir.path(), "claude-mem", &entry, report).unwrap();

        assert!(dir.path().join("mcps/claude-mem.toml").exists());
        assert!(dir.path().join("reports/claude-mem.json").exists());

        let toml_content = fs::read_to_string(dir.path().join("mcps/claude-mem.toml")).unwrap();
        let loaded: McpEntry = toml::from_str(&toml_content).unwrap();
        assert_eq!(loaded.metadata.name, "claude-mem");
    }
}
