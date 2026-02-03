use crate::toml_types::{CapabilityTaxonomy, McpEntry, SkillEntry, validate_sidecars};
use std::collections::HashMap;
use std::path::{Path, PathBuf};

#[derive(Debug)]
pub struct TomlRegistry {
    pub mcps: HashMap<String, McpEntry>,
    pub skills: HashMap<String, SkillEntry>,
    pub taxonomy: Option<CapabilityTaxonomy>,
}

#[derive(Debug, thiserror::Error)]
pub enum TomlRegistryError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("TOML parse error in {file}: {source}")]
    Parse {
        file: String,
        source: toml::de::Error,
    },
    #[error("Registry directory not found: {0}")]
    NotFound(String),
    #[error("Validation error in {file}: {reason}")]
    Validation { file: String, reason: String },
}

impl TomlRegistry {
    pub fn empty() -> Self {
        Self {
            mcps: HashMap::new(),
            skills: HashMap::new(),
            taxonomy: None,
        }
    }

    pub fn load_from_dir(dir: &Path) -> Result<Self, TomlRegistryError> {
        if !dir.is_dir() {
            return Err(TomlRegistryError::NotFound(dir.display().to_string()));
        }

        let mcps = Self::load_entries::<McpEntry>(&dir.join("mcps"))?;

        for (name, entry) in &mcps {
            validate_sidecars(&entry.sidecars).map_err(|e| TomlRegistryError::Validation {
                file: name.clone(),
                reason: e.to_string(),
            })?;
        }

        let skills = Self::load_entries::<SkillEntry>(&dir.join("skills"))?;
        let taxonomy = Self::load_taxonomy(&dir.join("capabilities"))?;

        Ok(Self {
            mcps,
            skills,
            taxonomy,
        })
    }

    pub fn load_mcp(path: &Path) -> Result<McpEntry, TomlRegistryError> {
        let entry: McpEntry = Self::load_single(path)?;
        validate_sidecars(&entry.sidecars).map_err(|e| TomlRegistryError::Validation {
            file: path.display().to_string(),
            reason: e.to_string(),
        })?;
        Ok(entry)
    }

    pub fn load_skill(path: &Path) -> Result<SkillEntry, TomlRegistryError> {
        Self::load_single(path)
    }

    fn load_single<T: serde::de::DeserializeOwned>(path: &Path) -> Result<T, TomlRegistryError> {
        let content = std::fs::read_to_string(path)?;
        toml::from_str(&content).map_err(|source| TomlRegistryError::Parse {
            file: path.display().to_string(),
            source,
        })
    }

    fn load_entries<T: serde::de::DeserializeOwned>(
        dir: &Path,
    ) -> Result<HashMap<String, T>, TomlRegistryError> {
        let mut entries = HashMap::new();
        if !dir.is_dir() {
            return Ok(entries);
        }

        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let path = entry.path();
            if path.extension().is_none_or(|e| e != "toml") {
                continue;
            }
            let name = path
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or_default()
                .to_string();
            let parsed: T = Self::load_single(&path)?;
            entries.insert(name, parsed);
        }

        Ok(entries)
    }

    fn load_taxonomy(dir: &Path) -> Result<Option<CapabilityTaxonomy>, TomlRegistryError> {
        let taxonomy_path = dir.join("taxonomy.toml");
        if !taxonomy_path.exists() {
            return Ok(None);
        }
        Self::load_single(&taxonomy_path).map(Some)
    }

    pub fn dir_for_source(base: &Path, source_name: &str) -> PathBuf {
        base.join("registries").join(source_name)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    fn write_fixture(dir: &Path, rel_path: &str, content: &str) {
        let full = dir.join(rel_path);
        if let Some(parent) = full.parent() {
            std::fs::create_dir_all(parent).unwrap();
        }
        std::fs::write(full, content).unwrap();
    }

    const MCP_TOML: &str = r#"
[metadata]
name = "test-mcp"
description = "A test MCP"
source = "community"
integrity = "observed"
capabilities = ["filesystem:read"]

[install]
type = "npm"
package = "@test/mcp"
version = "1.0.0"
"#;

    const SKILL_TOML: &str = r#"
[metadata]
name = "test-skill"
description = "A test skill"
tools_used = ["read_file", "write_file"]
capabilities = ["filesystem:read", "filesystem:write"]
"#;

    const TAXONOMY_TOML: &str = r#"
[capabilities.filesystem_read]
description = "Read files"
scope_type = "path_glob"

[integrity_levels.untrusted]
description = "Unvetted"
level = 1
"#;

    #[test]
    fn load_from_dir_with_mcps_and_skills() {
        let tmp = TempDir::new().unwrap();
        write_fixture(tmp.path(), "mcps/test-mcp.toml", MCP_TOML);
        write_fixture(tmp.path(), "skills/test-skill.toml", SKILL_TOML);

        let registry = TomlRegistry::load_from_dir(tmp.path()).unwrap();
        assert_eq!(registry.mcps.len(), 1);
        assert_eq!(registry.skills.len(), 1);
        assert!(registry.mcps.contains_key("test-mcp"));
        assert!(registry.skills.contains_key("test-skill"));
        assert_eq!(registry.mcps["test-mcp"].metadata.name, "test-mcp");
        assert_eq!(registry.skills["test-skill"].metadata.name, "test-skill");
    }

    #[test]
    fn load_from_dir_with_taxonomy() {
        let tmp = TempDir::new().unwrap();
        write_fixture(tmp.path(), "capabilities/taxonomy.toml", TAXONOMY_TOML);

        let registry = TomlRegistry::load_from_dir(tmp.path()).unwrap();
        let taxonomy = registry.taxonomy.unwrap();
        assert_eq!(taxonomy.capabilities.len(), 1);
        assert_eq!(taxonomy.integrity_levels.len(), 1);
    }

    #[test]
    fn load_from_dir_empty() {
        let tmp = TempDir::new().unwrap();
        let registry = TomlRegistry::load_from_dir(tmp.path()).unwrap();
        assert!(registry.mcps.is_empty());
        assert!(registry.skills.is_empty());
        assert!(registry.taxonomy.is_none());
    }

    #[test]
    fn load_from_missing_dir_returns_error() {
        let result = TomlRegistry::load_from_dir(Path::new("/nonexistent/path"));
        assert!(result.is_err());
        match result.unwrap_err() {
            TomlRegistryError::NotFound(path) => {
                assert!(path.contains("nonexistent"));
            }
            other => panic!("Expected NotFound, got: {other}"),
        }
    }

    #[test]
    fn load_malformed_toml_returns_parse_error() {
        let tmp = TempDir::new().unwrap();
        write_fixture(tmp.path(), "mcps/bad.toml", "this is not valid toml [[[");

        let result = TomlRegistry::load_from_dir(tmp.path());
        assert!(result.is_err());
        match result.unwrap_err() {
            TomlRegistryError::Parse { file, .. } => {
                assert!(file.contains("bad.toml"));
            }
            other => panic!("Expected Parse error, got: {other}"),
        }
    }

    #[test]
    fn load_single_mcp() {
        let tmp = TempDir::new().unwrap();
        let mcp_path = tmp.path().join("test.toml");
        std::fs::write(&mcp_path, MCP_TOML).unwrap();

        let entry = TomlRegistry::load_mcp(&mcp_path).unwrap();
        assert_eq!(entry.metadata.name, "test-mcp");
    }

    #[test]
    fn load_single_skill() {
        let tmp = TempDir::new().unwrap();
        let skill_path = tmp.path().join("test.toml");
        std::fs::write(&skill_path, SKILL_TOML).unwrap();

        let entry = TomlRegistry::load_skill(&skill_path).unwrap();
        assert_eq!(entry.metadata.name, "test-skill");
    }

    #[test]
    fn non_toml_files_are_ignored() {
        let tmp = TempDir::new().unwrap();
        write_fixture(tmp.path(), "mcps/test-mcp.toml", MCP_TOML);
        write_fixture(tmp.path(), "mcps/readme.md", "# Not a TOML file");
        write_fixture(tmp.path(), "mcps/.hidden", "hidden file");

        let registry = TomlRegistry::load_from_dir(tmp.path()).unwrap();
        assert_eq!(registry.mcps.len(), 1);
    }

    #[test]
    fn load_mcp_with_invalid_sidecar_returns_validation_error() {
        let toml_str = r#"
[metadata]
name = "bad-sidecar"
description = "MCP with invalid sidecar"
source = "community"
integrity = "observed"
capabilities = []

[install]
type = "binary"
url = "builtin"
checksum = "builtin"

[[sidecar]]
name = "broken-daemon"
command = "some-daemon"
lifecycle = "daemon"
"#;
        let tmp = TempDir::new().unwrap();
        write_fixture(tmp.path(), "mcps/bad-sidecar.toml", toml_str);

        let result = TomlRegistry::load_from_dir(tmp.path());
        assert!(result.is_err());
        match result.unwrap_err() {
            TomlRegistryError::Validation { file, reason } => {
                assert_eq!(file, "bad-sidecar");
                assert!(reason.contains("must have a ready_check"));
            }
            other => panic!("Expected Validation error, got: {other}"),
        }
    }
}
