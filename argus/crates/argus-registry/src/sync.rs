use crate::toml_loader::{TomlRegistry, TomlRegistryError};
use crate::toml_types::{McpEntry, SkillEntry};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::Path;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct RegistrySource {
    pub url: String,
    pub priority: u32,
    pub last_synced: Option<chrono::DateTime<chrono::Utc>>,
}

pub struct MultiRegistry {
    local: TomlRegistry,
    external: Vec<(RegistrySource, TomlRegistry)>,
}

impl MultiRegistry {
    pub fn new(local: TomlRegistry) -> Self {
        Self {
            local,
            external: Vec::new(),
        }
    }

    pub fn add_external(&mut self, source: RegistrySource, registry: TomlRegistry) {
        self.external.push((source, registry));
        self.external.sort_by_key(|(s, _)| s.priority);
    }

    pub fn resolve_mcp(&self, name: &str) -> Option<&McpEntry> {
        if let Some(entry) = self.local.mcps.get(name) {
            return Some(entry);
        }
        for (_, registry) in &self.external {
            if let Some(entry) = registry.mcps.get(name) {
                return Some(entry);
            }
        }
        None
    }

    pub fn resolve_skill(&self, name: &str) -> Option<&SkillEntry> {
        if let Some(entry) = self.local.skills.get(name) {
            return Some(entry);
        }
        for (_, registry) in &self.external {
            if let Some(entry) = registry.skills.get(name) {
                return Some(entry);
            }
        }
        None
    }

    pub fn all_mcps(&self) -> HashMap<&str, &McpEntry> {
        let mut merged = HashMap::new();
        for (_, registry) in self.external.iter().rev() {
            for (name, entry) in &registry.mcps {
                merged.insert(name.as_str(), entry);
            }
        }
        for (name, entry) in &self.local.mcps {
            merged.insert(name.as_str(), entry);
        }
        merged
    }

    pub fn all_skills(&self) -> HashMap<&str, &SkillEntry> {
        let mut merged = HashMap::new();
        for (_, registry) in self.external.iter().rev() {
            for (name, entry) in &registry.skills {
                merged.insert(name.as_str(), entry);
            }
        }
        for (name, entry) in &self.local.skills {
            merged.insert(name.as_str(), entry);
        }
        merged
    }

    pub fn sync_external_from_dir(
        base: &Path,
        source: &RegistrySource,
    ) -> Result<TomlRegistry, TomlRegistryError> {
        let hash = simple_hash(&source.url);
        let dir = TomlRegistry::dir_for_source(base, &hash);
        TomlRegistry::load_from_dir(&dir)
    }
}

pub fn simple_hash(input: &str) -> String {
    use sha2::{Digest, Sha256};
    let hash = Sha256::digest(input.as_bytes());
    hex::encode(&hash[..16])
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

    fn mcp_toml(name: &str, integrity: &str) -> String {
        format!(
            r#"
[metadata]
name = "{name}"
description = "Test MCP {name}"
source = "community"
integrity = "{integrity}"
capabilities = ["filesystem:read"]

[install]
type = "npm"
package = "@test/{name}"
version = "1.0.0"
"#
        )
    }

    fn skill_toml(name: &str) -> String {
        format!(
            r#"
[metadata]
name = "{name}"
description = "Test skill {name}"
tools_used = ["read_file"]
"#
        )
    }

    fn make_registry(dir: &TempDir, mcps: &[(&str, &str)], skills: &[&str]) -> TomlRegistry {
        for (name, integrity) in mcps {
            write_fixture(
                dir.path(),
                &format!("mcps/{name}.toml"),
                &mcp_toml(name, integrity),
            );
        }
        for name in skills {
            write_fixture(
                dir.path(),
                &format!("skills/{name}.toml"),
                &skill_toml(name),
            );
        }
        TomlRegistry::load_from_dir(dir.path()).unwrap()
    }

    #[test]
    fn local_wins_over_external() {
        let local_dir = TempDir::new().unwrap();
        let ext_dir = TempDir::new().unwrap();

        let local = make_registry(&local_dir, &[("test-mcp", "untrusted")], &[]);
        let external = make_registry(&ext_dir, &[("test-mcp", "verified")], &[]);

        let mut multi = MultiRegistry::new(local);
        multi.add_external(
            RegistrySource {
                url: "https://example.com/reg".to_string(),
                priority: 1,
                last_synced: None,
            },
            external,
        );

        let resolved = multi.resolve_mcp("test-mcp").unwrap();
        assert_eq!(resolved.metadata.integrity, "untrusted");
    }

    #[test]
    fn lower_priority_external_wins() {
        let local_dir = TempDir::new().unwrap();
        let ext1_dir = TempDir::new().unwrap();
        let ext2_dir = TempDir::new().unwrap();

        let local = make_registry(&local_dir, &[], &[]);
        let ext1 = make_registry(&ext1_dir, &[("test-mcp", "observed")], &[]);
        let ext2 = make_registry(&ext2_dir, &[("test-mcp", "verified")], &[]);

        let mut multi = MultiRegistry::new(local);
        multi.add_external(
            RegistrySource {
                url: "https://example.com/primary".to_string(),
                priority: 1,
                last_synced: None,
            },
            ext1,
        );
        multi.add_external(
            RegistrySource {
                url: "https://example.com/secondary".to_string(),
                priority: 10,
                last_synced: None,
            },
            ext2,
        );

        let resolved = multi.resolve_mcp("test-mcp").unwrap();
        assert_eq!(resolved.metadata.integrity, "observed");
    }

    #[test]
    fn all_mcps_merges_with_dedup() {
        let local_dir = TempDir::new().unwrap();
        let ext_dir = TempDir::new().unwrap();

        let local = make_registry(
            &local_dir,
            &[("local-only", "untrusted"), ("shared", "untrusted")],
            &[],
        );
        let external = make_registry(
            &ext_dir,
            &[("ext-only", "observed"), ("shared", "verified")],
            &[],
        );

        let mut multi = MultiRegistry::new(local);
        multi.add_external(
            RegistrySource {
                url: "https://example.com".to_string(),
                priority: 1,
                last_synced: None,
            },
            external,
        );

        let all = multi.all_mcps();
        assert_eq!(all.len(), 3);
        assert_eq!(all["shared"].metadata.integrity, "untrusted");
        assert_eq!(all["ext-only"].metadata.integrity, "observed");
        assert_eq!(all["local-only"].metadata.integrity, "untrusted");
    }

    #[test]
    fn resolve_missing_returns_none() {
        let local_dir = TempDir::new().unwrap();
        let local = make_registry(&local_dir, &[], &[]);
        let multi = MultiRegistry::new(local);
        assert!(multi.resolve_mcp("nonexistent").is_none());
        assert!(multi.resolve_skill("nonexistent").is_none());
    }

    #[test]
    fn skill_resolution_works() {
        let local_dir = TempDir::new().unwrap();
        let local = make_registry(&local_dir, &[], &["deploy"]);
        let multi = MultiRegistry::new(local);

        let resolved = multi.resolve_skill("deploy").unwrap();
        assert_eq!(resolved.metadata.name, "deploy");
    }
}
