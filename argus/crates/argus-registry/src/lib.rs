mod argus_db;
mod assembler;
mod binding;
mod hash;
mod installer;
mod policy_attestation;
mod quarantine;
pub mod resolver;
mod sandbox_gen;
pub mod sync;
pub mod toml_loader;
pub mod toml_types;
mod trust_event;
mod types;
mod watcher;

pub use argus_db::ArgusDb;
pub use assembler::{AssemblyInput, assemble_mcp_entry, write_registry_entry};
pub use binding::{BindingTable, ToolBinding};
pub use hash::compute_hash;
pub use installer::{InstalledItem, Installer, InstallerError, ItemKind};
pub use policy_attestation::{
    PolicyAttestation, PolicyAttestationStore, PolicyEventType, compute_content_hash,
};
pub use quarantine::{QuarantineError, QuarantineManager, QuarantineReason, QuarantinedItem};
pub use sandbox_gen::{
    ParsedCapability, extract_env_defaults, generate_env_declarations, generate_sandbox_config,
    parse_capability, required_env_keys,
};
pub use toml_types::{SidecarValidationError, validate_sidecars};
pub use trust_event::{TrustEvent, TrustEventStore, TrustEventType};
pub use watcher::{FolderWatcher, WatchEvent, WatcherError};

pub use types::*;

use std::collections::HashMap;
use std::path::Path;
use thiserror::Error;
use toml_loader::{TomlRegistry, TomlRegistryError};

#[derive(Error, Debug)]
pub enum RegistryError {
    #[error("Registry error: {0}")]
    Toml(#[from] TomlRegistryError),
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("Registry not synced. Run 'argus registry sync' first.")]
    NotSynced,
}

#[derive(Default)]
pub struct Registry {
    tools: HashMap<String, RegistryEntry>,
    synced: bool,
}

impl Registry {
    pub fn load(argus_home: &Path) -> Result<Self, RegistryError> {
        let local_dir = argus_home.join("local-registry");

        if !local_dir.is_dir() {
            return Ok(Self {
                tools: HashMap::new(),
                synced: false,
            });
        }

        let toml_registry = TomlRegistry::load_from_dir(&local_dir)?;
        let tools = toml_registry_to_tools(&toml_registry);

        Ok(Self {
            tools,
            synced: true,
        })
    }

    pub fn lookup(&self, name: &str) -> Option<&RegistryEntry> {
        self.tools.get(name)
    }

    pub fn is_synced(&self) -> bool {
        self.synced
    }

    pub fn tool_count(&self) -> usize {
        self.tools.len()
    }

    pub fn reload(&mut self, argus_home: &Path) -> Result<(), RegistryError> {
        let new = Self::load(argus_home)?;
        *self = new;
        Ok(())
    }
}

fn toml_registry_to_tools(registry: &TomlRegistry) -> HashMap<String, RegistryEntry> {
    let mut tools = HashMap::new();

    for (name, mcp) in &registry.mcps {
        tools.insert(
            name.clone(),
            RegistryEntry {
                capabilities: mcp.metadata.capabilities.clone(),
                schema_hash: mcp.metadata.schema_hash.clone(),
            },
        );
    }

    tools
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn registry_loads_empty_when_no_local_dir() {
        let temp = TempDir::new().unwrap();
        let registry = Registry::load(temp.path()).unwrap();
        assert!(!registry.is_synced());
        assert_eq!(registry.tool_count(), 0);
    }

    #[test]
    fn registry_loads_from_toml() {
        let temp = TempDir::new().unwrap();
        let local_dir = temp.path().join("local-registry");
        let mcps_dir = local_dir.join("mcps");
        std::fs::create_dir_all(&mcps_dir).unwrap();

        std::fs::write(
            mcps_dir.join("test.toml"),
            r#"
[metadata]
name = "test"
description = "Test MCP"
source = "local"
integrity = "untrusted"
capabilities = ["filesystem:read"]

[install]
type = "npm"
package = "test"
version = "1.0.0"
"#,
        )
        .unwrap();

        let registry = Registry::load(temp.path()).unwrap();
        assert!(registry.is_synced());
        assert_eq!(registry.tool_count(), 1);

        let entry = registry.lookup("test").unwrap();
        assert!(entry.capabilities.contains(&"filesystem:read".to_string()));
    }

    #[test]
    fn registry_default_is_empty() {
        let reg = Registry::default();
        assert!(!reg.is_synced());
        assert_eq!(reg.tool_count(), 0);
    }

    #[test]
    fn registry_reload_picks_up_new_entries() {
        let temp = TempDir::new().unwrap();
        let mcps_dir = temp.path().join("local-registry").join("mcps");
        std::fs::create_dir_all(&mcps_dir).unwrap();

        let mut registry = Registry::load(temp.path()).unwrap();
        assert_eq!(registry.tool_count(), 0);

        std::fs::write(
            mcps_dir.join("test_tool.toml"),
            r#"
[metadata]
name = "test-tool"
description = "A test tool"
source = "local"
integrity = "untrusted"
capabilities = ["filesystem:read"]

[install]
type = "binary"
url = "builtin"
checksum = "builtin"
"#,
        )
        .unwrap();

        registry.reload(temp.path()).unwrap();
        assert_eq!(registry.tool_count(), 1);
        assert!(registry.lookup("test_tool").is_some());
    }

    #[test]
    fn registry_stores_all_capabilities() {
        let temp = TempDir::new().unwrap();
        let mcps_dir = temp.path().join("local-registry").join("mcps");
        std::fs::create_dir_all(&mcps_dir).unwrap();

        std::fs::write(
            mcps_dir.join("multi_caps.toml"),
            r#"
[metadata]
name = "multi-caps"
description = "MCP with multiple capabilities"
source = "local"
integrity = "untrusted"
capabilities = ["filesystem:read", "network:egress", "execution:shell"]

[install]
type = "binary"
url = "builtin"
checksum = "builtin"
"#,
        )
        .unwrap();

        let registry = Registry::load(temp.path()).unwrap();
        let entry = registry.lookup("multi_caps").unwrap();
        assert_eq!(entry.capabilities.len(), 3);
    }

    #[test]
    fn registry_accepts_scoped_capabilities() {
        let temp = TempDir::new().unwrap();
        let mcps_dir = temp.path().join("local-registry").join("mcps");
        std::fs::create_dir_all(&mcps_dir).unwrap();

        std::fs::write(
            mcps_dir.join("scoped.toml"),
            r#"
[metadata]
name = "scoped-caps"
description = "MCP with scoped capabilities"
source = "local"
integrity = "observed"
capabilities = ["filesystem:read(/tmp/**)", "network:egress(api.github.com)", "execution:shell(git, ls)"]

[install]
type = "binary"
url = "builtin"
checksum = "builtin"
"#,
        )
        .unwrap();

        let registry = Registry::load(temp.path()).unwrap();
        let entry = registry.lookup("scoped").unwrap();
        assert_eq!(entry.capabilities.len(), 3);
    }
}
