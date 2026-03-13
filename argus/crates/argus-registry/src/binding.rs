use std::collections::{HashMap, HashSet};
use std::path::PathBuf;

use crate::hash::compute_hash;

#[derive(Debug, Clone, serde::Serialize, serde::Deserialize)]
pub struct ToolBinding {
    pub name: String,
    pub derivation_hash: String,
    pub capabilities: HashSet<String>,
    pub source_path: PathBuf,
    pub mcp_name: Option<String>,
}

#[derive(Debug, Default, Clone)]
pub struct BindingTable {
    tools: HashMap<String, ToolBinding>,
}

impl BindingTable {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn lookup(&self, tool_name: &str) -> Option<&ToolBinding> {
        self.tools.get(tool_name)
    }

    pub fn register(&mut self, binding: ToolBinding) {
        self.tools.insert(binding.name.clone(), binding);
    }

    pub fn remove(&mut self, tool_name: &str) {
        self.tools.remove(tool_name);
    }

    pub fn verify_hash(&self, tool_name: &str, expected_hash: &str) -> bool {
        self.tools
            .get(tool_name)
            .is_some_and(|b| b.derivation_hash == expected_hash)
    }

    pub fn iter(&self) -> impl Iterator<Item = &ToolBinding> {
        self.tools.values()
    }

    pub fn len(&self) -> usize {
        self.tools.len()
    }

    pub fn is_empty(&self) -> bool {
        self.tools.is_empty()
    }

    pub fn verify_and_remove_stale(&mut self) -> Vec<String> {
        let mut stale = Vec::new();
        self.tools.retain(|name, binding| {
            let hash_valid =
                compute_hash(&binding.source_path).is_ok_and(|h| h == binding.derivation_hash);
            if !hash_valid {
                tracing::warn!(
                    target: "argus::registry",
                    tool = %name,
                    "Binding hash mismatch -- removing stale binding"
                );
                stale.push(name.clone());
            }
            hash_valid
        });
        stale
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn tool_binding_can_be_created() {
        let binding = ToolBinding {
            name: "read_file".to_string(),
            derivation_hash: "sha256-abc123".to_string(),
            capabilities: ["filesystem:read".to_string()].into_iter().collect(),
            source_path: PathBuf::from("/store/abc-mcp"),
            mcp_name: None,
        };
        assert_eq!(binding.name, "read_file");
    }

    #[test]
    fn binding_table_lookup_returns_none_for_unknown() {
        let table = BindingTable::new();
        assert!(table.lookup("nonexistent").is_none());
    }

    #[test]
    fn binding_table_register_and_lookup() {
        let mut table = BindingTable::new();
        let binding = ToolBinding {
            name: "read_file".to_string(),
            derivation_hash: "sha256-abc123".to_string(),
            capabilities: ["filesystem:read".to_string()].into_iter().collect(),
            source_path: PathBuf::from("/store/abc-mcp"),
            mcp_name: None,
        };
        table.register(binding);

        let found = table.lookup("read_file").unwrap();
        assert_eq!(found.derivation_hash, "sha256-abc123");
    }

    #[test]
    fn binding_table_remove() {
        let mut table = BindingTable::new();
        let binding = ToolBinding {
            name: "read_file".to_string(),
            derivation_hash: "sha256-abc123".to_string(),
            capabilities: HashSet::new(),
            source_path: PathBuf::from("/store/abc-mcp"),
            mcp_name: None,
        };
        table.register(binding);
        assert!(table.lookup("read_file").is_some());

        table.remove("read_file");
        assert!(table.lookup("read_file").is_none());
    }

    #[test]
    fn verify_and_remove_stale_keeps_valid_bindings() {
        let temp = tempfile::TempDir::new().unwrap();
        let tool_dir = temp.path().join("my-tool");
        std::fs::create_dir(&tool_dir).unwrap();
        std::fs::write(tool_dir.join("main.js"), "console.log('hi')").unwrap();

        let hash = compute_hash(&tool_dir).unwrap();

        let mut table = BindingTable::new();
        table.register(ToolBinding {
            name: "my-tool".to_string(),
            derivation_hash: hash,
            capabilities: HashSet::new(),
            source_path: tool_dir,
            mcp_name: None,
        });

        let removed = table.verify_and_remove_stale();
        assert_eq!(removed.len(), 0);
        assert!(table.lookup("my-tool").is_some());
    }

    #[test]
    fn verify_and_remove_stale_removes_tampered_bindings() {
        let temp = tempfile::TempDir::new().unwrap();
        let tool_dir = temp.path().join("tampered-tool");
        std::fs::create_dir(&tool_dir).unwrap();
        std::fs::write(tool_dir.join("main.js"), "original").unwrap();

        let hash = compute_hash(&tool_dir).unwrap();

        std::fs::write(tool_dir.join("main.js"), "malicious").unwrap();

        let mut table = BindingTable::new();
        table.register(ToolBinding {
            name: "tampered-tool".to_string(),
            derivation_hash: hash,
            capabilities: HashSet::new(),
            source_path: tool_dir,
            mcp_name: None,
        });

        let removed = table.verify_and_remove_stale();
        assert_eq!(removed.len(), 1);
        assert_eq!(removed[0], "tampered-tool");
        assert!(table.lookup("tampered-tool").is_none());
    }

    #[test]
    fn verify_and_remove_stale_removes_missing_path() {
        let mut table = BindingTable::new();
        table.register(ToolBinding {
            name: "gone-tool".to_string(),
            derivation_hash: "sha256:abc".to_string(),
            capabilities: HashSet::new(),
            source_path: PathBuf::from("/nonexistent/path"),
            mcp_name: None,
        });

        let removed = table.verify_and_remove_stale();
        assert_eq!(removed.len(), 1);
        assert!(table.lookup("gone-tool").is_none());
    }

    #[test]
    fn binding_table_verify_hash() {
        let mut table = BindingTable::new();
        let binding = ToolBinding {
            name: "read_file".to_string(),
            derivation_hash: "sha256-abc123".to_string(),
            capabilities: HashSet::new(),
            source_path: PathBuf::from("/store/abc-mcp"),
            mcp_name: None,
        };
        table.register(binding);

        assert!(table.verify_hash("read_file", "sha256-abc123"));
        assert!(!table.verify_hash("read_file", "sha256-wrong"));
        assert!(!table.verify_hash("nonexistent", "sha256-abc123"));
    }
}
