use chrono::{DateTime, Utc};
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};
use thiserror::Error;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum QuarantineReason {
    UnauthorizedAddition,
    HashMismatch {
        expected: String,
        actual: String,
    },
    ManualQuarantine {
        reason: String,
    },
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct QuarantinedItem {
    pub name: String,
    pub original_path: PathBuf,
    pub quarantine_path: PathBuf,
    pub quarantined_at: DateTime<Utc>,
    pub reason: QuarantineReason,
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub hash_at_quarantine: Option<String>,
}

#[derive(Error, Debug)]
pub enum QuarantineError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("Failed to serialize metadata: {0}")]
    Serialize(#[from] serde_json::Error),
    #[error("Item not found: {0}")]
    NotFound(String),
    #[error("Item already exists in quarantine: {0}")]
    AlreadyExists(String),
    #[error("Integrity violation: item '{name}' was modified while in quarantine (expected {expected}, got {actual})")]
    IntegrityViolation {
        name: String,
        expected: String,
        actual: String,
    },
}

pub struct QuarantineManager {
    pub quarantine_dir: PathBuf,
}

impl QuarantineManager {
    pub fn new(quarantine_dir: &Path) -> Result<Self, QuarantineError> {
        std::fs::create_dir_all(quarantine_dir)?;
        Ok(Self {
            quarantine_dir: quarantine_dir.to_path_buf(),
        })
    }

    pub fn quarantine(
        &self,
        source_path: &Path,
        reason: QuarantineReason,
    ) -> Result<QuarantinedItem, QuarantineError> {
        let name = source_path
            .file_name()
            .and_then(|n| n.to_str())
            .ok_or_else(|| {
                QuarantineError::Io(std::io::Error::new(
                    std::io::ErrorKind::InvalidInput,
                    "Invalid source path",
                ))
            })?
            .to_string();

        let dest_path = self.quarantine_dir.join(&name);

        if dest_path.exists() {
            return Err(QuarantineError::AlreadyExists(name));
        }

        let hash_at_quarantine = crate::compute_hash(source_path).ok();

        std::fs::rename(source_path, &dest_path)?;

        let item = QuarantinedItem {
            name: name.clone(),
            original_path: source_path.to_path_buf(),
            quarantine_path: dest_path,
            quarantined_at: Utc::now(),
            reason,
            hash_at_quarantine,
        };

        let meta_path = self.meta_path(&name);
        let meta_json = serde_json::to_string_pretty(&item)?;
        std::fs::write(&meta_path, meta_json)?;

        Ok(item)
    }

    pub fn list_quarantined(&self) -> Result<Vec<QuarantinedItem>, QuarantineError> {
        let mut items = Vec::new();

        for entry in std::fs::read_dir(&self.quarantine_dir)? {
            let path = entry?.path();
            let Some(name) = path.file_name().and_then(|n| n.to_str()) else {
                continue;
            };

            if name.ends_with(".meta.json") {
                let content = std::fs::read_to_string(&path)?;
                let item: QuarantinedItem = serde_json::from_str(&content)?;
                items.push(item);
            }
        }

        items.sort_by(|a, b| b.quarantined_at.cmp(&a.quarantined_at));
        Ok(items)
    }

    pub fn restore_verified(&self, name: &str) -> Result<PathBuf, QuarantineError> {
        let item = self.load_metadata(name)?;

        if let Some(expected_hash) = &item.hash_at_quarantine {
            let current_hash =
                crate::compute_hash(&item.quarantine_path).map_err(QuarantineError::Io)?;
            if &current_hash != expected_hash {
                return Err(QuarantineError::IntegrityViolation {
                    name: name.to_string(),
                    expected: expected_hash.clone(),
                    actual: current_hash,
                });
            }
        } else {
            tracing::warn!(
                target: "argus::quarantine",
                name = %name,
                "Restoring item without integrity verification (no hash recorded at quarantine time)"
            );
        }

        std::fs::rename(&item.quarantine_path, &item.original_path)?;
        std::fs::remove_file(self.meta_path(name))?;

        Ok(item.original_path)
    }

    pub fn delete(&self, name: &str) -> Result<(), QuarantineError> {
        let item_path = self.quarantine_dir.join(name);
        self.load_metadata(name)?;

        if item_path.is_dir() {
            std::fs::remove_dir_all(&item_path)?;
        } else if item_path.exists() {
            std::fs::remove_file(&item_path)?;
        }

        std::fs::remove_file(self.meta_path(name))?;

        Ok(())
    }

    fn meta_path(&self, name: &str) -> PathBuf {
        self.quarantine_dir.join(format!("{name}.meta.json"))
    }

    fn load_metadata(&self, name: &str) -> Result<QuarantinedItem, QuarantineError> {
        let meta_path = self.meta_path(name);

        if !meta_path.exists() {
            return Err(QuarantineError::NotFound(name.to_string()));
        }

        let content = std::fs::read_to_string(&meta_path)?;
        Ok(serde_json::from_str(&content)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn quarantine_reason_serializes_correctly() {
        let reason = QuarantineReason::UnauthorizedAddition;
        let json = serde_json::to_string(&reason).unwrap();
        assert_eq!(json, "\"unauthorized_addition\"");
    }

    #[test]
    fn quarantine_reason_hash_mismatch_serializes() {
        let reason = QuarantineReason::HashMismatch {
            expected: "sha256-abc".to_string(),
            actual: "sha256-xyz".to_string(),
        };
        let json = serde_json::to_string(&reason).unwrap();
        assert!(json.contains("hash_mismatch"));
        assert!(json.contains("sha256-abc"));
    }

    #[test]
    fn quarantined_item_can_be_created() {
        let item = QuarantinedItem {
            name: "suspicious-mcp".to_string(),
            original_path: PathBuf::from("/home/user/.argus/mcps/suspicious-mcp"),
            quarantine_path: PathBuf::from("/home/user/.argus/quarantine/suspicious-mcp"),
            quarantined_at: Utc::now(),
            reason: QuarantineReason::UnauthorizedAddition,
            hash_at_quarantine: None,
        };
        assert_eq!(item.name, "suspicious-mcp");
    }

    #[test]
    fn quarantine_manager_creates_directory() {
        let temp = tempfile::TempDir::new().unwrap();
        let quarantine_dir = temp.path().join("quarantine");
        let manager = QuarantineManager::new(&quarantine_dir).unwrap();
        assert!(quarantine_dir.exists());
        assert_eq!(manager.quarantine_dir, quarantine_dir);
    }

    #[test]
    fn quarantine_moves_item_and_creates_metadata() {
        let temp = tempfile::TempDir::new().unwrap();
        let mcps_dir = temp.path().join("mcps");
        let quarantine_dir = temp.path().join("quarantine");
        std::fs::create_dir_all(&mcps_dir).unwrap();

        let item_path = mcps_dir.join("bad-mcp");
        std::fs::create_dir(&item_path).unwrap();
        std::fs::write(item_path.join("manifest.json"), "{}").unwrap();

        let manager = QuarantineManager::new(&quarantine_dir).unwrap();
        let result = manager
            .quarantine(&item_path, QuarantineReason::UnauthorizedAddition)
            .unwrap();

        assert!(!item_path.exists());
        assert!(result.quarantine_path.exists());
        assert!(quarantine_dir.join("bad-mcp.meta.json").exists());
    }

    #[test]
    fn list_quarantined_returns_all_items() {
        let temp = tempfile::TempDir::new().unwrap();
        let mcps_dir = temp.path().join("mcps");
        let quarantine_dir = temp.path().join("quarantine");
        std::fs::create_dir_all(&mcps_dir).unwrap();

        let item1 = mcps_dir.join("mcp1");
        let item2 = mcps_dir.join("mcp2");
        std::fs::create_dir(&item1).unwrap();
        std::fs::create_dir(&item2).unwrap();

        let manager = QuarantineManager::new(&quarantine_dir).unwrap();
        manager
            .quarantine(&item1, QuarantineReason::UnauthorizedAddition)
            .unwrap();
        manager
            .quarantine(
                &item2,
                QuarantineReason::HashMismatch {
                    expected: "a".to_string(),
                    actual: "b".to_string(),
                },
            )
            .unwrap();

        let items = manager.list_quarantined().unwrap();
        assert_eq!(items.len(), 2);
    }

    #[test]
    fn restore_verified_succeeds_when_unmodified() {
        let temp = tempfile::TempDir::new().unwrap();
        let mcps_dir = temp.path().join("mcps");
        let quarantine_dir = temp.path().join("quarantine");
        std::fs::create_dir_all(&mcps_dir).unwrap();

        let item_path = mcps_dir.join("mcp1");
        std::fs::create_dir(&item_path).unwrap();
        std::fs::write(item_path.join("manifest.json"), r#"{"name":"mcp1"}"#).unwrap();

        let manager = QuarantineManager::new(&quarantine_dir).unwrap();
        manager
            .quarantine(&item_path, QuarantineReason::UnauthorizedAddition)
            .unwrap();

        let restored = manager.restore_verified("mcp1").unwrap();
        assert!(restored.exists());
    }

    #[test]
    fn restore_verified_rejects_when_modified() {
        let temp = tempfile::TempDir::new().unwrap();
        let mcps_dir = temp.path().join("mcps");
        let quarantine_dir = temp.path().join("quarantine");
        std::fs::create_dir_all(&mcps_dir).unwrap();

        let item_path = mcps_dir.join("mcp2");
        std::fs::create_dir(&item_path).unwrap();
        std::fs::write(item_path.join("manifest.json"), r#"{"name":"mcp2"}"#).unwrap();

        let manager = QuarantineManager::new(&quarantine_dir).unwrap();
        manager
            .quarantine(&item_path, QuarantineReason::UnauthorizedAddition)
            .unwrap();

        std::fs::write(
            quarantine_dir.join("mcp2").join("manifest.json"),
            r#"{"name":"evil"}"#,
        )
        .unwrap();

        let result = manager.restore_verified("mcp2");
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(matches!(err, QuarantineError::IntegrityViolation { .. }));
    }

    #[test]
    fn quarantine_stores_hash() {
        let temp = tempfile::TempDir::new().unwrap();
        let mcps_dir = temp.path().join("mcps");
        let quarantine_dir = temp.path().join("quarantine");
        std::fs::create_dir_all(&mcps_dir).unwrap();

        let item_path = mcps_dir.join("mcp3");
        std::fs::create_dir(&item_path).unwrap();
        std::fs::write(item_path.join("file.txt"), "content").unwrap();

        let manager = QuarantineManager::new(&quarantine_dir).unwrap();
        let item = manager
            .quarantine(&item_path, QuarantineReason::UnauthorizedAddition)
            .unwrap();
        assert!(item.hash_at_quarantine.is_some());
        assert!(item.hash_at_quarantine.unwrap().starts_with("sha256:"));
    }

    #[test]
    fn delete_removes_quarantined_item_permanently() {
        let temp = tempfile::TempDir::new().unwrap();
        let mcps_dir = temp.path().join("mcps");
        let quarantine_dir = temp.path().join("quarantine");
        std::fs::create_dir_all(&mcps_dir).unwrap();

        let item_path = mcps_dir.join("mcp1");
        std::fs::create_dir(&item_path).unwrap();

        let manager = QuarantineManager::new(&quarantine_dir).unwrap();
        manager
            .quarantine(&item_path, QuarantineReason::UnauthorizedAddition)
            .unwrap();

        manager.delete("mcp1").unwrap();

        assert!(!quarantine_dir.join("mcp1").exists());
        assert!(!quarantine_dir.join("mcp1.meta.json").exists());
    }
}
