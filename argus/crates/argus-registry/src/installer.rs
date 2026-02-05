use serde::{Deserialize, Serialize};
use std::path::PathBuf;
use thiserror::Error;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ItemKind {
    Mcp,
    Skill,
}

impl ItemKind {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Mcp => "mcp",
            Self::Skill => "skill",
        }
    }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct InstalledItem {
    pub name: String,
    pub kind: ItemKind,
    pub derivation_hash: String,
    pub path: PathBuf,
    pub tools: Vec<String>,
    pub installed_at: String,
}

#[derive(Error, Debug)]
pub enum InstallerError {
    #[error("{kind:?} '{name}' not found in registry")]
    NotFound { kind: ItemKind, name: String },
    #[error("Already installed: {0}")]
    AlreadyInstalled(String),
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("Failed to parse manifest: {0}")]
    ManifestParse(#[from] serde_json::Error),
}

pub struct Installer {
    mcps_dir: PathBuf,
    skills_dir: PathBuf,
}

impl Installer {
    pub fn new(mcps_dir: PathBuf, skills_dir: PathBuf) -> Self {
        Self {
            mcps_dir,
            skills_dir,
        }
    }

    pub fn list_installed(&self, kind: ItemKind) -> Result<Vec<InstalledItem>, InstallerError> {
        let dir = match kind {
            ItemKind::Mcp => &self.mcps_dir,
            ItemKind::Skill => &self.skills_dir,
        };

        if !dir.exists() {
            return Ok(vec![]);
        }

        let mut items = vec![];
        for entry in std::fs::read_dir(dir)? {
            let entry = entry?;
            let manifest_path = entry.path().join("manifest.json");
            if manifest_path.exists() {
                let content = std::fs::read_to_string(&manifest_path)?;
                let item: InstalledItem = serde_json::from_str(&content)?;
                items.push(item);
            }
        }
        Ok(items)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn installer_can_be_created() {
        let temp = TempDir::new().unwrap();
        let installer = Installer::new(temp.path().join("mcps"), temp.path().join("skills"));
        assert!(installer.list_installed(ItemKind::Mcp).unwrap().is_empty());
    }

    #[test]
    fn item_kind_serializes_lowercase() {
        assert_eq!(serde_json::to_string(&ItemKind::Mcp).unwrap(), "\"mcp\"");
        assert_eq!(
            serde_json::to_string(&ItemKind::Skill).unwrap(),
            "\"skill\""
        );
    }

    #[test]
    fn item_kind_as_str() {
        assert_eq!(ItemKind::Mcp.as_str(), "mcp");
        assert_eq!(ItemKind::Skill.as_str(), "skill");
    }

    #[test]
    fn installed_item_can_be_serialized() {
        let item = InstalledItem {
            name: "stripe".to_string(),
            kind: ItemKind::Mcp,
            derivation_hash: "sha256-abc123".to_string(),
            path: PathBuf::from("/store/abc-stripe"),
            tools: vec!["create_payment".to_string()],
            installed_at: "2026-02-03T12:00:00Z".to_string(),
        };
        let json = serde_json::to_string(&item).unwrap();
        assert!(json.contains("\"name\":\"stripe\""));
        assert!(json.contains("\"kind\":\"mcp\""));
    }

    #[test]
    fn installer_error_display() {
        let err = InstallerError::NotFound {
            kind: ItemKind::Mcp,
            name: "stripe".to_string(),
        };
        assert!(err.to_string().contains("stripe"));
        assert!(err.to_string().contains("Mcp"));
    }
}
