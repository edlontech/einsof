use std::collections::BTreeMap;
use std::path::{Path, PathBuf};

use argus_kernel::ToolId;
use cedar_policy::PolicySet;

use crate::error::CedarError;

#[derive(Debug, Clone, Default, serde::Deserialize)]
pub struct ToolScope {
    #[serde(default)]
    pub paths: Vec<String>,
    #[serde(default)]
    pub domains: Vec<String>,
    #[serde(default)]
    pub commands: Vec<String>,
}

pub trait PolicySource {
    fn load_policies(&self) -> Result<PolicySet, CedarError>;
    fn load_tool_scopes(&self) -> Result<BTreeMap<ToolId, ToolScope>, CedarError>;
}

#[derive(Debug, Clone, Default, serde::Deserialize)]
struct ScopeManifest {
    #[serde(default)]
    tools: BTreeMap<String, ToolScope>,
}

pub struct FilePolicySource {
    policy_dir: PathBuf,
}

impl FilePolicySource {
    pub fn new(policy_dir: &Path) -> Self {
        Self {
            policy_dir: policy_dir.to_path_buf(),
        }
    }
}

impl PolicySource for FilePolicySource {
    fn load_policies(&self) -> Result<PolicySet, CedarError> {
        let mut cedar_paths = Vec::new();
        for entry in std::fs::read_dir(&self.policy_dir).map_err(CedarError::Io)? {
            let path = entry.map_err(CedarError::Io)?.path();
            if path.extension().and_then(|e| e.to_str()) == Some("cedar") {
                cedar_paths.push(path);
            }
        }
        cedar_paths.sort();

        let mut combined = String::new();
        for path in &cedar_paths {
            let content = std::fs::read_to_string(path).map_err(CedarError::Io)?;
            combined.push_str(&content);
            combined.push('\n');
        }

        if combined.is_empty() {
            return Ok(PolicySet::new());
        }
        combined
            .parse::<PolicySet>()
            .map_err(|e| CedarError::PolicyParse(e.to_string()))
    }

    fn load_tool_scopes(&self) -> Result<BTreeMap<ToolId, ToolScope>, CedarError> {
        let path = self.policy_dir.join("tool-scopes.toml");
        if !path.exists() {
            return Ok(BTreeMap::new());
        }
        let content = std::fs::read_to_string(&path).map_err(CedarError::Io)?;
        let manifest: ScopeManifest =
            toml::from_str(&content).map_err(|e| CedarError::ScopeManifestParse(e.to_string()))?;
        Ok(manifest
            .tools
            .into_iter()
            .map(|(name, scope)| (ToolId::new(&name), scope))
            .collect())
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::fs;

    fn setup_policy_dir(dir: &Path, policies: &[(&str, &str)], scopes_toml: Option<&str>) {
        fs::create_dir_all(dir).unwrap();
        for (name, content) in policies {
            fs::write(dir.join(name), content).unwrap();
        }
        if let Some(toml_content) = scopes_toml {
            fs::write(dir.join("tool-scopes.toml"), toml_content).unwrap();
        }
    }

    #[test]
    fn loads_cedar_policies_from_dir() {
        let tmp = tempfile::tempdir().unwrap();
        let policy = r#"permit(principal, action, resource);"#;
        setup_policy_dir(tmp.path(), &[("basic.cedar", policy)], None);

        let source = FilePolicySource::new(tmp.path());
        let ps = source.load_policies().unwrap();
        assert!(!ps.is_empty());
    }

    #[test]
    fn empty_dir_returns_empty_policy_set() {
        let tmp = tempfile::tempdir().unwrap();
        setup_policy_dir(tmp.path(), &[], None);

        let source = FilePolicySource::new(tmp.path());
        let ps = source.load_policies().unwrap();
        assert!(ps.is_empty());
    }

    #[test]
    fn invalid_policy_returns_error() {
        let tmp = tempfile::tempdir().unwrap();
        setup_policy_dir(tmp.path(), &[("bad.cedar", "not valid cedar!!!")], None);

        let source = FilePolicySource::new(tmp.path());
        assert!(source.load_policies().is_err());
    }

    #[test]
    fn loads_tool_scopes_from_toml() {
        let tmp = tempfile::tempdir().unwrap();
        let scopes = r#"
[tools."fs-reader"]
paths = ["/home/user/**"]

[tools."web-fetch"]
domains = ["api.example.com"]
"#;
        setup_policy_dir(tmp.path(), &[], Some(scopes));

        let source = FilePolicySource::new(tmp.path());
        let scopes = source.load_tool_scopes().unwrap();
        assert_eq!(scopes.len(), 2);
        assert_eq!(
            scopes[&ToolId::new("fs-reader")].paths,
            vec!["/home/user/**"]
        );
        assert_eq!(
            scopes[&ToolId::new("web-fetch")].domains,
            vec!["api.example.com"]
        );
    }

    #[test]
    fn missing_scopes_file_returns_empty_map() {
        let tmp = tempfile::tempdir().unwrap();
        setup_policy_dir(tmp.path(), &[], None);

        let source = FilePolicySource::new(tmp.path());
        let scopes = source.load_tool_scopes().unwrap();
        assert!(scopes.is_empty());
    }
}
