use serde::{Deserialize, Serialize};

use crate::registry_types::{DependencyReport, DependencyVulnerability, FlaggedDependency};
use crate::sandbox::ManifestKind;

#[derive(Debug, Serialize)]
struct OsvQuery {
    package: OsvPackage,
}

#[derive(Debug, Serialize)]
struct OsvPackage {
    name: String,
    ecosystem: String,
}

#[derive(Debug, Deserialize)]
struct OsvResponse {
    #[serde(default)]
    vulns: Vec<OsvVuln>,
}

#[derive(Debug, Deserialize)]
struct OsvVuln {
    id: String,
    summary: Option<String>,
    #[serde(default)]
    database_specific: Option<OsvDatabaseSpecific>,
}

#[derive(Debug, Deserialize)]
struct OsvDatabaseSpecific {
    severity: Option<String>,
}

const OSV_API_URL: &str = "https://api.osv.dev/v1/query";

fn ecosystem_for_manifest(kind: &ManifestKind) -> &'static str {
    match kind {
        ManifestKind::PackageJson => "npm",
        ManifestKind::CargoToml => "crates.io",
        ManifestKind::PyprojectToml => "PyPI",
        ManifestKind::GoMod => "Go",
    }
}

#[derive(Debug, Clone)]
pub struct ParsedDependency {
    pub name: String,
    pub version: Option<String>,
}

pub fn parse_npm_dependencies(content: &str) -> Vec<ParsedDependency> {
    let parsed: serde_json::Value = match serde_json::from_str(content) {
        Ok(v) => v,
        Err(_) => return vec![],
    };

    let mut deps = Vec::new();
    for section in ["dependencies", "devDependencies"] {
        if let Some(obj) = parsed.get(section).and_then(|v| v.as_object()) {
            for (name, version) in obj {
                deps.push(ParsedDependency {
                    name: name.clone(),
                    version: version.as_str().map(|s| s.to_string()),
                });
            }
        }
    }
    deps
}

pub fn parse_cargo_dependencies(content: &str) -> Vec<ParsedDependency> {
    let parsed: toml::Value = match toml::from_str(content) {
        Ok(v) => v,
        Err(_) => return vec![],
    };

    let mut deps = Vec::new();
    for section in ["dependencies", "dev-dependencies", "build-dependencies"] {
        if let Some(table) = parsed.get(section).and_then(|v| v.as_table()) {
            for (name, value) in table {
                let version = match value {
                    toml::Value::String(v) => Some(v.clone()),
                    toml::Value::Table(t) => t
                        .get("version")
                        .and_then(|v| v.as_str())
                        .map(|s| s.to_string()),
                    _ => None,
                };
                deps.push(ParsedDependency {
                    name: name.clone(),
                    version,
                });
            }
        }
    }
    deps
}

pub fn parse_dependencies(kind: &ManifestKind, content: &str) -> Vec<ParsedDependency> {
    match kind {
        ManifestKind::PackageJson => parse_npm_dependencies(content),
        ManifestKind::CargoToml => parse_cargo_dependencies(content),
        _ => vec![],
    }
}

const FLAGGED_PATTERNS: &[(&str, &str)] = &[
    ("child_process", "Can execute arbitrary system commands"),
    ("node-pty", "Provides pseudo-terminal access"),
    ("puppeteer", "Browser automation with full page access"),
    ("playwright", "Browser automation with full page access"),
    ("keytar", "Access to OS credential store"),
    ("node-keychain", "Access to OS credential store"),
];

pub fn flag_suspicious_packages(deps: &[ParsedDependency]) -> Vec<FlaggedDependency> {
    deps.iter()
        .filter_map(|dep| {
            FLAGGED_PATTERNS
                .iter()
                .find(|(pattern, _)| dep.name.contains(pattern))
                .map(|(_, reason)| FlaggedDependency {
                    package: dep.name.clone(),
                    reason: reason.to_string(),
                })
        })
        .collect()
}

pub async fn query_osv(
    client: &reqwest::Client,
    package: &str,
    ecosystem: &str,
) -> std::result::Result<Vec<DependencyVulnerability>, reqwest::Error> {
    let query = OsvQuery {
        package: OsvPackage {
            name: package.to_string(),
            ecosystem: ecosystem.to_string(),
        },
    };

    let response: OsvResponse = client
        .post(OSV_API_URL)
        .json(&query)
        .send()
        .await?
        .json()
        .await?;

    Ok(response
        .vulns
        .into_iter()
        .map(|v| DependencyVulnerability {
            package: package.to_string(),
            id: v.id,
            severity: v
                .database_specific
                .and_then(|d| d.severity)
                .unwrap_or_else(|| "unknown".to_string()),
            description: v.summary.unwrap_or_default(),
        })
        .collect())
}

pub async fn audit_dependencies(
    manifest_kind: &ManifestKind,
    manifest_content: &str,
) -> DependencyReport {
    let deps = parse_dependencies(manifest_kind, manifest_content);
    let ecosystem = ecosystem_for_manifest(manifest_kind);
    let flagged = flag_suspicious_packages(&deps);

    let client = reqwest::Client::new();
    let mut vulnerabilities = Vec::new();

    for dep in &deps {
        match query_osv(&client, &dep.name, ecosystem).await {
            Ok(vulns) => vulnerabilities.extend(vulns),
            Err(e) => {
                tracing::warn!(package = %dep.name, error = %e, "OSV query failed");
            }
        }
    }

    DependencyReport {
        total: deps.len(),
        vulnerabilities,
        flagged,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_npm_deps_from_package_json() {
        let content = r#"{
            "dependencies": {
                "express": "^4.18.2",
                "@anthropic-ai/sdk": "^0.1.0"
            },
            "devDependencies": {
                "typescript": "^5.0.0"
            }
        }"#;
        let deps = parse_npm_dependencies(content);
        assert_eq!(deps.len(), 3);
        assert!(deps.iter().any(|d| d.name == "express"));
        assert!(deps.iter().any(|d| d.name == "@anthropic-ai/sdk"));
        assert!(deps.iter().any(|d| d.name == "typescript"));
    }

    #[test]
    fn parse_cargo_deps_from_cargo_toml() {
        let content = r#"
[dependencies]
serde = "1.0"
tokio = { version = "1", features = ["full"] }

[dev-dependencies]
tempfile = "3"
"#;
        let deps = parse_cargo_dependencies(content);
        assert_eq!(deps.len(), 3);
        assert!(
            deps.iter()
                .any(|d| d.name == "serde" && d.version.as_deref() == Some("1.0"))
        );
        assert!(
            deps.iter()
                .any(|d| d.name == "tokio" && d.version.as_deref() == Some("1"))
        );
    }

    #[test]
    fn parse_empty_manifest_returns_empty() {
        assert!(parse_npm_dependencies("{}").is_empty());
        assert!(parse_npm_dependencies("invalid json").is_empty());
        assert!(parse_cargo_dependencies("").is_empty());
    }

    #[test]
    fn flag_suspicious_npm_packages() {
        let deps = vec![
            ParsedDependency {
                name: "express".to_string(),
                version: None,
            },
            ParsedDependency {
                name: "child_process".to_string(),
                version: None,
            },
            ParsedDependency {
                name: "puppeteer".to_string(),
                version: None,
            },
            ParsedDependency {
                name: "lodash".to_string(),
                version: None,
            },
        ];
        let flagged = flag_suspicious_packages(&deps);
        assert_eq!(flagged.len(), 2);
        assert!(flagged.iter().any(|f| f.package == "child_process"));
        assert!(flagged.iter().any(|f| f.package == "puppeteer"));
    }

    #[test]
    fn ecosystem_mapping() {
        assert_eq!(ecosystem_for_manifest(&ManifestKind::PackageJson), "npm");
        assert_eq!(
            ecosystem_for_manifest(&ManifestKind::CargoToml),
            "crates.io"
        );
        assert_eq!(ecosystem_for_manifest(&ManifestKind::PyprojectToml), "PyPI");
        assert_eq!(ecosystem_for_manifest(&ManifestKind::GoMod), "Go");
    }
}
