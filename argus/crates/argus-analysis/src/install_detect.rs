use crate::registry_types::InstallDetection;
use crate::sandbox::ManifestKind;

pub fn detect_install(kind: &ManifestKind, content: &str) -> InstallDetection {
    match kind {
        ManifestKind::PackageJson => detect_npm_install(content),
        ManifestKind::CargoToml => detect_cargo_install(content),
        ManifestKind::PyprojectToml => detect_pip_install(content),
        ManifestKind::GoMod => detect_go_install(content),
    }
}

fn detect_npm_install(content: &str) -> InstallDetection {
    let parsed: serde_json::Value = match serde_json::from_str(content) {
        Ok(v) => v,
        Err(_) => serde_json::Value::Object(Default::default()),
    };
    let name = parsed
        .get("name")
        .and_then(|v| v.as_str())
        .unwrap_or("unknown")
        .to_string();
    let version = parsed
        .get("version")
        .and_then(|v| v.as_str())
        .unwrap_or("0.0.0")
        .to_string();

    InstallDetection {
        method: "npm".to_string(),
        package: name,
        version,
        source: "package.json".to_string(),
    }
}

fn detect_cargo_install(content: &str) -> InstallDetection {
    let parsed: toml::Value = match toml::from_str(content) {
        Ok(v) => v,
        Err(_) => toml::Value::Table(Default::default()),
    };
    let package = parsed.get("package").and_then(|v| v.as_table());
    let name = package
        .and_then(|p| p.get("name"))
        .and_then(|v| v.as_str())
        .unwrap_or("unknown")
        .to_string();
    let version = package
        .and_then(|p| p.get("version"))
        .and_then(|v| v.as_str())
        .unwrap_or("0.0.0")
        .to_string();

    InstallDetection {
        method: "cargo".to_string(),
        package: name,
        version,
        source: "Cargo.toml".to_string(),
    }
}

fn detect_pip_install(content: &str) -> InstallDetection {
    let parsed: toml::Value = match toml::from_str(content) {
        Ok(v) => v,
        Err(_) => toml::Value::Table(Default::default()),
    };
    let project = parsed.get("project").and_then(|v| v.as_table());
    let name = project
        .and_then(|p| p.get("name"))
        .and_then(|v| v.as_str())
        .unwrap_or("unknown")
        .to_string();
    let version = project
        .and_then(|p| p.get("version"))
        .and_then(|v| v.as_str())
        .unwrap_or("0.0.0")
        .to_string();

    InstallDetection {
        method: "pip".to_string(),
        package: name,
        version,
        source: "pyproject.toml".to_string(),
    }
}

fn detect_go_install(content: &str) -> InstallDetection {
    let module_line = content
        .lines()
        .find(|l| l.starts_with("module "))
        .and_then(|l| l.strip_prefix("module "))
        .unwrap_or("unknown");

    InstallDetection {
        method: "go".to_string(),
        package: module_line.trim().to_string(),
        version: "0.0.0".to_string(),
        source: "go.mod".to_string(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn detect_npm_from_package_json() {
        let content = r#"{"name": "@thedotmack/claude-mem", "version": "1.2.3"}"#;
        let result = detect_install(&ManifestKind::PackageJson, content);
        assert_eq!(result.method, "npm");
        assert_eq!(result.package, "@thedotmack/claude-mem");
        assert_eq!(result.version, "1.2.3");
        assert_eq!(result.source, "package.json");
    }

    #[test]
    fn detect_cargo_from_cargo_toml() {
        let content = "[package]\nname = \"my-tool\"\nversion = \"0.5.0\"\n";
        let result = detect_install(&ManifestKind::CargoToml, content);
        assert_eq!(result.method, "cargo");
        assert_eq!(result.package, "my-tool");
        assert_eq!(result.version, "0.5.0");
    }

    #[test]
    fn detect_pip_from_pyproject() {
        let content = "[project]\nname = \"my-python-tool\"\nversion = \"2.0.0\"\n";
        let result = detect_install(&ManifestKind::PyprojectToml, content);
        assert_eq!(result.method, "pip");
        assert_eq!(result.package, "my-python-tool");
        assert_eq!(result.version, "2.0.0");
    }

    #[test]
    fn detect_go_from_go_mod() {
        let content = "module github.com/user/tool\n\ngo 1.21\n";
        let result = detect_install(&ManifestKind::GoMod, content);
        assert_eq!(result.method, "go");
        assert_eq!(result.package, "github.com/user/tool");
    }

    #[test]
    fn handles_malformed_manifest_gracefully() {
        let result = detect_install(&ManifestKind::PackageJson, "not json");
        assert_eq!(result.method, "npm");
        assert_eq!(result.package, "unknown");
    }
}
