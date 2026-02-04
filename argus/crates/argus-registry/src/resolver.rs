use std::path::Path;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProjectType {
    Npm,
    Pip,
    Cargo,
    Docker,
    Unknown,
}

pub fn detect_project_type(path: &Path) -> ProjectType {
    if path.join("package.json").exists() {
        return ProjectType::Npm;
    }
    if path.join("pyproject.toml").exists()
        || path.join("setup.py").exists()
        || path.join("setup.cfg").exists()
    {
        return ProjectType::Pip;
    }
    if path.join("Cargo.toml").exists() {
        return ProjectType::Cargo;
    }
    if path.join("Dockerfile").exists() {
        return ProjectType::Docker;
    }
    ProjectType::Unknown
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn detect_npm_from_package_json() {
        let tmp = TempDir::new().unwrap();
        std::fs::write(tmp.path().join("package.json"), "{}").unwrap();
        assert_eq!(detect_project_type(tmp.path()), ProjectType::Npm);
    }

    #[test]
    fn detect_pip_from_pyproject() {
        let tmp = TempDir::new().unwrap();
        std::fs::write(tmp.path().join("pyproject.toml"), "").unwrap();
        assert_eq!(detect_project_type(tmp.path()), ProjectType::Pip);
    }

    #[test]
    fn detect_pip_from_setup_py() {
        let tmp = TempDir::new().unwrap();
        std::fs::write(tmp.path().join("setup.py"), "").unwrap();
        assert_eq!(detect_project_type(tmp.path()), ProjectType::Pip);
    }

    #[test]
    fn detect_cargo_from_cargo_toml() {
        let tmp = TempDir::new().unwrap();
        std::fs::write(tmp.path().join("Cargo.toml"), "").unwrap();
        assert_eq!(detect_project_type(tmp.path()), ProjectType::Cargo);
    }

    #[test]
    fn detect_docker_from_dockerfile() {
        let tmp = TempDir::new().unwrap();
        std::fs::write(tmp.path().join("Dockerfile"), "").unwrap();
        assert_eq!(detect_project_type(tmp.path()), ProjectType::Docker);
    }

    #[test]
    fn detect_unknown_for_empty_dir() {
        let tmp = TempDir::new().unwrap();
        assert_eq!(detect_project_type(tmp.path()), ProjectType::Unknown);
    }

    #[test]
    fn npm_takes_priority_over_docker() {
        let tmp = TempDir::new().unwrap();
        std::fs::write(tmp.path().join("package.json"), "{}").unwrap();
        std::fs::write(tmp.path().join("Dockerfile"), "").unwrap();
        assert_eq!(detect_project_type(tmp.path()), ProjectType::Npm);
    }
}
