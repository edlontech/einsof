use std::path::{Path, PathBuf};

use crate::SandboxError;

const SENSITIVE_PREFIXES: &[&str] = &[
    ".ssh",
    ".aws",
    ".gnupg",
    ".config/gcloud",
    ".azure",
    ".kube",
    ".docker/config.json",
    ".config/gh",
    ".netrc",
    ".npmrc",
    ".pypirc",
    ".cargo/credentials.toml",
    ".config/google-chrome",
    ".config/chromium",
    ".mozilla/firefox",
    "Library/Application Support/Google/Chrome",
    "Library/Application Support/Firefox",
    ".bash_history",
    ".zsh_history",
    ".fish_history",
    ".password-store",
    ".local/share/keyrings",
    "Library/Keychains",
];

pub fn validate_path_not_sensitive(path: &Path) -> Result<(), SandboxError> {
    let home = home_dir();
    for prefix in SENSITIVE_PREFIXES {
        let sensitive = home.join(prefix);
        if path.starts_with(&sensitive) {
            return Err(SandboxError::SensitivePath {
                path: path.to_path_buf(),
                reason: format!("matches sensitive prefix: ~/{prefix}"),
            });
        }
    }
    Ok(())
}

fn home_dir() -> PathBuf {
    std::env::var("HOME")
        .map(PathBuf::from)
        .unwrap_or_else(|_| PathBuf::from("/root"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejects_ssh_directory() {
        let home = home_dir();
        let result = validate_path_not_sensitive(&home.join(".ssh"));
        assert!(result.is_err());
    }

    #[test]
    fn rejects_ssh_subdirectory() {
        let home = home_dir();
        let result = validate_path_not_sensitive(&home.join(".ssh/id_rsa"));
        assert!(result.is_err());
    }

    #[test]
    fn allows_non_sensitive_path() {
        let result = validate_path_not_sensitive(Path::new("/tmp/workspace"));
        assert!(result.is_ok());
    }

    #[test]
    fn allows_similar_but_different_name() {
        let home = home_dir();
        let result = validate_path_not_sensitive(&home.join(".sshfoo"));
        assert!(result.is_ok());
    }

    #[test]
    fn rejects_aws_credentials() {
        let home = home_dir();
        let result = validate_path_not_sensitive(&home.join(".aws/credentials"));
        assert!(result.is_err());
    }

    #[test]
    fn rejects_gnupg() {
        let home = home_dir();
        let result = validate_path_not_sensitive(&home.join(".gnupg/private-keys-v1.d"));
        assert!(result.is_err());
    }

    #[test]
    fn rejects_kube_config() {
        let home = home_dir();
        let result = validate_path_not_sensitive(&home.join(".kube/config"));
        assert!(result.is_err());
    }

    #[test]
    fn rejects_shell_history() {
        let home = home_dir();
        assert!(validate_path_not_sensitive(&home.join(".bash_history")).is_err());
        assert!(validate_path_not_sensitive(&home.join(".zsh_history")).is_err());
        assert!(validate_path_not_sensitive(&home.join(".fish_history")).is_err());
    }
}
