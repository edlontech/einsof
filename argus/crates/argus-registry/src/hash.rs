use std::collections::BTreeMap;
use std::path::Path;

use sha2::{Digest, Sha256};

pub fn compute_hash(path: &Path) -> Result<String, std::io::Error> {
    compute_hash_excluding(path, &[])
}

pub fn compute_hash_excluding(
    path: &Path,
    exclude_names: &[&str],
) -> Result<String, std::io::Error> {
    let mut hasher = Sha256::new();
    let mut entries: BTreeMap<String, Vec<u8>> = BTreeMap::new();

    collect_files_for_hash(path, path, exclude_names, &mut entries)?;

    for (rel_path, content) in entries {
        hasher.update(rel_path.as_bytes());
        hasher.update(b"\0");
        hasher.update((content.len() as u64).to_le_bytes());
        hasher.update(&content);
    }

    let result = hasher.finalize();
    Ok(format!("sha256:{}", hex::encode(result)))
}

fn collect_files_for_hash(
    base: &Path,
    dir: &Path,
    exclude_names: &[&str],
    entries: &mut BTreeMap<String, Vec<u8>>,
) -> Result<(), std::io::Error> {
    if !dir.is_dir() {
        if dir.is_file() {
            insert_file_entry(base, dir, entries)?;
        }
        return Ok(());
    }

    for entry in std::fs::read_dir(dir)? {
        let entry = entry?;
        let path = entry.path();

        if path
            .file_name()
            .is_some_and(|n| exclude_names.iter().any(|ex| *ex == n))
        {
            continue;
        }

        if entry.metadata()?.file_type().is_symlink() {
            let target = std::fs::read_link(&path)
                .map(|t| t.to_string_lossy().into_owned())
                .unwrap_or_default();
            let rel = path
                .strip_prefix(base)
                .unwrap_or(&path)
                .to_string_lossy()
                .into_owned();
            entries.insert(rel, format!("symlink:{target}").into_bytes());
            continue;
        }

        if path.is_dir() {
            collect_files_for_hash(base, &path, exclude_names, entries)?;
        } else if path.is_file() {
            insert_file_entry(base, &path, entries)?;
        }
    }

    Ok(())
}

fn insert_file_entry(
    base: &Path,
    file: &Path,
    entries: &mut BTreeMap<String, Vec<u8>>,
) -> Result<(), std::io::Error> {
    let rel_path = file
        .strip_prefix(base)
        .unwrap_or(file)
        .to_string_lossy()
        .into_owned();
    let content = std::fs::read(file)?;
    entries.insert(rel_path, content);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use tempfile::TempDir;

    #[test]
    fn compute_hash_consistent() {
        let temp = TempDir::new().unwrap();
        std::fs::write(temp.path().join("file.txt"), "content").unwrap();

        let hash1 = compute_hash(temp.path()).unwrap();
        let hash2 = compute_hash(temp.path()).unwrap();

        assert_eq!(hash1, hash2);
        assert!(hash1.starts_with("sha256:"));
    }

    #[test]
    fn compute_hash_changes_with_content() {
        let temp = TempDir::new().unwrap();
        std::fs::write(temp.path().join("file.txt"), "content1").unwrap();
        let hash1 = compute_hash(temp.path()).unwrap();

        std::fs::write(temp.path().join("file.txt"), "content2").unwrap();
        let hash2 = compute_hash(temp.path()).unwrap();

        assert_ne!(hash1, hash2);
    }

    #[test]
    fn compute_hash_empty_dir() {
        let temp = TempDir::new().unwrap();
        let hash = compute_hash(temp.path()).unwrap();
        assert!(hash.starts_with("sha256:"));
    }

    #[cfg(unix)]
    #[test]
    fn compute_hash_includes_symlinks() {
        let temp = TempDir::new().unwrap();
        std::fs::write(temp.path().join("real.txt"), "content").unwrap();

        let hash_before = compute_hash(temp.path()).unwrap();

        let external = TempDir::new().unwrap();
        std::fs::write(external.path().join("secret.txt"), "secret").unwrap();
        std::os::unix::fs::symlink(
            external.path().join("secret.txt"),
            temp.path().join("link.txt"),
        )
        .unwrap();

        let hash_after = compute_hash(temp.path()).unwrap();
        assert_ne!(
            hash_before, hash_after,
            "Hash should change when symlink is added"
        );
    }
}
