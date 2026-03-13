use content_inspector::{ContentType, inspect};
use grep_regex::RegexMatcher;
use grep_searcher::sinks::UTF8;
use grep_searcher::{BinaryDetection, SearcherBuilder};
use ignore::WalkBuilder;
use serde::{Deserialize, Serialize};
use std::path::{Path, PathBuf};

const DEFAULT_MAX_FILE_SIZE: usize = 102_400;
const DEFAULT_MAX_RESULTS: usize = 50;

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct DirEntry {
    pub name: String,
    pub size: u64,
    pub is_dir: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct SearchResult {
    pub file: String,
    pub line: u32,
    pub text: String,
}

#[derive(Debug, Clone, PartialEq)]
pub enum ManifestKind {
    PackageJson,
    CargoToml,
    PyprojectToml,
    GoMod,
}

pub struct ToolContext {
    target_root: PathBuf,
    max_file_size: usize,
    max_results: usize,
}

impl ToolContext {
    pub fn new(root: &Path) -> std::io::Result<Self> {
        let target_root = root.canonicalize()?;
        Ok(Self {
            target_root,
            max_file_size: DEFAULT_MAX_FILE_SIZE,
            max_results: DEFAULT_MAX_RESULTS,
        })
    }

    pub fn with_max_file_size(mut self, max_file_size: usize) -> Self {
        self.max_file_size = max_file_size;
        self
    }

    pub fn target_root(&self) -> &Path {
        &self.target_root
    }

    pub fn resolve_path(&self, rel: &str) -> std::io::Result<PathBuf> {
        if rel.starts_with('/') {
            return Err(std::io::Error::new(
                std::io::ErrorKind::PermissionDenied,
                "absolute paths not allowed",
            ));
        }

        let joined = self.target_root.join(rel);
        let resolved = joined.canonicalize()?;

        if !resolved.starts_with(&self.target_root) {
            return Err(std::io::Error::new(
                std::io::ErrorKind::PermissionDenied,
                "path escapes target root",
            ));
        }

        Ok(resolved)
    }

    pub fn list_directory(&self, rel: &str) -> std::io::Result<Vec<DirEntry>> {
        let dir = self.resolve_path(rel)?;
        let mut entries = Vec::new();

        for result in std::fs::read_dir(&dir)? {
            let entry = result?;
            let name = entry.file_name().to_string_lossy().to_string();

            if name.starts_with('.') {
                continue;
            }

            let metadata = entry.metadata()?;
            entries.push(DirEntry {
                name,
                size: metadata.len(),
                is_dir: metadata.is_dir(),
            });
        }

        entries.sort_by(|a, b| a.name.cmp(&b.name));
        Ok(entries)
    }

    pub fn read_file(
        &self,
        rel: &str,
        offset: Option<usize>,
        limit: Option<usize>,
    ) -> std::io::Result<String> {
        let path = self.resolve_path(rel)?;

        let raw = std::fs::read(&path)?;
        if inspect(&raw) == ContentType::BINARY {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidData,
                "binary file detected",
            ));
        }

        let full_content = String::from_utf8(raw)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidData, e))?;

        let sliced = slice_lines(&full_content, offset, limit);

        if sliced.len() > self.max_file_size {
            let mut truncated = sliced[..self.max_file_size].to_string();
            truncated.push_str("\n... [truncated]");
            Ok(truncated)
        } else {
            Ok(sliced)
        }
    }

    pub fn search_code(
        &self,
        pattern: &str,
        glob_filter: Option<&str>,
    ) -> std::io::Result<Vec<SearchResult>> {
        let matcher = RegexMatcher::new(pattern)
            .map_err(|e| std::io::Error::new(std::io::ErrorKind::InvalidInput, e.to_string()))?;

        let mut builder = WalkBuilder::new(&self.target_root);
        builder.hidden(true).git_ignore(true).git_global(false);

        if let Some(glob) = glob_filter {
            let mut types_builder = ignore::types::TypesBuilder::new();
            types_builder.add("custom", glob).map_err(|e| {
                std::io::Error::new(std::io::ErrorKind::InvalidInput, e.to_string())
            })?;
            types_builder.select("custom");
            let types = types_builder.build().map_err(|e| {
                std::io::Error::new(std::io::ErrorKind::InvalidInput, e.to_string())
            })?;
            builder.types(types);
        }

        let mut results = Vec::new();
        let mut searcher = SearcherBuilder::new()
            .binary_detection(BinaryDetection::quit(0))
            .build();

        for entry in builder.build().flatten() {
            if results.len() >= self.max_results {
                break;
            }

            let path = entry.path();
            if !path.is_file() {
                continue;
            }

            let rel_path = path
                .strip_prefix(&self.target_root)
                .unwrap_or(path)
                .to_string_lossy()
                .to_string();

            let remaining = self.max_results - results.len();
            let mut file_results = Vec::new();

            let _ = searcher.search_path(
                &matcher,
                path,
                UTF8(|line_num, line| {
                    if file_results.len() < remaining {
                        file_results.push(SearchResult {
                            file: rel_path.clone(),
                            line: line_num as u32,
                            text: line.trim().to_string(),
                        });
                    }
                    Ok(true)
                }),
            );

            results.extend(file_results);
        }

        Ok(results)
    }

    pub fn detect_manifest(&self) -> Option<ManifestKind> {
        let checks = [
            ("package.json", ManifestKind::PackageJson),
            ("Cargo.toml", ManifestKind::CargoToml),
            ("pyproject.toml", ManifestKind::PyprojectToml),
            ("go.mod", ManifestKind::GoMod),
        ];

        for (file, kind) in checks {
            if self.target_root.join(file).exists() {
                return Some(kind);
            }
        }

        None
    }
}

fn slice_lines(content: &str, offset: Option<usize>, limit: Option<usize>) -> String {
    if offset.is_none() && limit.is_none() {
        return content.to_string();
    }

    let lines: Vec<&str> = content.lines().collect();
    let start = offset.unwrap_or(0);
    if start >= lines.len() {
        return String::new();
    }

    let end = limit
        .map(|l| (start + l).min(lines.len()))
        .unwrap_or(lines.len());

    lines[start..end].join("\n")
}

#[cfg(test)]
mod tests {
    use super::*;

    fn setup_test_dir() -> tempfile::TempDir {
        let dir = tempfile::TempDir::new().unwrap();
        std::fs::write(dir.path().join("index.js"), "console.log('hello');").unwrap();
        std::fs::create_dir(dir.path().join("src")).unwrap();
        std::fs::write(dir.path().join("src/main.js"), "export default {};").unwrap();
        std::fs::write(dir.path().join("package.json"), r#"{"name":"test"}"#).unwrap();
        std::fs::create_dir(dir.path().join(".git")).unwrap();
        std::fs::write(dir.path().join(".git/HEAD"), "ref: refs/heads/main").unwrap();
        dir
    }

    #[test]
    fn resolve_path_within_root() {
        let dir = setup_test_dir();
        let ctx = ToolContext::new(dir.path()).unwrap();
        assert!(ctx.resolve_path("index.js").is_ok());
        assert!(ctx.resolve_path("src/main.js").is_ok());
    }

    #[test]
    fn resolve_path_rejects_traversal() {
        let dir = setup_test_dir();
        let ctx = ToolContext::new(dir.path()).unwrap();
        assert!(ctx.resolve_path("../../../etc/passwd").is_err());
        assert!(ctx.resolve_path("/etc/passwd").is_err());
    }

    #[test]
    fn list_directory_skips_hidden() {
        let dir = setup_test_dir();
        std::fs::create_dir(dir.path().join("node_modules")).unwrap();
        let ctx = ToolContext::new(dir.path()).unwrap();
        let entries = ctx.list_directory(".").unwrap();
        assert!(!entries.iter().any(|e| e.name == ".git"));
        assert!(entries.iter().any(|e| e.name == "index.js"));
        assert!(entries.iter().any(|e| e.name == "src"));
        assert!(entries.iter().any(|e| e.name == "node_modules"));
    }

    #[test]
    fn list_directory_sorted() {
        let dir = setup_test_dir();
        let ctx = ToolContext::new(dir.path()).unwrap();
        let entries = ctx.list_directory(".").unwrap();
        let names: Vec<&str> = entries.iter().map(|e| e.name.as_str()).collect();
        let mut sorted = names.clone();
        sorted.sort();
        assert_eq!(names, sorted);
    }

    #[test]
    fn read_file_returns_content() {
        let dir = setup_test_dir();
        let ctx = ToolContext::new(dir.path()).unwrap();
        let content = ctx.read_file("index.js", None, None).unwrap();
        assert!(content.contains("console.log"));
    }

    #[test]
    fn read_file_truncates_large() {
        let dir = setup_test_dir();
        let large = "x\n".repeat(100_000);
        std::fs::write(dir.path().join("big.js"), &large).unwrap();
        let ctx = ToolContext::new(dir.path())
            .unwrap()
            .with_max_file_size(1024);
        let content = ctx.read_file("big.js", None, None).unwrap();
        assert!(content.len() < large.len());
        assert!(content.contains("[truncated]"));
    }

    #[test]
    fn read_file_rejects_binary_by_content() {
        let dir = setup_test_dir();
        std::fs::write(dir.path().join("image.png"), [0u8; 100]).unwrap();
        let ctx = ToolContext::new(dir.path()).unwrap();
        assert!(ctx.read_file("image.png", None, None).is_err());
    }

    #[test]
    fn read_file_rejects_binary_disguised_as_text() {
        let dir = setup_test_dir();
        let mut binary_content = b"looks like javascript\n".to_vec();
        binary_content.extend_from_slice(&[0u8; 50]);
        binary_content.extend_from_slice(b"more text");
        std::fs::write(dir.path().join("sneaky.js"), &binary_content).unwrap();
        let ctx = ToolContext::new(dir.path()).unwrap();
        assert!(ctx.read_file("sneaky.js", None, None).is_err());
    }

    #[test]
    fn read_file_with_offset_and_limit() {
        let dir = setup_test_dir();
        std::fs::write(
            dir.path().join("lines.txt"),
            "line1\nline2\nline3\nline4\nline5\n",
        )
        .unwrap();
        let ctx = ToolContext::new(dir.path()).unwrap();
        let content = ctx.read_file("lines.txt", Some(1), Some(2)).unwrap();
        assert!(content.contains("line2"));
        assert!(content.contains("line3"));
        assert!(!content.contains("line1"));
        assert!(!content.contains("line4"));
    }

    #[test]
    fn search_code_finds_pattern() {
        let dir = setup_test_dir();
        let ctx = ToolContext::new(dir.path()).unwrap();
        let results = ctx.search_code("console", None).unwrap();
        assert!(!results.is_empty());
        assert!(results[0].file.contains("index.js"));
    }

    #[test]
    fn search_code_skips_hidden_dirs() {
        let dir = setup_test_dir();
        let ctx = ToolContext::new(dir.path()).unwrap();
        let results = ctx.search_code("refs/heads", None).unwrap();
        assert!(results.is_empty());
    }

    #[test]
    fn detect_manifest_finds_package_json() {
        let dir = setup_test_dir();
        let ctx = ToolContext::new(dir.path()).unwrap();
        assert_eq!(ctx.detect_manifest(), Some(ManifestKind::PackageJson));
    }

    #[test]
    fn detect_manifest_finds_cargo_toml() {
        let dir = tempfile::TempDir::new().unwrap();
        std::fs::write(dir.path().join("Cargo.toml"), "[package]").unwrap();
        let ctx = ToolContext::new(dir.path()).unwrap();
        assert_eq!(ctx.detect_manifest(), Some(ManifestKind::CargoToml));
    }

    #[test]
    fn detect_manifest_none_for_empty() {
        let dir = tempfile::TempDir::new().unwrap();
        let ctx = ToolContext::new(dir.path()).unwrap();
        assert_eq!(ctx.detect_manifest(), None);
    }
}
