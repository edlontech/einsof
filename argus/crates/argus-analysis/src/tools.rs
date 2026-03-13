use crate::sandbox::ToolContext;
use rig::completion::ToolDefinition;
use rig::tool::Tool;
use serde::{Deserialize, Serialize};
use serde_json::json;
use std::sync::Arc;

#[derive(Debug, thiserror::Error)]
#[error("{0}")]
pub struct ToolError(String);

impl From<std::io::Error> for ToolError {
    fn from(e: std::io::Error) -> Self {
        Self(e.to_string())
    }
}

impl From<serde_json::Error> for ToolError {
    fn from(e: serde_json::Error) -> Self {
        Self(e.to_string())
    }
}

#[derive(Deserialize)]
pub struct ListDirectoryArgs {
    pub path: String,
}

pub struct ListDirectoryTool {
    pub ctx: Arc<ToolContext>,
}

impl Tool for ListDirectoryTool {
    const NAME: &'static str = "list_directory";
    type Error = ToolError;
    type Args = ListDirectoryArgs;
    type Output = String;

    async fn definition(&self, _prompt: String) -> ToolDefinition {
        ToolDefinition {
            name: "list_directory".to_string(),
            description: "List files and directories at a path relative to the target root. Returns names, sizes, and whether each entry is a directory.".to_string(),
            parameters: json!({
                "type": "object",
                "properties": {
                    "path": {
                        "type": "string",
                        "description": "Relative path to list (use '.' for root)"
                    }
                },
                "required": ["path"]
            }),
        }
    }

    async fn call(&self, args: Self::Args) -> Result<Self::Output, Self::Error> {
        let entries = self.ctx.list_directory(&args.path)?;
        Ok(serde_json::to_string_pretty(&entries)?)
    }
}

#[derive(Deserialize)]
pub struct ReadFileArgs {
    pub path: String,
    pub offset: Option<usize>,
    pub limit: Option<usize>,
}

pub struct ReadFileTool {
    pub ctx: Arc<ToolContext>,
}

impl Tool for ReadFileTool {
    const NAME: &'static str = "read_file";
    type Error = ToolError;
    type Args = ReadFileArgs;
    type Output = String;

    async fn definition(&self, _prompt: String) -> ToolDefinition {
        ToolDefinition {
            name: "read_file".to_string(),
            description: "Read the contents of a file. Supports optional line offset and limit for pagination. Binary files are rejected.".to_string(),
            parameters: json!({
                "type": "object",
                "properties": {
                    "path": {
                        "type": "string",
                        "description": "Relative path to the file"
                    },
                    "offset": {
                        "type": "integer",
                        "description": "Line number to start reading from (0-indexed)"
                    },
                    "limit": {
                        "type": "integer",
                        "description": "Maximum number of lines to return"
                    }
                },
                "required": ["path"]
            }),
        }
    }

    async fn call(&self, args: Self::Args) -> Result<Self::Output, Self::Error> {
        Ok(self.ctx.read_file(&args.path, args.offset, args.limit)?)
    }
}

#[derive(Deserialize)]
pub struct SearchCodeArgs {
    pub pattern: String,
    pub glob: Option<String>,
}

pub struct SearchCodeTool {
    pub ctx: Arc<ToolContext>,
}

impl Tool for SearchCodeTool {
    const NAME: &'static str = "search_code";
    type Error = ToolError;
    type Args = SearchCodeArgs;
    type Output = String;

    async fn definition(&self, _prompt: String) -> ToolDefinition {
        ToolDefinition {
            name: "search_code".to_string(),
            description: "Search for a regex pattern across all source files. Returns matching file paths, line numbers, and matching text. Optionally filter by glob pattern.".to_string(),
            parameters: json!({
                "type": "object",
                "properties": {
                    "pattern": {
                        "type": "string",
                        "description": "Regex pattern to search for (e.g. 'exec\\(', 'eval', 'require\\(')"
                    },
                    "glob": {
                        "type": "string",
                        "description": "Optional glob to filter files (e.g. '*.js', '*.py')"
                    }
                },
                "required": ["pattern"]
            }),
        }
    }

    async fn call(&self, args: Self::Args) -> Result<Self::Output, Self::Error> {
        let results = self.ctx.search_code(&args.pattern, args.glob.as_deref())?;
        Ok(serde_json::to_string_pretty(&results)?)
    }
}

#[derive(Deserialize)]
pub struct ReadManifestArgs {}

#[derive(Serialize)]
struct ManifestOutput {
    kind: String,
    content: String,
}

pub struct ReadManifestTool {
    pub ctx: Arc<ToolContext>,
}

impl Tool for ReadManifestTool {
    const NAME: &'static str = "read_manifest";
    type Error = ToolError;
    type Args = ReadManifestArgs;
    type Output = String;

    async fn definition(&self, _prompt: String) -> ToolDefinition {
        ToolDefinition {
            name: "read_manifest".to_string(),
            description: "Detect and read the project manifest (package.json, Cargo.toml, pyproject.toml, or go.mod). Returns the manifest type and its contents.".to_string(),
            parameters: json!({
                "type": "object",
                "properties": {},
            }),
        }
    }

    async fn call(&self, _args: Self::Args) -> Result<Self::Output, Self::Error> {
        use crate::sandbox::ManifestKind;

        let kind = self
            .ctx
            .detect_manifest()
            .ok_or_else(|| ToolError("No manifest file found".to_string()))?;

        let filename = match kind {
            ManifestKind::PackageJson => "package.json",
            ManifestKind::CargoToml => "Cargo.toml",
            ManifestKind::PyprojectToml => "pyproject.toml",
            ManifestKind::GoMod => "go.mod",
        };

        let content = self.ctx.read_file(filename, None, None)?;
        let output = ManifestOutput {
            kind: filename.to_string(),
            content,
        };

        Ok(serde_json::to_string_pretty(&output)?)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::sandbox::ToolContext;

    #[test]
    fn list_dir_tool_has_correct_name() {
        assert_eq!(ListDirectoryTool::NAME, "list_directory");
    }

    #[test]
    fn read_file_tool_has_correct_name() {
        assert_eq!(ReadFileTool::NAME, "read_file");
    }

    #[test]
    fn search_code_tool_has_correct_name() {
        assert_eq!(SearchCodeTool::NAME, "search_code");
    }

    #[test]
    fn read_manifest_tool_has_correct_name() {
        assert_eq!(ReadManifestTool::NAME, "read_manifest");
    }

    #[tokio::test]
    async fn list_dir_tool_calls_sandbox() {
        let dir = tempfile::TempDir::new().unwrap();
        std::fs::write(dir.path().join("test.js"), "hello").unwrap();
        let ctx = Arc::new(ToolContext::new(dir.path()).unwrap());
        let tool = ListDirectoryTool { ctx };
        let result = tool
            .call(ListDirectoryArgs {
                path: ".".to_string(),
            })
            .await;
        assert!(result.is_ok());
        assert!(result.unwrap().contains("test.js"));
    }

    #[tokio::test]
    async fn read_file_tool_calls_sandbox() {
        let dir = tempfile::TempDir::new().unwrap();
        std::fs::write(dir.path().join("test.js"), "console.log('hi');").unwrap();
        let ctx = Arc::new(ToolContext::new(dir.path()).unwrap());
        let tool = ReadFileTool { ctx };
        let result = tool
            .call(ReadFileArgs {
                path: "test.js".to_string(),
                offset: None,
                limit: None,
            })
            .await;
        assert!(result.is_ok());
        assert!(result.unwrap().contains("console.log"));
    }

    #[tokio::test]
    async fn search_code_tool_calls_sandbox() {
        let dir = tempfile::TempDir::new().unwrap();
        std::fs::write(dir.path().join("test.js"), "exec('rm -rf')").unwrap();
        let ctx = Arc::new(ToolContext::new(dir.path()).unwrap());
        let tool = SearchCodeTool { ctx };
        let result = tool
            .call(SearchCodeArgs {
                pattern: "exec".to_string(),
                glob: None,
            })
            .await;
        assert!(result.is_ok());
        assert!(result.unwrap().contains("exec"));
    }

    #[tokio::test]
    async fn read_manifest_tool_finds_package_json() {
        let dir = tempfile::TempDir::new().unwrap();
        std::fs::write(
            dir.path().join("package.json"),
            r#"{"name":"test","version":"1.0.0"}"#,
        )
        .unwrap();
        let ctx = Arc::new(ToolContext::new(dir.path()).unwrap());
        let tool = ReadManifestTool { ctx };
        let result = tool.call(ReadManifestArgs {}).await;
        assert!(result.is_ok());
        let output = result.unwrap();
        assert!(output.contains("package.json"));
        assert!(output.contains("test"));
    }

    #[tokio::test]
    async fn read_manifest_tool_returns_error_when_no_manifest() {
        let dir = tempfile::TempDir::new().unwrap();
        let ctx = Arc::new(ToolContext::new(dir.path()).unwrap());
        let tool = ReadManifestTool { ctx };
        let result = tool.call(ReadManifestArgs {}).await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn list_dir_tool_rejects_traversal() {
        let dir = tempfile::TempDir::new().unwrap();
        std::fs::write(dir.path().join("test.js"), "hello").unwrap();
        let ctx = Arc::new(ToolContext::new(dir.path()).unwrap());
        let tool = ListDirectoryTool { ctx };
        let result = tool
            .call(ListDirectoryArgs {
                path: "../../etc".to_string(),
            })
            .await;
        assert!(result.is_err());
    }

    #[tokio::test]
    async fn read_file_tool_with_offset_and_limit() {
        let dir = tempfile::TempDir::new().unwrap();
        std::fs::write(
            dir.path().join("lines.txt"),
            "line1\nline2\nline3\nline4\nline5\n",
        )
        .unwrap();
        let ctx = Arc::new(ToolContext::new(dir.path()).unwrap());
        let tool = ReadFileTool { ctx };
        let result = tool
            .call(ReadFileArgs {
                path: "lines.txt".to_string(),
                offset: Some(1),
                limit: Some(2),
            })
            .await;
        assert!(result.is_ok());
        let content = result.unwrap();
        assert!(content.contains("line2"));
        assert!(content.contains("line3"));
        assert!(!content.contains("line1"));
    }

    #[tokio::test]
    async fn tool_definitions_have_descriptions() {
        let dir = tempfile::TempDir::new().unwrap();
        let ctx = Arc::new(ToolContext::new(dir.path()).unwrap());

        let list_def = ListDirectoryTool { ctx: ctx.clone() }
            .definition(String::new())
            .await;
        assert_eq!(list_def.name, "list_directory");
        assert!(!list_def.description.is_empty());

        let read_def = ReadFileTool { ctx: ctx.clone() }
            .definition(String::new())
            .await;
        assert_eq!(read_def.name, "read_file");
        assert!(!read_def.description.is_empty());

        let search_def = SearchCodeTool { ctx: ctx.clone() }
            .definition(String::new())
            .await;
        assert_eq!(search_def.name, "search_code");
        assert!(!search_def.description.is_empty());

        let manifest_def = ReadManifestTool { ctx }.definition(String::new()).await;
        assert_eq!(manifest_def.name, "read_manifest");
        assert!(!manifest_def.description.is_empty());
    }
}
