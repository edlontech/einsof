use argus_kernel::KernelError;
use argus_sandbox::SandboxError;

#[derive(Debug, thiserror::Error)]
pub enum GatewayError {
    #[error(transparent)]
    Kernel(#[from] KernelError),

    #[error("MCP error: {0}")]
    Mcp(#[from] McpError),
}

#[derive(Debug, thiserror::Error)]
pub enum ProxyError {
    #[error("missing X-Argus-Agent header")]
    MissingAgentHeader,

    #[error("agent not found: {0}")]
    AgentNotFound(String),

    #[error("unsupported path: {0}")]
    UnsupportedPath(String),

    #[error("no upstream configured for format")]
    NoUpstream,

    #[error("upstream request failed: {0}")]
    UpstreamRequest(#[from] reqwest::Error),

    #[error("max tool rounds ({0}) exceeded")]
    MaxRoundsExceeded(usize),

    #[error("invalid request body: {0}")]
    InvalidBody(String),

    #[error("gateway: {0}")]
    Gateway(#[from] GatewayError),

    #[error("json: {0}")]
    Json(#[from] serde_json::Error),

    #[error("upstream returned error: {status}")]
    UpstreamStatus { status: u16, body: String },
}

#[derive(Debug, thiserror::Error)]
pub enum McpError {
    #[error("failed to spawn MCP server '{name}': {source}")]
    SpawnFailed {
        name: String,
        source: std::io::Error,
    },

    #[error("MCP server '{name}' initialization failed: {reason}")]
    InitFailed { name: String, reason: String },

    #[error("no server registered for tool '{0}'")]
    NoServerForTool(String),

    #[error("tool call to '{tool}' on server '{server}' failed: {reason}")]
    CallFailed {
        server: String,
        tool: String,
        reason: String,
    },

    #[error("sidecar '{sidecar}' for MCP server '{mcp}' failed: {reason}")]
    SidecarFailed {
        mcp: String,
        sidecar: String,
        reason: String,
    },

    #[error(transparent)]
    Sandbox(#[from] SandboxError),
}
