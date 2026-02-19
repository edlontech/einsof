use rmcp::handler::server::{tool::ToolRouter, wrapper::Parameters};
use rmcp::model::*;
use rmcp::schemars;
use rmcp::serde;
use rmcp::service::ServiceExt;
use rmcp::transport::io::stdio;
use rmcp::{tool, tool_handler, tool_router, ErrorData as McpError};

#[derive(Clone)]
struct EchoServer {
    tool_router: ToolRouter<Self>,
}

impl EchoServer {
    fn new() -> Self {
        Self {
            tool_router: Self::tool_router(),
        }
    }
}

#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
struct EchoParams {
    message: String,
}

#[derive(Debug, serde::Deserialize, schemars::JsonSchema)]
struct AddParams {
    a: f64,
    b: f64,
}

#[tool_router]
impl EchoServer {
    #[tool(description = "Echoes the input message back")]
    fn echo(
        &self,
        Parameters(params): Parameters<EchoParams>,
    ) -> Result<CallToolResult, McpError> {
        Ok(CallToolResult::success(vec![Content::text(params.message)]))
    }

    #[tool(description = "Adds two numbers")]
    fn add(
        &self,
        Parameters(params): Parameters<AddParams>,
    ) -> Result<CallToolResult, McpError> {
        Ok(CallToolResult::success(vec![Content::text(
            (params.a + params.b).to_string(),
        )]))
    }
}

#[tool_handler]
impl rmcp::ServerHandler for EchoServer {
    fn get_info(&self) -> ServerInfo {
        ServerInfo {
            protocol_version: ProtocolVersion::V_2024_11_05,
            capabilities: ServerCapabilities::builder().enable_tools().build(),
            server_info: Implementation {
                name: "echo-test-server".into(),
                version: "0.1.0".into(),
                ..Default::default()
            },
            instructions: Some("A test echo MCP server for integration tests".into()),
        }
    }
}

#[tokio::main]
async fn main() -> Result<(), Box<dyn std::error::Error>> {
    let service = EchoServer::new().serve(stdio()).await?;
    service.waiting().await?;
    Ok(())
}
