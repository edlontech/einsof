use std::collections::BTreeSet;

use argus_audit::InMemoryEventStore;
use argus_gateway::{GatewayService, McpManager, McpServerConfig};
use argus_kernel::{
    AgentId, BackgroundTheoryBuilder, ConfLevel, InvocationId, ToolId, ToolMetadata,
};
use argus_oracle::{MockAuthorizer, MockContentGate};
use argus_sandbox::{NoopSandbox, SandboxProfile};
use serde_json::json;

fn echo_server_path() -> String {
    std::path::PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .ancestors()
        .nth(2)
        .expect("CARGO_MANIFEST_DIR should have at least two parent directories")
        .join("target/debug/examples/echo_mcp_server")
        .to_string_lossy()
        .into_owned()
}

fn echo_server_config() -> McpServerConfig {
    McpServerConfig {
        name: "echo".to_string(),
        command: echo_server_path(),
        args: vec![],
        env: vec![],
        sandbox_profile: SandboxProfile::default(),
        sidecars: vec![],
    }
}

#[tokio::test]
async fn spawn_server_discovers_tools() {
    let mut manager = McpManager::new(NoopSandbox);
    manager.spawn_server(echo_server_config()).await.unwrap();

    let mut tools = manager.managed_tools();
    tools.sort();
    assert_eq!(tools, vec!["echo/add", "echo/echo"]);
}

#[tokio::test]
async fn call_tool_routes_to_correct_server() {
    let mut manager = McpManager::new(NoopSandbox);
    manager.spawn_server(echo_server_config()).await.unwrap();

    let result = manager
        .call_tool("echo/echo", json!({ "message": "hello world" }))
        .await
        .unwrap();

    assert_eq!(result, "hello world");
}

#[tokio::test]
async fn call_tool_add_returns_sum() {
    let mut manager = McpManager::new(NoopSandbox);
    manager.spawn_server(echo_server_config()).await.unwrap();

    let result = manager
        .call_tool("echo/add", json!({ "a": 2.0, "b": 3.0 }))
        .await
        .unwrap();

    assert_eq!(result, "5");
}

#[tokio::test]
async fn call_tool_unknown_tool_returns_error() {
    let manager = McpManager::new(NoopSandbox);

    let result = manager
        .call_tool("nonexistent/tool", json!({}))
        .await;

    assert!(result.is_err());
}

#[tokio::test]
async fn shutdown_clears_all_servers() {
    let mut manager = McpManager::new(NoopSandbox);
    manager.spawn_server(echo_server_config()).await.unwrap();

    assert!(!manager.managed_tools().is_empty());

    manager.shutdown().await;

    assert!(manager.managed_tools().is_empty());
}

#[tokio::test]
async fn spawn_all_starts_servers_from_configs() {
    let mut manager = McpManager::new(NoopSandbox);

    let results = manager.spawn_all(vec![echo_server_config()]).await;

    assert_eq!(results.len(), 1);
    assert!(results[0].is_ok());
    assert!(!manager.managed_tools().is_empty());
}

#[tokio::test]
async fn full_invoke_pipeline_with_mcp() {
    let mut mcp = McpManager::new(NoopSandbox);
    mcp.spawn_server(echo_server_config()).await.unwrap();

    let managed = mcp.managed_tools();
    assert!(managed.contains(&"echo/echo".to_string()));

    let mut bg = BackgroundTheoryBuilder::new();
    for tool_name in &managed {
        bg.register_tool(
            ToolId::new(tool_name),
            ToolMetadata {
                capabilities: BTreeSet::new(),
                egress: BTreeSet::new(),
                conf_floor: ConfLevel::Public,
                endorsed: true,
            },
        );
    }

    let gateway = GatewayService::new(
        bg.build(),
        MockAuthorizer::allow_all(),
        MockContentGate::pass_all(),
        InMemoryEventStore::new(),
    );

    for tool_name in &managed {
        gateway.register_tool(ToolId::new(tool_name)).await.unwrap();
    }

    let worker = AgentId::new("worker");
    gateway
        .delegate(AgentId::root(), worker.clone())
        .await
        .unwrap();

    let tool = ToolId::new("echo/echo");
    let inv = InvocationId::new("inv-001");

    gateway
        .invoke_start(worker.clone(), tool, inv.clone())
        .await
        .unwrap();

    let result = mcp
        .call_tool("echo/echo", json!({ "message": "authorized call" }))
        .await
        .unwrap();

    assert_eq!(result, "authorized call");

    gateway
        .invoke_complete(worker, inv)
        .await
        .unwrap();

    mcp.shutdown().await;
}
