use std::collections::BTreeSet;
use std::sync::Arc;

use argus_audit::InMemoryEventStore;
use argus_gateway::GatewayService;
use argus_kernel::{
    AgentId, BackgroundTheoryBuilder, CapKind, ConfLevel, EgressKind, FlowMode,
    InvocationId, ToolId, ToolMetadata,
};
use argus_oracle::{MockAuthorizer, MockContentGate};

fn test_gateway() -> GatewayService<MockAuthorizer, MockContentGate, InMemoryEventStore> {
    let mut b = BackgroundTheoryBuilder::new();
    b.register_tool(
        ToolId::new("read_file"),
        ToolMetadata {
            capabilities: BTreeSet::from([CapKind::FilesystemRead]),
            egress: BTreeSet::new(),
            conf_floor: ConfLevel::Sensitive,
            endorsed: false,
        },
    );
    b.register_tool(
        ToolId::new("send_email"),
        ToolMetadata {
            capabilities: BTreeSet::from([CapKind::NetworkEgress]),
            egress: BTreeSet::from([EgressKind::NetworkExternal]),
            conf_floor: ConfLevel::Public,
            endorsed: false,
        },
    );
    b.register_tool(
        ToolId::new("check_exists"),
        ToolMetadata {
            capabilities: BTreeSet::from([CapKind::FilesystemRead]),
            egress: BTreeSet::new(),
            conf_floor: ConfLevel::Sensitive,
            endorsed: true,
        },
    );
    b.set_flow(
        ConfLevel::Public,
        EgressKind::NetworkExternal,
        FlowMode::Allow,
    );

    GatewayService::new(
        b.build(),
        MockAuthorizer::allow_all(),
        MockContentGate::pass_all(),
        InMemoryEventStore::new(),
    )
}

#[tokio::test]
async fn register_tool_records_event() {
    let gw = test_gateway();
    let event = gw.register_tool(ToolId::new("read_file")).await.unwrap();
    assert_eq!(event.sequence, 1);
}

#[tokio::test]
async fn delegation_and_capability_flow() {
    let gw = test_gateway();
    gw.register_tool(ToolId::new("read_file")).await.unwrap();

    let e1 = gw
        .delegate(AgentId::root(), AgentId::new("worker"))
        .await
        .unwrap();
    assert_eq!(e1.sequence, 2);

    gw.grant_capability(
        AgentId::root(),
        AgentId::new("worker"),
        CapKind::FilesystemRead,
    )
    .await
    .unwrap();

    let state = gw.state_snapshot().await;
    assert!(state.agent_active.contains(&AgentId::new("worker")));
    assert!(state
        .agent_cap
        .get(&AgentId::new("worker"))
        .unwrap()
        .contains(&CapKind::FilesystemRead));
}

#[tokio::test]
async fn revoke_removes_agent() {
    let gw = test_gateway();
    gw.delegate(AgentId::root(), AgentId::new("worker"))
        .await
        .unwrap();

    gw.revoke(AgentId::root(), AgentId::new("worker"))
        .await
        .unwrap();

    let state = gw.state_snapshot().await;
    assert!(!state.agent_active.contains(&AgentId::new("worker")));
}

#[tokio::test]
async fn full_invocation_pipeline() {
    let gw = test_gateway();
    gw.register_tool(ToolId::new("read_file")).await.unwrap();
    gw.delegate(AgentId::root(), AgentId::new("worker"))
        .await
        .unwrap();
    gw.grant_capability(
        AgentId::root(),
        AgentId::new("worker"),
        CapKind::FilesystemRead,
    )
    .await
    .unwrap();

    let e_start = gw
        .invoke_start(
            AgentId::new("worker"),
            ToolId::new("read_file"),
            InvocationId::new("inv-1"),
        )
        .await
        .unwrap();
    assert_eq!(e_start.sequence, 4);

    let state = gw.state_snapshot().await;
    assert!(state
        .in_flight
        .get(&AgentId::new("worker"))
        .unwrap()
        .contains(&InvocationId::new("inv-1")));

    let e_complete = gw
        .invoke_complete(AgentId::new("worker"), InvocationId::new("inv-1"))
        .await
        .unwrap();
    assert_eq!(e_complete.sequence, 5);

    let state = gw.state_snapshot().await;
    assert!(state
        .taint_levels
        .get(&AgentId::new("worker"))
        .unwrap()
        .contains(&ConfLevel::Sensitive));
}

#[tokio::test]
async fn return_endorsed_no_taint_propagation() {
    let gw = test_gateway();
    gw.register_tool(ToolId::new("read_file")).await.unwrap();
    gw.delegate(AgentId::root(), AgentId::new("parent"))
        .await
        .unwrap();
    gw.grant_capability(
        AgentId::root(),
        AgentId::new("parent"),
        CapKind::FilesystemRead,
    )
    .await
    .unwrap();
    gw.delegate(AgentId::new("parent"), AgentId::new("child"))
        .await
        .unwrap();
    gw.grant_capability(
        AgentId::new("parent"),
        AgentId::new("child"),
        CapKind::FilesystemRead,
    )
    .await
    .unwrap();

    gw.invoke_start(
        AgentId::new("child"),
        ToolId::new("read_file"),
        InvocationId::new("i1"),
    )
    .await
    .unwrap();
    gw.invoke_complete(AgentId::new("child"), InvocationId::new("i1"))
        .await
        .unwrap();

    gw.return_endorsed(AgentId::new("child"), AgentId::new("parent"))
        .await
        .unwrap();

    let state = gw.state_snapshot().await;
    assert!(!state.taint_levels.contains_key(&AgentId::new("parent")));
}

#[tokio::test]
async fn return_unendorsed_propagates_taint() {
    let gw = test_gateway();
    gw.register_tool(ToolId::new("read_file")).await.unwrap();
    gw.delegate(AgentId::root(), AgentId::new("parent"))
        .await
        .unwrap();
    gw.grant_capability(
        AgentId::root(),
        AgentId::new("parent"),
        CapKind::FilesystemRead,
    )
    .await
    .unwrap();
    gw.delegate(AgentId::new("parent"), AgentId::new("child"))
        .await
        .unwrap();
    gw.grant_capability(
        AgentId::new("parent"),
        AgentId::new("child"),
        CapKind::FilesystemRead,
    )
    .await
    .unwrap();

    gw.invoke_start(
        AgentId::new("child"),
        ToolId::new("read_file"),
        InvocationId::new("i1"),
    )
    .await
    .unwrap();
    gw.invoke_complete(AgentId::new("child"), InvocationId::new("i1"))
        .await
        .unwrap();

    gw.return_unendorsed(AgentId::new("child"), AgentId::new("parent"))
        .await
        .unwrap();

    let state = gw.state_snapshot().await;
    assert!(state
        .taint_levels
        .get(&AgentId::new("parent"))
        .unwrap()
        .contains(&ConfLevel::Sensitive));
}

#[tokio::test]
async fn authorization_denial() {
    let mut b = BackgroundTheoryBuilder::new();
    b.register_tool(
        ToolId::new("read_file"),
        ToolMetadata {
            capabilities: BTreeSet::from([CapKind::FilesystemRead]),
            egress: BTreeSet::new(),
            conf_floor: ConfLevel::Sensitive,
            endorsed: false,
        },
    );

    let gw = GatewayService::new(
        b.build(),
        MockAuthorizer::new(),
        MockContentGate::pass_all(),
        InMemoryEventStore::new(),
    );
    gw.register_tool(ToolId::new("read_file")).await.unwrap();
    gw.delegate(AgentId::root(), AgentId::new("worker"))
        .await
        .unwrap();
    gw.grant_capability(
        AgentId::root(),
        AgentId::new("worker"),
        CapKind::FilesystemRead,
    )
    .await
    .unwrap();

    let result = gw
        .invoke_start(
            AgentId::new("worker"),
            ToolId::new("read_file"),
            InvocationId::new("inv-1"),
        )
        .await;
    assert!(result.is_err());
}

#[tokio::test]
async fn precondition_unregistered_tool() {
    let gw = test_gateway();
    let result = gw.register_tool(ToolId::new("nonexistent")).await;
    assert!(result.is_err());
}

#[tokio::test]
async fn precondition_duplicate_delegate() {
    let gw = test_gateway();
    gw.delegate(AgentId::root(), AgentId::new("worker"))
        .await
        .unwrap();
    let result = gw
        .delegate(AgentId::root(), AgentId::new("worker"))
        .await;
    assert!(result.is_err());
}

#[tokio::test]
async fn concurrent_tool_registration() {
    let gw = Arc::new(test_gateway());
    let mut handles = vec![];

    for i in 0..3 {
        let tool_name = match i {
            0 => "read_file",
            1 => "send_email",
            2 => "check_exists",
            _ => unreachable!(),
        };
        let gw = Arc::clone(&gw);
        handles.push(tokio::spawn(async move {
            gw.register_tool(ToolId::new(tool_name)).await
        }));
    }

    let mut successes = 0;
    for handle in handles {
        if handle.await.unwrap().is_ok() {
            successes += 1;
        }
    }
    assert_eq!(successes, 3);

    let state = gw.state_snapshot().await;
    assert_eq!(state.tool_registered.len(), 3);
}
