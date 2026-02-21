use std::collections::BTreeSet;
use std::sync::Arc;

use argus_audit::InMemoryEventStore;
use argus_gateway::proto::argus_gateway_client::ArgusGatewayClient;
use argus_gateway::{proto, ArgusGrpcService, GatewayService};
use argus_kernel::{
    BackgroundTheoryBuilder, CapKind, ConfLevel, EgressKind, FlowMode, ToolId, ToolMetadata,
};
use argus_oracle::{MockAuthorizer, MockContentGate};
use tokio::net::TcpListener;
use tonic::transport::{Channel, Server};

type TestGateway = GatewayService<MockAuthorizer, MockContentGate, InMemoryEventStore>;

fn test_gateway() -> TestGateway {
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

fn deny_gateway() -> TestGateway {
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
    GatewayService::new(
        b.build(),
        MockAuthorizer::new(),
        MockContentGate::pass_all(),
        InMemoryEventStore::new(),
    )
}

async fn start_server(gateway: TestGateway) -> ArgusGatewayClient<Channel> {
    let listener = TcpListener::bind("127.0.0.1:0").await.unwrap();
    let addr = listener.local_addr().unwrap();

    let grpc_service = ArgusGrpcService::new(Arc::new(gateway));

    tokio::spawn(async move {
        Server::builder()
            .add_service(grpc_service.into_server())
            .serve_with_incoming(tokio_stream::wrappers::TcpListenerStream::new(listener))
            .await
            .unwrap();
    });

    let endpoint = format!("http://127.0.0.1:{}", addr.port());
    loop {
        match ArgusGatewayClient::connect(endpoint.clone()).await {
            Ok(client) => break client,
            Err(_) => tokio::time::sleep(std::time::Duration::from_millis(5)).await,
        }
    }
}

#[tokio::test]
async fn grpc_register_tool() {
    let mut client = start_server(test_gateway()).await;
    let resp = client
        .register_tool(proto::RegisterToolRequest {
            tool_id: "read_file".into(),
        })
        .await
        .unwrap()
        .into_inner();

    assert_eq!(resp.sequence, 1);
    assert_eq!(
        resp.action,
        proto::KernelActionKind::KernelActionRegisterTool as i32
    );
}

#[tokio::test]
async fn grpc_delegate_and_grant_capability() {
    let mut client = start_server(test_gateway()).await;

    client
        .register_tool(proto::RegisterToolRequest {
            tool_id: "read_file".into(),
        })
        .await
        .unwrap();

    let resp = client
        .delegate(proto::DelegateRequest {
            grantor: "root".into(),
            grantee: "worker".into(),
        })
        .await
        .unwrap()
        .into_inner();
    assert_eq!(
        resp.action,
        proto::KernelActionKind::KernelActionDelegate as i32
    );

    let resp = client
        .grant_capability(proto::GrantCapabilityRequest {
            parent: "root".into(),
            child: "worker".into(),
            capability: proto::CapKind::FilesystemRead as i32,
        })
        .await
        .unwrap()
        .into_inner();
    assert_eq!(
        resp.action,
        proto::KernelActionKind::KernelActionGrantCapability as i32
    );

    let state = client
        .state_snapshot(proto::StateSnapshotRequest {})
        .await
        .unwrap()
        .into_inner();
    assert!(state.active_agents.contains(&"worker".to_string()));
    assert!(state.agent_capabilities.contains_key("worker"));
}

#[tokio::test]
async fn grpc_full_invoke_pipeline() {
    let mut client = start_server(test_gateway()).await;

    client
        .register_tool(proto::RegisterToolRequest {
            tool_id: "read_file".into(),
        })
        .await
        .unwrap();
    client
        .delegate(proto::DelegateRequest {
            grantor: "root".into(),
            grantee: "worker".into(),
        })
        .await
        .unwrap();
    client
        .grant_capability(proto::GrantCapabilityRequest {
            parent: "root".into(),
            child: "worker".into(),
            capability: proto::CapKind::FilesystemRead as i32,
        })
        .await
        .unwrap();

    let resp = client
        .invoke_start(proto::InvokeStartRequest {
            agent_id: "worker".into(),
            tool_id: "read_file".into(),
            invocation_id: "inv-1".into(),
        })
        .await
        .unwrap()
        .into_inner();
    assert_eq!(
        resp.action,
        proto::KernelActionKind::KernelActionInvokeStart as i32
    );

    let resp = client
        .invoke_complete(proto::InvokeCompleteRequest {
            agent_id: "worker".into(),
            invocation_id: "inv-1".into(),
        })
        .await
        .unwrap()
        .into_inner();
    assert_eq!(
        resp.action,
        proto::KernelActionKind::KernelActionInvokeComplete as i32
    );

    let state = client
        .state_snapshot(proto::StateSnapshotRequest {})
        .await
        .unwrap()
        .into_inner();
    let worker_flights = state.in_flight.get("worker");
    assert!(
        worker_flights.is_none() || worker_flights.unwrap().invocation_ids.is_empty()
    );
}

#[tokio::test]
async fn grpc_authorization_denial() {
    let mut client = start_server(deny_gateway()).await;

    client
        .register_tool(proto::RegisterToolRequest {
            tool_id: "read_file".into(),
        })
        .await
        .unwrap();
    client
        .delegate(proto::DelegateRequest {
            grantor: "root".into(),
            grantee: "worker".into(),
        })
        .await
        .unwrap();
    client
        .grant_capability(proto::GrantCapabilityRequest {
            parent: "root".into(),
            child: "worker".into(),
            capability: proto::CapKind::FilesystemRead as i32,
        })
        .await
        .unwrap();

    let result = client
        .invoke_start(proto::InvokeStartRequest {
            agent_id: "worker".into(),
            tool_id: "read_file".into(),
            invocation_id: "inv-1".into(),
        })
        .await;

    assert!(result.is_err());
    let status = result.unwrap_err();
    assert_eq!(status.code(), tonic::Code::FailedPrecondition);
}

#[tokio::test]
async fn grpc_state_snapshot_initial() {
    let mut client = start_server(test_gateway()).await;
    let state = client
        .state_snapshot(proto::StateSnapshotRequest {})
        .await
        .unwrap()
        .into_inner();

    assert!(state.active_agents.contains(&"root".to_string()));
    assert!(state.registered_tools.is_empty());
    assert!(state.in_flight.is_empty());
}
