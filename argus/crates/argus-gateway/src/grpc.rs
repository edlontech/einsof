use std::collections::HashMap;
use std::sync::Arc;

use argus_kernel::{
    AgentId, AuthorizerOracle, CapKind, ConfLevel, ContentGateOracle, EventStore,
    InvocationId, KernelAction, KernelError, KernelEvent, KernelState, ToolId,
};
use tonic::{Request, Response, Status};

use crate::{GatewayError, GatewayService};

pub mod proto {
    tonic::include_proto!("argus.v1");
}

pub use proto::argus_gateway_server::ArgusGatewayServer;

// --- Enum conversions ---

impl From<CapKind> for proto::CapKind {
    fn from(k: CapKind) -> Self {
        match k {
            CapKind::FilesystemRead => Self::FilesystemRead,
            CapKind::FilesystemWrite => Self::FilesystemWrite,
            CapKind::FilesystemDelete => Self::FilesystemDelete,
            CapKind::NetworkEgress => Self::NetworkEgress,
            CapKind::NetworkIngress => Self::NetworkIngress,
            CapKind::ExecutionShell => Self::ExecutionShell,
            CapKind::ExecutionCode => Self::ExecutionCode,
            CapKind::Credentials => Self::Credentials,
            CapKind::SystemInfo => Self::SystemInfo,
            CapKind::SystemModify => Self::SystemModify,
            CapKind::Clipboard => Self::Clipboard,
            CapKind::BrowserNavigate => Self::BrowserNavigate,
            CapKind::DatabaseRead => Self::DatabaseRead,
            CapKind::DatabaseWrite => Self::DatabaseWrite,
            CapKind::Ipc => Self::Ipc,
        }
    }
}

impl TryFrom<proto::CapKind> for CapKind {
    type Error = Status;
    fn try_from(k: proto::CapKind) -> Result<Self, Status> {
        match k {
            proto::CapKind::Unspecified => {
                Err(Status::invalid_argument("CapKind unspecified"))
            }
            proto::CapKind::FilesystemRead => Ok(Self::FilesystemRead),
            proto::CapKind::FilesystemWrite => Ok(Self::FilesystemWrite),
            proto::CapKind::FilesystemDelete => Ok(Self::FilesystemDelete),
            proto::CapKind::NetworkEgress => Ok(Self::NetworkEgress),
            proto::CapKind::NetworkIngress => Ok(Self::NetworkIngress),
            proto::CapKind::ExecutionShell => Ok(Self::ExecutionShell),
            proto::CapKind::ExecutionCode => Ok(Self::ExecutionCode),
            proto::CapKind::Credentials => Ok(Self::Credentials),
            proto::CapKind::SystemInfo => Ok(Self::SystemInfo),
            proto::CapKind::SystemModify => Ok(Self::SystemModify),
            proto::CapKind::Clipboard => Ok(Self::Clipboard),
            proto::CapKind::BrowserNavigate => Ok(Self::BrowserNavigate),
            proto::CapKind::DatabaseRead => Ok(Self::DatabaseRead),
            proto::CapKind::DatabaseWrite => Ok(Self::DatabaseWrite),
            proto::CapKind::Ipc => Ok(Self::Ipc),
        }
    }
}

impl From<ConfLevel> for proto::ConfLevel {
    fn from(c: ConfLevel) -> Self {
        match c {
            ConfLevel::Public => Self::Public,
            ConfLevel::Internal => Self::Internal,
            ConfLevel::Sensitive => Self::Sensitive,
            ConfLevel::Restricted => Self::Restricted,
        }
    }
}

impl TryFrom<proto::ConfLevel> for ConfLevel {
    type Error = Status;
    fn try_from(c: proto::ConfLevel) -> Result<Self, Status> {
        match c {
            proto::ConfLevel::Unspecified => {
                Err(Status::invalid_argument("ConfLevel unspecified"))
            }
            proto::ConfLevel::Public => Ok(Self::Public),
            proto::ConfLevel::Internal => Ok(Self::Internal),
            proto::ConfLevel::Sensitive => Ok(Self::Sensitive),
            proto::ConfLevel::Restricted => Ok(Self::Restricted),
        }
    }
}

fn kernel_action_to_proto(action: &KernelAction) -> proto::KernelActionKind {
    match action {
        KernelAction::RegisterTool { .. } => proto::KernelActionKind::KernelActionRegisterTool,
        KernelAction::Delegate { .. } => proto::KernelActionKind::KernelActionDelegate,
        KernelAction::GrantCapability { .. } => proto::KernelActionKind::KernelActionGrantCapability,
        KernelAction::Revoke { .. } => proto::KernelActionKind::KernelActionRevoke,
        KernelAction::CascadeRevoke { .. } => proto::KernelActionKind::KernelActionCascadeRevoke,
        KernelAction::InvokeStart { .. } => proto::KernelActionKind::KernelActionInvokeStart,
        KernelAction::InvokeComplete { .. } => proto::KernelActionKind::KernelActionInvokeComplete,
        KernelAction::ReturnEndorsed { .. } => proto::KernelActionKind::KernelActionReturnEndorsed,
        KernelAction::ReturnUnendorsed { .. } => proto::KernelActionKind::KernelActionReturnUnendorsed,
    }
}

fn event_to_response(event: &KernelEvent) -> proto::EventResponse {
    proto::EventResponse {
        action: kernel_action_to_proto(&event.action) as i32,
        sequence: event.sequence,
    }
}

/// Maps kernel state to the gRPC snapshot.
/// Ghost fields `gh_taint_invoked` and `gh_taint_received` are intentionally
/// excluded -- they exist only for formal verification invariants.
fn state_to_response(state: &KernelState) -> proto::StateSnapshotResponse {
    let active_agents: Vec<String> = state.agent_active.iter().map(|a| a.0.clone()).collect();

    let agent_parents: HashMap<String, String> = state
        .agent_parent
        .iter()
        .map(|(k, v)| (k.0.clone(), v.0.clone()))
        .collect();

    let agent_capabilities: HashMap<String, proto::CapabilitySet> = state
        .agent_cap
        .iter()
        .map(|(k, v)| {
            let caps = v.iter().map(|c| proto::CapKind::from(*c) as i32).collect();
            (k.0.clone(), proto::CapabilitySet { capabilities: caps })
        })
        .collect();

    let taint_levels: HashMap<String, proto::ConfLevelSet> = state
        .taint_levels
        .iter()
        .map(|(k, v)| {
            let levels = v.iter().map(|c| proto::ConfLevel::from(*c) as i32).collect();
            (k.0.clone(), proto::ConfLevelSet { levels })
        })
        .collect();

    let in_flight: HashMap<String, proto::InvocationIdSet> = state
        .in_flight
        .iter()
        .map(|(k, v)| {
            let ids = v.iter().map(|i| i.0.clone()).collect();
            (k.0.clone(), proto::InvocationIdSet { invocation_ids: ids })
        })
        .collect();

    let invocation_tool: HashMap<String, String> = state
        .invocation_tool
        .iter()
        .map(|(k, v)| (k.0.clone(), v.0.clone()))
        .collect();

    let registered_tools: Vec<String> = state.tool_registered.iter().map(|t| t.0.clone()).collect();

    proto::StateSnapshotResponse {
        active_agents,
        agent_parents,
        agent_capabilities,
        taint_levels,
        in_flight,
        invocation_tool,
        registered_tools,
    }
}

fn gateway_error_to_status(err: GatewayError) -> Status {
    match err {
        GatewayError::Kernel(ke) => match ke {
            KernelError::PreconditionViolation(msg) => Status::failed_precondition(msg),
            KernelError::EventStoreError(msg) => Status::internal(msg),
        },
        GatewayError::Mcp(me) => Status::internal(me.to_string()),
    }
}

fn cap_kind_from_i32(v: i32) -> Result<CapKind, Status> {
    proto::CapKind::try_from(v)
        .map_err(|_| Status::invalid_argument(format!("unknown capability value: {v}")))?
        .try_into()
}

// --- gRPC service ---

pub struct ArgusGrpcService<A, C, E>
where
    A: AuthorizerOracle,
    C: ContentGateOracle,
    E: EventStore,
{
    gateway: Arc<GatewayService<A, C, E>>,
}

impl<A, C, E> ArgusGrpcService<A, C, E>
where
    A: AuthorizerOracle,
    C: ContentGateOracle,
    E: EventStore,
{
    pub fn new(gateway: Arc<GatewayService<A, C, E>>) -> Self {
        Self { gateway }
    }

    pub fn into_server(self) -> ArgusGatewayServer<Self>
    where
        A: Send + Sync + 'static,
        C: Send + Sync + 'static,
        E: Send + Sync + 'static,
    {
        ArgusGatewayServer::new(self)
    }
}

#[tonic::async_trait]
impl<A, C, E> proto::argus_gateway_server::ArgusGateway for ArgusGrpcService<A, C, E>
where
    A: AuthorizerOracle + Send + Sync + 'static,
    C: ContentGateOracle + Send + Sync + 'static,
    E: EventStore + Send + Sync + 'static,
{
    async fn register_tool(
        &self,
        request: Request<proto::RegisterToolRequest>,
    ) -> Result<Response<proto::EventResponse>, Status> {
        let req = request.into_inner();
        let event = self.gateway
            .register_tool(ToolId::new(&req.tool_id))
            .await
            .map_err(gateway_error_to_status)?;
        Ok(Response::new(event_to_response(&event)))
    }

    async fn delegate(
        &self,
        request: Request<proto::DelegateRequest>,
    ) -> Result<Response<proto::EventResponse>, Status> {
        let req = request.into_inner();
        let event = self.gateway
            .delegate(AgentId::new(&req.grantor), AgentId::new(&req.grantee))
            .await
            .map_err(gateway_error_to_status)?;
        Ok(Response::new(event_to_response(&event)))
    }

    async fn grant_capability(
        &self,
        request: Request<proto::GrantCapabilityRequest>,
    ) -> Result<Response<proto::EventResponse>, Status> {
        let req = request.into_inner();
        let cap = cap_kind_from_i32(req.capability)?;
        let event = self.gateway
            .grant_capability(
                AgentId::new(&req.parent),
                AgentId::new(&req.child),
                cap,
            )
            .await
            .map_err(gateway_error_to_status)?;
        Ok(Response::new(event_to_response(&event)))
    }

    async fn revoke(
        &self,
        request: Request<proto::RevokeRequest>,
    ) -> Result<Response<proto::EventResponse>, Status> {
        let req = request.into_inner();
        let event = self.gateway
            .revoke(AgentId::new(&req.parent), AgentId::new(&req.target))
            .await
            .map_err(gateway_error_to_status)?;
        Ok(Response::new(event_to_response(&event)))
    }

    async fn cascade_revoke(
        &self,
        request: Request<proto::CascadeRevokeRequest>,
    ) -> Result<Response<proto::EventResponse>, Status> {
        let req = request.into_inner();
        let event = self.gateway
            .cascade_revoke(AgentId::new(&req.child), AgentId::new(&req.parent))
            .await
            .map_err(gateway_error_to_status)?;
        Ok(Response::new(event_to_response(&event)))
    }

    async fn invoke_start(
        &self,
        request: Request<proto::InvokeStartRequest>,
    ) -> Result<Response<proto::EventResponse>, Status> {
        let req = request.into_inner();
        let event = self.gateway
            .invoke_start(
                AgentId::new(&req.agent_id),
                ToolId::new(&req.tool_id),
                InvocationId::new(&req.invocation_id),
            )
            .await
            .map_err(gateway_error_to_status)?;
        Ok(Response::new(event_to_response(&event)))
    }

    async fn invoke_complete(
        &self,
        request: Request<proto::InvokeCompleteRequest>,
    ) -> Result<Response<proto::EventResponse>, Status> {
        let req = request.into_inner();
        let event = self.gateway
            .invoke_complete(
                AgentId::new(&req.agent_id),
                InvocationId::new(&req.invocation_id),
            )
            .await
            .map_err(gateway_error_to_status)?;
        Ok(Response::new(event_to_response(&event)))
    }

    async fn return_endorsed(
        &self,
        request: Request<proto::ReturnEndorsedRequest>,
    ) -> Result<Response<proto::EventResponse>, Status> {
        let req = request.into_inner();
        let event = self.gateway
            .return_endorsed(AgentId::new(&req.child), AgentId::new(&req.parent))
            .await
            .map_err(gateway_error_to_status)?;
        Ok(Response::new(event_to_response(&event)))
    }

    async fn return_unendorsed(
        &self,
        request: Request<proto::ReturnUnendorsedRequest>,
    ) -> Result<Response<proto::EventResponse>, Status> {
        let req = request.into_inner();
        let event = self.gateway
            .return_unendorsed(AgentId::new(&req.child), AgentId::new(&req.parent))
            .await
            .map_err(gateway_error_to_status)?;
        Ok(Response::new(event_to_response(&event)))
    }

    async fn state_snapshot(
        &self,
        _request: Request<proto::StateSnapshotRequest>,
    ) -> Result<Response<proto::StateSnapshotResponse>, Status> {
        let state = self.gateway.state_snapshot().await;
        Ok(Response::new(state_to_response(&state)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cap_kind_roundtrip_all_variants() {
        let variants = [
            (CapKind::FilesystemRead, proto::CapKind::FilesystemRead),
            (CapKind::FilesystemWrite, proto::CapKind::FilesystemWrite),
            (CapKind::FilesystemDelete, proto::CapKind::FilesystemDelete),
            (CapKind::NetworkEgress, proto::CapKind::NetworkEgress),
            (CapKind::NetworkIngress, proto::CapKind::NetworkIngress),
            (CapKind::ExecutionShell, proto::CapKind::ExecutionShell),
            (CapKind::ExecutionCode, proto::CapKind::ExecutionCode),
            (CapKind::Credentials, proto::CapKind::Credentials),
            (CapKind::SystemInfo, proto::CapKind::SystemInfo),
            (CapKind::SystemModify, proto::CapKind::SystemModify),
            (CapKind::Clipboard, proto::CapKind::Clipboard),
            (CapKind::BrowserNavigate, proto::CapKind::BrowserNavigate),
            (CapKind::DatabaseRead, proto::CapKind::DatabaseRead),
            (CapKind::DatabaseWrite, proto::CapKind::DatabaseWrite),
            (CapKind::Ipc, proto::CapKind::Ipc),
        ];
        for (kernel, proto_val) in variants {
            let converted: proto::CapKind = kernel.into();
            assert_eq!(converted, proto_val);
            let back: CapKind = proto_val.try_into().unwrap();
            assert_eq!(back, kernel);
        }
    }

    #[test]
    fn cap_kind_unspecified_errors() {
        let result: Result<CapKind, Status> = proto::CapKind::Unspecified.try_into();
        assert!(result.is_err());
    }

    #[test]
    fn cap_kind_from_i32_invalid_errors() {
        let result = cap_kind_from_i32(999);
        assert!(result.is_err());
    }

    #[test]
    fn conf_level_roundtrip_all_variants() {
        let variants = [
            (ConfLevel::Public, proto::ConfLevel::Public),
            (ConfLevel::Internal, proto::ConfLevel::Internal),
            (ConfLevel::Sensitive, proto::ConfLevel::Sensitive),
            (ConfLevel::Restricted, proto::ConfLevel::Restricted),
        ];
        for (kernel, proto_val) in variants {
            let converted: proto::ConfLevel = kernel.into();
            assert_eq!(converted, proto_val);
            let back: ConfLevel = proto_val.try_into().unwrap();
            assert_eq!(back, kernel);
        }
    }

    #[test]
    fn conf_level_unspecified_errors() {
        let result: Result<ConfLevel, Status> = proto::ConfLevel::Unspecified.try_into();
        assert!(result.is_err());
    }

    #[test]
    fn kernel_action_to_proto_all_variants() {
        let tool = ToolId::new("t");
        let agent = AgentId::new("a");
        let parent = AgentId::root();
        let inv = InvocationId::new("i");

        let cases = [
            (KernelAction::RegisterTool { tool }, proto::KernelActionKind::KernelActionRegisterTool),
            (KernelAction::Delegate { grantor: parent.clone(), grantee: agent.clone() }, proto::KernelActionKind::KernelActionDelegate),
            (KernelAction::GrantCapability { parent: parent.clone(), child: agent.clone(), cap: CapKind::FilesystemRead }, proto::KernelActionKind::KernelActionGrantCapability),
            (KernelAction::Revoke { parent: parent.clone(), target: agent.clone() }, proto::KernelActionKind::KernelActionRevoke),
            (KernelAction::CascadeRevoke { child: agent.clone(), parent: parent.clone() }, proto::KernelActionKind::KernelActionCascadeRevoke),
            (KernelAction::InvokeStart { agent: agent.clone(), tool: ToolId::new("t"), inv: inv.clone() }, proto::KernelActionKind::KernelActionInvokeStart),
            (KernelAction::InvokeComplete { agent: agent.clone(), inv }, proto::KernelActionKind::KernelActionInvokeComplete),
            (KernelAction::ReturnEndorsed { child: agent.clone(), parent: parent.clone() }, proto::KernelActionKind::KernelActionReturnEndorsed),
            (KernelAction::ReturnUnendorsed { child: agent, parent }, proto::KernelActionKind::KernelActionReturnUnendorsed),
        ];
        for (action, expected) in cases {
            let converted = kernel_action_to_proto(&action);
            assert_eq!(converted, expected);
        }
    }

    #[test]
    fn event_response_conversion() {
        let event = KernelEvent::new(
            42,
            KernelAction::RegisterTool { tool: ToolId::new("t") },
        );
        let response = event_to_response(&event);
        assert_eq!(response.sequence, 42);
        assert_eq!(
            response.action,
            proto::KernelActionKind::KernelActionRegisterTool as i32
        );
    }

    #[test]
    fn gateway_error_to_status_precondition() {
        let err = GatewayError::Kernel(KernelError::PreconditionViolation(
            "tool not registered".into(),
        ));
        let status = gateway_error_to_status(err);
        assert_eq!(status.code(), tonic::Code::FailedPrecondition);
        assert!(status.message().contains("tool not registered"));
    }

    #[test]
    fn gateway_error_to_status_internal() {
        let err = GatewayError::Kernel(KernelError::EventStoreError("disk full".into()));
        let status = gateway_error_to_status(err);
        assert_eq!(status.code(), tonic::Code::Internal);
        assert!(status.message().contains("disk full"));
    }
}
