use argus_kernel::{
    AgentId, AuthorizerOracle, BackgroundTheory, CapKind, ContentGateOracle,
    EventStore, InvocationId, Kernel, KernelEvent, KernelState, ToolId,
};
use tokio::sync::Mutex;

use crate::GatewayError;

pub struct GatewayService<A, C, E>
where
    A: AuthorizerOracle,
    C: ContentGateOracle,
    E: EventStore,
{
    kernel: Mutex<Kernel<A, C, E>>,
}

impl<A, C, E> GatewayService<A, C, E>
where
    A: AuthorizerOracle + Send,
    C: ContentGateOracle + Send,
    E: EventStore + Send,
{
    pub fn new(
        background: BackgroundTheory,
        authorizer: A,
        content_gate: C,
        events: E,
    ) -> Self {
        Self {
            kernel: Mutex::new(Kernel::new(background, authorizer, content_gate, events)),
        }
    }

    pub async fn register_tool(&self, tool: ToolId) -> Result<KernelEvent, GatewayError> {
        let mut kernel = self.kernel.lock().await;
        Ok(kernel.register_tool(tool)?)
    }

    pub async fn delegate(
        &self,
        grantor: AgentId,
        grantee: AgentId,
    ) -> Result<KernelEvent, GatewayError> {
        let mut kernel = self.kernel.lock().await;
        Ok(kernel.delegate(grantor, grantee)?)
    }

    pub async fn grant_capability(
        &self,
        parent: AgentId,
        child: AgentId,
        cap: CapKind,
    ) -> Result<KernelEvent, GatewayError> {
        let mut kernel = self.kernel.lock().await;
        Ok(kernel.grant_capability(parent, child, cap)?)
    }

    pub async fn revoke(
        &self,
        parent: AgentId,
        target: AgentId,
    ) -> Result<KernelEvent, GatewayError> {
        let mut kernel = self.kernel.lock().await;
        Ok(kernel.revoke(parent, target)?)
    }

    pub async fn cascade_revoke(
        &self,
        child: AgentId,
        parent: AgentId,
    ) -> Result<KernelEvent, GatewayError> {
        let mut kernel = self.kernel.lock().await;
        Ok(kernel.cascade_revoke(child, parent)?)
    }

    pub async fn invoke_start(
        &self,
        agent: AgentId,
        tool: ToolId,
        inv: InvocationId,
    ) -> Result<KernelEvent, GatewayError> {
        let mut kernel = self.kernel.lock().await;
        Ok(kernel.invoke_start(agent, tool, inv)?)
    }

    pub async fn invoke_complete(
        &self,
        agent: AgentId,
        inv: InvocationId,
    ) -> Result<KernelEvent, GatewayError> {
        let mut kernel = self.kernel.lock().await;
        Ok(kernel.invoke_complete(agent, inv)?)
    }

    pub async fn return_endorsed(
        &self,
        child: AgentId,
        parent: AgentId,
    ) -> Result<KernelEvent, GatewayError> {
        let mut kernel = self.kernel.lock().await;
        Ok(kernel.return_endorsed(child, parent)?)
    }

    pub async fn return_unendorsed(
        &self,
        child: AgentId,
        parent: AgentId,
    ) -> Result<KernelEvent, GatewayError> {
        let mut kernel = self.kernel.lock().await;
        Ok(kernel.return_unendorsed(child, parent)?)
    }

    pub async fn state_snapshot(&self) -> KernelState {
        let kernel = self.kernel.lock().await;
        kernel.state().clone()
    }
}
