use crate::capability::CapKind;
use crate::types::{AgentId, InvocationId, ToolId};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KernelAction {
    RegisterTool { tool: ToolId },
    Delegate { grantor: AgentId, grantee: AgentId },
    GrantCapability { parent: AgentId, child: AgentId, cap: CapKind },
    Revoke { parent: AgentId, target: AgentId },
    CascadeRevoke { child: AgentId, parent: AgentId },
    InvokeStart { agent: AgentId, tool: ToolId, inv: InvocationId },
    InvokeComplete { agent: AgentId, inv: InvocationId },
    ReturnEndorsed { child: AgentId, parent: AgentId },
    ReturnUnendorsed { child: AgentId, parent: AgentId },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelEvent {
    pub sequence: u64,
    pub action: KernelAction,
}

impl KernelEvent {
    pub fn new(sequence: u64, action: KernelAction) -> Self {
        Self { sequence, action }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn kernel_action_variant_count() {
        let actions = [
            KernelAction::RegisterTool { tool: ToolId::new("t") },
            KernelAction::Delegate { grantor: AgentId::root(), grantee: AgentId::new("a") },
            KernelAction::GrantCapability { parent: AgentId::root(), child: AgentId::new("a"), cap: CapKind::FilesystemRead },
            KernelAction::Revoke { parent: AgentId::root(), target: AgentId::new("a") },
            KernelAction::CascadeRevoke { child: AgentId::new("a"), parent: AgentId::root() },
            KernelAction::InvokeStart { agent: AgentId::new("a"), tool: ToolId::new("t"), inv: InvocationId::new("i") },
            KernelAction::InvokeComplete { agent: AgentId::new("a"), inv: InvocationId::new("i") },
            KernelAction::ReturnEndorsed { child: AgentId::new("a"), parent: AgentId::root() },
            KernelAction::ReturnUnendorsed { child: AgentId::new("a"), parent: AgentId::root() },
        ];
        assert_eq!(actions.len(), 9);
    }

    #[test]
    fn kernel_event_construction() {
        let event = KernelEvent::new(42, KernelAction::RegisterTool { tool: ToolId::new("t") });
        assert_eq!(event.sequence, 42);
    }
}
