use crate::capability::CapKind;
use crate::types::{AgentId, ConfLevel, InstructionId, IntegLevel, InvocationId, ToolId};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KernelAction {
    RegisterTool {
        tool: ToolId,
    },
    UnregisterTool {
        tool: ToolId,
    },
    Delegate {
        grantor: AgentId,
        grantee: AgentId,
    },
    GrantCapability {
        parent: AgentId,
        child: AgentId,
        cap: CapKind,
    },
    Revoke {
        parent: AgentId,
        target: AgentId,
    },
    CascadeRevoke {
        child: AgentId,
        parent: AgentId,
    },
    InvokeStart {
        agent: AgentId,
        tool: ToolId,
        inv: InvocationId,
    },
    InvokeComplete {
        agent: AgentId,
        inv: InvocationId,
        endorsed: bool,
    },
    ReturnEndorsed {
        child: AgentId,
        parent: AgentId,
        clvl: ConfLevel,
        ilvl: IntegLevel,
    },
    ReturnUnendorsed {
        child: AgentId,
        parent: AgentId,
    },
    SentinelElevateTaint {
        agent: AgentId,
        level: ConfLevel,
    },
    SentinelDegradeIntegrity {
        agent: AgentId,
        level: IntegLevel,
    },
    SentinelCreditBudget {
        agent: AgentId,
        amount: u8,
    },
    LoadInstruction {
        agent: AgentId,
        instr: InstructionId,
    },
    GrantOverride {
        granter: AgentId,
        target: AgentId,
        tool: ToolId,
        level: ConfLevel,
    },
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
            KernelAction::RegisterTool {
                tool: ToolId::new("t"),
            },
            KernelAction::UnregisterTool {
                tool: ToolId::new("t"),
            },
            KernelAction::Delegate {
                grantor: AgentId::root(),
                grantee: AgentId::new("a"),
            },
            KernelAction::GrantCapability {
                parent: AgentId::root(),
                child: AgentId::new("a"),
                cap: CapKind::FilesystemRead,
            },
            KernelAction::Revoke {
                parent: AgentId::root(),
                target: AgentId::new("a"),
            },
            KernelAction::CascadeRevoke {
                child: AgentId::new("a"),
                parent: AgentId::root(),
            },
            KernelAction::InvokeStart {
                agent: AgentId::new("a"),
                tool: ToolId::new("t"),
                inv: InvocationId::new("i"),
            },
            KernelAction::InvokeComplete {
                agent: AgentId::new("a"),
                inv: InvocationId::new("i"),
                endorsed: false,
            },
            KernelAction::ReturnEndorsed {
                child: AgentId::new("a"),
                parent: AgentId::root(),
                clvl: ConfLevel::Sensitive,
                ilvl: IntegLevel::Attested,
            },
            KernelAction::ReturnUnendorsed {
                child: AgentId::new("a"),
                parent: AgentId::root(),
            },
            KernelAction::SentinelElevateTaint {
                agent: AgentId::new("a"),
                level: ConfLevel::Sensitive,
            },
            KernelAction::SentinelDegradeIntegrity {
                agent: AgentId::new("a"),
                level: IntegLevel::Untrusted,
            },
            KernelAction::SentinelCreditBudget {
                agent: AgentId::new("a"),
                amount: 1,
            },
            KernelAction::LoadInstruction {
                agent: AgentId::new("a"),
                instr: InstructionId::new("i"),
            },
            KernelAction::GrantOverride {
                granter: AgentId::root(),
                target: AgentId::new("a"),
                tool: ToolId::new("t"),
                level: ConfLevel::Sensitive,
            },
        ];
        assert_eq!(actions.len(), 15);
    }

    #[test]
    fn kernel_event_construction() {
        let event = KernelEvent::new(
            42,
            KernelAction::RegisterTool {
                tool: ToolId::new("t"),
            },
        );
        assert_eq!(event.sequence, 42);
    }
}
