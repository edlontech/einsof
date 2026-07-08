use argus_kernel::{KernelAction, KernelError};
use rustler::{NifTaggedEnum, NifUnitEnum};

use crate::enums::{CapKindN, ConfLevelN, IntegLevelN};
use crate::state::StateN;

#[derive(Debug, NifTaggedEnum)]
pub enum ActionN {
    RegisterTool(String),
    UnregisterTool(String),
    LoadInstruction(String, String),
    Delegate(String, String),
    GrantCapability(String, String, CapKindN),
    Revoke(String, String),
    CascadeRevoke(String, String),
    InvokeStart(String, String, String),
    InvokeComplete(String, String, bool),
    ReturnEndorsed(String, String, ConfLevelN, IntegLevelN),
    ReturnUnendorsed(String, String),
    SentinelElevateTaint(String, ConfLevelN),
    SentinelDegradeIntegrity(String, IntegLevelN),
    SentinelCreditBudget(String, u8),
    GrantOverride(String, String, String, ConfLevelN),
}

impl ActionN {
    pub fn from_kernel(a: KernelAction) -> Self {
        match a {
            KernelAction::RegisterTool { tool } => Self::RegisterTool(tool.0),
            KernelAction::UnregisterTool { tool } => Self::UnregisterTool(tool.0),
            KernelAction::LoadInstruction { agent, instr } => {
                Self::LoadInstruction(agent.0, instr.0)
            }
            KernelAction::Delegate { grantor, grantee } => Self::Delegate(grantor.0, grantee.0),
            KernelAction::GrantCapability { parent, child, cap } => {
                Self::GrantCapability(parent.0, child.0, CapKindN::from_kernel(cap))
            }
            KernelAction::Revoke { parent, target } => Self::Revoke(parent.0, target.0),
            KernelAction::CascadeRevoke { child, parent } => Self::CascadeRevoke(child.0, parent.0),
            KernelAction::InvokeStart { agent, tool, inv } => {
                Self::InvokeStart(agent.0, tool.0, inv.0)
            }
            KernelAction::InvokeComplete { agent, inv, endorsed } => {
                Self::InvokeComplete(agent.0, inv.0, endorsed)
            }
            KernelAction::ReturnEndorsed { child, parent, clvl, ilvl } => Self::ReturnEndorsed(
                child.0,
                parent.0,
                ConfLevelN::from_kernel(clvl),
                IntegLevelN::from_kernel(ilvl),
            ),
            KernelAction::ReturnUnendorsed { child, parent } => {
                Self::ReturnUnendorsed(child.0, parent.0)
            }
            KernelAction::SentinelElevateTaint { agent, level } => {
                Self::SentinelElevateTaint(agent.0, ConfLevelN::from_kernel(level))
            }
            KernelAction::SentinelDegradeIntegrity { agent, level } => {
                Self::SentinelDegradeIntegrity(agent.0, IntegLevelN::from_kernel(level))
            }
            KernelAction::SentinelCreditBudget { agent, amount } => {
                Self::SentinelCreditBudget(agent.0, amount)
            }
            KernelAction::GrantOverride { granter, target, tool, level } => {
                Self::GrantOverride(granter.0, target.0, tool.0, ConfLevelN::from_kernel(level))
            }
        }
    }
}

#[derive(Debug, NifUnitEnum)]
pub enum KernelErrorN {
    ToolNotInTheory,
    ToolAlreadyRegistered,
    ToolNotRegistered,
    UntrustedIssuer,
    InstructionIssuerUnknown,
    AgentInactive,
    AgentAlreadyActive,
    RootNotAllowed,
    NotDirectChild,
    ParentStillActive,
    CapabilityMissing,
    InvocationExists,
    InvocationInFlight,
    NotInFlight,
    ChildHasInFlight,
    TargetHasInFlight,
    FlowGateBlocked,
    AuthorizerDenied,
    NotConforming,
    BudgetExhausted,
    MissingToolBinding,
    InvocationReplayed,
    AttestationInvalid,
    IntegrityFloorDenied,
    LeverIntegrityDenied,
    DeclarationNotCovering,
    ToolInFlight,
    EventStore,
}

impl KernelErrorN {
    pub fn from_kernel(e: KernelError) -> Self {
        match e {
            KernelError::ToolNotInTheory => Self::ToolNotInTheory,
            KernelError::ToolAlreadyRegistered => Self::ToolAlreadyRegistered,
            KernelError::ToolNotRegistered => Self::ToolNotRegistered,
            KernelError::UntrustedIssuer => Self::UntrustedIssuer,
            KernelError::InstructionIssuerUnknown => Self::InstructionIssuerUnknown,
            KernelError::AgentInactive => Self::AgentInactive,
            KernelError::AgentAlreadyActive => Self::AgentAlreadyActive,
            KernelError::RootNotAllowed => Self::RootNotAllowed,
            KernelError::NotDirectChild => Self::NotDirectChild,
            KernelError::ParentStillActive => Self::ParentStillActive,
            KernelError::CapabilityMissing => Self::CapabilityMissing,
            KernelError::InvocationExists => Self::InvocationExists,
            KernelError::InvocationInFlight => Self::InvocationInFlight,
            KernelError::NotInFlight => Self::NotInFlight,
            KernelError::ChildHasInFlight => Self::ChildHasInFlight,
            KernelError::TargetHasInFlight => Self::TargetHasInFlight,
            KernelError::FlowGateBlocked => Self::FlowGateBlocked,
            KernelError::AuthorizerDenied => Self::AuthorizerDenied,
            KernelError::NotConforming => Self::NotConforming,
            KernelError::BudgetExhausted => Self::BudgetExhausted,
            KernelError::MissingToolBinding => Self::MissingToolBinding,
            KernelError::InvocationReplayed => Self::InvocationReplayed,
            KernelError::AttestationInvalid => Self::AttestationInvalid,
            KernelError::IntegrityFloorDenied => Self::IntegrityFloorDenied,
            KernelError::LeverIntegrityDenied => Self::LeverIntegrityDenied,
            KernelError::DeclarationNotCovering => Self::DeclarationNotCovering,
            KernelError::ToolInFlight => Self::ToolInFlight,
            KernelError::EventStore => Self::EventStore,
        }
    }
}

// Transient FFI return value: it is encoded to an Elixir term and dropped immediately, so the
// Ok/Error size disparity is irrelevant and boxing would only add a needless allocation.
#[allow(clippy::large_enum_variant)]
#[derive(Debug, NifTaggedEnum)]
pub enum Outcome {
    Ok(StateN, ActionN),
    Error(KernelErrorN),
}

// Instance-transition return: the live state stays in the resource, so on success we hand
// back only the monotone seq (for the adapter's gap/reorder detection) and the action.
#[derive(Debug, NifTaggedEnum)]
pub enum InstanceOutcome {
    Ok(u64, ActionN),
    Error(KernelErrorN),
}

#[cfg(test)]
mod tests {
    use super::*;
    use argus_kernel::AgentId;

    #[test]
    fn action_from_kernel_maps_invoke_start() {
        let a = KernelAction::InvokeStart {
            agent: AgentId::new("a1"),
            tool: argus_kernel::ToolId::new("t"),
            inv: argus_kernel::InvocationId::new("i"),
        };
        match ActionN::from_kernel(a) {
            ActionN::InvokeStart(agent, tool, inv) => {
                assert_eq!((agent.as_str(), tool.as_str(), inv.as_str()), ("a1", "t", "i"));
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn action_from_kernel_maps_invoke_complete_endorsed() {
        let a = KernelAction::InvokeComplete {
            agent: AgentId::new("a1"),
            inv: argus_kernel::InvocationId::new("i"),
            endorsed: true,
        };
        match ActionN::from_kernel(a) {
            ActionN::InvokeComplete(agent, inv, endorsed) => {
                assert_eq!((agent.as_str(), inv.as_str()), ("a1", "i"));
                assert!(endorsed);
            }
            other => panic!("unexpected: {other:?}"),
        }
    }

    #[test]
    fn error_from_kernel_maps_capability_missing() {
        assert!(matches!(
            KernelErrorN::from_kernel(KernelError::CapabilityMissing),
            KernelErrorN::CapabilityMissing
        ));
    }

    #[test]
    fn error_from_kernel_maps_v3_variants() {
        assert!(matches!(
            KernelErrorN::from_kernel(KernelError::AttestationInvalid),
            KernelErrorN::AttestationInvalid
        ));
        assert!(matches!(
            KernelErrorN::from_kernel(KernelError::IntegrityFloorDenied),
            KernelErrorN::IntegrityFloorDenied
        ));
        assert!(matches!(
            KernelErrorN::from_kernel(KernelError::ToolInFlight),
            KernelErrorN::ToolInFlight
        ));
    }
}
