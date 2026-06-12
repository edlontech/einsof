use argus_kernel::{KernelAction, KernelError};
use rustler::{NifTaggedEnum, NifUnitEnum};

use crate::enums::{CapKindN, ConfLevelN};
use crate::state::StateN;

#[derive(Debug, NifTaggedEnum)]
pub enum ActionN {
    RegisterTool(String),
    LoadInstruction(String, String),
    Delegate(String, String),
    GrantCapability(String, String, CapKindN),
    Revoke(String, String),
    CascadeRevoke(String, String),
    InvokeStart(String, String, String),
    InvokeComplete(String, String),
    ReturnEndorsed(String, String),
    ReturnUnendorsed(String, String),
    SentinelElevateTaint(String, ConfLevelN),
    SentinelRefreshBudget(String),
    GrantOverride(String, String, String, ConfLevelN),
}

impl ActionN {
    pub fn from_kernel(a: KernelAction) -> Self {
        match a {
            KernelAction::RegisterTool { tool } => Self::RegisterTool(tool.0),
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
            KernelAction::InvokeComplete { agent, inv } => Self::InvokeComplete(agent.0, inv.0),
            KernelAction::ReturnEndorsed { child, parent } => {
                Self::ReturnEndorsed(child.0, parent.0)
            }
            KernelAction::ReturnUnendorsed { child, parent } => {
                Self::ReturnUnendorsed(child.0, parent.0)
            }
            KernelAction::SentinelElevateTaint { agent, level } => {
                Self::SentinelElevateTaint(agent.0, ConfLevelN::from_kernel(level))
            }
            KernelAction::SentinelRefreshBudget { agent } => Self::SentinelRefreshBudget(agent.0),
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
    BudgetExhausted,
    MissingToolBinding,
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
            KernelError::BudgetExhausted => Self::BudgetExhausted,
            KernelError::MissingToolBinding => Self::MissingToolBinding,
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
    fn error_from_kernel_maps_capability_missing() {
        assert!(matches!(
            KernelErrorN::from_kernel(KernelError::CapabilityMissing),
            KernelErrorN::CapabilityMissing
        ));
    }
}
