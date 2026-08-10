use argus_kernel::{KernelAction, KernelError};
use rustler::{NifTaggedEnum, NifUnitEnum, NifUntaggedEnum};

use crate::enums::{ConfLevelN, CrossBranchN, DispositionN, IntegLevelN, OutcomeN, VerdictN};
use crate::wire::{
    AuthorizeInspectedActionN, BeginInvocationActionN, CascadeRevokeActionN, CrossOutputActionN,
    DelegateActionN, GrantCapabilityActionN, GrantCrossingActionN, IngestActionN,
    RegisterToolActionN, RevokeActionN, SettleInvocationActionN, UnregisterToolActionN,
};

#[derive(Debug, Clone, PartialEq, Eq, NifUntaggedEnum)]
pub enum ActionN {
    RegisterTool(RegisterToolActionN),
    UnregisterTool(UnregisterToolActionN),
    Delegate(DelegateActionN),
    GrantCapability(GrantCapabilityActionN),
    GrantCrossing(GrantCrossingActionN),
    Revoke(RevokeActionN),
    CascadeRevoke(CascadeRevokeActionN),
    Ingest(IngestActionN),
    BeginInvocation(BeginInvocationActionN),
    AuthorizeInspected(AuthorizeInspectedActionN),
    SettleInvocation(SettleInvocationActionN),
    CrossOutput(CrossOutputActionN),
}

impl ActionN {
    pub fn from_kernel(action: KernelAction) -> Self {
        match action {
            KernelAction::RegisterTool { tool } => {
                Self::RegisterTool(RegisterToolActionN { tool: tool.0 })
            }
            KernelAction::UnregisterTool { tool } => {
                Self::UnregisterTool(UnregisterToolActionN { tool: tool.0 })
            }
            KernelAction::Delegate { grantor, grantee } => Self::Delegate(DelegateActionN {
                grantor: grantor.0,
                grantee: grantee.0,
            }),
            KernelAction::GrantCapability { parent, child, cap } => {
                Self::GrantCapability(GrantCapabilityActionN {
                    parent: parent.0,
                    child: child.0,
                    cap: crate::enums::CapKindN::from_kernel(cap),
                })
            }
            KernelAction::GrantCrossing {
                grantor,
                agent,
                assignment,
                n,
            } => Self::GrantCrossing(GrantCrossingActionN {
                grantor: grantor.0,
                agent: agent.0,
                assignment: assignment.0,
                n,
            }),
            KernelAction::Revoke { parent, target } => Self::Revoke(RevokeActionN {
                parent: parent.0,
                target: target.0,
            }),
            KernelAction::CascadeRevoke { child, parent } => {
                Self::CascadeRevoke(CascadeRevokeActionN {
                    child: child.0,
                    parent: parent.0,
                })
            }
            KernelAction::Ingest {
                agent,
                src,
                pconf,
                pinteg,
                disposition,
            } => Self::Ingest(IngestActionN {
                agent: agent.0,
                src: src.map(|source| source.0),
                pconf: ConfLevelN::from_kernel(pconf),
                pinteg: IntegLevelN::from_kernel(pinteg),
                disposition: DispositionN::from_kernel(disposition),
            }),
            KernelAction::BeginInvocation {
                agent,
                inv,
                tool,
                verdict,
                authorized,
            } => Self::BeginInvocation(BeginInvocationActionN {
                agent: agent.0,
                inv: inv.0,
                tool: tool.0,
                verdict: VerdictN::from_kernel(verdict),
                authorized,
            }),
            KernelAction::AuthorizeInspected {
                inv,
                attestation,
                admitted,
            } => Self::AuthorizeInspected(AuthorizeInspectedActionN {
                inv: inv.0,
                attestation: attestation.0,
                admitted,
            }),
            KernelAction::SettleInvocation {
                inv,
                agent,
                disposition,
                outcome,
                clvl,
                ilvl,
                resolution,
            } => Self::SettleInvocation(SettleInvocationActionN {
                inv: inv.0,
                agent: agent.0,
                disposition: DispositionN::from_kernel(disposition),
                outcome: OutcomeN::from_kernel(outcome),
                clvl: ConfLevelN::from_kernel(clvl),
                ilvl: IntegLevelN::from_kernel(ilvl),
                resolution: resolution.map(|id| id.0),
            }),
            KernelAction::CrossOutput {
                src,
                rcv,
                crossing,
                branch,
                disposition,
            } => Self::CrossOutput(CrossOutputActionN {
                src: src.0,
                rcv: rcv.0,
                crossing: crossing.0,
                branch: CrossBranchN::from_kernel(branch),
                disposition: DispositionN::from_kernel(disposition),
            }),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, NifUnitEnum)]
pub enum KernelErrorN {
    ToolAlreadyRegistered,
    ToolNotRegistered,
    ToolInUse,
    AgentInactive,
    AgentAlreadyActive,
    RootNotAllowed,
    NotDirectChild,
    ParentStillActive,
    AgentHasChildren,
    CapabilityMissing,
    NotRoot,
    InvocationExists,
    InvocationReplayed,
    NotPending,
    EgressNotNarrowing,
    EgressNotCovering,
    IncoherentPolicy,
    ChallengeAlreadyOpen,
    ClearanceDenied,
    FlowGateBlocked,
    AuthorizerDenied,
    IntegrityFloorDenied,
    PairwiseConflict,
    ChallengeNotOpen,
    ChallengeScopeMismatch,
    AttestationConsumed,
    InspectionNegative,
    BlockedPending,
    NotQuarantined,
    QuarantineResolutionRequired,
    ResolutionAttestationInvalid,
    IngestHoldFailed,
    ProvenanceNotDominated,
    CrossingReplayed,
    GrantMissing,
    GrantExhausted,
    SourceInFlight,
    CrossingBoundViolated,
    CrossingHoldFailed,
    EventStore,
}

impl KernelErrorN {
    pub fn from_kernel(error: KernelError) -> Self {
        match error {
            KernelError::ToolAlreadyRegistered => Self::ToolAlreadyRegistered,
            KernelError::ToolNotRegistered => Self::ToolNotRegistered,
            KernelError::ToolInUse => Self::ToolInUse,
            KernelError::AgentInactive => Self::AgentInactive,
            KernelError::AgentAlreadyActive => Self::AgentAlreadyActive,
            KernelError::RootNotAllowed => Self::RootNotAllowed,
            KernelError::NotDirectChild => Self::NotDirectChild,
            KernelError::ParentStillActive => Self::ParentStillActive,
            KernelError::AgentHasChildren => Self::AgentHasChildren,
            KernelError::CapabilityMissing => Self::CapabilityMissing,
            KernelError::NotRoot => Self::NotRoot,
            KernelError::InvocationExists => Self::InvocationExists,
            KernelError::InvocationReplayed => Self::InvocationReplayed,
            KernelError::NotPending => Self::NotPending,
            KernelError::EgressNotNarrowing => Self::EgressNotNarrowing,
            KernelError::EgressNotCovering => Self::EgressNotCovering,
            KernelError::IncoherentPolicy => Self::IncoherentPolicy,
            KernelError::ChallengeAlreadyOpen => Self::ChallengeAlreadyOpen,
            KernelError::ClearanceDenied => Self::ClearanceDenied,
            KernelError::FlowGateBlocked => Self::FlowGateBlocked,
            KernelError::AuthorizerDenied => Self::AuthorizerDenied,
            KernelError::IntegrityFloorDenied => Self::IntegrityFloorDenied,
            KernelError::PairwiseConflict => Self::PairwiseConflict,
            KernelError::ChallengeNotOpen => Self::ChallengeNotOpen,
            KernelError::ChallengeScopeMismatch => Self::ChallengeScopeMismatch,
            KernelError::AttestationConsumed => Self::AttestationConsumed,
            KernelError::InspectionNegative => Self::InspectionNegative,
            KernelError::BlockedPending => Self::BlockedPending,
            KernelError::NotQuarantined => Self::NotQuarantined,
            KernelError::QuarantineResolutionRequired => Self::QuarantineResolutionRequired,
            KernelError::ResolutionAttestationInvalid => Self::ResolutionAttestationInvalid,
            KernelError::IngestHoldFailed => Self::IngestHoldFailed,
            KernelError::ProvenanceNotDominated => Self::ProvenanceNotDominated,
            KernelError::CrossingReplayed => Self::CrossingReplayed,
            KernelError::GrantMissing => Self::GrantMissing,
            KernelError::GrantExhausted => Self::GrantExhausted,
            KernelError::SourceInFlight => Self::SourceInFlight,
            KernelError::CrossingBoundViolated => Self::CrossingBoundViolated,
            KernelError::CrossingHoldFailed => Self::CrossingHoldFailed,
            KernelError::EventStore => Self::EventStore,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, NifTaggedEnum)]
pub enum ErrorN {
    Kernel(KernelErrorN),
    InstanceBusy,
    ResourcePoisoned,
    CapacityExceeded,
    SequenceExhausted,
    InvalidVersion,
    SequenceMismatch,
    PreviousDigestMismatch,
    ActionMismatch,
    DigestMismatch,
    RecoveryConsumed,
    FinalAnchorMismatch,
}

impl ErrorN {
    pub fn kernel(error: KernelErrorN) -> Self {
        Self::Kernel(error)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use argus_kernel::{AgentId, AttestationId, InvocationId};

    #[test]
    fn settlement_action_preserves_resolution_and_computed_fields() {
        let action = KernelAction::SettleInvocation {
            inv: InvocationId::new("inv"),
            agent: AgentId::new("agent"),
            disposition: argus_kernel::Disposition::Permitted,
            outcome: argus_kernel::Outcome::Success,
            clvl: argus_kernel::ConfLevel::Sensitive,
            ilvl: argus_kernel::IntegLevel::Trusted,
            resolution: Some(AttestationId::new("resolution")),
        };

        assert_eq!(
            ActionN::from_kernel(action),
            ActionN::SettleInvocation(SettleInvocationActionN {
                inv: "inv".to_owned(),
                agent: "agent".to_owned(),
                disposition: DispositionN::Permitted,
                outcome: OutcomeN::Success,
                clvl: ConfLevelN::Sensitive,
                ilvl: IntegLevelN::Trusted,
                resolution: Some("resolution".to_owned()),
            })
        );
    }

    #[test]
    fn kernel_error_maps_to_closed_native_reason() {
        assert_eq!(
            KernelErrorN::from_kernel(KernelError::CrossingBoundViolated),
            KernelErrorN::CrossingBoundViolated
        );
    }
}
