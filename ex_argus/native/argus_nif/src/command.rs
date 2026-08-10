use argus_kernel::{
    AgentId, AssignmentDigest, BackgroundTheory, ChallengeId, ContentHash, InvocationId,
    KernelState, ToolId, transitions,
};
use rustler::NifUntaggedEnum;

use crate::event::{ActionN, KernelErrorN};
use crate::wire::{
    AuthorizeInspectedCommandN, BeginInvocationCommandN, CascadeRevokeCommandN,
    CrossOutputCommandN, DelegateCommandN, GrantCapabilityCommandN, GrantCrossingCommandN,
    IngestCommandN, RegisterToolCommandN, RevokeCommandN, SettleInvocationCommandN,
    UnregisterToolCommandN,
};

#[derive(Debug, Clone, PartialEq, Eq, NifUntaggedEnum)]
pub enum CommandN {
    RegisterTool(RegisterToolCommandN),
    UnregisterTool(UnregisterToolCommandN),
    Delegate(DelegateCommandN),
    GrantCapability(GrantCapabilityCommandN),
    GrantCrossing(GrantCrossingCommandN),
    Revoke(RevokeCommandN),
    CascadeRevoke(CascadeRevokeCommandN),
    Ingest(IngestCommandN),
    BeginInvocation(BeginInvocationCommandN),
    AuthorizeInspected(AuthorizeInspectedCommandN),
    SettleInvocation(SettleInvocationCommandN),
    CrossOutput(CrossOutputCommandN),
}

impl CommandN {
    pub(crate) fn canonical_tag(&self) -> u8 {
        match self {
            Self::RegisterTool(_) => 0,
            Self::UnregisterTool(_) => 1,
            Self::Delegate(_) => 2,
            Self::GrantCapability(_) => 3,
            Self::GrantCrossing(_) => 4,
            Self::Revoke(_) => 5,
            Self::CascadeRevoke(_) => 6,
            Self::Ingest(_) => 7,
            Self::BeginInvocation(_) => 8,
            Self::AuthorizeInspected(_) => 9,
            Self::SettleInvocation(_) => 10,
            Self::CrossOutput(_) => 11,
        }
    }

    pub fn apply(
        self,
        state: KernelState,
        background: &BackgroundTheory,
    ) -> Result<(KernelState, ActionN), KernelErrorN> {
        let result = match self {
            Self::RegisterTool(command) => transitions::register_tool(state, ToolId(command.tool)),
            Self::UnregisterTool(command) => {
                transitions::unregister_tool(state, ToolId(command.tool))
            }
            Self::Delegate(command) => transitions::delegate(
                state,
                background,
                AgentId(command.grantor),
                AgentId(command.grantee),
            ),
            Self::GrantCapability(command) => transitions::grant_capability(
                state,
                AgentId(command.parent),
                AgentId(command.child),
                command.cap.into_kernel(),
            ),
            Self::GrantCrossing(command) => transitions::grant_crossing(
                state,
                background,
                AgentId(command.grantor),
                AgentId(command.agent),
                AssignmentDigest(command.assignment),
                command.n,
            ),
            Self::Revoke(command) => transitions::revoke(
                state,
                background,
                AgentId(command.parent),
                AgentId(command.target),
            ),
            Self::CascadeRevoke(command) => transitions::cascade_revoke(
                state,
                background,
                AgentId(command.child),
                AgentId(command.parent),
            ),
            Self::Ingest(command) => transitions::ingest(
                state,
                background,
                AgentId(command.agent),
                command.src.map(AgentId),
                command.pconf.into_kernel(),
                command.pinteg.into_kernel(),
            ),
            Self::BeginInvocation(command) => transitions::begin_invocation(
                state,
                background,
                AgentId(command.agent),
                InvocationId(command.inv),
                ChallengeId(command.challenge),
                command.policy.into_kernel(),
                command
                    .egress
                    .into_iter()
                    .map(crate::enums::EgressKindN::into_kernel)
                    .collect(),
                ContentHash(command.args_hash),
                command.authorized,
            ),
            Self::AuthorizeInspected(command) => transitions::authorize_inspected(
                state,
                background,
                InvocationId(command.inv),
                command.attestation.into_kernel(),
            ),
            Self::SettleInvocation(command) => transitions::settle_invocation(
                state,
                InvocationId(command.inv),
                command.outcome.into_kernel(),
                command.resolution.map(|value| value.into_kernel()),
            ),
            Self::CrossOutput(command) => {
                transitions::cross_output(state, background, command.input.into_kernel())
            }
        };

        result
            .map(|(next, action)| (next, ActionN::from_kernel(action)))
            .map_err(KernelErrorN::from_kernel)
    }
}
