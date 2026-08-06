//! Canonical transition envelope. `KernelAction` gains one variant per V4 command as the
//! transitions land; the invocation/crossing variants arrive in Tasks A3–A5.

use crate::capability::CapKind;
use crate::types::{
    AgentId, AssignmentDigest, AttestationId, ConfLevel, Disposition, IntegLevel, InvocationId,
    Outcome, ToolId, Verdict,
};

/// The recorded action of a committed transition.
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
    GrantCrossing {
        grantor: AgentId,
        agent: AgentId,
        assignment: AssignmentDigest,
        n: u32,
    },
    Revoke {
        parent: AgentId,
        target: AgentId,
    },
    CascadeRevoke {
        child: AgentId,
        parent: AgentId,
    },
    Ingest {
        agent: AgentId,
        src: Option<AgentId>,
        pconf: ConfLevel,
        pinteg: IntegLevel,
        disposition: Disposition,
    },
    SettleInvocation {
        inv: InvocationId,
        agent: AgentId,
        disposition: Disposition,
        outcome: Outcome,
        clvl: ConfLevel,
        ilvl: IntegLevel,
        /// The consumed resolution attestation id, if this was the quarantine-resolution arm.
        resolution: Option<AttestationId>,
    },
    BeginInvocation {
        agent: AgentId,
        inv: InvocationId,
        tool: ToolId,
        verdict: Verdict,
        authorized: bool,
    },
    AuthorizeInspected {
        inv: InvocationId,
        attestation: AttestationId,
        admitted: bool,
    },
}

/// A durable, sequenced kernel event.
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
