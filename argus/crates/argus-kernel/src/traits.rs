use crate::background::BackgroundTheory;
use crate::error::KernelError;
use crate::event::KernelEvent;
use crate::state::KernelState;
use crate::types::{AgentId, InvocationId, ToolId};

/// Per-decision authorization verdict (TzimtzumV3 `invocation_authorized`), rekeyed by
/// `InvocationId`: a static per-(agent, tool) relation cannot express "the authorizer changed
/// its mind" between two calls of the same tool, so the verdict is attested per invocation.
pub trait AuthorizerOracle {
    fn allows(
        &self,
        agent: &AgentId,
        tool: &ToolId,
        inv: &InvocationId,
        state: &KernelState,
        bg: &BackgroundTheory,
    ) -> bool;
}

/// Per-decision content-gate verdict (TzimtzumV3 `invocation_gate_passes`), rekeyed by
/// `InvocationId`: `inv` is the invocation being VOUCHED for, not necessarily the invocation
/// being gated (CHECK 2b vouches an in-flight invocation against a newly examined floor).
pub trait ContentGateOracle {
    fn passes(
        &self,
        agent: &AgentId,
        tool: &ToolId,
        inv: &InvocationId,
        state: &KernelState,
        bg: &BackgroundTheory,
    ) -> bool;
}

/// Runtime conformance oracle (TzimtzumV3 `invocation_conforms`, rekeyed by `InvocationId` from
/// the V2 `output_conforms`): did this invocation's actual output match its declared bounded
/// schema? A bounded tool only takes the zero-taint (endorsed) path when this answers true;
/// otherwise it falls back to full taint, fail-closed. A distinct trust surface from
/// `ContentGateOracle` (which inspects *arguments*) -- the honest seam keeps output-schema
/// conformance separately named in the TCB.
pub trait ConformanceOracle {
    fn conforms(
        &self,
        agent: &AgentId,
        tool: &ToolId,
        inv: &InvocationId,
        state: &KernelState,
        bg: &BackgroundTheory,
    ) -> bool;

    /// Did the endorsed cross-boundary return from `child` to `parent` conform to the
    /// declared contract? `return_endorsed` requires this (P2: closes the content-blind gap).
    fn return_conforms(
        &self,
        child: &AgentId,
        parent: &AgentId,
        state: &KernelState,
        bg: &BackgroundTheory,
    ) -> bool;
}

pub trait EventStore {
    fn append(&self, event: &KernelEvent) -> Result<(), KernelError>;
}
