use crate::background::BackgroundTheory;
use crate::error::KernelError;
use crate::event::KernelEvent;
use crate::state::KernelState;
use crate::types::{AgentId, ToolId};

pub trait AuthorizerOracle {
    fn allows(
        &self,
        agent: &AgentId,
        tool: &ToolId,
        state: &KernelState,
        bg: &BackgroundTheory,
    ) -> bool;
}

pub trait ContentGateOracle {
    fn passes(
        &self,
        agent: &AgentId,
        tool: &ToolId,
        state: &KernelState,
        bg: &BackgroundTheory,
    ) -> bool;
}

/// Runtime conformance oracle (TzimtzumV2 `output_conforms`): did tool `T`'s actual output
/// for `agent` match its declared bounded schema? A bounded tool only takes the zero-taint
/// (endorsed) path when this answers true; otherwise it falls back to full taint, fail-closed.
/// A distinct trust surface from `ContentGateOracle` (which inspects *arguments*) -- the honest
/// seam keeps output-schema conformance separately named in the TCB.
pub trait ConformanceOracle {
    fn conforms(
        &self,
        agent: &AgentId,
        tool: &ToolId,
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
