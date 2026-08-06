use crate::background::BackgroundTheory;
use crate::error::KernelError;
use crate::event::KernelEvent;
use crate::state::KernelState;
use crate::types::{AgentId, InvocationId, ToolId};

/// The authorizer verdict oracle. One of the two per-invocation oracle-shaped inputs V4 keeps in
/// `OracleFidelity` (the other is egress-kind classification). Inspection and conformance are NO
/// longer oracle relations — they are explicit one-use scoped attestation data the kernel checks.
pub trait AuthorizerOracle {
    fn allows(
        &self,
        agent: &AgentId,
        tool: &ToolId,
        inv: &InvocationId,
        state: &KernelState,
        background: &BackgroundTheory,
    ) -> bool;
}

/// Durable, append-before-commit event sink. Its failure leaves kernel state and sequence
/// unchanged (the driver appends before advancing).
pub trait EventStore {
    fn append(&self, event: &KernelEvent) -> Result<(), KernelError>;
}
