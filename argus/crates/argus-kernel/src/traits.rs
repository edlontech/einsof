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

pub trait EventStore {
    fn append(&self, event: &KernelEvent) -> Result<(), KernelError>;
}
