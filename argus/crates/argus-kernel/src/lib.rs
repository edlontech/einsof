mod background;
mod capability;
mod error;
mod event;
mod kernel;
mod state;
mod traits;
pub(crate) mod transitions;
mod types;

pub use background::{BackgroundTheory, BackgroundTheoryBuilder, FlowMode, ToolMetadata};
pub use capability::{CapKind, DomainPort, NetScope, Scope};
pub use error::KernelError;
pub use event::{KernelAction, KernelEvent};
pub use kernel::Kernel;
pub use state::KernelState;
pub use traits::{AuthorizerOracle, ConformanceOracle, ContentGateOracle, EventStore};
pub use types::{
    AgentId, BudgetLevel, ConfLevel, EgressKind, InstructionId, InvocationId, IssuerId,
    OverrideKey, ToolId,
};
