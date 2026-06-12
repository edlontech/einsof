// The kernel is the Aeneas/Charon extraction source: it deliberately uses the explicit `match` /
// nested `if let` forms (not clippy's `unwrap_or_default` / collapsed let-chains), because the
// extractor models neither the closure-based combinators nor let-chains transparently. The wide
// `gate_egress` arity is likewise intentional (it threads the full flow-gate context).
#![allow(
    clippy::collapsible_if,
    clippy::manual_unwrap_or_default,
    clippy::too_many_arguments
)]

mod background;
mod capability;
mod collections;
mod error;
mod event;
mod kernel;
mod state;
mod traits;
pub mod transitions;
mod types;

pub use background::{
    BackgroundTheory, BackgroundTheoryBuilder, FlowMatrixError, FlowMode, ToolMetadata,
};
pub use capability::{CapKind, DomainPort, NetScope, Scope};
pub use collections::{VecMap, VecSet};
pub use error::KernelError;
pub use event::{KernelAction, KernelEvent};
pub use kernel::Kernel;
pub use state::KernelState;
pub use traits::{AuthorizerOracle, ConformanceOracle, ContentGateOracle, EventStore};
pub use types::{
    AgentId, BudgetLevel, ConfLevel, EgressKind, InstructionId, InvocationId, IssuerId,
    OverrideKey, ToolId,
};
