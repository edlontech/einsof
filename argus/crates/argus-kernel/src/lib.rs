// The kernel is the Aeneas/Charon extraction source: it deliberately uses the explicit `match` /
// nested `if let` forms (not clippy's `unwrap_or_default` / collapsed let-chains), because the
// extractor models neither the closure-based combinators nor let-chains transparently. The wide
// gate arities are likewise intentional (they thread the full flow-gate context).
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

pub use background::{BackgroundTheory, BackgroundTheoryBuilder};
pub use capability::{CapKind, DomainPort, NetScope, Scope};
pub use collections::{VecMap, VecSet};
pub use error::KernelError;
pub use event::{KernelAction, KernelEvent};
pub use kernel::Kernel;
pub use state::{KernelState, STATE_VERSION};
pub use traits::{AuthorizerOracle, EventStore};
pub use types::{
    ActionPolicySnapshot, Admission, AgentId, AssignmentDigest, AttestationId, ChallengeId,
    ChallengeScope, ConfLevel, ContentHash, CrossingGrant, CrossingId, CrossingKey, Disposition,
    EgressKind, Fallback, IntegLevel, InvocationId, Mode, Outcome, PendingInvocation, PolicyDigest,
    ToolId, Verdict,
};
