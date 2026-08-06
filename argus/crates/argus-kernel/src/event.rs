//! Canonical transition envelope. The `KernelAction` variants — one per V4 command, each carrying
//! its canonical verdict/disposition/outcome payload — are added as the transitions land in Tasks
//! A2–A5; the skeleton keeps the append-before-commit driver shape stable.

/// The recorded action of a committed transition. Uninhabited until the first transition lands.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum KernelAction {}

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
