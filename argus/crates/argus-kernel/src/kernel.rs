use crate::background::BackgroundTheory;
use crate::state::KernelState;

/// The stateful V4 kernel driver. The generic oracle/event-store parameters and the 12
/// append-before-commit transition methods are wired in Tasks A2–A5; this skeleton holds the
/// immutable state/background/sequence triple the driver advances.
pub struct Kernel {
    state: KernelState,
    background: BackgroundTheory,
    sequence: u64,
}

impl Kernel {
    pub fn new(background: BackgroundTheory) -> Self {
        Self {
            state: KernelState::initial(),
            background,
            sequence: 0,
        }
    }

    pub fn state(&self) -> &KernelState {
        &self.state
    }

    pub fn background(&self) -> &BackgroundTheory {
        &self.background
    }

    pub fn sequence(&self) -> u64 {
        self.sequence
    }
}
