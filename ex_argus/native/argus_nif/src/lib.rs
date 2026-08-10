mod chain;
mod command;
#[cfg(test)]
mod conformance_tests;
mod enums;
mod event;
mod instance;
pub mod limits;
mod state;
mod wire;

pub use chain::{VERSION, genesis, genesis_transcript, link, link_transcript};
pub use command::CommandN;
pub use enums::*;
pub use event::{ActionN, ErrorN, KernelErrorN, NativeResult};
pub use instance::{LiveInstance, RecoveryInstance};
pub use state::*;
pub use wire::*;

rustler::init!("Elixir.ExArgus.Native");
