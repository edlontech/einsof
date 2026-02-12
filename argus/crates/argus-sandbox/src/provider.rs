use tokio::process::Command;

use crate::{SandboxError, SandboxProfile};

pub trait SandboxProvider: Send + Sync {
    fn prepare_command(
        &self,
        command: Command,
        profile: &SandboxProfile,
    ) -> Result<Command, SandboxError>;
}

impl<T: SandboxProvider + ?Sized> SandboxProvider for Box<T> {
    fn prepare_command(
        &self,
        command: Command,
        profile: &SandboxProfile,
    ) -> Result<Command, SandboxError> {
        (**self).prepare_command(command, profile)
    }
}
