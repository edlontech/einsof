#[derive(Debug, Clone, Default)]
pub struct NoopSandbox;

#[cfg(feature = "runtime")]
impl crate::SandboxProvider for NoopSandbox {
    fn prepare_command(
        &self,
        command: tokio::process::Command,
        _profile: &crate::SandboxProfile,
    ) -> Result<tokio::process::Command, crate::SandboxError> {
        Ok(command)
    }
}
