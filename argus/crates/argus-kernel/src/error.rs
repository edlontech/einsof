#[derive(Debug, thiserror::Error)]
pub enum KernelError {
    #[error("precondition violated: {0}")]
    PreconditionViolation(String),

    #[error("event store error: {0}")]
    EventStoreError(String),
}
