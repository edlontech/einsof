use std::io;
use std::path::PathBuf;

#[derive(Debug, thiserror::Error)]
pub enum SandboxError {
    #[error("failed to spawn sandboxed process: {0}")]
    SpawnFailed(#[from] io::Error),

    #[error("sandbox profile generation failed: {reason}")]
    ProfileError { reason: String },

    #[error("path {path} denied: {reason}")]
    SensitivePath { path: PathBuf, reason: String },

    #[error("sandbox wrapper binary not found: {reason}")]
    WrapperNotFound { reason: String },

    #[error("failed to write sandbox profile: {0}")]
    ProfileWriteFailed(io::Error),
}
