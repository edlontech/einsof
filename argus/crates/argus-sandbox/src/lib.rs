mod build;
mod domain_match;
mod error;
mod noop;
#[cfg(feature = "runtime")]
mod os;
mod profile;
#[cfg(feature = "runtime")]
mod provider;
mod secret;
pub(crate) mod sensitive;
#[cfg(feature = "runtime")]
mod static_provider;

pub use build::ProfileBuilder;
pub use domain_match::{domain_matches, domain_matches_any};
pub use error::SandboxError;
pub use noop::NoopSandbox;
#[cfg(feature = "runtime")]
pub use os::OsSandbox;
pub use profile::{NetPolicy, SandboxProfile};
#[cfg(feature = "runtime")]
pub use provider::SandboxProvider;
pub use secret::{ResolvedEnv, SecretError, SecretProvider, SecretSource, SecretValue};
pub use sensitive::validate_path_not_sensitive;
#[cfg(feature = "runtime")]
pub use static_provider::StaticProvider;
