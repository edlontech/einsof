use thiserror::Error;

#[derive(Error, Debug)]
pub enum AnalysisError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("LLM inference error: {0}")]
    LlmInference(String),
    #[error("Parse error: {0}")]
    Parse(String),
    #[error("Invalid path: {0}")]
    InvalidPath(String),
}

pub type Result<T> = std::result::Result<T, AnalysisError>;

pub fn client_error<E: std::fmt::Display>(provider: &str, e: E) -> AnalysisError {
    AnalysisError::LlmInference(format!("{} client: {}", provider, e))
}

pub fn get_env_var(name: &str) -> Result<String> {
    std::env::var(name)
        .map_err(|_| AnalysisError::LlmInference(format!("Environment variable {} not set", name)))
}
