#[derive(Debug, thiserror::Error)]
pub enum CedarError {
    #[error("policy parse error: {0}")]
    PolicyParse(String),
    #[error("schema validation error: {0}")]
    SchemaValidation(String),
    #[error("scope manifest parse error: {0}")]
    ScopeManifestParse(String),
    #[error("io error: {0}")]
    Io(#[from] std::io::Error),
}
