#[derive(Debug, Clone)]
pub struct RegistryEntry {
    pub capabilities: Vec<String>,
    pub schema_hash: Option<String>,
}
