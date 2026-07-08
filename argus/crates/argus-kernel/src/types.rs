use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AgentId(pub String);

impl AgentId {
    pub fn root() -> Self {
        Self("root".to_owned())
    }

    pub fn new(name: &str) -> Self {
        Self(name.to_owned())
    }
}

impl fmt::Display for AgentId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ToolId(pub String);

impl ToolId {
    pub fn new(name: &str) -> Self {
        Self(name.to_owned())
    }
}

impl fmt::Display for ToolId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InvocationId(pub String);

impl InvocationId {
    pub fn new(id: &str) -> Self {
        Self(id.to_owned())
    }
}

impl fmt::Display for InvocationId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct IssuerId(pub String);

impl IssuerId {
    pub fn new(id: &str) -> Self {
        Self(id.to_owned())
    }
}

impl fmt::Display for IssuerId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct InstructionId(pub String);

impl InstructionId {
    pub fn new(id: &str) -> Self {
        Self(id.to_owned())
    }
}

impl fmt::Display for InstructionId {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ConfLevel {
    Public,
    Internal,
    Sensitive,
    Restricted,
}

impl ConfLevel {
    fn rank(self) -> u8 {
        match self {
            Self::Public => 0,
            Self::Internal => 1,
            Self::Sensitive => 2,
            Self::Restricted => 3,
        }
    }

    /// Total-order compare via rank (extraction-friendly: no trait dispatch).
    pub fn le(self, other: Self) -> bool {
        self.rank() <= other.rank()
    }
}

impl Ord for ConfLevel {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.rank().cmp(&other.rank())
    }
}

impl PartialOrd for ConfLevel {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

/// A consumed single-use flow-override, keyed by the `(tool, level)` it justified. A named struct
/// (not a `(ToolId, ConfLevel)` tuple) so the extractor gets a concrete derived equality instead of
/// the tuple "Pair" comparison Aeneas cannot resolve.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct OverrideKey {
    pub tool: ToolId,
    pub level: ConfLevel,
}

impl fmt::Display for ConfLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Public => f.write_str("public"),
            Self::Internal => f.write_str("internal"),
            Self::Sensitive => f.write_str("sensitive"),
            Self::Restricted => f.write_str("restricted"),
        }
    }
}

/// Protocol declassification budget capacity (fixed; not operator-configurable).
pub const BUDGET_CAPACITY: u8 = 16;

/// Sensitivity-weighted declassification cost: Public flows are free, Restricted is dearest.
pub fn declass_weight(level: ConfLevel) -> u8 {
    match level {
        ConfLevel::Public => 0,
        ConfLevel::Internal => 1,
        ConfLevel::Sensitive => 2,
        ConfLevel::Restricted => 4,
    }
}

/// The dual taint dimension: it falls as an agent ingests untrusted content (confidentiality
/// taint rises as an agent reads secret data). Mirrors `ConfLevel` exactly.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum IntegLevel {
    Untrusted,
    Standard,
    Trusted,
    Attested,
}

impl IntegLevel {
    fn rank(self) -> u8 {
        match self {
            Self::Untrusted => 0,
            Self::Standard => 1,
            Self::Trusted => 2,
            Self::Attested => 3,
        }
    }

    /// Total-order compare via rank (extraction-friendly: no trait dispatch).
    pub fn le(self, other: Self) -> bool {
        self.rank() <= other.rank()
    }
}

impl Ord for IntegLevel {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.rank().cmp(&other.rank())
    }
}

impl PartialOrd for IntegLevel {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl fmt::Display for IntegLevel {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Untrusted => f.write_str("untrusted"),
            Self::Standard => f.write_str("standard"),
            Self::Trusted => f.write_str("trusted"),
            Self::Attested => f.write_str("attested"),
        }
    }
}

/// Endorsement weight: dual of `declass_weight`. Attested content is free to endorse, untrusted
/// is dearest -- prices endorsement by how far below attested the ingested content sits.
pub fn integ_weight(level: IntegLevel) -> u8 {
    match level {
        IntegLevel::Attested => 0,
        IntegLevel::Trusted => 1,
        IntegLevel::Standard => 2,
        IntegLevel::Untrusted => 4,
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum EgressKind {
    NetworkExternal,
    NetworkInternal,
    FilesystemWrite,
    Ipc,
}

impl fmt::Display for EgressKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NetworkExternal => f.write_str("network_external"),
            Self::NetworkInternal => f.write_str("network_internal"),
            Self::FilesystemWrite => f.write_str("filesystem_write"),
            Self::Ipc => f.write_str("ipc"),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conf_level_le() {
        assert!(ConfLevel::Public.le(ConfLevel::Public));
        assert!(ConfLevel::Public.le(ConfLevel::Restricted));
        assert!(!ConfLevel::Restricted.le(ConfLevel::Sensitive));
    }

    #[test]
    fn conf_level_ordering() {
        assert!(ConfLevel::Public < ConfLevel::Internal);
        assert!(ConfLevel::Internal < ConfLevel::Sensitive);
        assert!(ConfLevel::Sensitive < ConfLevel::Restricted);
    }

    #[test]
    fn declass_weight_by_level() {
        assert_eq!(declass_weight(ConfLevel::Public), 0);
        assert_eq!(declass_weight(ConfLevel::Internal), 1);
        assert_eq!(declass_weight(ConfLevel::Sensitive), 2);
        assert_eq!(declass_weight(ConfLevel::Restricted), 4);
    }

    #[test]
    fn conf_level_equality() {
        assert_eq!(ConfLevel::Public, ConfLevel::Public);
        assert_ne!(ConfLevel::Public, ConfLevel::Internal);
    }

    #[test]
    fn integ_level_le() {
        assert!(IntegLevel::Untrusted.le(IntegLevel::Standard));
        assert!(IntegLevel::Standard.le(IntegLevel::Trusted));
        assert!(IntegLevel::Trusted.le(IntegLevel::Attested));
        assert!(!IntegLevel::Standard.le(IntegLevel::Untrusted));
        assert!(!IntegLevel::Trusted.le(IntegLevel::Standard));
        assert!(!IntegLevel::Attested.le(IntegLevel::Trusted));
    }

    #[test]
    fn integ_level_ordering() {
        assert!(IntegLevel::Untrusted < IntegLevel::Standard);
        assert!(IntegLevel::Standard < IntegLevel::Trusted);
        assert!(IntegLevel::Trusted < IntegLevel::Attested);
    }

    #[test]
    fn integ_weight_by_level() {
        assert_eq!(integ_weight(IntegLevel::Attested), 0);
        assert_eq!(integ_weight(IntegLevel::Trusted), 1);
        assert_eq!(integ_weight(IntegLevel::Standard), 2);
        assert_eq!(integ_weight(IntegLevel::Untrusted), 4);
    }

    #[test]
    fn integ_level_display() {
        assert_eq!(IntegLevel::Untrusted.to_string(), "untrusted");
        assert_eq!(IntegLevel::Standard.to_string(), "standard");
        assert_eq!(IntegLevel::Trusted.to_string(), "trusted");
        assert_eq!(IntegLevel::Attested.to_string(), "attested");
    }

    #[test]
    fn agent_id_root() {
        assert_eq!(AgentId::root(), AgentId("root".into()));
    }

    #[test]
    fn agent_id_display() {
        let id = AgentId::new("test-agent");
        assert_eq!(id.to_string(), "test-agent");
    }

    #[test]
    fn tool_id_display() {
        let id = ToolId::new("read_file");
        assert_eq!(id.to_string(), "read_file");
    }

    #[test]
    fn invocation_id_display() {
        let id = InvocationId::new("inv-001");
        assert_eq!(id.to_string(), "inv-001");
    }

    #[test]
    fn egress_kind_display() {
        assert_eq!(EgressKind::NetworkExternal.to_string(), "network_external");
        assert_eq!(EgressKind::Ipc.to_string(), "ipc");
    }

    #[test]
    fn issuer_id_display() {
        let id = IssuerId::new("sigstore-ci");
        assert_eq!(id.to_string(), "sigstore-ci");
    }

    #[test]
    fn instruction_id_display() {
        let id = InstructionId::new("system-prompt-v1");
        assert_eq!(id.to_string(), "system-prompt-v1");
    }
}
