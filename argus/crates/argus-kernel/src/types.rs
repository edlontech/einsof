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

/// Flow-policy key (the `(level, egress)` pair the policy table maps to a `FlowMode`). Named
/// struct rather than a tuple key, for the same extraction reason as `OverrideKey`.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug, Hash)]
pub struct FlowKey {
    pub level: ConfLevel,
    pub egress: EgressKind,
}

/// A flow-override grant in the background theory (the `(agent, tool, level)` triple that licenses
/// a single DENY-mode flow). Named struct rather than a tuple element.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Debug)]
pub struct OverrideEntry {
    pub agent: AgentId,
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

/// Declassification budget level (TzimtzumV2 `BudgetLevel`): a finite saturating ladder
/// `Exhausted < L1 < L2 < L3 < L4 < L5`. `L5` is full; each endorsement debits one level;
/// `Exhausted` blocks the zero-taint path (fail-closed). `#[derive(Ord)]` follows declaration
/// order, so `Exhausted` is the minimum.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum BudgetLevel {
    Exhausted,
    L1,
    L2,
    L3,
    L4,
    L5,
}

impl BudgetLevel {
    /// The full budget a fresh agent starts with.
    pub fn full() -> Self {
        Self::L5
    }

    /// Step down one level, saturating at `Exhausted` (mirrors Veil `budget_debit`).
    pub fn debit(self) -> Self {
        match self {
            Self::L5 => Self::L4,
            Self::L4 => Self::L3,
            Self::L3 => Self::L2,
            Self::L2 => Self::L1,
            Self::L1 => Self::Exhausted,
            Self::Exhausted => Self::Exhausted,
        }
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
    fn budget_level_ordering() {
        assert!(BudgetLevel::Exhausted < BudgetLevel::L1);
        assert!(BudgetLevel::L1 < BudgetLevel::L5);
        assert_eq!(BudgetLevel::full(), BudgetLevel::L5);
    }

    #[test]
    fn budget_level_debit_saturates() {
        assert_eq!(BudgetLevel::L5.debit(), BudgetLevel::L4);
        assert_eq!(BudgetLevel::L1.debit(), BudgetLevel::Exhausted);
        assert_eq!(BudgetLevel::Exhausted.debit(), BudgetLevel::Exhausted);
    }

    #[test]
    fn conf_level_equality() {
        assert_eq!(ConfLevel::Public, ConfLevel::Public);
        assert_ne!(ConfLevel::Public, ConfLevel::Internal);
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
