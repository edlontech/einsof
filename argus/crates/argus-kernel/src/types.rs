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
    fn conf_level_ordering() {
        assert!(ConfLevel::Public < ConfLevel::Internal);
        assert!(ConfLevel::Internal < ConfLevel::Sensitive);
        assert!(ConfLevel::Sensitive < ConfLevel::Restricted);
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
}
