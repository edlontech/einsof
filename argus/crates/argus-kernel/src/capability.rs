use std::fmt;
use std::path::PathBuf;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CapKind {
    FilesystemRead,
    FilesystemWrite,
    FilesystemDelete,
    NetworkEgress,
    NetworkIngress,
    ExecutionShell,
    ExecutionCode,
    Credentials,
    SystemInfo,
    SystemModify,
    Clipboard,
    BrowserNavigate,
    DatabaseRead,
    DatabaseWrite,
    Ipc,
}

impl CapKind {
    /// All capability kinds, as an owned array (extraction-friendly: no `&'static` slice).
    pub const ALL: [CapKind; 15] = [
        Self::FilesystemRead,
        Self::FilesystemWrite,
        Self::FilesystemDelete,
        Self::NetworkEgress,
        Self::NetworkIngress,
        Self::ExecutionShell,
        Self::ExecutionCode,
        Self::Credentials,
        Self::SystemInfo,
        Self::SystemModify,
        Self::Clipboard,
        Self::BrowserNavigate,
        Self::DatabaseRead,
        Self::DatabaseWrite,
        Self::Ipc,
    ];

    pub fn as_str(self) -> &'static str {
        match self {
            Self::FilesystemRead => "filesystem_read",
            Self::FilesystemWrite => "filesystem_write",
            Self::FilesystemDelete => "filesystem_delete",
            Self::NetworkEgress => "network_egress",
            Self::NetworkIngress => "network_ingress",
            Self::ExecutionShell => "execution_shell",
            Self::ExecutionCode => "execution_code",
            Self::Credentials => "credentials",
            Self::SystemInfo => "system_info",
            Self::SystemModify => "system_modify",
            Self::Clipboard => "clipboard",
            Self::BrowserNavigate => "browser_navigate",
            Self::DatabaseRead => "database_read",
            Self::DatabaseWrite => "database_write",
            Self::Ipc => "ipc",
        }
    }

    pub fn from_catalog_name(s: &str) -> Option<Self> {
        match s {
            "filesystem_read" => Some(Self::FilesystemRead),
            "filesystem_write" => Some(Self::FilesystemWrite),
            "filesystem_delete" => Some(Self::FilesystemDelete),
            "network_egress" => Some(Self::NetworkEgress),
            "network_ingress" => Some(Self::NetworkIngress),
            "execution_shell" => Some(Self::ExecutionShell),
            "execution_code" => Some(Self::ExecutionCode),
            "credentials" => Some(Self::Credentials),
            "system_info" => Some(Self::SystemInfo),
            "system_modify" => Some(Self::SystemModify),
            "clipboard" => Some(Self::Clipboard),
            "browser_navigate" => Some(Self::BrowserNavigate),
            "database_read" => Some(Self::DatabaseRead),
            "database_write" => Some(Self::DatabaseWrite),
            "ipc" => Some(Self::Ipc),
            _ => None,
        }
    }
}

impl fmt::Display for CapKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DomainPort {
    pub host: String,
    pub port: u16,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NetScope {
    Blocked,
    EgressOnly,
    EgressWithPorts(Vec<u16>),
    EgressWithDomains(Vec<DomainPort>),
    Unrestricted,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Scope {
    Filesystem { paths: Vec<PathBuf> },
    Network { policy: NetScope },
    Execution { allowed_bins: Vec<PathBuf> },
    None,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cap_kind_all_variants_count() {
        assert_eq!(CapKind::ALL.len(), 15);
    }

    #[test]
    fn cap_kind_display_roundtrip() {
        for kind in CapKind::ALL {
            let name = kind.as_str();
            let parsed = CapKind::from_catalog_name(name);
            assert_eq!(parsed, Some(kind), "roundtrip failed for {name}");
        }
    }

    #[test]
    fn cap_kind_unknown_returns_none() {
        assert_eq!(CapKind::from_catalog_name("nonexistent"), None);
    }
}
