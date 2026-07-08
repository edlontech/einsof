use argus_kernel::{CapKind, ConfLevel, EgressKind, FlowMode, IntegLevel, VecSet};
use rustler::NifUnitEnum;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, NifUnitEnum)]
pub enum ConfLevelN {
    Public,
    Internal,
    Sensitive,
    Restricted,
}

impl ConfLevelN {
    pub fn into_kernel(self) -> ConfLevel {
        match self {
            Self::Public => ConfLevel::Public,
            Self::Internal => ConfLevel::Internal,
            Self::Sensitive => ConfLevel::Sensitive,
            Self::Restricted => ConfLevel::Restricted,
        }
    }
    pub fn from_kernel(c: ConfLevel) -> Self {
        match c {
            ConfLevel::Public => Self::Public,
            ConfLevel::Internal => Self::Internal,
            ConfLevel::Sensitive => Self::Sensitive,
            ConfLevel::Restricted => Self::Restricted,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, NifUnitEnum)]
pub enum IntegLevelN {
    Untrusted,
    Standard,
    Trusted,
    Attested,
}

impl IntegLevelN {
    pub fn into_kernel(self) -> IntegLevel {
        match self {
            Self::Untrusted => IntegLevel::Untrusted,
            Self::Standard => IntegLevel::Standard,
            Self::Trusted => IntegLevel::Trusted,
            Self::Attested => IntegLevel::Attested,
        }
    }
    pub fn from_kernel(l: IntegLevel) -> Self {
        match l {
            IntegLevel::Untrusted => Self::Untrusted,
            IntegLevel::Standard => Self::Standard,
            IntegLevel::Trusted => Self::Trusted,
            IntegLevel::Attested => Self::Attested,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, NifUnitEnum)]
pub enum EgressKindN {
    NetworkExternal,
    NetworkInternal,
    FilesystemWrite,
    Ipc,
}

impl EgressKindN {
    pub fn into_kernel(self) -> EgressKind {
        match self {
            Self::NetworkExternal => EgressKind::NetworkExternal,
            Self::NetworkInternal => EgressKind::NetworkInternal,
            Self::FilesystemWrite => EgressKind::FilesystemWrite,
            Self::Ipc => EgressKind::Ipc,
        }
    }
    pub fn from_kernel(e: EgressKind) -> Self {
        match e {
            EgressKind::NetworkExternal => Self::NetworkExternal,
            EgressKind::NetworkInternal => Self::NetworkInternal,
            EgressKind::FilesystemWrite => Self::FilesystemWrite,
            EgressKind::Ipc => Self::Ipc,
        }
    }
}

/// Decode an attested-egress list off the wire into the kernel's set representation. Shared by
/// every `attested_egress` NIF parameter (`invoke_start`/`explain_invoke`, offline and instance).
pub fn attested_into_kernel(kinds: Vec<EgressKindN>) -> VecSet<EgressKind> {
    kinds.into_iter().map(EgressKindN::into_kernel).collect()
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, NifUnitEnum)]
pub enum FlowModeN {
    Allow,
    Inspect,
    Deny,
}

impl FlowModeN {
    #[allow(dead_code)]
    pub fn into_kernel(self) -> FlowMode {
        match self {
            Self::Allow => FlowMode::Allow,
            Self::Inspect => FlowMode::Inspect,
            Self::Deny => FlowMode::Deny,
        }
    }
    pub fn from_kernel(m: FlowMode) -> Self {
        match m {
            FlowMode::Allow => Self::Allow,
            FlowMode::Inspect => Self::Inspect,
            FlowMode::Deny => Self::Deny,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, NifUnitEnum)]
pub enum CapKindN {
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
    Declassify,
    CreditBudget,
    GrantOverride,
}

impl CapKindN {
    pub fn into_kernel(self) -> CapKind {
        match self {
            Self::FilesystemRead => CapKind::FilesystemRead,
            Self::FilesystemWrite => CapKind::FilesystemWrite,
            Self::FilesystemDelete => CapKind::FilesystemDelete,
            Self::NetworkEgress => CapKind::NetworkEgress,
            Self::NetworkIngress => CapKind::NetworkIngress,
            Self::ExecutionShell => CapKind::ExecutionShell,
            Self::ExecutionCode => CapKind::ExecutionCode,
            Self::Credentials => CapKind::Credentials,
            Self::SystemInfo => CapKind::SystemInfo,
            Self::SystemModify => CapKind::SystemModify,
            Self::Clipboard => CapKind::Clipboard,
            Self::BrowserNavigate => CapKind::BrowserNavigate,
            Self::DatabaseRead => CapKind::DatabaseRead,
            Self::DatabaseWrite => CapKind::DatabaseWrite,
            Self::Ipc => CapKind::Ipc,
            Self::Declassify => CapKind::Declassify,
            Self::CreditBudget => CapKind::CreditBudget,
            Self::GrantOverride => CapKind::GrantOverride,
        }
    }
    pub fn from_kernel(c: CapKind) -> Self {
        match c {
            CapKind::FilesystemRead => Self::FilesystemRead,
            CapKind::FilesystemWrite => Self::FilesystemWrite,
            CapKind::FilesystemDelete => Self::FilesystemDelete,
            CapKind::NetworkEgress => Self::NetworkEgress,
            CapKind::NetworkIngress => Self::NetworkIngress,
            CapKind::ExecutionShell => Self::ExecutionShell,
            CapKind::ExecutionCode => Self::ExecutionCode,
            CapKind::Credentials => Self::Credentials,
            CapKind::SystemInfo => Self::SystemInfo,
            CapKind::SystemModify => Self::SystemModify,
            CapKind::Clipboard => Self::Clipboard,
            CapKind::BrowserNavigate => Self::BrowserNavigate,
            CapKind::DatabaseRead => Self::DatabaseRead,
            CapKind::DatabaseWrite => Self::DatabaseWrite,
            CapKind::Ipc => Self::Ipc,
            CapKind::Declassify => Self::Declassify,
            CapKind::CreditBudget => Self::CreditBudget,
            CapKind::GrantOverride => Self::GrantOverride,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn conf_level_roundtrips() {
        for c in [
            ConfLevel::Public,
            ConfLevel::Internal,
            ConfLevel::Sensitive,
            ConfLevel::Restricted,
        ] {
            assert_eq!(ConfLevelN::from_kernel(c).into_kernel(), c);
        }
    }

    #[test]
    fn integ_level_roundtrips() {
        for l in [
            IntegLevel::Untrusted,
            IntegLevel::Standard,
            IntegLevel::Trusted,
            IntegLevel::Attested,
        ] {
            assert_eq!(IntegLevelN::from_kernel(l).into_kernel(), l);
        }
    }

    #[test]
    fn cap_kind_roundtrips_all_18() {
        for c in CapKind::ALL {
            assert_eq!(CapKindN::from_kernel(c).into_kernel(), c);
        }
    }
}
