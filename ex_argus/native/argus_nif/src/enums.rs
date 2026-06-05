use argus_kernel::{BudgetLevel, CapKind, ConfLevel, EgressKind, FlowMode};
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
pub enum EgressKindN {
    NetworkExternal,
    NetworkInternal,
    FilesystemWrite,
    Ipc,
}

impl EgressKindN {
    // Decode-only: egress appears only in the (decode-only) BackgroundTheory, never encoded back.
    pub fn into_kernel(self) -> EgressKind {
        match self {
            Self::NetworkExternal => EgressKind::NetworkExternal,
            Self::NetworkInternal => EgressKind::NetworkInternal,
            Self::FilesystemWrite => EgressKind::FilesystemWrite,
            Self::Ipc => EgressKind::Ipc,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, NifUnitEnum)]
pub enum FlowModeN {
    Allow,
    Inspect,
    Deny,
}

impl FlowModeN {
    // Decode-only: flow mode appears only in the (decode-only) BackgroundTheory, never encoded back.
    pub fn into_kernel(self) -> FlowMode {
        match self {
            Self::Allow => FlowMode::Allow,
            Self::Inspect => FlowMode::Inspect,
            Self::Deny => FlowMode::Deny,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, NifUnitEnum)]
pub enum BudgetLevelN {
    Exhausted,
    L1,
    L2,
    L3,
    L4,
    L5,
}

impl BudgetLevelN {
    pub fn into_kernel(self) -> BudgetLevel {
        match self {
            Self::Exhausted => BudgetLevel::Exhausted,
            Self::L1 => BudgetLevel::L1,
            Self::L2 => BudgetLevel::L2,
            Self::L3 => BudgetLevel::L3,
            Self::L4 => BudgetLevel::L4,
            Self::L5 => BudgetLevel::L5,
        }
    }
    pub fn from_kernel(b: BudgetLevel) -> Self {
        match b {
            BudgetLevel::Exhausted => Self::Exhausted,
            BudgetLevel::L1 => Self::L1,
            BudgetLevel::L2 => Self::L2,
            BudgetLevel::L3 => Self::L3,
            BudgetLevel::L4 => Self::L4,
            BudgetLevel::L5 => Self::L5,
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
    RefreshBudget,
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
            Self::RefreshBudget => CapKind::RefreshBudget,
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
            CapKind::RefreshBudget => Self::RefreshBudget,
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
    fn budget_level_roundtrips() {
        for b in [
            BudgetLevel::Exhausted,
            BudgetLevel::L1,
            BudgetLevel::L2,
            BudgetLevel::L3,
            BudgetLevel::L4,
            BudgetLevel::L5,
        ] {
            assert_eq!(BudgetLevelN::from_kernel(b).into_kernel(), b);
        }
    }

    #[test]
    fn cap_kind_roundtrips_all_17() {
        for c in CapKind::ALL {
            assert_eq!(CapKindN::from_kernel(c).into_kernel(), c);
        }
    }
}
