use argus_kernel::{
    CapKind, ConfLevel, CrossBranch, Disposition, EgressKind, Fallback, IntegLevel, Mode, Outcome,
    Verdict,
};
use rustler::{NifTaggedEnum, NifUnitEnum};

macro_rules! unit_wire_enum {
    ($native:ident, $kernel:ty, [$($variant:ident),+ $(,)?]) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, NifUnitEnum)]
        pub enum $native {
            $($variant),+
        }

        impl $native {
            pub fn into_kernel(self) -> $kernel {
                match self {
                    $(Self::$variant => <$kernel>::$variant),+
                }
            }

            pub fn from_kernel(value: $kernel) -> Self {
                match value {
                    $(<$kernel>::$variant => Self::$variant),+
                }
            }
        }
    };
}

unit_wire_enum!(
    ConfLevelN,
    ConfLevel,
    [Public, Internal, Sensitive, Restricted]
);
unit_wire_enum!(
    IntegLevelN,
    IntegLevel,
    [Untrusted, Standard, Trusted, Attested]
);
unit_wire_enum!(
    EgressKindN,
    EgressKind,
    [NetworkExternal, NetworkInternal, FilesystemWrite, Ipc]
);
unit_wire_enum!(
    CapKindN,
    CapKind,
    [
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
    ]
);
unit_wire_enum!(VerdictN, Verdict, [Allow, InspectionRequired, Deny]);
unit_wire_enum!(
    DispositionN,
    Disposition,
    [Permitted, Blocked, MonitorBypassed]
);
unit_wire_enum!(ModeN, Mode, [Enforce, Monitor]);
unit_wire_enum!(OutcomeN, Outcome, [Success, Failure, Ambiguous]);
unit_wire_enum!(FallbackN, Fallback, [Fail, ReleaseUnendorsed]);
unit_wire_enum!(CrossBranchN, CrossBranch, [Endorsed, Unendorsed, Fail]);

#[derive(Debug, Clone, PartialEq, Eq, NifTaggedEnum)]
pub enum AdmissionN {
    Plain,
    Inspected(String),
    Bypassed,
}

impl AdmissionN {
    pub fn into_kernel(self) -> argus_kernel::Admission {
        match self {
            Self::Plain => argus_kernel::Admission::Plain,
            Self::Inspected(id) => {
                argus_kernel::Admission::Inspected(argus_kernel::AttestationId(id))
            }
            Self::Bypassed => argus_kernel::Admission::Bypassed,
        }
    }

    pub fn from_kernel(value: argus_kernel::Admission) -> Self {
        match value {
            argus_kernel::Admission::Plain => Self::Plain,
            argus_kernel::Admission::Inspected(id) => Self::Inspected(id.0),
            argus_kernel::Admission::Bypassed => Self::Bypassed,
        }
    }
}

impl EgressKindN {
    pub const ALL: [Self; 4] = [
        Self::NetworkExternal,
        Self::NetworkInternal,
        Self::FilesystemWrite,
        Self::Ipc,
    ];
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn capability_vocabulary_roundtrips_in_fixed_order() {
        let roundtrip: Vec<_> = CapKind::ALL
            .into_iter()
            .map(|kind| CapKindN::from_kernel(kind).into_kernel())
            .collect();

        assert_eq!(roundtrip, CapKind::ALL);
    }

    #[test]
    fn admission_with_attestation_roundtrips() {
        let admission = argus_kernel::Admission::Inspected(argus_kernel::AttestationId::new("a"));

        assert_eq!(
            AdmissionN::from_kernel(admission.clone()).into_kernel(),
            admission
        );
    }
}
