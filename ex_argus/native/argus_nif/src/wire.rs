use std::collections::HashMap;

use argus_kernel::{
    ActionPolicySnapshot, AgentId, AssignmentDigest, AttestationId, BackgroundTheory,
    BackgroundTheoryBuilder, ChallengeId, ConformanceAttestation, ContentHash, CrossInput,
    InspectionAttestation, InvocationId, PolicyDigest, ResolutionAttestation, ToolId,
};
use rustler::NifStruct;

use crate::command::CommandN;
use crate::enums::{
    CapKindN, ConfLevelN, DispositionN, EgressKindN, FallbackN, IntegLevelN, ModeN, OutcomeN,
    VerdictN,
};
use crate::event::ActionN;

#[derive(Debug, Clone, PartialEq, Eq, NifStruct)]
#[module = "ExArgus.Kernel.Background"]
pub struct BackgroundN {
    pub mode: ModeN,
    pub allow_ceiling: HashMap<EgressKindN, Option<ConfLevelN>>,
    pub inspect_ceiling: HashMap<EgressKindN, Option<ConfLevelN>>,
}

impl BackgroundN {
    pub fn into_kernel(self) -> BackgroundTheory {
        let mut builder = BackgroundTheoryBuilder::new();
        builder.set_mode(self.mode.into_kernel());
        for egress in EgressKindN::ALL {
            builder.set_egress_ceilings(
                egress.into_kernel(),
                self.allow_ceiling
                    .get(&egress)
                    .copied()
                    .flatten()
                    .map(ConfLevelN::into_kernel),
                self.inspect_ceiling
                    .get(&egress)
                    .copied()
                    .flatten()
                    .map(ConfLevelN::into_kernel),
            );
        }
        builder.build()
    }
}

#[derive(Debug, Clone, PartialEq, Eq, NifStruct)]
#[module = "ExArgus.Kernel.Types.ActionPolicySnapshot"]
pub struct ActionPolicySnapshotN {
    pub tool: String,
    pub required_caps: Vec<CapKindN>,
    pub conf_clearance: ConfLevelN,
    pub integ_floor: IntegLevelN,
    pub integ_inspect: IntegLevelN,
    pub output_conf: ConfLevelN,
    pub output_integ: IntegLevelN,
    pub declared_egress: Vec<EgressKindN>,
    pub policy_digest: String,
}

impl ActionPolicySnapshotN {
    pub fn into_kernel(self) -> ActionPolicySnapshot {
        ActionPolicySnapshot {
            tool: ToolId(self.tool),
            required_caps: self
                .required_caps
                .into_iter()
                .map(CapKindN::into_kernel)
                .collect(),
            conf_clearance: self.conf_clearance.into_kernel(),
            integ_floor: self.integ_floor.into_kernel(),
            integ_inspect: self.integ_inspect.into_kernel(),
            output_conf: self.output_conf.into_kernel(),
            output_integ: self.output_integ.into_kernel(),
            declared_egress: self
                .declared_egress
                .into_iter()
                .map(EgressKindN::into_kernel)
                .collect(),
            policy_digest: PolicyDigest(self.policy_digest),
        }
    }

    pub fn from_kernel(value: ActionPolicySnapshot) -> Self {
        Self {
            tool: value.tool.0,
            required_caps: value
                .required_caps
                .iter()
                .copied()
                .map(CapKindN::from_kernel)
                .collect(),
            conf_clearance: ConfLevelN::from_kernel(value.conf_clearance),
            integ_floor: IntegLevelN::from_kernel(value.integ_floor),
            integ_inspect: IntegLevelN::from_kernel(value.integ_inspect),
            output_conf: ConfLevelN::from_kernel(value.output_conf),
            output_integ: IntegLevelN::from_kernel(value.output_integ),
            declared_egress: value
                .declared_egress
                .iter()
                .copied()
                .map(EgressKindN::from_kernel)
                .collect(),
            policy_digest: value.policy_digest.0,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, NifStruct)]
#[module = "ExArgus.Kernel.Types.InspectionAttestation"]
pub struct InspectionAttestationN {
    pub id: String,
    pub inv: String,
    pub challenge: String,
    pub args_hash: String,
    pub policy_digest: String,
    pub positive: bool,
}

impl InspectionAttestationN {
    pub fn into_kernel(self) -> InspectionAttestation {
        InspectionAttestation {
            id: AttestationId(self.id),
            inv: InvocationId(self.inv),
            challenge: ChallengeId(self.challenge),
            args_hash: ContentHash(self.args_hash),
            policy_digest: PolicyDigest(self.policy_digest),
            positive: self.positive,
        }
    }

    pub fn from_kernel(value: InspectionAttestation) -> Self {
        Self {
            id: value.id.0,
            inv: value.inv.0,
            challenge: value.challenge.0,
            args_hash: value.args_hash.0,
            policy_digest: value.policy_digest.0,
            positive: value.positive,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, NifStruct)]
#[module = "ExArgus.Kernel.Types.ResolutionAttestation"]
pub struct ResolutionAttestationN {
    pub id: String,
    pub inv: String,
    pub outcome: OutcomeN,
}

impl ResolutionAttestationN {
    pub fn into_kernel(self) -> ResolutionAttestation {
        ResolutionAttestation {
            id: AttestationId(self.id),
            inv: InvocationId(self.inv),
            outcome: self.outcome.into_kernel(),
        }
    }

    pub fn from_kernel(value: ResolutionAttestation) -> Self {
        Self {
            id: value.id.0,
            inv: value.inv.0,
            outcome: OutcomeN::from_kernel(value.outcome),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, NifStruct)]
#[module = "ExArgus.Kernel.Types.ConformanceAttestation"]
pub struct ConformanceAttestationN {
    pub id: String,
    pub output: String,
    pub src: String,
    pub rcv: String,
    pub descriptor: String,
    pub assignment: String,
    pub positive: bool,
}

impl ConformanceAttestationN {
    pub fn into_kernel(self) -> ConformanceAttestation {
        ConformanceAttestation {
            id: AttestationId(self.id),
            output: ContentHash(self.output),
            src: AgentId(self.src),
            rcv: AgentId(self.rcv),
            descriptor: ContentHash(self.descriptor),
            assignment: AssignmentDigest(self.assignment),
            positive: self.positive,
        }
    }

    pub fn from_kernel(value: ConformanceAttestation) -> Self {
        Self {
            id: value.id.0,
            output: value.output.0,
            src: value.src.0,
            rcv: value.rcv.0,
            descriptor: value.descriptor.0,
            assignment: value.assignment.0,
            positive: value.positive,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, NifStruct)]
#[module = "ExArgus.Kernel.Types.CrossInput"]
pub struct CrossInputN {
    pub src: String,
    pub rcv: String,
    pub crossing: String,
    pub output_hash: String,
    pub descriptor: String,
    pub fallback: FallbackN,
    pub t_integ: IntegLevelN,
    pub t_conf: Option<ConfLevelN>,
    pub assignment: String,
    pub evidence: Option<ConformanceAttestationN>,
    pub released_conf: ConfLevelN,
    pub released_integ: IntegLevelN,
}

impl CrossInputN {
    pub fn into_kernel(self) -> CrossInput {
        CrossInput {
            src: AgentId(self.src),
            rcv: AgentId(self.rcv),
            crossing: argus_kernel::CrossingId(self.crossing),
            output_hash: ContentHash(self.output_hash),
            descriptor: ContentHash(self.descriptor),
            fallback: self.fallback.into_kernel(),
            t_integ: self.t_integ.into_kernel(),
            t_conf: self.t_conf.map(ConfLevelN::into_kernel),
            assignment: AssignmentDigest(self.assignment),
            evidence: self.evidence.map(ConformanceAttestationN::into_kernel),
            released_conf: self.released_conf.into_kernel(),
            released_integ: self.released_integ.into_kernel(),
        }
    }

    pub fn from_kernel(value: CrossInput) -> Self {
        Self {
            src: value.src.0,
            rcv: value.rcv.0,
            crossing: value.crossing.0,
            output_hash: value.output_hash.0,
            descriptor: value.descriptor.0,
            fallback: FallbackN::from_kernel(value.fallback),
            t_integ: IntegLevelN::from_kernel(value.t_integ),
            t_conf: value.t_conf.map(ConfLevelN::from_kernel),
            assignment: value.assignment.0,
            evidence: value.evidence.map(ConformanceAttestationN::from_kernel),
            released_conf: ConfLevelN::from_kernel(value.released_conf),
            released_integ: IntegLevelN::from_kernel(value.released_integ),
        }
    }
}

macro_rules! command_struct {
    ($name:ident, $module:literal, {$($field:ident: $ty:ty),* $(,)?}) => {
        #[derive(Debug, Clone, PartialEq, Eq, NifStruct)]
        #[module = $module]
        pub struct $name {
            $(pub $field: $ty),*
        }
    };
}

command_struct!(RegisterToolCommandN, "ExArgus.Command.RegisterTool", { tool: String });
command_struct!(UnregisterToolCommandN, "ExArgus.Command.UnregisterTool", { tool: String });
command_struct!(DelegateCommandN, "ExArgus.Command.Delegate", {
    grantor: String,
    grantee: String,
});
command_struct!(GrantCapabilityCommandN, "ExArgus.Command.GrantCapability", {
    parent: String,
    child: String,
    cap: CapKindN,
});
command_struct!(GrantCrossingCommandN, "ExArgus.Command.GrantCrossing", {
    grantor: String,
    agent: String,
    assignment: String,
    n: u32,
});
command_struct!(RevokeCommandN, "ExArgus.Command.Revoke", {
    parent: String,
    target: String,
});
command_struct!(CascadeRevokeCommandN, "ExArgus.Command.CascadeRevoke", {
    child: String,
    parent: String,
});
command_struct!(IngestCommandN, "ExArgus.Command.Ingest", {
    agent: String,
    src: Option<String>,
    pconf: ConfLevelN,
    pinteg: IntegLevelN,
});
command_struct!(BeginInvocationCommandN, "ExArgus.Command.BeginInvocation", {
    agent: String,
    inv: String,
    challenge: String,
    policy: ActionPolicySnapshotN,
    egress: Vec<EgressKindN>,
    args_hash: String,
    authorized: bool,
});
command_struct!(AuthorizeInspectedCommandN, "ExArgus.Command.AuthorizeInspected", {
    inv: String,
    attestation: InspectionAttestationN,
});
command_struct!(SettleInvocationCommandN, "ExArgus.Command.SettleInvocation", {
    inv: String,
    outcome: OutcomeN,
    resolution: Option<ResolutionAttestationN>,
});
command_struct!(CrossOutputCommandN, "ExArgus.Command.CrossOutput", { input: CrossInputN });

macro_rules! action_struct {
    ($name:ident, $module:literal, {$($field:ident: $ty:ty),* $(,)?}) => {
        #[derive(Debug, Clone, PartialEq, Eq, NifStruct)]
        #[module = $module]
        pub struct $name {
            $(pub $field: $ty),*
        }
    };
}

action_struct!(RegisterToolActionN, "ExArgus.Kernel.Action.RegisterTool", { tool: String });
action_struct!(UnregisterToolActionN, "ExArgus.Kernel.Action.UnregisterTool", { tool: String });
action_struct!(DelegateActionN, "ExArgus.Kernel.Action.Delegate", {
    grantor: String,
    grantee: String,
});
action_struct!(GrantCapabilityActionN, "ExArgus.Kernel.Action.GrantCapability", {
    parent: String,
    child: String,
    cap: CapKindN,
});
action_struct!(GrantCrossingActionN, "ExArgus.Kernel.Action.GrantCrossing", {
    grantor: String,
    agent: String,
    assignment: String,
    n: u32,
});
action_struct!(RevokeActionN, "ExArgus.Kernel.Action.Revoke", {
    parent: String,
    target: String,
});
action_struct!(CascadeRevokeActionN, "ExArgus.Kernel.Action.CascadeRevoke", {
    child: String,
    parent: String,
});
action_struct!(IngestActionN, "ExArgus.Kernel.Action.Ingest", {
    agent: String,
    src: Option<String>,
    pconf: ConfLevelN,
    pinteg: IntegLevelN,
    disposition: DispositionN,
});
action_struct!(BeginInvocationActionN, "ExArgus.Kernel.Action.BeginInvocation", {
    agent: String,
    inv: String,
    tool: String,
    verdict: VerdictN,
    authorized: bool,
});
action_struct!(AuthorizeInspectedActionN, "ExArgus.Kernel.Action.AuthorizeInspected", {
    inv: String,
    attestation: String,
    admitted: bool,
});
action_struct!(SettleInvocationActionN, "ExArgus.Kernel.Action.SettleInvocation", {
    inv: String,
    agent: String,
    disposition: DispositionN,
    outcome: OutcomeN,
    clvl: ConfLevelN,
    ilvl: IntegLevelN,
    resolution: Option<String>,
});
action_struct!(CrossOutputActionN, "ExArgus.Kernel.Action.CrossOutput", {
    src: String,
    rcv: String,
    crossing: String,
    branch: crate::enums::CrossBranchN,
    disposition: DispositionN,
});

#[derive(Debug, Clone, PartialEq, Eq, NifStruct)]
#[module = "ExArgus.Envelope"]
pub struct EnvelopeN {
    pub version: u32,
    pub sequence: u64,
    pub previous_digest: Vec<u8>,
    pub digest: Vec<u8>,
    pub command: CommandN,
    pub action: ActionN,
}

#[derive(Debug, Clone, PartialEq, Eq, NifStruct)]
#[module = "ExArgus.Chain"]
pub struct ChainN {
    pub version: u32,
    pub sequence: u64,
    pub head: Vec<u8>,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn policy() -> ActionPolicySnapshotN {
        ActionPolicySnapshotN {
            tool: "tool".to_owned(),
            required_caps: vec![CapKindN::FilesystemRead, CapKindN::Ipc],
            conf_clearance: ConfLevelN::Sensitive,
            integ_floor: IntegLevelN::Standard,
            integ_inspect: IntegLevelN::Untrusted,
            output_conf: ConfLevelN::Internal,
            output_integ: IntegLevelN::Trusted,
            declared_egress: vec![EgressKindN::NetworkInternal, EgressKindN::Ipc],
            policy_digest: "policy".to_owned(),
        }
    }

    fn cross_input(evidence: Option<ConformanceAttestationN>) -> CrossInputN {
        CrossInputN {
            src: "source".to_owned(),
            rcv: "receiver".to_owned(),
            crossing: "crossing".to_owned(),
            output_hash: "output".to_owned(),
            descriptor: "descriptor".to_owned(),
            fallback: FallbackN::ReleaseUnendorsed,
            t_integ: IntegLevelN::Trusted,
            t_conf: evidence.as_ref().map(|_| ConfLevelN::Internal),
            assignment: "assignment".to_owned(),
            evidence,
            released_conf: ConfLevelN::Internal,
            released_integ: IntegLevelN::Standard,
        }
    }

    #[test]
    fn background_preserves_present_and_absent_ceilings() {
        let background = BackgroundN {
            mode: ModeN::Monitor,
            allow_ceiling: HashMap::from([
                (EgressKindN::NetworkExternal, Some(ConfLevelN::Internal)),
                (EgressKindN::NetworkInternal, None),
                (EgressKindN::FilesystemWrite, None),
                (EgressKindN::Ipc, None),
            ]),
            inspect_ceiling: HashMap::from([
                (EgressKindN::NetworkExternal, Some(ConfLevelN::Sensitive)),
                (EgressKindN::NetworkInternal, None),
                (EgressKindN::FilesystemWrite, None),
                (EgressKindN::Ipc, None),
            ]),
        }
        .into_kernel();

        assert_eq!(
            (
                background.mode(),
                background.root_agent(),
                background.flow_allows(
                    argus_kernel::ConfLevel::Internal,
                    argus_kernel::EgressKind::NetworkExternal,
                ),
                background.flow_allows(
                    argus_kernel::ConfLevel::Public,
                    argus_kernel::EgressKind::NetworkInternal,
                ),
            ),
            (
                argus_kernel::Mode::Monitor,
                &argus_kernel::AgentId::root(),
                true,
                false,
            )
        );
    }

    #[test]
    fn policy_roundtrips_without_losing_set_members() {
        let value = policy();

        assert_eq!(
            ActionPolicySnapshotN::from_kernel(value.clone().into_kernel()),
            value
        );
    }

    #[test]
    fn inspection_evidence_roundtrips() {
        let value = InspectionAttestationN {
            id: "attestation".to_owned(),
            inv: "invocation".to_owned(),
            challenge: "challenge".to_owned(),
            args_hash: "arguments".to_owned(),
            policy_digest: "policy".to_owned(),
            positive: true,
        };

        assert_eq!(
            InspectionAttestationN::from_kernel(value.clone().into_kernel()),
            value
        );
    }

    #[test]
    fn resolution_evidence_roundtrips() {
        let value = ResolutionAttestationN {
            id: "attestation".to_owned(),
            inv: "invocation".to_owned(),
            outcome: OutcomeN::Failure,
        };

        assert_eq!(
            ResolutionAttestationN::from_kernel(value.clone().into_kernel()),
            value
        );
    }

    #[test]
    fn cross_input_roundtrips_present_optional_fields() {
        let value = cross_input(Some(ConformanceAttestationN {
            id: "attestation".to_owned(),
            output: "output".to_owned(),
            src: "source".to_owned(),
            rcv: "receiver".to_owned(),
            descriptor: "descriptor".to_owned(),
            assignment: "assignment".to_owned(),
            positive: true,
        }));

        assert_eq!(CrossInputN::from_kernel(value.clone().into_kernel()), value);
    }

    #[test]
    fn cross_input_roundtrips_absent_optional_fields() {
        let value = cross_input(None);

        assert_eq!(CrossInputN::from_kernel(value.clone().into_kernel()), value);
    }
}
