use sha2::{Digest as _, Sha256};

use crate::command::CommandN;
use crate::enums::{
    CapKindN, ConfLevelN, CrossBranchN, DispositionN, EgressKindN, FallbackN, IntegLevelN, ModeN,
    OutcomeN, VerdictN,
};
use crate::event::ActionN;
use crate::wire::{
    ActionPolicySnapshotN, AuthorizeInspectedActionN, AuthorizeInspectedCommandN, BackgroundN,
    BeginInvocationActionN, BeginInvocationCommandN, CascadeRevokeActionN, CascadeRevokeCommandN,
    ConformanceAttestationN, CrossInputN, CrossOutputActionN, CrossOutputCommandN, DelegateActionN,
    DelegateCommandN, DigestN, GrantCapabilityActionN, GrantCapabilityCommandN,
    GrantCrossingActionN, GrantCrossingCommandN, IngestActionN, IngestCommandN,
    InspectionAttestationN, RegisterToolActionN, RegisterToolCommandN, ResolutionAttestationN,
    RevokeActionN, RevokeCommandN, SettleInvocationActionN, SettleInvocationCommandN,
    UnregisterToolActionN, UnregisterToolCommandN,
};

const GENESIS_DOMAIN: &[u8] = b"EXARGUS\0GENESIS\0";
const ENVELOPE_DOMAIN: &[u8] = b"EXARGUS\0ENVELOPE\0";
pub const VERSION: u32 = 5;

trait Sink {
    fn write(&mut self, bytes: &[u8]);
}

impl Sink for Vec<u8> {
    fn write(&mut self, bytes: &[u8]) {
        self.extend_from_slice(bytes);
    }
}

impl Sink for Sha256 {
    fn write(&mut self, bytes: &[u8]) {
        self.update(bytes);
    }
}

struct Transcript<S> {
    sink: S,
}

impl<S: Sink> Transcript<S> {
    fn new(sink: S) -> Self {
        Self { sink }
    }

    fn bytes(&mut self, value: &[u8]) {
        self.sink.write(value);
    }

    fn u8(&mut self, value: u8) {
        self.bytes(&[value]);
    }

    fn u32(&mut self, value: u32) {
        self.bytes(&value.to_be_bytes());
    }

    fn u64(&mut self, value: u64) {
        self.bytes(&value.to_be_bytes());
    }

    fn string(&mut self, value: &str) {
        self.u32(value.len() as u32);
        self.bytes(value.as_bytes());
    }

    fn list<T: Canonical>(&mut self, values: &[T]) {
        self.u32(values.len() as u32);
        for value in values {
            value.write_canonical(self);
        }
    }

    fn canonical_set<T: CanonicalTag + Copy>(&mut self, values: &[T]) {
        let mut normalized = values.to_vec();
        normalized.sort_unstable_by_key(CanonicalTag::canonical_tag);
        normalized.dedup_by_key(|value| value.canonical_tag());
        self.list(&normalized);
    }

    fn finish(self) -> S {
        self.sink
    }
}

trait Canonical {
    fn write_canonical<S: Sink>(&self, out: &mut Transcript<S>);
}

pub(crate) trait CanonicalTag {
    fn canonical_tag(&self) -> u8;
}

impl<T: CanonicalTag> Canonical for T {
    fn write_canonical<S: Sink>(&self, out: &mut Transcript<S>) {
        out.u8(self.canonical_tag());
    }
}

macro_rules! canonical_enum {
    ($ty:ty, {$($variant:path => $tag:literal),+ $(,)?}) => {
        impl CanonicalTag for $ty {
            fn canonical_tag(&self) -> u8 {
                match self {
                    $($variant => $tag),+
                }
            }
        }
    };
}

canonical_enum!(ConfLevelN, {
    ConfLevelN::Public => 0,
    ConfLevelN::Internal => 1,
    ConfLevelN::Sensitive => 2,
    ConfLevelN::Restricted => 3,
});
canonical_enum!(IntegLevelN, {
    IntegLevelN::Untrusted => 0,
    IntegLevelN::Standard => 1,
    IntegLevelN::Trusted => 2,
    IntegLevelN::Attested => 3,
});
canonical_enum!(EgressKindN, {
    EgressKindN::NetworkExternal => 0,
    EgressKindN::NetworkInternal => 1,
    EgressKindN::FilesystemWrite => 2,
    EgressKindN::Ipc => 3,
});
canonical_enum!(CapKindN, {
    CapKindN::FilesystemRead => 0,
    CapKindN::FilesystemWrite => 1,
    CapKindN::FilesystemDelete => 2,
    CapKindN::NetworkEgress => 3,
    CapKindN::NetworkIngress => 4,
    CapKindN::ExecutionShell => 5,
    CapKindN::ExecutionCode => 6,
    CapKindN::Credentials => 7,
    CapKindN::SystemInfo => 8,
    CapKindN::SystemModify => 9,
    CapKindN::Clipboard => 10,
    CapKindN::BrowserNavigate => 11,
    CapKindN::DatabaseRead => 12,
    CapKindN::DatabaseWrite => 13,
    CapKindN::Ipc => 14,
});
canonical_enum!(VerdictN, {
    VerdictN::Allow => 0,
    VerdictN::InspectionRequired => 1,
    VerdictN::Deny => 2,
});
canonical_enum!(DispositionN, {
    DispositionN::Permitted => 0,
    DispositionN::Blocked => 1,
    DispositionN::MonitorBypassed => 2,
});
canonical_enum!(ModeN, { ModeN::Enforce => 0, ModeN::Monitor => 1 });
canonical_enum!(OutcomeN, {
    OutcomeN::Success => 0,
    OutcomeN::Failure => 1,
    OutcomeN::Ambiguous => 2,
});
canonical_enum!(FallbackN, { FallbackN::Fail => 0, FallbackN::ReleaseUnendorsed => 1 });
canonical_enum!(CrossBranchN, {
    CrossBranchN::Endorsed => 0,
    CrossBranchN::Unendorsed => 1,
    CrossBranchN::Fail => 2,
});

impl Canonical for String {
    fn write_canonical<S: Sink>(&self, out: &mut Transcript<S>) {
        out.string(self);
    }
}

impl Canonical for bool {
    fn write_canonical<S: Sink>(&self, out: &mut Transcript<S>) {
        out.u8(u8::from(*self));
    }
}

impl Canonical for u32 {
    fn write_canonical<S: Sink>(&self, out: &mut Transcript<S>) {
        out.u32(*self);
    }
}

impl<T: Canonical> Canonical for Option<T> {
    fn write_canonical<S: Sink>(&self, out: &mut Transcript<S>) {
        match self {
            Some(value) => {
                out.u8(1);
                value.write_canonical(out);
            }
            None => out.u8(0),
        }
    }
}

macro_rules! canonical_struct {
    ($ty:ty, [$($field:ident),+ $(,)?]) => {
        impl Canonical for $ty {
            fn write_canonical<S: Sink>(&self, out: &mut Transcript<S>) {
                $(self.$field.write_canonical(out);)+
            }
        }
    };
}

canonical_struct!(
    InspectionAttestationN,
    [id, inv, challenge, args_hash, policy_digest, positive]
);
canonical_struct!(ResolutionAttestationN, [id, inv, outcome]);
canonical_struct!(
    ConformanceAttestationN,
    [id, output, src, rcv, descriptor, assignment, positive]
);
canonical_struct!(
    CrossInputN,
    [
        src,
        rcv,
        crossing,
        output_hash,
        descriptor,
        fallback,
        t_integ,
        t_conf,
        assignment,
        evidence,
        released_conf,
        released_integ,
    ]
);

impl Canonical for ActionPolicySnapshotN {
    fn write_canonical<S: Sink>(&self, out: &mut Transcript<S>) {
        self.tool.write_canonical(out);
        out.canonical_set(&self.required_caps);
        self.conf_clearance.write_canonical(out);
        self.integ_floor.write_canonical(out);
        self.integ_inspect.write_canonical(out);
        self.output_conf.write_canonical(out);
        self.output_integ.write_canonical(out);
        out.canonical_set(&self.declared_egress);
        self.policy_digest.write_canonical(out);
    }
}

canonical_struct!(RegisterToolCommandN, [tool]);
canonical_struct!(UnregisterToolCommandN, [tool]);
canonical_struct!(DelegateCommandN, [grantor, grantee]);
canonical_struct!(GrantCapabilityCommandN, [parent, child, cap]);
canonical_struct!(GrantCrossingCommandN, [grantor, agent, assignment, n]);
canonical_struct!(RevokeCommandN, [parent, target]);
canonical_struct!(CascadeRevokeCommandN, [child, parent]);
canonical_struct!(IngestCommandN, [agent, src, pconf, pinteg]);
canonical_struct!(AuthorizeInspectedCommandN, [inv, attestation]);
canonical_struct!(SettleInvocationCommandN, [inv, outcome, resolution]);
canonical_struct!(CrossOutputCommandN, [input]);

impl Canonical for BeginInvocationCommandN {
    fn write_canonical<S: Sink>(&self, out: &mut Transcript<S>) {
        self.agent.write_canonical(out);
        self.inv.write_canonical(out);
        self.challenge.write_canonical(out);
        self.policy.write_canonical(out);
        out.canonical_set(&self.egress);
        self.args_hash.write_canonical(out);
        self.authorized.write_canonical(out);
    }
}

impl Canonical for CommandN {
    fn write_canonical<S: Sink>(&self, out: &mut Transcript<S>) {
        out.u8(self.canonical_tag());
        match self {
            Self::RegisterTool(value) => value.write_canonical(out),
            Self::UnregisterTool(value) => value.write_canonical(out),
            Self::Delegate(value) => value.write_canonical(out),
            Self::GrantCapability(value) => value.write_canonical(out),
            Self::GrantCrossing(value) => value.write_canonical(out),
            Self::Revoke(value) => value.write_canonical(out),
            Self::CascadeRevoke(value) => value.write_canonical(out),
            Self::Ingest(value) => value.write_canonical(out),
            Self::BeginInvocation(value) => value.write_canonical(out),
            Self::AuthorizeInspected(value) => value.write_canonical(out),
            Self::SettleInvocation(value) => value.write_canonical(out),
            Self::CrossOutput(value) => value.write_canonical(out),
        }
    }
}

canonical_struct!(RegisterToolActionN, [tool]);
canonical_struct!(UnregisterToolActionN, [tool]);
canonical_struct!(DelegateActionN, [grantor, grantee]);
canonical_struct!(GrantCapabilityActionN, [parent, child, cap]);
canonical_struct!(GrantCrossingActionN, [grantor, agent, assignment, n]);
canonical_struct!(RevokeActionN, [parent, target]);
canonical_struct!(CascadeRevokeActionN, [child, parent]);
canonical_struct!(IngestActionN, [agent, src, pconf, pinteg, disposition]);
canonical_struct!(
    BeginInvocationActionN,
    [agent, inv, tool, verdict, authorized]
);
canonical_struct!(AuthorizeInspectedActionN, [inv, attestation, admitted]);
canonical_struct!(
    SettleInvocationActionN,
    [inv, agent, disposition, outcome, clvl, ilvl, resolution,]
);
canonical_struct!(
    CrossOutputActionN,
    [src, rcv, crossing, branch, disposition]
);

impl Canonical for ActionN {
    fn write_canonical<S: Sink>(&self, out: &mut Transcript<S>) {
        out.u8(self.canonical_tag());
        match self {
            Self::RegisterTool(value) => value.write_canonical(out),
            Self::UnregisterTool(value) => value.write_canonical(out),
            Self::Delegate(value) => value.write_canonical(out),
            Self::GrantCapability(value) => value.write_canonical(out),
            Self::GrantCrossing(value) => value.write_canonical(out),
            Self::Revoke(value) => value.write_canonical(out),
            Self::CascadeRevoke(value) => value.write_canonical(out),
            Self::Ingest(value) => value.write_canonical(out),
            Self::BeginInvocation(value) => value.write_canonical(out),
            Self::AuthorizeInspected(value) => value.write_canonical(out),
            Self::SettleInvocation(value) => value.write_canonical(out),
            Self::CrossOutput(value) => value.write_canonical(out),
        }
    }
}

impl Canonical for BackgroundN {
    fn write_canonical<S: Sink>(&self, out: &mut Transcript<S>) {
        self.mode.write_canonical(out);
        for egress in EgressKindN::ALL {
            self.allow_ceiling
                .get(&egress)
                .copied()
                .flatten()
                .write_canonical(out);
        }
        for egress in EgressKindN::ALL {
            self.inspect_ceiling
                .get(&egress)
                .copied()
                .flatten()
                .write_canonical(out);
        }
    }
}

fn write_genesis<S: Sink>(out: &mut Transcript<S>, background: &BackgroundN) {
    out.bytes(GENESIS_DOMAIN);
    out.u32(VERSION);
    out.string("root");
    background.write_canonical(out);
}

fn write_link<S: Sink>(
    out: &mut Transcript<S>,
    previous: DigestN,
    sequence: u64,
    command: &CommandN,
    action: &ActionN,
) {
    out.bytes(ENVELOPE_DOMAIN);
    out.u32(VERSION);
    out.bytes(previous.as_bytes());
    out.u64(sequence);
    command.write_canonical(out);
    action.write_canonical(out);
}

pub fn genesis_transcript(background: &BackgroundN) -> Vec<u8> {
    let mut out = Transcript::new(Vec::new());
    write_genesis(&mut out, background);
    out.finish()
}

pub fn genesis(background: &BackgroundN) -> DigestN {
    let mut out = Transcript::new(Sha256::new());
    write_genesis(&mut out, background);
    DigestN::new(out.finish().finalize().into())
}

pub fn link_transcript(
    previous: DigestN,
    sequence: u64,
    command: &CommandN,
    action: &ActionN,
) -> Vec<u8> {
    let mut out = Transcript::new(Vec::new());
    write_link(&mut out, previous, sequence, command, action);
    out.finish()
}

pub fn link(previous: DigestN, sequence: u64, command: &CommandN, action: &ActionN) -> DigestN {
    let mut out = Transcript::new(Sha256::new());
    write_link(&mut out, previous, sequence, command, action);
    DigestN::new(out.finish().finalize().into())
}

#[cfg(test)]
mod tests {
    use std::collections::HashMap;

    use super::*;

    fn background() -> BackgroundN {
        BackgroundN {
            mode: ModeN::Monitor,
            allow_ceiling: HashMap::from([
                (EgressKindN::NetworkExternal, Some(ConfLevelN::Internal)),
                (EgressKindN::NetworkInternal, None),
                (EgressKindN::FilesystemWrite, Some(ConfLevelN::Restricted)),
                (EgressKindN::Ipc, Some(ConfLevelN::Public)),
            ]),
            inspect_ceiling: HashMap::from([
                (EgressKindN::NetworkExternal, Some(ConfLevelN::Sensitive)),
                (EgressKindN::NetworkInternal, Some(ConfLevelN::Public)),
                (EgressKindN::FilesystemWrite, None),
                (EgressKindN::Ipc, Some(ConfLevelN::Internal)),
            ]),
        }
    }

    #[test]
    fn genesis_pins_canonical_bytes_and_sha256() {
        let transcript = genesis_transcript(&background());

        assert_eq!(
            hex(&transcript),
            "455841524755530047454e45534953000000000500000004726f6f74010101000103010001020100000101"
        );
        assert_eq!(
            hex(genesis(&background()).as_bytes()),
            "909cf2b46d6f57257e56704813925e65f7a17584c4b682dedd360dc693321566"
        );
    }

    #[test]
    fn settlement_link_pins_authoritative_tag_bytes_and_sha256() {
        let previous = DigestN::new(core::array::from_fn(|index| index as u8));
        let command = CommandN::SettleInvocation(SettleInvocationCommandN {
            inv: "inv".to_owned(),
            outcome: OutcomeN::Ambiguous,
            resolution: Some(ResolutionAttestationN {
                id: "res".to_owned(),
                inv: "inv".to_owned(),
                outcome: OutcomeN::Failure,
            }),
        });
        let action = ActionN::SettleInvocation(SettleInvocationActionN {
            inv: "inv".to_owned(),
            agent: "agent".to_owned(),
            disposition: DispositionN::MonitorBypassed,
            outcome: OutcomeN::Ambiguous,
            clvl: ConfLevelN::Sensitive,
            ilvl: IntegLevelN::Trusted,
            resolution: Some("res".to_owned()),
        });

        assert_eq!(
            hex(&link_transcript(previous, 42, &command, &action)),
            "4558415247555300454e56454c4f50450000000005000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f000000000000002a0a00000003696e7602010000000372657300000003696e76010a00000003696e76000000056167656e74020202020100000003726573"
        );
        assert_eq!(
            hex(link(previous, 42, &command, &action).as_bytes()),
            "d3020216c7a8f595170d33a289efdce61ea505896c8892f1a0d489818146b751"
        );
    }

    #[test]
    fn genesis_hash_changes_when_each_background_field_changes() {
        let baseline = genesis(&background());
        let mut variants = Vec::new();

        let mut changed = background();
        changed.mode = ModeN::Enforce;
        variants.push(changed);
        for (inspect, egress) in [false, true]
            .into_iter()
            .flat_map(|inspect| EgressKindN::ALL.map(|egress| (inspect, egress)))
        {
            let mut changed = background();
            let ceilings = if inspect {
                &mut changed.inspect_ceiling
            } else {
                &mut changed.allow_ceiling
            };
            let replacement = if ceilings.get(&egress).copied().flatten().is_some() {
                None
            } else {
                Some(ConfLevelN::Public)
            };
            ceilings.insert(egress, replacement);
            variants.push(changed);
        }

        assert!(variants.iter().all(|changed| genesis(changed) != baseline));
    }

    #[test]
    fn settlement_hash_changes_when_each_link_field_changes() {
        let previous = DigestN::new([7; 32]);
        let command = SettleInvocationCommandN {
            inv: "inv".to_owned(),
            outcome: OutcomeN::Ambiguous,
            resolution: Some(ResolutionAttestationN {
                id: "res".to_owned(),
                inv: "inv".to_owned(),
                outcome: OutcomeN::Failure,
            }),
        };
        let action = SettleInvocationActionN {
            inv: "inv".to_owned(),
            agent: "agent".to_owned(),
            disposition: DispositionN::MonitorBypassed,
            outcome: OutcomeN::Ambiguous,
            clvl: ConfLevelN::Sensitive,
            ilvl: IntegLevelN::Trusted,
            resolution: Some("res".to_owned()),
        };
        let digest = |previous,
                      sequence,
                      command: SettleInvocationCommandN,
                      action: SettleInvocationActionN| {
            link(
                previous,
                sequence,
                &CommandN::SettleInvocation(command),
                &ActionN::SettleInvocation(action),
            )
        };
        let baseline = digest(previous, 42, command.clone(), action.clone());
        let mut variants = Vec::new();
        variants.push(digest(
            DigestN::new([8; 32]),
            42,
            command.clone(),
            action.clone(),
        ));
        variants.push(digest(previous, 43, command.clone(), action.clone()));

        let mut changed = command.clone();
        changed.inv.push('2');
        variants.push(digest(previous, 42, changed, action.clone()));
        let mut changed = command.clone();
        changed.outcome = OutcomeN::Success;
        variants.push(digest(previous, 42, changed, action.clone()));
        let mut changed = command.clone();
        changed.resolution = None;
        variants.push(digest(previous, 42, changed, action.clone()));
        let mut changed = command.clone();
        changed.resolution.as_mut().unwrap().id.push('2');
        variants.push(digest(previous, 42, changed, action.clone()));
        let mut changed = command.clone();
        changed.resolution.as_mut().unwrap().inv.push('2');
        variants.push(digest(previous, 42, changed, action.clone()));
        let mut changed = command.clone();
        changed.resolution.as_mut().unwrap().outcome = OutcomeN::Success;
        variants.push(digest(previous, 42, changed, action.clone()));

        let mut changed = action.clone();
        changed.inv.push('2');
        variants.push(digest(previous, 42, command.clone(), changed));
        let mut changed = action.clone();
        changed.agent.push('2');
        variants.push(digest(previous, 42, command.clone(), changed));
        let mut changed = action.clone();
        changed.disposition = DispositionN::Permitted;
        variants.push(digest(previous, 42, command.clone(), changed));
        let mut changed = action.clone();
        changed.outcome = OutcomeN::Failure;
        variants.push(digest(previous, 42, command.clone(), changed));
        let mut changed = action.clone();
        changed.clvl = ConfLevelN::Restricted;
        variants.push(digest(previous, 42, command.clone(), changed));
        let mut changed = action.clone();
        changed.ilvl = IntegLevelN::Attested;
        variants.push(digest(previous, 42, command.clone(), changed));
        let mut changed = action.clone();
        changed.resolution = None;
        variants.push(digest(previous, 42, command.clone(), changed));
        let mut changed = action;
        changed.resolution.as_mut().unwrap().push('2');
        variants.push(digest(previous, 42, command, changed));

        assert!(variants.into_iter().all(|changed| changed != baseline));
    }

    #[test]
    fn set_lists_hash_in_fixed_semantic_order() {
        let mut first = sample_begin();
        first.policy.required_caps = vec![CapKindN::Ipc, CapKindN::FilesystemRead];
        first.policy.declared_egress = vec![EgressKindN::Ipc, EgressKindN::NetworkExternal];
        first.egress = vec![EgressKindN::Ipc, EgressKindN::NetworkExternal];
        let mut second = first.clone();
        second.policy.required_caps.reverse();
        second.policy.declared_egress.reverse();
        second.egress.reverse();
        let action = ActionN::BeginInvocation(BeginInvocationActionN {
            agent: "agent".to_owned(),
            inv: "inv".to_owned(),
            tool: "tool".to_owned(),
            verdict: VerdictN::Allow,
            authorized: true,
        });

        assert_eq!(
            link(
                DigestN::new([0; 32]),
                1,
                &CommandN::BeginInvocation(first),
                &action
            ),
            link(
                DigestN::new([0; 32]),
                1,
                &CommandN::BeginInvocation(second),
                &action
            )
        );
    }

    fn sample_begin() -> BeginInvocationCommandN {
        BeginInvocationCommandN {
            agent: "agent".to_owned(),
            inv: "inv".to_owned(),
            challenge: "challenge".to_owned(),
            policy: ActionPolicySnapshotN {
                tool: "tool".to_owned(),
                required_caps: vec![],
                conf_clearance: ConfLevelN::Restricted,
                integ_floor: IntegLevelN::Standard,
                integ_inspect: IntegLevelN::Untrusted,
                output_conf: ConfLevelN::Internal,
                output_integ: IntegLevelN::Trusted,
                declared_egress: vec![],
                policy_digest: "policy".to_owned(),
            },
            egress: vec![],
            args_hash: "args".to_owned(),
            authorized: true,
        }
    }

    fn hex(bytes: &[u8]) -> String {
        bytes.iter().map(|byte| format!("{byte:02x}")).collect()
    }
}
