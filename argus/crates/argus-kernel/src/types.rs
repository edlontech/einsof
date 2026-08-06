use std::fmt;

use crate::capability::CapKind;
use crate::collections::VecSet;

/// String-backed identity. A private helper macro keeps the nine opaque id newtypes identical
/// without repeating the `Display`/constructor boilerplate; extraction sees the expanded structs.
macro_rules! string_id {
    ($(#[$m:meta])* $name:ident) => {
        $(#[$m])*
        #[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub struct $name(pub String);

        impl $name {
            pub fn new(s: &str) -> Self {
                Self(s.to_owned())
            }
        }

        impl fmt::Display for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(&self.0)
            }
        }
    };
}

string_id!(
    /// Agent identity. `root` is the distinguished operator-plane agent.
    AgentId
);
string_id!(
    /// Composite exact tool identity (entry id + version + code hash together, never a bare
    /// name); `tool_registered` is per-version, so a mismatched version/hash is a boundary denial
    /// (E17 — subsumes V3's `tool_attestation_intact`).
    ToolId
);
string_id!(InvocationId);
string_id!(
    /// Attribution id carried inside a `ChallengeScope`; the challenge map is keyed by invocation.
    ChallengeId
);
string_id!(
    /// Identifies one-use inspection / quarantine-resolution / conformance evidence.
    AttestationId
);
string_id!(
    /// Fresh id burned by every transitioning `cross_output`; its own consumed history (E16).
    CrossingId
);
string_id!(
    /// Exact endorsement-assignment digest; a crossing grant is keyed by `(holder, assignment)`.
    AssignmentDigest
);
string_id!(
    /// Binds an inspection attestation's scope to the frozen action policy.
    PolicyDigest
);
string_id!(
    /// Hash of the invocation arguments carried in a challenge scope.
    ContentHash
);

impl AgentId {
    pub fn root() -> Self {
        Self("root".to_owned())
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

/// Canonical admission verdict for `begin_invocation` (E8: computed, then passed as data).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Verdict {
    Allow,
    InspectionRequired,
    Deny,
}

/// Whether a pending record is `Permitted` (contained — claims its gates passed), `Blocked`
/// (never pends), or `MonitorBypassed` (dispatched under monitor without a passing gate).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Disposition {
    Permitted,
    Blocked,
    MonitorBypassed,
}

/// Immutable governed enforcement mode: `Enforce` rejects failed holds, `Monitor` demotes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Mode {
    Enforce,
    Monitor,
}

/// Settlement outcome; `Ambiguous` quarantines instead of closing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Outcome {
    Success,
    Failure,
    Ambiguous,
}

/// Declared behavior of a contract revision when endorsement is unavailable.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Fallback {
    Fail,
    ReleaseUnendorsed,
}

/// How a pending invocation was admitted; *evidence*, never authority.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Admission {
    Plain,
    Inspected(AttestationId),
    Bypassed,
}

/// Remaining/provisioned crossing uses. `grant_bounded` requires `remaining <= provisioned`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CrossingGrant {
    pub remaining: u32,
    pub provisioned: u32,
}

/// Composite `crossing_grants` key `(holder agent, exact assignment digest)`. A named struct (not
/// a tuple) so the extractor gets a concrete derived equality instead of the tuple "Pair" compare
/// Aeneas cannot resolve.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CrossingKey {
    pub agent: AgentId,
    pub assignment: AssignmentDigest,
}

/// The exact action policy frozen at admission. Its gates and settlement use stable required
/// capabilities, floors, output provenance, egress set, and digest. Frozen INPUT, not kernel state.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActionPolicySnapshot {
    /// Exact registered tool identity bound to this snapshot.
    pub tool: ToolId,
    pub required_caps: VecSet<CapKind>,
    /// Maximum confidentiality level the invoker may hold.
    pub conf_clearance: ConfLevel,
    /// ALLOW floor.
    pub integ_floor: IntegLevel,
    /// Inspect-band floor (a floor above it is an empty band, coherent by construction).
    pub integ_inspect: IntegLevel,
    /// Confidentiality provenance of ordinary output.
    pub output_conf: ConfLevel,
    /// Integrity provenance of ordinary output.
    pub output_integ: IntegLevel,
    /// Declared egress set; the invocation egress set must narrow to this set.
    pub declared_egress: VecSet<EgressKind>,
    /// Binds inspection-attestation scope.
    pub policy_digest: PolicyDigest,
}

/// A pending invocation. `contained` exactly when `disposition == Permitted`; monitor-bypassed
/// records still constrain future decisions but do not claim their gates passed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PendingInvocation {
    pub agent: AgentId,
    pub policy: ActionPolicySnapshot,
    /// The attested per-invocation egress set.
    pub egress: VecSet<EgressKind>,
    pub admission: Admission,
    pub disposition: Disposition,
    /// Authorizer verdict recorded at admission.
    pub authorized: bool,
    /// Set by `settle_invocation ambiguous`; keeps participating in every speculative/pairwise set.
    pub quarantined: bool,
}

impl PendingInvocation {
    /// A record is contained exactly when it is `Permitted`.
    pub fn contained(&self) -> bool {
        self.disposition == Disposition::Permitted
    }

    /// A record is vouched exactly when its admission stores an inspection attestation.
    pub fn vouched(&self) -> bool {
        matches!(self.admission, Admission::Inspected(_))
    }
}

/// An inspection challenge scope: binds the invocation key, agent, frozen policy, egress set,
/// arguments hash, and authorizer verdict. The kernel has no clock; resolver freshness is external.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChallengeScope {
    /// Challenge identifier used for attestation attribution; the invocation is the map key.
    pub challenge: ChallengeId,
    pub agent: AgentId,
    pub policy: ActionPolicySnapshot,
    pub egress: VecSet<EgressKind>,
    pub args_hash: ContentHash,
    pub authorized: bool,
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
    fn integ_level_le() {
        assert!(IntegLevel::Untrusted.le(IntegLevel::Standard));
        assert!(IntegLevel::Standard.le(IntegLevel::Trusted));
        assert!(IntegLevel::Trusted.le(IntegLevel::Attested));
        assert!(!IntegLevel::Standard.le(IntegLevel::Untrusted));
        assert!(!IntegLevel::Attested.le(IntegLevel::Trusted));
    }

    #[test]
    fn integ_level_ordering() {
        assert!(IntegLevel::Untrusted < IntegLevel::Standard);
        assert!(IntegLevel::Standard < IntegLevel::Trusted);
        assert!(IntegLevel::Trusted < IntegLevel::Attested);
    }

    #[test]
    fn integ_level_display() {
        assert_eq!(IntegLevel::Untrusted.to_string(), "untrusted");
        assert_eq!(IntegLevel::Attested.to_string(), "attested");
    }

    #[test]
    fn agent_id_root() {
        assert_eq!(AgentId::root(), AgentId("root".into()));
    }

    #[test]
    fn agent_id_display() {
        assert_eq!(AgentId::new("test-agent").to_string(), "test-agent");
    }

    #[test]
    fn tool_id_display() {
        assert_eq!(ToolId::new("read_file").to_string(), "read_file");
    }

    #[test]
    fn egress_kind_display() {
        assert_eq!(EgressKind::NetworkExternal.to_string(), "network_external");
        assert_eq!(EgressKind::Ipc.to_string(), "ipc");
    }

    #[test]
    fn contained_iff_permitted() {
        let snap = ActionPolicySnapshot {
            tool: ToolId::new("t"),
            required_caps: VecSet::new(),
            conf_clearance: ConfLevel::Restricted,
            integ_floor: IntegLevel::Untrusted,
            integ_inspect: IntegLevel::Untrusted,
            output_conf: ConfLevel::Public,
            output_integ: IntegLevel::Attested,
            declared_egress: VecSet::new(),
            policy_digest: PolicyDigest::new("d"),
        };
        let mut p = PendingInvocation {
            agent: AgentId::new("a"),
            policy: snap,
            egress: VecSet::new(),
            admission: Admission::Plain,
            disposition: Disposition::Permitted,
            authorized: true,
            quarantined: false,
        };
        assert!(p.contained());
        assert!(!p.vouched());
        p.disposition = Disposition::MonitorBypassed;
        assert!(!p.contained());
        p.admission = Admission::Inspected(AttestationId::new("att"));
        assert!(p.vouched());
    }
}
