use std::collections::HashSet;

use serde::{Deserialize, Serialize};

pub const ACTIONS: [ActionTag; 12] = [
    ActionTag::RegisterTool,
    ActionTag::UnregisterTool,
    ActionTag::Delegate,
    ActionTag::GrantCapability,
    ActionTag::GrantCrossing,
    ActionTag::Revoke,
    ActionTag::CascadeRevoke,
    ActionTag::Ingest,
    ActionTag::BeginInvocation,
    ActionTag::AuthorizeInspected,
    ActionTag::SettleInvocation,
    ActionTag::CrossOutput,
];
pub const CAPABILITIES: [Capability; 15] = [
    Capability::FilesystemRead,
    Capability::FilesystemWrite,
    Capability::FilesystemDelete,
    Capability::NetworkEgress,
    Capability::NetworkIngress,
    Capability::ExecutionShell,
    Capability::ExecutionCode,
    Capability::Credentials,
    Capability::SystemInfo,
    Capability::SystemModify,
    Capability::Clipboard,
    Capability::BrowserNavigate,
    Capability::DatabaseRead,
    Capability::DatabaseWrite,
    Capability::Ipc,
];
pub const EGRESS: [Egress; 4] = [
    Egress::NetworkExternal,
    Egress::NetworkInternal,
    Egress::FilesystemWrite,
    Egress::Ipc,
];
pub const CONFIDENTIALITY: [Conf; 4] = [
    Conf::Public,
    Conf::Internal,
    Conf::Sensitive,
    Conf::Restricted,
];
pub const INTEGRITY: [Integ; 4] = [
    Integ::Untrusted,
    Integ::Standard,
    Integ::Trusted,
    Integ::Attested,
];
pub const MODES: [Mode; 2] = [Mode::Enforce, Mode::Monitor];
pub const VERDICTS: [Verdict; 3] = [Verdict::Allow, Verdict::InspectionRequired, Verdict::Deny];
pub const DISPOSITIONS: [Disposition; 3] = [
    Disposition::Permitted,
    Disposition::Blocked,
    Disposition::MonitorBypassed,
];
pub const OUTCOMES: [Outcome; 3] = [Outcome::Success, Outcome::Failure, Outcome::Ambiguous];
pub const FALLBACKS: [Fallback; 2] = [Fallback::Fail, Fallback::ReleaseUnendorsed];
pub const CROSS_BRANCHES: [CrossBranch; 3] = [
    CrossBranch::Endorsed,
    CrossBranch::Unendorsed,
    CrossBranch::Fail,
];
pub const ADMISSIONS: [AdmissionTag; 3] = [
    AdmissionTag::Plain,
    AdmissionTag::Inspected,
    AdmissionTag::Bypassed,
];
pub const TELEMETRY_OUTCOMES: [TelemetryOutcome; 4] = [
    TelemetryOutcome::Accepted,
    TelemetryOutcome::KernelRefused,
    TelemetryOutcome::BoundaryRefused,
    TelemetryOutcome::InternalError,
];

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Corpus {
    pub schema: String,
    pub version: u32,
    pub vocabulary: Vocabulary,
    pub required_coverage: Vec<String>,
    pub semantic_cases: Vec<SemanticCase>,
    pub boundary_cases: Vec<BoundaryCase>,
    pub recovery_cases: Vec<RecoveryCase>,
    pub goldens: Vec<Golden>,
}

impl Corpus {
    pub fn parse(input: &str) -> Result<Self, String> {
        let mut deserializer = serde_json::Deserializer::from_str(input);
        let corpus = Self::deserialize(&mut deserializer).map_err(|error| error.to_string())?;
        deserializer.end().map_err(|error| error.to_string())?;
        corpus.validate()?;
        Ok(corpus)
    }

    fn validate(&self) -> Result<(), String> {
        require(self.schema == "ex_argus.v4.conformance", "invalid schema")?;
        require(self.version == 5, "invalid version")?;
        self.vocabulary.validate()?;
        unique_strings(&self.required_coverage, "required coverage")?;
        require(!self.semantic_cases.is_empty(), "empty semantic cases")?;
        require(!self.boundary_cases.is_empty(), "empty boundary cases")?;
        require(!self.recovery_cases.is_empty(), "empty recovery cases")?;
        require(!self.goldens.is_empty(), "empty goldens")?;

        let mut ids = HashSet::new();
        let mut coverage = HashSet::new();
        for case in &self.semantic_cases {
            unique_id(&mut ids, &case.id)?;
            unique_strings(&case.covers, "case coverage")?;
            coverage.extend(case.covers.iter().cloned());
            case.validate()?;
        }
        for case in &self.boundary_cases {
            unique_id(&mut ids, &case.id)?;
            if let Some(telemetry) = &case.telemetry {
                require(
                    telemetry.outcome == TelemetryOutcome::BoundaryRefused
                        && telemetry.sequence.is_none()
                        && telemetry.reason.as_deref() == Some(case.expected.reason.as_str()),
                    "invalid boundary telemetry",
                )?;
            }
        }
        for case in &self.recovery_cases {
            unique_id(&mut ids, &case.id)?;
            require(
                self.semantic_cases
                    .iter()
                    .any(|semantic| semantic.id == case.source_case),
                "unknown recovery source case",
            )?;
            require(
                case.telemetry_events == 0,
                "recovery telemetry must be zero",
            )?;
        }
        for golden in &self.goldens {
            unique_id(&mut ids, &golden.id)?;
            validate_hex(&golden.transcript_hex, None)?;
            validate_hex(&golden.digest, Some(64))?;
        }
        require(
            self.required_coverage
                .iter()
                .all(|item| coverage.contains(item)),
            "required coverage not advertised by semantic cases",
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Vocabulary {
    pub actions: Vec<ActionTag>,
    pub capabilities: Vec<Capability>,
    pub egress: Vec<Egress>,
    pub confidentiality: Vec<Conf>,
    pub integrity: Vec<Integ>,
    pub modes: Vec<Mode>,
    pub verdicts: Vec<Verdict>,
    pub dispositions: Vec<Disposition>,
    pub outcomes: Vec<Outcome>,
    pub fallbacks: Vec<Fallback>,
    pub cross_branches: Vec<CrossBranch>,
    pub admissions: Vec<AdmissionTag>,
    pub telemetry_outcomes: Vec<TelemetryOutcome>,
}

impl Vocabulary {
    fn validate(&self) -> Result<(), String> {
        require(self.actions == ACTIONS, "action vocabulary mismatch")?;
        require(
            self.capabilities == CAPABILITIES,
            "capability vocabulary mismatch",
        )?;
        require(self.egress == EGRESS, "egress vocabulary mismatch")?;
        require(
            self.confidentiality == CONFIDENTIALITY,
            "confidentiality vocabulary mismatch",
        )?;
        require(self.integrity == INTEGRITY, "integrity vocabulary mismatch")?;
        require(self.modes == MODES, "mode vocabulary mismatch")?;
        require(self.verdicts == VERDICTS, "verdict vocabulary mismatch")?;
        require(
            self.dispositions == DISPOSITIONS,
            "disposition vocabulary mismatch",
        )?;
        require(self.outcomes == OUTCOMES, "outcome vocabulary mismatch")?;
        require(self.fallbacks == FALLBACKS, "fallback vocabulary mismatch")?;
        require(
            self.cross_branches == CROSS_BRANCHES,
            "cross branch vocabulary mismatch",
        )?;
        require(
            self.admissions == ADMISSIONS,
            "admission vocabulary mismatch",
        )?;
        require(
            self.telemetry_outcomes == TELEMETRY_OUTCOMES,
            "telemetry outcome vocabulary mismatch",
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct SemanticCase {
    pub id: String,
    pub background: Background,
    pub initial_chain: Chain,
    pub covers: Vec<String>,
    pub steps: Vec<Step>,
}

impl SemanticCase {
    fn validate(&self) -> Result<(), String> {
        require(!self.id.is_empty(), "empty case id")?;
        require(
            self.initial_chain.version == 5,
            "invalid initial chain version",
        )?;
        require(self.initial_chain.sequence == 0, "invalid initial sequence")?;
        validate_hex(&self.initial_chain.head, Some(64))?;
        require(!self.steps.is_empty(), "empty semantic case")?;
        let mut ids = HashSet::new();
        let mut state: Option<&State> = None;
        let mut chain = &self.initial_chain;
        for step in &self.steps {
            unique_id(&mut ids, &step.id)?;
            step.command.validate_sets()?;
            step.expected.state.validate()?;
            require(
                step.expected.chain.version == 5,
                "invalid checkpoint version",
            )?;
            validate_hex(&step.expected.chain.head, Some(64))?;
            if let Some(transcript) = &step.expected.transcript_hex {
                validate_hex(transcript, None)?;
            }
            match &step.expected.result {
                ResultExpectation::Accepted { .. } => {
                    require(
                        step.expected.chain.sequence == chain.sequence + 1,
                        "accepted sequence is not contiguous",
                    )?;
                    require(
                        step.expected.telemetry.outcome == TelemetryOutcome::Accepted,
                        "accepted telemetry mismatch",
                    )?;
                    require(
                        step.expected.telemetry.sequence == Some(step.expected.chain.sequence),
                        "accepted telemetry sequence mismatch",
                    )?;
                }
                ResultExpectation::Error { class, reason } => {
                    require(
                        *class == ErrorClass::Kernel,
                        "semantic error must be kernel",
                    )?;
                    require(!reason.is_empty(), "empty kernel error")?;
                    require(step.expected.chain == *chain, "refusal changed chain")?;
                    if let Some(previous) = state {
                        require(step.expected.state == *previous, "refusal changed state")?;
                    }
                    require(
                        step.expected.telemetry.outcome == TelemetryOutcome::KernelRefused,
                        "refusal telemetry mismatch",
                    )?;
                    require(
                        step.expected.telemetry.sequence.is_none(),
                        "refusal has sequence",
                    )?;
                }
            }
            step.expected.telemetry.validate(&step.command)?;
            state = Some(&step.expected.state);
            chain = &step.expected.chain;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Step {
    pub id: String,
    pub command: Command,
    pub expected: Checkpoint,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Checkpoint {
    pub result: ResultExpectation,
    pub state: State,
    pub chain: Chain,
    pub telemetry: TelemetryExpectation,
    pub transcript_hex: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case", deny_unknown_fields)]
pub enum ResultExpectation {
    Accepted { action: Action },
    Error { class: ErrorClass, reason: String },
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ErrorClass {
    Boundary,
    Kernel,
    Recovery,
    Internal,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct TelemetryExpectation {
    pub command: ActionTag,
    pub outcome: TelemetryOutcome,
    pub sequence: Option<u64>,
    pub reason: Option<String>,
    pub verdict: Option<Verdict>,
    pub disposition: Option<Disposition>,
    pub branch: Option<CrossBranch>,
}

impl TelemetryExpectation {
    fn validate(&self, command: &Command) -> Result<(), String> {
        require(self.command == command.tag(), "telemetry command mismatch")?;
        match self.outcome {
            TelemetryOutcome::Accepted => require(self.reason.is_none(), "accepted has reason"),
            TelemetryOutcome::KernelRefused | TelemetryOutcome::BoundaryRefused => {
                require(self.reason.is_some(), "refusal missing reason")
            }
            TelemetryOutcome::InternalError => Ok(()),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Chain {
    pub version: u32,
    pub sequence: u64,
    pub head: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Background {
    pub mode: Mode,
    pub allow_ceiling: Ceiling,
    pub inspect_ceiling: Ceiling,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Ceiling {
    pub network_external: Option<Conf>,
    pub network_internal: Option<Conf>,
    pub filesystem_write: Option<Conf>,
    pub ipc: Option<Conf>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Policy {
    pub tool: String,
    pub required_caps: Vec<Capability>,
    pub conf_clearance: Conf,
    pub integ_floor: Integ,
    pub integ_inspect: Integ,
    pub output_conf: Conf,
    pub output_integ: Integ,
    pub declared_egress: Vec<Egress>,
    pub policy_digest: String,
}

impl Policy {
    fn validate_sets(&self) -> Result<(), String> {
        unique_copy(&self.required_caps, "required capabilities")?;
        unique_copy(&self.declared_egress, "declared egress")
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Inspection {
    pub id: String,
    pub inv: String,
    pub challenge: String,
    pub args_hash: String,
    pub policy_digest: String,
    pub positive: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Resolution {
    pub id: String,
    pub inv: String,
    pub outcome: Outcome,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Conformance {
    pub id: String,
    pub output: String,
    pub src: String,
    pub rcv: String,
    pub descriptor: String,
    pub assignment: String,
    pub positive: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CrossInput {
    pub src: String,
    pub rcv: String,
    pub crossing: String,
    pub output_hash: String,
    pub descriptor: String,
    pub fallback: Fallback,
    pub t_integ: Integ,
    pub t_conf: Option<Conf>,
    pub assignment: String,
    pub evidence: Option<Conformance>,
    pub released_conf: Conf,
    pub released_integ: Integ,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case", deny_unknown_fields)]
pub enum Command {
    RegisterTool {
        tool: String,
    },
    UnregisterTool {
        tool: String,
    },
    Delegate {
        grantor: String,
        grantee: String,
    },
    GrantCapability {
        parent: String,
        child: String,
        cap: Capability,
    },
    GrantCrossing {
        grantor: String,
        agent: String,
        assignment: String,
        n: u32,
    },
    Revoke {
        parent: String,
        target: String,
    },
    CascadeRevoke {
        child: String,
        parent: String,
    },
    Ingest {
        agent: String,
        src: Option<String>,
        pconf: Conf,
        pinteg: Integ,
    },
    BeginInvocation {
        agent: String,
        inv: String,
        challenge: String,
        policy: Policy,
        egress: Vec<Egress>,
        args_hash: String,
        authorized: bool,
    },
    AuthorizeInspected {
        inv: String,
        attestation: Inspection,
    },
    SettleInvocation {
        inv: String,
        outcome: Outcome,
        resolution: Option<Resolution>,
    },
    CrossOutput {
        input: CrossInput,
    },
}

impl Command {
    pub fn tag(&self) -> ActionTag {
        match self {
            Self::RegisterTool { .. } => ActionTag::RegisterTool,
            Self::UnregisterTool { .. } => ActionTag::UnregisterTool,
            Self::Delegate { .. } => ActionTag::Delegate,
            Self::GrantCapability { .. } => ActionTag::GrantCapability,
            Self::GrantCrossing { .. } => ActionTag::GrantCrossing,
            Self::Revoke { .. } => ActionTag::Revoke,
            Self::CascadeRevoke { .. } => ActionTag::CascadeRevoke,
            Self::Ingest { .. } => ActionTag::Ingest,
            Self::BeginInvocation { .. } => ActionTag::BeginInvocation,
            Self::AuthorizeInspected { .. } => ActionTag::AuthorizeInspected,
            Self::SettleInvocation { .. } => ActionTag::SettleInvocation,
            Self::CrossOutput { .. } => ActionTag::CrossOutput,
        }
    }

    fn validate_sets(&self) -> Result<(), String> {
        if let Self::BeginInvocation { policy, egress, .. } = self {
            policy.validate_sets()?;
            unique_copy(egress, "attested egress")?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "type", rename_all = "snake_case", deny_unknown_fields)]
pub enum Action {
    RegisterTool {
        tool: String,
    },
    UnregisterTool {
        tool: String,
    },
    Delegate {
        grantor: String,
        grantee: String,
    },
    GrantCapability {
        parent: String,
        child: String,
        cap: Capability,
    },
    GrantCrossing {
        grantor: String,
        agent: String,
        assignment: String,
        n: u32,
    },
    Revoke {
        parent: String,
        target: String,
    },
    CascadeRevoke {
        child: String,
        parent: String,
    },
    Ingest {
        agent: String,
        src: Option<String>,
        pconf: Conf,
        pinteg: Integ,
        disposition: Disposition,
    },
    BeginInvocation {
        agent: String,
        inv: String,
        tool: String,
        verdict: Verdict,
        authorized: bool,
    },
    AuthorizeInspected {
        inv: String,
        attestation: String,
        admitted: bool,
    },
    SettleInvocation {
        inv: String,
        agent: String,
        disposition: Disposition,
        outcome: Outcome,
        clvl: Conf,
        ilvl: Integ,
        resolution: Option<String>,
    },
    CrossOutput {
        src: String,
        rcv: String,
        crossing: String,
        branch: CrossBranch,
        disposition: Disposition,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct State {
    pub agent_active: Vec<String>,
    pub agent_parent: Vec<(String, String)>,
    pub agent_cap: Vec<(String, Vec<Capability>)>,
    pub taint_levels: Vec<(String, Vec<Conf>)>,
    pub integ_levels: Vec<(String, Vec<Integ>)>,
    pub pending: Vec<(String, Pending)>,
    pub challenges: Vec<(String, Challenge)>,
    pub consumed_ids: Vec<String>,
    pub consumed_attestations: Vec<String>,
    pub consumed_crossings: Vec<String>,
    pub crossing_grants: Vec<((String, String), CrossingGrant)>,
    pub tool_registered: Vec<String>,
}

impl State {
    fn validate(&self) -> Result<(), String> {
        sorted_unique_strings(&self.agent_active, "active agents")?;
        sorted_unique_pairs(&self.agent_parent, "agent parent")?;
        sorted_unique_pairs(&self.agent_cap, "agent capabilities")?;
        sorted_unique_pairs(&self.taint_levels, "taint levels")?;
        sorted_unique_pairs(&self.integ_levels, "integrity levels")?;
        sorted_unique_pairs(&self.pending, "pending")?;
        sorted_unique_pairs(&self.challenges, "challenges")?;
        sorted_unique_strings(&self.consumed_ids, "consumed ids")?;
        sorted_unique_strings(&self.consumed_attestations, "consumed attestations")?;
        sorted_unique_strings(&self.consumed_crossings, "consumed crossings")?;
        sorted_unique_crossing_pairs(&self.crossing_grants)?;
        sorted_unique_strings(&self.tool_registered, "registered tools")?;
        for (_, values) in &self.agent_cap {
            ordered_unique(values, &CAPABILITIES, "state capabilities")?;
        }
        for (_, values) in &self.taint_levels {
            ordered_unique(values, &CONFIDENTIALITY, "state confidentiality")?;
        }
        for (_, values) in &self.integ_levels {
            ordered_unique(values, &INTEGRITY, "state integrity")?;
        }
        for (_, pending) in &self.pending {
            pending.validate()?;
        }
        for (_, challenge) in &self.challenges {
            challenge.validate()?;
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Pending {
    pub agent: String,
    pub policy: Policy,
    pub egress: Vec<Egress>,
    pub admission: Admission,
    pub disposition: Disposition,
    pub authorized: bool,
    pub quarantined: bool,
}

impl Pending {
    fn validate(&self) -> Result<(), String> {
        self.policy.validate_sets()?;
        ordered_unique(&self.egress, &EGRESS, "pending egress")?;
        self.admission.validate()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Challenge {
    pub challenge: String,
    pub agent: String,
    pub policy: Policy,
    pub egress: Vec<Egress>,
    pub args_hash: String,
    pub authorized: bool,
}

impl Challenge {
    fn validate(&self) -> Result<(), String> {
        self.policy.validate_sets()?;
        ordered_unique(&self.egress, &EGRESS, "challenge egress")
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Admission {
    pub kind: AdmissionTag,
    pub attestation: Option<String>,
}

impl Admission {
    fn validate(&self) -> Result<(), String> {
        require(
            matches!(
                (self.kind, self.attestation.is_some()),
                (AdmissionTag::Inspected, true)
                    | (AdmissionTag::Plain | AdmissionTag::Bypassed, false)
            ),
            "invalid admission payload",
        )
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct CrossingGrant {
    pub remaining: u32,
    pub provisioned: u32,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct BoundaryCase {
    pub id: String,
    pub mutation: BoundaryMutation,
    pub expected: ErrorExpectation,
    pub telemetry: Option<TelemetryExpectation>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum BoundaryMutation {
    InvalidShape,
    MissingKey,
    ExtraKey,
    InvalidType,
    InvalidUtf8,
    EmptyValue,
    OversizeValue,
    UnknownEnum,
    DuplicateSetMember,
    U32Overflow,
    InvalidDigest,
    InvalidVersion,
    RecoveryCount,
    RecoveryContent,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct RecoveryCase {
    pub id: String,
    pub source_case: String,
    pub mutation: RecoveryMutation,
    pub expected: ErrorExpectation,
    pub telemetry_events: u8,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum RecoveryMutation {
    Edit,
    Insertion,
    Deletion,
    Reorder,
    Duplicate,
    Gap,
    WrongBackground,
    WrongAction,
    WrongDigest,
    ReplayRefusal,
    StaleAnchor,
    TruncatedAnchor,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ErrorExpectation {
    pub class: ErrorClass,
    pub reason: String,
    pub path: Vec<String>,
    pub index: Option<u64>,
    pub cause: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Golden {
    pub id: String,
    pub kind: GoldenKind,
    pub background: Option<Background>,
    pub case_id: Option<String>,
    pub step_id: Option<String>,
    pub transcript_hex: String,
    pub digest: String,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum GoldenKind {
    Genesis,
    Link,
}

macro_rules! string_enum {
    ($name:ident { $($variant:ident),+ $(,)? }) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
        #[serde(rename_all = "snake_case")]
        pub enum $name { $($variant),+ }
    };
}

string_enum!(ActionTag {
    RegisterTool,
    UnregisterTool,
    Delegate,
    GrantCapability,
    GrantCrossing,
    Revoke,
    CascadeRevoke,
    Ingest,
    BeginInvocation,
    AuthorizeInspected,
    SettleInvocation,
    CrossOutput
});
string_enum!(Capability {
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
    Ipc
});
string_enum!(Egress {
    NetworkExternal,
    NetworkInternal,
    FilesystemWrite,
    Ipc
});
string_enum!(Conf {
    Public,
    Internal,
    Sensitive,
    Restricted
});
string_enum!(Integ {
    Untrusted,
    Standard,
    Trusted,
    Attested
});
string_enum!(Mode { Enforce, Monitor });
string_enum!(Verdict {
    Allow,
    InspectionRequired,
    Deny
});
string_enum!(Disposition {
    Permitted,
    Blocked,
    MonitorBypassed
});
string_enum!(Outcome {
    Success,
    Failure,
    Ambiguous
});
string_enum!(Fallback {
    Fail,
    ReleaseUnendorsed
});
string_enum!(CrossBranch {
    Endorsed,
    Unendorsed,
    Fail
});
string_enum!(AdmissionTag {
    Plain,
    Inspected,
    Bypassed
});
string_enum!(TelemetryOutcome {
    Accepted,
    KernelRefused,
    BoundaryRefused,
    InternalError
});

fn require(condition: bool, message: &str) -> Result<(), String> {
    if condition {
        Ok(())
    } else {
        Err(message.to_owned())
    }
}

fn unique_id(ids: &mut HashSet<String>, id: &str) -> Result<(), String> {
    require(!id.is_empty(), "empty id")?;
    require(ids.insert(id.to_owned()), "duplicate id")
}

fn unique_strings(values: &[String], label: &str) -> Result<(), String> {
    let mut seen = HashSet::new();
    require(
        values.iter().all(|value| seen.insert(value)),
        &format!("duplicate {label}"),
    )
}

fn unique_copy<T: Copy + Eq + std::hash::Hash>(values: &[T], label: &str) -> Result<(), String> {
    let mut seen = HashSet::new();
    require(
        values.iter().copied().all(|value| seen.insert(value)),
        &format!("duplicate {label}"),
    )
}

fn ordered_unique<T: Copy + Eq>(values: &[T], order: &[T], label: &str) -> Result<(), String> {
    let positions: Option<Vec<_>> = values
        .iter()
        .map(|value| order.iter().position(|candidate| candidate == value))
        .collect();
    let positions = positions.ok_or_else(|| format!("unknown {label}"))?;
    require(
        positions.windows(2).all(|pair| pair[0] < pair[1]),
        &format!("unordered or duplicate {label}"),
    )
}

fn sorted_unique_strings(values: &[String], label: &str) -> Result<(), String> {
    require(
        values
            .windows(2)
            .all(|pair| pair[0].as_bytes() < pair[1].as_bytes()),
        &format!("unordered or duplicate {label}"),
    )
}

fn sorted_unique_pairs<T>(values: &[(String, T)], label: &str) -> Result<(), String> {
    require(
        values
            .windows(2)
            .all(|pair| pair[0].0.as_bytes() < pair[1].0.as_bytes()),
        &format!("unordered or duplicate {label}"),
    )
}

fn sorted_unique_crossing_pairs(
    values: &[((String, String), CrossingGrant)],
) -> Result<(), String> {
    require(
        values.windows(2).all(|pair| {
            (pair[0].0.0.as_bytes(), pair[0].0.1.as_bytes())
                < (pair[1].0.0.as_bytes(), pair[1].0.1.as_bytes())
        }),
        "unordered or duplicate crossing grants",
    )?;
    require(
        values
            .iter()
            .all(|(_, grant)| grant.remaining <= grant.provisioned),
        "invalid crossing grant",
    )
}

fn validate_hex(value: &str, exact_len: Option<usize>) -> Result<(), String> {
    require(!value.is_empty(), "empty hex")?;
    require(value.len().is_multiple_of(2), "odd hex length")?;
    if let Some(length) = exact_len {
        require(value.len() == length, "invalid hex length")?;
    }
    require(
        value
            .bytes()
            .all(|byte| byte.is_ascii_digit() || (b'a'..=b'f').contains(&byte)),
        "invalid or noncanonical hex",
    )
}
