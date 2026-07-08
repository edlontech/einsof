use argus_kernel::{CapKind, ConfLevel, EgressKind, FlowMode, IntegLevel, KernelError};

/// Which gate produced a finding. Names mirror the spec's check numbering.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GateCheck {
    /// invoke_start 2a: existing speculative taint x the new tool's egress.
    SpecTaintVsNewEgress,
    /// invoke_start 2b: the new tool's conf floor x an in-flight tool's egress.
    NewFloorVsInFlight,
    /// invoke_start 2c: the new tool's own floor x its own egress.
    SelfFloor,
    /// return_unendorsed: child taint x a parent in-flight tool's egress.
    ChildTaintVsParentFlight,
    /// sentinel_elevate_taint: the raised level x an in-flight tool's egress.
    ElevatedVsInFlight,
    /// invoke_start 4a: existing speculative integrity x the new tool's floor.
    SpecIntegVsNewFloor,
    /// invoke_start 4b: the new tool's emission x an in-flight tool's floor.
    NewEmissionVsInFlightFloor,
    /// invoke_start 4c: the new tool's own emission x its own floor.
    SelfEmissionVsOwnFloor,
    /// return_unendorsed integrity gate: child integrity x a parent in-flight tool's floor.
    ChildIntegVsParentInFlight,
    /// sentinel_degrade_integrity: the degrade level x an in-flight tool's floor.
    DegradeVsInFlightFloor,
    /// return_endorsed's lever gate: the child's held integrity x the shared lever floor.
    ChildIntegVsLeverFloor,
    /// grant_override's lever gate: the granter's held integrity x the shared lever floor
    /// (strict -- no inspect band, `inspect_floor` is pinned to `floor`).
    GranterIntegVsLeverFloor,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CheckOutcome {
    /// Flow mode is ALLOW.
    Allowed,
    /// Flow mode is INSPECT and the content gate passed.
    AllowedViaInspect,
    /// Flow mode is DENY but an armed (un-consumed) override rescues it.
    RescuedByOverride,
    Denied,
}

/// A counterfactual: one change that would flip a Denied finding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Rescue {
    /// Arm (or re-arm) a flow override for (agent, tool, level).
    OverrideGrant { agent: String, tool: String, level: ConfLevel },
    /// Raise the named egress's ALLOW ceiling to `to_level` (the minimal raise that
    /// would flip this finding).
    CeilingRaise { egress: EgressKind, to_level: ConfLevel },
    /// Lower the named tool's conf floor below its current value (only emitted when
    /// the denied level IS that tool's floor).
    ToolRelabel { tool: String, current_floor: ConfLevel },
    /// The content gate verdict for this tool was false on an INSPECT pair.
    ContentGatePass { tool: String },
    /// Lower the named tool's integrity floor below its current value (the integrity dual
    /// of `ToolRelabel`; every integrity check's floor belongs to the named tool).
    IntegFloorRelabel { tool: String, current_floor: IntegLevel },
    /// No override lever exists for the integrity gate (design: endorsement is the only
    /// way up). Below the inspect band there is no rescue but a genuinely higher-integrity
    /// (endorsed) ingestion at this tool.
    EndorseIngestion { tool: String },
    /// The `return_conforms` verdict for (child, parent) was false on an INSPECT-band lever
    /// pair -- the dual of `ContentGatePass` for the vouch return_endorsed's lever gate uses.
    ReturnConformancePass { child: String, parent: String },
    /// No vouch or override rescues this lever pair; the agent's held integrity itself must
    /// genuinely rise (dual of `EndorseIngestion`, not scoped to a tool).
    RaiseIntegrity { agent: String },
    /// Lower the shared lever floor below its current value (the lever dual of
    /// `IntegFloorRelabel`; lever floors are background-wide, not per-tool).
    LeverFloorRelabel { current_floor: IntegLevel },
}

/// One (level, egress) gate evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GateFinding {
    pub check: GateCheck,
    /// The tool whose egress is being gated (the in-flight tool for 2b-style checks).
    pub tool: String,
    pub level: ConfLevel,
    pub egress: EgressKind,
    pub mode: FlowMode,
    pub outcome: CheckOutcome,
    /// Non-empty only when `outcome == Denied`.
    pub rescues: Vec<Rescue>,
}

/// Outcome of an integrity-gate check (CHECK 4 a/b/c, return_unendorsed's integ gate,
/// `sentinel_degrade_integrity`). No `RescuedByOverride` arm exists -- there is no override
/// lever for integrity, endorsement is the only way up.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum IntegCheckOutcome {
    /// The level clears the floor outright.
    Allowed,
    /// The level sits in the inspect band and the content gate passed.
    AllowedViaInspect,
    Denied,
}

/// One (level, floor) integrity-gate evaluation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IntegGateFinding {
    pub check: GateCheck,
    /// The tool whose floor is being gated (owns `floor`/`inspect_floor`).
    pub tool: String,
    pub level: IntegLevel,
    pub floor: IntegLevel,
    pub inspect_floor: IntegLevel,
    pub outcome: IntegCheckOutcome,
    /// Non-empty only when `outcome == Denied`.
    pub rescues: Vec<Rescue>,
}

/// One (level, lever floor) evaluation of a declassification lever's integrity gate
/// (`return_endorsed`'s child check, `grant_override`'s strict granter check). No `tool` field --
/// the floor is a background-wide lever, not per-tool metadata.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LeverGateFinding {
    pub check: GateCheck,
    pub level: IntegLevel,
    pub floor: IntegLevel,
    pub inspect_floor: IntegLevel,
    pub outcome: IntegCheckOutcome,
    /// Non-empty only when `outcome == Denied`.
    pub rescues: Vec<Rescue>,
}

/// The full diagnosis of one would-be transition.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ExplainReport {
    /// Exactly the error the real transition returns, in the kernel's check order.
    /// `None` = the transition would succeed.
    pub verdict: Option<KernelError>,
    /// All capabilities the tool requires that the agent lacks (kernel reports only
    /// the boolean; explain enumerates).
    pub missing_caps: Vec<CapKind>,
    pub findings: Vec<GateFinding>,
    pub integ_findings: Vec<IntegGateFinding>,
    pub lever_findings: Vec<LeverGateFinding>,
    pub authorizer_denied: bool,
}

impl ExplainReport {
    pub fn denied_findings(&self) -> impl Iterator<Item = &GateFinding> {
        self.findings.iter().filter(|f| f.outcome == CheckOutcome::Denied)
    }

    pub fn denied_integ_findings(&self) -> impl Iterator<Item = &IntegGateFinding> {
        self.integ_findings.iter().filter(|f| f.outcome == IntegCheckOutcome::Denied)
    }

    pub fn denied_lever_findings(&self) -> impl Iterator<Item = &LeverGateFinding> {
        self.lever_findings.iter().filter(|f| f.outcome == IntegCheckOutcome::Denied)
    }
}
