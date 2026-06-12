use argus_kernel::{CapKind, ConfLevel, EgressKind, FlowMode, KernelError};

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
    pub authorizer_denied: bool,
}

impl ExplainReport {
    pub fn denied_findings(&self) -> impl Iterator<Item = &GateFinding> {
        self.findings.iter().filter(|f| f.outcome == CheckOutcome::Denied)
    }
}
