use std::collections::HashMap;

use argus_explain::{CheckOutcome, ExplainReport, GateCheck, GateFinding, Rescue};
use argus_kernel::{AgentId, InvocationId, ToolId};
use rustler::{NifMap, NifTaggedEnum, NifUnitEnum, ResourceArc};

use crate::enums::{CapKindN, ConfLevelN, EgressKindN, FlowModeN};
use crate::event::KernelErrorN;
use crate::instance::KernelInstance;
use crate::oracles::{ConstAuthorizer, MapContentGate};
use crate::state::{BackgroundN, StateN};

#[derive(Debug, NifUnitEnum)]
pub enum GateCheckN {
    SpecTaintVsNewEgress,
    NewFloorVsInFlight,
    SelfFloor,
    ChildTaintVsParentFlight,
    ElevatedVsInFlight,
}

impl GateCheckN {
    fn from_explain(c: GateCheck) -> Self {
        match c {
            GateCheck::SpecTaintVsNewEgress => Self::SpecTaintVsNewEgress,
            GateCheck::NewFloorVsInFlight => Self::NewFloorVsInFlight,
            GateCheck::SelfFloor => Self::SelfFloor,
            GateCheck::ChildTaintVsParentFlight => Self::ChildTaintVsParentFlight,
            GateCheck::ElevatedVsInFlight => Self::ElevatedVsInFlight,
        }
    }
}

#[derive(Debug, NifUnitEnum)]
pub enum CheckOutcomeN {
    Allowed,
    AllowedViaInspect,
    RescuedByOverride,
    Denied,
}

impl CheckOutcomeN {
    fn from_explain(o: CheckOutcome) -> Self {
        match o {
            CheckOutcome::Allowed => Self::Allowed,
            CheckOutcome::AllowedViaInspect => Self::AllowedViaInspect,
            CheckOutcome::RescuedByOverride => Self::RescuedByOverride,
            CheckOutcome::Denied => Self::Denied,
        }
    }
}

#[derive(Debug, NifTaggedEnum)]
pub enum RescueN {
    OverrideGrant(String, String, ConfLevelN),
    PolicyAllow(ConfLevelN, EgressKindN),
    ToolRelabel(String, ConfLevelN),
    ContentGatePass(String),
}

impl RescueN {
    fn from_explain(r: Rescue) -> Self {
        match r {
            Rescue::OverrideGrant { agent, tool, level } => {
                Self::OverrideGrant(agent, tool, ConfLevelN::from_kernel(level))
            }
            Rescue::PolicyAllow { level, egress } => Self::PolicyAllow(
                ConfLevelN::from_kernel(level),
                EgressKindN::from_kernel(egress),
            ),
            Rescue::ToolRelabel {
                tool,
                current_floor,
            } => Self::ToolRelabel(tool, ConfLevelN::from_kernel(current_floor)),
            Rescue::ContentGatePass { tool } => Self::ContentGatePass(tool),
        }
    }
}

#[derive(Debug, NifMap)]
pub struct GateFindingN {
    pub check: GateCheckN,
    pub tool: String,
    pub level: ConfLevelN,
    pub egress: EgressKindN,
    pub mode: FlowModeN,
    pub outcome: CheckOutcomeN,
    pub rescues: Vec<RescueN>,
}

impl GateFindingN {
    fn from_explain(f: GateFinding) -> Self {
        Self {
            check: GateCheckN::from_explain(f.check),
            tool: f.tool,
            level: ConfLevelN::from_kernel(f.level),
            egress: EgressKindN::from_kernel(f.egress),
            mode: FlowModeN::from_kernel(f.mode),
            outcome: CheckOutcomeN::from_explain(f.outcome),
            rescues: f.rescues.into_iter().map(RescueN::from_explain).collect(),
        }
    }
}

#[derive(Debug, NifMap)]
pub struct ExplainReportN {
    pub verdict: Option<KernelErrorN>,
    pub missing_caps: Vec<CapKindN>,
    pub findings: Vec<GateFindingN>,
    pub authorizer_denied: bool,
}

impl ExplainReportN {
    fn from_explain(r: ExplainReport) -> Self {
        Self {
            verdict: r.verdict.map(KernelErrorN::from_kernel),
            missing_caps: r
                .missing_caps
                .into_iter()
                .map(CapKindN::from_kernel)
                .collect(),
            findings: r
                .findings
                .into_iter()
                .map(GateFindingN::from_explain)
                .collect(),
            authorizer_denied: r.authorizer_denied,
        }
    }
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn explain_invoke(
    state: StateN,
    bg: BackgroundN,
    agent: String,
    tool: String,
    inv: String,
    authorizer_allows: bool,
    content_gate: HashMap<String, bool>,
) -> ExplainReportN {
    ExplainReportN::from_explain(argus_explain::explain_invoke(
        &state.into_kernel(),
        &bg.into_kernel(),
        &ConstAuthorizer(authorizer_allows),
        &MapContentGate(content_gate),
        &AgentId(agent),
        &ToolId(tool),
        &InvocationId(inv),
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn explain_return_unendorsed(
    state: StateN,
    bg: BackgroundN,
    child: String,
    parent: String,
    content_gate: HashMap<String, bool>,
) -> ExplainReportN {
    ExplainReportN::from_explain(argus_explain::explain_return_unendorsed(
        &state.into_kernel(),
        &bg.into_kernel(),
        &MapContentGate(content_gate),
        &AgentId(child),
        &AgentId(parent),
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn explain_sentinel_elevate_taint(
    state: StateN,
    bg: BackgroundN,
    agent: String,
    level: ConfLevelN,
    content_gate: HashMap<String, bool>,
) -> ExplainReportN {
    ExplainReportN::from_explain(argus_explain::explain_sentinel_elevate_taint(
        &state.into_kernel(),
        &bg.into_kernel(),
        &MapContentGate(content_gate),
        &AgentId(agent),
        level.into_kernel(),
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_explain_invoke(
    handle: ResourceArc<KernelInstance>,
    agent: String,
    tool: String,
    inv: String,
    authorizer_allows: bool,
    content_gate: HashMap<String, bool>,
) -> ExplainReportN {
    let inner = handle.inner.lock().unwrap();
    ExplainReportN::from_explain(argus_explain::explain_invoke(
        &inner.state,
        &handle.bg,
        &ConstAuthorizer(authorizer_allows),
        &MapContentGate(content_gate),
        &AgentId(agent),
        &ToolId(tool),
        &InvocationId(inv),
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_explain_return_unendorsed(
    handle: ResourceArc<KernelInstance>,
    child: String,
    parent: String,
    content_gate: HashMap<String, bool>,
) -> ExplainReportN {
    let inner = handle.inner.lock().unwrap();
    ExplainReportN::from_explain(argus_explain::explain_return_unendorsed(
        &inner.state,
        &handle.bg,
        &MapContentGate(content_gate),
        &AgentId(child),
        &AgentId(parent),
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_explain_sentinel_elevate_taint(
    handle: ResourceArc<KernelInstance>,
    agent: String,
    level: ConfLevelN,
    content_gate: HashMap<String, bool>,
) -> ExplainReportN {
    let inner = handle.inner.lock().unwrap();
    ExplainReportN::from_explain(argus_explain::explain_sentinel_elevate_taint(
        &inner.state,
        &handle.bg,
        &MapContentGate(content_gate),
        &AgentId(agent),
        level.into_kernel(),
    ))
}
