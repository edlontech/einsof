use std::collections::HashMap;

use argus_explain::{
    CheckOutcome, ExplainReport, GateCheck, GateFinding, IntegCheckOutcome, IntegGateFinding,
    LeverGateFinding, Rescue,
};
use argus_kernel::{AgentId, InvocationId, ToolId};
use rustler::{NifMap, NifTaggedEnum, NifUnitEnum, ResourceArc};

use crate::enums::{attested_into_kernel, CapKindN, ConfLevelN, EgressKindN, FlowModeN, IntegLevelN};
use crate::event::KernelErrorN;
use crate::instance::KernelInstance;
use crate::oracles::{ConstAuthorizer, ConstConformance, MapContentGate};
use crate::state::{BackgroundN, StateN};

#[derive(Debug, NifUnitEnum)]
pub enum GateCheckN {
    SpecTaintVsNewEgress,
    NewFloorVsInFlight,
    SelfFloor,
    ChildTaintVsParentFlight,
    ElevatedVsInFlight,
    SpecIntegVsNewFloor,
    NewEmissionVsInFlightFloor,
    SelfEmissionVsOwnFloor,
    ChildIntegVsParentInFlight,
    DegradeVsInFlightFloor,
    ChildIntegVsLeverFloor,
    GranterIntegVsLeverFloor,
}

impl GateCheckN {
    fn from_explain(c: GateCheck) -> Self {
        match c {
            GateCheck::SpecTaintVsNewEgress => Self::SpecTaintVsNewEgress,
            GateCheck::NewFloorVsInFlight => Self::NewFloorVsInFlight,
            GateCheck::SelfFloor => Self::SelfFloor,
            GateCheck::ChildTaintVsParentFlight => Self::ChildTaintVsParentFlight,
            GateCheck::ElevatedVsInFlight => Self::ElevatedVsInFlight,
            GateCheck::SpecIntegVsNewFloor => Self::SpecIntegVsNewFloor,
            GateCheck::NewEmissionVsInFlightFloor => Self::NewEmissionVsInFlightFloor,
            GateCheck::SelfEmissionVsOwnFloor => Self::SelfEmissionVsOwnFloor,
            GateCheck::ChildIntegVsParentInFlight => Self::ChildIntegVsParentInFlight,
            GateCheck::DegradeVsInFlightFloor => Self::DegradeVsInFlightFloor,
            GateCheck::ChildIntegVsLeverFloor => Self::ChildIntegVsLeverFloor,
            GateCheck::GranterIntegVsLeverFloor => Self::GranterIntegVsLeverFloor,
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

#[derive(Debug, NifUnitEnum)]
pub enum IntegCheckOutcomeN {
    Allowed,
    AllowedViaInspect,
    Denied,
}

impl IntegCheckOutcomeN {
    fn from_explain(o: IntegCheckOutcome) -> Self {
        match o {
            IntegCheckOutcome::Allowed => Self::Allowed,
            IntegCheckOutcome::AllowedViaInspect => Self::AllowedViaInspect,
            IntegCheckOutcome::Denied => Self::Denied,
        }
    }
}

#[derive(Debug, NifTaggedEnum)]
pub enum RescueN {
    OverrideGrant(String, String, ConfLevelN),
    CeilingRaise(EgressKindN, ConfLevelN),
    ToolRelabel(String, ConfLevelN),
    ContentGatePass(String),
    IntegFloorRelabel(String, IntegLevelN),
    EndorseIngestion(String),
    ReturnConformancePass(String, String),
    RaiseIntegrity(String),
    LeverFloorRelabel(IntegLevelN),
}

impl RescueN {
    fn from_explain(r: Rescue) -> Self {
        match r {
            Rescue::OverrideGrant { agent, tool, level } => {
                Self::OverrideGrant(agent, tool, ConfLevelN::from_kernel(level))
            }
            Rescue::CeilingRaise { egress, to_level } => {
                Self::CeilingRaise(EgressKindN::from_kernel(egress), ConfLevelN::from_kernel(to_level))
            }
            Rescue::ToolRelabel { tool, current_floor } => {
                Self::ToolRelabel(tool, ConfLevelN::from_kernel(current_floor))
            }
            Rescue::ContentGatePass { tool } => Self::ContentGatePass(tool),
            Rescue::IntegFloorRelabel { tool, current_floor } => {
                Self::IntegFloorRelabel(tool, IntegLevelN::from_kernel(current_floor))
            }
            Rescue::EndorseIngestion { tool } => Self::EndorseIngestion(tool),
            Rescue::ReturnConformancePass { child, parent } => {
                Self::ReturnConformancePass(child, parent)
            }
            Rescue::RaiseIntegrity { agent } => Self::RaiseIntegrity(agent),
            Rescue::LeverFloorRelabel { current_floor } => {
                Self::LeverFloorRelabel(IntegLevelN::from_kernel(current_floor))
            }
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
pub struct IntegGateFindingN {
    pub check: GateCheckN,
    pub tool: String,
    pub level: IntegLevelN,
    pub floor: IntegLevelN,
    pub inspect_floor: IntegLevelN,
    pub outcome: IntegCheckOutcomeN,
    pub rescues: Vec<RescueN>,
}

impl IntegGateFindingN {
    fn from_explain(f: IntegGateFinding) -> Self {
        Self {
            check: GateCheckN::from_explain(f.check),
            tool: f.tool,
            level: IntegLevelN::from_kernel(f.level),
            floor: IntegLevelN::from_kernel(f.floor),
            inspect_floor: IntegLevelN::from_kernel(f.inspect_floor),
            outcome: IntegCheckOutcomeN::from_explain(f.outcome),
            rescues: f.rescues.into_iter().map(RescueN::from_explain).collect(),
        }
    }
}

#[derive(Debug, NifMap)]
pub struct LeverGateFindingN {
    pub check: GateCheckN,
    pub level: IntegLevelN,
    pub floor: IntegLevelN,
    pub inspect_floor: IntegLevelN,
    pub outcome: IntegCheckOutcomeN,
    pub rescues: Vec<RescueN>,
}

impl LeverGateFindingN {
    fn from_explain(f: LeverGateFinding) -> Self {
        Self {
            check: GateCheckN::from_explain(f.check),
            level: IntegLevelN::from_kernel(f.level),
            floor: IntegLevelN::from_kernel(f.floor),
            inspect_floor: IntegLevelN::from_kernel(f.inspect_floor),
            outcome: IntegCheckOutcomeN::from_explain(f.outcome),
            rescues: f.rescues.into_iter().map(RescueN::from_explain).collect(),
        }
    }
}

#[derive(Debug, NifMap)]
pub struct ExplainReportN {
    pub verdict: Option<KernelErrorN>,
    pub missing_caps: Vec<CapKindN>,
    pub findings: Vec<GateFindingN>,
    pub integ_findings: Vec<IntegGateFindingN>,
    pub lever_findings: Vec<LeverGateFindingN>,
    pub authorizer_denied: bool,
}

impl ExplainReportN {
    pub fn from_explain(r: ExplainReport) -> Self {
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
            integ_findings: r
                .integ_findings
                .into_iter()
                .map(IntegGateFindingN::from_explain)
                .collect(),
            lever_findings: r
                .lever_findings
                .into_iter()
                .map(LeverGateFindingN::from_explain)
                .collect(),
            authorizer_denied: r.authorizer_denied,
        }
    }
}

#[allow(clippy::too_many_arguments)]
#[rustler::nif(schedule = "DirtyCpu")]
pub fn explain_invoke(
    state: StateN,
    bg: BackgroundN,
    agent: String,
    tool: String,
    inv: String,
    authorizer_allows: bool,
    content_gate: HashMap<String, bool>,
    attested_egress: Vec<EgressKindN>,
) -> ExplainReportN {
    let attested = attested_into_kernel(attested_egress);
    ExplainReportN::from_explain(argus_explain::explain_invoke(
        &state.into_kernel(),
        &bg.into_kernel(),
        &ConstAuthorizer(authorizer_allows),
        &MapContentGate(content_gate),
        &AgentId(agent),
        &ToolId(tool),
        &InvocationId(inv),
        &attested,
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
pub fn explain_sentinel_degrade_integrity(
    state: StateN,
    bg: BackgroundN,
    agent: String,
    level: IntegLevelN,
    content_gate: HashMap<String, bool>,
) -> ExplainReportN {
    ExplainReportN::from_explain(argus_explain::explain_sentinel_degrade_integrity(
        &state.into_kernel(),
        &bg.into_kernel(),
        &MapContentGate(content_gate),
        &AgentId(agent),
        level.into_kernel(),
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn explain_return_endorsed(
    state: StateN,
    bg: BackgroundN,
    child: String,
    parent: String,
    return_conforms: bool,
    clvl: ConfLevelN,
    ilvl: IntegLevelN,
) -> ExplainReportN {
    ExplainReportN::from_explain(argus_explain::explain_return_endorsed(
        &state.into_kernel(),
        &bg.into_kernel(),
        &ConstConformance(return_conforms),
        &AgentId(child),
        &AgentId(parent),
        clvl.into_kernel(),
        ilvl.into_kernel(),
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn explain_grant_override(
    state: StateN,
    bg: BackgroundN,
    granter: String,
    target: String,
    level: ConfLevelN,
) -> ExplainReportN {
    ExplainReportN::from_explain(argus_explain::explain_grant_override(
        &state.into_kernel(),
        &bg.into_kernel(),
        &AgentId(granter),
        &AgentId(target),
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
    attested_egress: Vec<EgressKindN>,
) -> ExplainReportN {
    let attested = attested_into_kernel(attested_egress);
    let inner = handle.inner.lock().unwrap();
    ExplainReportN::from_explain(argus_explain::explain_invoke(
        &inner.state,
        &handle.bg,
        &ConstAuthorizer(authorizer_allows),
        &MapContentGate(content_gate),
        &AgentId(agent),
        &ToolId(tool),
        &InvocationId(inv),
        &attested,
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

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_explain_sentinel_degrade_integrity(
    handle: ResourceArc<KernelInstance>,
    agent: String,
    level: IntegLevelN,
    content_gate: HashMap<String, bool>,
) -> ExplainReportN {
    let inner = handle.inner.lock().unwrap();
    ExplainReportN::from_explain(argus_explain::explain_sentinel_degrade_integrity(
        &inner.state,
        &handle.bg,
        &MapContentGate(content_gate),
        &AgentId(agent),
        level.into_kernel(),
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_explain_return_endorsed(
    handle: ResourceArc<KernelInstance>,
    child: String,
    parent: String,
    return_conforms: bool,
    clvl: ConfLevelN,
    ilvl: IntegLevelN,
) -> ExplainReportN {
    let inner = handle.inner.lock().unwrap();
    ExplainReportN::from_explain(argus_explain::explain_return_endorsed(
        &inner.state,
        &handle.bg,
        &ConstConformance(return_conforms),
        &AgentId(child),
        &AgentId(parent),
        clvl.into_kernel(),
        ilvl.into_kernel(),
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_explain_grant_override(
    handle: ResourceArc<KernelInstance>,
    granter: String,
    target: String,
    level: ConfLevelN,
) -> ExplainReportN {
    let inner = handle.inner.lock().unwrap();
    ExplainReportN::from_explain(argus_explain::explain_grant_override(
        &inner.state,
        &handle.bg,
        &AgentId(granter),
        &AgentId(target),
        level.into_kernel(),
    ))
}
