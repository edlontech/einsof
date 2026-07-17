use std::collections::HashMap;

use argus_kernel::{transitions, AgentId, InstructionId, InvocationId, KernelState, ToolId};
use rustler::{NifMap, NifTaggedEnum, Resource, ResourceArc};

use crate::enums::{attested_into_kernel, CapKindN, ConfLevelN, EgressKindN, IntegLevelN};
use crate::event::{ActionN, InstanceOutcome, KernelErrorN};
use crate::explain::ExplainReportN;
use crate::instance::InstanceInner;
use crate::oracles::{ConstAuthorizer, ConstConformance, MapContentGate};
use crate::state::{BackgroundN, StateN};

// A live trajectory with a candidate background bound alongside the live one. Each apply
// evaluates the candidate against the PRE-entry state and commits under live, so the
// candidate never forks the trajectory and state never crosses the NIF boundary.
pub struct ShadowInstance {
    pub inner: std::sync::Mutex<InstanceInner>,
    pub live_bg: argus_kernel::BackgroundTheory,
    pub candidate_bg: argus_kernel::BackgroundTheory,
}

#[rustler::resource_impl]
impl Resource for ShadowInstance {}

// The candidate side is never applied, so its outcome carries no seq/action: it is a
// pure verdict on the pre-entry state.
#[derive(Debug, NifTaggedEnum)]
pub enum ShadowVerdictN {
    Allow,
    Deny(KernelErrorN),
}

#[derive(Debug, NifMap)]
pub struct ShadowOutcome {
    pub live: InstanceOutcome,
    pub candidate: ShadowVerdictN,
    pub report: Option<ExplainReportN>,
}

fn diverged(live: &InstanceOutcome, candidate: &ShadowVerdictN) -> bool {
    match (live, candidate) {
        (InstanceOutcome::Ok(_, _), ShadowVerdictN::Allow) => false,
        (InstanceOutcome::Error(a), ShadowVerdictN::Deny(b)) => a != b,
        _ => true,
    }
}

macro_rules! shadow_verdict {
    ($call:expr) => {
        match $call {
            Ok(_) => ShadowVerdictN::Allow,
            Err(e) => ShadowVerdictN::Deny(KernelErrorN::from_kernel(e)),
        }
    };
}

macro_rules! shadow_commit {
    ($inner:expr, $call:expr) => {
        match $call {
            Ok((ns, action)) => {
                $inner.state = ns;
                $inner.seq += 1;
                InstanceOutcome::Ok($inner.seq, ActionN::from_kernel(action))
            }
            Err(e) => InstanceOutcome::Error(KernelErrorN::from_kernel(e)),
        }
    };
}

// Transitions with no explain machinery: candidate verdict from the pure transition under
// the candidate background on a discarded clone of the pre-entry state; report always nil.
macro_rules! shadow_apply {
    ($handle:expr, $s:ident, $bg:ident => $call:expr) => {{
        let mut inner = $handle.inner.lock().unwrap();
        let pre = inner.state.clone();
        let candidate = {
            let $s = pre.clone();
            let $bg = &$handle.candidate_bg;
            shadow_verdict!($call)
        };
        let live = {
            let $s = pre;
            let $bg = &$handle.live_bg;
            shadow_commit!(inner, $call)
        };
        ShadowOutcome { live, candidate, report: None }
    }};
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_new(live_bg: BackgroundN, candidate_bg: BackgroundN) -> ResourceArc<ShadowInstance> {
    ResourceArc::new(ShadowInstance {
        inner: std::sync::Mutex::new(InstanceInner {
            state: KernelState::initial(),
            seq: 0,
        }),
        live_bg: live_bg.into_kernel(),
        candidate_bg: candidate_bg.into_kernel(),
    })
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_state(handle: ResourceArc<ShadowInstance>) -> StateN {
    let inner = handle.inner.lock().unwrap();
    StateN::from_kernel(&inner.state)
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_seq(handle: ResourceArc<ShadowInstance>) -> u64 {
    handle.inner.lock().unwrap().seq
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_register_tool(handle: ResourceArc<ShadowInstance>, tool: String) -> ShadowOutcome {
    shadow_apply!(handle, s, bg => transitions::register_tool(s, bg, ToolId(tool.clone())))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_unregister_tool(handle: ResourceArc<ShadowInstance>, tool: String) -> ShadowOutcome {
    shadow_apply!(handle, s, bg => transitions::unregister_tool(s, bg, ToolId(tool.clone())))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_load_instruction(
    handle: ResourceArc<ShadowInstance>,
    agent: String,
    instr: String,
) -> ShadowOutcome {
    shadow_apply!(handle, s, bg =>
        transitions::load_instruction(s, bg, AgentId(agent.clone()), InstructionId(instr.clone())))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_delegate(
    handle: ResourceArc<ShadowInstance>,
    grantor: String,
    grantee: String,
) -> ShadowOutcome {
    shadow_apply!(handle, s, bg =>
        transitions::delegate(s, bg, AgentId(grantor.clone()), AgentId(grantee.clone())))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_grant_capability(
    handle: ResourceArc<ShadowInstance>,
    parent: String,
    child: String,
    cap: CapKindN,
) -> ShadowOutcome {
    shadow_apply!(handle, s, bg =>
        transitions::grant_capability(s, bg, AgentId(parent.clone()), AgentId(child.clone()), cap.into_kernel()))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_revoke(
    handle: ResourceArc<ShadowInstance>,
    parent: String,
    target: String,
) -> ShadowOutcome {
    shadow_apply!(handle, s, bg =>
        transitions::revoke(s, bg, AgentId(parent.clone()), AgentId(target.clone())))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_cascade_revoke(
    handle: ResourceArc<ShadowInstance>,
    child: String,
    parent: String,
) -> ShadowOutcome {
    shadow_apply!(handle, s, bg =>
        transitions::cascade_revoke(s, bg, AgentId(child.clone()), AgentId(parent.clone())))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_sentinel_credit_budget(
    handle: ResourceArc<ShadowInstance>,
    agent: String,
    amount: u8,
) -> ShadowOutcome {
    shadow_apply!(handle, s, bg =>
        transitions::sentinel_credit_budget(s, bg, AgentId(agent.clone()), amount))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_invoke_complete(
    handle: ResourceArc<ShadowInstance>,
    agent: String,
    inv: String,
    conformance_conforms: bool,
) -> ShadowOutcome {
    shadow_apply!(handle, s, bg => transitions::invoke_complete(
        s,
        bg,
        &ConstConformance(conformance_conforms),
        AgentId(agent.clone()),
        InvocationId(inv.clone())
    ))
}

#[allow(clippy::too_many_arguments)]
#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_invoke_start(
    handle: ResourceArc<ShadowInstance>,
    agent: String,
    tool: String,
    inv: String,
    authorizer_allows: bool,
    content_gate: HashMap<String, bool>,
    attested_egress: Vec<EgressKindN>,
) -> ShadowOutcome {
    let attested = attested_into_kernel(attested_egress);
    let mut inner = handle.inner.lock().unwrap();
    let pre = inner.state.clone();
    let candidate = shadow_verdict!(transitions::invoke_start(
        pre.clone(),
        &handle.candidate_bg,
        &ConstAuthorizer(authorizer_allows),
        &MapContentGate(content_gate.clone()),
        AgentId(agent.clone()),
        ToolId(tool.clone()),
        InvocationId(inv.clone()),
        attested.clone()
    ));
    let live = shadow_commit!(inner, transitions::invoke_start(
        pre.clone(),
        &handle.live_bg,
        &ConstAuthorizer(authorizer_allows),
        &MapContentGate(content_gate.clone()),
        AgentId(agent.clone()),
        ToolId(tool.clone()),
        InvocationId(inv.clone()),
        attested.clone()
    ));
    let report = if diverged(&live, &candidate) {
        Some(ExplainReportN::from_explain(argus_explain::explain_invoke(
            &pre,
            &handle.candidate_bg,
            &ConstAuthorizer(authorizer_allows),
            &MapContentGate(content_gate),
            &AgentId(agent),
            &ToolId(tool),
            &InvocationId(inv),
            &attested,
        )))
    } else {
        None
    };
    ShadowOutcome { live, candidate, report }
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_return_unendorsed(
    handle: ResourceArc<ShadowInstance>,
    child: String,
    parent: String,
    content_gate: HashMap<String, bool>,
) -> ShadowOutcome {
    let mut inner = handle.inner.lock().unwrap();
    let pre = inner.state.clone();
    let candidate = shadow_verdict!(transitions::return_unendorsed(
        pre.clone(),
        &handle.candidate_bg,
        &MapContentGate(content_gate.clone()),
        AgentId(child.clone()),
        AgentId(parent.clone())
    ));
    let live = shadow_commit!(inner, transitions::return_unendorsed(
        pre.clone(),
        &handle.live_bg,
        &MapContentGate(content_gate.clone()),
        AgentId(child.clone()),
        AgentId(parent.clone())
    ));
    let report = if diverged(&live, &candidate) {
        Some(ExplainReportN::from_explain(
            argus_explain::explain_return_unendorsed(
                &pre,
                &handle.candidate_bg,
                &MapContentGate(content_gate),
                &AgentId(child),
                &AgentId(parent),
            ),
        ))
    } else {
        None
    };
    ShadowOutcome { live, candidate, report }
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_sentinel_elevate_taint(
    handle: ResourceArc<ShadowInstance>,
    agent: String,
    level: ConfLevelN,
    content_gate: HashMap<String, bool>,
) -> ShadowOutcome {
    let mut inner = handle.inner.lock().unwrap();
    let pre = inner.state.clone();
    let candidate = shadow_verdict!(transitions::sentinel_elevate_taint(
        pre.clone(),
        &handle.candidate_bg,
        &MapContentGate(content_gate.clone()),
        AgentId(agent.clone()),
        level.into_kernel()
    ));
    let live = shadow_commit!(inner, transitions::sentinel_elevate_taint(
        pre.clone(),
        &handle.live_bg,
        &MapContentGate(content_gate.clone()),
        AgentId(agent.clone()),
        level.into_kernel()
    ));
    let report = if diverged(&live, &candidate) {
        Some(ExplainReportN::from_explain(
            argus_explain::explain_sentinel_elevate_taint(
                &pre,
                &handle.candidate_bg,
                &MapContentGate(content_gate),
                &AgentId(agent),
                level.into_kernel(),
            ),
        ))
    } else {
        None
    };
    ShadowOutcome { live, candidate, report }
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_sentinel_degrade_integrity(
    handle: ResourceArc<ShadowInstance>,
    agent: String,
    level: IntegLevelN,
    content_gate: HashMap<String, bool>,
) -> ShadowOutcome {
    let mut inner = handle.inner.lock().unwrap();
    let pre = inner.state.clone();
    let candidate = shadow_verdict!(transitions::sentinel_degrade_integrity(
        pre.clone(),
        &handle.candidate_bg,
        &MapContentGate(content_gate.clone()),
        AgentId(agent.clone()),
        level.into_kernel()
    ));
    let live = shadow_commit!(inner, transitions::sentinel_degrade_integrity(
        pre.clone(),
        &handle.live_bg,
        &MapContentGate(content_gate.clone()),
        AgentId(agent.clone()),
        level.into_kernel()
    ));
    let report = if diverged(&live, &candidate) {
        Some(ExplainReportN::from_explain(
            argus_explain::explain_sentinel_degrade_integrity(
                &pre,
                &handle.candidate_bg,
                &MapContentGate(content_gate),
                &AgentId(agent),
                level.into_kernel(),
            ),
        ))
    } else {
        None
    };
    ShadowOutcome { live, candidate, report }
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_return_endorsed(
    handle: ResourceArc<ShadowInstance>,
    child: String,
    parent: String,
    return_conforms: bool,
    clvl: ConfLevelN,
    ilvl: IntegLevelN,
) -> ShadowOutcome {
    let mut inner = handle.inner.lock().unwrap();
    let pre = inner.state.clone();
    let candidate = shadow_verdict!(transitions::return_endorsed(
        pre.clone(),
        &handle.candidate_bg,
        &ConstConformance(return_conforms),
        AgentId(child.clone()),
        AgentId(parent.clone()),
        clvl.into_kernel(),
        ilvl.into_kernel()
    ));
    let live = shadow_commit!(inner, transitions::return_endorsed(
        pre.clone(),
        &handle.live_bg,
        &ConstConformance(return_conforms),
        AgentId(child.clone()),
        AgentId(parent.clone()),
        clvl.into_kernel(),
        ilvl.into_kernel()
    ));
    let report = if diverged(&live, &candidate) {
        Some(ExplainReportN::from_explain(
            argus_explain::explain_return_endorsed(
                &pre,
                &handle.candidate_bg,
                &ConstConformance(return_conforms),
                &AgentId(child),
                &AgentId(parent),
                clvl.into_kernel(),
                ilvl.into_kernel(),
            ),
        ))
    } else {
        None
    };
    ShadowOutcome { live, candidate, report }
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn shadow_grant_override(
    handle: ResourceArc<ShadowInstance>,
    granter: String,
    target: String,
    tool: String,
    level: ConfLevelN,
) -> ShadowOutcome {
    let mut inner = handle.inner.lock().unwrap();
    let pre = inner.state.clone();
    let candidate = shadow_verdict!(transitions::grant_override(
        pre.clone(),
        &handle.candidate_bg,
        AgentId(granter.clone()),
        AgentId(target.clone()),
        ToolId(tool.clone()),
        level.into_kernel()
    ));
    let live = shadow_commit!(inner, transitions::grant_override(
        pre.clone(),
        &handle.live_bg,
        AgentId(granter.clone()),
        AgentId(target.clone()),
        ToolId(tool),
        level.into_kernel()
    ));
    let report = if diverged(&live, &candidate) {
        Some(ExplainReportN::from_explain(
            argus_explain::explain_grant_override(
                &pre,
                &handle.candidate_bg,
                &AgentId(granter),
                &AgentId(target),
                level.into_kernel(),
            ),
        ))
    } else {
        None
    };
    ShadowOutcome { live, candidate, report }
}
