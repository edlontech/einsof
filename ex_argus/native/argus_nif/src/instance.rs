use std::collections::HashMap;
use std::sync::Mutex;

use argus_kernel::{transitions, AgentId, InstructionId, InvocationId, KernelState, ToolId};
use rustler::{Resource, ResourceArc};

use crate::enums::{CapKindN, ConfLevelN};
use crate::event::{ActionN, InstanceOutcome, KernelErrorN};
use crate::oracles::{ConstAuthorizer, ConstConformance, MapContentGate};
use crate::state::{BackgroundN, StateN};

pub struct InstanceInner {
    pub state: KernelState,
    pub seq: u64,
}

pub struct KernelInstance {
    pub inner: Mutex<InstanceInner>,
    pub bg: argus_kernel::BackgroundTheory,
}

#[rustler::resource_impl]
impl Resource for KernelInstance {}

// Lock, clone the live state (the pure transition consumes it and drops it on Err), run,
// commit + bump seq on Ok, leave state untouched on Err.
macro_rules! instance_finish {
    ($handle:expr, $state:ident => $call:expr) => {{
        let mut inner = $handle.inner.lock().unwrap();
        let $state = inner.state.clone();
        match $call {
            Ok((ns, action)) => {
                inner.state = ns;
                inner.seq += 1;
                InstanceOutcome::Ok(inner.seq, ActionN::from_kernel(action))
            }
            Err(e) => InstanceOutcome::Error(KernelErrorN::from_kernel(e)),
        }
    }};
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_new(bg: BackgroundN) -> ResourceArc<KernelInstance> {
    ResourceArc::new(KernelInstance {
        inner: Mutex::new(InstanceInner {
            state: KernelState::initial(),
            seq: 0,
        }),
        bg: bg.into_kernel(),
    })
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_state(handle: ResourceArc<KernelInstance>) -> StateN {
    let inner = handle.inner.lock().unwrap();
    StateN::from_kernel(&inner.state)
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_seq(handle: ResourceArc<KernelInstance>) -> u64 {
    handle.inner.lock().unwrap().seq
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_register_tool(
    handle: ResourceArc<KernelInstance>,
    tool: String,
) -> InstanceOutcome {
    instance_finish!(handle, s => transitions::register_tool(s, &handle.bg, ToolId(tool)))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_load_instruction(
    handle: ResourceArc<KernelInstance>,
    agent: String,
    instr: String,
) -> InstanceOutcome {
    instance_finish!(handle, s =>
        transitions::load_instruction(s, &handle.bg, AgentId(agent), InstructionId(instr)))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_delegate(
    handle: ResourceArc<KernelInstance>,
    grantor: String,
    grantee: String,
) -> InstanceOutcome {
    instance_finish!(handle, s =>
        transitions::delegate(s, &handle.bg, AgentId(grantor), AgentId(grantee)))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_grant_capability(
    handle: ResourceArc<KernelInstance>,
    parent: String,
    child: String,
    cap: CapKindN,
) -> InstanceOutcome {
    instance_finish!(handle, s =>
        transitions::grant_capability(s, &handle.bg, AgentId(parent), AgentId(child), cap.into_kernel()))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_revoke(
    handle: ResourceArc<KernelInstance>,
    parent: String,
    target: String,
) -> InstanceOutcome {
    instance_finish!(handle, s =>
        transitions::revoke(s, &handle.bg, AgentId(parent), AgentId(target)))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_cascade_revoke(
    handle: ResourceArc<KernelInstance>,
    child: String,
    parent: String,
) -> InstanceOutcome {
    instance_finish!(handle, s =>
        transitions::cascade_revoke(s, &handle.bg, AgentId(child), AgentId(parent)))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_return_endorsed(
    handle: ResourceArc<KernelInstance>,
    child: String,
    parent: String,
    return_conforms: bool,
) -> InstanceOutcome {
    instance_finish!(handle, s =>
        transitions::return_endorsed(s, &handle.bg, &ConstConformance(return_conforms), AgentId(child), AgentId(parent)))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_sentinel_credit_budget(
    handle: ResourceArc<KernelInstance>,
    agent: String,
    amount: u8,
) -> InstanceOutcome {
    instance_finish!(handle, s =>
        transitions::sentinel_credit_budget(s, &handle.bg, AgentId(agent), amount))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_grant_override(
    handle: ResourceArc<KernelInstance>,
    granter: String,
    target: String,
    tool: String,
    level: ConfLevelN,
) -> InstanceOutcome {
    instance_finish!(handle, s =>
        transitions::grant_override(
            s,
            &handle.bg,
            AgentId(granter),
            AgentId(target),
            ToolId(tool),
            level.into_kernel()
        ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_invoke_start(
    handle: ResourceArc<KernelInstance>,
    agent: String,
    tool: String,
    inv: String,
    authorizer_allows: bool,
    content_gate: HashMap<String, bool>,
) -> InstanceOutcome {
    instance_finish!(handle, s => transitions::invoke_start(
        s,
        &handle.bg,
        &ConstAuthorizer(authorizer_allows),
        &MapContentGate(content_gate),
        AgentId(agent),
        ToolId(tool),
        InvocationId(inv)
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_invoke_complete(
    handle: ResourceArc<KernelInstance>,
    agent: String,
    inv: String,
    conformance_conforms: bool,
) -> InstanceOutcome {
    instance_finish!(handle, s => transitions::invoke_complete(
        s,
        &handle.bg,
        &ConstConformance(conformance_conforms),
        AgentId(agent),
        InvocationId(inv)
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_return_unendorsed(
    handle: ResourceArc<KernelInstance>,
    child: String,
    parent: String,
    content_gate: HashMap<String, bool>,
) -> InstanceOutcome {
    instance_finish!(handle, s => transitions::return_unendorsed(
        s,
        &handle.bg,
        &MapContentGate(content_gate),
        AgentId(child),
        AgentId(parent)
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn instance_sentinel_elevate_taint(
    handle: ResourceArc<KernelInstance>,
    agent: String,
    level: ConfLevelN,
    content_gate: HashMap<String, bool>,
) -> InstanceOutcome {
    instance_finish!(handle, s => transitions::sentinel_elevate_taint(
        s,
        &handle.bg,
        &MapContentGate(content_gate),
        AgentId(agent),
        level.into_kernel()
    ))
}
