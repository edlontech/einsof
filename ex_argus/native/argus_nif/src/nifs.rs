use std::collections::HashMap;

use argus_kernel::{transitions, AgentId, InstructionId, InvocationId, KernelState, ToolId};

use crate::enums::{CapKindN, ConfLevelN};
use crate::event::{ActionN, KernelErrorN, Outcome};
use crate::oracles::{ConstAuthorizer, ConstConformance, MapContentGate};
use crate::state::{BackgroundN, StateN};

macro_rules! finish {
    ($result:expr) => {
        match $result {
            Ok((ns, action)) => Outcome::Ok(StateN::from_kernel(&ns), ActionN::from_kernel(action)),
            Err(e) => Outcome::Error(KernelErrorN::from_kernel(e)),
        }
    };
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn initial_state() -> StateN {
    StateN::from_kernel(&KernelState::initial())
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn register_tool(state: StateN, bg: BackgroundN, tool: String) -> Outcome {
    finish!(transitions::register_tool(
        state.into_kernel(),
        &bg.into_kernel(),
        ToolId(tool)
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn load_instruction(state: StateN, bg: BackgroundN, agent: String, instr: String) -> Outcome {
    finish!(transitions::load_instruction(
        state.into_kernel(),
        &bg.into_kernel(),
        AgentId(agent),
        InstructionId(instr)
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn delegate(state: StateN, bg: BackgroundN, grantor: String, grantee: String) -> Outcome {
    finish!(transitions::delegate(
        state.into_kernel(),
        &bg.into_kernel(),
        AgentId(grantor),
        AgentId(grantee)
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn grant_capability(
    state: StateN,
    bg: BackgroundN,
    parent: String,
    child: String,
    cap: CapKindN,
) -> Outcome {
    finish!(transitions::grant_capability(
        state.into_kernel(),
        &bg.into_kernel(),
        AgentId(parent),
        AgentId(child),
        cap.into_kernel()
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn revoke(state: StateN, bg: BackgroundN, parent: String, target: String) -> Outcome {
    finish!(transitions::revoke(
        state.into_kernel(),
        &bg.into_kernel(),
        AgentId(parent),
        AgentId(target)
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn cascade_revoke(state: StateN, bg: BackgroundN, child: String, parent: String) -> Outcome {
    finish!(transitions::cascade_revoke(
        state.into_kernel(),
        &bg.into_kernel(),
        AgentId(child),
        AgentId(parent)
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn return_endorsed(
    state: StateN,
    bg: BackgroundN,
    child: String,
    parent: String,
    return_conforms: bool,
) -> Outcome {
    finish!(transitions::return_endorsed(
        state.into_kernel(),
        &bg.into_kernel(),
        &ConstConformance(return_conforms),
        AgentId(child),
        AgentId(parent)
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn sentinel_credit_budget(
    state: StateN,
    bg: BackgroundN,
    agent: String,
    amount: u8,
) -> Outcome {
    finish!(transitions::sentinel_credit_budget(
        state.into_kernel(),
        &bg.into_kernel(),
        AgentId(agent),
        amount
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn grant_override(
    state: StateN,
    bg: BackgroundN,
    granter: String,
    target: String,
    tool: String,
    level: ConfLevelN,
) -> Outcome {
    finish!(transitions::grant_override(
        state.into_kernel(),
        &bg.into_kernel(),
        AgentId(granter),
        AgentId(target),
        ToolId(tool),
        level.into_kernel()
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn invoke_start(
    state: StateN,
    bg: BackgroundN,
    agent: String,
    tool: String,
    inv: String,
    authorizer_allows: bool,
    content_gate: HashMap<String, bool>,
) -> Outcome {
    finish!(transitions::invoke_start(
        state.into_kernel(),
        &bg.into_kernel(),
        &ConstAuthorizer(authorizer_allows),
        &MapContentGate(content_gate),
        AgentId(agent),
        ToolId(tool),
        InvocationId(inv)
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn invoke_complete(
    state: StateN,
    bg: BackgroundN,
    agent: String,
    inv: String,
    conformance_conforms: bool,
) -> Outcome {
    finish!(transitions::invoke_complete(
        state.into_kernel(),
        &bg.into_kernel(),
        &ConstConformance(conformance_conforms),
        AgentId(agent),
        InvocationId(inv)
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn return_unendorsed(
    state: StateN,
    bg: BackgroundN,
    child: String,
    parent: String,
    content_gate: HashMap<String, bool>,
) -> Outcome {
    finish!(transitions::return_unendorsed(
        state.into_kernel(),
        &bg.into_kernel(),
        &MapContentGate(content_gate),
        AgentId(child),
        AgentId(parent)
    ))
}

#[rustler::nif(schedule = "DirtyCpu")]
pub fn sentinel_elevate_taint(
    state: StateN,
    bg: BackgroundN,
    agent: String,
    level: ConfLevelN,
    content_gate: HashMap<String, bool>,
) -> Outcome {
    finish!(transitions::sentinel_elevate_taint(
        state.into_kernel(),
        &bg.into_kernel(),
        &MapContentGate(content_gate),
        AgentId(agent),
        level.into_kernel()
    ))
}
