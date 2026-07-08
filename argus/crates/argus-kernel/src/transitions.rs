use crate::background::{BackgroundTheory, FlowMode};
use crate::capability::CapKind;
use crate::collections::{VecMap, VecSet};
use crate::error::KernelError;
use crate::event::KernelAction;
use crate::state::KernelState;
use crate::traits::{AuthorizerOracle, ConformanceOracle, ContentGateOracle};
use crate::types::{
    AgentId, ConfLevel, EgressKind, InstructionId, InvocationId, OverrideKey, ToolId,
    declass_weight,
};

/// Outcome of a flow-gate check at a consuming site (`invoke_start` / `return_unendorsed` /
/// `sentinel_elevate_taint`). Distinguishes a flow permitted outright (ALLOW, or INSPECT with a
/// passing content gate) from one rescued *only* by a single-use override -- the latter must be
/// spent (MF-3). Mirrors the Veil "only when necessary" rule: an override is consumed iff the
/// `(level, egress)` pair is DENY-mode and a not-yet-used grant exists. All three
/// flow-introducing actions consume uniformly, which is what makes single-use a proved property
/// (`override_consumed_when_sole_justification`).
enum FlowDecision {
    Allowed,
    ConsumedOverride,
    Denied,
}

fn flow_decision(
    bg: &BackgroundTheory,
    content_gate: &impl ContentGateOracle,
    agent: &AgentId,
    tool: &ToolId,
    st: &KernelState,
    level: ConfLevel,
    egress: EgressKind,
) -> FlowDecision {
    match bg.flow_mode(level, egress) {
        FlowMode::Allow => FlowDecision::Allowed,
        FlowMode::Inspect => {
            if content_gate.passes(agent, tool, st, bg) {
                FlowDecision::Allowed
            } else {
                FlowDecision::Denied
            }
        }
        FlowMode::Deny => {
            if st.has_flow_override(agent, tool, level)
                && !st.override_consumed(agent, tool, level)
            {
                FlowDecision::ConsumedOverride
            } else {
                FlowDecision::Denied
            }
        }
    }
}

fn clear_agent_state(st: &mut KernelState, agent: &AgentId) {
    st.taint_levels.remove(agent);
    st.integ_levels.remove(agent);
    st.in_flight.remove(agent);
    st.agent_instruction.remove(agent);
    st.override_used.remove(agent);
    st.flow_override.remove(agent);
}

/// Drop every `agent_parent` edge that touches `dropped` on either endpoint (the stale-edge
/// cleanup `delegate` did via `BTreeMap::retain`). Transparent index loop over the `VecMap`
/// (no early return, no iterator adapters) -- the Aeneas-extractable idiom.
fn agent_parent_drop_endpoint(
    map: &VecMap<AgentId, AgentId>,
    dropped: &AgentId,
) -> VecMap<AgentId, AgentId> {
    let mut kept = VecMap::new();
    let mut i = 0;
    while i < map.len() {
        let child = map.key_at(i);
        let parent = map.val_at(i);
        if child != dropped && parent != dropped {
            kept.insert(child.clone(), parent.clone());
        }
        i += 1;
    }
    kept
}

/// Drop every `agent_parent` edge whose CHILD is `dropped` (the cleanup `revoke` /
/// `cascade_revoke` did via `BTreeMap::retain`). Transparent index loop -- see
/// `agent_parent_drop_endpoint`.
fn agent_parent_drop_child(
    map: &VecMap<AgentId, AgentId>,
    dropped: &AgentId,
) -> VecMap<AgentId, AgentId> {
    let mut kept = VecMap::new();
    let mut i = 0;
    while i < map.len() {
        let child = map.key_at(i);
        if child != dropped {
            kept.insert(child.clone(), map.val_at(i).clone());
        }
        i += 1;
    }
    kept
}

/// Accumulator threaded through the flow-gate loops. `denied` is monotone (set on any DENY);
/// `to_consume` collects the single-use overrides spent on the accepted flows. No early `return`
/// inside the loops -- callers inspect `denied` after the fold. This (plus index loops) is the
/// shape Aeneas extracts transparently; the previous early-return-in-loop form forced an axiom.
struct GateAccum {
    denied: bool,
    to_consume: VecSet<OverrideKey>,
}

/// Fold `flow_decision` over a tool's egress kinds at `level`, updating the accumulator. Shared
/// innermost gate; the per-transition in-flight / taint loops call it and thread `acc`.
fn gate_egress<C: ContentGateOracle>(
    bg: &BackgroundTheory,
    content_gate: &C,
    agent: &AgentId,
    tool: &ToolId,
    st: &KernelState,
    level: ConfLevel,
    egress_set: &VecSet<EgressKind>,
    mut acc: GateAccum,
) -> GateAccum {
    let mut i = 0;
    while i < egress_set.len() {
        let egress = *egress_set.at(i);
        match flow_decision(bg, content_gate, agent, tool, st, level, egress) {
            FlowDecision::Allowed => {}
            FlowDecision::ConsumedOverride => {
                acc.to_consume.insert(OverrideKey { tool: tool.clone(), level });
            }
            FlowDecision::Denied => {
                acc.denied = true;
            }
        }
        i += 1;
    }
    acc
}

pub fn register_tool(
    mut st: KernelState,
    bg: &BackgroundTheory,
    tool: ToolId,
) -> Result<(KernelState, KernelAction), KernelError> {
    let issuer = match bg.tool_metadata(&tool) {
        Some(tmeta) => tmeta.issuer.clone(),
        None => return Err(KernelError::ToolNotInTheory),
    };
    if !bg.is_trusted_issuer(&issuer) {
        return Err(KernelError::UntrustedIssuer);
    }
    if st.tool_registered.contains(&tool) {
        return Err(KernelError::ToolAlreadyRegistered);
    }

    st.tool_registered.insert(tool.clone());

    Ok((st, KernelAction::RegisterTool { tool }))
}

pub fn load_instruction(
    mut st: KernelState,
    bg: &BackgroundTheory,
    agent: AgentId,
    instr: InstructionId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !st.agent_active.contains(&agent) {
        return Err(KernelError::AgentInactive);
    }
    let issuer = match bg.instruction_issuer(&instr) {
        Some(issuer) => issuer.clone(),
        None => return Err(KernelError::InstructionIssuerUnknown),
    };
    if !bg.is_trusted_issuer(&issuer) {
        return Err(KernelError::UntrustedIssuer);
    }

    st.agent_instruction.insert_into(agent.clone(), instr.clone());

    Ok((st, KernelAction::LoadInstruction { agent, instr }))
}

pub fn delegate(
    mut st: KernelState,
    _bg: &BackgroundTheory,
    grantor: AgentId,
    grantee: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !st.agent_active.contains(&grantor) {
        return Err(KernelError::AgentInactive);
    }
    if st.agent_active.contains(&grantee) {
        return Err(KernelError::AgentAlreadyActive);
    }
    if grantee == AgentId::root() {
        return Err(KernelError::RootNotAllowed);
    }

    st.agent_active.insert(grantee.clone());
    st.agent_parent = agent_parent_drop_endpoint(&st.agent_parent, &grantee);
    st.agent_parent.insert(grantee.clone(), grantor.clone());
    st.agent_cap.insert(grantee.clone(), VecSet::new());
    clear_agent_state(&mut st, &grantee);
    st.agent_budget.insert(grantee.clone(), 0);

    Ok((st, KernelAction::Delegate { grantor, grantee }))
}

pub fn grant_capability(
    mut st: KernelState,
    _bg: &BackgroundTheory,
    parent: AgentId,
    child: AgentId,
    cap: CapKind,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !st.agent_active.contains(&parent) {
        return Err(KernelError::AgentInactive);
    }
    if !st.agent_active.contains(&child) {
        return Err(KernelError::AgentInactive);
    }
    if st.agent_parent.get(&child) != Some(&parent) {
        return Err(KernelError::NotDirectChild);
    }
    if !st.agent_cap.set_contains(&parent, &cap) {
        return Err(KernelError::CapabilityMissing);
    }

    st.agent_cap.insert_into(child.clone(), cap);

    Ok((st, KernelAction::GrantCapability { parent, child, cap }))
}

pub fn revoke(
    mut st: KernelState,
    _bg: &BackgroundTheory,
    parent: AgentId,
    target: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if st.agent_parent.get(&target) != Some(&parent) {
        return Err(KernelError::NotDirectChild);
    }
    if !st.agent_active.contains(&parent) {
        return Err(KernelError::AgentInactive);
    }
    if !st.agent_active.contains(&target) {
        return Err(KernelError::AgentInactive);
    }
    if target == AgentId::root() {
        return Err(KernelError::RootNotAllowed);
    }

    st.agent_active.remove(&target);
    st.agent_parent = agent_parent_drop_child(&st.agent_parent, &target);
    st.agent_cap.remove(&target);
    clear_agent_state(&mut st, &target);

    Ok((st, KernelAction::Revoke { parent, target }))
}

pub fn cascade_revoke(
    mut st: KernelState,
    _bg: &BackgroundTheory,
    child: AgentId,
    parent: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if st.agent_parent.get(&child) != Some(&parent) {
        return Err(KernelError::NotDirectChild);
    }
    if st.agent_active.contains(&parent) {
        return Err(KernelError::ParentStillActive);
    }
    if !st.agent_active.contains(&child) {
        return Err(KernelError::AgentInactive);
    }
    if child == AgentId::root() {
        return Err(KernelError::RootNotAllowed);
    }

    st.agent_active.remove(&child);
    st.agent_parent = agent_parent_drop_child(&st.agent_parent, &child);
    st.agent_cap.remove(&child);
    clear_agent_state(&mut st, &child);

    Ok((st, KernelAction::CascadeRevoke { child, parent }))
}

pub fn invoke_start<A: AuthorizerOracle, C: ContentGateOracle>(
    mut st: KernelState,
    bg: &BackgroundTheory,
    authorizer: &A,
    content_gate: &C,
    agent: AgentId,
    tool: ToolId,
    inv: InvocationId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !st.agent_active.contains(&agent) {
        return Err(KernelError::AgentInactive);
    }
    if agent == AgentId::root() {
        return Err(KernelError::RootNotAllowed);
    }
    if !st.tool_registered.contains(&tool) {
        return Err(KernelError::ToolNotRegistered);
    }
    if st.invocation_tool.contains_key(&inv) {
        return Err(KernelError::InvocationExists);
    }
    if st.in_flight.any_value_contains(&inv) {
        return Err(KernelError::InvocationInFlight);
    }

    // Clone the tool's metadata to an owned local: holding the `bg` borrow while it is read across
    // the gate loops and used to clone egress sets keeps the extractor's region analysis happy.
    let tool_meta = match bg.tool_metadata(&tool) {
        Some(m) => m,
        None => return Err(KernelError::ToolNotInTheory),
    };
    let conf_floor = tool_meta.conf_floor;

    let mut missing_cap = false;
    let mut ci = 0;
    while ci < tool_meta.capabilities.len() {
        let required_cap = tool_meta.capabilities.at(ci);
        if !st.agent_cap.set_contains(&agent, required_cap) {
            missing_cap = true;
        }
        ci += 1;
    }
    if missing_cap {
        return Err(KernelError::CapabilityMissing);
    }

    // Override grants that are the *sole* justification for a flow this transition; spent on
    // success (single-use, MF-3). Folded with no early return (the extractable shape); `denied`
    // is checked once after all three checks.
    let mut acc = GateAccum { denied: false, to_consume: VecSet::new() };

    // CHECK 2a: the new tool's egress against every speculative-taint level the agent carries.
    let spec_taint = st.speculative_taint(&agent, bg);
    let mut li = 0;
    while li < spec_taint.len() {
        let level = *spec_taint.at(li);
        acc = gate_egress(bg, content_gate, &agent, &tool, &st, level, &tool_meta.egress, acc);
        li += 1;
    }

    // CHECK 2b/2c run for ALL tools -- bounded is NOT excluded. With conformance-gating a bounded
    // tool may still add taint on completion (if it fails conformance), so its floor must be
    // flow-compatible just like a non-bounded tool (worst-case / fail-closed).
    let agent_flights = st.in_flight.get_set_or_empty(&agent);
    let mut fi = 0;
    while fi < agent_flights.len() {
        let flight_inv = agent_flights.at(fi);
        if let Some(flight_tool_id) = st.invocation_tool.get_cloned(flight_inv) {
            let flight_egress = match bg.tool_metadata(&flight_tool_id) {
                Some(m) => m.egress.clone(),
                None => VecSet::new(),
            };
            acc = gate_egress(
                bg,
                content_gate,
                &agent,
                &flight_tool_id,
                &st,
                conf_floor,
                &flight_egress,
                acc,
            );
        }
        fi += 1;
    }

    // CHECK: the new tool's own egress at its floor.
    acc = gate_egress(bg, content_gate, &agent, &tool, &st, conf_floor, &tool_meta.egress, acc);

    if acc.denied {
        return Err(KernelError::FlowGateBlocked);
    }

    if !authorizer.allows(&agent, &tool, &st, bg) {
        return Err(KernelError::AuthorizerDenied);
    }

    if !acc.to_consume.is_empty() {
        st.override_used.extend_into(agent.clone(), &acc.to_consume);
    }

    st.invocation_tool.insert(inv.clone(), tool.clone());
    st.in_flight.insert_into(agent.clone(), inv.clone());

    Ok((st, KernelAction::InvokeStart { agent, tool, inv }))
}

pub fn invoke_complete<F: ConformanceOracle>(
    mut st: KernelState,
    bg: &BackgroundTheory,
    conformance: &F,
    agent: AgentId,
    inv: InvocationId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !st.in_flight.set_contains(&agent, &inv) {
        return Err(KernelError::NotInFlight);
    }
    if !st.agent_active.contains(&agent) {
        return Err(KernelError::AgentInactive);
    }

    st.in_flight.remove_from(&agent, &inv);

    // Owned binding so the read of `invocation_tool` ends before the taint updates mutate `st`.
    if let Some(tool_id) = st.invocation_tool.get_cloned(&inv) {
        let meta_info = match bg.tool_metadata(&tool_id) {
            Some(tmeta) => Some((tmeta.conf_floor, tmeta.output_bounded)),
            None => None,
        };
        if let Some((conf_floor, output_bounded)) = meta_info {
            let weight = declass_weight(conf_floor);
            let already_tainted = st.taint_levels.set_contains(&agent, &conf_floor);
            // Zero-taint (endorsed) path: bounded + conforms + affordable AND the agent does not
            // already hold this floor (re-tainting buys nothing, so don't waste budget on it).
            let zero_taint = output_bounded
                && conformance.conforms(&agent, &tool_id, &st, bg)
                && st.affordable(&agent, weight)
                && !already_tainted;
            if zero_taint {
                st.debit_budget(&agent, weight);
            } else {
                st.taint_levels.insert_into(agent.clone(), conf_floor);
            }
        }
    }

    Ok((st, KernelAction::InvokeComplete { agent, inv }))
}

pub fn return_endorsed<F: ConformanceOracle>(
    mut st: KernelState,
    bg: &BackgroundTheory,
    conformance: &F,
    child: AgentId,
    parent: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if st.agent_parent.get(&child) != Some(&parent) {
        return Err(KernelError::NotDirectChild);
    }
    if !st.agent_active.contains(&child) {
        return Err(KernelError::AgentInactive);
    }
    if !st.agent_active.contains(&parent) {
        return Err(KernelError::AgentInactive);
    }
    if st.in_flight.set_nonempty(&child) {
        return Err(KernelError::ChildHasInFlight);
    }
    // Cross-boundary declassification tier: the child must be authorised to declassify, and the
    // RECIPIENT (parent) is charged budget -- a per-agent bound on the parent's total endorsed
    // inflow across its whole subtree (smurfing defense). A child lacking the cap, or an
    // out-of-budget parent, must use return_unendorsed (full taint) instead.
    if !st.agent_cap.set_contains(&child, &CapKind::Declassify) {
        return Err(KernelError::CapabilityMissing);
    }
    if !conformance.return_conforms(&child, &parent, &st, bg) {
        return Err(KernelError::NotConforming);
    }
    if !st.affordable(&parent, 2) {
        return Err(KernelError::BudgetExhausted);
    }
    st.debit_budget(&parent, 2);

    Ok((st, KernelAction::ReturnEndorsed { child, parent }))
}

pub fn return_unendorsed<C: ContentGateOracle>(
    mut st: KernelState,
    bg: &BackgroundTheory,
    content_gate: &C,
    child: AgentId,
    parent: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if st.agent_parent.get(&child) != Some(&parent) {
        return Err(KernelError::NotDirectChild);
    }
    if !st.agent_active.contains(&child) {
        return Err(KernelError::AgentInactive);
    }
    if !st.agent_active.contains(&parent) {
        return Err(KernelError::AgentInactive);
    }
    if st.in_flight.set_nonempty(&child) {
        return Err(KernelError::ChildHasInFlight);
    }

    let child_taint = st.taint_levels.get_set_or_empty(&child);

    // Override grants spent on success (single-use, MF-3), charged to the recipient `parent`.
    // Folded over child-taint levels x parent's in-flight tools with no early return.
    let mut acc = GateAccum { denied: false, to_consume: VecSet::new() };
    let parent_flights = st.in_flight.get_set_or_empty(&parent);
    let mut li = 0;
    while li < child_taint.len() {
        let level = *child_taint.at(li);
        let mut fi = 0;
        while fi < parent_flights.len() {
            let inv = parent_flights.at(fi);
            if let Some(tool_id) = st.invocation_tool.get_cloned(inv) {
                let egress = match bg.tool_metadata(&tool_id) {
                    Some(m) => m.egress.clone(),
                    None => VecSet::new(),
                };
                acc = gate_egress(bg, content_gate, &parent, &tool_id, &st, level, &egress, acc);
            }
            fi += 1;
        }
        li += 1;
    }
    if acc.denied {
        return Err(KernelError::FlowGateBlocked);
    }

    if !child_taint.is_empty() {
        st.taint_levels.extend_into(parent.clone(), &child_taint);
    }

    if !acc.to_consume.is_empty() {
        st.override_used.extend_into(parent.clone(), &acc.to_consume);
    }

    Ok((st, KernelAction::ReturnUnendorsed { child, parent }))
}

pub fn sentinel_elevate_taint<C: ContentGateOracle>(
    mut st: KernelState,
    bg: &BackgroundTheory,
    content_gate: &C,
    agent: AgentId,
    level: ConfLevel,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !st.agent_active.contains(&agent) {
        return Err(KernelError::AgentInactive);
    }

    // Override grants spent on success (single-use, MF-3) -- uniform with invoke_start /
    // return_unendorsed. Flow gate folded over the agent's in-flight tools x egress at the raised
    // `level`, with no early return; `missing_binding` / `denied` are checked once after the fold.
    let mut acc = GateAccum { denied: false, to_consume: VecSet::new() };
    let mut missing_binding = false;
    let in_flight_invs = st.in_flight.get_set_or_empty(&agent);
    let mut fi = 0;
    while fi < in_flight_invs.len() {
        let inv = in_flight_invs.at(fi);
        match st.invocation_tool.get_cloned(inv) {
            Some(tool) => {
                let egress = match bg.tool_metadata(&tool) {
                    Some(m) => m.egress.clone(),
                    None => VecSet::new(),
                };
                acc = gate_egress(bg, content_gate, &agent, &tool, &st, level, &egress, acc);
            }
            None => {
                missing_binding = true;
            }
        }
        fi += 1;
    }
    if missing_binding {
        return Err(KernelError::MissingToolBinding);
    }
    if acc.denied {
        return Err(KernelError::FlowGateBlocked);
    }

    if !acc.to_consume.is_empty() {
        st.override_used.extend_into(agent.clone(), &acc.to_consume);
    }

    st.taint_levels.insert_into(agent.clone(), level);

    Ok((st, KernelAction::SentinelElevateTaint { agent, level }))
}

/// Capability-gated granular budget credit (saturates at capacity). Full refresh =
/// credit `BUDGET_CAPACITY`. The rare, logged exception that keeps a long-running orchestrator
/// from dead-ending on an exhausted budget.
pub fn sentinel_credit_budget(
    mut st: KernelState,
    _bg: &BackgroundTheory,
    agent: AgentId,
    amount: u8,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !st.agent_active.contains(&agent) {
        return Err(KernelError::AgentInactive);
    }
    if !st.agent_cap.set_contains(&agent, &CapKind::CreditBudget) {
        return Err(KernelError::CapabilityMissing);
    }
    st.credit_budget(&agent, amount);

    Ok((st, KernelAction::SentinelCreditBudget { agent, amount }))
}

/// Capability-gated arming (or re-arming) of a single-use flow override for
/// `(target, tool, level)`, debited to the GRANTER's declassification budget. The re-arm
/// guard (target has no in-flight invocations) is what keeps single-use sound across
/// re-arms: no in-flight flow can be retroactively justified by the fresh grant.
/// Self-grant (granter == target) is legal; the guard then binds the granter.
pub fn grant_override(
    mut st: KernelState,
    _bg: &BackgroundTheory,
    granter: AgentId,
    target: AgentId,
    tool: ToolId,
    level: ConfLevel,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !st.agent_active.contains(&granter) {
        return Err(KernelError::AgentInactive);
    }
    if !st.agent_active.contains(&target) {
        return Err(KernelError::AgentInactive);
    }
    if !st.agent_cap.set_contains(&granter, &CapKind::GrantOverride) {
        return Err(KernelError::CapabilityMissing);
    }
    if !st.affordable(&granter, 1) {
        return Err(KernelError::BudgetExhausted);
    }
    if st.in_flight.set_nonempty(&target) {
        return Err(KernelError::TargetHasInFlight);
    }

    st.flow_override.insert_into(
        target.clone(),
        OverrideKey { tool: tool.clone(), level },
    );
    st.override_used.remove_from(
        &target,
        &OverrideKey { tool: tool.clone(), level },
    );
    st.debit_budget(&granter, 1);

    Ok((st, KernelAction::GrantOverride { granter, target, tool, level }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::background::{BackgroundTheoryBuilder, ToolMetadata};
    use crate::types::{BUDGET_CAPACITY, EgressKind, InstructionId, IntegLevel, IssuerId};

    struct AllowAll;
    impl AuthorizerOracle for AllowAll {
        fn allows(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
            true
        }
    }
    struct PassAll;
    impl ContentGateOracle for PassAll {
        fn passes(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
            true
        }
    }
    struct FailAll;
    impl ContentGateOracle for FailAll {
        fn passes(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
            false
        }
    }
    struct ConformsAll;
    impl ConformanceOracle for ConformsAll {
        fn conforms(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
            true
        }
        fn return_conforms(
            &self,
            _: &AgentId,
            _: &AgentId,
            _: &KernelState,
            _: &BackgroundTheory,
        ) -> bool {
            true
        }
    }
    struct ConformsNone;
    impl ConformanceOracle for ConformsNone {
        fn conforms(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
            false
        }
        fn return_conforms(
            &self,
            _: &AgentId,
            _: &AgentId,
            _: &KernelState,
            _: &BackgroundTheory,
        ) -> bool {
            false
        }
    }

    fn tool_meta_simple() -> ToolMetadata {
        ToolMetadata {
            capabilities: VecSet::new(),
            egress: VecSet::from([EgressKind::NetworkExternal]),
            conf_floor: ConfLevel::Public,
            output_bounded: false,
            issuer: IssuerId::new("trusted"),
            integ_floor: IntegLevel::Untrusted,
            integ_inspect_floor: IntegLevel::Untrusted,
            output_integ: IntegLevel::Attested,
        }
    }

    fn bg_with_tool(id: &str) -> BackgroundTheory {
        let mut b = BackgroundTheoryBuilder::new();
        b.trust_issuer(IssuerId::new("trusted"));
        b.register_tool(ToolId::new(id), tool_meta_simple());
        b.build()
    }

    fn bg_with_tools() -> BackgroundTheory {
        let mut b = BackgroundTheoryBuilder::new();
        b.trust_issuer(IssuerId::new("trusted"));
        b.register_tool(
            ToolId::new("read_file"),
            ToolMetadata {
                capabilities: VecSet::from([CapKind::FilesystemRead]),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Sensitive,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        b.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: VecSet::from([CapKind::NetworkEgress]),
                egress: VecSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        b.register_tool(
            ToolId::new("check_exists"),
            ToolMetadata {
                capabilities: VecSet::from([CapKind::FilesystemRead]),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Sensitive,
                output_bounded: true,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        b.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Public), None);
        b.build()
    }

    fn state_with_agent(id: &str, caps: &[CapKind]) -> KernelState {
        let mut st = KernelState::initial();
        let agent = AgentId::new(id);
        st.agent_active.insert(agent.clone());
        st.agent_parent.insert(agent.clone(), AgentId::root());
        st
            .agent_cap
            .insert(agent, caps.iter().copied().collect());
        st.tool_registered.insert(ToolId::new("read_file"));
        st.tool_registered.insert(ToolId::new("send_email"));
        st.tool_registered.insert(ToolId::new("check_exists"));
        st
    }

    // --- register_tool ---

    #[test]
    fn register_tool_success() {
        let st = KernelState::initial();
        let bg = bg_with_tool("read_file");
        let tool = ToolId::new("read_file");

        let (new_state, action) = register_tool(st, &bg, tool.clone()).unwrap();
        assert!(new_state.tool_registered.contains(&tool));
        assert_eq!(action, KernelAction::RegisterTool { tool });
    }

    #[test]
    fn register_tool_rejects_already_registered() {
        let mut st = KernelState::initial();
        let tool = ToolId::new("read_file");
        st.tool_registered.insert(tool.clone());
        let bg = bg_with_tool("read_file");
        assert!(register_tool(st, &bg, tool).is_err());
    }

    #[test]
    fn register_tool_rejects_unknown_tool() {
        let st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        assert!(register_tool(st, &bg, ToolId::new("unknown")).is_err());
    }

    // --- delegate ---

    #[test]
    fn delegate_success() {
        let st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let grantor = AgentId::root();
        let grantee = AgentId::new("child-1");

        let (new_state, action) = delegate(st, &bg, grantor.clone(), grantee.clone()).unwrap();
        assert!(new_state.agent_active.contains(&grantee));
        assert_eq!(new_state.agent_parent.get(&grantee), Some(&grantor));
        assert!(
            new_state
                .agent_cap
                .get(&grantee)
                .is_none_or(|s| s.is_empty())
        );
        assert!(new_state.taint_levels.get(&grantee).is_none());
        assert_eq!(action, KernelAction::Delegate { grantor, grantee });
    }

    #[test]
    fn delegate_rejects_inactive_grantor() {
        let st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        assert!(delegate(st, &bg, AgentId::new("ghost"), AgentId::new("child")).is_err());
    }

    #[test]
    fn delegate_rejects_already_active_grantee() {
        let st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        assert!(delegate(st, &bg, AgentId::root(), AgentId::root()).is_err());
    }

    #[test]
    fn delegate_clears_stale_grantee_parent_entries() {
        let mut st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let grantee = AgentId::new("child-1");
        st
            .agent_parent
            .insert(AgentId::new("phantom"), grantee.clone());

        let (new_state, _) = delegate(st, &bg, AgentId::root(), grantee.clone()).unwrap();
        assert_eq!(new_state.agent_parent.get(&grantee), Some(&AgentId::root()));
        assert!(
            !new_state
                .agent_parent
                .contains_key(&AgentId::new("phantom"))
        );
    }

    #[test]
    fn delegate_spawns_grantee_at_budget_zero() {
        let st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let grantee = AgentId::new("child-1");

        let (new_state, _) = delegate(st, &bg, AgentId::root(), grantee.clone()).unwrap();
        assert_eq!(new_state.budget(&grantee), 0);
        assert!(!new_state.affordable(&grantee, 1));
    }

    #[test]
    fn delegate_gives_grantee_empty_integ_levels() {
        let mut st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let grantee = AgentId::new("child-1");
        st
            .integ_levels
            .insert(grantee.clone(), VecSet::from([IntegLevel::Untrusted]));

        let (new_state, _) = delegate(st, &bg, AgentId::root(), grantee.clone()).unwrap();
        assert!(new_state.integ_levels.get(&grantee).is_none());
    }

    #[test]
    fn delegate_child_cannot_endorse_until_credited() {
        // Design finding 5 regression: a delegated child cannot self-fund an endorsed
        // completion (bounded + conforming) until sentinel_credit_budget faucets it.
        let st = KernelState::initial();
        let bg_delegate = BackgroundTheoryBuilder::new().build();
        let grantee = AgentId::new("child-1");
        let (mut st, _) =
            delegate(st, &bg_delegate, AgentId::root(), grantee.clone()).unwrap();

        st.agent_cap.insert(grantee.clone(), VecSet::from([CapKind::CreditBudget]));

        let tool = ToolId::new("bounded");
        let inv = InvocationId::new("binv");
        st.invocation_tool.insert(inv.clone(), tool.clone());
        st.in_flight.insert_into(grantee.clone(), inv.clone());

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            tool,
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Sensitive,
                output_bounded: true,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        let bg = builder.build();

        // Before credit: budget 0 cannot afford the Sensitive weight (2), so the endorsed
        // path is skipped and full taint applies -- laundering requires an explicit credit.
        let (st, _) = invoke_complete(st, &bg, &ConformsAll, grantee.clone(), inv.clone())
            .expect("invoke_complete succeeds even when endorsement is unaffordable");
        assert!(
            st.taint_levels.get(&grantee).unwrap().contains(&ConfLevel::Sensitive),
            "uncredited child cannot self-fund the endorsed path"
        );
        assert_eq!(st.budget(&grantee), 0, "no debit on the unendorsed path");

        // After credit: same shape completes endorsed with a debit.
        let (mut st, _) = sentinel_credit_budget(st, &bg, grantee.clone(), 4)
            .expect("credit succeeds with cap_credit_budget");
        st.taint_levels.remove(&grantee);
        st.in_flight.insert_into(grantee.clone(), inv.clone());

        let (st, _) = invoke_complete(st, &bg, &ConformsAll, grantee.clone(), inv)
            .expect("invoke_complete succeeds");
        assert!(
            st.taint_levels.get(&grantee).is_none(),
            "credited child affords the endorsed path"
        );
        assert_eq!(st.budget(&grantee), 4 - 2, "endorsed debit applied");
    }

    #[test]
    fn revoke_does_not_reset_budget_on_id_reuse() {
        let st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child-1");

        let (mut st, _) = delegate(st, &bg, AgentId::root(), child.clone()).unwrap();
        st.agent_cap.insert(child.clone(), VecSet::from([CapKind::CreditBudget]));
        let (st, _) = sentinel_credit_budget(st, &bg, child.clone(), 5).unwrap();
        assert_eq!(st.budget(&child), 5);

        let (st, _) = revoke(st, &bg, AgentId::root(), child.clone()).unwrap();
        assert_eq!(
            st.budget(&child),
            5,
            "revoke leaves the budget entry framed, not reset to capacity"
        );

        let (st, _) = delegate(st, &bg, AgentId::root(), child.clone()).unwrap();
        assert_eq!(
            st.budget(&child),
            0,
            "re-delegating the same id zeroes the budget explicitly, not via capacity absence"
        );
    }

    // --- grant_capability ---

    #[test]
    fn grant_capability_success() {
        let mut st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child-1");
        st.agent_active.insert(child.clone());
        st.agent_parent.insert(child.clone(), AgentId::root());
        st.agent_cap.insert(child.clone(), VecSet::new());

        let (new_state, action) = grant_capability(
            st,
            &bg,
            AgentId::root(),
            child.clone(),
            CapKind::FilesystemRead,
        )
        .unwrap();
        assert!(
            new_state
                .agent_cap
                .get(&child)
                .unwrap()
                .contains(&CapKind::FilesystemRead)
        );
        assert_eq!(
            action,
            KernelAction::GrantCapability {
                parent: AgentId::root(),
                child,
                cap: CapKind::FilesystemRead,
            }
        );
    }

    #[test]
    fn grant_capability_rejects_cap_parent_lacks() {
        let mut st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let parent = AgentId::new("parent");
        let child = AgentId::new("child");
        st.agent_active.insert(parent.clone());
        st.agent_active.insert(child.clone());
        st.agent_parent.insert(child.clone(), parent.clone());
        st.agent_cap.insert(parent, VecSet::new());
        st.agent_cap.insert(child.clone(), VecSet::new());
        assert!(
            grant_capability(
                st,
                &bg,
                AgentId::new("parent"),
                child,
                CapKind::FilesystemRead
            )
            .is_err()
        );
    }

    #[test]
    fn grant_capability_rejects_non_child() {
        let mut st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let other = AgentId::new("other");
        st.agent_active.insert(other.clone());
        assert!(
            grant_capability(st, &bg, AgentId::root(), other, CapKind::FilesystemRead).is_err()
        );
    }

    // --- revoke ---

    #[test]
    fn revoke_success() {
        let mut st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child-1");
        st.agent_active.insert(child.clone());
        st.agent_parent.insert(child.clone(), AgentId::root());
        st
            .agent_cap
            .insert(child.clone(), VecSet::from([CapKind::FilesystemRead]));
        st
            .taint_levels
            .insert(child.clone(), VecSet::from([ConfLevel::Internal]));

        let (new_state, action) = revoke(st, &bg, AgentId::root(), child.clone()).unwrap();
        assert!(!new_state.agent_active.contains(&child));
        assert!(!new_state.agent_parent.contains_key(&child));
        assert!(new_state.taint_levels.get(&child).is_none());
        assert_eq!(
            action,
            KernelAction::Revoke {
                parent: AgentId::root(),
                target: child,
            }
        );
    }

    #[test]
    fn revoke_clears_integ_levels_but_leaves_invocation_used_intact() {
        let mut st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child-1");
        let inv = InvocationId::new("inv-1");
        st.agent_active.insert(child.clone());
        st.agent_parent.insert(child.clone(), AgentId::root());
        st
            .integ_levels
            .insert(child.clone(), VecSet::from([IntegLevel::Untrusted]));
        st.invocation_used.insert(inv.clone());

        let (new_state, _) = revoke(st, &bg, AgentId::root(), child.clone()).unwrap();
        assert!(new_state.integ_levels.get(&child).is_none());
        assert!(new_state.invocation_used.contains(&inv));
    }

    #[test]
    fn revoke_rejects_non_child() {
        let st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        assert!(revoke(st, &bg, AgentId::root(), AgentId::new("stranger")).is_err());
    }

    #[test]
    fn revoke_preserves_grandchild_parent_link() {
        let mut st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child");
        let grandchild = AgentId::new("grandchild");
        st.agent_active.insert(child.clone());
        st.agent_active.insert(grandchild.clone());
        st.agent_parent.insert(child.clone(), AgentId::root());
        st.agent_parent.insert(grandchild.clone(), child.clone());

        let (new_state, _) = revoke(st, &bg, AgentId::root(), child.clone()).unwrap();
        assert_eq!(new_state.agent_parent.get(&grandchild), Some(&child));
    }

    // --- cascade_revoke ---

    #[test]
    fn cascade_revoke_success() {
        let mut st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let parent = AgentId::new("parent");
        let child = AgentId::new("child");
        st.agent_active.insert(child.clone());
        st.agent_parent.insert(child.clone(), parent.clone());

        let (new_state, action) =
            cascade_revoke(st, &bg, child.clone(), parent.clone()).unwrap();
        assert!(!new_state.agent_active.contains(&child));
        assert!(!new_state.agent_parent.contains_key(&child));
        assert_eq!(action, KernelAction::CascadeRevoke { child, parent });
    }

    #[test]
    fn cascade_revoke_rejects_active_parent() {
        let mut st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child");
        st.agent_active.insert(child.clone());
        st.agent_parent.insert(child.clone(), AgentId::root());
        assert!(cascade_revoke(st, &bg, child, AgentId::root()).is_err());
    }

    // --- invoke_complete ---

    #[test]
    fn invoke_complete_adds_taint_for_non_endorsed() {
        let mut st = KernelState::initial();
        let agent = AgentId::new("agent-1");
        let tool = ToolId::new("risky_tool");
        let inv = InvocationId::new("inv-1");

        st.agent_active.insert(agent.clone());
        st
            .in_flight
            .insert_into(agent.clone(), inv.clone());
        st.invocation_tool.insert(inv.clone(), tool.clone());

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            tool,
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Sensitive,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        let bg = builder.build();

        let (new_state, action) =
            invoke_complete(st, &bg, &ConformsAll, agent.clone(), inv.clone()).unwrap();
        assert!(
            !new_state
                .in_flight
                .get(&agent)
                .is_some_and(|s| s.contains(&inv))
        );
        assert!(
            new_state
                .taint_levels
                .get(&agent)
                .unwrap()
                .contains(&ConfLevel::Sensitive)
        );
        assert_eq!(action, KernelAction::InvokeComplete { agent, inv });
    }

    #[test]
    fn invoke_complete_no_taint_for_endorsed() {
        let mut st = KernelState::initial();
        let agent = AgentId::new("agent-1");
        let tool = ToolId::new("safe_tool");
        let inv = InvocationId::new("inv-1");

        st.agent_active.insert(agent.clone());
        st
            .in_flight
            .insert_into(agent.clone(), inv.clone());
        st.invocation_tool.insert(inv.clone(), tool.clone());

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            tool,
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Sensitive,
                output_bounded: true,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        let bg = builder.build();

        let (new_state, _) = invoke_complete(st, &bg, &ConformsAll, agent.clone(), inv).unwrap();
        assert!(new_state.taint_levels.get(&agent).is_none());
    }

    #[test]
    fn invoke_complete_rejects_not_in_flight() {
        let mut st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let agent = AgentId::new("agent-1");
        st.agent_active.insert(agent.clone());
        assert!(invoke_complete(st, &bg, &ConformsAll, agent, InvocationId::new("inv-1")).is_err());
    }

    // --- return_endorsed ---

    #[test]
    fn return_endorsed_success() {
        let mut st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child-1");
        st.agent_active.insert(child.clone());
        st.agent_parent.insert(child.clone(), AgentId::root());
        // Cross-boundary declassification now requires the child to hold cap_declassify.
        st
            .agent_cap
            .insert(child.clone(), VecSet::from([CapKind::Declassify]));

        let (new_state, action) =
            return_endorsed(st.clone(), &bg, &ConformsAll, child.clone(), AgentId::root()).unwrap();
        assert_eq!(new_state.taint_levels, st.taint_levels);
        assert_eq!(
            action,
            KernelAction::ReturnEndorsed {
                child,
                parent: AgentId::root(),
            }
        );
    }

    #[test]
    fn return_endorsed_rejects_child_with_in_flight() {
        let mut st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child-1");
        st.agent_active.insert(child.clone());
        st.agent_parent.insert(child.clone(), AgentId::root());
        st
            .in_flight
            .insert_into(child.clone(), InvocationId::new("inv-1"));
        st
            .invocation_tool
            .insert(InvocationId::new("inv-1"), ToolId::new("t"));
        assert!(return_endorsed(st, &bg, &ConformsAll, child, AgentId::root()).is_err());
    }

    #[test]
    fn return_endorsed_rejects_non_child() {
        let mut st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let stranger = AgentId::new("stranger");
        st.agent_active.insert(stranger.clone());
        assert!(return_endorsed(st, &bg, &ConformsAll, stranger, AgentId::root()).is_err());
    }

    // --- declassification: conformance + budget ---

    /// State with one in-flight invocation of a bounded tool at `conf_floor`, for agent `a1`.
    fn state_with_bounded_in_flight(conf_floor: ConfLevel) -> (KernelState, BackgroundTheory) {
        let mut st = state_with_agent("a1", &[]);
        let tool = ToolId::new("bounded");
        let inv = InvocationId::new("binv");
        st.invocation_tool.insert(inv.clone(), tool.clone());
        st
            .in_flight
            .insert_into(AgentId::new("a1"), inv);

        let mut b = BackgroundTheoryBuilder::new();
        b.trust_issuer(IssuerId::new("trusted"));
        b.register_tool(
            tool,
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::new(),
                conf_floor,
                output_bounded: true,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        (st, b.build())
    }

    #[test]
    fn invoke_complete_bounded_conforming_is_zero_taint_and_debits_budget() {
        let (st, bg) = state_with_bounded_in_flight(ConfLevel::Sensitive);
        let (st, _) =
            invoke_complete(st, &bg, &ConformsAll, AgentId::new("a1"), InvocationId::new("binv"))
                .unwrap();
        assert!(
            !st.taint_levels.contains_key(&AgentId::new("a1")),
            "bounded + conforming + budget => zero taint"
        );
        assert_eq!(
            st.budget(&AgentId::new("a1")),
            BUDGET_CAPACITY - 2,
            "the endorsed completion debits the agent's own budget by the Sensitive weight (2)"
        );
    }

    #[test]
    fn invoke_complete_bounded_nonconforming_adds_full_taint() {
        let (st, bg) = state_with_bounded_in_flight(ConfLevel::Sensitive);
        let (st, _) = invoke_complete(
            st,
            &bg,
            &ConformsNone,
            AgentId::new("a1"),
            InvocationId::new("binv"),
        )
        .unwrap();
        assert!(
            st
                .taint_levels
                .get(&AgentId::new("a1"))
                .unwrap()
                .contains(&ConfLevel::Sensitive),
            "bounded but non-conforming fails closed to full taint"
        );
        assert_eq!(
            st.budget(&AgentId::new("a1")),
            BUDGET_CAPACITY,
            "the full-taint path does not debit budget"
        );
    }

    #[test]
    fn invoke_complete_exhausted_budget_adds_full_taint() {
        let (mut st, bg) = state_with_bounded_in_flight(ConfLevel::Sensitive);
        // Budget below the Sensitive weight (2) cannot afford the endorsed debit.
        st
            .agent_budget
            .insert(AgentId::new("a1"), 1);
        let (st, _) =
            invoke_complete(st, &bg, &ConformsAll, AgentId::new("a1"), InvocationId::new("binv"))
                .unwrap();
        assert!(
            st
                .taint_levels
                .get(&AgentId::new("a1"))
                .unwrap()
                .contains(&ConfLevel::Sensitive),
            "exhausted budget fails closed to full taint even when bounded + conforming"
        );
    }

    #[test]
    fn invoke_complete_already_tainted_does_not_debit() {
        // Bounded + conforming Sensitive-floor tool, but the agent already holds Sensitive taint.
        // The endorsed path is skipped (re-tainting buys nothing) => no debit, taint preserved.
        let (mut st, bg) = state_with_bounded_in_flight(ConfLevel::Sensitive);
        st
            .taint_levels
            .insert(AgentId::new("a1"), VecSet::from([ConfLevel::Sensitive]));
        let (st, _) =
            invoke_complete(st, &bg, &ConformsAll, AgentId::new("a1"), InvocationId::new("binv"))
                .unwrap();
        assert_eq!(
            st.budget(&AgentId::new("a1")),
            BUDGET_CAPACITY,
            "already-tainted at the floor => no wasted budget debit"
        );
        assert!(
            st
                .taint_levels
                .get(&AgentId::new("a1"))
                .unwrap()
                .contains(&ConfLevel::Sensitive),
            "the pre-existing taint is still present"
        );
    }

    #[test]
    fn return_endorsed_non_conforming_refuses() {
        // A ConformanceOracle whose return_conforms == false blocks the endorsed return.
        let st = parent_child_state();
        let bg = BackgroundTheoryBuilder::new().build();
        let result =
            return_endorsed(st, &bg, &ConformsNone, AgentId::new("c"), AgentId::new("p"));
        assert_eq!(result.unwrap_err(), KernelError::NotConforming);
    }

    /// Active parent `p` (child of root) and active child `c` (child of `p`) holding cap_declassify.
    fn parent_child_state() -> KernelState {
        let mut st = KernelState::initial();
        let p = AgentId::new("p");
        let c = AgentId::new("c");
        st.agent_active.insert(p.clone());
        st.agent_active.insert(c.clone());
        st.agent_parent.insert(p.clone(), AgentId::root());
        st.agent_parent.insert(c.clone(), p.clone());
        st
            .agent_cap
            .insert(c, VecSet::from([CapKind::Declassify]));
        st
    }

    #[test]
    fn return_endorsed_requires_declassify_cap() {
        let mut st = parent_child_state();
        st.agent_cap.insert(AgentId::new("c"), VecSet::new());
        let bg = BackgroundTheoryBuilder::new().build();
        assert!(
            return_endorsed(st, &bg, &ConformsAll, AgentId::new("c"), AgentId::new("p")).is_err(),
            "a child lacking cap_declassify cannot declassify upward"
        );
    }

    #[test]
    fn return_endorsed_debits_recipient_budget() {
        let st = parent_child_state();
        let bg = BackgroundTheoryBuilder::new().build();
        let (st, _) =
            return_endorsed(st, &bg, &ConformsAll, AgentId::new("c"), AgentId::new("p")).unwrap();
        assert_eq!(
            st.budget(&AgentId::new("p")),
            BUDGET_CAPACITY - 2,
            "return_endorsed charges the RECIPIENT (parent) budget by the flat weight (2)"
        );
    }

    #[test]
    fn return_endorsed_budget_drains_then_refuses() {
        let mut st = parent_child_state();
        let bg = BackgroundTheoryBuilder::new().build();
        // Eight endorsed returns (each costs 2) drain the parent's per-subtree budget (16).
        for _ in 0..8 {
            let (s, _) =
                return_endorsed(st, &bg, &ConformsAll, AgentId::new("c"), AgentId::new("p"))
                    .unwrap();
            st = s;
        }
        assert!(!st.affordable(&AgentId::new("p"), 2));
        assert!(
            return_endorsed(st, &bg, &ConformsAll, AgentId::new("c"), AgentId::new("p")).is_err(),
            "the next endorsed return is refused -- caller must fall back to return_unendorsed"
        );
    }

    #[test]
    fn sentinel_credit_budget_saturates_at_capacity() {
        let mut st = state_with_agent("a1", &[CapKind::CreditBudget]);
        st
            .agent_budget
            .insert(AgentId::new("a1"), 3);
        let bg = BackgroundTheoryBuilder::new().build();
        let (st, action) = sentinel_credit_budget(st, &bg, AgentId::new("a1"), 100).unwrap();
        assert_eq!(st.budget(&AgentId::new("a1")), BUDGET_CAPACITY);
        assert_eq!(
            action,
            KernelAction::SentinelCreditBudget {
                agent: AgentId::new("a1"),
                amount: 100,
            }
        );
    }

    #[test]
    fn sentinel_credit_budget_requires_cap() {
        let st = state_with_agent("a1", &[]);
        let bg = BackgroundTheoryBuilder::new().build();
        assert!(
            sentinel_credit_budget(st, &bg, AgentId::new("a1"), 4).is_err(),
            "crediting budget requires cap_credit_budget"
        );
    }

    // --- return_unendorsed ---

    #[test]
    fn return_unendorsed_merges_taint() {
        let mut st = KernelState::initial();
        let child = AgentId::new("child-1");
        st.agent_active.insert(child.clone());
        st.agent_parent.insert(child.clone(), AgentId::root());
        st
            .taint_levels
            .insert(child.clone(), VecSet::from([ConfLevel::Sensitive]));

        let bg = BackgroundTheoryBuilder::new().build();

        let (new_state, action) =
            return_unendorsed(st, &bg, &PassAll, child.clone(), AgentId::root()).unwrap();
        assert!(
            new_state
                .taint_levels
                .get(&AgentId::root())
                .unwrap()
                .contains(&ConfLevel::Sensitive)
        );
        assert_eq!(
            action,
            KernelAction::ReturnUnendorsed {
                child,
                parent: AgentId::root(),
            }
        );
    }

    #[test]
    fn return_unendorsed_blocked_by_flow_gate() {
        let mut st = KernelState::initial();
        let child = AgentId::new("child-1");
        let parent_inv = InvocationId::new("parent-inv");
        let parent_tool = ToolId::new("egress_tool");

        st.agent_active.insert(child.clone());
        st.agent_parent.insert(child.clone(), AgentId::root());
        st
            .taint_levels
            .insert(child.clone(), VecSet::from([ConfLevel::Sensitive]));
        st
            .in_flight
            .insert_into(AgentId::root(), parent_inv.clone());
        st
            .invocation_tool
            .insert(parent_inv, parent_tool.clone());

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            parent_tool,
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        let bg = builder.build();

        assert!(return_unendorsed(st, &bg, &FailAll, child, AgentId::root()).is_err());
    }

    #[test]
    fn return_unendorsed_rejects_child_with_in_flight() {
        let mut st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child-1");
        st.agent_active.insert(child.clone());
        st.agent_parent.insert(child.clone(), AgentId::root());
        st
            .in_flight
            .insert_into(child.clone(), InvocationId::new("i"));
        st
            .invocation_tool
            .insert(InvocationId::new("i"), ToolId::new("t"));
        assert!(return_unendorsed(st, &bg, &PassAll, child, AgentId::root()).is_err());
    }

    // --- invoke_start ---

    #[test]
    fn invoke_start_success_no_egress_tool() {
        let st = state_with_agent("a1", &[CapKind::FilesystemRead]);
        let bg = bg_with_tools();

        let (new_state, action) = invoke_start(
            st,
            &bg,
            &AllowAll,
            &PassAll,
            AgentId::new("a1"),
            ToolId::new("read_file"),
            InvocationId::new("inv-1"),
        )
        .unwrap();

        assert!(
            new_state
                .in_flight
                .get(&AgentId::new("a1"))
                .unwrap()
                .contains(&InvocationId::new("inv-1"))
        );
        assert_eq!(
            *new_state
                .invocation_tool
                .get(&InvocationId::new("inv-1"))
                .unwrap(),
            ToolId::new("read_file"),
        );
        assert_eq!(
            action,
            KernelAction::InvokeStart {
                agent: AgentId::new("a1"),
                tool: ToolId::new("read_file"),
                inv: InvocationId::new("inv-1"),
            }
        );
    }

    #[test]
    fn invoke_start_rejects_missing_capability() {
        let st = state_with_agent("a1", &[]);
        let bg = bg_with_tools();
        assert!(
            invoke_start(
                st,
                &bg,
                &AllowAll,
                &PassAll,
                AgentId::new("a1"),
                ToolId::new("read_file"),
                InvocationId::new("inv-1"),
            )
            .is_err()
        );
    }

    #[test]
    fn invoke_start_rejects_root() {
        let st = KernelState::initial();
        let bg = bg_with_tools();
        assert!(
            invoke_start(
                st,
                &bg,
                &AllowAll,
                &PassAll,
                AgentId::root(),
                ToolId::new("read_file"),
                InvocationId::new("inv-1"),
            )
            .is_err()
        );
    }

    #[test]
    fn invoke_start_rejects_unregistered_tool() {
        let st = state_with_agent("a1", &[CapKind::FilesystemRead]);
        let bg = bg_with_tools();
        assert!(
            invoke_start(
                st,
                &bg,
                &AllowAll,
                &PassAll,
                AgentId::new("a1"),
                ToolId::new("unregistered"),
                InvocationId::new("inv-1"),
            )
            .is_err()
        );
    }

    #[test]
    fn invoke_start_rejects_duplicate_invocation_id() {
        let mut st = state_with_agent("a1", &[CapKind::FilesystemRead]);
        st
            .invocation_tool
            .insert(InvocationId::new("inv-1"), ToolId::new("read_file"));
        let bg = bg_with_tools();
        assert!(
            invoke_start(
                st,
                &bg,
                &AllowAll,
                &PassAll,
                AgentId::new("a1"),
                ToolId::new("read_file"),
                InvocationId::new("inv-1"),
            )
            .is_err()
        );
    }

    #[test]
    fn invoke_start_rejects_authorizer_deny() {
        struct DenyAll;
        impl AuthorizerOracle for DenyAll {
            fn allows(
                &self,
                _: &AgentId,
                _: &ToolId,
                _: &KernelState,
                _: &BackgroundTheory,
            ) -> bool {
                false
            }
        }
        let st = state_with_agent("a1", &[CapKind::FilesystemRead]);
        let bg = bg_with_tools();
        assert!(
            invoke_start(
                st,
                &bg,
                &DenyAll,
                &PassAll,
                AgentId::new("a1"),
                ToolId::new("read_file"),
                InvocationId::new("inv-1"),
            )
            .is_err()
        );
    }

    #[test]
    fn invoke_start_flow_gate_blocks_tainted_agent_egress() {
        let mut st = state_with_agent("a1", &[CapKind::NetworkEgress]);
        st
            .taint_levels
            .insert(AgentId::new("a1"), VecSet::from([ConfLevel::Sensitive]));
        let bg = bg_with_tools();
        assert!(
            invoke_start(
                st,
                &bg,
                &AllowAll,
                &FailAll,
                AgentId::new("a1"),
                ToolId::new("send_email"),
                InvocationId::new("inv-1"),
            )
            .is_err()
        );
    }

    #[test]
    fn invoke_start_flow_gate_allows_with_override() {
        let mut st = state_with_agent("a1", &[CapKind::NetworkEgress]);
        st
            .taint_levels
            .insert(AgentId::new("a1"), VecSet::from([ConfLevel::Sensitive]));
        // Override for Sensitive level (check 2a passes via override) -- seeded into state
        st.flow_override.insert_into(
            AgentId::new("a1"),
            OverrideKey { tool: ToolId::new("send_email"), level: ConfLevel::Sensitive },
        );
        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: VecSet::from([CapKind::NetworkEgress]),
                egress: VecSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        // Public egress is ALLOW (self-flow check 2c passes)
        builder.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Public), None);
        let bg = builder.build();

        assert!(
            invoke_start(
                st,
                &bg,
                &AllowAll,
                &FailAll,
                AgentId::new("a1"),
                ToolId::new("send_email"),
                InvocationId::new("inv-1"),
            )
            .is_ok()
        );
    }

    #[test]
    fn invoke_start_override_is_single_use() {
        let mut st = state_with_agent("a1", &[CapKind::NetworkEgress]);
        st
            .taint_levels
            .insert(AgentId::new("a1"), VecSet::from([ConfLevel::Sensitive]));
        // Override for Sensitive level -- seeded into state
        st.flow_override.insert_into(
            AgentId::new("a1"),
            OverrideKey { tool: ToolId::new("send_email"), level: ConfLevel::Sensitive },
        );
        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: VecSet::from([CapKind::NetworkEgress]),
                egress: VecSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        // Public egress is ALLOW (2c passes); Sensitive/NetworkExternal stays DENY (2a needs override).
        builder.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Public), None);
        let bg = builder.build();

        // First invocation: rescued by the override at 2a.
        let (st, _) = invoke_start(
            st,
            &bg,
            &AllowAll,
            &FailAll,
            AgentId::new("a1"),
            ToolId::new("send_email"),
            InvocationId::new("inv-1"),
        )
        .expect("first invoke_start should pass via override");
        assert!(
            st.override_consumed(
                &AgentId::new("a1"),
                &ToolId::new("send_email"),
                ConfLevel::Sensitive
            ),
            "override should be marked consumed after first necessary use"
        );

        // Free the in-flight slot (adds harmless Public taint).
        let (st, _) = invoke_complete(
            st,
            &bg,
            &ConformsAll,
            AgentId::new("a1"),
            InvocationId::new("inv-1"),
        )
        .expect("invoke_complete should pass");

        // Second invocation: the override is now spent, so 2a is an un-rescued DENY.
        let result = invoke_start(
            st,
            &bg,
            &AllowAll,
            &FailAll,
            AgentId::new("a1"),
            ToolId::new("send_email"),
            InvocationId::new("inv-2"),
        );
        assert!(
            result.is_err(),
            "second invoke_start must fail: single-use override already spent"
        );
    }

    #[test]
    fn invoke_start_override_not_consumed_when_flow_allows() {
        let mut st = state_with_agent("a1", &[CapKind::NetworkEgress]);
        st
            .taint_levels
            .insert(AgentId::new("a1"), VecSet::from([ConfLevel::Sensitive]));
        // Override seeded into state, but ALLOW should prevent it from being consumed.
        st.flow_override.insert_into(
            AgentId::new("a1"),
            OverrideKey { tool: ToolId::new("send_email"), level: ConfLevel::Sensitive },
        );
        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: VecSet::from([CapKind::NetworkEgress]),
                egress: VecSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        // Both relevant pairs ALLOW (ceiling at Sensitive) -> the override is never the operative justification.
        builder.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Sensitive), None);
        let bg = builder.build();

        let (st, _) = invoke_start(
            st,
            &bg,
            &AllowAll,
            &FailAll,
            AgentId::new("a1"),
            ToolId::new("send_email"),
            InvocationId::new("inv-1"),
        )
        .expect("invoke_start should pass via ALLOW");
        assert!(
            !st.override_consumed(
                &AgentId::new("a1"),
                &ToolId::new("send_email"),
                ConfLevel::Sensitive
            ),
            "override must NOT be consumed when ALLOW already permits the flow"
        );
    }

    #[test]
    fn override_used_cleared_on_revoke() {
        let mut st = state_with_agent("a1", &[CapKind::NetworkEgress]);
        st
            .override_used
            .insert_into(AgentId::new("a1"), OverrideKey {
                tool: ToolId::new("send_email"),
                level: ConfLevel::Sensitive,
            });
        let bg = BackgroundTheoryBuilder::new().build();

        let (st, _) = revoke(st, &bg, AgentId::root(), AgentId::new("a1"))
            .expect("revoke should pass");
        assert!(
            !st.override_used.contains_key(&AgentId::new("a1")),
            "revoke must clear consumed-override st so a re-delegated id starts fresh"
        );
    }

    #[test]
    fn return_unendorsed_override_is_single_use() {
        let mut st = KernelState::initial();
        let parent = AgentId::new("p");
        let child = AgentId::new("c");
        st.agent_active.insert(parent.clone());
        st.agent_active.insert(child.clone());
        st.agent_parent.insert(parent.clone(), AgentId::root());
        st.agent_parent.insert(child.clone(), parent.clone());

        // Parent has an in-flight egress tool; child carries conflicting Sensitive taint.
        let inv = InvocationId::new("p-inv");
        st
            .invocation_tool
            .insert(inv.clone(), ToolId::new("send_email"));
        st.in_flight.insert_into(parent.clone(), inv);
        st
            .taint_levels
            .insert(child.clone(), VecSet::from([ConfLevel::Sensitive]));

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        // Sensitive/NetworkExternal defaults to DENY; rescue only via the parent's override.
        // Override seeded into state.
        st.flow_override.insert_into(
            parent.clone(),
            OverrideKey { tool: ToolId::new("send_email"), level: ConfLevel::Sensitive },
        );
        let bg = builder.build();

        let (st, _) =
            return_unendorsed(st, &bg, &FailAll, child.clone(), parent.clone())
                .expect("first return_unendorsed should pass via override");
        assert!(
            st.override_consumed(&parent, &ToolId::new("send_email"), ConfLevel::Sensitive),
            "override should be marked consumed after first necessary use"
        );

        let result = return_unendorsed(st, &bg, &FailAll, child, parent);
        assert!(
            result.is_err(),
            "second return_unendorsed must fail: single-use override already spent"
        );
    }

    #[test]
    fn sentinel_elevate_taint_override_is_single_use() {
        let mut st = KernelState::initial();
        let agent = AgentId::new("a");
        st.agent_active.insert(agent.clone());
        st.agent_parent.insert(agent.clone(), AgentId::root());

        // Agent is clean but has an in-flight external-egress tool.
        let inv = InvocationId::new("a-inv");
        st
            .invocation_tool
            .insert(inv.clone(), ToolId::new("send_email"));
        st.in_flight.insert_into(agent.clone(), inv);

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        // Raising taint to Sensitive makes (Sensitive, NetworkExternal)=DENY bite the in-flight
        // send_email; only the override rescues it -- and spends it. Override seeded into state.
        st.flow_override.insert_into(
            agent.clone(),
            OverrideKey { tool: ToolId::new("send_email"), level: ConfLevel::Sensitive },
        );
        let bg = builder.build();

        let (st, _) =
            sentinel_elevate_taint(st, &bg, &FailAll, agent.clone(), ConfLevel::Sensitive)
                .expect("first sentinel raise should pass via override");
        assert!(
            st.override_consumed(&agent, &ToolId::new("send_email"), ConfLevel::Sensitive),
            "sentinel should consume the override that was the sole justification"
        );

        let result = sentinel_elevate_taint(st, &bg, &FailAll, agent, ConfLevel::Sensitive);
        assert!(
            result.is_err(),
            "second sentinel raise must fail: single-use override already spent"
        );
    }

    #[test]
    fn invoke_start_check_2b_new_tool_taint_vs_existing_inflight_egress() {
        let mut st = state_with_agent("a1", &[CapKind::FilesystemRead, CapKind::NetworkEgress]);
        let email_inv = InvocationId::new("email-inv");
        st
            .in_flight
            .insert_into(AgentId::new("a1"), email_inv.clone());
        st
            .invocation_tool
            .insert(email_inv, ToolId::new("send_email"));

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("read_file"),
            ToolMetadata {
                capabilities: VecSet::from([CapKind::FilesystemRead]),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Sensitive,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        builder.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: VecSet::from([CapKind::NetworkEgress]),
                egress: VecSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        let bg = builder.build();

        assert!(
            invoke_start(
                st,
                &bg,
                &AllowAll,
                &FailAll,
                AgentId::new("a1"),
                ToolId::new("read_file"),
                InvocationId::new("inv-2"),
            )
            .is_err()
        );
    }

    // --- load_instruction ---

    #[test]
    fn load_instruction_success() {
        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_instruction(InstructionId::new("sys"), IssuerId::new("trusted"));
        let bg = builder.build();

        let mut st = KernelState::initial();
        let agent = AgentId::new("a1");
        st.agent_active.insert(agent.clone());

        let (new_state, action) =
            load_instruction(st, &bg, agent.clone(), InstructionId::new("sys")).unwrap();
        assert!(
            new_state
                .agent_instruction
                .get(&agent)
                .unwrap()
                .contains(&InstructionId::new("sys"))
        );
        assert_eq!(
            action,
            KernelAction::LoadInstruction {
                agent,
                instr: InstructionId::new("sys")
            }
        );
    }

    #[test]
    fn load_instruction_rejects_inactive_agent() {
        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_instruction(InstructionId::new("sys"), IssuerId::new("trusted"));
        let bg = builder.build();
        let st = KernelState::initial();
        assert!(
            load_instruction(st, &bg, AgentId::new("ghost"), InstructionId::new("sys")).is_err()
        );
    }

    #[test]
    fn load_instruction_rejects_untrusted_issuer() {
        let mut builder = BackgroundTheoryBuilder::new();
        builder.register_instruction(InstructionId::new("skill"), IssuerId::new("rogue"));
        let bg = builder.build();
        let mut st = KernelState::initial();
        let agent = AgentId::new("a1");
        st.agent_active.insert(agent.clone());
        assert!(load_instruction(st, &bg, agent, InstructionId::new("skill")).is_err());
    }

    #[test]
    fn load_instruction_rejects_unknown_instruction() {
        let bg = BackgroundTheoryBuilder::new().build();
        let mut st = KernelState::initial();
        let agent = AgentId::new("a1");
        st.agent_active.insert(agent.clone());
        assert!(load_instruction(st, &bg, agent, InstructionId::new("nope")).is_err());
    }

    #[test]
    fn register_tool_rejects_untrusted_issuer() {
        let mut builder = BackgroundTheoryBuilder::new();
        builder.register_tool(
            ToolId::new("evil"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Public,
                output_bounded: true,
                issuer: IssuerId::new("rogue"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        // "rogue" is NOT trusted (no trust_issuer call)
        let bg = builder.build();
        let st = KernelState::initial();
        assert!(register_tool(st, &bg, ToolId::new("evil")).is_err());
    }

    // --- grant_override ---

    #[test]
    fn grant_override_requires_cap() {
        // Non-root agent without GrantOverride cap.
        let granter = AgentId::new("g");
        let target = AgentId::new("t");
        let mut st = KernelState::initial();
        st.agent_active.insert(granter.clone());
        st.agent_active.insert(target.clone());
        // Deliberately give it some caps, just not GrantOverride.
        st.agent_cap.insert(granter.clone(), VecSet::from([CapKind::FilesystemRead]));

        let bg = BackgroundTheoryBuilder::new().build();
        let result =
            grant_override(st, &bg, granter, target, ToolId::new("t"), ConfLevel::Sensitive);
        assert_eq!(result.unwrap_err(), KernelError::CapabilityMissing);
    }

    #[test]
    fn grant_override_requires_granter_budget() {
        let granter = AgentId::new("g");
        let target = AgentId::new("t");
        let mut st = KernelState::initial();
        st.agent_active.insert(granter.clone());
        st.agent_active.insert(target.clone());
        st.agent_cap.insert(granter.clone(), VecSet::from([CapKind::GrantOverride]));
        st.agent_budget.insert(granter.clone(), 0);

        let bg = BackgroundTheoryBuilder::new().build();
        let result =
            grant_override(st, &bg, granter, target, ToolId::new("t"), ConfLevel::Sensitive);
        assert_eq!(result.unwrap_err(), KernelError::BudgetExhausted);
    }

    #[test]
    fn grant_override_debits_granter() {
        // Root starts at full capacity; after grant_override it should be one lower.
        let target = AgentId::new("t");
        let mut st = KernelState::initial();
        st.agent_active.insert(target.clone());

        let bg = BackgroundTheoryBuilder::new().build();
        let granter = AgentId::root();

        assert_eq!(st.budget(&granter), BUDGET_CAPACITY);
        let target_budget_before = st.budget(&target);

        let (st, _) = grant_override(
            st,
            &bg,
            granter.clone(),
            target.clone(),
            ToolId::new("t"),
            ConfLevel::Sensitive,
        )
        .expect("grant_override should succeed");

        assert_eq!(st.budget(&granter), BUDGET_CAPACITY - 1, "granter debited by one");
        assert_eq!(st.budget(&target), target_budget_before, "target budget untouched");
    }

    #[test]
    fn grant_override_rearm_refused_while_target_in_flight() {
        let target = AgentId::new("t");
        let mut st = KernelState::initial();
        st.agent_active.insert(target.clone());

        let inv = InvocationId::new("inv-1");
        st.invocation_tool.insert(inv.clone(), ToolId::new("t"));
        st.in_flight.insert_into(target.clone(), inv);

        let bg = BackgroundTheoryBuilder::new().build();
        let result = grant_override(
            st,
            &bg,
            AgentId::root(),
            target,
            ToolId::new("t"),
            ConfLevel::Sensitive,
        );
        assert_eq!(result.unwrap_err(), KernelError::TargetHasInFlight);
    }

    #[test]
    fn grant_override_rearms_consumed_override() {
        // Scenario:
        // 1. Arm override for (agent, send_email, Sensitive) via grant_override.
        // 2. Consume it via sentinel_elevate_taint (DENY flow, sole justification).
        // 3. Verify consumed; verify second sentinel raise is blocked.
        // 4. Complete in-flight (none needed here; sentinel reuse check uses st directly).
        // 5. Re-arm via grant_override; verify NOT consumed any more, flow passes once more.
        let agent = AgentId::new("a");
        let mut st = KernelState::initial();
        st.agent_active.insert(agent.clone());
        st.agent_parent.insert(agent.clone(), AgentId::root());

        // Arm an in-flight so sentinel_elevate_taint can bite a DENY-mode pair.
        let inv = InvocationId::new("a-inv");
        st.invocation_tool.insert(inv.clone(), ToolId::new("send_email"));
        st.in_flight.insert_into(agent.clone(), inv.clone());

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        let bg = builder.build();

        // Root arms the override (agent has no in-flight from root's perspective — wait, the
        // re-arm guard is on TARGET, not granter). But agent IS the target and has in-flight.
        // We need to arm BEFORE the in-flight exists. Re-seed properly: arm first, then add flight.
        let mut st2 = KernelState::initial();
        st2.agent_active.insert(agent.clone());
        st2.agent_parent.insert(agent.clone(), AgentId::root());

        // Arm (no in-flight yet).
        let (mut st2, _) = grant_override(
            st2,
            &bg,
            AgentId::root(),
            agent.clone(),
            ToolId::new("send_email"),
            ConfLevel::Sensitive,
        )
        .expect("arm should succeed when no in-flight");

        // Now add the in-flight so sentinel_elevate_taint can trigger a DENY check.
        st2.invocation_tool.insert(inv.clone(), ToolId::new("send_email"));
        st2.in_flight.insert_into(agent.clone(), inv.clone());

        // Consume via sentinel raise (Sensitive/NetworkExternal = DENY; override rescues once).
        let (st2, _) =
            sentinel_elevate_taint(st2, &bg, &FailAll, agent.clone(), ConfLevel::Sensitive)
                .expect("first sentinel raise should pass via override");
        assert!(
            st2.override_consumed(&agent, &ToolId::new("send_email"), ConfLevel::Sensitive),
            "override should be consumed after first sentinel use"
        );

        // Second sentinel raise must be blocked.
        let result = sentinel_elevate_taint(st2.clone(), &bg, &FailAll, agent.clone(), ConfLevel::Sensitive);
        assert!(result.is_err(), "second sentinel raise must fail: override spent");

        // Complete the in-flight so re-arm guard passes.
        let (st2, _) = invoke_complete(st2, &bg, &ConformsAll, agent.clone(), inv)
            .expect("invoke_complete should succeed");
        assert!(!st2.in_flight.set_nonempty(&agent), "no more in-flight");

        // Re-arm: override_consumed entry must be cleared (grant_override removes from override_used).
        let (st2, _) = grant_override(
            st2,
            &bg,
            AgentId::root(),
            agent.clone(),
            ToolId::new("send_email"),
            ConfLevel::Sensitive,
        )
        .expect("re-arm should succeed");
        assert!(
            !st2.override_consumed(&agent, &ToolId::new("send_email"), ConfLevel::Sensitive),
            "re-arm must clear the consumed flag"
        );
        assert!(
            st2.has_flow_override(&agent, &ToolId::new("send_email"), ConfLevel::Sensitive),
            "re-arm must restore the flow_override grant"
        );

        // Add a new in-flight and verify the override is usable exactly once more.
        let inv2 = InvocationId::new("a-inv-2");
        let mut st2 = st2;
        st2.invocation_tool.insert(inv2.clone(), ToolId::new("send_email"));
        st2.in_flight.insert_into(agent.clone(), inv2);

        let (st2, _) =
            sentinel_elevate_taint(st2, &bg, &FailAll, agent.clone(), ConfLevel::Sensitive)
                .expect("post-rearm sentinel raise should pass");
        assert!(
            st2.override_consumed(&agent, &ToolId::new("send_email"), ConfLevel::Sensitive),
            "re-armed override consumed again"
        );

        let result2 =
            sentinel_elevate_taint(st2, &bg, &FailAll, agent.clone(), ConfLevel::Sensitive);
        assert!(result2.is_err(), "third raise must fail: re-armed override also single-use");
    }

    #[test]
    fn grant_override_self_grant() {
        let agent = AgentId::new("a");
        let mut st = KernelState::initial();
        st.agent_active.insert(agent.clone());
        st.agent_cap.insert(agent.clone(), VecSet::from([CapKind::GrantOverride]));

        let bg = BackgroundTheoryBuilder::new().build();
        let budget_before = st.budget(&agent);
        let (st, _) = grant_override(
            st,
            &bg,
            agent.clone(),
            agent.clone(),
            ToolId::new("t"),
            ConfLevel::Sensitive,
        )
        .expect("self-grant should succeed with no in-flight");

        assert!(
            st.has_flow_override(&agent, &ToolId::new("t"), ConfLevel::Sensitive),
            "override armed for granter-as-target"
        );
        assert_eq!(st.budget(&agent), budget_before - 1, "granter debited");
    }

    #[test]
    fn death_clears_override_grants() {
        let child = AgentId::new("child");
        let mut st = KernelState::initial();
        st.agent_active.insert(child.clone());
        st.agent_parent.insert(child.clone(), AgentId::root());

        let bg = BackgroundTheoryBuilder::new().build();

        // Arm an override for child.
        let (st, _) = grant_override(
            st,
            &bg,
            AgentId::root(),
            child.clone(),
            ToolId::new("t"),
            ConfLevel::Sensitive,
        )
        .expect("arm should succeed");
        assert!(
            st.flow_override.get(&child).is_some(),
            "override should be armed"
        );

        // Revoke the child; clear_agent_state should clear flow_override.
        let (st, _) = revoke(st, &bg, AgentId::root(), child.clone())
            .expect("revoke should succeed");
        assert!(
            st.flow_override.get(&child).is_none(),
            "revoke must clear flow_override for the dead agent"
        );
    }
}
