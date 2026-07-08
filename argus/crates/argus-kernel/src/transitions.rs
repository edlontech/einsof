use crate::background::{BackgroundTheory, FlowMode};
use crate::capability::CapKind;
use crate::collections::{VecMap, VecSet};
use crate::error::KernelError;
use crate::event::KernelAction;
use crate::state::KernelState;
use crate::traits::{AuthorizerOracle, ConformanceOracle, ContentGateOracle};
use crate::types::{
    AgentId, ConfLevel, EgressKind, InstructionId, IntegLevel, InvocationId, OverrideKey, ToolId,
    declass_weight, integ_weight,
};

/// Outcome of a flow-gate check at a consuming site (`invoke_start` / `return_unendorsed` /
/// `sentinel_elevate_taint`). ALLOW (or INSPECT with a passing content gate) admits the flow
/// outright; DENY admits only when rescued by an armed, not-yet-consumed override grant. Eager
/// consumption (design "Override consumption semantics" -- Actions.lean:187-196) is tracked by
/// dedicated per-transition loops, not here: the spec's consumption clauses have no egress
/// conjunct, so this decision only gates admission and never marks an override as spent.
enum FlowDecision {
    Allowed,
    Denied,
}

fn flow_decision(
    bg: &BackgroundTheory,
    content_gate: &impl ContentGateOracle,
    agent: &AgentId,
    tool: &ToolId,
    vouch_inv: &InvocationId,
    st: &KernelState,
    level: ConfLevel,
    egress: EgressKind,
) -> FlowDecision {
    match bg.flow_mode(level, egress) {
        FlowMode::Allow => FlowDecision::Allowed,
        FlowMode::Inspect => {
            if content_gate.passes(agent, tool, vouch_inv, st, bg) {
                FlowDecision::Allowed
            } else {
                FlowDecision::Denied
            }
        }
        FlowMode::Deny => {
            if st.has_flow_override(agent, tool, level)
                && !st.override_consumed(agent, tool, level)
            {
                FlowDecision::Allowed
            } else {
                FlowDecision::Denied
            }
        }
    }
}

/// Outcome of an integrity-gate check at `invoke_start`'s CHECK 4 (a/b/c). ALLOW clears the
/// floor outright; INSPECT admits with a passing vouch from the content gate; DENY otherwise.
/// No override arm anywhere -- endorsement is the only way up (design §3 non-goal, §5.3).
enum IntegDecision {
    Allowed,
    Denied,
}

/// Graduated two-verdict + vouch integrity check (dual of `flow_decision`, minus the override
/// arm): ALLOW iff `floor.le(level)` (the level clears the floor), else INSPECT iff
/// `inspect_floor.le(level)` and the vouched invocation's content gate passes, else DENY.
fn integ_decision(
    content_gate: &impl ContentGateOracle,
    agent: &AgentId,
    tool: &ToolId,
    vouch_inv: &InvocationId,
    st: &KernelState,
    bg: &BackgroundTheory,
    floor: IntegLevel,
    inspect_floor: IntegLevel,
    level: IntegLevel,
) -> IntegDecision {
    let allowed = floor.le(level)
        || (inspect_floor.le(level) && content_gate.passes(agent, tool, vouch_inv, st, bg));
    if allowed { IntegDecision::Allowed } else { IntegDecision::Denied }
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

/// Fold `flow_decision` over a tool's egress kinds at `level`, updating `denied` (monotone --
/// set on any DENY, never cleared). No early `return` inside the loop -- callers inspect
/// `denied` after the fold. This (plus index loops) is the shape Aeneas extracts transparently;
/// the previous early-return-in-loop form forced an axiom. Consumption is NOT tracked here --
/// see the `FlowDecision` doc comment; callers run dedicated consumption loops after all gates
/// pass.
fn gate_egress<C: ContentGateOracle>(
    bg: &BackgroundTheory,
    content_gate: &C,
    agent: &AgentId,
    tool: &ToolId,
    vouch_inv: &InvocationId,
    st: &KernelState,
    level: ConfLevel,
    egress_set: &VecSet<EgressKind>,
    mut denied: bool,
) -> bool {
    let mut i = 0;
    while i < egress_set.len() {
        let egress = *egress_set.at(i);
        if let FlowDecision::Denied =
            flow_decision(bg, content_gate, agent, tool, vouch_inv, st, level, egress)
        {
            denied = true;
        }
        i += 1;
    }
    denied
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
    attested_egress: VecSet<EgressKind>,
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
    // Freshness: this invocation id has never been used before (design §5.3).
    if st.invocation_used.contains(&inv) {
        return Err(KernelError::InvocationReplayed);
    }

    // Clone the tool's metadata to an owned local: holding the `bg` borrow while it is read across
    // the gate loops and used to clone egress sets keeps the extractor's region analysis happy.
    let tool_meta = match bg.tool_metadata(&tool) {
        Some(m) => m,
        None => return Err(KernelError::ToolNotInTheory),
    };
    let conf_floor = tool_meta.conf_floor;

    // Narrowing: the attested egress cannot exceed the tool's declared set.
    let mut narrowing_violated = false;
    let mut nai = 0;
    while nai < attested_egress.len() {
        if !tool_meta.egress.contains(attested_egress.at(nai)) {
            narrowing_violated = true;
        }
        nai += 1;
    }
    if narrowing_violated {
        return Err(KernelError::AttestationInvalid);
    }
    // Coverage: an egress-bearing tool cannot be admitted on an empty attestation.
    if !tool_meta.egress.is_empty() && attested_egress.is_empty() {
        return Err(KernelError::AttestationInvalid);
    }

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

    // Flow-gate admission, folded with no early return (the extractable shape); `denied` is
    // checked once after all three checks. Override consumption is tracked separately below --
    // it is eager (design "Override consumption semantics"), not tied to gate admission.
    let mut denied = false;

    // CHECK 2a: the new tool's attested egress against every speculative-taint level the agent
    // carries. The vouch is the NEW invocation's content-gate verdict.
    let spec_taint = st.speculative_taint(&agent, bg);
    let mut li = 0;
    while li < spec_taint.len() {
        let level = *spec_taint.at(li);
        denied = gate_egress(bg, content_gate, &agent, &tool, &inv, &st, level, &attested_egress, denied);
        li += 1;
    }

    // CHECK 2b/2c run for ALL tools -- bounded is NOT excluded. With conformance-gating a bounded
    // tool may still add taint on completion (if it fails conformance), so its floor must be
    // flow-compatible just like a non-bounded tool (worst-case / fail-closed).
    // CHECK 2b: the new tool's floor against every in-flight invocation's STORED (attested)
    // egress. The vouch is the IN-FLIGHT invocation's content-gate verdict (being re-examined
    // against the new floor).
    let agent_flights = st.in_flight.get_set_or_empty(&agent);
    let mut fi = 0;
    while fi < agent_flights.len() {
        let flight_inv = agent_flights.at(fi);
        if let Some(flight_tool_id) = st.invocation_tool.get_cloned(flight_inv) {
            let flight_egress = st.invocation_egress.get_set_or_empty(flight_inv);
            denied = gate_egress(
                bg,
                content_gate,
                &agent,
                &flight_tool_id,
                flight_inv,
                &st,
                conf_floor,
                &flight_egress,
                denied,
            );
        }
        fi += 1;
    }

    // CHECK 2c: the new tool's own attested egress at its own floor. The vouch is again the NEW
    // invocation's content-gate verdict.
    denied = gate_egress(bg, content_gate, &agent, &tool, &inv, &st, conf_floor, &attested_egress, denied);

    if denied {
        return Err(KernelError::FlowGateBlocked);
    }

    // CHECK 3: authorizer gate, keyed on this invocation.
    if !authorizer.allows(&agent, &tool, &inv, &st, bg) {
        return Err(KernelError::AuthorizerDenied);
    }

    // CHECK 4 a/b/c: integrity gate (mirrors CHECK 2's three sub-checks on the integrity
    // side). NO override arm anywhere -- endorsement is the only way up.
    let mut integ_denied = false;

    // CHECK 4a: every speculative-integrity level the agent carries against the new tool's
    // floor. The vouch is the NEW invocation's content-gate verdict.
    let spec_integ = st.speculative_integ(&agent, bg);
    let mut igi = 0;
    while igi < spec_integ.len() {
        let level = *spec_integ.at(igi);
        if let IntegDecision::Denied = integ_decision(
            content_gate,
            &agent,
            &tool,
            &inv,
            &st,
            bg,
            tool_meta.integ_floor,
            tool_meta.integ_inspect_floor,
            level,
        ) {
            integ_denied = true;
        }
        igi += 1;
    }

    // CHECK 4b: the new tool's emission against every in-flight tool's floor (the "web_fetch
    // completes while delete_repo is in flight" hazard). The vouch is the IN-FLIGHT
    // invocation whose floor is being crossed.
    let mut fbi = 0;
    while fbi < agent_flights.len() {
        let flight_inv = agent_flights.at(fbi);
        if let Some(flight_tool_id) = st.invocation_tool.get_cloned(flight_inv) {
            if let Some(flight_meta) = bg.tool_metadata(&flight_tool_id) {
                if let IntegDecision::Denied = integ_decision(
                    content_gate,
                    &agent,
                    &flight_tool_id,
                    flight_inv,
                    &st,
                    bg,
                    flight_meta.integ_floor,
                    flight_meta.integ_inspect_floor,
                    tool_meta.output_integ,
                ) {
                    integ_denied = true;
                }
            }
        }
        fbi += 1;
    }

    // CHECK 4c: the new tool's own emission against its own floor. The vouch is again the
    // NEW invocation.
    if let IntegDecision::Denied = integ_decision(
        content_gate,
        &agent,
        &tool,
        &inv,
        &st,
        bg,
        tool_meta.integ_floor,
        tool_meta.integ_inspect_floor,
        tool_meta.output_integ,
    ) {
        integ_denied = true;
    }

    if integ_denied {
        return Err(KernelError::IntegrityFloorDenied);
    }

    // Eager override consumption (Actions.lean:187-196): an armed override is marked used
    // whenever the gate examined a pair it was armed for, regardless of which arm admitted the
    // flow -- no egress conjunct, no negated gate arms.
    let mut to_consume: VecSet<OverrideKey> = VecSet::new();

    // Clause 2a: the new tool armed against a speculative-taint level the agent carries.
    let mut ti = 0;
    while ti < spec_taint.len() {
        let level = *spec_taint.at(ti);
        if st.has_flow_override(&agent, &tool, level) {
            to_consume.insert(OverrideKey { tool: tool.clone(), level });
        }
        ti += 1;
    }

    // Clause 2c: the new tool's own floor armed against its own egress -- unconditional.
    if st.has_flow_override(&agent, &tool, conf_floor) {
        to_consume.insert(OverrideKey { tool: tool.clone(), level: conf_floor });
    }

    // Clause 2b: each pre-existing in-flight tool armed against the new tool's floor.
    let mut ri = 0;
    while ri < agent_flights.len() {
        let flight_inv = agent_flights.at(ri);
        if let Some(flight_tool_id) = st.invocation_tool.get_cloned(flight_inv) {
            if st.has_flow_override(&agent, &flight_tool_id, conf_floor) {
                to_consume.insert(OverrideKey { tool: flight_tool_id, level: conf_floor });
            }
        }
        ri += 1;
    }

    if !to_consume.is_empty() {
        st.override_used.extend_into(agent.clone(), &to_consume);
    }

    st.invocation_tool.insert(inv.clone(), tool.clone());
    st.in_flight.insert_into(agent.clone(), inv.clone());
    st.invocation_egress.insert(inv.clone(), attested_egress);
    st.invocation_used.insert(inv.clone());

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
    let mut endorsed = false;
    if let Some(tool_id) = st.invocation_tool.get_cloned(&inv) {
        let meta_info = match bg.tool_metadata(&tool_id) {
            Some(tmeta) => Some((tmeta.conf_floor, tmeta.output_bounded, tmeta.output_integ)),
            None => None,
        };
        if let Some((conf_floor, output_bounded, output_integ)) = meta_info {
            // The unified two-dimension crossing (design §5.4): a crossing helps a dimension
            // when the agent does not already hold that dimension's level, and is priced only
            // for the dimensions it helps.
            let conf_helps = !st.taint_levels.set_contains(&agent, &conf_floor);
            let integ_helps = !st.integ_levels.set_contains(&agent, &output_integ);
            let crossing_weight = (if conf_helps { declass_weight(conf_floor) } else { 0 })
                + (if integ_helps { integ_weight(output_integ) } else { 0 });
            let crossing_ok = output_bounded
                && conformance.conforms(&agent, &tool_id, &inv, &st, bg)
                && st.agent_cap.set_contains(&agent, &CapKind::Declassify)
                && st.affordable(&agent, crossing_weight)
                && (conf_helps || integ_helps);
            if crossing_ok {
                st.debit_budget(&agent, crossing_weight);
                endorsed = true;
            } else {
                st.taint_levels.insert_into(agent.clone(), conf_floor);
                st.integ_levels.insert_into(agent.clone(), output_integ);
            }
        }
    }

    Ok((
        st,
        KernelAction::InvokeComplete {
            agent,
            inv,
            endorsed,
        },
    ))
}

pub fn return_endorsed<F: ConformanceOracle>(
    mut st: KernelState,
    bg: &BackgroundTheory,
    conformance: &F,
    child: AgentId,
    parent: AgentId,
    clvl: ConfLevel,
    ilvl: IntegLevel,
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

    // Robust declassification lever floor: the CHILD is the declassifying party, so its held
    // integrity must clear the shared lever floor, or sit in the inspect band vouched by
    // `return_conforms` (already required above; mirrored here for shape fidelity with the
    // design's graduated-gate shape).
    let child_integ = st.integ_levels.get_set_or_empty(&child);
    let vouched = conformance.return_conforms(&child, &parent, &st, bg);
    let mut lever_denied = false;
    let mut li = 0;
    while li < child_integ.len() {
        let level = *child_integ.at(li);
        let allowed = bg.lever_integ_floor().le(level)
            || (bg.lever_integ_inspect_floor().le(level) && vouched);
        if !allowed {
            lever_denied = true;
        }
        li += 1;
    }
    if lever_denied {
        return Err(KernelError::LeverIntegrityDenied);
    }

    // Coverage: the declared confidentiality level bounds the child's entire taint set, and the
    // declared integrity level LOWER-bounds the child's entire integ set (integrity is a
    // min lattice -- the declaration sits at or below every level the child holds).
    let child_taint = st.taint_levels.get_set_or_empty(&child);
    let mut conf_denied = false;
    let mut ci = 0;
    while ci < child_taint.len() {
        let level = *child_taint.at(ci);
        if !level.le(clvl) {
            conf_denied = true;
        }
        ci += 1;
    }
    let mut integ_denied = false;
    let mut ii = 0;
    while ii < child_integ.len() {
        let level = *child_integ.at(ii);
        if !ilvl.le(level) {
            integ_denied = true;
        }
        ii += 1;
    }
    if conf_denied || integ_denied {
        return Err(KernelError::DeclarationNotCovering);
    }

    let weight = declass_weight(clvl) + integ_weight(ilvl);
    if !st.affordable(&parent, weight) {
        return Err(KernelError::BudgetExhausted);
    }
    st.debit_budget(&parent, weight);

    Ok((
        st,
        KernelAction::ReturnEndorsed { child, parent, clvl, ilvl },
    ))
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

    // Flow-gate admission, folded over child-taint levels x parent's in-flight tools with no
    // early return.
    let mut denied = false;
    let parent_flights = st.in_flight.get_set_or_empty(&parent);
    let mut li = 0;
    while li < child_taint.len() {
        let level = *child_taint.at(li);
        let mut fi = 0;
        while fi < parent_flights.len() {
            let inv = parent_flights.at(fi);
            if let Some(tool_id) = st.invocation_tool.get_cloned(inv) {
                let egress = st.invocation_egress.get_set_or_empty(inv);
                // Vouch is the parent's in-flight invocation being gated.
                denied = gate_egress(bg, content_gate, &parent, &tool_id, inv, &st, level, &egress, denied);
            }
            fi += 1;
        }
        li += 1;
    }
    if denied {
        return Err(KernelError::FlowGateBlocked);
    }

    if !child_taint.is_empty() {
        st.taint_levels.extend_into(parent.clone(), &child_taint);
    }

    // Eager override consumption (Actions.lean:362-366): armed against the parent's in-flight
    // tool at a level the child holds -- no egress conjunct.
    let mut to_consume: VecSet<OverrideKey> = VecSet::new();
    let mut ci = 0;
    while ci < child_taint.len() {
        let level = *child_taint.at(ci);
        let mut fi = 0;
        while fi < parent_flights.len() {
            let inv = parent_flights.at(fi);
            if let Some(tool_id) = st.invocation_tool.get_cloned(inv) {
                if st.has_flow_override(&parent, &tool_id, level) {
                    to_consume.insert(OverrideKey { tool: tool_id, level });
                }
            }
            fi += 1;
        }
        ci += 1;
    }
    if !to_consume.is_empty() {
        st.override_used.extend_into(parent.clone(), &to_consume);
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

    // Flow gate folded over the agent's in-flight tools x egress at the raised `level`, with no
    // early return; `missing_binding` / `denied` are checked once after the fold.
    let mut denied = false;
    let mut missing_binding = false;
    let in_flight_invs = st.in_flight.get_set_or_empty(&agent);
    let mut fi = 0;
    while fi < in_flight_invs.len() {
        let inv = in_flight_invs.at(fi);
        match st.invocation_tool.get_cloned(inv) {
            Some(tool) => {
                let egress = st.invocation_egress.get_set_or_empty(inv);
                // Vouch is the agent's in-flight invocation being gated.
                denied = gate_egress(bg, content_gate, &agent, &tool, inv, &st, level, &egress, denied);
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
    if denied {
        return Err(KernelError::FlowGateBlocked);
    }

    // Eager override consumption (Actions.lean:380-384): armed against an in-flight tool at
    // `level` -- no egress conjunct.
    let mut to_consume: VecSet<OverrideKey> = VecSet::new();
    let mut ci = 0;
    while ci < in_flight_invs.len() {
        let inv = in_flight_invs.at(ci);
        if let Some(tool) = st.invocation_tool.get_cloned(inv) {
            if st.has_flow_override(&agent, &tool, level) {
                to_consume.insert(OverrideKey { tool, level });
            }
        }
        ci += 1;
    }
    if !to_consume.is_empty() {
        st.override_used.extend_into(agent.clone(), &to_consume);
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
    bg: &BackgroundTheory,
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

    // Robust declassification lever floor: the GRANTER is the declassifying party arming this
    // lever, so its held integrity must clear the floor -- STRICT, no inspect/vouch arm (no
    // conformance object exists here to vouch a near-miss granter with).
    let granter_integ = st.integ_levels.get_set_or_empty(&granter);
    let mut lever_denied = false;
    let mut i = 0;
    while i < granter_integ.len() {
        let level = *granter_integ.at(i);
        if !bg.lever_integ_floor().le(level) {
            lever_denied = true;
        }
        i += 1;
    }
    if lever_denied {
        return Err(KernelError::LeverIntegrityDenied);
    }

    let weight = declass_weight(level);
    if !st.affordable(&granter, weight) {
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
    st.debit_budget(&granter, weight);

    Ok((st, KernelAction::GrantOverride { granter, target, tool, level }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::background::{BackgroundTheoryBuilder, ToolMetadata};
    use crate::types::{BUDGET_CAPACITY, EgressKind, InstructionId, IntegLevel, IssuerId};

    struct AllowAll;
    impl AuthorizerOracle for AllowAll {
        fn allows(&self, _: &AgentId, _: &ToolId, _: &InvocationId, _: &KernelState, _: &BackgroundTheory) -> bool {
            true
        }
    }
    struct PassAll;
    impl ContentGateOracle for PassAll {
        fn passes(&self, _: &AgentId, _: &ToolId, _: &InvocationId, _: &KernelState, _: &BackgroundTheory) -> bool {
            true
        }
    }
    struct FailAll;
    impl ContentGateOracle for FailAll {
        fn passes(&self, _: &AgentId, _: &ToolId, _: &InvocationId, _: &KernelState, _: &BackgroundTheory) -> bool {
            false
        }
    }
    struct ConformsAll;
    impl ConformanceOracle for ConformsAll {
        fn conforms(&self, _: &AgentId, _: &ToolId, _: &InvocationId, _: &KernelState, _: &BackgroundTheory) -> bool {
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
        fn conforms(&self, _: &AgentId, _: &ToolId, _: &InvocationId, _: &KernelState, _: &BackgroundTheory) -> bool {
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

        st.agent_cap.insert(
            grantee.clone(),
            VecSet::from([CapKind::CreditBudget, CapKind::Declassify]),
        );

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
        assert!(
            new_state
                .integ_levels
                .get(&agent)
                .unwrap()
                .contains(&IntegLevel::Attested),
            "unendorsed completion degrades both dimensions"
        );
        assert_eq!(
            action,
            KernelAction::InvokeComplete {
                agent,
                inv,
                endorsed: false,
            }
        );
    }

    #[test]
    fn invoke_complete_no_taint_for_endorsed() {
        let mut st = KernelState::initial();
        let agent = AgentId::new("agent-1");
        let tool = ToolId::new("safe_tool");
        let inv = InvocationId::new("inv-1");

        st.agent_active.insert(agent.clone());
        st
            .agent_cap
            .insert(agent.clone(), VecSet::from([CapKind::Declassify]));
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

        let (new_state, action) = return_endorsed(
            st.clone(),
            &bg,
            &ConformsAll,
            child.clone(),
            AgentId::root(),
            ConfLevel::Public,
            IntegLevel::Attested,
        )
        .unwrap();
        assert_eq!(new_state.taint_levels, st.taint_levels);
        assert_eq!(
            new_state.budget(&AgentId::root()),
            st.budget(&AgentId::root()),
            "a clean child returning at (public, attested) costs the parent nothing"
        );
        assert_eq!(
            action,
            KernelAction::ReturnEndorsed {
                child,
                parent: AgentId::root(),
                clvl: ConfLevel::Public,
                ilvl: IntegLevel::Attested,
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
        assert!(
            return_endorsed(
                st,
                &bg,
                &ConformsAll,
                child,
                AgentId::root(),
                ConfLevel::Public,
                IntegLevel::Attested,
            )
            .is_err()
        );
    }

    #[test]
    fn return_endorsed_rejects_non_child() {
        let mut st = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let stranger = AgentId::new("stranger");
        st.agent_active.insert(stranger.clone());
        assert!(
            return_endorsed(
                st,
                &bg,
                &ConformsAll,
                stranger,
                AgentId::root(),
                ConfLevel::Public,
                IntegLevel::Attested,
            )
            .is_err()
        );
    }

    // --- declassification: conformance + budget ---

    /// State with one in-flight invocation of a bounded tool at `conf_floor`, for agent `a1`,
    /// who holds `cap_declassify` (required at the completion crossing since design §5.4).
    fn state_with_bounded_in_flight(conf_floor: ConfLevel) -> (KernelState, BackgroundTheory) {
        let mut st = state_with_agent("a1", &[CapKind::Declassify]);
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
        // Bounded + conforming Sensitive-floor tool, but the agent already holds Sensitive taint:
        // conf_helps is false, so the conf component of the crossing weight is zero. The
        // integrity component is also zero (tool_output_integ is Attested), so the crossing is
        // free either way => no debit, and the pre-existing taint is left untouched.
        let (mut st, bg) = state_with_bounded_in_flight(ConfLevel::Sensitive);
        st
            .taint_levels
            .insert(AgentId::new("a1"), VecSet::from([ConfLevel::Sensitive]));
        let (st, action) =
            invoke_complete(st, &bg, &ConformsAll, AgentId::new("a1"), InvocationId::new("binv"))
                .unwrap();
        assert_eq!(
            action,
            KernelAction::InvokeComplete {
                agent: AgentId::new("a1"),
                inv: InvocationId::new("binv"),
                endorsed: true,
            },
            "integ_helps (Attested emission not held) keeps the crossing endorsed at weight 0"
        );
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

    /// State with one in-flight invocation of a bounded tool at `conf_floor`/`output_integ`,
    /// for agent `a1` holding `caps` (dual-dimension crossing tests, design §5.4).
    fn state_with_bounded_in_flight_dims(
        conf_floor: ConfLevel,
        output_integ: IntegLevel,
        caps: &[CapKind],
    ) -> (KernelState, BackgroundTheory) {
        let mut st = state_with_agent("a1", caps);
        let tool = ToolId::new("bounded");
        let inv = InvocationId::new("binv");
        st.invocation_tool.insert(inv.clone(), tool.clone());
        st.in_flight.insert_into(AgentId::new("a1"), inv);

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
                output_integ,
            },
        );
        (st, b.build())
    }

    #[test]
    fn invoke_complete_missing_declassify_cap_routes_unendorsed() {
        // Bounded + conforming + affordable, but the agent lacks cap_declassify: crossing_ok is
        // false regardless (design §5.4, finding 11) and the crossing routes unendorsed,
        // degrading both dimensions with no debit.
        let (st, bg) =
            state_with_bounded_in_flight_dims(ConfLevel::Sensitive, IntegLevel::Untrusted, &[]);
        let (st, action) =
            invoke_complete(st, &bg, &ConformsAll, AgentId::new("a1"), InvocationId::new("binv"))
                .unwrap();
        assert!(
            st
                .taint_levels
                .get(&AgentId::new("a1"))
                .unwrap()
                .contains(&ConfLevel::Sensitive),
            "missing cap_declassify fails safe to full taint degradation"
        );
        assert!(
            st
                .integ_levels
                .get(&AgentId::new("a1"))
                .unwrap()
                .contains(&IntegLevel::Untrusted),
            "missing cap_declassify fails safe to full integrity degradation"
        );
        assert_eq!(
            st.budget(&AgentId::new("a1")),
            BUDGET_CAPACITY,
            "the unendorsed path never debits"
        );
        assert_eq!(
            action,
            KernelAction::InvokeComplete {
                agent: AgentId::new("a1"),
                inv: InvocationId::new("binv"),
                endorsed: false,
            }
        );
    }

    #[test]
    fn invoke_complete_dimension_adjusted_debit_integ_only() {
        // The agent already holds the conf floor (conf_helps false) but not the tool's Untrusted
        // emission (integ_helps true): the crossing pays only the integrity component.
        let (mut st, bg) = state_with_bounded_in_flight_dims(
            ConfLevel::Sensitive,
            IntegLevel::Untrusted,
            &[CapKind::Declassify],
        );
        st
            .taint_levels
            .insert(AgentId::new("a1"), VecSet::from([ConfLevel::Sensitive]));
        let (st, action) =
            invoke_complete(st, &bg, &ConformsAll, AgentId::new("a1"), InvocationId::new("binv"))
                .unwrap();
        assert_eq!(
            st.budget(&AgentId::new("a1")),
            BUDGET_CAPACITY - integ_weight(IntegLevel::Untrusted),
            "only the integrity component of the crossing weight is debited"
        );
        assert!(
            st
                .taint_levels
                .get(&AgentId::new("a1"))
                .unwrap()
                .contains(&ConfLevel::Sensitive),
            "conf taint is untouched by the endorsed path"
        );
        assert!(
            st.integ_levels.get(&AgentId::new("a1")).is_none(),
            "integ levels are untouched by the endorsed path"
        );
        assert_eq!(
            action,
            KernelAction::InvokeComplete {
                agent: AgentId::new("a1"),
                inv: InvocationId::new("binv"),
                endorsed: true,
            }
        );
    }

    #[test]
    fn invoke_complete_neither_helps_routes_unendorsed_idempotent() {
        // The agent already holds both the conf floor and the tool's emission: neither dimension
        // helps, so crossing_ok is false (the last conjunct) regardless of cap/conformance/budget,
        // and the crossing routes unendorsed with a zero debit and idempotent inserts.
        let (mut st, bg) = state_with_bounded_in_flight_dims(
            ConfLevel::Sensitive,
            IntegLevel::Untrusted,
            &[CapKind::Declassify],
        );
        st
            .taint_levels
            .insert(AgentId::new("a1"), VecSet::from([ConfLevel::Sensitive]));
        st
            .integ_levels
            .insert(AgentId::new("a1"), VecSet::from([IntegLevel::Untrusted]));
        let (st, action) =
            invoke_complete(st, &bg, &ConformsAll, AgentId::new("a1"), InvocationId::new("binv"))
                .unwrap();
        assert_eq!(
            st.budget(&AgentId::new("a1")),
            BUDGET_CAPACITY,
            "neither dimension helping means zero debit"
        );
        assert!(
            st
                .taint_levels
                .get(&AgentId::new("a1"))
                .unwrap()
                .contains(&ConfLevel::Sensitive),
            "idempotent conf insert"
        );
        assert!(
            st
                .integ_levels
                .get(&AgentId::new("a1"))
                .unwrap()
                .contains(&IntegLevel::Untrusted),
            "idempotent integ insert"
        );
        assert_eq!(
            action,
            KernelAction::InvokeComplete {
                agent: AgentId::new("a1"),
                inv: InvocationId::new("binv"),
                endorsed: false,
            }
        );
    }

    #[test]
    fn invoke_complete_endorsed_both_dimensions_debits_sum() {
        // Fresh agent, both dimensions help: the crossing debits declass_weight(floor) +
        // integ_weight(emission) and propagates neither set.
        let (st, bg) = state_with_bounded_in_flight_dims(
            ConfLevel::Sensitive,
            IntegLevel::Untrusted,
            &[CapKind::Declassify],
        );
        let (st, action) =
            invoke_complete(st, &bg, &ConformsAll, AgentId::new("a1"), InvocationId::new("binv"))
                .unwrap();
        assert_eq!(
            st.budget(&AgentId::new("a1")),
            BUDGET_CAPACITY
                - (declass_weight(ConfLevel::Sensitive) + integ_weight(IntegLevel::Untrusted)),
            "the endorsed debit sums both dimension weights"
        );
        assert!(st.taint_levels.get(&AgentId::new("a1")).is_none());
        assert!(st.integ_levels.get(&AgentId::new("a1")).is_none());
        assert_eq!(
            action,
            KernelAction::InvokeComplete {
                agent: AgentId::new("a1"),
                inv: InvocationId::new("binv"),
                endorsed: true,
            }
        );
    }

    #[test]
    fn return_endorsed_non_conforming_refuses() {
        // A ConformanceOracle whose return_conforms == false blocks the endorsed return.
        let st = parent_child_state();
        let bg = BackgroundTheoryBuilder::new().build();
        let result = return_endorsed(
            st,
            &bg,
            &ConformsNone,
            AgentId::new("c"),
            AgentId::new("p"),
            ConfLevel::Sensitive,
            IntegLevel::Attested,
        );
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
            return_endorsed(
                st,
                &bg,
                &ConformsAll,
                AgentId::new("c"),
                AgentId::new("p"),
                ConfLevel::Sensitive,
                IntegLevel::Attested,
            )
            .is_err(),
            "a child lacking cap_declassify cannot declassify upward"
        );
    }

    #[test]
    fn return_endorsed_debits_recipient_budget() {
        let st = parent_child_state();
        let bg = BackgroundTheoryBuilder::new().build();
        // The child is untainted, so declaring (Sensitive, Attested) is an over-declaration --
        // legal (coverage only requires the declaration to BOUND the held sets) and produces the
        // same weight (declass_weight(Sensitive) + integ_weight(Attested) = 2 + 0 = 2) the old
        // flat debit charged.
        let (st, _) = return_endorsed(
            st,
            &bg,
            &ConformsAll,
            AgentId::new("c"),
            AgentId::new("p"),
            ConfLevel::Sensitive,
            IntegLevel::Attested,
        )
        .unwrap();
        assert_eq!(
            st.budget(&AgentId::new("p")),
            BUDGET_CAPACITY - 2,
            "return_endorsed charges the RECIPIENT (parent) the declared weight"
        );
    }

    #[test]
    fn return_endorsed_budget_drains_then_refuses() {
        let mut st = parent_child_state();
        let bg = BackgroundTheoryBuilder::new().build();
        // Eight endorsed returns (each costs declass_weight(Sensitive) + integ_weight(Attested) =
        // 2) drain the parent's per-subtree budget (16).
        for _ in 0..8 {
            let (s, _) = return_endorsed(
                st,
                &bg,
                &ConformsAll,
                AgentId::new("c"),
                AgentId::new("p"),
                ConfLevel::Sensitive,
                IntegLevel::Attested,
            )
            .unwrap();
            st = s;
        }
        assert!(!st.affordable(&AgentId::new("p"), 2));
        assert!(
            return_endorsed(
                st,
                &bg,
                &ConformsAll,
                AgentId::new("c"),
                AgentId::new("p"),
                ConfLevel::Sensitive,
                IntegLevel::Attested,
            )
            .is_err(),
            "the next endorsed return is refused -- caller must fall back to return_unendorsed"
        );
    }

    #[test]
    fn return_endorsed_conf_coverage_rejects_under_declaration() {
        // Scenario 10: the child holds Sensitive taint; declaring a clvl strictly below it fails
        // coverage.
        let mut st = parent_child_state();
        st
            .taint_levels
            .insert(AgentId::new("c"), VecSet::from([ConfLevel::Sensitive]));
        let bg = BackgroundTheoryBuilder::new().build();
        let result = return_endorsed(
            st,
            &bg,
            &ConformsAll,
            AgentId::new("c"),
            AgentId::new("p"),
            ConfLevel::Internal,
            IntegLevel::Attested,
        );
        assert_eq!(result.unwrap_err(), KernelError::DeclarationNotCovering);
    }

    #[test]
    fn return_endorsed_conf_coverage_accepts_bounding_declaration() {
        // A declaration that bounds the held taint set (Restricted >= Sensitive) is accepted and
        // debits the parent the declared weight -- closing the child-laundering arbitrage.
        let mut st = parent_child_state();
        st
            .taint_levels
            .insert(AgentId::new("c"), VecSet::from([ConfLevel::Sensitive]));
        let bg = BackgroundTheoryBuilder::new().build();
        let (st, _) = return_endorsed(
            st,
            &bg,
            &ConformsAll,
            AgentId::new("c"),
            AgentId::new("p"),
            ConfLevel::Restricted,
            IntegLevel::Attested,
        )
        .expect("Restricted bounds the held Sensitive taint level");
        assert_eq!(
            st.budget(&AgentId::new("p")),
            BUDGET_CAPACITY
                - (declass_weight(ConfLevel::Restricted) + integ_weight(IntegLevel::Attested)),
            "debit follows the declaration, not the held set"
        );
    }

    #[test]
    fn return_endorsed_integ_coverage_rejects_over_declaration() {
        // The child holds Standard integrity; declaring ilvl Trusted (above the held level)
        // fails the lower-bound coverage -- integrity is a min lattice.
        let mut st = parent_child_state();
        st
            .integ_levels
            .insert(AgentId::new("c"), VecSet::from([IntegLevel::Standard]));
        let bg = BackgroundTheoryBuilder::new().build();
        let result = return_endorsed(
            st,
            &bg,
            &ConformsAll,
            AgentId::new("c"),
            AgentId::new("p"),
            ConfLevel::Public,
            IntegLevel::Trusted,
        );
        assert_eq!(result.unwrap_err(), KernelError::DeclarationNotCovering);
    }

    #[test]
    fn return_endorsed_integ_coverage_accepts_bounding_declaration() {
        let mut st = parent_child_state();
        st
            .integ_levels
            .insert(AgentId::new("c"), VecSet::from([IntegLevel::Standard]));
        let bg = BackgroundTheoryBuilder::new().build();
        assert!(
            return_endorsed(
                st.clone(),
                &bg,
                &ConformsAll,
                AgentId::new("c"),
                AgentId::new("p"),
                ConfLevel::Public,
                IntegLevel::Standard,
            )
            .is_ok(),
            "ilvl == the held level bounds it"
        );
        assert!(
            return_endorsed(
                st,
                &bg,
                &ConformsAll,
                AgentId::new("c"),
                AgentId::new("p"),
                ConfLevel::Public,
                IntegLevel::Untrusted,
            )
            .is_ok(),
            "ilvl below the held level still lower-bounds it"
        );
    }

    #[test]
    fn return_endorsed_lever_floor_denies_untrusted_child() {
        // Scenario 4: lever floors set to (Trusted, Trusted); a child holding Untrusted
        // integrity fails the strict arm and does not clear the inspect band either.
        let mut st = parent_child_state();
        st
            .integ_levels
            .insert(AgentId::new("c"), VecSet::from([IntegLevel::Untrusted]));
        let mut builder = BackgroundTheoryBuilder::new();
        builder.set_lever_floors(IntegLevel::Trusted, IntegLevel::Trusted);
        let bg = builder.build();
        let result = return_endorsed(
            st,
            &bg,
            &ConformsAll,
            AgentId::new("c"),
            AgentId::new("p"),
            ConfLevel::Public,
            IntegLevel::Untrusted,
        );
        assert_eq!(result.unwrap_err(), KernelError::LeverIntegrityDenied);
    }

    #[test]
    fn return_endorsed_lever_floor_allows_trusted_child() {
        let mut st = parent_child_state();
        st
            .integ_levels
            .insert(AgentId::new("c"), VecSet::from([IntegLevel::Trusted]));
        let mut builder = BackgroundTheoryBuilder::new();
        builder.set_lever_floors(IntegLevel::Trusted, IntegLevel::Trusted);
        let bg = builder.build();
        assert!(
            return_endorsed(
                st,
                &bg,
                &ConformsAll,
                AgentId::new("c"),
                AgentId::new("p"),
                ConfLevel::Public,
                IntegLevel::Trusted,
            )
            .is_ok(),
            "a child clearing the strict floor may declassify"
        );
    }

    #[test]
    fn return_endorsed_lever_inspect_band_vouched_by_return_conforms() {
        // Floors (Attested, Trusted): a child holding Trusted sits in the inspect band and is
        // rescued by return_conforms (already required above -- the vouch is honest but
        // redundant, kept for shape-fidelity per design §5.5).
        let mut st = parent_child_state();
        st
            .integ_levels
            .insert(AgentId::new("c"), VecSet::from([IntegLevel::Trusted]));
        let mut builder = BackgroundTheoryBuilder::new();
        builder.set_lever_floors(IntegLevel::Attested, IntegLevel::Trusted);
        let bg = builder.build();
        assert!(
            return_endorsed(
                st.clone(),
                &bg,
                &ConformsAll,
                AgentId::new("c"),
                AgentId::new("p"),
                ConfLevel::Public,
                IntegLevel::Trusted,
            )
            .is_ok(),
            "inspect band + return_conforms vouch admits the declassification"
        );
        // With a non-conforming oracle, NotConforming fires first (the earlier require) --
        // the inspect-band vouch is never reached.
        let result = return_endorsed(
            st,
            &bg,
            &ConformsNone,
            AgentId::new("c"),
            AgentId::new("p"),
            ConfLevel::Public,
            IntegLevel::Trusted,
        );
        assert_eq!(result.unwrap_err(), KernelError::NotConforming);
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
            .insert(parent_inv.clone(), parent_tool.clone());
        st
            .invocation_egress
            .insert(parent_inv, VecSet::from([EgressKind::NetworkExternal]));

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
            VecSet::new(),
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
                VecSet::new(),
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
                VecSet::new(),
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
                VecSet::new(),
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
                VecSet::new(),
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
                _: &InvocationId,
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
                VecSet::new(),
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
                VecSet::from([EgressKind::NetworkExternal]),
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
                VecSet::from([EgressKind::NetworkExternal]),
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
            VecSet::from([EgressKind::NetworkExternal]),
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
            VecSet::from([EgressKind::NetworkExternal]),
        );
        assert!(
            result.is_err(),
            "second invoke_start must fail: single-use override already spent"
        );
    }

    #[test]
    fn invoke_start_eager_consumption_when_flow_allows() {
        // Design §7 scenario 15 (first half): an override armed for (tool, L) is consumed by
        // invoke_start even when the flow is admissible via ALLOW anyway (eager consumption,
        // Actions.lean:187-196) -- consumption does not depend on which arm admitted the flow.
        let mut st = state_with_agent("a1", &[CapKind::NetworkEgress]);
        st
            .taint_levels
            .insert(AgentId::new("a1"), VecSet::from([ConfLevel::Sensitive]));
        // Override seeded into state; ALLOW alone would already admit the flow without it.
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
        // Both relevant pairs ALLOW (ceiling at Sensitive) -> the override is never the sole
        // justification, but eager consumption burns it anyway.
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
            VecSet::from([EgressKind::NetworkExternal]),
        )
        .expect("invoke_start should pass via ALLOW");
        assert!(
            st.override_consumed(
                &AgentId::new("a1"),
                &ToolId::new("send_email"),
                ConfLevel::Sensitive
            ),
            "eager consumption burns the override even when ALLOW already permits the flow"
        );

        // Re-arm restores (design finding 12): free the in-flight slot then re-arm via
        // grant_override; override_consumed reports false again.
        let (st, _) = invoke_complete(
            st,
            &bg,
            &ConformsAll,
            AgentId::new("a1"),
            InvocationId::new("inv-1"),
        )
        .expect("invoke_complete should succeed");
        let (st, _) = grant_override(
            st,
            &bg,
            AgentId::root(),
            AgentId::new("a1"),
            ToolId::new("send_email"),
            ConfLevel::Sensitive,
        )
        .expect("re-arm should succeed with no in-flight");
        assert!(
            !st.override_consumed(
                &AgentId::new("a1"),
                &ToolId::new("send_email"),
                ConfLevel::Sensitive
            ),
            "re-arm restores override_consumed to false"
        );
    }

    #[test]
    fn invoke_start_consumes_override_with_empty_egress_no_conjunct() {
        // Design finding 12 / Actions.lean:187-196 clause 2a: consumption has no egress
        // conjunct. A tool with an EMPTY attested egress set still consumes an armed override
        // when the agent holds the taint level the override was armed for -- the gate is
        // vacuous (nothing to deny), but the override is examined and burned regardless.
        let mut st = state_with_agent("a1", &[]);
        st.tool_registered.insert(ToolId::new("no_egress_tool"));
        st
            .taint_levels
            .insert(AgentId::new("a1"), VecSet::from([ConfLevel::Sensitive]));
        st.flow_override.insert_into(
            AgentId::new("a1"),
            OverrideKey { tool: ToolId::new("no_egress_tool"), level: ConfLevel::Sensitive },
        );

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("no_egress_tool"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        let bg = builder.build();

        let (st, _) = invoke_start(
            st,
            &bg,
            &AllowAll,
            &FailAll,
            AgentId::new("a1"),
            ToolId::new("no_egress_tool"),
            InvocationId::new("inv-1"),
            VecSet::new(),
        )
        .expect("gates are vacuous with empty egress: invoke_start succeeds");

        assert!(
            st.override_consumed(
                &AgentId::new("a1"),
                &ToolId::new("no_egress_tool"),
                ConfLevel::Sensitive
            ),
            "clause 2a has no egress conjunct: consumed even with an empty egress set"
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
        st.in_flight.insert_into(parent.clone(), inv.clone());
        st
            .invocation_egress
            .insert(inv, VecSet::from([EgressKind::NetworkExternal]));
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
        st.in_flight.insert_into(agent.clone(), inv.clone());
        st
            .invocation_egress
            .insert(inv, VecSet::from([EgressKind::NetworkExternal]));

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
            .insert(email_inv.clone(), ToolId::new("send_email"));
        st
            .invocation_egress
            .insert(email_inv, VecSet::from([EgressKind::NetworkExternal]));

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
                VecSet::new(),
            )
            .is_err()
        );
    }

    #[test]
    fn invoke_start_check_2b_vouch_keys_the_in_flight_invocation_not_the_new_one() {
        // Oracle verdict keying pin (design finding 13): CHECK 2b's content-gate vouch must
        // key the IN-FLIGHT invocation being re-examined against the new floor, not the
        // invocation being started. A ContentGateOracle that passes for exactly one
        // InvocationId distinguishes correct per-invocation keying from the old per-tool
        // keying, which would have keyed on the new invocation instead.
        struct PassesOnly(InvocationId);
        impl ContentGateOracle for PassesOnly {
            fn passes(
                &self,
                _: &AgentId,
                _: &ToolId,
                inv: &InvocationId,
                _: &KernelState,
                _: &BackgroundTheory,
            ) -> bool {
                *inv == self.0
            }
        }

        fn setup() -> (KernelState, BackgroundTheory) {
            let mut st = state_with_agent("a1", &[CapKind::FilesystemRead, CapKind::NetworkEgress]);
            let email_inv = InvocationId::new("email-inv");
            st
                .in_flight
                .insert_into(AgentId::new("a1"), email_inv.clone());
            st
                .invocation_tool
                .insert(email_inv.clone(), ToolId::new("send_email"));
            st
                .invocation_egress
                .insert(email_inv, VecSet::from([EgressKind::NetworkExternal]));

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
            // (Sensitive, NetworkExternal) sits in the inspect band, so CHECK 2b's admission
            // depends entirely on the content-gate vouch.
            builder.set_egress_ceilings(
                EgressKind::NetworkExternal,
                Some(ConfLevel::Public),
                Some(ConfLevel::Sensitive),
            );
            (st, builder.build())
        }

        let new_inv = InvocationId::new("new-inv");
        let email_inv = InvocationId::new("email-inv");

        // The oracle accepts only the FLIGHT invocation: correct keying admits the flow.
        let (st, bg) = setup();
        assert!(
            invoke_start(
                st,
                &bg,
                &AllowAll,
                &PassesOnly(email_inv),
                AgentId::new("a1"),
                ToolId::new("read_file"),
                new_inv.clone(),
                VecSet::new(),
            )
            .is_ok(),
            "CHECK 2b must vouch with the in-flight invocation's content-gate verdict"
        );

        // The oracle accepts only the NEW invocation: the old per-tool keying would have
        // wrongly admitted this flow.
        let (st, bg) = setup();
        assert!(
            invoke_start(
                st,
                &bg,
                &AllowAll,
                &PassesOnly(new_inv.clone()),
                AgentId::new("a1"),
                ToolId::new("read_file"),
                new_inv,
                VecSet::new(),
            )
            .is_err(),
            "CHECK 2b must not accept a vouch keyed on the new invocation"
        );
    }

    #[test]
    fn invoke_start_rejects_replayed_invocation() {
        // Design §7 scenario 13: reusing an InvocationId that is already in `invocation_used`
        // is rejected by freshness even though `invocation_tool` never recorded it (the id was
        // never actually completed through invoke_start -- freshness is independent history).
        let mut st = state_with_agent("a1", &[CapKind::FilesystemRead]);
        st.invocation_used.insert(InvocationId::new("inv-1"));
        let bg = bg_with_tools();

        let result = invoke_start(
            st,
            &bg,
            &AllowAll,
            &PassAll,
            AgentId::new("a1"),
            ToolId::new("read_file"),
            InvocationId::new("inv-1"),
            VecSet::new(),
        );
        assert_eq!(result.unwrap_err(), KernelError::InvocationReplayed);
    }

    #[test]
    fn invoke_start_rejects_narrowing_violation() {
        // Design §7 scenario 12 (narrowing): an attested egress kind outside the tool's
        // declared set is rejected -- a lying classifier cannot mint egress kinds the tool
        // never declared.
        let st = state_with_agent("a1", &[CapKind::NetworkEgress]);
        let bg = bg_with_tools();

        let result = invoke_start(
            st,
            &bg,
            &AllowAll,
            &PassAll,
            AgentId::new("a1"),
            ToolId::new("send_email"),
            InvocationId::new("inv-1"),
            VecSet::from([EgressKind::FilesystemWrite]),
        );
        assert_eq!(result.unwrap_err(), KernelError::AttestationInvalid);
    }

    #[test]
    fn invoke_start_rejects_coverage_violation_but_allows_empty_on_no_egress_tool() {
        // Design §7 scenario 12 (coverage): an egress-bearing tool cannot be admitted on an
        // empty attestation (which would pass every flow gate vacuously); a no-egress tool is
        // unaffected by an empty attestation.
        let st = state_with_agent("a1", &[CapKind::NetworkEgress]);
        let bg = bg_with_tools();
        let result = invoke_start(
            st,
            &bg,
            &AllowAll,
            &PassAll,
            AgentId::new("a1"),
            ToolId::new("send_email"),
            InvocationId::new("inv-1"),
            VecSet::new(),
        );
        assert_eq!(result.unwrap_err(), KernelError::AttestationInvalid);

        let st = state_with_agent("a1", &[CapKind::FilesystemRead]);
        let bg = bg_with_tools();
        assert!(
            invoke_start(
                st,
                &bg,
                &AllowAll,
                &PassAll,
                AgentId::new("a1"),
                ToolId::new("check_exists"),
                InvocationId::new("inv-1"),
                VecSet::new(),
            )
            .is_ok(),
            "empty attestation on a no-egress tool is fine"
        );
    }

    #[test]
    fn invoke_start_success_populates_invocation_used_and_egress() {
        let st = state_with_agent("a1", &[CapKind::FilesystemRead]);
        let bg = bg_with_tools();
        let inv = InvocationId::new("inv-1");

        let (new_state, _) = invoke_start(
            st,
            &bg,
            &AllowAll,
            &PassAll,
            AgentId::new("a1"),
            ToolId::new("read_file"),
            inv.clone(),
            VecSet::new(),
        )
        .unwrap();

        assert!(new_state.invocation_used.contains(&inv));
        assert_eq!(new_state.invocation_egress.get(&inv), Some(&VecSet::new()));
    }

    #[test]
    fn invoke_start_precision_win_narrow_attestation_admits_where_full_set_denies() {
        // Design §7 scenario 11: a tainted agent invoking a tool that declares two egress kinds
        // is denied under the V2-equivalent full-set attestation (one of the kinds is DENY at
        // the held taint level), but succeeds when the attestation narrows to only the ALLOWed
        // kind -- the precision win per-invocation attestation buys over the static worst case.
        fn setup() -> (KernelState, BackgroundTheory) {
            let mut st = state_with_agent("a1", &[]);
            st.taint_levels.insert(AgentId::new("a1"), VecSet::from([ConfLevel::Sensitive]));
            st.tool_registered.insert(ToolId::new("dyn_tool"));

            let mut builder = BackgroundTheoryBuilder::new();
            builder.trust_issuer(IssuerId::new("trusted"));
            builder.register_tool(
                ToolId::new("dyn_tool"),
                ToolMetadata {
                    capabilities: VecSet::new(),
                    egress: VecSet::from([EgressKind::NetworkExternal, EgressKind::NetworkInternal]),
                    conf_floor: ConfLevel::Public,
                    output_bounded: false,
                    issuer: IssuerId::new("trusted"),
                    integ_floor: IntegLevel::Untrusted,
                    integ_inspect_floor: IntegLevel::Untrusted,
                    output_integ: IntegLevel::Attested,
                },
            );
            // NetworkExternal denies Sensitive; NetworkInternal allows it.
            builder.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Public), None);
            builder.set_egress_ceilings(EgressKind::NetworkInternal, Some(ConfLevel::Sensitive), None);
            (st, builder.build())
        }

        let (st, bg) = setup();
        assert!(
            invoke_start(
                st,
                &bg,
                &AllowAll,
                &FailAll,
                AgentId::new("a1"),
                ToolId::new("dyn_tool"),
                InvocationId::new("inv-1"),
                VecSet::from([EgressKind::NetworkExternal, EgressKind::NetworkInternal]),
            )
            .is_err(),
            "the full declared egress set (V2-equivalent worst case) is denied"
        );

        let (st, bg) = setup();
        assert!(
            invoke_start(
                st,
                &bg,
                &AllowAll,
                &FailAll,
                AgentId::new("a1"),
                ToolId::new("dyn_tool"),
                InvocationId::new("inv-1"),
                VecSet::from([EgressKind::NetworkInternal]),
            )
            .is_ok(),
            "a narrower attestation covering only the ALLOWed kind succeeds"
        );
    }

    #[test]
    fn invoke_start_check_2b_gates_over_stored_attestation_not_static_egress() {
        // Design finding 4/6 precision pin: CHECK 2b must gate over the in-flight invocation's
        // STORED attestation, not the flight tool's static declared egress set.
        fn setup() -> (KernelState, BackgroundTheory) {
            let mut st = state_with_agent("a1", &[]);
            st.tool_registered.insert(ToolId::new("flight_tool"));
            st.tool_registered.insert(ToolId::new("new_tool"));
            let flight_inv = InvocationId::new("flight-inv");
            st.in_flight.insert_into(AgentId::new("a1"), flight_inv.clone());
            st.invocation_tool.insert(flight_inv, ToolId::new("flight_tool"));

            let mut builder = BackgroundTheoryBuilder::new();
            builder.trust_issuer(IssuerId::new("trusted"));
            builder.register_tool(
                ToolId::new("flight_tool"),
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
            builder.register_tool(
                ToolId::new("new_tool"),
                ToolMetadata {
                    capabilities: VecSet::new(),
                    egress: VecSet::new(),
                    conf_floor: ConfLevel::Sensitive,
                    output_bounded: false,
                    issuer: IssuerId::new("trusted"),
                    integ_floor: IntegLevel::Untrusted,
                    integ_inspect_floor: IntegLevel::Untrusted,
                    output_integ: IntegLevel::Attested,
                },
            );
            // Sensitive/NetworkExternal is DENY: the flight tool's static declared egress would
            // have blocked CHECK 2b if it were still the gate's egress source.
            builder.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Public), None);
            (st, builder.build())
        }

        // Stored attestation empty (narrower than flight_tool's declared set): CHECK 2b is
        // vacuous, so the new invoke is NOT blocked by the flight's static egress.
        let (st, bg) = setup();
        assert!(
            invoke_start(
                st,
                &bg,
                &AllowAll,
                &FailAll,
                AgentId::new("a1"),
                ToolId::new("new_tool"),
                InvocationId::new("new-inv"),
                VecSet::new(),
            )
            .is_ok(),
            "CHECK 2b must gate over the stored attestation, not the flight tool's static egress"
        );

        // Contrast: a stored attestation matching the flight's declared egress still blocks.
        let (mut st, bg) = setup();
        st.invocation_egress.insert(
            InvocationId::new("flight-inv"),
            VecSet::from([EgressKind::NetworkExternal]),
        );
        assert!(
            invoke_start(
                st,
                &bg,
                &AllowAll,
                &FailAll,
                AgentId::new("a1"),
                ToolId::new("new_tool"),
                InvocationId::new("new-inv"),
                VecSet::new(),
            )
            .is_err(),
            "with a matching stored attestation, CHECK 2b still blocks"
        );
    }

    // --- invoke_start: CHECK 4 (integrity gate) ---

    #[test]
    fn invoke_start_check_4a_denies_untrusted_agent_below_trusted_floor() {
        let mut st = state_with_agent("a1", &[]);
        st.tool_registered.insert(ToolId::new("trusted_tool"));
        st.integ_levels.insert(AgentId::new("a1"), VecSet::from([IntegLevel::Untrusted]));

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("trusted_tool"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Trusted,
                integ_inspect_floor: IntegLevel::Trusted,
                output_integ: IntegLevel::Attested,
            },
        );
        let bg = builder.build();

        let result = invoke_start(
            st,
            &bg,
            &AllowAll,
            &FailAll,
            AgentId::new("a1"),
            ToolId::new("trusted_tool"),
            InvocationId::new("inv-1"),
            VecSet::new(),
        );
        assert_eq!(result.unwrap_err(), KernelError::IntegrityFloorDenied);
    }

    #[test]
    fn invoke_start_check_4a_inspect_band_allows_with_passing_vouch() {
        let mut st = state_with_agent("a1", &[]);
        st.tool_registered.insert(ToolId::new("trusted_tool"));
        st.integ_levels.insert(AgentId::new("a1"), VecSet::from([IntegLevel::Untrusted]));

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("trusted_tool"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Trusted,
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
                &PassAll,
                AgentId::new("a1"),
                ToolId::new("trusted_tool"),
                InvocationId::new("inv-1"),
                VecSet::new(),
            )
            .is_ok(),
            "inspect band + a passing content-gate vouch admits below the floor"
        );
    }

    #[test]
    fn invoke_start_check_4a_speculative_blocks_before_completion() {
        // 4a speculative: an in-flight tool's UNTRUSTED emission counts even before it
        // completes (worst-case speculative_integ), not just held integ_levels.
        let mut st = state_with_agent("a1", &[]);
        st.tool_registered.insert(ToolId::new("web_fetch"));
        st.tool_registered.insert(ToolId::new("delete_repo"));
        let flight_inv = InvocationId::new("wf-inv");
        st.in_flight.insert_into(AgentId::new("a1"), flight_inv.clone());
        st.invocation_tool.insert(flight_inv, ToolId::new("web_fetch"));

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("web_fetch"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Untrusted,
            },
        );
        builder.register_tool(
            ToolId::new("delete_repo"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Trusted,
                integ_inspect_floor: IntegLevel::Trusted,
                output_integ: IntegLevel::Attested,
            },
        );
        let bg = builder.build();

        let result = invoke_start(
            st,
            &bg,
            &AllowAll,
            &FailAll,
            AgentId::new("a1"),
            ToolId::new("delete_repo"),
            InvocationId::new("dr-inv"),
            VecSet::new(),
        );
        assert_eq!(result.unwrap_err(), KernelError::IntegrityFloorDenied);
    }

    #[test]
    fn invoke_start_check_4b_new_emission_vs_inflight_floor_denies() {
        // 4b: the "web_fetch completes while delete_repo is in flight" hazard, from the other
        // side -- delete_repo (Trusted floor) already in flight, THEN invoking web_fetch
        // (Untrusted emission) is denied: the in-flight tool's floor gates the new emission.
        let mut st = state_with_agent("a1", &[]);
        st.tool_registered.insert(ToolId::new("delete_repo"));
        st.tool_registered.insert(ToolId::new("web_fetch"));
        let flight_inv = InvocationId::new("dr-inv");
        st.in_flight.insert_into(AgentId::new("a1"), flight_inv.clone());
        st.invocation_tool.insert(flight_inv, ToolId::new("delete_repo"));

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("delete_repo"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Trusted,
                integ_inspect_floor: IntegLevel::Trusted,
                output_integ: IntegLevel::Attested,
            },
        );
        builder.register_tool(
            ToolId::new("web_fetch"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Untrusted,
            },
        );
        let bg = builder.build();

        let result = invoke_start(
            st,
            &bg,
            &AllowAll,
            &FailAll,
            AgentId::new("a1"),
            ToolId::new("web_fetch"),
            InvocationId::new("wf-inv"),
            VecSet::new(),
        );
        assert_eq!(result.unwrap_err(), KernelError::IntegrityFloorDenied);
    }

    #[test]
    fn invoke_start_check_4b_vouch_keys_the_in_flight_invocation() {
        // Oracle verdict keying pin (integrity dual of the CHECK 2b vouch-keying pin): CHECK
        // 4b's content-gate vouch must key the IN-FLIGHT invocation whose floor is being
        // crossed, not the invocation being started.
        struct PassesOnly(InvocationId);
        impl ContentGateOracle for PassesOnly {
            fn passes(
                &self,
                _: &AgentId,
                _: &ToolId,
                inv: &InvocationId,
                _: &KernelState,
                _: &BackgroundTheory,
            ) -> bool {
                *inv == self.0
            }
        }

        fn setup() -> (KernelState, BackgroundTheory) {
            let mut st = state_with_agent("a1", &[]);
            st.tool_registered.insert(ToolId::new("delete_repo"));
            st.tool_registered.insert(ToolId::new("web_fetch"));
            let flight_inv = InvocationId::new("dr-inv");
            st.in_flight.insert_into(AgentId::new("a1"), flight_inv.clone());
            st.invocation_tool.insert(flight_inv, ToolId::new("delete_repo"));

            let mut builder = BackgroundTheoryBuilder::new();
            builder.trust_issuer(IssuerId::new("trusted"));
            builder.register_tool(
                ToolId::new("delete_repo"),
                ToolMetadata {
                    capabilities: VecSet::new(),
                    egress: VecSet::new(),
                    conf_floor: ConfLevel::Public,
                    output_bounded: false,
                    issuer: IssuerId::new("trusted"),
                    integ_floor: IntegLevel::Trusted,
                    // Inspect band open down to Untrusted -- CHECK 4b's admission depends
                    // entirely on the content-gate vouch.
                    integ_inspect_floor: IntegLevel::Untrusted,
                    output_integ: IntegLevel::Attested,
                },
            );
            builder.register_tool(
                ToolId::new("web_fetch"),
                ToolMetadata {
                    capabilities: VecSet::new(),
                    egress: VecSet::new(),
                    conf_floor: ConfLevel::Public,
                    output_bounded: false,
                    issuer: IssuerId::new("trusted"),
                    integ_floor: IntegLevel::Untrusted,
                    integ_inspect_floor: IntegLevel::Untrusted,
                    output_integ: IntegLevel::Untrusted,
                },
            );
            (st, builder.build())
        }

        let new_inv = InvocationId::new("wf-inv");
        let flight_inv = InvocationId::new("dr-inv");

        // The oracle accepts only the FLIGHT invocation: correct keying admits the flow.
        let (st, bg) = setup();
        assert!(
            invoke_start(
                st,
                &bg,
                &AllowAll,
                &PassesOnly(flight_inv),
                AgentId::new("a1"),
                ToolId::new("web_fetch"),
                new_inv.clone(),
                VecSet::new(),
            )
            .is_ok(),
            "CHECK 4b must vouch with the in-flight invocation's content-gate verdict"
        );

        // The oracle accepts only the NEW invocation: keying on the new invocation must not
        // rescue the crossing.
        let (st, bg) = setup();
        assert!(
            invoke_start(
                st,
                &bg,
                &AllowAll,
                &PassesOnly(new_inv.clone()),
                AgentId::new("a1"),
                ToolId::new("web_fetch"),
                new_inv,
                VecSet::new(),
            )
            .is_err(),
            "CHECK 4b must not accept a vouch keyed on the new invocation"
        );
    }

    #[test]
    fn invoke_start_check_4c_self_pair_denies_even_for_clean_agent() {
        // 4c: a tool whose own emission fails its own floor is denied even for a clean agent
        // with nothing in flight (the self-pair, needed for inductiveness of the pairwise
        // in-flight invariant).
        let mut st = state_with_agent("a1", &[]);
        st.tool_registered.insert(ToolId::new("self_conflicted"));

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("self_conflicted"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Trusted,
                integ_inspect_floor: IntegLevel::Trusted,
                output_integ: IntegLevel::Untrusted,
            },
        );
        let bg = builder.build();

        let result = invoke_start(
            st,
            &bg,
            &AllowAll,
            &FailAll,
            AgentId::new("a1"),
            ToolId::new("self_conflicted"),
            InvocationId::new("inv-1"),
            VecSet::new(),
        );
        assert_eq!(result.unwrap_err(), KernelError::IntegrityFloorDenied);
    }

    #[test]
    fn invoke_start_check_4_denial_not_rescued_by_flow_override() {
        // No-override pin: CHECK 4 has no override arm anywhere -- an armed flow_override for
        // the tool's own (tool, conf_floor) pair does not rescue an integrity-floor denial.
        let mut st = state_with_agent("a1", &[]);
        st.tool_registered.insert(ToolId::new("trusted_tool"));
        st.integ_levels.insert(AgentId::new("a1"), VecSet::from([IntegLevel::Untrusted]));
        st.flow_override.insert_into(
            AgentId::new("a1"),
            OverrideKey { tool: ToolId::new("trusted_tool"), level: ConfLevel::Public },
        );

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("trusted_tool"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Trusted,
                integ_inspect_floor: IntegLevel::Trusted,
                output_integ: IntegLevel::Attested,
            },
        );
        let bg = builder.build();

        let result = invoke_start(
            st,
            &bg,
            &AllowAll,
            &FailAll,
            AgentId::new("a1"),
            ToolId::new("trusted_tool"),
            InvocationId::new("inv-1"),
            VecSet::new(),
        );
        assert_eq!(
            result.unwrap_err(),
            KernelError::IntegrityFloorDenied,
            "an armed flow_override must not rescue a CHECK 4 denial"
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
        // Root starts at full capacity; after grant_override it should be debited by
        // declass_weight(level).
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

        assert_eq!(
            st.budget(&granter),
            BUDGET_CAPACITY - declass_weight(ConfLevel::Sensitive),
            "granter debited by declass_weight(level)"
        );
        assert_eq!(st.budget(&target), target_budget_before, "target budget untouched");
    }

    #[test]
    fn grant_override_public_level_is_free() {
        let target = AgentId::new("t");
        let mut st = KernelState::initial();
        st.agent_active.insert(target.clone());
        st.agent_budget.insert(AgentId::root(), 0);

        let bg = BackgroundTheoryBuilder::new().build();

        let (st, _) = grant_override(
            st,
            &bg,
            AgentId::root(),
            target,
            ToolId::new("t"),
            ConfLevel::Public,
        )
        .expect("public-level overrides are free -- affordable even at budget 0");
        assert_eq!(st.budget(&AgentId::root()), 0);
    }

    #[test]
    fn grant_override_restricted_debits_four() {
        let target = AgentId::new("t");
        let mut st = KernelState::initial();
        st.agent_active.insert(target.clone());

        let bg = BackgroundTheoryBuilder::new().build();
        let (st, _) = grant_override(
            st,
            &bg,
            AgentId::root(),
            target,
            ToolId::new("t"),
            ConfLevel::Restricted,
        )
        .expect("grant_override should succeed");
        assert_eq!(st.budget(&AgentId::root()), BUDGET_CAPACITY - 4);
    }

    #[test]
    fn grant_override_restricted_refused_at_low_budget() {
        let target = AgentId::new("t");
        let mut st = KernelState::initial();
        st.agent_active.insert(target.clone());
        st.agent_budget.insert(AgentId::root(), 3);

        let bg = BackgroundTheoryBuilder::new().build();
        let result = grant_override(
            st,
            &bg,
            AgentId::root(),
            target,
            ToolId::new("t"),
            ConfLevel::Restricted,
        );
        assert_eq!(result.unwrap_err(), KernelError::BudgetExhausted);
    }

    #[test]
    fn grant_override_strict_lever_floor_denies_degraded_granter() {
        let mut st = KernelState::initial();
        let target = AgentId::new("t");
        st.agent_active.insert(target.clone());
        st
            .integ_levels
            .insert(AgentId::root(), VecSet::from([IntegLevel::Untrusted]));

        let mut builder = BackgroundTheoryBuilder::new();
        builder.set_lever_floors(IntegLevel::Trusted, IntegLevel::Trusted);
        let bg = builder.build();

        // Passing content gate does not rescue: grant_override's lever floor is strict, no
        // vouch arm exists.
        let result = grant_override(
            st.clone(),
            &bg,
            AgentId::root(),
            target.clone(),
            ToolId::new("t"),
            ConfLevel::Sensitive,
        );
        assert_eq!(result.unwrap_err(), KernelError::LeverIntegrityDenied);

        st
            .integ_levels
            .insert(AgentId::root(), VecSet::from([IntegLevel::Trusted]));
        let (st, _) = grant_override(
            st,
            &bg,
            AgentId::root(),
            target,
            ToolId::new("t"),
            ConfLevel::Sensitive,
        )
        .expect("granter clearing the lever floor may arm the override");
        assert_eq!(st.budget(&AgentId::root()), BUDGET_CAPACITY - declass_weight(ConfLevel::Sensitive));
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
        st2
            .invocation_egress
            .insert(inv.clone(), VecSet::from([EgressKind::NetworkExternal]));

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
        st2.in_flight.insert_into(agent.clone(), inv2.clone());
        st2
            .invocation_egress
            .insert(inv2, VecSet::from([EgressKind::NetworkExternal]));

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
        assert_eq!(
            st.budget(&agent),
            budget_before - declass_weight(ConfLevel::Sensitive),
            "granter debited by declass_weight(level)"
        );
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
