use std::collections::BTreeSet;

use crate::background::{BackgroundTheory, FlowMode};
use crate::capability::CapKind;
use crate::error::KernelError;
use crate::event::KernelAction;
use crate::state::KernelState;
use crate::traits::{AuthorizerOracle, ConformanceOracle, ContentGateOracle};
use crate::types::{AgentId, ConfLevel, EgressKind, InstructionId, InvocationId, ToolId};

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
    state: &KernelState,
    level: ConfLevel,
    egress: EgressKind,
) -> FlowDecision {
    match bg.flow_mode(level, egress) {
        FlowMode::Allow => FlowDecision::Allowed,
        FlowMode::Inspect => {
            if content_gate.passes(agent, tool, state, bg) {
                FlowDecision::Allowed
            } else {
                FlowDecision::Denied
            }
        }
        FlowMode::Deny => {
            if bg.has_flow_override(agent, tool, level)
                && !state.override_consumed(agent, tool, level)
            {
                FlowDecision::ConsumedOverride
            } else {
                FlowDecision::Denied
            }
        }
    }
}

fn clear_agent_state(state: &mut KernelState, agent: &AgentId) {
    state.taint_levels.remove(agent);
    state.in_flight.remove(agent);
    state.gh_taint_invoked.remove(agent);
    state.gh_taint_received.remove(agent);
    state.agent_instruction.remove(agent);
    state.override_used.remove(agent);
    state.agent_budget.remove(agent);
}

pub fn register_tool(
    mut state: KernelState,
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
    if state.tool_registered.contains(&tool) {
        return Err(KernelError::ToolAlreadyRegistered);
    }

    state.tool_registered.insert(tool.clone());

    Ok((state, KernelAction::RegisterTool { tool }))
}

pub fn load_instruction(
    mut state: KernelState,
    bg: &BackgroundTheory,
    agent: AgentId,
    instr: InstructionId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !state.agent_active.contains(&agent) {
        return Err(KernelError::AgentInactive);
    }
    let issuer = match bg.instruction_issuer(&instr) {
        Some(issuer) => issuer.clone(),
        None => return Err(KernelError::InstructionIssuerUnknown),
    };
    if !bg.is_trusted_issuer(&issuer) {
        return Err(KernelError::UntrustedIssuer);
    }

    state
        .agent_instruction
        .entry(agent.clone())
        .or_default()
        .insert(instr.clone());

    Ok((state, KernelAction::LoadInstruction { agent, instr }))
}

pub fn delegate(
    mut state: KernelState,
    _bg: &BackgroundTheory,
    grantor: AgentId,
    grantee: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !state.agent_active.contains(&grantor) {
        return Err(KernelError::AgentInactive);
    }
    if state.agent_active.contains(&grantee) {
        return Err(KernelError::AgentAlreadyActive);
    }
    if grantee == AgentId::root() {
        return Err(KernelError::RootNotAllowed);
    }

    state.agent_active.insert(grantee.clone());
    state
        .agent_parent
        .retain(|child, parent| child != &grantee && parent != &grantee);
    state.agent_parent.insert(grantee.clone(), grantor.clone());
    state.agent_cap.insert(grantee.clone(), BTreeSet::new());
    clear_agent_state(&mut state, &grantee);

    Ok((state, KernelAction::Delegate { grantor, grantee }))
}

pub fn grant_capability(
    mut state: KernelState,
    _bg: &BackgroundTheory,
    parent: AgentId,
    child: AgentId,
    cap: CapKind,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !state.agent_active.contains(&parent) {
        return Err(KernelError::AgentInactive);
    }
    if !state.agent_active.contains(&child) {
        return Err(KernelError::AgentInactive);
    }
    if state.agent_parent.get(&child) != Some(&parent) {
        return Err(KernelError::NotDirectChild);
    }
    if !state
        .agent_cap
        .get(&parent)
        .is_some_and(|caps| caps.contains(&cap))
    {
        return Err(KernelError::CapabilityMissing);
    }

    state
        .agent_cap
        .entry(child.clone())
        .or_default()
        .insert(cap);

    Ok((state, KernelAction::GrantCapability { parent, child, cap }))
}

pub fn revoke(
    mut state: KernelState,
    _bg: &BackgroundTheory,
    parent: AgentId,
    target: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if state.agent_parent.get(&target) != Some(&parent) {
        return Err(KernelError::NotDirectChild);
    }
    if !state.agent_active.contains(&parent) {
        return Err(KernelError::AgentInactive);
    }
    if !state.agent_active.contains(&target) {
        return Err(KernelError::AgentInactive);
    }
    if target == AgentId::root() {
        return Err(KernelError::RootNotAllowed);
    }

    state.agent_active.remove(&target);
    state.agent_parent.retain(|child, _| child != &target);
    state.agent_cap.remove(&target);
    clear_agent_state(&mut state, &target);

    Ok((state, KernelAction::Revoke { parent, target }))
}

pub fn cascade_revoke(
    mut state: KernelState,
    _bg: &BackgroundTheory,
    child: AgentId,
    parent: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if state.agent_parent.get(&child) != Some(&parent) {
        return Err(KernelError::NotDirectChild);
    }
    if state.agent_active.contains(&parent) {
        return Err(KernelError::ParentStillActive);
    }
    if !state.agent_active.contains(&child) {
        return Err(KernelError::AgentInactive);
    }
    if child == AgentId::root() {
        return Err(KernelError::RootNotAllowed);
    }

    state.agent_active.remove(&child);
    state.agent_parent.retain(|c, _| c != &child);
    state.agent_cap.remove(&child);
    clear_agent_state(&mut state, &child);

    Ok((state, KernelAction::CascadeRevoke { child, parent }))
}

pub fn invoke_start<A: AuthorizerOracle, C: ContentGateOracle>(
    mut state: KernelState,
    bg: &BackgroundTheory,
    authorizer: &A,
    content_gate: &C,
    agent: AgentId,
    tool: ToolId,
    inv: InvocationId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !state.agent_active.contains(&agent) {
        return Err(KernelError::AgentInactive);
    }
    if agent == AgentId::root() {
        return Err(KernelError::RootNotAllowed);
    }
    if !state.tool_registered.contains(&tool) {
        return Err(KernelError::ToolNotRegistered);
    }
    if state.invocation_tool.contains_key(&inv) {
        return Err(KernelError::InvocationExists);
    }
    for flights in state.in_flight.values() {
        if flights.contains(&inv) {
            return Err(KernelError::InvocationInFlight);
        }
    }

    let tool_meta = bg.tool_metadata(&tool).ok_or(KernelError::ToolNotInTheory)?;

    let agent_caps = state.agent_cap.get(&agent);
    for required_cap in &tool_meta.capabilities {
        if !agent_caps.is_some_and(|caps| caps.contains(required_cap)) {
            return Err(KernelError::CapabilityMissing);
        }
    }

    // Override grants that are the *sole* justification for a flow this transition; spent
    // on success (single-use, MF-3). Keyed by (tool, level) for the invoking `agent`.
    let mut to_consume: BTreeSet<(ToolId, ConfLevel)> = BTreeSet::new();

    let spec_taint = state.speculative_taint(&agent, bg);
    for &level in &spec_taint {
        for &egress in &tool_meta.egress {
            match flow_decision(bg, content_gate, &agent, &tool, &state, level, egress) {
                FlowDecision::Allowed => {}
                FlowDecision::ConsumedOverride => {
                    to_consume.insert((tool.clone(), level));
                }
                FlowDecision::Denied => {
                    return Err(KernelError::FlowGateBlocked);
                }
            }
        }
    }

    // CHECK 2b/2c run for ALL tools -- bounded is NOT excluded. With conformance-gating a
    // bounded tool may still add taint on completion (if it fails conformance), so its floor
    // must be flow-compatible just like a non-bounded tool (worst-case / fail-closed).
    if let Some(agent_flights) = state.in_flight.get(&agent) {
        for flight_inv in agent_flights {
            if let Some(flight_tool_id) = state.invocation_tool.get(flight_inv)
                && let Some(flight_meta) = bg.tool_metadata(flight_tool_id)
            {
                for &egress in &flight_meta.egress {
                    match flow_decision(
                        bg,
                        content_gate,
                        &agent,
                        flight_tool_id,
                        &state,
                        tool_meta.conf_floor,
                        egress,
                    ) {
                        FlowDecision::Allowed => {}
                        FlowDecision::ConsumedOverride => {
                            to_consume.insert((flight_tool_id.clone(), tool_meta.conf_floor));
                        }
                        FlowDecision::Denied => {
                            return Err(KernelError::FlowGateBlocked);
                        }
                    }
                }
            }
        }
    }

    for &egress in &tool_meta.egress {
        match flow_decision(
            bg,
            content_gate,
            &agent,
            &tool,
            &state,
            tool_meta.conf_floor,
            egress,
        ) {
            FlowDecision::Allowed => {}
            FlowDecision::ConsumedOverride => {
                to_consume.insert((tool.clone(), tool_meta.conf_floor));
            }
            FlowDecision::Denied => {
                return Err(KernelError::FlowGateBlocked);
            }
        }
    }

    if !authorizer.allows(&agent, &tool, &state, bg) {
        return Err(KernelError::AuthorizerDenied);
    }

    if !to_consume.is_empty() {
        state
            .override_used
            .entry(agent.clone())
            .or_default()
            .extend(to_consume);
    }

    state.invocation_tool.insert(inv.clone(), tool.clone());
    state
        .in_flight
        .entry(agent.clone())
        .or_default()
        .insert(inv.clone());

    Ok((state, KernelAction::InvokeStart { agent, tool, inv }))
}

pub fn invoke_complete<F: ConformanceOracle>(
    mut state: KernelState,
    bg: &BackgroundTheory,
    conformance: &F,
    agent: AgentId,
    inv: InvocationId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !state
        .in_flight
        .get(&agent)
        .is_some_and(|flights| flights.contains(&inv))
    {
        return Err(KernelError::NotInFlight);
    }
    if !state.agent_active.contains(&agent) {
        return Err(KernelError::AgentInactive);
    }

    if let Some(flights) = state.in_flight.get_mut(&agent) {
        flights.remove(&inv);
    }

    if let Some(tool_id) = state.invocation_tool.get(&inv).cloned()
        && let Some(tmeta) = bg.tool_metadata(&tool_id)
    {
        let conf_floor = tmeta.conf_floor;
        // Zero-taint (endorsed) path = bounded declaration AND runtime conformance AND budget
        // available. Otherwise full taint at the tool's floor (fail-closed). Mirrors Veil
        // invoke_complete: a bounded-but-non-conforming or out-of-budget tool taints in full.
        let zero_taint = tmeta.output_bounded
            && conformance.conforms(&agent, &tool_id, &state, bg)
            && !state.budget_exhausted(&agent);
        if zero_taint {
            // Charge the agent's own budget for the in-agent declassification.
            state.debit_budget(&agent);
        } else {
            state
                .taint_levels
                .entry(agent.clone())
                .or_default()
                .insert(conf_floor);
            state
                .gh_taint_invoked
                .entry(agent.clone())
                .or_default()
                .insert(conf_floor);
        }
    }

    Ok((state, KernelAction::InvokeComplete { agent, inv }))
}

pub fn return_endorsed(
    mut state: KernelState,
    _bg: &BackgroundTheory,
    child: AgentId,
    parent: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if state.agent_parent.get(&child) != Some(&parent) {
        return Err(KernelError::NotDirectChild);
    }
    if !state.agent_active.contains(&child) {
        return Err(KernelError::AgentInactive);
    }
    if !state.agent_active.contains(&parent) {
        return Err(KernelError::AgentInactive);
    }
    if state
        .in_flight
        .get(&child)
        .is_some_and(|flights| !flights.is_empty())
    {
        return Err(KernelError::ChildHasInFlight);
    }
    // Cross-boundary declassification tier: the child must be authorised to declassify, and the
    // RECIPIENT (parent) is charged budget -- a per-agent bound on the parent's total endorsed
    // inflow across its whole subtree (smurfing defense). A child lacking the cap, or an
    // out-of-budget parent, must use return_unendorsed (full taint) instead.
    if !state
        .agent_cap
        .get(&child)
        .is_some_and(|caps| caps.contains(&CapKind::Declassify))
    {
        return Err(KernelError::CapabilityMissing);
    }
    if state.budget_exhausted(&parent) {
        return Err(KernelError::BudgetExhausted);
    }
    state.debit_budget(&parent);

    Ok((state, KernelAction::ReturnEndorsed { child, parent }))
}

pub fn return_unendorsed<C: ContentGateOracle>(
    mut state: KernelState,
    bg: &BackgroundTheory,
    content_gate: &C,
    child: AgentId,
    parent: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if state.agent_parent.get(&child) != Some(&parent) {
        return Err(KernelError::NotDirectChild);
    }
    if !state.agent_active.contains(&child) {
        return Err(KernelError::AgentInactive);
    }
    if !state.agent_active.contains(&parent) {
        return Err(KernelError::AgentInactive);
    }
    if state
        .in_flight
        .get(&child)
        .is_some_and(|flights| !flights.is_empty())
    {
        return Err(KernelError::ChildHasInFlight);
    }

    let child_taint = state.taint_levels.get(&child).cloned().unwrap_or_default();
    let empty_flights = BTreeSet::new();
    let parent_flights = state.in_flight.get(&parent).unwrap_or(&empty_flights);

    // Override grants spent on success (single-use, MF-3). Charged to the recipient `parent`.
    let mut to_consume: BTreeSet<(ToolId, ConfLevel)> = BTreeSet::new();
    for &level in &child_taint {
        for inv in parent_flights {
            if let Some(tool_id) = state.invocation_tool.get(inv)
                && let Some(tmeta) = bg.tool_metadata(tool_id)
            {
                for &egress in &tmeta.egress {
                    match flow_decision(bg, content_gate, &parent, tool_id, &state, level, egress) {
                        FlowDecision::Allowed => {}
                        FlowDecision::ConsumedOverride => {
                            to_consume.insert((tool_id.clone(), level));
                        }
                        FlowDecision::Denied => {
                            return Err(KernelError::FlowGateBlocked);
                        }
                    }
                }
            }
        }
    }

    if !child_taint.is_empty() {
        state
            .taint_levels
            .entry(parent.clone())
            .or_default()
            .extend(&child_taint);
        state
            .gh_taint_received
            .entry(parent.clone())
            .or_default()
            .extend(&child_taint);
    }

    if !to_consume.is_empty() {
        state
            .override_used
            .entry(parent.clone())
            .or_default()
            .extend(to_consume);
    }

    Ok((state, KernelAction::ReturnUnendorsed { child, parent }))
}

pub fn sentinel_elevate_taint<C: ContentGateOracle>(
    mut state: KernelState,
    bg: &BackgroundTheory,
    content_gate: &C,
    agent: AgentId,
    level: ConfLevel,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !state.agent_active.contains(&agent) {
        return Err(KernelError::AgentInactive);
    }

    // Override grants that are the *sole* justification for keeping an in-flight egress tool
    // legal under the raised taint; spent on success (single-use, MF-3) -- uniform with
    // invoke_start / return_unendorsed. A taint-raise that pushes an in-flight egress tool past a
    // DENY is exactly the one authorized exfil, so it consumes the exception.
    let mut to_consume: BTreeSet<(ToolId, ConfLevel)> = BTreeSet::new();
    if let Some(in_flight_invs) = state.in_flight.get(&agent) {
        for inv in in_flight_invs {
            let tool = state
                .invocation_tool
                .get(inv)
                .ok_or(KernelError::MissingToolBinding)?;
            if let Some(tmeta) = bg.tool_metadata(tool) {
                for &egress in &tmeta.egress {
                    match flow_decision(bg, content_gate, &agent, tool, &state, level, egress) {
                        FlowDecision::Allowed => {}
                        FlowDecision::ConsumedOverride => {
                            to_consume.insert((tool.clone(), level));
                        }
                        FlowDecision::Denied => {
                            return Err(KernelError::FlowGateBlocked);
                        }
                    }
                }
            }
        }
    }

    if !to_consume.is_empty() {
        state
            .override_used
            .entry(agent.clone())
            .or_default()
            .extend(to_consume);
    }

    state
        .taint_levels
        .entry(agent.clone())
        .or_default()
        .insert(level);
    state
        .gh_taint_invoked
        .entry(agent.clone())
        .or_default()
        .insert(level);

    Ok((state, KernelAction::SentinelElevateTaint { agent, level }))
}

/// Capability-gated audited budget reset (the DP "new epoch"). An agent holding
/// `cap_refresh_budget` -- strictly more privileged than `cap_declassify` -- resets its
/// declassification budget to full. The rare, logged exception that keeps a long-running
/// orchestrator from dead-ending on an exhausted budget while keeping the escape valve in
/// the verified kernel. (Audit lives in the event layer; here it is the state change only.)
pub fn sentinel_refresh_budget(
    mut state: KernelState,
    _bg: &BackgroundTheory,
    agent: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !state.agent_active.contains(&agent) {
        return Err(KernelError::AgentInactive);
    }
    if !state
        .agent_cap
        .get(&agent)
        .is_some_and(|caps| caps.contains(&CapKind::RefreshBudget))
    {
        return Err(KernelError::CapabilityMissing);
    }
    // Reset to full. Absence == full, so removing the entry is the canonical "full" state.
    state.agent_budget.remove(&agent);

    Ok((state, KernelAction::SentinelRefreshBudget { agent }))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::background::{BackgroundTheoryBuilder, ToolMetadata};
    use crate::types::{BudgetLevel, EgressKind, InstructionId, IssuerId};

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
    }
    struct ConformsNone;
    impl ConformanceOracle for ConformsNone {
        fn conforms(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
            false
        }
    }

    fn tool_meta_simple() -> ToolMetadata {
        ToolMetadata {
            capabilities: BTreeSet::new(),
            egress: BTreeSet::from([EgressKind::NetworkExternal]),
            conf_floor: ConfLevel::Public,
            output_bounded: false,
            issuer: IssuerId::new("trusted"),
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
                capabilities: BTreeSet::from([CapKind::FilesystemRead]),
                egress: BTreeSet::new(),
                conf_floor: ConfLevel::Sensitive,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
            },
        );
        b.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::NetworkEgress]),
                egress: BTreeSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
            },
        );
        b.register_tool(
            ToolId::new("check_exists"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::FilesystemRead]),
                egress: BTreeSet::new(),
                conf_floor: ConfLevel::Sensitive,
                output_bounded: true,
                issuer: IssuerId::new("trusted"),
            },
        );
        b.set_flow(
            ConfLevel::Public,
            EgressKind::NetworkExternal,
            FlowMode::Allow,
        );
        b.build()
    }

    fn state_with_agent(id: &str, caps: &[CapKind]) -> KernelState {
        let mut state = KernelState::initial();
        let agent = AgentId::new(id);
        state.agent_active.insert(agent.clone());
        state.agent_parent.insert(agent.clone(), AgentId::root());
        state
            .agent_cap
            .insert(agent, caps.iter().copied().collect());
        state.tool_registered.insert(ToolId::new("read_file"));
        state.tool_registered.insert(ToolId::new("send_email"));
        state.tool_registered.insert(ToolId::new("check_exists"));
        state
    }

    // --- register_tool ---

    #[test]
    fn register_tool_success() {
        let state = KernelState::initial();
        let bg = bg_with_tool("read_file");
        let tool = ToolId::new("read_file");

        let (new_state, action) = register_tool(state, &bg, tool.clone()).unwrap();
        assert!(new_state.tool_registered.contains(&tool));
        assert_eq!(action, KernelAction::RegisterTool { tool });
    }

    #[test]
    fn register_tool_rejects_already_registered() {
        let mut state = KernelState::initial();
        let tool = ToolId::new("read_file");
        state.tool_registered.insert(tool.clone());
        let bg = bg_with_tool("read_file");
        assert!(register_tool(state, &bg, tool).is_err());
    }

    #[test]
    fn register_tool_rejects_unknown_tool() {
        let state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        assert!(register_tool(state, &bg, ToolId::new("unknown")).is_err());
    }

    // --- delegate ---

    #[test]
    fn delegate_success() {
        let state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let grantor = AgentId::root();
        let grantee = AgentId::new("child-1");

        let (new_state, action) = delegate(state, &bg, grantor.clone(), grantee.clone()).unwrap();
        assert!(new_state.agent_active.contains(&grantee));
        assert_eq!(new_state.agent_parent.get(&grantee), Some(&grantor));
        assert!(
            new_state
                .agent_cap
                .get(&grantee)
                .map_or(true, |s| s.is_empty())
        );
        assert!(new_state.taint_levels.get(&grantee).is_none());
        assert_eq!(action, KernelAction::Delegate { grantor, grantee });
    }

    #[test]
    fn delegate_rejects_inactive_grantor() {
        let state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        assert!(delegate(state, &bg, AgentId::new("ghost"), AgentId::new("child")).is_err());
    }

    #[test]
    fn delegate_rejects_already_active_grantee() {
        let state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        assert!(delegate(state, &bg, AgentId::root(), AgentId::root()).is_err());
    }

    #[test]
    fn delegate_clears_stale_grantee_parent_entries() {
        let mut state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let grantee = AgentId::new("child-1");
        state
            .agent_parent
            .insert(AgentId::new("phantom"), grantee.clone());

        let (new_state, _) = delegate(state, &bg, AgentId::root(), grantee.clone()).unwrap();
        assert_eq!(new_state.agent_parent.get(&grantee), Some(&AgentId::root()));
        assert!(
            !new_state
                .agent_parent
                .contains_key(&AgentId::new("phantom"))
        );
    }

    // --- grant_capability ---

    #[test]
    fn grant_capability_success() {
        let mut state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child-1");
        state.agent_active.insert(child.clone());
        state.agent_parent.insert(child.clone(), AgentId::root());
        state.agent_cap.insert(child.clone(), BTreeSet::new());

        let (new_state, action) = grant_capability(
            state,
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
        let mut state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let parent = AgentId::new("parent");
        let child = AgentId::new("child");
        state.agent_active.insert(parent.clone());
        state.agent_active.insert(child.clone());
        state.agent_parent.insert(child.clone(), parent.clone());
        state.agent_cap.insert(parent, BTreeSet::new());
        state.agent_cap.insert(child.clone(), BTreeSet::new());
        assert!(
            grant_capability(
                state,
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
        let mut state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let other = AgentId::new("other");
        state.agent_active.insert(other.clone());
        assert!(
            grant_capability(state, &bg, AgentId::root(), other, CapKind::FilesystemRead).is_err()
        );
    }

    // --- revoke ---

    #[test]
    fn revoke_success() {
        let mut state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child-1");
        state.agent_active.insert(child.clone());
        state.agent_parent.insert(child.clone(), AgentId::root());
        state
            .agent_cap
            .insert(child.clone(), BTreeSet::from([CapKind::FilesystemRead]));
        state
            .taint_levels
            .insert(child.clone(), BTreeSet::from([ConfLevel::Internal]));

        let (new_state, action) = revoke(state, &bg, AgentId::root(), child.clone()).unwrap();
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
    fn revoke_rejects_non_child() {
        let state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        assert!(revoke(state, &bg, AgentId::root(), AgentId::new("stranger")).is_err());
    }

    #[test]
    fn revoke_preserves_grandchild_parent_link() {
        let mut state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child");
        let grandchild = AgentId::new("grandchild");
        state.agent_active.insert(child.clone());
        state.agent_active.insert(grandchild.clone());
        state.agent_parent.insert(child.clone(), AgentId::root());
        state.agent_parent.insert(grandchild.clone(), child.clone());

        let (new_state, _) = revoke(state, &bg, AgentId::root(), child.clone()).unwrap();
        assert_eq!(new_state.agent_parent.get(&grandchild), Some(&child));
    }

    // --- cascade_revoke ---

    #[test]
    fn cascade_revoke_success() {
        let mut state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let parent = AgentId::new("parent");
        let child = AgentId::new("child");
        state.agent_active.insert(child.clone());
        state.agent_parent.insert(child.clone(), parent.clone());

        let (new_state, action) =
            cascade_revoke(state, &bg, child.clone(), parent.clone()).unwrap();
        assert!(!new_state.agent_active.contains(&child));
        assert!(!new_state.agent_parent.contains_key(&child));
        assert_eq!(action, KernelAction::CascadeRevoke { child, parent });
    }

    #[test]
    fn cascade_revoke_rejects_active_parent() {
        let mut state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child");
        state.agent_active.insert(child.clone());
        state.agent_parent.insert(child.clone(), AgentId::root());
        assert!(cascade_revoke(state, &bg, child, AgentId::root()).is_err());
    }

    // --- invoke_complete ---

    #[test]
    fn invoke_complete_adds_taint_for_non_endorsed() {
        let mut state = KernelState::initial();
        let agent = AgentId::new("agent-1");
        let tool = ToolId::new("risky_tool");
        let inv = InvocationId::new("inv-1");

        state.agent_active.insert(agent.clone());
        state
            .in_flight
            .entry(agent.clone())
            .or_default()
            .insert(inv.clone());
        state.invocation_tool.insert(inv.clone(), tool.clone());

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            tool,
            ToolMetadata {
                capabilities: BTreeSet::new(),
                egress: BTreeSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Sensitive,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
            },
        );
        let bg = builder.build();

        let (new_state, action) =
            invoke_complete(state, &bg, &ConformsAll, agent.clone(), inv.clone()).unwrap();
        assert!(
            !new_state
                .in_flight
                .get(&agent)
                .map_or(false, |s| s.contains(&inv))
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
                .gh_taint_invoked
                .get(&agent)
                .unwrap()
                .contains(&ConfLevel::Sensitive)
        );
        assert_eq!(action, KernelAction::InvokeComplete { agent, inv });
    }

    #[test]
    fn invoke_complete_no_taint_for_endorsed() {
        let mut state = KernelState::initial();
        let agent = AgentId::new("agent-1");
        let tool = ToolId::new("safe_tool");
        let inv = InvocationId::new("inv-1");

        state.agent_active.insert(agent.clone());
        state
            .in_flight
            .entry(agent.clone())
            .or_default()
            .insert(inv.clone());
        state.invocation_tool.insert(inv.clone(), tool.clone());

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            tool,
            ToolMetadata {
                capabilities: BTreeSet::new(),
                egress: BTreeSet::new(),
                conf_floor: ConfLevel::Sensitive,
                output_bounded: true,
                issuer: IssuerId::new("trusted"),
            },
        );
        let bg = builder.build();

        let (new_state, _) = invoke_complete(state, &bg, &ConformsAll, agent.clone(), inv).unwrap();
        assert!(new_state.taint_levels.get(&agent).is_none());
    }

    #[test]
    fn invoke_complete_rejects_not_in_flight() {
        let mut state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let agent = AgentId::new("agent-1");
        state.agent_active.insert(agent.clone());
        assert!(invoke_complete(state, &bg, &ConformsAll, agent, InvocationId::new("inv-1")).is_err());
    }

    // --- return_endorsed ---

    #[test]
    fn return_endorsed_success() {
        let mut state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child-1");
        state.agent_active.insert(child.clone());
        state.agent_parent.insert(child.clone(), AgentId::root());
        // Cross-boundary declassification now requires the child to hold cap_declassify.
        state
            .agent_cap
            .insert(child.clone(), BTreeSet::from([CapKind::Declassify]));

        let (new_state, action) =
            return_endorsed(state.clone(), &bg, child.clone(), AgentId::root()).unwrap();
        assert_eq!(new_state.taint_levels, state.taint_levels);
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
        let mut state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child-1");
        state.agent_active.insert(child.clone());
        state.agent_parent.insert(child.clone(), AgentId::root());
        state
            .in_flight
            .entry(child.clone())
            .or_default()
            .insert(InvocationId::new("inv-1"));
        state
            .invocation_tool
            .insert(InvocationId::new("inv-1"), ToolId::new("t"));
        assert!(return_endorsed(state, &bg, child, AgentId::root()).is_err());
    }

    #[test]
    fn return_endorsed_rejects_non_child() {
        let mut state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let stranger = AgentId::new("stranger");
        state.agent_active.insert(stranger.clone());
        assert!(return_endorsed(state, &bg, stranger, AgentId::root()).is_err());
    }

    // --- declassification: conformance + budget ---

    /// State with one in-flight invocation of a bounded tool at `conf_floor`, for agent `a1`.
    fn state_with_bounded_in_flight(conf_floor: ConfLevel) -> (KernelState, BackgroundTheory) {
        let mut state = state_with_agent("a1", &[]);
        let tool = ToolId::new("bounded");
        let inv = InvocationId::new("binv");
        state.invocation_tool.insert(inv.clone(), tool.clone());
        state
            .in_flight
            .entry(AgentId::new("a1"))
            .or_default()
            .insert(inv);

        let mut b = BackgroundTheoryBuilder::new();
        b.trust_issuer(IssuerId::new("trusted"));
        b.register_tool(
            tool,
            ToolMetadata {
                capabilities: BTreeSet::new(),
                egress: BTreeSet::new(),
                conf_floor,
                output_bounded: true,
                issuer: IssuerId::new("trusted"),
            },
        );
        (state, b.build())
    }

    #[test]
    fn invoke_complete_bounded_conforming_is_zero_taint_and_debits_budget() {
        let (state, bg) = state_with_bounded_in_flight(ConfLevel::Sensitive);
        let (state, _) =
            invoke_complete(state, &bg, &ConformsAll, AgentId::new("a1"), InvocationId::new("binv"))
                .unwrap();
        assert!(
            !state.taint_levels.contains_key(&AgentId::new("a1")),
            "bounded + conforming + budget => zero taint"
        );
        assert_eq!(
            state.budget(&AgentId::new("a1")),
            BudgetLevel::L4,
            "the endorsed completion debits the agent's own budget"
        );
    }

    #[test]
    fn invoke_complete_bounded_nonconforming_adds_full_taint() {
        let (state, bg) = state_with_bounded_in_flight(ConfLevel::Sensitive);
        let (state, _) = invoke_complete(
            state,
            &bg,
            &ConformsNone,
            AgentId::new("a1"),
            InvocationId::new("binv"),
        )
        .unwrap();
        assert!(
            state
                .taint_levels
                .get(&AgentId::new("a1"))
                .unwrap()
                .contains(&ConfLevel::Sensitive),
            "bounded but non-conforming fails closed to full taint"
        );
        assert_eq!(
            state.budget(&AgentId::new("a1")),
            BudgetLevel::L5,
            "the full-taint path does not debit budget"
        );
    }

    #[test]
    fn invoke_complete_exhausted_budget_adds_full_taint() {
        let (mut state, bg) = state_with_bounded_in_flight(ConfLevel::Sensitive);
        state
            .agent_budget
            .insert(AgentId::new("a1"), BudgetLevel::Exhausted);
        let (state, _) =
            invoke_complete(state, &bg, &ConformsAll, AgentId::new("a1"), InvocationId::new("binv"))
                .unwrap();
        assert!(
            state
                .taint_levels
                .get(&AgentId::new("a1"))
                .unwrap()
                .contains(&ConfLevel::Sensitive),
            "exhausted budget fails closed to full taint even when bounded + conforming"
        );
    }

    /// Active parent `p` (child of root) and active child `c` (child of `p`) holding cap_declassify.
    fn parent_child_state() -> KernelState {
        let mut state = KernelState::initial();
        let p = AgentId::new("p");
        let c = AgentId::new("c");
        state.agent_active.insert(p.clone());
        state.agent_active.insert(c.clone());
        state.agent_parent.insert(p.clone(), AgentId::root());
        state.agent_parent.insert(c.clone(), p.clone());
        state
            .agent_cap
            .insert(c, BTreeSet::from([CapKind::Declassify]));
        state
    }

    #[test]
    fn return_endorsed_requires_declassify_cap() {
        let mut state = parent_child_state();
        state.agent_cap.insert(AgentId::new("c"), BTreeSet::new());
        let bg = BackgroundTheoryBuilder::new().build();
        assert!(
            return_endorsed(state, &bg, AgentId::new("c"), AgentId::new("p")).is_err(),
            "a child lacking cap_declassify cannot declassify upward"
        );
    }

    #[test]
    fn return_endorsed_debits_recipient_budget() {
        let state = parent_child_state();
        let bg = BackgroundTheoryBuilder::new().build();
        let (state, _) =
            return_endorsed(state, &bg, AgentId::new("c"), AgentId::new("p")).unwrap();
        assert_eq!(
            state.budget(&AgentId::new("p")),
            BudgetLevel::L4,
            "return_endorsed charges the RECIPIENT (parent) budget"
        );
    }

    #[test]
    fn return_endorsed_budget_exhausts_after_five_then_refuses() {
        let mut state = parent_child_state();
        let bg = BackgroundTheoryBuilder::new().build();
        // Five endorsed returns drain the parent's per-subtree budget (smurfing bound).
        for _ in 0..5 {
            let (s, _) =
                return_endorsed(state, &bg, AgentId::new("c"), AgentId::new("p")).unwrap();
            state = s;
        }
        assert!(state.budget_exhausted(&AgentId::new("p")));
        assert!(
            return_endorsed(state, &bg, AgentId::new("c"), AgentId::new("p")).is_err(),
            "sixth endorsed return is refused -- caller must fall back to return_unendorsed"
        );
    }

    #[test]
    fn sentinel_refresh_budget_restores_full() {
        let mut state = state_with_agent("a1", &[CapKind::RefreshBudget]);
        state
            .agent_budget
            .insert(AgentId::new("a1"), BudgetLevel::Exhausted);
        let bg = BackgroundTheoryBuilder::new().build();
        let (state, action) = sentinel_refresh_budget(state, &bg, AgentId::new("a1")).unwrap();
        assert_eq!(state.budget(&AgentId::new("a1")), BudgetLevel::L5);
        assert_eq!(
            action,
            KernelAction::SentinelRefreshBudget {
                agent: AgentId::new("a1")
            }
        );
    }

    #[test]
    fn sentinel_refresh_budget_requires_cap() {
        let state = state_with_agent("a1", &[]);
        let bg = BackgroundTheoryBuilder::new().build();
        assert!(
            sentinel_refresh_budget(state, &bg, AgentId::new("a1")).is_err(),
            "refreshing budget requires cap_refresh_budget"
        );
    }

    // --- return_unendorsed ---

    #[test]
    fn return_unendorsed_merges_taint() {
        let mut state = KernelState::initial();
        let child = AgentId::new("child-1");
        state.agent_active.insert(child.clone());
        state.agent_parent.insert(child.clone(), AgentId::root());
        state
            .taint_levels
            .insert(child.clone(), BTreeSet::from([ConfLevel::Sensitive]));

        let bg = BackgroundTheoryBuilder::new().build();

        let (new_state, action) =
            return_unendorsed(state, &bg, &PassAll, child.clone(), AgentId::root()).unwrap();
        assert!(
            new_state
                .taint_levels
                .get(&AgentId::root())
                .unwrap()
                .contains(&ConfLevel::Sensitive)
        );
        assert!(
            new_state
                .gh_taint_received
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
        let mut state = KernelState::initial();
        let child = AgentId::new("child-1");
        let parent_inv = InvocationId::new("parent-inv");
        let parent_tool = ToolId::new("egress_tool");

        state.agent_active.insert(child.clone());
        state.agent_parent.insert(child.clone(), AgentId::root());
        state
            .taint_levels
            .insert(child.clone(), BTreeSet::from([ConfLevel::Sensitive]));
        state
            .in_flight
            .entry(AgentId::root())
            .or_default()
            .insert(parent_inv.clone());
        state
            .invocation_tool
            .insert(parent_inv, parent_tool.clone());

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            parent_tool,
            ToolMetadata {
                capabilities: BTreeSet::new(),
                egress: BTreeSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
            },
        );
        let bg = builder.build();

        assert!(return_unendorsed(state, &bg, &FailAll, child, AgentId::root()).is_err());
    }

    #[test]
    fn return_unendorsed_rejects_child_with_in_flight() {
        let mut state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child-1");
        state.agent_active.insert(child.clone());
        state.agent_parent.insert(child.clone(), AgentId::root());
        state
            .in_flight
            .entry(child.clone())
            .or_default()
            .insert(InvocationId::new("i"));
        state
            .invocation_tool
            .insert(InvocationId::new("i"), ToolId::new("t"));
        assert!(return_unendorsed(state, &bg, &PassAll, child, AgentId::root()).is_err());
    }

    // --- invoke_start ---

    #[test]
    fn invoke_start_success_no_egress_tool() {
        let state = state_with_agent("a1", &[CapKind::FilesystemRead]);
        let bg = bg_with_tools();

        let (new_state, action) = invoke_start(
            state,
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
        let state = state_with_agent("a1", &[]);
        let bg = bg_with_tools();
        assert!(
            invoke_start(
                state,
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
        let state = KernelState::initial();
        let bg = bg_with_tools();
        assert!(
            invoke_start(
                state,
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
        let state = state_with_agent("a1", &[CapKind::FilesystemRead]);
        let bg = bg_with_tools();
        assert!(
            invoke_start(
                state,
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
        let mut state = state_with_agent("a1", &[CapKind::FilesystemRead]);
        state
            .invocation_tool
            .insert(InvocationId::new("inv-1"), ToolId::new("read_file"));
        let bg = bg_with_tools();
        assert!(
            invoke_start(
                state,
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
        let state = state_with_agent("a1", &[CapKind::FilesystemRead]);
        let bg = bg_with_tools();
        assert!(
            invoke_start(
                state,
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
        let mut state = state_with_agent("a1", &[CapKind::NetworkEgress]);
        state
            .taint_levels
            .insert(AgentId::new("a1"), BTreeSet::from([ConfLevel::Sensitive]));
        let bg = bg_with_tools();
        assert!(
            invoke_start(
                state,
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
        let mut state = state_with_agent("a1", &[CapKind::NetworkEgress]);
        state
            .taint_levels
            .insert(AgentId::new("a1"), BTreeSet::from([ConfLevel::Sensitive]));
        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::NetworkEgress]),
                egress: BTreeSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
            },
        );
        // Public egress is ALLOW (self-flow check 2c passes)
        builder.set_flow(
            ConfLevel::Public,
            EgressKind::NetworkExternal,
            FlowMode::Allow,
        );
        // Override for Sensitive level (check 2a passes via override)
        builder.add_override(
            AgentId::new("a1"),
            ToolId::new("send_email"),
            ConfLevel::Sensitive,
        );
        let bg = builder.build();

        assert!(
            invoke_start(
                state,
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
        let mut state = state_with_agent("a1", &[CapKind::NetworkEgress]);
        state
            .taint_levels
            .insert(AgentId::new("a1"), BTreeSet::from([ConfLevel::Sensitive]));
        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::NetworkEgress]),
                egress: BTreeSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
            },
        );
        // Public egress is ALLOW (2c passes); Sensitive/NetworkExternal stays DENY (2a needs override).
        builder.set_flow(
            ConfLevel::Public,
            EgressKind::NetworkExternal,
            FlowMode::Allow,
        );
        builder.add_override(
            AgentId::new("a1"),
            ToolId::new("send_email"),
            ConfLevel::Sensitive,
        );
        let bg = builder.build();

        // First invocation: rescued by the override at 2a.
        let (state, _) = invoke_start(
            state,
            &bg,
            &AllowAll,
            &FailAll,
            AgentId::new("a1"),
            ToolId::new("send_email"),
            InvocationId::new("inv-1"),
        )
        .expect("first invoke_start should pass via override");
        assert!(
            state.override_consumed(
                &AgentId::new("a1"),
                &ToolId::new("send_email"),
                ConfLevel::Sensitive
            ),
            "override should be marked consumed after first necessary use"
        );

        // Free the in-flight slot (adds harmless Public taint).
        let (state, _) = invoke_complete(
            state,
            &bg,
            &ConformsAll,
            AgentId::new("a1"),
            InvocationId::new("inv-1"),
        )
        .expect("invoke_complete should pass");

        // Second invocation: the override is now spent, so 2a is an un-rescued DENY.
        let result = invoke_start(
            state,
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
        let mut state = state_with_agent("a1", &[CapKind::NetworkEgress]);
        state
            .taint_levels
            .insert(AgentId::new("a1"), BTreeSet::from([ConfLevel::Sensitive]));
        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::NetworkEgress]),
                egress: BTreeSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
            },
        );
        // Both relevant pairs ALLOW -> the override is never the operative justification.
        builder.set_flow(
            ConfLevel::Public,
            EgressKind::NetworkExternal,
            FlowMode::Allow,
        );
        builder.set_flow(
            ConfLevel::Sensitive,
            EgressKind::NetworkExternal,
            FlowMode::Allow,
        );
        builder.add_override(
            AgentId::new("a1"),
            ToolId::new("send_email"),
            ConfLevel::Sensitive,
        );
        let bg = builder.build();

        let (state, _) = invoke_start(
            state,
            &bg,
            &AllowAll,
            &FailAll,
            AgentId::new("a1"),
            ToolId::new("send_email"),
            InvocationId::new("inv-1"),
        )
        .expect("invoke_start should pass via ALLOW");
        assert!(
            !state.override_consumed(
                &AgentId::new("a1"),
                &ToolId::new("send_email"),
                ConfLevel::Sensitive
            ),
            "override must NOT be consumed when ALLOW already permits the flow"
        );
    }

    #[test]
    fn override_used_cleared_on_revoke() {
        let mut state = state_with_agent("a1", &[CapKind::NetworkEgress]);
        state
            .override_used
            .entry(AgentId::new("a1"))
            .or_default()
            .insert((ToolId::new("send_email"), ConfLevel::Sensitive));
        let bg = BackgroundTheoryBuilder::new().build();

        let (state, _) = revoke(state, &bg, AgentId::root(), AgentId::new("a1"))
            .expect("revoke should pass");
        assert!(
            !state.override_used.contains_key(&AgentId::new("a1")),
            "revoke must clear consumed-override state so a re-delegated id starts fresh"
        );
    }

    #[test]
    fn return_unendorsed_override_is_single_use() {
        let mut state = KernelState::initial();
        let parent = AgentId::new("p");
        let child = AgentId::new("c");
        state.agent_active.insert(parent.clone());
        state.agent_active.insert(child.clone());
        state.agent_parent.insert(parent.clone(), AgentId::root());
        state.agent_parent.insert(child.clone(), parent.clone());

        // Parent has an in-flight egress tool; child carries conflicting Sensitive taint.
        let inv = InvocationId::new("p-inv");
        state
            .invocation_tool
            .insert(inv.clone(), ToolId::new("send_email"));
        state.in_flight.entry(parent.clone()).or_default().insert(inv);
        state
            .taint_levels
            .insert(child.clone(), BTreeSet::from([ConfLevel::Sensitive]));

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: BTreeSet::new(),
                egress: BTreeSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
            },
        );
        // Sensitive/NetworkExternal defaults to DENY; rescue only via the parent's override.
        builder.add_override(
            parent.clone(),
            ToolId::new("send_email"),
            ConfLevel::Sensitive,
        );
        let bg = builder.build();

        let (state, _) =
            return_unendorsed(state, &bg, &FailAll, child.clone(), parent.clone())
                .expect("first return_unendorsed should pass via override");
        assert!(
            state.override_consumed(&parent, &ToolId::new("send_email"), ConfLevel::Sensitive),
            "override should be marked consumed after first necessary use"
        );

        let result = return_unendorsed(state, &bg, &FailAll, child, parent);
        assert!(
            result.is_err(),
            "second return_unendorsed must fail: single-use override already spent"
        );
    }

    #[test]
    fn sentinel_elevate_taint_override_is_single_use() {
        let mut state = KernelState::initial();
        let agent = AgentId::new("a");
        state.agent_active.insert(agent.clone());
        state.agent_parent.insert(agent.clone(), AgentId::root());

        // Agent is clean but has an in-flight external-egress tool.
        let inv = InvocationId::new("a-inv");
        state
            .invocation_tool
            .insert(inv.clone(), ToolId::new("send_email"));
        state.in_flight.entry(agent.clone()).or_default().insert(inv);

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: BTreeSet::new(),
                egress: BTreeSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
            },
        );
        // Raising taint to Sensitive makes (Sensitive, NetworkExternal)=DENY bite the in-flight
        // send_email; only the override rescues it -- and spends it.
        builder.add_override(agent.clone(), ToolId::new("send_email"), ConfLevel::Sensitive);
        let bg = builder.build();

        let (state, _) =
            sentinel_elevate_taint(state, &bg, &FailAll, agent.clone(), ConfLevel::Sensitive)
                .expect("first sentinel raise should pass via override");
        assert!(
            state.override_consumed(&agent, &ToolId::new("send_email"), ConfLevel::Sensitive),
            "sentinel should consume the override that was the sole justification"
        );

        let result = sentinel_elevate_taint(state, &bg, &FailAll, agent, ConfLevel::Sensitive);
        assert!(
            result.is_err(),
            "second sentinel raise must fail: single-use override already spent"
        );
    }

    #[test]
    fn invoke_start_check_2b_new_tool_taint_vs_existing_inflight_egress() {
        let mut state = state_with_agent("a1", &[CapKind::FilesystemRead, CapKind::NetworkEgress]);
        let email_inv = InvocationId::new("email-inv");
        state
            .in_flight
            .entry(AgentId::new("a1"))
            .or_default()
            .insert(email_inv.clone());
        state
            .invocation_tool
            .insert(email_inv, ToolId::new("send_email"));

        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_tool(
            ToolId::new("read_file"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::FilesystemRead]),
                egress: BTreeSet::new(),
                conf_floor: ConfLevel::Sensitive,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
            },
        );
        builder.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::NetworkEgress]),
                egress: BTreeSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
            },
        );
        let bg = builder.build();

        assert!(
            invoke_start(
                state,
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

        let mut state = KernelState::initial();
        let agent = AgentId::new("a1");
        state.agent_active.insert(agent.clone());

        let (new_state, action) =
            load_instruction(state, &bg, agent.clone(), InstructionId::new("sys")).unwrap();
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
        let state = KernelState::initial();
        assert!(
            load_instruction(state, &bg, AgentId::new("ghost"), InstructionId::new("sys")).is_err()
        );
    }

    #[test]
    fn load_instruction_rejects_untrusted_issuer() {
        let mut builder = BackgroundTheoryBuilder::new();
        builder.register_instruction(InstructionId::new("skill"), IssuerId::new("rogue"));
        let bg = builder.build();
        let mut state = KernelState::initial();
        let agent = AgentId::new("a1");
        state.agent_active.insert(agent.clone());
        assert!(load_instruction(state, &bg, agent, InstructionId::new("skill")).is_err());
    }

    #[test]
    fn load_instruction_rejects_unknown_instruction() {
        let bg = BackgroundTheoryBuilder::new().build();
        let mut state = KernelState::initial();
        let agent = AgentId::new("a1");
        state.agent_active.insert(agent.clone());
        assert!(load_instruction(state, &bg, agent, InstructionId::new("nope")).is_err());
    }

    #[test]
    fn register_tool_rejects_untrusted_issuer() {
        let mut builder = BackgroundTheoryBuilder::new();
        builder.register_tool(
            ToolId::new("evil"),
            ToolMetadata {
                capabilities: BTreeSet::new(),
                egress: BTreeSet::new(),
                conf_floor: ConfLevel::Public,
                output_bounded: true,
                issuer: IssuerId::new("rogue"),
            },
        );
        // "rogue" is NOT trusted (no trust_issuer call)
        let bg = builder.build();
        let state = KernelState::initial();
        assert!(register_tool(state, &bg, ToolId::new("evil")).is_err());
    }
}
