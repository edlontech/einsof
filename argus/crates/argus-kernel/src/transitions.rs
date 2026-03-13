use std::collections::BTreeSet;

use crate::background::{BackgroundTheory, FlowMode};
use crate::capability::CapKind;
use crate::error::KernelError;
use crate::event::KernelAction;
use crate::state::KernelState;
use crate::traits::{AuthorizerOracle, ContentGateOracle};
use crate::types::{AgentId, ConfLevel, EgressKind, InvocationId, ToolId};

fn flow_allowed(
    bg: &BackgroundTheory,
    content_gate: &impl ContentGateOracle,
    agent: &AgentId,
    tool: &ToolId,
    state: &KernelState,
    level: ConfLevel,
    egress: EgressKind,
) -> bool {
    match bg.flow_mode(level, egress) {
        FlowMode::Allow => true,
        FlowMode::Inspect => content_gate.passes(agent, tool, state, bg),
        FlowMode::Deny => bg.has_flow_override(agent, tool, level),
    }
}

fn clear_agent_state(state: &mut KernelState, agent: &AgentId) {
    state.taint_levels.remove(agent);
    state.in_flight.remove(agent);
    state.gh_taint_invoked.remove(agent);
    state.gh_taint_received.remove(agent);
}

pub fn register_tool(
    mut state: KernelState,
    bg: &BackgroundTheory,
    tool: ToolId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !bg.has_tool(&tool) {
        return Err(KernelError::PreconditionViolation(
            format!("tool {tool} not in background theory"),
        ));
    }
    if state.tool_registered.contains(&tool) {
        return Err(KernelError::PreconditionViolation(
            format!("tool {tool} already registered"),
        ));
    }

    state.tool_registered.insert(tool.clone());

    Ok((state, KernelAction::RegisterTool { tool }))
}

pub fn delegate(
    mut state: KernelState,
    _bg: &BackgroundTheory,
    grantor: AgentId,
    grantee: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !state.agent_active.contains(&grantor) {
        return Err(KernelError::PreconditionViolation(
            format!("grantor {grantor} is not active"),
        ));
    }
    if state.agent_active.contains(&grantee) {
        return Err(KernelError::PreconditionViolation(
            format!("grantee {grantee} is already active"),
        ));
    }
    if grantee == AgentId::root() {
        return Err(KernelError::PreconditionViolation(
            "cannot delegate to root".to_owned(),
        ));
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
        return Err(KernelError::PreconditionViolation(
            format!("parent {parent} is not active"),
        ));
    }
    if !state.agent_active.contains(&child) {
        return Err(KernelError::PreconditionViolation(
            format!("child {child} is not active"),
        ));
    }
    if state.agent_parent.get(&child) != Some(&parent) {
        return Err(KernelError::PreconditionViolation(
            format!("{child} is not a direct child of {parent}"),
        ));
    }
    if !state.agent_cap.get(&parent).is_some_and(|caps| caps.contains(&cap)) {
        return Err(KernelError::PreconditionViolation(
            format!("parent {parent} does not hold capability {cap}"),
        ));
    }

    state.agent_cap.entry(child.clone()).or_default().insert(cap);

    Ok((state, KernelAction::GrantCapability { parent, child, cap }))
}

pub fn revoke(
    mut state: KernelState,
    _bg: &BackgroundTheory,
    parent: AgentId,
    target: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if state.agent_parent.get(&target) != Some(&parent) {
        return Err(KernelError::PreconditionViolation(
            format!("{target} is not a direct child of {parent}"),
        ));
    }
    if !state.agent_active.contains(&parent) {
        return Err(KernelError::PreconditionViolation(
            format!("parent {parent} is not active"),
        ));
    }
    if !state.agent_active.contains(&target) {
        return Err(KernelError::PreconditionViolation(
            format!("target {target} is not active"),
        ));
    }
    if target == AgentId::root() {
        return Err(KernelError::PreconditionViolation(
            "cannot revoke root".to_owned(),
        ));
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
        return Err(KernelError::PreconditionViolation(
            format!("{child} is not a direct child of {parent}"),
        ));
    }
    if state.agent_active.contains(&parent) {
        return Err(KernelError::PreconditionViolation(
            format!("parent {parent} is still active (use revoke, not cascade_revoke)"),
        ));
    }
    if !state.agent_active.contains(&child) {
        return Err(KernelError::PreconditionViolation(
            format!("child {child} is not active"),
        ));
    }
    if child == AgentId::root() {
        return Err(KernelError::PreconditionViolation(
            "cannot cascade_revoke root".to_owned(),
        ));
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
        return Err(KernelError::PreconditionViolation(
            format!("agent {agent} is not active"),
        ));
    }
    if agent == AgentId::root() {
        return Err(KernelError::PreconditionViolation(
            "root agent cannot invoke tools directly".to_owned(),
        ));
    }
    if !state.tool_registered.contains(&tool) {
        return Err(KernelError::PreconditionViolation(
            format!("tool {tool} is not registered"),
        ));
    }
    if state.invocation_tool.contains_key(&inv) {
        return Err(KernelError::PreconditionViolation(
            format!("invocation {inv} already exists"),
        ));
    }
    for flights in state.in_flight.values() {
        if flights.contains(&inv) {
            return Err(KernelError::PreconditionViolation(
                format!("invocation {inv} is already in-flight"),
            ));
        }
    }

    let tool_meta = bg.tool_metadata(&tool).ok_or_else(|| {
        KernelError::PreconditionViolation(format!("tool {tool} not in background theory"))
    })?;

    let agent_caps = state.agent_cap.get(&agent);
    for required_cap in &tool_meta.capabilities {
        if !agent_caps.is_some_and(|caps| caps.contains(required_cap)) {
            return Err(KernelError::PreconditionViolation(
                format!("agent {agent} lacks required capability {required_cap}"),
            ));
        }
    }

    let spec_taint = state.speculative_taint(&agent, bg);
    for &level in &spec_taint {
        for &egress in &tool_meta.egress {
            if !flow_allowed(bg, content_gate, &agent, &tool, &state, level, egress) {
                return Err(KernelError::PreconditionViolation(format!(
                    "flow gate 2a: speculative taint {level} blocked for egress {egress} on tool {tool}"
                )));
            }
        }
    }

    if !tool_meta.endorsed {
        if let Some(agent_flights) = state.in_flight.get(&agent) {
            for flight_inv in agent_flights {
                if let Some(flight_tool_id) = state.invocation_tool.get(flight_inv)
                    && let Some(flight_meta) = bg.tool_metadata(flight_tool_id)
                {
                    for &egress in &flight_meta.egress {
                        if !flow_allowed(bg, content_gate, &agent, flight_tool_id, &state, tool_meta.conf_floor, egress) {
                            return Err(KernelError::PreconditionViolation(format!(
                                "flow gate 2b: new tool {tool} taint {} conflicts with in-flight {flight_tool_id} egress {egress}",
                                tool_meta.conf_floor
                            )));
                        }
                    }
                }
            }
        }

        for &egress in &tool_meta.egress {
            if !flow_allowed(bg, content_gate, &agent, &tool, &state, tool_meta.conf_floor, egress) {
                return Err(KernelError::PreconditionViolation(format!(
                    "flow gate 2c: tool {tool} self-flow blocked ({}, {egress})",
                    tool_meta.conf_floor
                )));
            }
        }
    }

    if !authorizer.allows(&agent, &tool, &state, bg) {
        return Err(KernelError::PreconditionViolation(
            format!("authorizer denied ({agent}, {tool})"),
        ));
    }

    state.invocation_tool.insert(inv.clone(), tool.clone());
    state
        .in_flight
        .entry(agent.clone())
        .or_default()
        .insert(inv.clone());

    Ok((state, KernelAction::InvokeStart { agent, tool, inv }))
}

pub fn invoke_complete(
    mut state: KernelState,
    bg: &BackgroundTheory,
    agent: AgentId,
    inv: InvocationId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !state.in_flight.get(&agent).is_some_and(|flights| flights.contains(&inv)) {
        return Err(KernelError::PreconditionViolation(
            format!("invocation {inv} is not in-flight for agent {agent}"),
        ));
    }
    if !state.agent_active.contains(&agent) {
        return Err(KernelError::PreconditionViolation(
            format!("agent {agent} is not active"),
        ));
    }

    if let Some(flights) = state.in_flight.get_mut(&agent) {
        flights.remove(&inv);
    }

    if let Some(tool_id) = state.invocation_tool.get(&inv)
        && let Some(meta) = bg.tool_metadata(tool_id)
        && !meta.endorsed
    {
        state
            .taint_levels
            .entry(agent.clone())
            .or_default()
            .insert(meta.conf_floor);
        state
            .gh_taint_invoked
            .entry(agent.clone())
            .or_default()
            .insert(meta.conf_floor);
    }

    Ok((state, KernelAction::InvokeComplete { agent, inv }))
}

pub fn return_endorsed(
    state: KernelState,
    _bg: &BackgroundTheory,
    child: AgentId,
    parent: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if state.agent_parent.get(&child) != Some(&parent) {
        return Err(KernelError::PreconditionViolation(
            format!("{child} is not a direct child of {parent}"),
        ));
    }
    if !state.agent_active.contains(&child) {
        return Err(KernelError::PreconditionViolation(
            format!("child {child} is not active"),
        ));
    }
    if !state.agent_active.contains(&parent) {
        return Err(KernelError::PreconditionViolation(
            format!("parent {parent} is not active"),
        ));
    }
    if state.in_flight.get(&child).is_some_and(|flights| !flights.is_empty()) {
        return Err(KernelError::PreconditionViolation(
            format!("child {child} has in-flight invocations"),
        ));
    }

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
        return Err(KernelError::PreconditionViolation(
            format!("{child} is not a direct child of {parent}"),
        ));
    }
    if !state.agent_active.contains(&child) {
        return Err(KernelError::PreconditionViolation(
            format!("child {child} is not active"),
        ));
    }
    if !state.agent_active.contains(&parent) {
        return Err(KernelError::PreconditionViolation(
            format!("parent {parent} is not active"),
        ));
    }
    if state.in_flight.get(&child).is_some_and(|flights| !flights.is_empty()) {
        return Err(KernelError::PreconditionViolation(
            format!("child {child} has in-flight invocations"),
        ));
    }

    let child_taint = state
        .taint_levels
        .get(&child)
        .cloned()
        .unwrap_or_default();
    let empty_flights = BTreeSet::new();
    let parent_flights = state.in_flight.get(&parent).unwrap_or(&empty_flights);

    for &level in &child_taint {
        for inv in parent_flights {
            if let Some(tool_id) = state.invocation_tool.get(inv)
                && let Some(meta) = bg.tool_metadata(tool_id)
            {
                for &egress in &meta.egress {
                    if !flow_allowed(bg, content_gate, &parent, tool_id, &state, level, egress) {
                        return Err(KernelError::PreconditionViolation(format!(
                            "flow gate: child taint {level} conflicts with parent in-flight tool {tool_id} egress {egress}"
                        )));
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
        return Err(KernelError::PreconditionViolation(
            format!("agent not active: {agent}"),
        ));
    }

    if let Some(in_flight_invs) = state.in_flight.get(&agent) {
        for inv in in_flight_invs {
            let tool = state.invocation_tool.get(inv).ok_or_else(|| {
                KernelError::PreconditionViolation(
                    format!("no tool binding for invocation {inv}"),
                )
            })?;
            debug_assert!(bg.tool_metadata(tool).is_some(), "in-flight tool {tool} missing from background theory");
            if let Some(meta) = bg.tool_metadata(tool) {
                for &egress in &meta.egress {
                    if !flow_allowed(bg, content_gate, &agent, tool, &state, level, egress) {
                        return Err(KernelError::PreconditionViolation(
                            format!(
                                "flow incompatible: taint {level} with {tool} egress {egress}"
                            ),
                        ));
                    }
                }
            }
        }
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

    Ok((
        state,
        KernelAction::SentinelElevateTaint { agent, level },
    ))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::background::{BackgroundTheoryBuilder, ToolMetadata};
    use crate::types::EgressKind;

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

    fn tool_meta_simple() -> ToolMetadata {
        ToolMetadata {
            capabilities: BTreeSet::new(),
            egress: BTreeSet::from([EgressKind::NetworkExternal]),
            conf_floor: ConfLevel::Public,
            endorsed: false,
        }
    }

    fn bg_with_tool(id: &str) -> BackgroundTheory {
        let mut b = BackgroundTheoryBuilder::new();
        b.register_tool(ToolId::new(id), tool_meta_simple());
        b.build()
    }

    fn bg_with_tools() -> BackgroundTheory {
        let mut b = BackgroundTheoryBuilder::new();
        b.register_tool(
            ToolId::new("read_file"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::FilesystemRead]),
                egress: BTreeSet::new(),
                conf_floor: ConfLevel::Sensitive,
                endorsed: false,
            },
        );
        b.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::NetworkEgress]),
                egress: BTreeSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                endorsed: false,
            },
        );
        b.register_tool(
            ToolId::new("check_exists"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::FilesystemRead]),
                egress: BTreeSet::new(),
                conf_floor: ConfLevel::Sensitive,
                endorsed: true,
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

        let (new_state, action) =
            delegate(state, &bg, grantor.clone(), grantee.clone()).unwrap();
        assert!(new_state.agent_active.contains(&grantee));
        assert_eq!(new_state.agent_parent.get(&grantee), Some(&grantor));
        assert!(new_state
            .agent_cap
            .get(&grantee)
            .map_or(true, |s| s.is_empty()));
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
        assert_eq!(
            new_state.agent_parent.get(&grantee),
            Some(&AgentId::root())
        );
        assert!(!new_state.agent_parent.contains_key(&AgentId::new("phantom")));
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
        assert!(new_state
            .agent_cap
            .get(&child)
            .unwrap()
            .contains(&CapKind::FilesystemRead));
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
            grant_capability(state, &bg, AgentId::new("parent"), child, CapKind::FilesystemRead)
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

        let (new_state, action) =
            revoke(state, &bg, AgentId::root(), child.clone()).unwrap();
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
        state
            .agent_parent
            .insert(grandchild.clone(), child.clone());

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
        builder.register_tool(
            tool,
            ToolMetadata {
                capabilities: BTreeSet::new(),
                egress: BTreeSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Sensitive,
                endorsed: false,
            },
        );
        let bg = builder.build();

        let (new_state, action) =
            invoke_complete(state, &bg, agent.clone(), inv.clone()).unwrap();
        assert!(!new_state
            .in_flight
            .get(&agent)
            .map_or(false, |s| s.contains(&inv)));
        assert!(new_state
            .taint_levels
            .get(&agent)
            .unwrap()
            .contains(&ConfLevel::Sensitive));
        assert!(new_state
            .gh_taint_invoked
            .get(&agent)
            .unwrap()
            .contains(&ConfLevel::Sensitive));
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
        builder.register_tool(
            tool,
            ToolMetadata {
                capabilities: BTreeSet::new(),
                egress: BTreeSet::new(),
                conf_floor: ConfLevel::Sensitive,
                endorsed: true,
            },
        );
        let bg = builder.build();

        let (new_state, _) = invoke_complete(state, &bg, agent.clone(), inv).unwrap();
        assert!(new_state.taint_levels.get(&agent).is_none());
    }

    #[test]
    fn invoke_complete_rejects_not_in_flight() {
        let mut state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let agent = AgentId::new("agent-1");
        state.agent_active.insert(agent.clone());
        assert!(invoke_complete(state, &bg, agent, InvocationId::new("inv-1")).is_err());
    }

    // --- return_endorsed ---

    #[test]
    fn return_endorsed_success() {
        let mut state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let child = AgentId::new("child-1");
        state.agent_active.insert(child.clone());
        state.agent_parent.insert(child.clone(), AgentId::root());

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
        assert!(new_state
            .taint_levels
            .get(&AgentId::root())
            .unwrap()
            .contains(&ConfLevel::Sensitive));
        assert!(new_state
            .gh_taint_received
            .get(&AgentId::root())
            .unwrap()
            .contains(&ConfLevel::Sensitive));
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
        builder.register_tool(
            parent_tool,
            ToolMetadata {
                capabilities: BTreeSet::new(),
                egress: BTreeSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                endorsed: false,
            },
        );
        let bg = builder.build();

        assert!(
            return_unendorsed(state, &bg, &FailAll, child, AgentId::root()).is_err()
        );
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

        assert!(new_state
            .in_flight
            .get(&AgentId::new("a1"))
            .unwrap()
            .contains(&InvocationId::new("inv-1")));
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
        assert!(invoke_start(
            state,
            &bg,
            &AllowAll,
            &PassAll,
            AgentId::new("a1"),
            ToolId::new("read_file"),
            InvocationId::new("inv-1"),
        )
        .is_err());
    }

    #[test]
    fn invoke_start_rejects_root() {
        let state = KernelState::initial();
        let bg = bg_with_tools();
        assert!(invoke_start(
            state,
            &bg,
            &AllowAll,
            &PassAll,
            AgentId::root(),
            ToolId::new("read_file"),
            InvocationId::new("inv-1"),
        )
        .is_err());
    }

    #[test]
    fn invoke_start_rejects_unregistered_tool() {
        let state = state_with_agent("a1", &[CapKind::FilesystemRead]);
        let bg = bg_with_tools();
        assert!(invoke_start(
            state,
            &bg,
            &AllowAll,
            &PassAll,
            AgentId::new("a1"),
            ToolId::new("unregistered"),
            InvocationId::new("inv-1"),
        )
        .is_err());
    }

    #[test]
    fn invoke_start_rejects_duplicate_invocation_id() {
        let mut state = state_with_agent("a1", &[CapKind::FilesystemRead]);
        state
            .invocation_tool
            .insert(InvocationId::new("inv-1"), ToolId::new("read_file"));
        let bg = bg_with_tools();
        assert!(invoke_start(
            state,
            &bg,
            &AllowAll,
            &PassAll,
            AgentId::new("a1"),
            ToolId::new("read_file"),
            InvocationId::new("inv-1"),
        )
        .is_err());
    }

    #[test]
    fn invoke_start_rejects_authorizer_deny() {
        struct DenyAll;
        impl AuthorizerOracle for DenyAll {
            fn allows(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
                false
            }
        }
        let state = state_with_agent("a1", &[CapKind::FilesystemRead]);
        let bg = bg_with_tools();
        assert!(invoke_start(
            state,
            &bg,
            &DenyAll,
            &PassAll,
            AgentId::new("a1"),
            ToolId::new("read_file"),
            InvocationId::new("inv-1"),
        )
        .is_err());
    }

    #[test]
    fn invoke_start_flow_gate_blocks_tainted_agent_egress() {
        let mut state = state_with_agent("a1", &[CapKind::NetworkEgress]);
        state.taint_levels.insert(
            AgentId::new("a1"),
            BTreeSet::from([ConfLevel::Sensitive]),
        );
        let bg = bg_with_tools();
        assert!(invoke_start(
            state,
            &bg,
            &AllowAll,
            &FailAll,
            AgentId::new("a1"),
            ToolId::new("send_email"),
            InvocationId::new("inv-1"),
        )
        .is_err());
    }

    #[test]
    fn invoke_start_flow_gate_allows_with_override() {
        let mut state = state_with_agent("a1", &[CapKind::NetworkEgress]);
        state.taint_levels.insert(
            AgentId::new("a1"),
            BTreeSet::from([ConfLevel::Sensitive]),
        );
        let mut builder = BackgroundTheoryBuilder::new();
        builder.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::NetworkEgress]),
                egress: BTreeSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                endorsed: false,
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

        assert!(invoke_start(
            state,
            &bg,
            &AllowAll,
            &FailAll,
            AgentId::new("a1"),
            ToolId::new("send_email"),
            InvocationId::new("inv-1"),
        )
        .is_ok());
    }

    #[test]
    fn invoke_start_check_2b_new_tool_taint_vs_existing_inflight_egress() {
        let mut state =
            state_with_agent("a1", &[CapKind::FilesystemRead, CapKind::NetworkEgress]);
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
        builder.register_tool(
            ToolId::new("read_file"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::FilesystemRead]),
                egress: BTreeSet::new(),
                conf_floor: ConfLevel::Sensitive,
                endorsed: false,
            },
        );
        builder.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: BTreeSet::from([CapKind::NetworkEgress]),
                egress: BTreeSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                endorsed: false,
            },
        );
        let bg = builder.build();

        assert!(invoke_start(
            state,
            &bg,
            &AllowAll,
            &FailAll,
            AgentId::new("a1"),
            ToolId::new("read_file"),
            InvocationId::new("inv-2"),
        )
        .is_err());
    }
}
