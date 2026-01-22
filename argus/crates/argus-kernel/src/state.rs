use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::background::BackgroundTheory;
use crate::capability::CapKind;
use crate::types::{AgentId, ConfLevel, InvocationId, ToolId};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelState {
    pub agent_active: BTreeSet<AgentId>,
    pub agent_parent: BTreeMap<AgentId, AgentId>,
    pub agent_cap: BTreeMap<AgentId, BTreeSet<CapKind>>,
    pub taint_levels: BTreeMap<AgentId, BTreeSet<ConfLevel>>,
    pub in_flight: BTreeMap<AgentId, BTreeSet<InvocationId>>,
    pub invocation_tool: BTreeMap<InvocationId, ToolId>,
    pub tool_registered: BTreeSet<ToolId>,
    pub gh_taint_invoked: BTreeMap<AgentId, BTreeSet<ConfLevel>>,
    pub gh_taint_received: BTreeMap<AgentId, BTreeSet<ConfLevel>>,
}

impl KernelState {
    pub fn initial() -> Self {
        let root = AgentId::root();
        let all_caps: BTreeSet<CapKind> = CapKind::all().iter().copied().collect();

        let mut agent_active = BTreeSet::new();
        agent_active.insert(root.clone());

        let mut agent_cap = BTreeMap::new();
        agent_cap.insert(root, all_caps);

        Self {
            agent_active,
            agent_parent: BTreeMap::new(),
            agent_cap,
            taint_levels: BTreeMap::new(),
            in_flight: BTreeMap::new(),
            invocation_tool: BTreeMap::new(),
            tool_registered: BTreeSet::new(),
            gh_taint_invoked: BTreeMap::new(),
            gh_taint_received: BTreeMap::new(),
        }
    }

    pub fn speculative_taint(
        &self,
        agent: &AgentId,
        bg: &BackgroundTheory,
    ) -> BTreeSet<ConfLevel> {
        let mut taint: BTreeSet<ConfLevel> = self
            .taint_levels
            .get(agent)
            .cloned()
            .unwrap_or_default();

        if let Some(flights) = self.in_flight.get(agent) {
            for inv in flights {
                debug_assert!(
                    self.invocation_tool.contains_key(inv),
                    "in_flight contains InvocationId {inv} with no invocation_tool binding"
                );
                if let Some(tool_id) = self.invocation_tool.get(inv)
                    && let Some(meta) = bg.tool_metadata(tool_id)
                    && !meta.endorsed
                {
                    taint.insert(meta.conf_floor);
                }
            }
        }

        taint
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::background::{BackgroundTheoryBuilder, ToolMetadata};
    use crate::types::EgressKind;

    #[test]
    fn initial_state_has_root_active() {
        let state = KernelState::initial();
        assert!(state.agent_active.contains(&AgentId::root()));
    }

    #[test]
    fn initial_state_root_has_all_caps() {
        let state = KernelState::initial();
        let root_caps = state.agent_cap.get(&AgentId::root()).unwrap();
        for &kind in CapKind::all() {
            assert!(root_caps.contains(&kind), "root missing cap: {kind}");
        }
    }

    #[test]
    fn initial_state_no_tools_registered() {
        let state = KernelState::initial();
        assert!(state.tool_registered.is_empty());
    }

    #[test]
    fn initial_state_no_taint() {
        let state = KernelState::initial();
        assert!(state.taint_levels.is_empty());
    }

    #[test]
    fn initial_state_no_in_flight() {
        let state = KernelState::initial();
        assert!(state.in_flight.is_empty());
    }

    #[test]
    fn speculative_taint_empty_for_clean_agent() {
        let state = KernelState::initial();
        let bg = BackgroundTheoryBuilder::new().build();
        let taint = state.speculative_taint(&AgentId::new("agent-1"), &bg);
        assert!(taint.is_empty());
    }

    #[test]
    fn speculative_taint_includes_in_flight_non_endorsed() {
        let mut state = KernelState::initial();
        let agent = AgentId::new("agent-1");
        let tool = ToolId::new("risky_tool");
        let inv = InvocationId::new("inv-1");

        state.agent_active.insert(agent.clone());
        state.invocation_tool.insert(inv.clone(), tool.clone());
        state
            .in_flight
            .entry(agent.clone())
            .or_default()
            .insert(inv);

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

        let taint = state.speculative_taint(&agent, &bg);
        assert!(taint.contains(&ConfLevel::Sensitive));
    }

    #[test]
    fn speculative_taint_skips_endorsed_tools() {
        let mut state = KernelState::initial();
        let agent = AgentId::new("agent-1");
        let tool = ToolId::new("safe_tool");
        let inv = InvocationId::new("inv-1");

        state.agent_active.insert(agent.clone());
        state.invocation_tool.insert(inv.clone(), tool.clone());
        state
            .in_flight
            .entry(agent.clone())
            .or_default()
            .insert(inv);

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

        let taint = state.speculative_taint(&agent, &bg);
        assert!(taint.is_empty());
    }
}
