use crate::background::BackgroundTheory;
use crate::capability::CapKind;
use crate::collections::{VecMap, VecSet};
use crate::types::{AgentId, BudgetLevel, ConfLevel, InstructionId, InvocationId, OverrideKey, ToolId};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelState {
    pub agent_active: VecSet<AgentId>,
    pub agent_parent: VecMap<AgentId, AgentId>,
    pub agent_cap: VecMap<AgentId, VecSet<CapKind>>,
    pub taint_levels: VecMap<AgentId, VecSet<ConfLevel>>,
    pub in_flight: VecMap<AgentId, VecSet<InvocationId>>,
    pub invocation_tool: VecMap<InvocationId, ToolId>,
    pub tool_registered: VecSet<ToolId>,
    pub gh_taint_invoked: VecMap<AgentId, VecSet<ConfLevel>>,
    pub gh_taint_received: VecMap<AgentId, VecSet<ConfLevel>>,
    pub agent_instruction: VecMap<AgentId, VecSet<InstructionId>>,
    /// Single-use flow_override consumption (MF-3). Records the `(tool, level)` override
    /// grants an agent has already spent, so each immutable grant rescues at most one
    /// flow. Write-only on the hot path; cleared per-agent by `clear_agent_state`.
    pub override_used: VecMap<AgentId, VecSet<OverrideKey>>,
    /// Live single-use flow-override grants, armed exclusively by `grant_override`
    /// (no background seeding). Exact `override_used` shape; cleared per-agent by
    /// `clear_agent_state`.
    pub flow_override: VecMap<AgentId, VecSet<OverrideKey>>,
    /// Per-agent declassification budget (TzimtzumV2 `agent_budget`). Absence == full (`L5`):
    /// a fresh or budget-refreshed agent has no entry. Debited on each endorsement; `Exhausted`
    /// forces the fail-closed full-taint path. Reset to full by `clear_agent_state`.
    pub agent_budget: VecMap<AgentId, BudgetLevel>,
}

impl KernelState {
    pub fn initial() -> Self {
        let root = AgentId::root();
        let mut all_caps: VecSet<CapKind> = VecSet::new();
        let mut i = 0;
        while i < CapKind::ALL.len() {
            all_caps.insert(CapKind::ALL[i]);
            i += 1;
        }

        let mut agent_active = VecSet::new();
        agent_active.insert(root.clone());

        let mut agent_cap = VecMap::new();
        agent_cap.insert(root, all_caps);

        Self {
            agent_active,
            agent_parent: VecMap::new(),
            agent_cap,
            taint_levels: VecMap::new(),
            in_flight: VecMap::new(),
            invocation_tool: VecMap::new(),
            tool_registered: VecSet::new(),
            gh_taint_invoked: VecMap::new(),
            gh_taint_received: VecMap::new(),
            agent_instruction: VecMap::new(),
            override_used: VecMap::new(),
            flow_override: VecMap::new(),
            agent_budget: VecMap::new(),
        }
    }

    /// True if `agent` has already spent its single-use `flow_override` grant for
    /// `(tool, level)`. A consumed grant no longer rescues a DENY-mode flow.
    pub fn override_consumed(&self, agent: &AgentId, tool: &ToolId, level: ConfLevel) -> bool {
        match self.override_used.get(agent) {
            Some(used) => used.contains(&OverrideKey { tool: tool.clone(), level }),
            None => false,
        }
    }

    /// True if `agent` holds an (armed or consumed) `flow_override` grant for
    /// `(tool, level)`. Consumption is tracked separately in `override_used`.
    pub fn has_flow_override(&self, agent: &AgentId, tool: &ToolId, level: ConfLevel) -> bool {
        match self.flow_override.get(agent) {
            Some(grants) => grants.contains(&OverrideKey { tool: tool.clone(), level }),
            None => false,
        }
    }

    /// Current declassification budget for `agent` (absence == full, `L5`).
    pub fn budget(&self, agent: &AgentId) -> BudgetLevel {
        match self.agent_budget.get(agent) {
            Some(b) => *b,
            None => BudgetLevel::full(),
        }
    }

    /// True if `agent`'s declassification budget is exhausted (blocks the zero-taint path).
    pub fn budget_exhausted(&self, agent: &AgentId) -> bool {
        self.budget(agent) == BudgetLevel::Exhausted
    }

    /// Debit `agent`'s budget one level (saturating). Materialises the entry on first debit.
    pub fn debit_budget(&mut self, agent: &AgentId) {
        let next = self.budget(agent).debit();
        self.agent_budget.insert(agent.clone(), next);
    }

    pub fn speculative_taint(&self, agent: &AgentId, bg: &BackgroundTheory) -> VecSet<ConfLevel> {
        let mut taint: VecSet<ConfLevel> = self.taint_levels.get_set_or_empty(agent);

        // Conformance-gating made the old bounded-tool exclusion unsound: a bounded in-flight
        // tool may still add taint on completion (if it fails conformance), so every in-flight
        // tool contributes its floor (worst-case / fail-closed). Owned locals + index loop.
        let flights = self.in_flight.get_set_or_empty(agent);
        let mut j = 0;
        while j < flights.len() {
            let inv = flights.at(j);
            if let Some(tool_id) = self.invocation_tool.get_cloned(inv) {
                if let Some(tmeta) = bg.tool_metadata(&tool_id) {
                    taint.insert(tmeta.conf_floor);
                }
            }
            j += 1;
        }

        taint
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::background::{BackgroundTheoryBuilder, ToolMetadata};
    use crate::types::{EgressKind, IssuerId};

    #[test]
    fn initial_state_has_root_active() {
        let state = KernelState::initial();
        assert!(state.agent_active.contains(&AgentId::root()));
    }

    #[test]
    fn initial_state_root_has_all_caps() {
        let state = KernelState::initial();
        let root_caps = state.agent_cap.get(&AgentId::root()).unwrap();
        for kind in CapKind::ALL {
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
            .insert_into(agent.clone(), inv);

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
            },
        );
        let bg = builder.build();

        let taint = state.speculative_taint(&agent, &bg);
        assert!(taint.contains(&ConfLevel::Sensitive));
    }

    #[test]
    fn speculative_taint_includes_bounded_tools() {
        // Conformance-gating soundness fix: a bounded in-flight tool may still add taint on
        // completion (if it fails conformance), so speculative taint includes its floor too --
        // the old "skip endorsed tools" exclusion would have been unsound.
        let mut state = KernelState::initial();
        let agent = AgentId::new("agent-1");
        let tool = ToolId::new("bounded_tool");
        let inv = InvocationId::new("inv-1");

        state.agent_active.insert(agent.clone());
        state.invocation_tool.insert(inv.clone(), tool.clone());
        state
            .in_flight
            .insert_into(agent.clone(), inv);

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
            },
        );
        let bg = builder.build();

        let taint = state.speculative_taint(&agent, &bg);
        assert!(taint.contains(&ConfLevel::Sensitive));
    }

    #[test]
    fn initial_state_has_no_agent_instructions() {
        let state = KernelState::initial();
        assert!(state.agent_instruction.is_empty());
    }

    #[test]
    fn flow_override_lookup() {
        let mut st = KernelState::initial();
        let agent = AgentId::new("a1");
        st.flow_override.insert_into(
            agent.clone(),
            OverrideKey { tool: ToolId::new("t"), level: ConfLevel::Sensitive },
        );
        assert!(st.has_flow_override(&agent, &ToolId::new("t"), ConfLevel::Sensitive));
        assert!(!st.has_flow_override(&agent, &ToolId::new("t"), ConfLevel::Public));
        assert!(!st.has_flow_override(&AgentId::new("b"), &ToolId::new("t"), ConfLevel::Sensitive));
    }
}
