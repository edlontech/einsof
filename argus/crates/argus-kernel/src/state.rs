use crate::background::BackgroundTheory;
use crate::capability::CapKind;
use crate::collections::{VecMap, VecSet};
use crate::types::{AgentId, BUDGET_CAPACITY, ConfLevel, InstructionId, InvocationId, OverrideKey, ToolId};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelState {
    pub agent_active: VecSet<AgentId>,
    pub agent_parent: VecMap<AgentId, AgentId>,
    pub agent_cap: VecMap<AgentId, VecSet<CapKind>>,
    pub taint_levels: VecMap<AgentId, VecSet<ConfLevel>>,
    pub in_flight: VecMap<AgentId, VecSet<InvocationId>>,
    pub invocation_tool: VecMap<InvocationId, ToolId>,
    pub tool_registered: VecSet<ToolId>,
    pub agent_instruction: VecMap<AgentId, VecSet<InstructionId>>,
    /// Single-use flow_override consumption (MF-3). Records the `(tool, level)` override
    /// grants an agent has already spent, so each immutable grant rescues at most one
    /// flow. Write-only on the hot path; cleared per-agent by `clear_agent_state`.
    pub override_used: VecMap<AgentId, VecSet<OverrideKey>>,
    /// Live single-use flow-override grants, armed exclusively by `grant_override`
    /// (no background seeding). Exact `override_used` shape; cleared per-agent by
    /// `clear_agent_state`.
    pub flow_override: VecMap<AgentId, VecSet<OverrideKey>>,
    /// Per-agent declassification budget (TzimtzumV2 `agent_budget`). Absence == capacity
    /// (`BUDGET_CAPACITY`) only for an agent that has never been delegated (root, or the
    /// initial state) -- the spec's `initial` gives capacity everywhere. `delegate` spawns
    /// every grantee with an explicit `0` entry instead: budget conservation means delegation
    /// mints nothing, and `sentinel_credit_budget` is the only faucet. Debited by the
    /// sensitivity weight on each endorsement; an unaffordable debit forces the fail-closed
    /// full-taint / refusal path. `revoke`/`cascade_revoke` leave the entry framed (inert --
    /// a revoked agent cannot act); `delegate` deterministically zeroes it again if the id is
    /// ever reused as a grantee.
    pub agent_budget: VecMap<AgentId, u8>,
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

    /// Current declassification budget for `agent` (absence == capacity).
    pub fn budget(&self, agent: &AgentId) -> u8 {
        match self.agent_budget.get(agent) {
            Some(b) => *b,
            None => BUDGET_CAPACITY,
        }
    }

    /// True if `agent` can pay a debit of weight `w`.
    pub fn affordable(&self, agent: &AgentId, w: u8) -> bool {
        self.budget(agent) >= w
    }

    /// Debit `agent`'s budget by weight `w` (saturating at 0). Materialises the entry.
    pub fn debit_budget(&mut self, agent: &AgentId, w: u8) {
        let next = self.budget(agent).saturating_sub(w);
        self.agent_budget.insert(agent.clone(), next);
    }

    /// Credit `agent`'s budget by `n` (saturating at capacity). Materialises the entry.
    pub fn credit_budget(&mut self, agent: &AgentId, n: u8) {
        let next = self.budget(agent).saturating_add(n).min(BUDGET_CAPACITY);
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
    use crate::types::IntegLevel;
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
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
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
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
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
