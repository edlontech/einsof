use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::background::BackgroundTheory;
use crate::capability::CapKind;
use crate::types::{AgentId, BudgetLevel, ConfLevel, InstructionId, InvocationId, ToolId};

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
    pub agent_instruction: BTreeMap<AgentId, BTreeSet<InstructionId>>,
    /// Single-use flow_override consumption (MF-3). Records the `(tool, level)` override
    /// grants an agent has already spent, so each immutable grant rescues at most one
    /// flow. Write-only on the hot path; cleared per-agent by `clear_agent_state`.
    pub override_used: BTreeMap<AgentId, BTreeSet<(ToolId, ConfLevel)>>,
    /// Per-agent declassification budget (TzimtzumV2 `agent_budget`). Absence == full (`L5`):
    /// a fresh or budget-refreshed agent has no entry. Debited on each endorsement; `Exhausted`
    /// forces the fail-closed full-taint path. Reset to full by `clear_agent_state`.
    pub agent_budget: BTreeMap<AgentId, BudgetLevel>,
}

impl KernelState {
    pub fn initial() -> Self {
        let root = AgentId::root();
        let mut all_caps: BTreeSet<CapKind> = BTreeSet::new();
        for cap in CapKind::ALL {
            all_caps.insert(cap);
        }

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
            agent_instruction: BTreeMap::new(),
            override_used: BTreeMap::new(),
            agent_budget: BTreeMap::new(),
        }
    }

    /// True if `agent` has already spent its single-use `flow_override` grant for
    /// `(tool, level)`. A consumed grant no longer rescues a DENY-mode flow.
    pub fn override_consumed(&self, agent: &AgentId, tool: &ToolId, level: ConfLevel) -> bool {
        self.override_used
            .get(agent)
            .is_some_and(|used| used.contains(&(tool.clone(), level)))
    }

    /// Current declassification budget for `agent` (absence == full, `L5`).
    pub fn budget(&self, agent: &AgentId) -> BudgetLevel {
        self.agent_budget
            .get(agent)
            .copied()
            .unwrap_or_else(BudgetLevel::full)
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

    pub fn speculative_taint(&self, agent: &AgentId, bg: &BackgroundTheory) -> BTreeSet<ConfLevel> {
        let mut taint: BTreeSet<ConfLevel> =
            self.taint_levels.get(agent).cloned().unwrap_or_default();

        if let Some(flights) = self.in_flight.get(agent) {
            for inv in flights {
                debug_assert!(
                    self.invocation_tool.contains_key(inv),
                    "in_flight contains InvocationId {inv} with no invocation_tool binding"
                );
                // Conformance-gating made the old bounded-tool exclusion unsound: a bounded
                // in-flight tool may still add taint on completion (if it fails conformance),
                // so every in-flight tool contributes its floor (worst-case / fail-closed).
                if let Some(tool_id) = self.invocation_tool.get(inv)
                    && let Some(meta) = bg.tool_metadata(tool_id)
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
            .entry(agent.clone())
            .or_default()
            .insert(inv);

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
            .entry(agent.clone())
            .or_default()
            .insert(inv);

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

        let taint = state.speculative_taint(&agent, &bg);
        assert!(taint.contains(&ConfLevel::Sensitive));
    }

    #[test]
    fn initial_state_has_no_agent_instructions() {
        let state = KernelState::initial();
        assert!(state.agent_instruction.is_empty());
    }
}
