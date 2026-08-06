use crate::capability::CapKind;
use crate::collections::{VecMap, VecSet};
use crate::types::{
    AgentId, AttestationId, ChallengeScope, ConfLevel, CrossingGrant, CrossingId, CrossingKey,
    IntegLevel, InvocationId, PendingInvocation, ToolId,
};

/// The state-shape version the ex_argus NIF binds against. TzimtzumV4 (pending/challenge/crossing
/// state, no budget/override economy) is shape version 5.
pub const STATE_VERSION: u32 = 5;

/// TzimtzumV4 mutable kernel state — the exact `Tzimtzum.St` field set (State.lean). Enforcement
/// mode, egress ceilings, and root identity are immutable background, not fields here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KernelState {
    pub agent_active: VecSet<AgentId>,
    pub agent_parent: VecMap<AgentId, AgentId>,
    pub agent_cap: VecMap<AgentId, VecSet<CapKind>>,
    /// Levels ingested. Effective taint is the MAX of the set; EMPTY SET = UNTAINTED.
    pub taint_levels: VecMap<AgentId, VecSet<ConfLevel>>,
    /// Levels ingested. Effective integrity is the MIN of the set; EMPTY SET = FULLY TRUSTED
    /// (dual of taint). Cleared per-agent by `delegate`/`revoke`/`cascade_revoke`.
    pub integ_levels: VecMap<AgentId, VecSet<IntegLevel>>,
    /// Pending invocations keyed by invocation id (each invocation pends at most once).
    pub pending: VecMap<InvocationId, PendingInvocation>,
    /// Open inspection challenges keyed by invocation (each invocation has at most one open scope).
    pub challenges: VecMap<InvocationId, ChallengeScope>,
    /// Invocation ids consumed at admission; NEVER removed (freshness history, not agent state).
    pub consumed_ids: VecSet<InvocationId>,
    /// Attestation ids consumed by inspected admission, resolution, or endorsement; never removed.
    pub consumed_attestations: VecSet<AttestationId>,
    /// Crossing ids consumed by `cross_output`; never removed.
    pub consumed_crossings: VecSet<CrossingId>,
    /// Remaining crossing uses keyed by `(holder agent, exact assignment digest)`. Provisioned only
    /// by `grant_crossing`, decremented by conforming `cross_output`, destroyed by revocation.
    pub crossing_grants: VecMap<CrossingKey, CrossingGrant>,
    pub tool_registered: VecSet<ToolId>,
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
            integ_levels: VecMap::new(),
            pending: VecMap::new(),
            challenges: VecMap::new(),
            consumed_ids: VecSet::new(),
            consumed_attestations: VecSet::new(),
            consumed_crossings: VecSet::new(),
            crossing_grants: VecMap::new(),
            tool_registered: VecSet::new(),
        }
    }

    /// Worst-case taint: held taint ∪ the frozen `output_conf` of every pending record of `agent`
    /// (including quarantined and monitor-bypassed ones). NOTE: extraction-safe index loop with
    /// owned `get_cloned` per entry (val_at borrows are avoided under the §13 discipline).
    pub fn speculative_taint(&self, agent: &AgentId) -> VecSet<ConfLevel> {
        let mut taint: VecSet<ConfLevel> = self.taint_levels.get_set_or_empty(agent);
        let mut i = 0;
        while i < self.pending.len() {
            let inv = self.pending.key_at(i).clone();
            if let Some(j) = self.pending.get_cloned(&inv) {
                if j.agent == *agent {
                    taint.insert(j.policy.output_conf);
                }
            }
            i += 1;
        }
        taint
    }

    /// Worst-case integrity: held integrity ∪ the frozen `output_integ` of every pending record of
    /// `agent` (dual of `speculative_taint`).
    pub fn speculative_integ(&self, agent: &AgentId) -> VecSet<IntegLevel> {
        let mut integ: VecSet<IntegLevel> = self.integ_levels.get_set_or_empty(agent);
        let mut i = 0;
        while i < self.pending.len() {
            let inv = self.pending.key_at(i).clone();
            if let Some(j) = self.pending.get_cloned(&inv) {
                if j.agent == *agent {
                    integ.insert(j.policy.output_integ);
                }
            }
            i += 1;
        }
        integ
    }

    /// Held taint ∪ `output_conf` of the agent's *contained* pending records only. Clearance
    /// confinement reads this filtered set; admission checks read the unrestricted set (E10).
    pub fn speculative_taint_contained(&self, agent: &AgentId) -> VecSet<ConfLevel> {
        let mut taint: VecSet<ConfLevel> = self.taint_levels.get_set_or_empty(agent);
        let mut i = 0;
        while i < self.pending.len() {
            let inv = self.pending.key_at(i).clone();
            if let Some(j) = self.pending.get_cloned(&inv) {
                if j.agent == *agent && j.contained() {
                    taint.insert(j.policy.output_conf);
                }
            }
            i += 1;
        }
        taint
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{ActionPolicySnapshot, Admission, Disposition, PolicyDigest};

    fn snap(output_conf: ConfLevel, output_integ: IntegLevel) -> ActionPolicySnapshot {
        ActionPolicySnapshot {
            tool: ToolId::new("t"),
            required_caps: VecSet::new(),
            conf_clearance: ConfLevel::Restricted,
            integ_floor: IntegLevel::Untrusted,
            integ_inspect: IntegLevel::Untrusted,
            output_conf,
            output_integ,
            declared_egress: VecSet::new(),
            policy_digest: PolicyDigest::new("d"),
        }
    }

    fn pending(
        agent: &str,
        disposition: Disposition,
        oc: ConfLevel,
        oi: IntegLevel,
    ) -> PendingInvocation {
        PendingInvocation {
            agent: AgentId::new(agent),
            policy: snap(oc, oi),
            egress: VecSet::new(),
            admission: Admission::Plain,
            disposition,
            authorized: true,
            quarantined: false,
        }
    }

    #[test]
    fn initial_state_has_root_active_with_all_caps() {
        let state = KernelState::initial();
        assert!(state.agent_active.contains(&AgentId::root()));
        let root_caps = state.agent_cap.get(&AgentId::root()).unwrap();
        for kind in CapKind::ALL {
            assert!(root_caps.contains(&kind), "root missing cap: {kind}");
        }
    }

    #[test]
    fn initial_state_is_empty_everywhere_else() {
        let state = KernelState::initial();
        assert!(state.agent_parent.is_empty());
        assert!(state.taint_levels.is_empty());
        assert!(state.integ_levels.is_empty());
        assert!(state.pending.is_empty());
        assert!(state.challenges.is_empty());
        assert!(state.consumed_ids.is_empty());
        assert!(state.consumed_attestations.is_empty());
        assert!(state.consumed_crossings.is_empty());
        assert!(state.crossing_grants.is_empty());
        assert!(state.tool_registered.is_empty());
    }

    #[test]
    fn state_version_is_five() {
        assert_eq!(STATE_VERSION, 5);
    }

    #[test]
    fn speculative_taint_empty_for_clean_agent() {
        let state = KernelState::initial();
        assert!(state.speculative_taint(&AgentId::new("a1")).is_empty());
    }

    #[test]
    fn speculative_taint_includes_pending_output_conf() {
        let mut state = KernelState::initial();
        let a = AgentId::new("a1");
        state.pending.insert(
            InvocationId::new("inv-1"),
            pending(
                "a1",
                Disposition::Permitted,
                ConfLevel::Sensitive,
                IntegLevel::Attested,
            ),
        );
        let taint = state.speculative_taint(&a);
        assert!(taint.contains(&ConfLevel::Sensitive));
    }

    #[test]
    fn speculative_taint_includes_bypassed_but_contained_filters_it() {
        let mut state = KernelState::initial();
        let a = AgentId::new("a1");
        state.pending.insert(
            InvocationId::new("inv-b"),
            pending(
                "a1",
                Disposition::MonitorBypassed,
                ConfLevel::Restricted,
                IntegLevel::Untrusted,
            ),
        );
        // Unrestricted speculative set includes the bypassed record...
        assert!(state.speculative_taint(&a).contains(&ConfLevel::Restricted));
        // ...but the contained filter (E10) excludes it.
        assert!(
            !state
                .speculative_taint_contained(&a)
                .contains(&ConfLevel::Restricted)
        );
    }

    #[test]
    fn speculative_integ_includes_pending_output_integ() {
        let mut state = KernelState::initial();
        let a = AgentId::new("a1");
        state.pending.insert(
            InvocationId::new("inv-1"),
            pending(
                "a1",
                Disposition::Permitted,
                ConfLevel::Public,
                IntegLevel::Untrusted,
            ),
        );
        assert!(state.speculative_integ(&a).contains(&IntegLevel::Untrusted));
    }

    #[test]
    fn speculative_integ_includes_held_levels() {
        let mut state = KernelState::initial();
        let a = AgentId::new("a1");
        state
            .integ_levels
            .insert_into(a.clone(), IntegLevel::Standard);
        assert!(state.speculative_integ(&a).contains(&IntegLevel::Standard));
    }
}
