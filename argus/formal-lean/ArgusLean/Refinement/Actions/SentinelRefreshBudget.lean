import ArgusLean.Refinement.StateRelation

/-! # Refinement — `sentinel_refresh_budget`

`sentinel_refresh_budget agent` is the capability-gated budget reset: two read gates (`agent`
active, `agent` holds the `RefreshBudget` capability) followed by a single write — `agent`'s entry
is **deleted** from `agent_budget`. The kernel's "absent key ⇒ full budget (`bl5`)" convention then
reads the now-absent entry back as full, which is exactly the abstract action's post-image
(`agent`'s budget set to `bl5`).

Unlike `revoke` / `cascade_revoke` — the other `VecMap.remove`-on-budget actions — `agent` stays
**active** here, so the convention is observable on the very agent that changed and the *unguarded*
`Rdel`-style budget clause is faithful (`Rrefresh`, not `Rcasc`'s active-guarded variant). The cap
gate reuses `set_contains` (forward → `vmsMem`) and the proved `CapKind` eq/clone; the remove reuses
`vecMapRemove_spec`. No agent is added or removed, no root is named — so no new axioms and no
`sorryAx`/`AgentId.root` residual beyond the `register_tool` baseline. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Inversion lemma for a successful `sentinel_refresh_budget` step. Peels the two gates (active via
    `VecSet.contains`, the `RefreshBudget` cap via `set_contains`'s forward direction) and reads off
    the single `agent_budget` write as the key-filtered entry list (`VecMap.remove`). -/
theorem sentinel_refresh_budget_ok_inv
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (agent : types.AgentId)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.sentinel_refresh_budget st bg agent = .ok (.Ok (st', ev))) :
    ∃ vm,
      vsMem st.agent_active agent ∧
      vmsMem st.agent_cap agent capability.CapKind.RefreshBudget ∧
      st' = { st with agent_budget := vm } ∧
      vm.entries.val = st.agent_budget.entries.val.filter (removeKept agent) := by
  simp only [transitions.sentinel_refresh_budget] at hok
  -- Gate 1: `agent` active.
  obtain ⟨b, hbEq, hbIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active agent)
  rw [hbEq] at hok
  simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  -- Gate 2: `agent` holds the `RefreshBudget` capability.
  obtain ⟨b1, hb1Eq, hb1Imp⟩ := spec_imp_exists
    (vecMapKVecSetSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      capability.CapKind.Insts.CoreCloneClone capability.CapKind.Insts.CoreCmpPartialEqCapKind
      capKind_eq_spec capKind_clone_spec st.agent_cap agent capability.CapKind.RefreshBudget)
  rw [hb1Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb1 : b1 = true := by cases b1 with | true => rfl | false => simp at hok
  simp only [hb1, reduceIte] at hok
  -- Body: delete `agent`'s budget entry.
  obtain ⟨vm, hvmEq, hvmChar⟩ := spec_imp_exists
    (vecMapRemove_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_ne_spec
      types.BudgetLevel.Insts.CoreCloneClone st.agent_budget agent)
  rw [hvmEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _hEventEq⟩ := hok
  exact ⟨vm, hbIff.mp hb, hb1Imp hb1, hStateEq.symm, hvmChar⟩

/-- Forward simulation: a successful `sentinel_refresh_budget` step is matched by the abstract action,
    preserving `Rrefresh`. The witness sets `agent`'s budget to `bl5` and frames everything else; the
    delete-then-read-as-`bl5` convention closes the `agent` case, and `mem_filter_removeKept` carries
    the others through unchanged. -/
theorem sentinel_refresh_budget_refines
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (agent : types.AgentId)
    (hR : Rrefresh st a)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.sentinel_refresh_budget st bg agent = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.sentinel_refresh_budget agent).guard a ∧
          (Tzimtzum.sentinel_refresh_budget agent).next a a' ∧ Rrefresh st' a' := by
  obtain ⟨hRcapconst, hRactive, hRcap, hRbudget⟩ := hR
  obtain ⟨vm, hAgentActive, hAgentCap, hStEq, hvmChar⟩ :=
    sentinel_refresh_budget_ok_inv st bg agent st' ev hok
  refine ⟨{a with agent_budget :=
      fun A L => (A = agent ∧ L = Tzimtzum.BudgetLevel.bl5) ∨ (A ≠ agent ∧ a.agent_budget A L)},
    ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.sentinel_refresh_budget]
    refine ⟨(hRactive agent).mpr hAgentActive, ?_⟩
    rw [hRcapconst]
    exact (hRcap agent capability.CapKind.RefreshBudget).mpr hAgentCap
  · -- next
    simp [Tzimtzum.sentinel_refresh_budget]
  · -- Rrefresh st' a'
    subst hStEq
    refine ⟨hRcapconst, hRactive, hRcap, ?_⟩
    intro G L
    show ((G = agent ∧ L = Tzimtzum.BudgetLevel.bl5) ∨ (G ≠ agent ∧ a.agent_budget G L)) ↔
      ((G, budgetC L) ∈ vm.entries.val) ∨
      ((∀ bl, (G, bl) ∉ vm.entries.val) ∧ L = Tzimtzum.BudgetLevel.bl5)
    rw [hvmChar]
    by_cases hG : G = agent
    · subst hG
      constructor
      · rintro (⟨_, hL5⟩ | ⟨hne, _⟩)
        · exact Or.inr ⟨fun bl hc => ((mem_filter_removeKept _ _ _ _).mp hc).2 rfl, hL5⟩
        · exact absurd rfl hne
      · rintro (hmem | ⟨_, hL5⟩)
        · exact absurd rfl ((mem_filter_removeKept _ _ _ _).mp hmem).2
        · exact Or.inl ⟨rfl, hL5⟩
    · have hLHS :
          ((G = agent ∧ L = Tzimtzum.BudgetLevel.bl5) ∨ (G ≠ agent ∧ a.agent_budget G L)) ↔
            a.agent_budget G L :=
        ⟨fun h => h.elim (fun hp => absurd hp.1 hG) (fun hp => hp.2), fun h => Or.inr ⟨hG, h⟩⟩
      rw [hLHS, hRbudget G L]
      constructor
      · rintro (hmem | ⟨hab, h5⟩)
        · exact Or.inl ((mem_filter_removeKept _ _ _ _).mpr ⟨hmem, hG⟩)
        · exact Or.inr ⟨fun bl hc => hab bl ((mem_filter_removeKept _ _ _ _).mp hc).1, h5⟩
      · rintro (hmem | ⟨hab, h5⟩)
        · exact Or.inl ((mem_filter_removeKept _ _ _ _).mp hmem).1
        · exact Or.inr ⟨fun bl hc => hab bl ((mem_filter_removeKept _ _ _ _).mpr ⟨hc, hG⟩), h5⟩

end ArgusLean.Refinement

-- Trust-base audit. Beyond the three standard axioms: the `register_tool` `String`/id residuals
-- (`agentId_eq_spec` / `agentId_ne_spec` via `string_*`). The `CapKind` eq/clone facts are PROVED
-- (nullary enum), not trusted. `sentinel_refresh_budget` adds and removes no agent and never names
-- the root, so it carries NO `optionAgentId_ne_spec` and NO `sorryAx`/`AgentId.root` residual.
#print axioms ArgusLean.Refinement.sentinel_refresh_budget_ok_inv
#print axioms ArgusLean.Refinement.sentinel_refresh_budget_refines
