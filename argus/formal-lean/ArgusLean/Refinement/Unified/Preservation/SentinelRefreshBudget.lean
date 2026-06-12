import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `sentinel_refresh_budget` preserves the unified `R`

`sentinel_refresh_budget` deletes `agent`'s `agent_budget` entry (a `VecMap.remove`), framing
everything else. The first **budget** action: `R`'s canonical budget view is the active-guarded
`budgetReadC`, bridged from the raw-membership filter post (`sentinel_refresh_budget_ok_inv`) via
`budgetRaw_iff_budgetReadC` (key-uniqueness of the filtered budget map). The cap read-gate (`vmsMem`)
is bridged to `R`'s `vmsMemLast` cap view via `R.ndCap`. -/

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

/-- `sentinel_refresh_budget` preserves the unified `R`. -/
theorem sentinel_refresh_budget_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (agent : types.AgentId)
    (hR : R st bg a)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.sentinel_refresh_budget st bg agent = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.sentinel_refresh_budget agent).guard a ∧
          (Tzimtzum.sentinel_refresh_budget agent).next a a' ∧ R st' bg a' := by
  obtain ⟨vm, hAgentActive, hAgentCap, rfl, hvmChar⟩ :=
    sentinel_refresh_budget_ok_inv st bg agent st' ev hok
  have hndVm : vmNodupKeys vm := by
    unfold vmNodupKeys; rw [hvmChar]; exact vmNodupKeys_filter st.agent_budget.entries.val agent hR.ndBudget
  refine ⟨{ a with agent_budget :=
      fun A L => (A = agent ∧ L = Tzimtzum.BudgetLevel.bl5) ∨ (A ≠ agent ∧ a.agent_budget A L) },
    ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.sentinel_refresh_budget]
    refine ⟨(hR.active agent).mpr hAgentActive, ?_⟩
    rw [hR.cap_refresh]
    exact (hR.cap agent capability.CapKind.RefreshBudget).mpr
      ((vmsMem_iff_vmsMemLast st.agent_cap hR.ndCap agent capability.CapKind.RefreshBudget).mp hAgentCap)
  · -- next
    simp [Tzimtzum.sentinel_refresh_budget]
  · -- R st' bg a'
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov, hR.active, hR.tool_reg, hR.parent, hR.cap,
      hR.instr, hR.taint, hR.inflight, hR.ghInvoked, hR.ghReceived, hR.override, ?_, hR.toolCap,
      hR.toolEgress, hR.toolFloor, hR.toolBounded, hR.toolIssuer, hR.trustedIss, hR.instrIssuer,
      hR.flowAllows, hR.flowInspects, hR.flowOverride, hR.invTool, hR.ndParent, hR.ndCap, hR.ndInstr,
      hR.ndTaint, hR.ndInflight, hR.ndGhInvoked, hR.ndGhReceived, hR.ndOverride, hR.ndFlowOverride,
      ?_, hR.wfInflight⟩
    · -- budget (active-guarded budgetReadC; the deleted entry reads back as full on `agent`, and is
      -- untouched off `agent`)
      intro G L hactiveG
      have hbr : budgetReadC vm G =
          if G = agent then types.BudgetLevel.L5 else budgetReadC st.agent_budget G := by
        unfold budgetReadC
        rw [hvmChar, vmLastEntry_filter_removeKept]
        by_cases hG : G = agent <;> simp [hG]
      show ((G = agent ∧ L = Tzimtzum.BudgetLevel.bl5) ∨ (G ≠ agent ∧ a.agent_budget G L)) ↔
        budgetReadC vm G = budgetC L
      rw [hbr]
      by_cases hG : G = agent
      · rw [if_pos hG]
        constructor
        · rintro (⟨_, hL5⟩ | ⟨hne, _⟩)
          · subst hL5; rfl
          · exact absurd hG hne
        · intro h
          exact Or.inl ⟨hG, (@budgetC_injective Tzimtzum.BudgetLevel.bl5 L h).symm⟩
      · rw [if_neg hG]
        have hLHS :
            ((G = agent ∧ L = Tzimtzum.BudgetLevel.bl5) ∨ (G ≠ agent ∧ a.agent_budget G L)) ↔
              a.agent_budget G L :=
          ⟨fun h => h.elim (fun hp => absurd hp.1 hG) (fun hp => hp.2), fun h => Or.inr ⟨hG, h⟩⟩
        rw [hLHS]
        exact hR.budget G L hactiveG
    · -- ndBudget
      exact hndVm

end ArgusLean.Refinement
