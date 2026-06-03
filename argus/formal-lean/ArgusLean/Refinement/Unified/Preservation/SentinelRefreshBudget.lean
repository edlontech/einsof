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
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.active, hR.tool_reg, hR.parent, hR.cap,
      hR.instr, hR.taint, hR.inflight, hR.ghInvoked, hR.ghReceived, hR.override, ?_, hR.toolCap,
      hR.toolEgress, hR.toolFloor, hR.toolBounded, hR.toolIssuer, hR.trustedIss, hR.instrIssuer,
      hR.flowAllows, hR.flowInspects, hR.flowOverride, hR.invTool, hR.ndParent, hR.ndCap, hR.ndInstr,
      hR.ndTaint, hR.ndInflight, hR.ndGhInvoked, hR.ndGhReceived, hR.ndOverride, ?_, hR.wfInflight⟩
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
