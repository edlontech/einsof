import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `return_endorsed` preserves the unified `R`

`return_endorsed` debits `parent`'s budget by one level (`VecMap.insert`), framing everything else as
`{ st with agent_budget := vm }` (via `debitBudget_full`). All non-budget conjuncts transport
definitionally; the budget conjunct uses the get-style `budgetReadC` post + `budgetC` injectivity (the
same lattice walk as `return_endorsed_refines`), and `R.ndBudget` re-establishes via the insert's nodup
post. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Comprehensive inversion: gates + structural budget-debit frame + nodup post. -/
theorem return_endorsed_inv_full
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (child parent : types.AgentId)
    (hcap : st.agent_budget.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.return_endorsed st bg child parent = .ok (.Ok (st', ev))) :
    ∃ vm,
      vmLastEntry st.agent_parent.entries.val child = some (child, parent) ∧
      vsMem st.agent_active child ∧ vsMem st.agent_active parent ∧
      (∀ inv, ¬ vmsMemLast st.in_flight child inv) ∧
      vmsMem st.agent_cap child capability.CapKind.Declassify ∧
      budgetReadC st.agent_budget parent ≠ types.BudgetLevel.Exhausted ∧
      st' = { st with agent_budget := vm } ∧
      (∀ G, budgetReadC vm G =
        if G = parent then debitC (budgetReadC st.agent_budget parent) else budgetReadC st.agent_budget G) ∧
      (vmNodupKeys st.agent_budget → vmNodupKeys vm) := by
  simp only [transitions.return_endorsed] at hok
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGet_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.AgentId.Insts.CoreCloneClone st.agent_parent child)
  rw [hoEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨b, hbEq, hbIff⟩ :
      ∃ bb, core.option.Option.Insts.CoreCmpPartialEqOption.ne
        (core.cmp.PartialEqShared types.AgentId.Insts.CoreCmpPartialEqAgentId) o (some parent) =
        .ok bb ∧ (bb = true ↔ o ≠ some parent) :=
    ⟨_, optionAgentId_ne_spec o (some parent), by simp⟩
  rw [hbEq] at hok
  simp only [bind_tc_ok] at hok
  have hb : b = false := by cases b with | false => rfl | true => simp at hok
  simp only [hb, reduceIte, Bool.false_eq_true] at hok
  have hoP : o = some parent := by
    by_contra hc; have := hbIff.mpr hc; rw [hb] at this; simp at this
  have hlast : vmLastEntry st.agent_parent.entries.val child = some (child, parent) := by
    have hoP' : (vmLastEntry st.agent_parent.entries.val child).map Prod.snd = some parent := by
      rw [← ho]; exact hoP
    cases hL : vmLastEntry st.agent_parent.entries.val child with
    | none => rw [hL] at hoP'; simp at hoP'
    | some p =>
      have hp1 : p.1 = child := vmLastEntry_fst _ _ _ hL
      rw [hL, Option.map_some] at hoP'
      obtain ⟨x, y⟩ := p
      simp only [Option.some_inj] at hoP'
      simp_all
  obtain ⟨b1, hb1Eq, hb1Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active child)
  rw [hb1Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb1 : b1 = true := by cases b1 with | true => rfl | false => simp at hok
  simp only [hb1, reduceIte] at hok
  obtain ⟨b2, hb2Eq, hb2Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active parent)
  rw [hb2Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb2 : b2 = true := by cases b2 with | true => rfl | false => simp at hok
  simp only [hb2, reduceIte] at hok
  obtain ⟨b3, hb3Eq, hb3Iff⟩ := spec_imp_exists
    (vecMapKVecSetSetNonempty_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight child)
  rw [hb3Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb3 : b3 = false := by cases b3 with | false => rfl | true => simp at hok
  simp only [hb3, reduceIte, Bool.false_eq_true] at hok
  have hNoFlight : ∀ inv, ¬ vmsMemLast st.in_flight child inv := by
    intro inv hc
    have : b3 = true := hb3Iff.mpr ⟨inv, hc⟩
    rw [hb3] at this; simp at this
  obtain ⟨b4, hb4Eq, hb4Imp⟩ := spec_imp_exists
    (vecMapKVecSetSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      capability.CapKind.Insts.CoreCloneClone capability.CapKind.Insts.CoreCmpPartialEqCapKind
      capKind_eq_spec capKind_clone_spec st.agent_cap child capability.CapKind.Declassify)
  rw [hb4Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb4 : b4 = true := by cases b4 with | true => rfl | false => simp at hok
  simp only [hb4, reduceIte] at hok
  obtain ⟨b5, hb5Eq, hb5Iff⟩ := spec_imp_exists (budgetExhausted_spec st parent)
  rw [hb5Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb5 : b5 = false := by cases b5 with | false => rfl | true => simp at hok
  simp only [hb5, reduceIte, Bool.false_eq_true] at hok
  have hNotExh : budgetReadC st.agent_budget parent ≠ types.BudgetLevel.Exhausted := by
    intro hc; have : b5 = true := hb5Iff.mpr hc; rw [hb5] at this; simp at this
  obtain ⟨st1, hst1Eq, vm, hStruct, hBud, hBudNd⟩ := spec_imp_exists (debitBudget_full st parent hcap)
  rw [hst1Eq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _hEventEq⟩ := hok
  exact ⟨vm, hlast, hb1Iff.mp hb1, hb2Iff.mp hb2, hNoFlight, hb4Imp hb4, hNotExh,
    hStateEq.symm.trans hStruct, hBud, hBudNd⟩

/-- `return_endorsed` preserves the unified `R`. -/
theorem return_endorsed_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (child parent : types.AgentId)
    (hR : R st bg a)
    (hcap : st.agent_budget.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.return_endorsed st bg child parent = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.return_endorsed child parent).guard a ∧
          (Tzimtzum.return_endorsed child parent).next a a' ∧ R st' bg a' := by
  obtain ⟨vm, hParentEdge, hChildActive, hParentActive, hNoFlight, hChildCap, hNotExh, rfl, hBud,
      hBudNd⟩ := return_endorsed_inv_full st bg child parent hcap st' ev hok
  have hParentActiveA : a.agent_active parent := (hR.active parent).mpr hParentActive
  refine ⟨{ a with agent_budget := fun A L =>
      (A = parent
        ∧ ((a.agent_budget parent Tzimtzum.BudgetLevel.bl5 ∧ L = Tzimtzum.BudgetLevel.bl4)
         ∨ (a.agent_budget parent Tzimtzum.BudgetLevel.bl4 ∧ L = Tzimtzum.BudgetLevel.bl3)
         ∨ (a.agent_budget parent Tzimtzum.BudgetLevel.bl3 ∧ L = Tzimtzum.BudgetLevel.bl2)
         ∨ (a.agent_budget parent Tzimtzum.BudgetLevel.bl2 ∧ L = Tzimtzum.BudgetLevel.bl1)
         ∨ (a.agent_budget parent Tzimtzum.BudgetLevel.bl1 ∧ L = Tzimtzum.BudgetLevel.bl_exhausted)))
      ∨ (A ≠ parent ∧ a.agent_budget A L) }, ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.return_endorsed]
    refine ⟨(hR.parent child parent).mpr hParentEdge, (hR.active child).mpr hChildActive,
      hParentActiveA, ?_, ?_, trivial, ?_⟩
    · intro I hc; exact hNoFlight I ((hR.inflight child I).mp hc)
    · rw [hR.cap_declass]
      exact (hR.cap child capability.CapKind.Declassify).mpr
        ((vmsMem_iff_vmsMemLast st.agent_cap hR.ndCap child capability.CapKind.Declassify).mp hChildCap)
    · intro hc
      exact hNotExh ((hR.budget parent Tzimtzum.BudgetLevel.bl_exhausted hParentActiveA).mp hc)
  · -- next
    simp [Tzimtzum.return_endorsed]
  · -- R st' bg a'
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.active, hR.tool_reg, hR.parent, hR.cap,
      hR.instr, hR.taint, hR.inflight, hR.ghInvoked, hR.ghReceived, hR.override, ?_, hR.toolCap,
      hR.toolEgress, hR.toolFloor, hR.toolBounded, hR.toolIssuer, hR.trustedIss, hR.instrIssuer,
      hR.flowAllows, hR.flowInspects, hR.flowOverride, hR.invTool, hR.ndParent, hR.ndCap, hR.ndInstr,
      hR.ndTaint, hR.ndInflight, hR.ndGhInvoked, hR.ndGhReceived, hR.ndOverride, ?_, hR.wfInflight⟩
    · -- budget
      intro G L hactiveG
      show ((G = parent ∧ _) ∨ (G ≠ parent ∧ a.agent_budget G L)) ↔ budgetReadC vm G = budgetC L
      rw [hBud G]
      by_cases hG : G = parent
      · subst hG
        simp only [if_pos rfl, true_and, and_self, ne_eq, not_true_eq_false, false_and, or_false]
        rw [hR.budget G Tzimtzum.BudgetLevel.bl5 hactiveG, hR.budget G Tzimtzum.BudgetLevel.bl4 hactiveG,
          hR.budget G Tzimtzum.BudgetLevel.bl3 hactiveG, hR.budget G Tzimtzum.BudgetLevel.bl2 hactiveG,
          hR.budget G Tzimtzum.BudgetLevel.bl1 hactiveG]
        cases hcur : budgetReadC st.agent_budget G <;> cases L <;> simp_all [debitC, budgetC]
      · rw [if_neg hG]
        constructor
        · rintro (⟨hp, _⟩ | ⟨_, hab⟩)
          · exact absurd hp hG
          · rw [← hR.budget G L hactiveG]; exact hab
        · intro hread
          exact Or.inr ⟨hG, (hR.budget G L hactiveG).mpr hread⟩
    · -- ndBudget
      exact hBudNd hR.ndBudget

end ArgusLean.Refinement
