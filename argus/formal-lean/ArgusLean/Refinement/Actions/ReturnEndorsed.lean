import ArgusLean.Refinement.StateRelation

/-! # Refinement — `return_endorsed`

`return_endorsed child parent` is the capability-gated, recipient-budget-charged cross-boundary
declassification (no taint propagation). Six read gates — `child`'s parent edge is `parent`, both
agents active, `child` has no in-flight invocation, `child` holds the `Declassify` capability, and
`parent`'s budget is not exhausted — followed by a single write: `parent`'s budget is **debited** by
one level (`VecMap.insert` of the saturating predecessor).

It refines against `Rret`, whose budget clause is the get-style `budgetReadC` convention (the read the
kernel's `budget`/`debit_budget` literally compute) tied to the abstract lattice through `budgetC`.
The parent-edge gate is read get-style (`vmLastEntry`, like the tree actions); the `child`-has-no-
in-flight gate through the last-match nested membership `vmsMemLast` (what `set_nonempty` observes);
the `Declassify` capability via the forward `set_contains` → raw `vmsMem` view (like
`grant_capability`). The body reuses `debitBudget_spec`. No agent is added or removed and the root is
never named, so beyond the `register_tool` baseline the only extractor residual is
`optionAgentId_ne_spec` (the parent-edge gate); the `BudgetLevel` eq/clone/debit facts are *proved*
(a nullary enum), not trusted. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Inversion lemma for a successful `return_endorsed` step. Peels the parent-edge gate (`VecMap.get`
    + `Option.ne`, like `grant_capability`), the two active gates, the `set_nonempty` in-flight gate
    (`false` → no last-match nested membership), the `set_contains` capability gate (forward →
    `vmsMem`), and the `budget_exhausted` gate, then reads off the single `agent_budget` debit. -/
theorem return_endorsed_ok_inv
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (child parent : types.AgentId)
    (hcap : st.agent_budget.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.return_endorsed st bg child parent = .ok (.Ok (st', ev))) :
    vmLastEntry st.agent_parent.entries.val child = some (child, parent) ∧
    vsMem st.agent_active child ∧
    vsMem st.agent_active parent ∧
    (∀ inv, ¬ vmsMemLast st.in_flight child inv) ∧
    vmsMem st.agent_cap child capability.CapKind.Declassify ∧
    budgetReadC st.agent_budget parent ≠ types.BudgetLevel.Exhausted ∧
    st'.agent_active = st.agent_active ∧ st'.agent_parent = st.agent_parent ∧
    st'.agent_cap = st.agent_cap ∧ st'.in_flight = st.in_flight ∧
    st'.taint_levels = st.taint_levels ∧ st'.gh_taint_received = st.gh_taint_received ∧
    st'.override_used = st.override_used ∧
    (∀ G, budgetReadC st'.agent_budget G =
      if G = parent then debitC (budgetReadC st.agent_budget parent)
      else budgetReadC st.agent_budget G) := by
  simp only [transitions.return_endorsed] at hok
  -- Gate 1: the parent edge `child → parent`.
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
    by_contra hc
    have := hbIff.mpr hc; rw [hb] at this; simp at this
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
  -- Gate 2: child active.
  obtain ⟨b1, hb1Eq, hb1Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active child)
  rw [hb1Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb1 : b1 = true := by cases b1 with | true => rfl | false => simp at hok
  simp only [hb1, reduceIte] at hok
  -- Gate 3: parent active.
  obtain ⟨b2, hb2Eq, hb2Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active parent)
  rw [hb2Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb2 : b2 = true := by cases b2 with | true => rfl | false => simp at hok
  simp only [hb2, reduceIte] at hok
  -- Gate 4: `child` has no in-flight invocation.
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
  -- Gate 5: `child` holds the `Declassify` capability.
  obtain ⟨b4, hb4Eq, hb4Imp⟩ := spec_imp_exists
    (vecMapKVecSetSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      capability.CapKind.Insts.CoreCloneClone capability.CapKind.Insts.CoreCmpPartialEqCapKind
      capKind_eq_spec capKind_clone_spec st.agent_cap child capability.CapKind.Declassify)
  rw [hb4Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb4 : b4 = true := by cases b4 with | true => rfl | false => simp at hok
  simp only [hb4, reduceIte] at hok
  -- Gate 6: `parent`'s budget is not exhausted.
  obtain ⟨b5, hb5Eq, hb5Iff⟩ := spec_imp_exists (budgetExhausted_spec st parent)
  rw [hb5Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb5 : b5 = false := by cases b5 with | false => rfl | true => simp at hok
  simp only [hb5, reduceIte, Bool.false_eq_true] at hok
  have hNotExh : budgetReadC st.agent_budget parent ≠ types.BudgetLevel.Exhausted := by
    intro hc; have : b5 = true := hb5Iff.mpr hc; rw [hb5] at this; simp at this
  -- Body: debit `parent`'s budget.
  obtain ⟨st1, hst1Eq, hAct, hPar, hCap, hFl, hTaint, hGh, hOv, _, _, _, _, hBud⟩ :=
    spec_imp_exists (debitBudget_spec st parent hcap)
  rw [hst1Eq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _hEventEq⟩ := hok
  subst hStateEq
  exact ⟨hlast, hb1Iff.mp hb1, hb2Iff.mp hb2, hNoFlight, hb4Imp hb4, hNotExh,
    hAct, hPar, hCap, hFl, hTaint, hGh, hOv, hBud⟩

/-- Forward simulation: a successful `return_endorsed` step is matched by the abstract action,
    preserving `Rret`. The witness debits `parent`'s budget by one level and frames everything else;
    the get-style `budgetReadC` convention + `budgetC` injectivity carry the budget clause through. -/
theorem return_endorsed_refines
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (child parent : types.AgentId)
    (hR : Rret st a)
    (hcap : st.agent_budget.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.return_endorsed st bg child parent = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.return_endorsed child parent).guard a ∧
          (Tzimtzum.return_endorsed child parent).next a a' ∧ Rret st' a' := by
  obtain ⟨hRdecl, hRactive, hRparent, hRflight, hRcap, hRbudget⟩ := hR
  obtain ⟨hParentEdge, hChildActive, hParentActive, hNoFlight, hChildCap, hNotExh,
      hAct, hPar, hCap, hFl, hTaint, hGh, hOv, hBud⟩ :=
    return_endorsed_ok_inv st bg child parent hcap st' ev hok
  refine ⟨{a with agent_budget := fun A L =>
      (A = parent
        ∧ ((a.agent_budget parent Tzimtzum.BudgetLevel.bl5 ∧ L = Tzimtzum.BudgetLevel.bl4)
         ∨ (a.agent_budget parent Tzimtzum.BudgetLevel.bl4 ∧ L = Tzimtzum.BudgetLevel.bl3)
         ∨ (a.agent_budget parent Tzimtzum.BudgetLevel.bl3 ∧ L = Tzimtzum.BudgetLevel.bl2)
         ∨ (a.agent_budget parent Tzimtzum.BudgetLevel.bl2 ∧ L = Tzimtzum.BudgetLevel.bl1)
         ∨ (a.agent_budget parent Tzimtzum.BudgetLevel.bl1 ∧ L = Tzimtzum.BudgetLevel.bl_exhausted)))
      ∨ (A ≠ parent ∧ a.agent_budget A L)}, ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.return_endorsed]
    refine ⟨(hRparent child parent).mpr hParentEdge, (hRactive child).mpr hChildActive,
      (hRactive parent).mpr hParentActive, ?_, ?_, trivial, ?_⟩
    · intro I hc; exact hNoFlight I ((hRflight child I).mp hc)
    · rw [hRdecl]; exact (hRcap child capability.CapKind.Declassify).mpr hChildCap
    · -- ¬ a.agent_budget parent bl_exhausted
      intro hc
      rw [hRbudget parent Tzimtzum.BudgetLevel.bl_exhausted] at hc
      exact hNotExh hc
  · -- next
    simp [Tzimtzum.return_endorsed]
  · -- Rret st' a'
    refine ⟨hRdecl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hAct]; exact hRactive
    · rw [hPar]; exact hRparent
    · intro ag inv; rw [hFl]; exact hRflight ag inv
    · rw [hCap]; exact hRcap
    · -- budget clause: post-state get-style read vs. abstract debit
      intro G L
      show ((G = parent ∧ _) ∨ (G ≠ parent ∧ a.agent_budget G L)) ↔
        budgetReadC st'.agent_budget G = budgetC L
      rw [hBud G]
      by_cases hG : G = parent
      · subst hG
        simp only [if_pos rfl, true_and, and_self, ne_eq, not_true_eq_false, false_and, or_false]
        -- abstract debit (in terms of a.agent_budget G) ↔ debitC (budgetReadC st G) = budgetC L
        have hb5 := hRbudget G Tzimtzum.BudgetLevel.bl5
        have hb4 := hRbudget G Tzimtzum.BudgetLevel.bl4
        have hb3 := hRbudget G Tzimtzum.BudgetLevel.bl3
        have hb2 := hRbudget G Tzimtzum.BudgetLevel.bl2
        have hb1 := hRbudget G Tzimtzum.BudgetLevel.bl1
        rw [hb5, hb4, hb3, hb2, hb1]
        -- now purely about budgetReadC st G : decide on the concrete level
        cases hcur : budgetReadC st.agent_budget G <;>
          cases L <;>
          simp_all [debitC, budgetC]
      · rw [if_neg hG]
        constructor
        · rintro (⟨hp, _⟩ | ⟨_, hab⟩)
          · exact absurd hp hG
          · rw [← hRbudget G L]; exact hab
        · intro hread
          exact Or.inr ⟨hG, (hRbudget G L).mpr hread⟩

end ArgusLean.Refinement

-- Trust-base audit. Beyond the three standard axioms: the `register_tool` `String`/id residuals plus
-- `optionAgentId_ne_spec` (the `Option AgentId` parent-edge gate, `agentId_ne_spec` class). The
-- `BudgetLevel` eq/clone/debit facts are PROVED (nullary enum), not trusted. `return_endorsed` adds
-- and removes no agent and never names the root, so it carries NO `sorryAx`/`AgentId.root` residual.
#print axioms ArgusLean.Refinement.return_endorsed_ok_inv
#print axioms ArgusLean.Refinement.return_endorsed_refines
