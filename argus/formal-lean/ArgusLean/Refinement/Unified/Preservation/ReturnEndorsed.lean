import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `return_endorsed` preserves the unified `R`

`return_endorsed` (Campaign B) gates the endorsed cross-boundary return on the new `return_conforms`
oracle (P2: closes the content-blind gap), then debits `parent`'s budget by the flat weight `2`
(`VecMap.insert` via the numeric `debit_budget`), framing everything else as
`{ st with agent_budget := vm }` (via `debitBudget_full`). The `NotConforming` arm refines the abstract
`require return_conforms`; the unaffordable arm (`BudgetExhausted`) refines `require affordable prnt 2`.
The budget conjunct uses the get-style `budgetReadC` post + the numeric `saturatingSub_val` collapse,
and `R.ndBudget` re-establishes via the insert's nodup post.

The `return_conforms` oracle is a runtime input (not stored state), so — like `invoke_complete`'s
`output_conforms` — it is supplied as a state-independent agreement hypothesis (`rcOf` + `hrc` + `hrcA`),
NOT folded into `R`. Threading it through the `OracleFidelity` bundle (the `RcAgree` predicate in
`Relation.lean`) is Task 16. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Comprehensive inversion: gates (incl. the `return_conforms` verdict and the weight-2 affordability)
    + structural budget-debit frame + nodup post. The `return_conforms` value is the state-independent
    `rcOf` (`hrc`); success forces it `true`. -/
theorem return_endorsed_inv_full {F : Type} (cfInst : traits.ConformanceOracle F)
    (st : state.KernelState) (bg : background.BackgroundTheory) (conformance : F)
    (child parent : types.AgentId)
    (rcOf : Bool)
    (hrc : ∀ s, cfInst.return_conforms conformance child parent s bg = .ok rcOf)
    (hcap : st.agent_budget.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.return_endorsed cfInst st bg conformance child parent = .ok (.Ok (st', ev))) :
    ∃ vm,
      vmLastEntry st.agent_parent.entries.val child = some (child, parent) ∧
      vsMem st.agent_active child ∧ vsMem st.agent_active parent ∧
      (∀ inv, ¬ vmsMemLast st.in_flight child inv) ∧
      vmsMem st.agent_cap child capability.CapKind.Declassify ∧
      rcOf = true ∧
      (2#u8 : Std.U8) ≤ budgetReadC st.agent_budget parent ∧
      st' = { st with agent_budget := vm } ∧
      (∀ G, budgetReadC vm G =
        if G = parent then core.num.U8.saturating_sub (budgetReadC st.agent_budget parent) 2#u8
        else budgetReadC st.agent_budget G) ∧
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
  -- Gate: `return_conforms` verdict (P2). Success forces it `true`.
  rw [hrc st] at hok
  simp only [bind_tc_ok] at hok
  have hrcTrue : rcOf = true := by cases rcOf with | true => rfl | false => simp at hok
  simp only [hrcTrue, reduceIte] at hok
  -- Gate: weight-2 affordability.
  obtain ⟨b6, hb6Eq, hb6Iff⟩ := spec_imp_exists (affordable_spec st parent 2#u8)
  rw [hb6Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb6 : b6 = true := by cases b6 with | true => rfl | false => simp at hok
  simp only [hb6, reduceIte] at hok
  have hAfford : (2#u8 : Std.U8) ≤ budgetReadC st.agent_budget parent := hb6Iff.mp hb6
  obtain ⟨st1, hst1Eq, vm, hStruct, hBud, hBudNd⟩ := spec_imp_exists (debitBudget_full st parent 2#u8 hcap)
  rw [hst1Eq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _hEventEq⟩ := hok
  exact ⟨vm, hlast, hb1Iff.mp hb1, hb2Iff.mp hb2, hNoFlight, hb4Imp hb4, hrcTrue, hAfford,
    hStateEq.symm.trans hStruct, hBud, hBudNd⟩

/-- `return_endorsed` preserves the unified `R`. The `return_conforms` oracle agreement is supplied as
    `hrc` (state-independent value `rcOf`) + `hrcA` (matches the abstract `return_conforms` field);
    Task 16 derives both from the bundle's `RcAgree`. -/
theorem return_endorsed_preservesR {F : Type} (cfInst : traits.ConformanceOracle F)
    (st : state.KernelState) (bg : background.BackgroundTheory) (conformance : F)
    (a : AbsState) (child parent : types.AgentId)
    (rcOf : Bool)
    (hrc : ∀ s, cfInst.return_conforms conformance child parent s bg = .ok rcOf)
    (hrcA : rcOf = true ↔ a.return_conforms child parent)
    (hR : R st bg a)
    (hcap : st.agent_budget.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.return_endorsed cfInst st bg conformance child parent = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.return_endorsed child parent).guard a ∧
          (Tzimtzum.return_endorsed child parent).next a a' ∧ R st' bg a' := by
  obtain ⟨vm, hParentEdge, hChildActive, hParentActive, hNoFlight, hChildCap, hRcTrue, hAfford, rfl,
      hBud, hBudNd⟩ :=
    return_endorsed_inv_full cfInst st bg conformance child parent rcOf hrc hcap st' ev hok
  have hParentActiveA : a.agent_active parent := (hR.active parent).mpr hParentActive
  refine ⟨{ a with agent_budget := fun A L =>
      (A = parent ∧ ∀ b, a.agent_budget parent b → L = b - 2)
      ∨ (A ≠ parent ∧ a.agent_budget A L) }, ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.return_endorsed]
    refine ⟨(hR.parent child parent).mpr hParentEdge, (hR.active child).mpr hChildActive,
      hParentActiveA, ?_, ?_, ?_, ?_⟩
    · intro I hc; exact hNoFlight I ((hR.inflight child I).mp hc)
    · rw [hR.cap_declass]
      exact (hR.cap child capability.CapKind.Declassify).mpr
        ((vmsMem_iff_vmsMemLast st.agent_cap hR.ndCap child capability.CapKind.Declassify).mp hChildCap)
    · -- return_conforms child parent
      exact hrcA.mp hRcTrue
    · -- affordable prnt 2: the abstract budget covers weight 2
      refine ⟨(budgetReadC st.agent_budget parent).val,
        (hR.budget parent _ hParentActiveA).mpr rfl, ?_⟩
      have : (2#u8 : Std.U8).val ≤ (budgetReadC st.agent_budget parent).val := by scalar_tac
      simpa using this
  · -- next
    simp [Tzimtzum.return_endorsed]
  · -- R st' bg a'
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov, hR.active, hR.tool_reg, hR.parent, hR.cap,
      hR.instr, hR.taint, hR.inflight, hR.ghInvoked, hR.ghReceived, hR.override, ?_, hR.toolCap,
      hR.toolEgress, hR.toolFloor, hR.toolBounded, hR.toolIssuer, hR.trustedIss, hR.instrIssuer,
      hR.flowAllows, hR.flowInspects, hR.flowOverride, hR.invTool, hR.ndParent, hR.ndCap, hR.ndInstr,
      hR.ndTaint, hR.ndInflight, hR.ndGhInvoked, hR.ndGhReceived, hR.ndOverride, hR.ndFlowOverride,
      ?_, hR.wfInflight⟩
    · -- budget (parent debit by weight 2; numeric Nat subtraction collapse)
      intro G L hactiveG
      show ((G = parent ∧ ∀ b, a.agent_budget parent b → L = b - 2) ∨ (G ≠ parent ∧ a.agent_budget G L))
        ↔ (budgetReadC vm G).val = L
      rw [hBud G]
      by_cases hG : G = parent
      · subst hG
        simp only [true_and, ne_eq, not_true_eq_false, false_and, or_false, if_true,
          saturatingSub_val]
        have htwo : (2#u8 : Std.U8).val = 2 := by rfl
        rw [htwo]
        constructor
        · intro h
          exact (h (budgetReadC st.agent_budget G).val ((hR.budget G _ hactiveG).mpr rfl)).symm
        · intro hread b hab
          have : (budgetReadC st.agent_budget G).val = b := (hR.budget G b hactiveG).mp hab
          omega
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
