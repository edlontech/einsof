import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `return_endorsed` preserves the unified `R`

V3 rewrite (design §5.4 "Weighted endorsed return" / §5.5, task 11): `return_endorsed` is now
level-parameterized — the caller declares `(clvl, ilvl)`, two coverage loops verify the declaration
bounds the child's entire taint set (`le_conf L clvl`) and lower-bounds its integ set
(`le_integ ilvl L`), the robust-declassification lever loop checks the child's held integrity
clears the lever floor (or sits in the inspect band vouched by `return_conforms` — the same
verdict this action already requires), and the debit is the level-parameterized
`declass_weight clvl + integ_weight ilvl` on the PARENT (recipient pays). Neither taint set
propagates. A clean child returns at `(public, attested)` for weight 0.

The `return_conforms` oracle stays pairwise and state-independent (`rcOf` + `hrc` + `hrcA`, the
`RcAgree` shape); Task 14 derives them from the bundle. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

private theorem declassWeight_le (L : Tzimtzum.ConfLevel) : Tzimtzum.declass_weight L ≤ 4 := by
  cases L <;> decide

private theorem integWeight_le (L : Tzimtzum.IntegLevel) : Tzimtzum.integ_weight L ≤ 4 := by
  cases L <;> decide


/-- Lever loop (loop 0): sticky-denied fold over the child's integ set — denied iff some held
    level neither clears the lever floor nor sits in the vouched inspect band. -/
theorem returnEndorsedLoop0_spec
    (bg : background.BackgroundTheory) (child_integ : collections.VecSet types.IntegLevel)
    (vouched : Bool) (denied0 : Bool) (i0 : Usize)
    (hi0 : i0.val ≤ child_integ.items.val.length)
    (hdenied0 : denied0 = true ↔
      ∃ l ∈ child_integ.items.val.take i0.val,
        (integLeC bg.lever_integ_floor l || (integLeC bg.lever_integ_inspect_floor l && vouched))
          = false) :
    transitions.return_endorsed_loop0 bg child_integ vouched denied0 i0 ⦃ b =>
      (b = true ↔ ∃ l ∈ child_integ.items.val,
        (integLeC bg.lever_integ_floor l || (integLeC bg.lever_integ_inspect_floor l && vouched))
          = false) ⦄ := by
  unfold transitions.return_endorsed_loop0
  apply loop.spec_decr_nat
    (measure := fun p => child_integ.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ child_integ.items.val.length ∧
        (p.1 = true ↔
          ∃ l ∈ child_integ.items.val.take p.2.val,
            (integLeC bg.lever_integ_floor l
              || (integLeC bg.lever_integ_inspect_floor l && vouched)) = false))
  · rintro ⟨denied, i⟩ ⟨hile, hden⟩
    simp only [transitions.return_endorsed_loop0.body]
    have hi1 : collections.VecSet.len types.IntegLevel.Insts.CoreCloneClone
        types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel child_integ =
        .ok (alloc.vec.Vec.len child_integ.items) := rfl
    rw [hi1]; simp only [bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < child_integ.items.val.length := by scalar_tac
      simp only [collections.VecSet.at, background.BackgroundTheory.impl.lever_integ_floor,
        background.BackgroundTheory.impl.lever_integ_inspect_floor, bind_tc_ok]
      step as ⟨lvl, hlvl⟩
      rw [integLevel_le_spec]
      have hAllowedEq : (if integLeC bg.lever_integ_floor lvl = true then (ok true : Result Bool)
          else do
            let b1 ← bg.lever_integ_inspect_floor.le lvl
            if b1 = true then ok vouched else ok false)
          = ok (integLeC bg.lever_integ_floor lvl
              || (integLeC bg.lever_integ_inspect_floor lvl && vouched)) := by
        rw [integLevel_le_spec]
        cases integLeC bg.lever_integ_floor lvl <;>
          cases integLeC bg.lever_integ_inspect_floor lvl <;> cases vouched <;> simp
      simp only [bind_tc_ok, hAllowedEq]
      step*
      split <;>
        (step*
         simp only [li1_post]
         refine ⟨by omega, ?_⟩
         simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
           List.mem_append, List.mem_singleton, ← hlvl]
         grind)
    case isFalse h =>
      have heq' : i.val = child_integ.items.val.length := by scalar_tac
      simp only [spec_ok]
      simp only [heq', List.take_length] at hden
      simpa using hden
  · exact ⟨hi0, hdenied0⟩

/-- Conf-coverage loop (loop 1): sticky-denied fold over the child's taint set — denied iff some
    held level exceeds the declared `clvl`. -/
theorem returnEndorsedLoop1_spec
    (clvl : types.ConfLevel) (child_taint : collections.VecSet types.ConfLevel)
    (denied0 : Bool) (i0 : Usize)
    (hi0 : i0.val ≤ child_taint.items.val.length)
    (hdenied0 : denied0 = true ↔
      ∃ l ∈ child_taint.items.val.take i0.val, confLeC l clvl = false) :
    transitions.return_endorsed_loop1 clvl child_taint denied0 i0 ⦃ b =>
      (b = true ↔ ∃ l ∈ child_taint.items.val, confLeC l clvl = false) ⦄ := by
  unfold transitions.return_endorsed_loop1
  apply loop.spec_decr_nat
    (measure := fun p => child_taint.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ child_taint.items.val.length ∧
        (p.1 = true ↔ ∃ l ∈ child_taint.items.val.take p.2.val, confLeC l clvl = false))
  · rintro ⟨denied, i⟩ ⟨hile, hden⟩
    simp only [transitions.return_endorsed_loop1.body]
    have hi1 : collections.VecSet.len types.ConfLevel.Insts.CoreCloneClone
        types.ConfLevel.Insts.CoreCmpPartialEqConfLevel child_taint =
        .ok (alloc.vec.Vec.len child_taint.items) := rfl
    rw [hi1]; simp only [bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < child_taint.items.val.length := by scalar_tac
      simp only [collections.VecSet.at, bind_tc_ok]
      step as ⟨lvl, hlvl⟩
      rw [confLevel_le_spec]
      step*
      split <;>
        (step*
         simp only [ci1_post]
         refine ⟨by omega, ?_⟩
         simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
           List.mem_append, List.mem_singleton, ← hlvl]
         grind)
    case isFalse h =>
      have heq' : i.val = child_taint.items.val.length := by scalar_tac
      simp only [spec_ok]
      simp only [heq', List.take_length] at hden
      simpa using hden
  · exact ⟨hi0, hdenied0⟩

/-- Integ-coverage loop (loop 2): sticky-denied fold over the child's integ set — denied iff the
    declared `ilvl` fails to lower-bound some held level. -/
theorem returnEndorsedLoop2_spec
    (ilvl : types.IntegLevel) (child_integ : collections.VecSet types.IntegLevel)
    (denied0 : Bool) (i0 : Usize)
    (hi0 : i0.val ≤ child_integ.items.val.length)
    (hdenied0 : denied0 = true ↔
      ∃ l ∈ child_integ.items.val.take i0.val, integLeC ilvl l = false) :
    transitions.return_endorsed_loop2 ilvl child_integ denied0 i0 ⦃ b =>
      (b = true ↔ ∃ l ∈ child_integ.items.val, integLeC ilvl l = false) ⦄ := by
  unfold transitions.return_endorsed_loop2
  apply loop.spec_decr_nat
    (measure := fun p => child_integ.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ child_integ.items.val.length ∧
        (p.1 = true ↔ ∃ l ∈ child_integ.items.val.take p.2.val, integLeC ilvl l = false))
  · rintro ⟨denied, i⟩ ⟨hile, hden⟩
    simp only [transitions.return_endorsed_loop2.body]
    have hi1 : collections.VecSet.len types.IntegLevel.Insts.CoreCloneClone
        types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel child_integ =
        .ok (alloc.vec.Vec.len child_integ.items) := rfl
    rw [hi1]; simp only [bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i.val < child_integ.items.val.length := by scalar_tac
      simp only [collections.VecSet.at, bind_tc_ok]
      step as ⟨lvl, hlvl⟩
      rw [integLevel_le_spec]
      step*
      split <;>
        (step*
         simp only [ii1_post]
         refine ⟨by omega, ?_⟩
         simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
           List.mem_append, List.mem_singleton, ← hlvl]
         grind)
    case isFalse h =>
      have heq' : i.val = child_integ.items.val.length := by scalar_tac
      simp only [spec_ok]
      simp only [heq', List.take_length] at hden
      simpa using hden
  · exact ⟨hi0, hdenied0⟩

/-- Comprehensive inversion: the six gates, the lever verdict, the two coverage verdicts, the
    level-parameterized weight, its affordability on the PARENT, and the structural budget-debit
    frame + nodup post. -/
theorem return_endorsed_inv_full {F : Type} (cfInst : traits.ConformanceOracle F)
    (st : state.KernelState) (bg : background.BackgroundTheory) (conformance : F)
    (child parent : types.AgentId) (clvl : types.ConfLevel) (ilvl : types.IntegLevel)
    (rcOf : Bool)
    (hrc : ∀ s, cfInst.return_conforms conformance child parent s bg = .ok rcOf)
    (hcap : st.agent_budget.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.return_endorsed cfInst st bg conformance child parent clvl ilvl
      = .ok (.Ok (st', ev))) :
    ∃ vm, ∃ weight : Std.U8,
      vmLastEntry st.agent_parent.entries.val child = some (child, parent) ∧
      vsMem st.agent_active child ∧ vsMem st.agent_active parent ∧
      (∀ inv, ¬ vmsMemLast st.in_flight child inv) ∧
      vmsMemLast st.agent_cap child capability.CapKind.Declassify ∧
      rcOf = true ∧
      (∀ l, vmsMemLast st.integ_levels child l →
        integLeC bg.lever_integ_floor l = true
        ∨ integLeC bg.lever_integ_inspect_floor l = true) ∧
      (∀ l, vmsMemLast st.taint_levels child l → confLeC l clvl = true) ∧
      (∀ l, vmsMemLast st.integ_levels child l → integLeC ilvl l = true) ∧
      weight.val = Tzimtzum.declass_weight (confA clvl) + Tzimtzum.integ_weight (integA ilvl) ∧
      weight ≤ budgetReadC st.agent_budget parent ∧
      st' = { st with agent_budget := vm } ∧
      (∀ G, budgetReadC vm G =
        if G = parent then core.num.U8.saturating_sub (budgetReadC st.agent_budget parent) weight
        else budgetReadC st.agent_budget G) ∧
      (vmNodupKeys st.agent_budget → vmNodupKeys vm) := by
  simp only [transitions.return_endorsed] at hok
  -- Gate 1: parenthood.
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGet_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.AgentId.Insts.CoreCloneClone st.agent_parent child)
  rw [hoEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨b, hbEq, hbIff⟩ :
      ∃ bb, core.cmp.PartialEq.ne.trait_default (core.option.Option.Insts.CoreCmpPartialEqOption
        (core.cmp.PartialEqShared types.AgentId.Insts.CoreCmpPartialEqAgentId)) o (some parent) =
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
      rw [show x = child from hp1, hoP']
  -- Gates 2/3: both active.
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
  -- Gate 4: child has nothing in flight.
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
  -- Gate 5: `cap_declassify` on the child.
  obtain ⟨b4, hb4Eq, hb4Iff⟩ := spec_imp_exists
    (setContainsLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      capability.CapKind.Insts.CoreCloneClone capability.CapKind.Insts.CoreCmpPartialEqCapKind
      capKind_eq_spec capKind_clone_spec st.agent_cap child capability.CapKind.Declassify)
  rw [hb4Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb4 : b4 = true := by cases b4 with | true => rfl | false => simp at hok
  simp only [hb4, reduceIte] at hok
  -- Gate 6: `return_conforms` verdict.
  rw [hrc st] at hok
  simp only [bind_tc_ok] at hok
  have hrcTrue : rcOf = true := by cases rcOf with | true => rfl | false => simp at hok
  simp only [hrcTrue, reduceIte] at hok
  -- The child's integ set + the lever loop.
  obtain ⟨child_integ, hciEq, hciMem, _⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
      integLevel_clone_spec st.integ_levels child)
  rw [hciEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨lever_denied, hldEq, hldIff⟩ := spec_imp_exists
    (returnEndorsedLoop0_spec bg child_integ true false 0#usize (by simp) (by simp))
  rw [hldEq] at hok; simp only [bind_tc_ok] at hok
  have hld : lever_denied = false := by
    cases lever_denied with | false => rfl | true => simp at hok
  simp only [hld, reduceIte, Bool.false_eq_true] at hok
  have hLever : ∀ l, vmsMemLast st.integ_levels child l →
      integLeC bg.lever_integ_floor l = true
      ∨ integLeC bg.lever_integ_inspect_floor l = true := by
    intro l hl
    by_contra hc
    push_neg at hc
    obtain ⟨hc1, hc2⟩ := hc
    have : lever_denied = true := hldIff.mpr ⟨l, (hciMem l).mpr hl, by
      rw [Bool.eq_false_iff.mpr hc1, Bool.eq_false_iff.mpr hc2]; rfl⟩
    rw [hld] at this; simp at this
  -- The child's taint set + the two coverage loops.
  obtain ⟨child_taint, hctEq, hctMem, _⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_clone_spec st.taint_levels child)
  rw [hctEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨conf_denied, hcdEq, hcdIff⟩ := spec_imp_exists
    (returnEndorsedLoop1_spec clvl child_taint false 0#usize (by simp) (by simp))
  rw [hcdEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨integ_denied, hidEq, hidIff⟩ := spec_imp_exists
    (returnEndorsedLoop2_spec ilvl child_integ false 0#usize (by simp) (by simp))
  rw [hidEq] at hok; simp only [bind_tc_ok] at hok
  have hcd : conf_denied = false := by
    cases conf_denied with | false => rfl | true => simp at hok
  simp only [hcd, reduceIte, Bool.false_eq_true] at hok
  have hid : integ_denied = false := by
    cases integ_denied with | false => rfl | true => simp at hok
  simp only [hid, reduceIte, Bool.false_eq_true] at hok
  have hConfCov : ∀ l, vmsMemLast st.taint_levels child l → confLeC l clvl = true := by
    intro l hl
    by_contra hc
    have : conf_denied = true := hcdIff.mpr ⟨l, (hctMem l).mpr hl, Bool.eq_false_iff.mpr hc⟩
    rw [hcd] at this; simp at this
  have hIntegCov : ∀ l, vmsMemLast st.integ_levels child l → integLeC ilvl l = true := by
    intro l hl
    by_contra hc
    have : integ_denied = true := hidIff.mpr ⟨l, (hciMem l).mpr hl, Bool.eq_false_iff.mpr hc⟩
    rw [hid] at this; simp at this
  -- The level-parameterized weight.
  obtain ⟨wc, hwcEq, hwcVal⟩ := declassWeight_spec (confA clvl)
  rw [confC_confA] at hwcEq
  obtain ⟨wi, hwiEq, hwiVal⟩ := integWeight_spec (integA ilvl)
  rw [integC_integA] at hwiEq
  rw [hwcEq] at hok; simp only [bind_tc_ok] at hok
  rw [hwiEq] at hok; simp only [bind_tc_ok] at hok
  have hwcB : wc.val ≤ 4 := by rw [hwcVal]; exact declassWeight_le (confA clvl)
  have hwiB : wi.val ≤ 4 := by rw [hwiVal]; exact integWeight_le (integA ilvl)
  obtain ⟨weight, hwtEq, hwtVal⟩ := spec_imp_exists
    (U8.add_spec (x := wc) (y := wi) (by scalar_tac))
  rw [hwtEq] at hok; simp only [bind_tc_ok] at hok
  -- Affordability on the parent.
  obtain ⟨b6, hb6Eq, hb6Iff⟩ := spec_imp_exists (affordable_spec st parent weight)
  rw [hb6Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb6 : b6 = true := by cases b6 with | true => rfl | false => simp at hok
  simp only [hb6, reduceIte] at hok
  have hAfford : weight ≤ budgetReadC st.agent_budget parent := hb6Iff.mp hb6
  -- The parent debit.
  obtain ⟨st1, hst1Eq, vm, hStruct, hBud, hBudNd⟩ :=
    spec_imp_exists (debitBudget_full st parent weight hcap)
  rw [hst1Eq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _hEventEq⟩ := hok
  exact ⟨vm, weight, hlast, hb1Iff.mp hb1, hb2Iff.mp hb2, hNoFlight, hb4Iff.mp hb4, hrcTrue,
    hLever, hConfCov, hIntegCov, by rw [hwtVal, hwcVal, hwiVal], hAfford,
    hStateEq.symm.trans hStruct, hBud, hBudNd⟩

/-- `return_endorsed` preserves the unified `R`: the kernel transition at concrete `(clvl, ilvl)`
    refines the spec action at `(confA clvl, integA ilvl)`. -/
theorem return_endorsed_preservesR {F : Type} (cfInst : traits.ConformanceOracle F)
    (st : state.KernelState) (bg : background.BackgroundTheory) (conformance : F)
    (a : AbsState) (child parent : types.AgentId)
    (clvl : types.ConfLevel) (ilvl : types.IntegLevel)
    (rcOf : Bool)
    (hrc : ∀ s, cfInst.return_conforms conformance child parent s bg = .ok rcOf)
    (hrcA : rcOf = true ↔ a.return_conforms child parent)
    (hR : R st bg a)
    (hcap : st.agent_budget.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.return_endorsed cfInst st bg conformance child parent clvl ilvl
      = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.return_endorsed child parent (confA clvl) (integA ilvl)).guard a ∧
          (Tzimtzum.return_endorsed child parent (confA clvl) (integA ilvl)).next a a' ∧
          R st' bg a' := by
  obtain ⟨vm, weight, hParentEdge, hChildActive, hParentActive, hNoFlight, hChildCap, hRcTrue,
      hLever, hConfCov, hIntegCov, hwVal, hAfford, rfl, hBud, hBudNd⟩ :=
    return_endorsed_inv_full cfInst st bg conformance child parent clvl ilvl rcOf hrc hcap
      st' ev hok
  refine ⟨{ a with agent_budget := fun A =>
      if A = parent then
        a.agent_budget parent
          - (Tzimtzum.declass_weight (confA clvl) + Tzimtzum.integ_weight (integA ilvl))
      else a.agent_budget A }, ?_, ?_, ?_⟩
  · -- guard
    refine ⟨(hR.parent child parent).mpr hParentEdge, (hR.active child).mpr hChildActive,
      (hR.active parent).mpr hParentActive, ?_, ?_, hrcA.mp hRcTrue, ?_, ?_, ?_, ?_⟩
    · intro I hc; exact hNoFlight I ((hR.inflight child I).mp hc)
    · rw [hR.cap_declass]
      exact (hR.cap child capability.CapKind.Declassify).mpr hChildCap
    · -- lever floor (graduated, vouched by return_conforms)
      intro L hL
      have hlast : vmsMemLast st.integ_levels child (integC L) := (hR.integ child L).mp hL
      rcases hLever (integC L) hlast with hA | hI
      · left
        show Tzimtzum.le_integ a.lever_integ_floor L
        rw [hR.leverFloor, le_integ_integLeC']
        exact hA
      · right
        refine ⟨?_, hrcA.mp hRcTrue⟩
        show Tzimtzum.le_integ a.lever_integ_inspect_floor L
        rw [hR.leverInspectFloor, le_integ_integLeC']
        exact hI
    · -- conf coverage: the declared clvl bounds the child's taint set
      intro L hL
      have hlast : vmsMemLast st.taint_levels child (confC L) := (hR.taint child L).mp hL
      rw [le_conf_confLeC]
      exact hConfCov (confC L) hlast
    · -- integ coverage: the declared ilvl lower-bounds the child's integ set
      intro L hL
      have hlast : vmsMemLast st.integ_levels child (integC L) := (hR.integ child L).mp hL
      rw [le_integ_integLeC']
      exact hIntegCov (integC L) hlast
    · -- affordable parent (declass_weight clvl + integ_weight ilvl)
      show Tzimtzum.declass_weight (confA clvl) + Tzimtzum.integ_weight (integA ilvl)
        ≤ a.agent_budget parent
      rw [hR.budget parent, ← hwVal]
      exact_mod_cast hAfford
  · -- next
    simp [Tzimtzum.return_endorsed]
    funext G
    by_cases hG : G = parent <;> simp [hG]
  · -- R st' bg a'
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov, hR.active, hR.tool_reg,
      hR.parent, hR.cap, hR.instr, hR.taint, hR.integ, hR.inflight, hR.override, ?_,
      hR.invUsed, hR.invEgress, hR.toolCap, hR.toolEgress, hR.toolFloor, hR.toolIntegFloor,
      hR.toolIntegInspectFloor, hR.toolOutputInteg, hR.toolBounded, hR.toolIssuer, hR.trustedIss,
      hR.instrIssuer, hR.flowAllows, hR.flowInspects, hR.leverFloor, hR.leverInspectFloor,
      hR.flowOverride, hR.invTool, hR.ndParent, hR.ndCap, hR.ndInstr, hR.ndTaint, hR.ndInteg,
      hR.ndInflight, hR.ndOverride, hR.ndFlowOverride, hBudNd hR.ndBudget, hR.wfInflight⟩
    -- budget (parent debit by the level-parameterized weight)
    intro G
    show (if G = parent then
        a.agent_budget parent
          - (Tzimtzum.declass_weight (confA clvl) + Tzimtzum.integ_weight (integA ilvl))
      else a.agent_budget G) = (budgetReadC vm G).val
    rw [hBud G]
    by_cases hG : G = parent
    · rw [if_pos hG, if_pos hG, saturatingSub_val, hR.budget parent, hwVal]
    · rw [if_neg hG, if_neg hG, hR.budget G]

end ArgusLean.Refinement
