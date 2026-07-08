import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `invoke_start` preserves the unified `R`

Clean rewrite for V3 (design §5.3, task 9): freshness (`invocation_used`), narrowing/coverage
attestation guards over `invocation_egress`, CHECK 2 a/b/c (the confidentiality flow gate over the
new invocation's *attested* egress, folded per speculative-taint level / per in-flight invocation /
at the tool's own floor), CHECK 3 (`invocation_authorized`), CHECK 4 a/b/c (the dual integrity gate,
no override arm — endorsement is the only way up), and eager override consumption (three short
clauses, no egress conjunct — the V2 `GateAccum`/`to_consume` accumulator and the "sole
justification" consumption machinery are gone from both kernel and spec).

The kernel's `if !tool_meta.egress.is_empty() && attested_egress.is_empty() { deny }` coverage check
compiles (Charon/Aeneas) into two structurally-duplicated continuations — `invoke_start_loop1..7`
(tool has no declared egress, coverage vacuous) and `invoke_start_loop8..14` (tool has declared
egress, attested set already checked non-empty) — that are byte-for-byte the same computation. Each
pair is literally `rfl`-equal (`invoke_start_loop8 = invoke_start_loop1`, ..., `invoke_start_loop14 =
invoke_start_loop7`), so every loop below is proved once and reused for both continuations via that
equality instead of being proved twice.

Two bridging facts this file needs that are not (and should not be) part of the shared `Bridging`/
`Relation` infrastructure, because they are specific to the one action that mints a fresh invocation
id:

* `hEgAgree` — the classifier's attested set for the FRESH `inv` literally is `inv`'s abstract
  `invocation_egress` relation. `R`'s `RinvocationEgress` is deliberately restricted to *used*
  invocations (Task 6: the concrete `KernelState.invocation_egress` carries no entry for `inv` until
  this very transition writes one), so it cannot supply this fact; it is exactly the missing half of
  the seam Task 6/7's notes flagged for this action. Threaded in as an explicit hypothesis (the
  per-invocation companion to `CgAgree`/`AuAgree`), to be supplied by the oracle adapter alongside
  them when Task 14 assembles `OracleFidelity`.
* `hFlightUsed` — every in-flight invocation is abstractly used (`in_flight_implies_used`, design
  §5.7's new strengthening invariant, freshness-inductive at the spec level). Needed to route CHECK
  2b/4b's in-flight egress/gate reads through `R`'s used-only `RinvocationEgress`. Carried as a
  hypothesis rather than derived here (it is a property of *reachable* abstract states, not of `R`
  itself); Task 14's bundle discharges it once the invariant is established. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option Aeneas.Deprecated.progressWarning false
set_option maxHeartbeats 4000000

/-! ## Loop-pair reuse: the coverage-branch duplicate loops are `rfl`-equal to loops 1-7 -/

theorem invokeStartLoop8_eq : @transitions.invoke_start_loop8 = @transitions.invoke_start_loop1 := rfl
theorem invokeStartLoop9_eq {C : Type} (cgInst : traits.ContentGateOracle C) :
    @transitions.invoke_start_loop9 C cgInst = @transitions.invoke_start_loop2 C cgInst := rfl
theorem invokeStartLoop10_eq {C : Type} (cgInst : traits.ContentGateOracle C) :
    @transitions.invoke_start_loop10 C cgInst = @transitions.invoke_start_loop3 C cgInst := rfl
theorem invokeStartLoop11_eq {C : Type} (cgInst : traits.ContentGateOracle C) :
    @transitions.invoke_start_loop11 C cgInst = @transitions.invoke_start_loop4 C cgInst := rfl
theorem invokeStartLoop12_eq {C : Type} (cgInst : traits.ContentGateOracle C) :
    @transitions.invoke_start_loop12 C cgInst = @transitions.invoke_start_loop5 C cgInst := rfl
theorem invokeStartLoop13_eq : @transitions.invoke_start_loop13 = @transitions.invoke_start_loop6 := rfl
theorem invokeStartLoop14_eq : @transitions.invoke_start_loop14 = @transitions.invoke_start_loop7 := rfl

/-! ## `speculative_taint` bridging (conf side, unchanged shape from V2) -/

/-- The conf-floor contribution of in-flight invocation `inv`: its bound tool's metadata floor
    (empty when unbound or no metadata). -/
def flightFloor (vm : collections.VecMap types.InvocationId types.ToolId)
    (bg : background.BackgroundTheory) (inv : types.InvocationId) (L : types.ConfLevel) : Prop :=
  ∃ tool tmeta, (vmLastEntry vm.entries.val inv).map Prod.snd = some tool ∧
    toolMetaC bg tool = some tmeta ∧ tmeta.conf_floor = L

/-- `speculative_taint_loop` accumulates the conf-floor of every in-flight tool into `taint`. -/
theorem specTaintLoop_spec (vm : collections.VecMap types.InvocationId types.ToolId)
    (bg : background.BackgroundTheory) (flights : collections.VecSet types.InvocationId)
    (taint0 : collections.VecSet types.ConfLevel)
    (hcapS : taint0.items.val.length + flights.items.val.length ≤ Usize.max)
    (taint : collections.VecSet types.ConfLevel) (j : Usize)
    (hj : j.val ≤ flights.items.val.length)
    (hlen : taint.items.val.length ≤ taint0.items.val.length + j.val)
    (hmem : ∀ L, vsMem taint L ↔ vsMem taint0 L ∨
      ∃ inv ∈ flights.items.val.take j.val, flightFloor vm bg inv L) :
    state.KernelState.speculative_taint_loop vm bg taint flights j ⦃ res =>
      (∀ L, vsMem res L ↔ vsMem taint0 L ∨ ∃ inv ∈ flights.items.val, flightFloor vm bg inv L) ∧
      res.items.val.length ≤ taint0.items.val.length + flights.items.val.length ⦄ := by
  unfold state.KernelState.speculative_taint_loop
  apply loop.spec_decr_nat
    (measure := fun p => flights.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ flights.items.val.length ∧
      p.1.items.val.length ≤ taint0.items.val.length + p.2.val ∧
      (∀ L, vsMem p.1 L ↔ vsMem taint0 L ∨
        ∃ inv ∈ flights.items.val.take p.2.val, flightFloor vm bg inv L))
  · rintro ⟨tnt, jL⟩ ⟨hile, hlenL, hmemL⟩
    dsimp only at hile hlenL hmemL ⊢
    simp only [state.KernelState.speculative_taint_loop.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : jL.val < flights.items.val.length := by scalar_tac
      step as ⟨inv, hinv⟩
      have hext : ∀ (P : types.InvocationId → Prop),
          (∃ x ∈ flights.items.val.take (jL.val + 1), P x) ↔
          (∃ x ∈ flights.items.val.take jL.val, P x) ∨ P inv := by
        intro P
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨x, hx | hx, hPx⟩
          · exact Or.inl ⟨x, hx, hPx⟩
          · subst hx; rw [hinv]; exact Or.inr hPx
        · rintro (⟨x, hx, hPx⟩ | hPi)
          · exact ⟨x, Or.inl hx, hPx⟩
          · exact ⟨inv, Or.inr hinv, hPi⟩
      have hi2 : ∀ (i2 : Usize), i2.val = jL.val + 1 →
          flights.items.val.take i2.val = flights.items.val.take (jL.val + 1) := fun i2 h2 => by rw [h2]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.ToolId.Insts.CoreCloneClone toolId_clone_spec vm inv)
      rw [hoEq]; simp only [bind_tc_ok]
      have hcapTnt : tnt.items.val.length < Usize.max := by
        have := hlenL; have := hlt; have := hcapS; omega
      cases hocase : o with
      | none =>
        have hnone : (vmLastEntry vm.entries.val inv).map Prod.snd = none := by rw [← ho]; exact hocase
        have hnf : ∀ L, ¬ flightFloor vm bg inv L := by
          intro L; rintro ⟨tool, tmeta, ht, _, _⟩; rw [hnone] at ht; simp at ht
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, by omega, fun L => ?_, by scalar_tac⟩
        rw [hi2 _ j1_post, hext (flightFloor vm bg · L), hmemL L]
        constructor
        · intro h; exact h.imp_right Or.inl
        · rintro (hA | hB | hC)
          · exact Or.inl hA
          · exact Or.inr hB
          · exact absurd hC (hnf L)
      | some tool =>
        have hsome : (vmLastEntry vm.entries.val inv).map Prod.snd = some tool := by
          rw [← ho]; exact hocase
        simp only []
        obtain ⟨o1, ho1Eq, ho1⟩ := spec_imp_exists (toolMetadata_spec bg tool)
        rw [ho1Eq]; simp only [bind_tc_ok]
        cases hmcase : o1 with
        | none =>
          have hnm : toolMetaC bg tool = none := by rw [← ho1]; exact hmcase
          have hnf : ∀ L, ¬ flightFloor vm bg inv L := by
            intro L; rintro ⟨tool', tmeta, ht, hm, _⟩
            rw [hsome, Option.some_inj] at ht; subst ht; rw [hnm] at hm; simp at hm
          simp only [bind_tc_ok]
          step*
          refine ⟨by scalar_tac, by omega, fun L => ?_, by scalar_tac⟩
          rw [hi2 _ j1_post, hext (flightFloor vm bg · L), hmemL L]
          constructor
          · intro h; exact h.imp_right Or.inl
          · rintro (hA | hB | hC)
            · exact Or.inl hA
            · exact Or.inr hB
            · exact absurd hC (hnf L)
        | some tmeta =>
          have hm : toolMetaC bg tool = some tmeta := by rw [← ho1]; exact hmcase
          obtain ⟨tnt', htnt'Eq, htnt'Mem, htnt'Len⟩ := spec_imp_exists
            (vecSetInsertLen_spec types.ConfLevel.Insts.CoreCloneClone
              types.ConfLevel.Insts.CoreCmpPartialEqConfLevel confLevel_eq_spec tnt tmeta.conf_floor
              hcapTnt)
          dsimp only
          rw [htnt'Eq]; simp only [bind_tc_ok]
          have hmem' : ∀ L, vsMem tnt' L ↔ vsMem tnt L ∨ flightFloor vm bg inv L := by
            intro L; rw [htnt'Mem L]
            apply or_congr_right
            constructor
            · intro hL; exact ⟨tool, tmeta, hsome, hm, hL.symm⟩
            · rintro ⟨tool', tmeta', ht, hm', hfl⟩
              rw [hsome, Option.some_inj] at ht; subst ht
              rw [hm, Option.some_inj] at hm'; subst hm'; exact hfl.symm
          step*
          refine ⟨by scalar_tac, by omega, fun L => ?_, by scalar_tac⟩
          rw [hmem' L, hmemL L, hi2 _ j1_post, hext (flightFloor vm bg · L), or_assoc]
    case isFalse h =>
      have heq' : jL.val = flights.items.val.length := by scalar_tac
      rw [heq'] at hlenL
      simp only [spec_ok, heq', List.take_length] at hmemL ⊢
      exact ⟨hmemL, hlenL⟩
  · exact ⟨hj, hlen, hmem⟩

/-- `speculative_taint st agent bg`: `agent`'s held taint plus the conf-floor of every in-flight tool. -/
theorem specTaint_spec (st : state.KernelState) (agent : types.AgentId)
    (bg : background.BackgroundTheory)
    (hcap : vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent ≤ Usize.max) :
    state.KernelState.speculative_taint st agent bg ⦃ res =>
      (∀ L, vsMem res L ↔ vmsMemLast st.taint_levels agent L ∨
        ∃ inv, vmsMemLast st.in_flight agent inv ∧ flightFloor st.invocation_tool bg inv L) ∧
      res.items.val.length ≤ vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent ⦄ := by
  unfold state.KernelState.speculative_taint
  obtain ⟨taint0, ht0Eq, ht0Mem, ht0Len⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_clone_spec st.taint_levels agent)
  rw [ht0Eq]; simp only [bind_tc_ok]
  obtain ⟨flights, hflEq, hflMem, hflLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight agent)
  rw [hflEq]; simp only [bind_tc_ok]
  obtain ⟨res, hresEq, hresMem, hresLen⟩ := spec_imp_exists
    (specTaintLoop_spec st.invocation_tool bg flights taint0
      (by rw [ht0Len, hflLen]; exact hcap) taint0 0#usize (by simp) (by simp) (by simp))
  rw [hresEq]; simp only [spec_ok]
  refine ⟨fun L => ?_, ?_⟩
  · rw [hresMem L, ht0Mem L]
    apply or_congr_right
    constructor
    · rintro ⟨inv, hinv, hfl⟩; exact ⟨inv, (hflMem inv).mp hinv, hfl⟩
    · rintro ⟨inv, hinv, hfl⟩; exact ⟨inv, (hflMem inv).mpr hinv, hfl⟩
  · rw [ht0Len, hflLen] at hresLen; exact hresLen

/-! ## `speculative_integ` bridging (dual of `speculative_taint`/`specTaintLoop_spec`) -/

/-- The integrity-emission contribution of in-flight invocation `inv`: its bound tool's metadata
    emission (empty when unbound or no metadata). Dual of `flightFloor`. -/
def flightIntegFloor (vm : collections.VecMap types.InvocationId types.ToolId)
    (bg : background.BackgroundTheory) (inv : types.InvocationId) (L : types.IntegLevel) : Prop :=
  ∃ tool tmeta, (vmLastEntry vm.entries.val inv).map Prod.snd = some tool ∧
    toolMetaC bg tool = some tmeta ∧ tmeta.output_integ = L

/-- `speculative_integ_loop` accumulates the emission of every in-flight tool into `integ`. Dual of
    `specTaintLoop_spec`. -/
theorem specIntegLoop_spec (vm : collections.VecMap types.InvocationId types.ToolId)
    (bg : background.BackgroundTheory) (flights : collections.VecSet types.InvocationId)
    (integ0 : collections.VecSet types.IntegLevel)
    (hcapS : integ0.items.val.length + flights.items.val.length ≤ Usize.max)
    (integ : collections.VecSet types.IntegLevel) (j : Usize)
    (hj : j.val ≤ flights.items.val.length)
    (hlen : integ.items.val.length ≤ integ0.items.val.length + j.val)
    (hmem : ∀ L, vsMem integ L ↔ vsMem integ0 L ∨
      ∃ inv ∈ flights.items.val.take j.val, flightIntegFloor vm bg inv L) :
    state.KernelState.speculative_integ_loop vm bg integ flights j ⦃ res =>
      (∀ L, vsMem res L ↔ vsMem integ0 L ∨ ∃ inv ∈ flights.items.val, flightIntegFloor vm bg inv L) ∧
      res.items.val.length ≤ integ0.items.val.length + flights.items.val.length ⦄ := by
  unfold state.KernelState.speculative_integ_loop
  apply loop.spec_decr_nat
    (measure := fun p => flights.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ flights.items.val.length ∧
      p.1.items.val.length ≤ integ0.items.val.length + p.2.val ∧
      (∀ L, vsMem p.1 L ↔ vsMem integ0 L ∨
        ∃ inv ∈ flights.items.val.take p.2.val, flightIntegFloor vm bg inv L))
  · rintro ⟨itg, jL⟩ ⟨hile, hlenL, hmemL⟩
    dsimp only at hile hlenL hmemL ⊢
    simp only [state.KernelState.speculative_integ_loop.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : jL.val < flights.items.val.length := by scalar_tac
      step as ⟨inv, hinv⟩
      have hext : ∀ (P : types.InvocationId → Prop),
          (∃ x ∈ flights.items.val.take (jL.val + 1), P x) ↔
          (∃ x ∈ flights.items.val.take jL.val, P x) ∨ P inv := by
        intro P
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨x, hx | hx, hPx⟩
          · exact Or.inl ⟨x, hx, hPx⟩
          · subst hx; rw [hinv]; exact Or.inr hPx
        · rintro (⟨x, hx, hPx⟩ | hPi)
          · exact ⟨x, Or.inl hx, hPx⟩
          · exact ⟨inv, Or.inr hinv, hPi⟩
      have hi2 : ∀ (i2 : Usize), i2.val = jL.val + 1 →
          flights.items.val.take i2.val = flights.items.val.take (jL.val + 1) := fun i2 h2 => by rw [h2]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.ToolId.Insts.CoreCloneClone toolId_clone_spec vm inv)
      rw [hoEq]; simp only [bind_tc_ok]
      have hcapItg : itg.items.val.length < Usize.max := by
        have := hlenL; have := hlt; have := hcapS; omega
      cases hocase : o with
      | none =>
        have hnone : (vmLastEntry vm.entries.val inv).map Prod.snd = none := by rw [← ho]; exact hocase
        have hnf : ∀ L, ¬ flightIntegFloor vm bg inv L := by
          intro L; rintro ⟨tool, tmeta, ht, _, _⟩; rw [hnone] at ht; simp at ht
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, by omega, fun L => ?_, by scalar_tac⟩
        rw [hi2 _ j1_post, hext (flightIntegFloor vm bg · L), hmemL L]
        constructor
        · intro h; exact h.imp_right Or.inl
        · rintro (hA | hB | hC)
          · exact Or.inl hA
          · exact Or.inr hB
          · exact absurd hC (hnf L)
      | some tool =>
        have hsome : (vmLastEntry vm.entries.val inv).map Prod.snd = some tool := by
          rw [← ho]; exact hocase
        simp only []
        obtain ⟨o1, ho1Eq, ho1⟩ := spec_imp_exists (toolMetadata_spec bg tool)
        rw [ho1Eq]; simp only [bind_tc_ok]
        cases hmcase : o1 with
        | none =>
          have hnm : toolMetaC bg tool = none := by rw [← ho1]; exact hmcase
          have hnf : ∀ L, ¬ flightIntegFloor vm bg inv L := by
            intro L; rintro ⟨tool', tmeta, ht, hm, _⟩
            rw [hsome, Option.some_inj] at ht; subst ht; rw [hnm] at hm; simp at hm
          simp only [bind_tc_ok]
          step*
          refine ⟨by scalar_tac, by omega, fun L => ?_, by scalar_tac⟩
          rw [hi2 _ j1_post, hext (flightIntegFloor vm bg · L), hmemL L]
          constructor
          · intro h; exact h.imp_right Or.inl
          · rintro (hA | hB | hC)
            · exact Or.inl hA
            · exact Or.inr hB
            · exact absurd hC (hnf L)
        | some tmeta =>
          have hm : toolMetaC bg tool = some tmeta := by rw [← ho1]; exact hmcase
          obtain ⟨itg', hitg'Eq, hitg'Mem, hitg'Len⟩ := spec_imp_exists
            (vecSetInsertLen_spec types.IntegLevel.Insts.CoreCloneClone
              types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel integLevel_eq_spec itg
              tmeta.output_integ hcapItg)
          dsimp only
          rw [hitg'Eq]; simp only [bind_tc_ok]
          have hmem' : ∀ L, vsMem itg' L ↔ vsMem itg L ∨ flightIntegFloor vm bg inv L := by
            intro L; rw [hitg'Mem L]
            apply or_congr_right
            constructor
            · intro hL; exact ⟨tool, tmeta, hsome, hm, hL.symm⟩
            · rintro ⟨tool', tmeta', ht, hm', hfl⟩
              rw [hsome, Option.some_inj] at ht; subst ht
              rw [hm, Option.some_inj] at hm'; subst hm'; exact hfl.symm
          step*
          refine ⟨by scalar_tac, by omega, fun L => ?_, by scalar_tac⟩
          rw [hmem' L, hmemL L, hi2 _ j1_post, hext (flightIntegFloor vm bg · L), or_assoc]
    case isFalse h =>
      have heq' : jL.val = flights.items.val.length := by scalar_tac
      rw [heq'] at hlenL
      simp only [spec_ok, heq', List.take_length] at hmemL ⊢
      exact ⟨hmemL, hlenL⟩
  · exact ⟨hj, hlen, hmem⟩

/-- `speculative_integ st agent bg`: `agent`'s held integrity levels plus the emission of every
    in-flight tool. Dual of `specTaint_spec`. -/
theorem specInteg_spec (st : state.KernelState) (agent : types.AgentId)
    (bg : background.BackgroundTheory)
    (hcap : vmSetLen st.integ_levels agent + vmSetLen st.in_flight agent ≤ Usize.max) :
    state.KernelState.speculative_integ st agent bg ⦃ res =>
      (∀ L, vsMem res L ↔ vmsMemLast st.integ_levels agent L ∨
        ∃ inv, vmsMemLast st.in_flight agent inv ∧ flightIntegFloor st.invocation_tool bg inv L) ∧
      res.items.val.length ≤ vmSetLen st.integ_levels agent + vmSetLen st.in_flight agent ⦄ := by
  unfold state.KernelState.speculative_integ
  obtain ⟨integ0, hi0Eq, hi0Mem, hi0Len⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.IntegLevel.Insts.CoreCloneClone types.IntegLevel.Insts.CoreCmpPartialEqIntegLevel
      integLevel_clone_spec st.integ_levels agent)
  rw [hi0Eq]; simp only [bind_tc_ok]
  obtain ⟨flights, hflEq, hflMem, hflLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight agent)
  rw [hflEq]; simp only [bind_tc_ok]
  obtain ⟨res, hresEq, hresMem, hresLen⟩ := spec_imp_exists
    (specIntegLoop_spec st.invocation_tool bg flights integ0
      (by rw [hi0Len, hflLen]; exact hcap) integ0 0#usize (by simp) (by simp) (by simp))
  rw [hresEq]; simp only [spec_ok]
  refine ⟨fun L => ?_, ?_⟩
  · rw [hresMem L, hi0Mem L]
    apply or_congr_right
    constructor
    · rintro ⟨inv, hinv, hfl⟩; exact ⟨inv, (hflMem inv).mp hinv, hfl⟩
    · rintro ⟨inv, hinv, hfl⟩; exact ⟨inv, (hflMem inv).mpr hinv, hfl⟩
  · rw [hi0Len, hflLen] at hresLen; exact hresLen

/-! ## Loop 0 — narrowing (`attested_egress ⊆ tool's declared egress`) -/

/-- `invoke_start_loop0` ORs `narrowing_violated` with "`e ∉ declared`" over the prefix of the
    attested set; the result is `true` iff some attested kind is not in the tool's declared set. -/
theorem invokeStartLoop0_spec
    (attested_egress declared : collections.VecSet types.EgressKind)
    (nv0 : Bool) (nai : Usize)
    (hnai : nai.val ≤ attested_egress.items.val.length)
    (hnv : nv0 = true ↔ ∃ e ∈ attested_egress.items.val.take nai.val, ¬ vsMem declared e) :
    transitions.invoke_start_loop0 attested_egress declared nv0 nai ⦃ res =>
      res = true ↔ ∃ e ∈ attested_egress.items.val, ¬ vsMem declared e ⦄ := by
  unfold transitions.invoke_start_loop0
  apply loop.spec_decr_nat
    (measure := fun p => attested_egress.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ attested_egress.items.val.length ∧
      (p.1 = true ↔ ∃ e ∈ attested_egress.items.val.take p.2.val, ¬ vsMem declared e))
  · rintro ⟨nv, nai'⟩ ⟨hile, hnvL⟩
    dsimp only at hile hnvL ⊢
    simp only [transitions.invoke_start_loop0.body, collections.VecSet.len, collections.VecSet.at,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : nai'.val < attested_egress.items.val.length := by scalar_tac
      step as ⟨e, he⟩
      obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists
        (vecSetContains_spec types.EgressKind.Insts.CoreCloneClone
          types.EgressKind.Insts.CoreCmpPartialEqEgressKind egressKind_eq_spec declared e)
      rw [hbEq]; simp only [bind_tc_ok]
      have hext : (∃ x ∈ attested_egress.items.val.take (nai'.val + 1), ¬ vsMem declared x) ↔
          (∃ x ∈ attested_egress.items.val.take nai'.val, ¬ vsMem declared x) ∨ ¬ vsMem declared e := by
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨x, hx | hx, hPx⟩
          · exact Or.inl ⟨x, hx, hPx⟩
          · subst hx; rw [he]; exact Or.inr hPx
        · rintro (⟨x, hx, hPx⟩ | hPi)
          · exact ⟨x, Or.inl hx, hPx⟩
          · exact ⟨e, Or.inr he, hPi⟩
      have hi2 : ∀ (i2 : Usize), i2.val = nai'.val + 1 →
          attested_egress.items.val.take i2.val = attested_egress.items.val.take (nai'.val + 1) :=
        fun i2 h2 => by rw [h2]
      have hval : (if b then (Result.ok nv : Result Bool) else Result.ok true) =
          Result.ok (nv || !b) := by cases b <;> simp
      rw [hval]; simp only [bind_tc_ok]
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hi2 _ nai1_post, hext, Bool.or_eq_true, Bool.not_eq_true', hnvL]
      apply or_congr_right
      rw [← hbIff]; cases b <;> simp
    case isFalse h =>
      have heq' : nai'.val = attested_egress.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hnvL ⊢
      exact hnvL
  · exact ⟨hnai, hnv⟩

/-! ## Loop 1 (= Loop 8) — CHECK 1 capability gate -/

/-- `invoke_start_loop1` ORs `missing_cap` with "`agent` lacks `c`" over the prefix of the tool's
    required caps; the result is `true` iff some required cap is missing (last-match `set_contains`). -/
theorem invokeStartLoop1_spec
    (vm : collections.VecMap types.AgentId (collections.VecSet capability.CapKind))
    (agent : types.AgentId) (caps : collections.VecSet capability.CapKind)
    (mc0 : Bool) (ci : Usize)
    (hci : ci.val ≤ caps.items.val.length)
    (hmc : mc0 = true ↔ ∃ c ∈ caps.items.val.take ci.val, ¬ vmsMemLast vm agent c) :
    transitions.invoke_start_loop1 vm agent caps mc0 ci ⦃ res =>
      res = true ↔ ∃ c ∈ caps.items.val, ¬ vmsMemLast vm agent c ⦄ := by
  unfold transitions.invoke_start_loop1
  apply loop.spec_decr_nat
    (measure := fun p => caps.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ caps.items.val.length ∧
      (p.1 = true ↔ ∃ c ∈ caps.items.val.take p.2.val, ¬ vmsMemLast vm agent c))
  · rintro ⟨mc, ci'⟩ ⟨hile, hmcL⟩
    dsimp only at hile hmcL ⊢
    simp only [transitions.invoke_start_loop1.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : ci'.val < caps.items.val.length := by scalar_tac
      step as ⟨cap, hcap⟩
      obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists
        (setContainsLast_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          capability.CapKind.Insts.CoreCloneClone capability.CapKind.Insts.CoreCmpPartialEqCapKind
          capKind_eq_spec capKind_clone_spec vm agent cap)
      rw [hbEq]; simp only [bind_tc_ok]
      have hext : (∃ c ∈ caps.items.val.take (ci'.val + 1), ¬ vmsMemLast vm agent c) ↔
          (∃ c ∈ caps.items.val.take ci'.val, ¬ vmsMemLast vm agent c) ∨ ¬ vmsMemLast vm agent cap := by
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨c, hc | hc, hPc⟩
          · exact Or.inl ⟨c, hc, hPc⟩
          · subst hc; rw [hcap]; exact Or.inr hPc
        · rintro (⟨c, hc, hPc⟩ | hPi)
          · exact ⟨c, Or.inl hc, hPc⟩
          · exact ⟨cap, Or.inr hcap, hPi⟩
      have hi2 : ∀ (i2 : Usize), i2.val = ci'.val + 1 →
          caps.items.val.take i2.val = caps.items.val.take (ci'.val + 1) := fun i2 h2 => by rw [h2]
      have hval : (if b then (Result.ok mc : Result Bool) else Result.ok true) =
          Result.ok (mc || !b) := by cases b <;> simp
      rw [hval]; simp only [bind_tc_ok]
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hi2 _ ci1_post, hext, Bool.or_eq_true, Bool.not_eq_true', hmcL]
      apply or_congr_right
      rw [← hbIff]; cases b <;> simp
    case isFalse h =>
      have heq' : ci'.val = caps.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hmcL ⊢
      exact hmcL
  · exact ⟨hci, hmc⟩

/-! ## Loop 2 (= Loop 9) — CHECK 2a: fold `gate_egress` over `spec_taint` at the fixed new tool -/

/-- `invoke_start_loop2` folds `gate_egress` at the fixed new `(tool, inv)`/attested set over each
    speculative-taint level: monotonically `denied`, no accumulator. -/
theorem invokeStartLoop2_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (agent : types.AgentId) (tool : types.ToolId) (inv : types.InvocationId)
    (attested_egress : collections.VecSet types.EgressKind)
    (cgVal : Bool) (hcg : cgInst.passes content_gate agent tool inv st bg = .ok cgVal)
    (ovOf ocOf : types.ConfLevel → Bool)
    (hov : ∀ L, state.KernelState.has_flow_override st agent tool L = .ok (ovOf L))
    (hoc : ∀ L, state.KernelState.override_consumed st agent tool L = .ok (ocOf L))
    (spec_taint : collections.VecSet types.ConfLevel) (denied0 denied : Bool) (li : Usize)
    (hli : li.val ≤ spec_taint.items.val.length)
    (hden : denied = true ↔ denied0 = true ∨
      ∃ level ∈ spec_taint.items.val.take li.val, ∃ E ∈ attested_egress.items.val,
        egressDenied (flowModeC bg level E) cgVal (ovOf level) (ocOf level)) :
    transitions.invoke_start_loop2 cgInst st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.integ_levels st.in_flight st.invocation_tool st.invocation_used
      st.invocation_egress st.tool_registered st.agent_instruction st.override_used
      st.flow_override st.agent_budget bg content_gate agent tool inv attested_egress denied
      spec_taint li ⦃ res =>
      res = true ↔ denied0 = true ∨
        ∃ level ∈ spec_taint.items.val, ∃ E ∈ attested_egress.items.val,
          egressDenied (flowModeC bg level E) cgVal (ovOf level) (ocOf level) ⦄ := by
  unfold transitions.invoke_start_loop2
  have hst : ((⟨st.agent_active, st.agent_parent, st.agent_cap, st.taint_levels, st.integ_levels,
      st.in_flight, st.invocation_tool, st.invocation_used, st.invocation_egress,
      st.tool_registered, st.agent_instruction, st.override_used, st.flow_override,
      st.agent_budget⟩ : state.KernelState)) = st := by cases st; rfl
  apply loop.spec_decr_nat
    (measure := fun p => spec_taint.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ spec_taint.items.val.length ∧
      (p.1 = true ↔ denied0 = true ∨
        ∃ level ∈ spec_taint.items.val.take p.2.val, ∃ E ∈ attested_egress.items.val,
          egressDenied (flowModeC bg level E) cgVal (ovOf level) (ocOf level)))
  · rintro ⟨deniedL, iL⟩ ⟨hile, hdenL⟩
    dsimp only at hile hdenL ⊢
    simp only [transitions.invoke_start_loop2.body, collections.VecSet.len, collections.VecSet.at,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : iL.val < spec_taint.items.val.length := by scalar_tac
      step as ⟨level, hlevel⟩
      rw [hst]
      obtain ⟨d2, hd2Eq, hd2Iff⟩ := spec_imp_exists
        (gateEgress_spec cgInst bg content_gate agent tool inv st level attested_egress
          cgVal (ovOf level) (ocOf level) hcg (hov level) (hoc level)
          (flowModeC bg level) (flowMode_eq bg level) deniedL)
      rw [hd2Eq]; simp only [bind_tc_ok]
      have hext : (∃ lev ∈ spec_taint.items.val.take (iL.val + 1), ∃ E ∈ attested_egress.items.val,
          egressDenied (flowModeC bg lev E) cgVal (ovOf lev) (ocOf lev)) ↔
          (∃ lev ∈ spec_taint.items.val.take iL.val, ∃ E ∈ attested_egress.items.val,
            egressDenied (flowModeC bg lev E) cgVal (ovOf lev) (ocOf lev))
          ∨ (∃ E ∈ attested_egress.items.val,
              egressDenied (flowModeC bg level E) cgVal (ovOf level) (ocOf level)) := by
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨lev, hlev | hlev, hPlev⟩
          · exact Or.inl ⟨lev, hlev, hPlev⟩
          · subst hlev; rw [hlevel]; exact Or.inr hPlev
        · rintro (⟨lev, hlev, hPlev⟩ | hPi)
          · exact ⟨lev, Or.inl hlev, hPlev⟩
          · exact ⟨level, Or.inr hlevel, hPi⟩
      have hi2 : ∀ (i2 : Usize), i2.val = iL.val + 1 →
          spec_taint.items.val.take i2.val = spec_taint.items.val.take (iL.val + 1) :=
        fun i2 h2 => by rw [h2]
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [hi2 _ li1_post, hext, hd2Iff, hdenL, or_assoc]
    case isFalse h =>
      have heq' : iL.val = spec_taint.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hdenL ⊢
      exact hdenL
  · exact ⟨hli, hden⟩

/-! ## Loop 3 (= Loop 10) — CHECK 2b: fold `gate_egress` over `agent_flights` at the new floor -/

/-- `invoke_start_loop3` folds `gate_egress` at the fixed `conf_floor`, one in-flight invocation at
    a time (looking up its bound tool and stored attested egress); unbound invocations leave
    `denied` unchanged. -/
theorem invokeStartLoop3_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (agent : types.AgentId) (conf_floor : types.ConfLevel)
    (cgOf : types.ToolId → types.InvocationId → Bool)
    (hcg : ∀ t I, cgInst.passes content_gate agent t I st bg = .ok (cgOf t I))
    (ovOf ocOf : types.ToolId → Bool)
    (hov : ∀ t, state.KernelState.has_flow_override st agent t conf_floor = .ok (ovOf t))
    (hoc : ∀ t, state.KernelState.override_consumed st agent t conf_floor = .ok (ocOf t))
    (agent_flights : collections.VecSet types.InvocationId) (denied0 denied : Bool) (fi : Usize)
    (hfi : fi.val ≤ agent_flights.items.val.length)
    (hden : denied = true ↔ denied0 = true ∨
      ∃ flight_inv ∈ agent_flights.items.val.take fi.val, ∃ t, invToolC st flight_inv = some t ∧
        ∃ E, vmsMemLast st.invocation_egress flight_inv E ∧
          egressDenied (flowModeC bg conf_floor E) (cgOf t flight_inv) (ovOf t) (ocOf t)) :
    transitions.invoke_start_loop3 cgInst st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.integ_levels st.in_flight st.invocation_tool st.invocation_used
      st.invocation_egress st.tool_registered st.agent_instruction st.override_used
      st.flow_override st.agent_budget bg content_gate agent conf_floor denied agent_flights fi
      ⦃ res =>
      res = true ↔ denied0 = true ∨
        ∃ flight_inv ∈ agent_flights.items.val, ∃ t, invToolC st flight_inv = some t ∧
          ∃ E, vmsMemLast st.invocation_egress flight_inv E ∧
            egressDenied (flowModeC bg conf_floor E) (cgOf t flight_inv) (ovOf t) (ocOf t) ⦄ := by
  unfold transitions.invoke_start_loop3
  have hst : ((⟨st.agent_active, st.agent_parent, st.agent_cap, st.taint_levels, st.integ_levels,
      st.in_flight, st.invocation_tool, st.invocation_used, st.invocation_egress,
      st.tool_registered, st.agent_instruction, st.override_used, st.flow_override,
      st.agent_budget⟩ : state.KernelState)) = st := by cases st; rfl
  apply loop.spec_decr_nat
    (measure := fun p => agent_flights.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ agent_flights.items.val.length ∧
      (p.1 = true ↔ denied0 = true ∨
        ∃ flight_inv ∈ agent_flights.items.val.take p.2.val, ∃ t, invToolC st flight_inv = some t ∧
          ∃ E, vmsMemLast st.invocation_egress flight_inv E ∧
            egressDenied (flowModeC bg conf_floor E) (cgOf t flight_inv) (ovOf t) (ocOf t)))
  · rintro ⟨deniedL, fiL⟩ ⟨hile, hdenL⟩
    dsimp only at hile hdenL ⊢
    simp only [transitions.invoke_start_loop3.body, collections.VecSet.len, collections.VecSet.at,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : fiL.val < agent_flights.items.val.length := by scalar_tac
      step as ⟨flight_inv, hflight_inv⟩
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.ToolId.Insts.CoreCloneClone toolId_clone_spec st.invocation_tool flight_inv)
      rw [hoEq]; simp only [bind_tc_ok]
      have hi2 : ∀ (i2 : Usize), i2.val = fiL.val + 1 →
          agent_flights.items.val.take i2.val = agent_flights.items.val.take (fiL.val + 1) :=
        fun i2 h2 => by rw [h2]
      have hext : ∀ (P : types.InvocationId → Prop),
          (∃ x ∈ agent_flights.items.val.take (fiL.val + 1), P x) ↔
          (∃ x ∈ agent_flights.items.val.take fiL.val, P x) ∨ P flight_inv := by
        intro P
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨x, hx | hx, hPx⟩
          · exact Or.inl ⟨x, hx, hPx⟩
          · subst hx; rw [hflight_inv]; exact Or.inr hPx
        · rintro (⟨x, hx, hPx⟩ | hPi)
          · exact ⟨x, Or.inl hx, hPx⟩
          · exact ⟨flight_inv, Or.inr hflight_inv, hPi⟩
      cases hocase : o with
      | none =>
        have hnone : invToolC st flight_inv = none := by unfold invToolC; rw [← ho]; exact hocase
        have hnf : ¬ ∃ t, invToolC st flight_inv = some t ∧
            ∃ E, vmsMemLast st.invocation_egress flight_inv E ∧
              egressDenied (flowModeC bg conf_floor E) (cgOf t flight_inv) (ovOf t) (ocOf t) := by
          rintro ⟨t, ht, _⟩; rw [hnone] at ht; simp at ht
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hi2 _ fi1_post, hext, hdenL]
        constructor
        · rintro (hA | hB)
          · exact Or.inl hA
          · exact Or.inr (Or.inl hB)
        · rintro (hA | hB | hC)
          · exact Or.inl hA
          · exact Or.inr hB
          · exact absurd hC hnf
      | some flight_tool_id =>
        have hsome : invToolC st flight_inv = some flight_tool_id := by
          unfold invToolC; rw [← ho]; exact hocase
        obtain ⟨flight_egress, hfeEq, hfeMem⟩ := spec_imp_exists
          (getSetOrEmpty_spec types.InvocationId.Insts.CoreCloneClone
            types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
            types.EgressKind.Insts.CoreCloneClone types.EgressKind.Insts.CoreCmpPartialEqEgressKind
            egressKind_clone_spec st.invocation_egress flight_inv)
        rw [hfeEq]; simp only [bind_tc_ok]
        rw [hst]
        obtain ⟨d2, hd2Eq, hd2Iff⟩ := spec_imp_exists
          (gateEgress_spec cgInst bg content_gate agent flight_tool_id flight_inv st conf_floor
            flight_egress (cgOf flight_tool_id flight_inv) (ovOf flight_tool_id) (ocOf flight_tool_id)
            (hcg flight_tool_id flight_inv) (hov flight_tool_id) (hoc flight_tool_id)
            (flowModeC bg conf_floor) (flowMode_eq bg conf_floor) deniedL)
        rw [hd2Eq]; simp only [bind_tc_ok]
        have hexPack : (∃ E ∈ flight_egress.items.val,
            egressDenied (flowModeC bg conf_floor E) (cgOf flight_tool_id flight_inv)
              (ovOf flight_tool_id) (ocOf flight_tool_id)) ↔
            (∃ E, vmsMemLast st.invocation_egress flight_inv E ∧
              egressDenied (flowModeC bg conf_floor E) (cgOf flight_tool_id flight_inv)
                (ovOf flight_tool_id) (ocOf flight_tool_id)) := by
          constructor
          · rintro ⟨E, hE, hden⟩; exact ⟨E, (hfeMem E).mp hE, hden⟩
          · rintro ⟨E, hE, hden⟩; exact ⟨E, (hfeMem E).mpr hE, hden⟩
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hi2 _ fi1_post, hext, hd2Iff, hexPack, hdenL]
        constructor
        · rintro ((hA1 | hA2) | hC)
          · exact Or.inl hA1
          · exact Or.inr (Or.inl hA2)
          · exact Or.inr (Or.inr ⟨flight_tool_id, hsome, hC⟩)
        · rintro (hA | hB | ⟨t, ht, hE⟩)
          · exact Or.inl (Or.inl hA)
          · exact Or.inl (Or.inr hB)
          · rw [hsome, Option.some_inj] at ht; subst ht; exact Or.inr hE
    case isFalse h =>
      have heq' : fiL.val = agent_flights.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hdenL ⊢
      exact hdenL
  · exact ⟨hfi, hden⟩

/-! ## Loop 4 (= Loop 11) — CHECK 4a: fold `integ_decision` over `spec_integ` at the new tool's floor -/

/-- `invoke_start_loop4` folds `integ_decision` at the fixed new `(tool, inv)`/floor/inspect-floor
    over each speculative-integrity level: monotonically `integ_denied`, no accumulator. -/
theorem invokeStartLoop4_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (agent : types.AgentId) (tool : types.ToolId) (inv : types.InvocationId)
    (floor inspect_floor : types.IntegLevel)
    (cgVal : Bool) (hcg : cgInst.passes content_gate agent tool inv st bg = .ok cgVal)
    (spec_integ : collections.VecSet types.IntegLevel) (denied0 denied : Bool) (igi : Usize)
    (higi : igi.val ≤ spec_integ.items.val.length)
    (hden : denied = true ↔ denied0 = true ∨
      ∃ level ∈ spec_integ.items.val.take igi.val,
        ¬ (integLeC floor level = true ∨ (integLeC inspect_floor level = true ∧ cgVal = true))) :
    transitions.invoke_start_loop4 cgInst st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.integ_levels st.in_flight st.invocation_tool st.invocation_used
      st.invocation_egress st.tool_registered st.agent_instruction st.override_used
      st.flow_override st.agent_budget bg content_gate agent tool inv floor inspect_floor denied
      spec_integ igi ⦃ res =>
      res = true ↔ denied0 = true ∨
        ∃ level ∈ spec_integ.items.val,
          ¬ (integLeC floor level = true ∨ (integLeC inspect_floor level = true ∧ cgVal = true)) ⦄ := by
  unfold transitions.invoke_start_loop4
  have hst : ((⟨st.agent_active, st.agent_parent, st.agent_cap, st.taint_levels, st.integ_levels,
      st.in_flight, st.invocation_tool, st.invocation_used, st.invocation_egress,
      st.tool_registered, st.agent_instruction, st.override_used, st.flow_override,
      st.agent_budget⟩ : state.KernelState)) = st := by cases st; rfl
  apply loop.spec_decr_nat
    (measure := fun p => spec_integ.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ spec_integ.items.val.length ∧
      (p.1 = true ↔ denied0 = true ∨
        ∃ level ∈ spec_integ.items.val.take p.2.val,
          ¬ (integLeC floor level = true ∨ (integLeC inspect_floor level = true ∧ cgVal = true))))
  · rintro ⟨deniedL, igiL⟩ ⟨hile, hdenL⟩
    dsimp only at hile hdenL ⊢
    simp only [transitions.invoke_start_loop4.body, collections.VecSet.len, collections.VecSet.at,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : igiL.val < spec_integ.items.val.length := by scalar_tac
      step as ⟨level, hlevel⟩
      rw [hst]
      obtain ⟨id, hidEq, hidAllow, hidDeny⟩ := spec_imp_exists
        (integDecision_spec cgInst content_gate agent tool inv st bg floor inspect_floor level
          cgVal hcg)
      rw [hidEq]; simp only [bind_tc_ok]
      have hext : (∃ lev ∈ spec_integ.items.val.take (igiL.val + 1),
            ¬ (integLeC floor lev = true ∨ (integLeC inspect_floor lev = true ∧ cgVal = true))) ↔
          (∃ lev ∈ spec_integ.items.val.take igiL.val,
              ¬ (integLeC floor lev = true ∨ (integLeC inspect_floor lev = true ∧ cgVal = true)))
          ∨ ¬ (integLeC floor level = true ∨ (integLeC inspect_floor level = true ∧ cgVal = true)) := by
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨lev, hlev | hlev, hPlev⟩
          · exact Or.inl ⟨lev, hlev, hPlev⟩
          · subst hlev; rw [hlevel]; exact Or.inr hPlev
        · rintro (⟨lev, hlev, hPlev⟩ | hPi)
          · exact ⟨lev, Or.inl hlev, hPlev⟩
          · exact ⟨level, Or.inr hlevel, hPi⟩
      have hi2 : ∀ (i2 : Usize), i2.val = igiL.val + 1 →
          spec_integ.items.val.take i2.val = spec_integ.items.val.take (igiL.val + 1) :=
        fun i2 h2 => by rw [h2]
      cases id with
      | Allowed =>
        have hnd : ¬ ¬ (integLeC floor level = true ∨ (integLeC inspect_floor level = true ∧ cgVal = true)) :=
          fun hc => hc (hidAllow.mp rfl)
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hi2 _ igi1_post, hext, hdenL]
        constructor
        · rintro (hA | hB)
          · exact Or.inl hA
          · exact Or.inr (Or.inl hB)
        · rintro (hA | hB | hC)
          · exact Or.inl hA
          · exact Or.inr hB
          · exact absurd hC hnd
      | Denied =>
        have hd : ¬ (integLeC floor level = true ∨ (integLeC inspect_floor level = true ∧ cgVal = true)) :=
          hidDeny.mp rfl
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hi2 _ igi1_post, hext]
        exact ⟨fun _ => Or.inr (Or.inr hd), fun _ => trivial⟩
    case isFalse h =>
      have heq' : igiL.val = spec_integ.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hdenL ⊢
      exact hdenL
  · exact ⟨higi, hden⟩

/-! ## Loop 5 (= Loop 12) — CHECK 4b: fold `integ_decision` over `agent_flights` at the new emission -/

/-- `invoke_start_loop5` folds `integ_decision` at the fixed new emission `il`, one in-flight
    invocation at a time (looking up its bound tool's OWN floor/inspect-floor); unbound
    invocations or tools missing metadata leave `integ_denied` unchanged. -/
theorem invokeStartLoop5_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (agent : types.AgentId) (il : types.IntegLevel)
    (cgOf : types.ToolId → types.InvocationId → Bool)
    (hcg : ∀ t I, cgInst.passes content_gate agent t I st bg = .ok (cgOf t I))
    (agent_flights : collections.VecSet types.InvocationId) (denied0 denied : Bool) (fbi : Usize)
    (hfbi : fbi.val ≤ agent_flights.items.val.length)
    (hden : denied = true ↔ denied0 = true ∨
      ∃ flight_inv ∈ agent_flights.items.val.take fbi.val, ∃ t tmeta,
        invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
        ¬ (integLeC tmeta.integ_floor il = true
            ∨ (integLeC tmeta.integ_inspect_floor il = true ∧ cgOf t flight_inv = true))) :
    transitions.invoke_start_loop5 cgInst st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.integ_levels st.in_flight st.invocation_tool st.invocation_used
      st.invocation_egress st.tool_registered st.agent_instruction st.override_used
      st.flow_override st.agent_budget bg content_gate agent il agent_flights denied fbi ⦃ res =>
      res = true ↔ denied0 = true ∨
        ∃ flight_inv ∈ agent_flights.items.val, ∃ t tmeta,
          invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
          ¬ (integLeC tmeta.integ_floor il = true
              ∨ (integLeC tmeta.integ_inspect_floor il = true ∧ cgOf t flight_inv = true)) ⦄ := by
  unfold transitions.invoke_start_loop5
  have hst : ((⟨st.agent_active, st.agent_parent, st.agent_cap, st.taint_levels, st.integ_levels,
      st.in_flight, st.invocation_tool, st.invocation_used, st.invocation_egress,
      st.tool_registered, st.agent_instruction, st.override_used, st.flow_override,
      st.agent_budget⟩ : state.KernelState)) = st := by cases st; rfl
  apply loop.spec_decr_nat
    (measure := fun p => agent_flights.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ agent_flights.items.val.length ∧
      (p.1 = true ↔ denied0 = true ∨
        ∃ flight_inv ∈ agent_flights.items.val.take p.2.val, ∃ t tmeta,
          invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
          ¬ (integLeC tmeta.integ_floor il = true
              ∨ (integLeC tmeta.integ_inspect_floor il = true ∧ cgOf t flight_inv = true))))
  · rintro ⟨deniedL, fbiL⟩ ⟨hile, hdenL⟩
    dsimp only at hile hdenL ⊢
    simp only [transitions.invoke_start_loop5.body, collections.VecSet.len, collections.VecSet.at,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : fbiL.val < agent_flights.items.val.length := by scalar_tac
      step as ⟨flight_inv, hflight_inv⟩
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.ToolId.Insts.CoreCloneClone toolId_clone_spec st.invocation_tool flight_inv)
      rw [hoEq]; simp only [bind_tc_ok]
      have hi2 : ∀ (i2 : Usize), i2.val = fbiL.val + 1 →
          agent_flights.items.val.take i2.val = agent_flights.items.val.take (fbiL.val + 1) :=
        fun i2 h2 => by rw [h2]
      have hext : ∀ (P : types.InvocationId → Prop),
          (∃ x ∈ agent_flights.items.val.take (fbiL.val + 1), P x) ↔
          (∃ x ∈ agent_flights.items.val.take fbiL.val, P x) ∨ P flight_inv := by
        intro P
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨x, hx | hx, hPx⟩
          · exact Or.inl ⟨x, hx, hPx⟩
          · subst hx; rw [hflight_inv]; exact Or.inr hPx
        · rintro (⟨x, hx, hPx⟩ | hPi)
          · exact ⟨x, Or.inl hx, hPx⟩
          · exact ⟨flight_inv, Or.inr hflight_inv, hPi⟩
      cases hocase : o with
      | none =>
        have hnone : invToolC st flight_inv = none := by unfold invToolC; rw [← ho]; exact hocase
        have hnf : ¬ ∃ t tmeta, invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
            ¬ (integLeC tmeta.integ_floor il = true
                ∨ (integLeC tmeta.integ_inspect_floor il = true ∧ cgOf t flight_inv = true)) := by
          rintro ⟨t, tmeta, ht, _⟩; rw [hnone] at ht; simp at ht
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hi2 _ fbi1_post, hext, hdenL]
        constructor
        · rintro (hA | hB)
          · exact Or.inl hA
          · exact Or.inr (Or.inl hB)
        · rintro (hA | hB | hC)
          · exact Or.inl hA
          · exact Or.inr hB
          · exact absurd hC hnf
      | some flight_tool_id =>
        have hsomeInv : invToolC st flight_inv = some flight_tool_id := by
          unfold invToolC; rw [← ho]; exact hocase
        simp only []
        obtain ⟨o1, ho1Eq, ho1⟩ := spec_imp_exists (toolMetadata_spec bg flight_tool_id)
        rw [ho1Eq]; simp only [bind_tc_ok]
        cases hmcase : o1 with
        | none =>
          have hnm : toolMetaC bg flight_tool_id = none := by rw [← ho1]; exact hmcase
          have hnf : ¬ ∃ t tmeta, invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
              ¬ (integLeC tmeta.integ_floor il = true
                  ∨ (integLeC tmeta.integ_inspect_floor il = true ∧ cgOf t flight_inv = true)) := by
            rintro ⟨t, tmeta, ht, hm, _⟩
            rw [hsomeInv, Option.some_inj] at ht; subst ht; rw [hnm] at hm; simp at hm
          simp only [bind_tc_ok]
          step*
          refine ⟨by scalar_tac, ?_, by scalar_tac⟩
          rw [hi2 _ fbi1_post, hext, hdenL]
          constructor
          · rintro (hA | hB)
            · exact Or.inl hA
            · exact Or.inr (Or.inl hB)
          · rintro (hA | hB | hC)
            · exact Or.inl hA
            · exact Or.inr hB
            · exact absurd hC hnf
        | some flight_meta =>
          have hm : toolMetaC bg flight_tool_id = some flight_meta := by rw [← ho1]; exact hmcase
          simp only []
          rw [hst]
          obtain ⟨id, hidEq, hidAllow, hidDeny⟩ := spec_imp_exists
            (integDecision_spec cgInst content_gate agent flight_tool_id flight_inv st bg
              flight_meta.integ_floor flight_meta.integ_inspect_floor il
              (cgOf flight_tool_id flight_inv) (hcg flight_tool_id flight_inv))
          rw [hidEq]
          have hPcur : (∃ t tmeta, invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
                ¬ (integLeC tmeta.integ_floor il = true
                    ∨ (integLeC tmeta.integ_inspect_floor il = true ∧ cgOf t flight_inv = true))) ↔
              ¬ (integLeC flight_meta.integ_floor il = true
                  ∨ (integLeC flight_meta.integ_inspect_floor il = true
                      ∧ cgOf flight_tool_id flight_inv = true)) := by
            constructor
            · rintro ⟨t, tmeta, ht, hmm, hc⟩
              rw [hsomeInv, Option.some_inj] at ht; subst ht
              rw [hm, Option.some_inj] at hmm; subst hmm; exact hc
            · intro hc; exact ⟨flight_tool_id, flight_meta, hsomeInv, hm, hc⟩
          cases id with
          | Allowed =>
            have hnd : ¬ ¬ (integLeC flight_meta.integ_floor il = true
                ∨ (integLeC flight_meta.integ_inspect_floor il = true
                    ∧ cgOf flight_tool_id flight_inv = true)) := fun hc => hc (hidAllow.mp rfl)
            simp only [bind_tc_ok]
            step*
            refine ⟨by scalar_tac, ?_, by scalar_tac⟩
            rw [hi2 _ fbi1_post, hext, hPcur, hdenL]
            constructor
            · rintro (hA | hB)
              · exact Or.inl hA
              · exact Or.inr (Or.inl hB)
            · rintro (hA | hB | hC)
              · exact Or.inl hA
              · exact Or.inr hB
              · exact absurd hC hnd
          | Denied =>
            have hd : ¬ (integLeC flight_meta.integ_floor il = true
                ∨ (integLeC flight_meta.integ_inspect_floor il = true
                    ∧ cgOf flight_tool_id flight_inv = true)) := hidDeny.mp rfl
            simp only [bind_tc_ok]
            step*
            refine ⟨by scalar_tac, ?_, by scalar_tac⟩
            rw [hi2 _ fbi1_post, hext]
            exact ⟨fun _ => Or.inr (Or.inr (hPcur.mpr hd)), fun _ => trivial⟩
    case isFalse h =>
      have heq' : fbiL.val = agent_flights.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hdenL ⊢
      exact hdenL
  · exact ⟨hfbi, hden⟩

/-! ## Loop 6 (= Loop 13) — eager consumption over `spec_taint` (CHECK 2a's arm) -/

/-- `invoke_start_loop6` inserts `{tool, level}` into `to_consume` for every speculative-taint
    `level` at which `agent` holds an armed override on the new `tool` — unconditionally, no
    egress/denial conjunct (eager consumption, design §5.3). -/
theorem invokeStartLoop6_spec
    (st : state.KernelState) (agent : types.AgentId) (tool : types.ToolId)
    (spec_taint : collections.VecSet types.ConfLevel)
    (to_consume0 to_consume : collections.VecSet types.OverrideKey) (ti : Usize)
    (hti : ti.val ≤ spec_taint.items.val.length)
    (hcap : to_consume0.items.val.length + spec_taint.items.val.length ≤ Usize.max)
    (hlen : to_consume.items.val.length ≤ to_consume0.items.val.length + ti.val)
    (hmem : ∀ k, vsMem to_consume k ↔ vsMem to_consume0 k ∨
      ∃ level ∈ spec_taint.items.val.take ti.val,
        k = ({ tool := tool, level := level } : types.OverrideKey) ∧
        vmsMemLast st.flow_override agent { tool := tool, level := level }) :
    transitions.invoke_start_loop6 st.agent_active st.agent_parent st.agent_cap st.taint_levels
      st.integ_levels st.in_flight st.invocation_tool st.invocation_used st.invocation_egress
      st.tool_registered st.agent_instruction st.override_used st.flow_override st.agent_budget
      agent tool spec_taint to_consume ti ⦃ res =>
      (∀ k, vsMem res k ↔ vsMem to_consume0 k ∨
        ∃ level ∈ spec_taint.items.val,
          k = ({ tool := tool, level := level } : types.OverrideKey) ∧
          vmsMemLast st.flow_override agent { tool := tool, level := level }) ∧
      res.items.val.length ≤ to_consume0.items.val.length + spec_taint.items.val.length ⦄ := by
  unfold transitions.invoke_start_loop6
  have hst : ((⟨st.agent_active, st.agent_parent, st.agent_cap, st.taint_levels, st.integ_levels,
      st.in_flight, st.invocation_tool, st.invocation_used, st.invocation_egress,
      st.tool_registered, st.agent_instruction, st.override_used, st.flow_override,
      st.agent_budget⟩ : state.KernelState)) = st := by cases st; rfl
  apply loop.spec_decr_nat
    (measure := fun p => spec_taint.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ spec_taint.items.val.length ∧
      p.1.items.val.length ≤ to_consume0.items.val.length + p.2.val ∧
      (∀ k, vsMem p.1 k ↔ vsMem to_consume0 k ∨
        ∃ level ∈ spec_taint.items.val.take p.2.val,
          k = ({ tool := tool, level := level } : types.OverrideKey) ∧
          vmsMemLast st.flow_override agent { tool := tool, level := level }))
  · rintro ⟨tcL, tiL⟩ ⟨hile, hlenL, hmemL⟩
    dsimp only at hile hlenL hmemL ⊢
    simp only [transitions.invoke_start_loop6.body, collections.VecSet.len, collections.VecSet.at,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : tiL.val < spec_taint.items.val.length := by scalar_tac
      step as ⟨level, hlevel⟩
      rw [hst]
      obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists (hasFlowOverride_spec st agent tool level)
      rw [hbEq]; simp only [bind_tc_ok]
      have hi2 : ∀ (i2 : Usize), i2.val = tiL.val + 1 →
          spec_taint.items.val.take i2.val = spec_taint.items.val.take (tiL.val + 1) :=
        fun i2 h2 => by rw [h2]
      have hext : ∀ (P : types.ConfLevel → Prop),
          (∃ x ∈ spec_taint.items.val.take (tiL.val + 1), P x) ↔
          (∃ x ∈ spec_taint.items.val.take tiL.val, P x) ∨ P level := by
        intro P
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨x, hx | hx, hPx⟩
          · exact Or.inl ⟨x, hx, hPx⟩
          · subst hx; rw [hlevel]; exact Or.inr hPx
        · rintro (⟨x, hx, hPx⟩ | hPi)
          · exact ⟨x, Or.inl hx, hPx⟩
          · exact ⟨level, Or.inr hlevel, hPi⟩
      split
      next h =>
        have hin : vmsMemLast st.flow_override agent { tool := tool, level := level } := hbIff.mp h
        rw [toolId_clone_spec]; simp only [bind_tc_ok]
        have hcapIns : tcL.items.val.length < Usize.max := by
          have := hlenL; have := hlt; have := hcap; omega
        obtain ⟨tc1, htc1Eq, htc1Mem, htc1Len⟩ := spec_imp_exists
          (vecSetInsertLen_spec types.OverrideKey.Insts.CoreCloneClone
            types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey overrideKey_eq_spec tcL
            { tool := tool, level := level } hcapIns)
        rw [htc1Eq]; try simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, by omega, ?_, by scalar_tac⟩
        intro k
        rw [htc1Mem k, hi2 _ ti1_post, hext (fun lev => k = ({tool := tool, level := lev} :
          types.OverrideKey) ∧ vmsMemLast st.flow_override agent {tool := tool, level := lev}),
          hmemL k]
        constructor
        · rintro ((hA | hB) | hC)
          · exact Or.inl hA
          · exact Or.inr (Or.inl hB)
          · exact Or.inr (Or.inr ⟨hC, hin⟩)
        · rintro (hA | hB | ⟨hC1, hC2⟩)
          · exact Or.inl (Or.inl hA)
          · exact Or.inl (Or.inr hB)
          · exact Or.inr (by rw [hC1])
      next h =>
        have hnin : ¬ vmsMemLast st.flow_override agent { tool := tool, level := level } := by
          intro hc; have := hbIff.mpr hc; exact h this
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        intro k
        rw [hi2 _ ti1_post, hext (fun lev => k = ({tool := tool, level := lev} :
          types.OverrideKey) ∧ vmsMemLast st.flow_override agent {tool := tool, level := lev}),
          hmemL k]
        constructor
        · rintro (hA | hB)
          · exact Or.inl hA
          · exact Or.inr (Or.inl hB)
        · rintro (hA | hB | ⟨hC1, hC2⟩)
          · exact Or.inl hA
          · exact Or.inr hB
          · exact absurd (hC1 ▸ hC2) hnin
    case isFalse h =>
      have heq' : tiL.val = spec_taint.items.val.length := by scalar_tac
      rw [heq'] at hlenL
      simp only [spec_ok, heq', List.take_length] at hmemL ⊢
      exact ⟨hmemL, hlenL⟩
  · exact ⟨hti, hlen, hmem⟩

/-! ## Loop 7 (= Loop 14) — eager consumption over `agent_flights` (CHECK 2b's arm) -/

/-- `invoke_start_loop7` inserts `{flight_tool_id, conf_floor}` into `to_consume` for every
    in-flight invocation whose bound tool has an armed override at `conf_floor` — unbound
    invocations are skipped. -/
theorem invokeStartLoop7_spec
    (st : state.KernelState) (agent : types.AgentId) (conf_floor : types.ConfLevel)
    (agent_flights : collections.VecSet types.InvocationId)
    (to_consume0 to_consume : collections.VecSet types.OverrideKey) (ri : Usize)
    (hri : ri.val ≤ agent_flights.items.val.length)
    (hcap : to_consume0.items.val.length + agent_flights.items.val.length ≤ Usize.max)
    (hlen : to_consume.items.val.length ≤ to_consume0.items.val.length + ri.val)
    (hmem : ∀ k, vsMem to_consume k ↔ vsMem to_consume0 k ∨
      ∃ flight_inv ∈ agent_flights.items.val.take ri.val, ∃ t, invToolC st flight_inv = some t ∧
        k = ({ tool := t, level := conf_floor } : types.OverrideKey) ∧
        vmsMemLast st.flow_override agent { tool := t, level := conf_floor }) :
    transitions.invoke_start_loop7 st.agent_active st.agent_parent st.agent_cap st.taint_levels
      st.integ_levels st.in_flight st.invocation_tool st.invocation_used st.invocation_egress
      st.tool_registered st.agent_instruction st.override_used st.flow_override st.agent_budget
      agent conf_floor agent_flights to_consume ri ⦃ res =>
      (∀ k, vsMem res k ↔ vsMem to_consume0 k ∨
        ∃ flight_inv ∈ agent_flights.items.val, ∃ t, invToolC st flight_inv = some t ∧
          k = ({ tool := t, level := conf_floor } : types.OverrideKey) ∧
          vmsMemLast st.flow_override agent { tool := t, level := conf_floor }) ∧
      res.items.val.length ≤ to_consume0.items.val.length + agent_flights.items.val.length ⦄ := by
  unfold transitions.invoke_start_loop7
  have hst : ((⟨st.agent_active, st.agent_parent, st.agent_cap, st.taint_levels, st.integ_levels,
      st.in_flight, st.invocation_tool, st.invocation_used, st.invocation_egress,
      st.tool_registered, st.agent_instruction, st.override_used, st.flow_override,
      st.agent_budget⟩ : state.KernelState)) = st := by cases st; rfl
  apply loop.spec_decr_nat
    (measure := fun p => agent_flights.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ agent_flights.items.val.length ∧
      p.1.items.val.length ≤ to_consume0.items.val.length + p.2.val ∧
      (∀ k, vsMem p.1 k ↔ vsMem to_consume0 k ∨
        ∃ flight_inv ∈ agent_flights.items.val.take p.2.val, ∃ t, invToolC st flight_inv = some t ∧
          k = ({ tool := t, level := conf_floor } : types.OverrideKey) ∧
          vmsMemLast st.flow_override agent { tool := t, level := conf_floor }))
  · rintro ⟨tcL, riL⟩ ⟨hile, hlenL, hmemL⟩
    dsimp only at hile hlenL hmemL ⊢
    simp only [transitions.invoke_start_loop7.body, collections.VecSet.len, collections.VecSet.at,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : riL.val < agent_flights.items.val.length := by scalar_tac
      step as ⟨flight_inv, hflight_inv⟩
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.ToolId.Insts.CoreCloneClone toolId_clone_spec st.invocation_tool flight_inv)
      rw [hoEq]; simp only [bind_tc_ok]
      have hi2 : ∀ (i2 : Usize), i2.val = riL.val + 1 →
          agent_flights.items.val.take i2.val = agent_flights.items.val.take (riL.val + 1) :=
        fun i2 h2 => by rw [h2]
      have hext : ∀ (P : types.InvocationId → Prop),
          (∃ x ∈ agent_flights.items.val.take (riL.val + 1), P x) ↔
          (∃ x ∈ agent_flights.items.val.take riL.val, P x) ∨ P flight_inv := by
        intro P
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨x, hx | hx, hPx⟩
          · exact Or.inl ⟨x, hx, hPx⟩
          · subst hx; rw [hflight_inv]; exact Or.inr hPx
        · rintro (⟨x, hx, hPx⟩ | hPi)
          · exact ⟨x, Or.inl hx, hPx⟩
          · exact ⟨flight_inv, Or.inr hflight_inv, hPi⟩
      cases hocase : o with
      | none =>
        have hnone : invToolC st flight_inv = none := by unfold invToolC; rw [← ho]; exact hocase
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
        intro k
        rw [hi2 _ ri1_post, hext, hmemL k]
        constructor
        · rintro (hA | hB)
          · exact Or.inl hA
          · exact Or.inr (Or.inl hB)
        · rintro (hA | hB | ⟨t, ht, _⟩)
          · exact Or.inl hA
          · exact Or.inr hB
          · rw [hnone] at ht; simp at ht
      | some flight_tool_id =>
        have hsomeInv : invToolC st flight_inv = some flight_tool_id := by
          unfold invToolC; rw [← ho]; exact hocase
        simp only []
        rw [hst]
        obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists
          (hasFlowOverride_spec st agent flight_tool_id conf_floor)
        rw [hbEq]; simp only [bind_tc_ok]
        split
        next h =>
          have hin : vmsMemLast st.flow_override agent { tool := flight_tool_id, level := conf_floor } :=
            hbIff.mp h
          have hcapIns : tcL.items.val.length < Usize.max := by
            have := hlenL; have := hlt; have := hcap; omega
          obtain ⟨tc1, htc1Eq, htc1Mem, htc1Len⟩ := spec_imp_exists
            (vecSetInsertLen_spec types.OverrideKey.Insts.CoreCloneClone
              types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey overrideKey_eq_spec tcL
              { tool := flight_tool_id, level := conf_floor } hcapIns)
          rw [htc1Eq]; try simp only [bind_tc_ok]
          step*
          refine ⟨by scalar_tac, by omega, ?_, by scalar_tac⟩
          intro k
          rw [htc1Mem k, hi2 _ ri1_post, hext, hmemL k]
          constructor
          · rintro ((hA | hB) | hC)
            · exact Or.inl hA
            · exact Or.inr (Or.inl hB)
            · exact Or.inr (Or.inr ⟨flight_tool_id, hsomeInv, hC, hin⟩)
          · rintro (hA | hB | ⟨t, ht, hk, hov⟩)
            · exact Or.inl (Or.inl hA)
            · exact Or.inl (Or.inr hB)
            · rw [hsomeInv, Option.some_inj] at ht; subst ht; exact Or.inr hk
        next h =>
          have hnin : ¬ vmsMemLast st.flow_override agent { tool := flight_tool_id, level := conf_floor } := by
            intro hc; exact h (hbIff.mpr hc)
          simp only [bind_tc_ok]
          step*
          refine ⟨by scalar_tac, by scalar_tac, ?_, by scalar_tac⟩
          intro k
          rw [hi2 _ ri1_post, hext, hmemL k]
          constructor
          · rintro (hA | hB)
            · exact Or.inl hA
            · exact Or.inr (Or.inl hB)
          · rintro (hA | hB | ⟨t, ht, hk, hov⟩)
            · exact Or.inl hA
            · exact Or.inr hB
            · rw [hsomeInv, Option.some_inj] at ht; subst ht; exact absurd hov hnin
    case isFalse h =>
      have heq' : riL.val = agent_flights.items.val.length := by scalar_tac
      rw [heq'] at hlenL
      simp only [spec_ok, heq', List.take_length] at hmemL ⊢
      exact ⟨hmemL, hlenL⟩
  · exact ⟨hri, hlen, hmem⟩

/-! ## `any_value_contains` — the freshness guard `∀ AG, ¬ in_flight AG inv` -/

/-- `any_value_contains self elem` folds `VecSet.contains` over every entry's nested set: `true`
    iff SOME entry's set holds `elem` (raw union membership, not last-match). -/
theorem anyValueContainsLoop_spec {K T : Type} [DecidableEq T]
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (heqT : ∀ a b : T, eqT.eq a b = .ok (decide (a = b)))
    (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (self : collections.VecMap K (collections.VecSet T)) (elem : T) (found0 : Bool) (i0 : Usize)
    (hi0 : i0.val ≤ self.entries.val.length)
    (hfound0 : found0 = true ↔
      ∃ ag vs, (ag, vs) ∈ self.entries.val.take i0.val ∧ elem ∈ vs.items.val) :
    collections.VecMapKVecSet.any_value_contains_loop cloneT eqT self elem found0 i0 ⦃ b =>
      b = true ↔ ∃ ag vs, (ag, vs) ∈ self.entries.val ∧ elem ∈ vs.items.val ⦄ := by
  unfold collections.VecMapKVecSet.any_value_contains_loop
  apply loop.spec_decr_nat
    (measure := fun p => self.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ self.entries.val.length ∧
      (p.1 = true ↔ ∃ ag vs, (ag, vs) ∈ self.entries.val.take p.2.val ∧ elem ∈ vs.items.val))
  · rintro ⟨found, iL⟩ ⟨hile, hfoundL⟩
    dsimp only at hile hfoundL ⊢
    simp only [collections.VecMapKVecSet.any_value_contains_loop.body, alloc.vec.Vec.len]
    split
    case isTrue h =>
      have hlt : iL.val < self.entries.val.length := by scalar_tac
      step as ⟨pk, vs, hp⟩
      rw [vecSetClone_spec cloneT hcloneT vs]
      simp only [bind_tc_ok]
      obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists (vecSetContains_spec cloneT eqT heqT vs elem)
      rw [hbEq]; simp only [bind_tc_ok]
      have hi2 : ∀ (i2 : Usize), i2.val = iL.val + 1 →
          self.entries.val.take i2.val = self.entries.val.take (iL.val + 1) := fun i2 h2 => by rw [h2]
      have hext : (∃ ag2 vs2, (ag2, vs2) ∈ self.entries.val.take (iL.val + 1) ∧ elem ∈ vs2.items.val) ↔
          (∃ ag2 vs2, (ag2, vs2) ∈ self.entries.val.take iL.val ∧ elem ∈ vs2.items.val)
          ∨ elem ∈ vs.items.val := by
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨ag2, vs2, hq | hq, hPq⟩
          · exact Or.inl ⟨ag2, vs2, hq, hPq⟩
          · have heqp : (ag2, vs2) = (pk, vs) := hq.trans hp.symm
            rw [Prod.mk.injEq] at heqp
            exact Or.inr (heqp.2 ▸ hPq)
        · rintro (⟨ag2, vs2, hq, hPq⟩ | hPi)
          · exact ⟨ag2, vs2, Or.inl hq, hPq⟩
          · exact ⟨pk, vs, Or.inr hp, hPi⟩
      split
      next hb =>
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hi2 _ i2_post, hext]
        constructor
        · intro _; exact Or.inr (hbIff.mp (by simpa using hb))
        · intro _; trivial
      next hb =>
        step*
        refine ⟨by scalar_tac, ?_, by scalar_tac⟩
        rw [hi2 _ i2_post, hext, hfoundL]
        constructor
        · intro h; exact Or.inl h
        · rintro (h | h)
          · exact h
          · exact absurd (hbIff.mpr h) (by simpa using hb)
    case isFalse h =>
      have heq' : iL.val = self.entries.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hfoundL ⊢
      exact hfoundL
  · exact ⟨hi0, hfound0⟩

theorem anyValueContains_spec {K T : Type} [DecidableEq T]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (heqT : ∀ a b : T, eqT.eq a b = .ok (decide (a = b)))
    (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (self : collections.VecMap K (collections.VecSet T)) (elem : T) :
    collections.VecMapKVecSet.any_value_contains cloneK eqK cloneT eqT self elem ⦃ b =>
      b = true ↔ ∃ ag vs, (ag, vs) ∈ self.entries.val ∧ elem ∈ vs.items.val ⦄ := by
  unfold collections.VecMapKVecSet.any_value_contains
  exact anyValueContainsLoop_spec cloneT eqT heqT hcloneT self elem false 0#usize (by simp) (by simp)

/-- `vmsMemLast` implies raw-union membership `vmsMem` unconditionally (no `Nodup` needed): the
    last-matching entry is one of the entries. Dual direction (`¬ vmsMem → ¬ vmsMemLast`) is what
    the freshness guard needs. -/
theorem vmsMemLast_imp_vmsMem {K T : Type} [DecidableEq K]
    (vm : collections.VecMap K (collections.VecSet T)) (k : K) (v : T) (h : vmsMemLast vm k v) :
    ∃ ag vs, (ag, vs) ∈ vm.entries.val ∧ v ∈ vs.items.val := by
  obtain ⟨vs, hvs, hv⟩ := h
  exact ⟨k, vs, vmLastEntry_mem vm.entries.val k (k, vs) hvs, hv⟩

/-! ## Non-denial disjunction (confidentiality side) -/

/-- `¬ egressDenied` unpacks into the three-way abstract admission disjunction: ALLOW outright,
    INSPECT with a passing gate, or DENY rescued by an unconsumed override. -/
theorem not_egressDenied_disj (fm : background.FlowMode) (cgVal ovVal ocVal : Bool)
    (h : ¬ egressDenied fm cgVal ovVal ocVal) :
    fm = .Allow ∨ (fm = .Inspect ∧ cgVal = true) ∨ (ovVal = true ∧ ocVal = false) := by
  unfold egressDenied at h
  cases fm with
  | Allow => exact Or.inl rfl
  | Inspect =>
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    cases cgVal with
    | true => rfl
    | false => exact absurd (Or.inl ⟨rfl, rfl⟩) h
  | Deny =>
    refine Or.inr (Or.inr ?_)
    cases ovVal with
    | false => exact absurd (Or.inr ⟨rfl, Or.inl rfl⟩) h
    | true =>
      cases ocVal with
      | false => exact ⟨rfl, rfl⟩
      | true => exact absurd (Or.inr ⟨rfl, Or.inr rfl⟩) h

/-! ## The shared post-coverage continuation

Everything from CHECK 1 onward is the same computation in both coverage branches (the kernel's
`b6 = m.egress.is_empty()` split duplicates it as loops 1-7 vs loops 8-14, `rfl`-equal pairwise),
so it is proved once here and invoked from both branches of `invoke_start_preservesR`. The
abstract-level facts the shared prefix establishes (activity, non-root, registration, freshness,
narrowing, coverage) enter as hypotheses. -/

set_option maxHeartbeats 8000000

private theorem invoke_start_core {A C : Type} (aInst : traits.AuthorizerOracle A)
    (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (authorizer : A) (content_gate : C)
    (a : AbsState) (agent : types.AgentId) (tool : types.ToolId) (inv : types.InvocationId)
    (attested_egress : collections.VecSet types.EgressKind) (m : background.ToolMetadata)
    (hR : R st bg a)
    (hCg : CgAgree cgInst content_gate st bg a)
    (hAu : AuAgree aInst authorizer st bg a)
    (hEgAgree : ∀ E, a.invocation_egress inv E ↔ vsMem attested_egress E)
    (hinvtool : a.invocation_tool inv = tool)
    (hFlightUsed : ∀ ag I, a.in_flight ag I → a.invocation_used I)
    (hcapFlow : vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent
      + vmSetLen st.in_flight agent + 1 ≤ Usize.max)
    (hcapInteg : vmSetLen st.integ_levels agent + vmSetLen st.in_flight agent ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJoint : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + (vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent + 1
        + vmSetLen st.in_flight agent) ≤ Usize.max)
    (hcapInvT : st.invocation_tool.entries.val.length < Usize.max)
    (hcapInflE : st.in_flight.entries.val.length < Usize.max)
    (hcapInflS : ∀ p ∈ st.in_flight.entries.val, p.2.items.val.length < Usize.max)
    (hcapUsed : st.invocation_used.items.val.length < Usize.max)
    (hcapEgress : st.invocation_egress.entries.val.length < Usize.max)
    (hmeta : toolMetaC bg tool = some m)
    (hActiveA : a.agent_active agent)
    (hNeRootA : agent ≠ a.root_agent)
    (hToolRegA : a.tool_registered tool)
    (hFreshFlightA : ∀ AG, ¬ a.in_flight AG inv)
    (hFreshUsedA : ¬ a.invocation_used inv)
    (hNarrowA : ∀ E, a.invocation_egress inv E → a.tool_egress tool E)
    (hCovA : (∃ E, a.tool_egress tool E) → (∃ E, a.invocation_egress inv E))
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : (do
      let missing_cap ←
        transitions.invoke_start_loop1 st.agent_cap agent
          m.capabilities false 0#usize
      if missing_cap
      then
        ok (core.result.Result.Err
          error.KernelError.CapabilityMissing)
      else
        let spec_taint ←
          state.KernelState.speculative_taint st agent bg
        let denied ←
          transitions.invoke_start_loop2
            cgInst st.agent_active
            st.agent_parent st.agent_cap st.taint_levels
            st.integ_levels st.in_flight st.invocation_tool
            st.invocation_used st.invocation_egress
            st.tool_registered st.agent_instruction
            st.override_used st.flow_override st.agent_budget bg
            content_gate agent tool inv attested_egress false
            spec_taint 0#usize
        let agent_flights ←
          collections.VecMapKVecSet.get_set_or_empty
            types.AgentId.Insts.CoreCloneClone
            types.AgentId.Insts.CoreCmpPartialEqAgentId
            types.InvocationId.Insts.CoreCloneClone
            types.InvocationId.Insts.CoreCmpPartialEqInvocationId
            st.in_flight agent
        let denied1 ←
          transitions.invoke_start_loop3
            cgInst st.agent_active
            st.agent_parent st.agent_cap st.taint_levels
            st.integ_levels st.in_flight st.invocation_tool
            st.invocation_used st.invocation_egress
            st.tool_registered st.agent_instruction
            st.override_used st.flow_override st.agent_budget bg
            content_gate agent m.conf_floor denied agent_flights
            0#usize
        let denied2 ←
          transitions.gate_egress cgInst bg
            content_gate agent tool inv st m.conf_floor
            attested_egress denied1
        if denied2
        then
          ok (core.result.Result.Err
            error.KernelError.FlowGateBlocked)
        else
          let b7 ←
            aInst.allows authorizer agent
              tool inv st bg
          if b7
          then
            let spec_integ ←
              state.KernelState.speculative_integ st agent bg
            let integ_denied ←
              transitions.invoke_start_loop4
                cgInst st.agent_active
                st.agent_parent st.agent_cap st.taint_levels
                st.integ_levels st.in_flight st.invocation_tool
                st.invocation_used st.invocation_egress
                st.tool_registered st.agent_instruction
                st.override_used st.flow_override st.agent_budget
                bg content_gate agent tool inv m.integ_floor
                m.integ_inspect_floor false spec_integ 0#usize
            let integ_denied1 ←
              transitions.invoke_start_loop5
                cgInst st.agent_active
                st.agent_parent st.agent_cap st.taint_levels
                st.integ_levels st.in_flight st.invocation_tool
                st.invocation_used st.invocation_egress
                st.tool_registered st.agent_instruction
                st.override_used st.flow_override st.agent_budget
                bg content_gate agent m.output_integ
                agent_flights integ_denied 0#usize
            let id ←
              transitions.integ_decision
                cgInst content_gate agent
                tool inv st bg m.integ_floor
                m.integ_inspect_floor m.output_integ
            let integ_denied2 ←
              (match id with
              | transitions.IntegDecision.Allowed =>
                ok integ_denied1
              | transitions.IntegDecision.Denied => ok true)
            if integ_denied2
            then
              ok (core.result.Result.Err
                error.KernelError.IntegrityFloorDenied)
            else
              let to_consume ←
                collections.VecSet.new
                  types.OverrideKey.Insts.CoreCloneClone
                  types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
              let to_consume1 ←
                transitions.invoke_start_loop6 st.agent_active
                  st.agent_parent st.agent_cap st.taint_levels
                  st.integ_levels st.in_flight st.invocation_tool
                  st.invocation_used st.invocation_egress
                  st.tool_registered st.agent_instruction
                  st.override_used st.flow_override
                  st.agent_budget agent tool spec_taint
                  to_consume 0#usize
              let b8 ←
                state.KernelState.has_flow_override st agent tool
                  m.conf_floor
              let to_consume2 ←
                (if b8
                then
                  do
                  let ti ←
                    types.ToolId.Insts.CoreCloneClone.clone tool
                  collections.VecSet.insert
                    types.OverrideKey.Insts.CoreCloneClone
                    types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
                    to_consume1
                    { tool := ti, level := m.conf_floor }
                else ok to_consume1)
              let to_consume3 ←
                transitions.invoke_start_loop7 st.agent_active
                  st.agent_parent st.agent_cap st.taint_levels
                  st.integ_levels st.in_flight st.invocation_tool
                  st.invocation_used st.invocation_egress
                  st.tool_registered st.agent_instruction
                  st.override_used st.flow_override
                  st.agent_budget agent m.conf_floor
                  agent_flights to_consume2 0#usize
              let b9 ←
                collections.VecSet.is_empty
                  types.OverrideKey.Insts.CoreCloneClone
                  types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
                  to_consume3
              let vm ←
                (if b9
                then ok st.override_used
                else
                  do
                  let ai1 ←
                    types.AgentId.Insts.CoreCloneClone.clone
                      agent
                  collections.VecMapKVecSet.extend_into
                    types.AgentId.Insts.CoreCloneClone
                    types.AgentId.Insts.CoreCmpPartialEqAgentId
                    types.OverrideKey.Insts.CoreCloneClone
                    types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
                    st.override_used ai1 to_consume3)
              let ii ←
                types.InvocationId.Insts.CoreCloneClone.clone inv
              let ti ←
                types.ToolId.Insts.CoreCloneClone.clone tool
              let vm1 ←
                collections.VecMap.insert
                  types.InvocationId.Insts.CoreCloneClone
                  types.InvocationId.Insts.CoreCmpPartialEqInvocationId
                  types.ToolId.Insts.CoreCloneClone
                  st.invocation_tool ii ti
              let ai1 ←
                types.AgentId.Insts.CoreCloneClone.clone agent
              let vm2 ←
                collections.VecMapKVecSet.insert_into
                  types.AgentId.Insts.CoreCloneClone
                  types.AgentId.Insts.CoreCmpPartialEqAgentId
                  types.InvocationId.Insts.CoreCloneClone
                  types.InvocationId.Insts.CoreCmpPartialEqInvocationId
                  st.in_flight ai1 ii
              let vm3 ←
                collections.VecMap.insert
                  types.InvocationId.Insts.CoreCloneClone
                  types.InvocationId.Insts.CoreCmpPartialEqInvocationId
                  (collections.VecSet.Insts.CoreCloneClone
                  types.EgressKind.Insts.CoreCloneClone)
                  st.invocation_egress ii attested_egress
              let vs ←
                collections.VecSet.insert
                  types.InvocationId.Insts.CoreCloneClone
                  types.InvocationId.Insts.CoreCmpPartialEqInvocationId
                  st.invocation_used ii
              ok (core.result.Result.Ok
                ({
                   st
                     with
                     in_flight := vm2,
                     invocation_tool := vm1,
                     invocation_used := vs,
                     invocation_egress := vm3,
                     override_used := vm
                 }, event.KernelAction.InvokeStart agent tool
                inv))
          else
            ok (core.result.Result.Err
              error.KernelError.AuthorizerDenied)
      ) = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.invoke_start agent tool inv).guard a ∧
          (Tzimtzum.invoke_start agent tool inv).next a a' ∧ R st' bg a' := by
  -- CHECK 1: capability gate
  obtain ⟨mc, hmcEq, hmcIff⟩ := spec_imp_exists
    (invokeStartLoop1_spec st.agent_cap agent m.capabilities false 0#usize (by simp) (by simp))
  rw [hmcEq] at hok; simp only [bind_tc_ok] at hok
  have hmc : mc = false := by cases mc with | false => rfl | true => simp at hok
  simp only [hmc, reduceIte, Bool.false_eq_true] at hok
  have hCapOk : ∀ c, vsMem m.capabilities c → vmsMemLast st.agent_cap agent c := by
    intro c hc
    by_contra hnc
    exact absurd (hmcIff.mpr ⟨c, hc, hnc⟩) (by simp [hmc])
  -- speculative taint / CHECK 2a
  obtain ⟨spec_taint, hstEq, hstMem, hstLen⟩ := spec_imp_exists
    (specTaint_spec st agent bg (by have := hcapFlow; omega))
  rw [hstEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨cgValInv, hcgInv, hcgAInv⟩ := hCg agent tool inv
  obtain ⟨denied, hdEq, hdIff⟩ := spec_imp_exists
    (invokeStartLoop2_spec cgInst st bg content_gate agent tool inv attested_egress cgValInv hcgInv
      (fun L => ovC st agent L tool) (fun L => ocC st agent L tool)
      (fun L => ovC_eq st agent L tool) (fun L => ocC_eq st agent L tool)
      spec_taint false false 0#usize (by simp) (by simp))
  rw [hdEq] at hok; simp only [bind_tc_ok] at hok
  -- CHECK 2b
  obtain ⟨agent_flights, hflEq, hflMem, hflLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
      agentId_eq_spec types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight agent)
  rw [hflEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨denied1, hd1Eq, hd1Iff⟩ := spec_imp_exists
    (invokeStartLoop3_spec cgInst st bg content_gate agent m.conf_floor
      (fun t I => Classical.choose (hCg agent t I))
      (fun t I => (Classical.choose_spec (hCg agent t I)).1)
      (fun t => ovC st agent m.conf_floor t) (fun t => ocC st agent m.conf_floor t)
      (fun t => ovC_eq st agent m.conf_floor t) (fun t => ocC_eq st agent m.conf_floor t)
      agent_flights denied denied 0#usize (by simp) (by simp))
  rw [hd1Eq] at hok; simp only [bind_tc_ok] at hok
  -- CHECK 2c
  obtain ⟨denied2, hd2Eq, hd2Iff⟩ := spec_imp_exists
    (gateEgress_spec cgInst bg content_gate agent tool inv st m.conf_floor attested_egress
      cgValInv (ovC st agent m.conf_floor tool) (ocC st agent m.conf_floor tool) hcgInv
      (ovC_eq st agent m.conf_floor tool) (ocC_eq st agent m.conf_floor tool)
      (flowModeC bg m.conf_floor) (flowMode_eq bg m.conf_floor) denied1)
  rw [hd2Eq] at hok; simp only [bind_tc_ok] at hok
  have hDen2 : denied2 = false := by cases denied2 with | false => rfl | true => simp at hok
  simp only [hDen2, reduceIte, Bool.false_eq_true] at hok
  -- CHECK 3: authorizer
  obtain ⟨auVal, hauEq, hauAIff⟩ := hAu agent tool inv
  rw [hauEq] at hok; simp only [bind_tc_ok] at hok
  have hAuTrue : auVal = true := by cases auVal with | true => rfl | false => simp at hok
  simp only [hAuTrue, reduceIte] at hok
  -- speculative integrity / CHECK 4a
  obtain ⟨spec_integ, hsiEq, hsiMem, hsiLen⟩ := spec_imp_exists
    (specInteg_spec st agent bg hcapInteg)
  rw [hsiEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨integ_denied, hidEq, hidIff⟩ := spec_imp_exists
    (invokeStartLoop4_spec cgInst st bg content_gate agent tool inv m.integ_floor
      m.integ_inspect_floor cgValInv hcgInv spec_integ false false 0#usize (by simp) (by simp))
  rw [hidEq] at hok; simp only [bind_tc_ok] at hok
  -- CHECK 4b
  obtain ⟨integ_denied1, hid1Eq, hid1Iff⟩ := spec_imp_exists
    (invokeStartLoop5_spec cgInst st bg content_gate agent m.output_integ
      (fun t I => Classical.choose (hCg agent t I))
      (fun t I => (Classical.choose_spec (hCg agent t I)).1)
      agent_flights integ_denied integ_denied 0#usize (by simp) (by simp))
  rw [hid1Eq] at hok; simp only [bind_tc_ok] at hok
  -- CHECK 4c
  obtain ⟨id4c, hid4cEq, hid4cAllow, hid4cDeny⟩ := spec_imp_exists
    (integDecision_spec cgInst content_gate agent tool inv st bg m.integ_floor
      m.integ_inspect_floor m.output_integ cgValInv hcgInv)
  rw [hid4cEq] at hok
  cases id4c with
  | Allowed =>
    simp only [bind_tc_ok] at hok
    have hid4cA : integLeC m.integ_floor m.output_integ = true
        ∨ (integLeC m.integ_inspect_floor m.output_integ = true ∧ cgValInv = true) := hid4cAllow.mp rfl
    have hIntegDen2 : integ_denied1 = false := by
      cases integ_denied1 with | false => rfl | true => simp at hok
    simp only [hIntegDen2, reduceIte, Bool.false_eq_true] at hok
    -- eager consumption: CHECK 2a arm
    obtain ⟨tc0, htc0Eq, htc0Nil⟩ : ∃ tc0, collections.VecSet.new
        types.OverrideKey.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
        = Result.ok tc0 ∧ tc0.items.val = [] := ⟨_, rfl, rfl⟩
    rw [htc0Eq] at hok; simp only [bind_tc_ok] at hok
    have htc0Len : tc0.items.val.length = 0 := by rw [htc0Nil]; rfl
    obtain ⟨tc1, htc1Eq, htc1Mem, htc1Len⟩ := spec_imp_exists
      (invokeStartLoop6_spec st agent tool spec_taint tc0 tc0 0#usize (by simp)
        (by have := hstLen; omega) (by simp) (by simp))
    rw [htc1Eq] at hok; simp only [bind_tc_ok] at hok
    -- eager consumption: CHECK 2c arm (unconditional)
    obtain ⟨b8, hb8Eq, hb8Iff⟩ := spec_imp_exists (hasFlowOverride_spec st agent tool m.conf_floor)
    rw [hb8Eq] at hok; simp only [bind_tc_ok] at hok
    obtain ⟨tc2, htc2Eq, htc2Mem, htc2Len⟩ :
        ∃ tc2, (if b8 = true then (do
            let ti ← types.ToolId.Insts.CoreCloneClone.clone tool
            collections.VecSet.insert types.OverrideKey.Insts.CoreCloneClone
              types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey tc1 { tool := ti, level := m.conf_floor })
          else (Result.ok tc1 : Result (collections.VecSet types.OverrideKey))) = Result.ok tc2 ∧
        (∀ k, vsMem tc2 k ↔ vsMem tc1 k ∨ (b8 = true ∧ k = { tool := tool, level := m.conf_floor })) ∧
        tc2.items.val.length ≤ tc1.items.val.length + 1 := by
      cases hb8c : b8 with
      | true =>
        simp only [reduceIte, toolId_clone_spec, bind_tc_ok]
        obtain ⟨tc2, htc2Eq, htc2Mem, htc2Len⟩ := spec_imp_exists
          (vecSetInsertLen_spec types.OverrideKey.Insts.CoreCloneClone
            types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey overrideKey_eq_spec tc1
            { tool := tool, level := m.conf_floor } (by have := htc1Len; have := hstLen; have := htc0Len; omega))
        refine ⟨tc2, htc2Eq, fun k => ?_, htc2Len⟩
        rw [htc2Mem k]; simp
      | false =>
        simp only [Bool.false_eq_true, reduceIte]
        exact ⟨tc1, rfl, fun k => by simp, by omega⟩
    rw [htc2Eq] at hok; simp only [bind_tc_ok] at hok
    -- CHECK 2b eager consumption
    obtain ⟨tc3, htc3Eq, htc3Mem, htc3Len⟩ := spec_imp_exists
      (invokeStartLoop7_spec st agent m.conf_floor agent_flights tc2 tc2 0#usize (by simp)
        (by have := htc2Len; have := htc1Len; have := hstLen; have := hflLen; have := hcapFlow; have := htc0Len; omega)
        (by simp) (by simp))
    rw [htc3Eq] at hok; simp only [bind_tc_ok] at hok
    -- override_used write
    obtain ⟨b9, hb9Eq, hb9Iff⟩ := spec_imp_exists
      (vecSetIsEmpty_spec types.OverrideKey.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
        tc3)
    rw [hb9Eq] at hok; simp only [bind_tc_ok] at hok
    obtain ⟨vmOv, hvmOvEq, hvmOvMem, hvmOvNd⟩ :
        ∃ vmOv, (if b9 = true then Result.ok st.override_used else (do
            let ai1 ← types.AgentId.Insts.CoreCloneClone.clone agent
            collections.VecMapKVecSet.extend_into types.AgentId.Insts.CoreCloneClone
              types.AgentId.Insts.CoreCmpPartialEqAgentId types.OverrideKey.Insts.CoreCloneClone
              types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey st.override_used ai1 tc3))
            = Result.ok vmOv ∧
        (∀ k v, vmsMemLast vmOv k v ↔ vmsMemLast st.override_used k v ∨ (k = agent ∧ vsMem tc3 v)) ∧
        (vmNodupKeys st.override_used → vmNodupKeys vmOv) := by
      cases hb9c : b9 with
      | true =>
        simp only [reduceIte]
        refine ⟨st.override_used, rfl, fun k v => ?_, id⟩
        have hEmpty : tc3.items.val = [] := by
          rw [← List.length_eq_zero_iff]; have := hb9Iff.mp hb9c; simpa using this
        simp [vsMem, hEmpty]
      | false =>
        simp only [Bool.false_eq_true, reduceIte, agentId_clone_spec, bind_tc_ok]
        obtain ⟨vmOv, hvmOvEq, hvmOvMem⟩ := spec_imp_exists
          (extendInto_spec types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
            agentId_eq_spec types.OverrideKey.Insts.CoreCloneClone
            types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey overrideKey_eq_spec overrideKey_clone_spec
            st.override_used agent tc3 hcapOvE
            (by intro p hp; have := hcapOvJoint p hp; have := htc3Len; have := htc2Len; have := htc1Len
                have := hstLen; have := hflLen; have := htc0Len; omega)
            (by have := htc3Len; have := htc2Len; have := htc1Len; have := hstLen; have := hflLen
                have := htc0Len; omega))
        obtain ⟨vmOvNd, hvmOvNdEq, hvmOvNdNd⟩ := spec_imp_exists
          (extendInto_nodup types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
            agentId_eq_spec types.OverrideKey.Insts.CoreCloneClone
            types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey overrideKey_eq_spec overrideKey_clone_spec
            st.override_used agent tc3 hcapOvE
            (by intro p hp; have := hcapOvJoint p hp; have := htc3Len; have := htc2Len; have := htc1Len
                have := hstLen; have := hflLen; have := htc0Len; omega)
            (by have := htc3Len; have := htc2Len; have := htc1Len; have := hstLen; have := hflLen
                have := htc0Len; omega))
        have hvmOvEq2 : vmOvNd = vmOv := Result.ok.inj (hvmOvNdEq.symm.trans hvmOvEq)
        exact ⟨vmOv, hvmOvEq, hvmOvMem, hvmOvEq2 ▸ hvmOvNdNd⟩
    rw [hvmOvEq] at hok; simp only [bind_tc_ok] at hok
    -- final writes: invocation_tool, in_flight, invocation_egress, invocation_used
    rw [invocationId_clone_spec, toolId_clone_spec] at hok; simp only [bind_tc_ok] at hok
    obtain ⟨vm1, hvm1Eq, hvm1Mem⟩ := spec_imp_exists
      (vecMapInsert_vmLast_spec types.InvocationId.Insts.CoreCloneClone
        types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
        types.ToolId.Insts.CoreCloneClone st.invocation_tool inv tool hcapInvT)
    rw [hvm1Eq] at hok; simp only [bind_tc_ok] at hok
    rw [agentId_clone_spec] at hok; simp only [bind_tc_ok] at hok
    obtain ⟨vm2, hvm2Eq, hvm2Mem⟩ := spec_imp_exists
      (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
        invocationId_eq_spec invocationId_clone_spec st.in_flight agent inv hcapInflE hcapInflS)
    obtain ⟨vm2nd, hvm2ndEq, hvm2ndNd⟩ := spec_imp_exists
      (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
        types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
        invocationId_eq_spec invocationId_clone_spec st.in_flight agent inv hcapInflE hcapInflS)
    have hvm2Eq2 : vm2nd = vm2 := Result.ok.inj (hvm2ndEq.symm.trans hvm2Eq)
    rw [hvm2Eq] at hok; simp only [bind_tc_ok] at hok
    obtain ⟨vm3, hvm3Eq, hvm3Mem⟩ := spec_imp_exists
      (vecMapInsert_vmLast_spec types.InvocationId.Insts.CoreCloneClone
        types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
        (collections.VecSet.Insts.CoreCloneClone types.EgressKind.Insts.CoreCloneClone)
        st.invocation_egress inv attested_egress hcapEgress)
    rw [hvm3Eq] at hok; simp only [bind_tc_ok] at hok
    obtain ⟨vsUsed, hvsUsedEq, hvsUsedMem, _⟩ := spec_imp_exists
      (vecSetInsertNodup_spec types.InvocationId.Insts.CoreCloneClone
        types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec st.invocation_used inv
        (fun _ => hcapUsed))
    rw [hvsUsedEq] at hok
    simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨hStateEq, _hEventEq⟩ := hok
    -- eager consumption: characterize the FINAL override_used post-image
    have hDen1False : denied1 = false := by
      by_contra hc
      have := hd2Iff.mpr (Or.inl (by simpa using hc)); rw [hDen2] at this; simp at this
    have hDenFalse : denied = false := by
      by_contra hc
      have := hd1Iff.mpr (Or.inl (by simpa using hc)); rw [hDen1False] at this; simp at this
    have hNoDen2a : ¬ ∃ level ∈ spec_taint.items.val, ∃ E ∈ attested_egress.items.val,
        egressDenied (flowModeC bg level E) cgValInv (ovC st agent level tool) (ocC st agent level tool) := by
      intro ⟨level, hlevel, E, hE, hd⟩
      exact absurd (hdIff.mpr (Or.inr ⟨level, hlevel, E, hE, hd⟩)) (by rw [hDenFalse]; simp)
    have hNoDen2b : ¬ ∃ flight_inv ∈ agent_flights.items.val, ∃ t, invToolC st flight_inv = some t ∧
        ∃ E, vmsMemLast st.invocation_egress flight_inv E ∧
          egressDenied (flowModeC bg m.conf_floor E) (Classical.choose (hCg agent t flight_inv))
            (ovC st agent m.conf_floor t) (ocC st agent m.conf_floor t) := by
      intro ⟨fi, hfi, t, ht, E, hE, hd⟩
      exact absurd (hd1Iff.mpr (Or.inr ⟨fi, hfi, t, ht, E, hE, hd⟩)) (by rw [hDen1False]; simp)
    have hNoDen2c : ¬ ∃ E ∈ attested_egress.items.val,
        egressDenied (flowModeC bg m.conf_floor E) cgValInv (ovC st agent m.conf_floor tool)
          (ocC st agent m.conf_floor tool) := by
      intro ⟨E, hE, hd⟩
      exact absurd (hd2Iff.mpr (Or.inr ⟨E, hE, hd⟩)) (by rw [hDen2]; simp)
    have hNoInteg4a : ¬ ∃ level ∈ spec_integ.items.val,
        ¬ (integLeC m.integ_floor level = true ∨ (integLeC m.integ_inspect_floor level = true ∧ cgValInv = true)) := by
      intro ⟨level, hlevel, hd⟩
      exact absurd (hidIff.mpr (Or.inr ⟨level, hlevel, hd⟩)) (by
        have hIntegDenFalse : integ_denied = false := by
          by_contra hc
          have := hid1Iff.mpr (Or.inl (by simpa using hc)); rw [hIntegDen2] at this; simp at this
        rw [hIntegDenFalse]; simp)
    have hNoInteg4b : ¬ ∃ flight_inv ∈ agent_flights.items.val, ∃ t tmeta,
        invToolC st flight_inv = some t ∧ toolMetaC bg t = some tmeta ∧
        ¬ (integLeC tmeta.integ_floor m.output_integ = true
            ∨ (integLeC tmeta.integ_inspect_floor m.output_integ = true
                ∧ Classical.choose (hCg agent t flight_inv) = true)) := by
      intro ⟨fi, hfi, t, tmeta, ht, htm, hd⟩
      exact absurd (hid1Iff.mpr (Or.inr ⟨fi, hfi, t, tmeta, ht, htm, hd⟩)) (by rw [hIntegDen2]; simp)
    -- speculative taint / integrity bridges
    have hbind : ∀ I, vmsMemLast st.in_flight agent I → invToolC st I = some (a.invocation_tool I) := by
      intro I hI
      obtain ⟨t, tm, ht, _⟩ := hR.wfInflight agent I hI
      rw [hR.invTool I t ht]; exact ht
    have hbindMeta : ∀ I, vmsMemLast st.in_flight agent I →
        ∃ tm, toolMetaC bg (a.invocation_tool I) = some tm := by
      intro I hI
      obtain ⟨t, tm, ht, htm⟩ := hR.wfInflight agent I hI
      exact ⟨tm, by rw [hR.invTool I t ht]; exact htm⟩
    have hSpecTaintBridge : ∀ L, Tzimtzum.speculative_taint a agent L ↔ vsMem spec_taint (confC L) := by
      intro L
      rw [Tzimtzum.speculative_taint, hstMem (confC L)]
      apply or_congr
      · exact hR.taint agent L
      · constructor
        · rintro ⟨I, hIfl, hcf⟩
          have hmem := (hR.inflight agent I).mp hIfl
          obtain ⟨tm, htm⟩ := hbindMeta I hmem
          refine ⟨I, hmem, a.invocation_tool I, tm, hbind I hmem, htm, ?_⟩
          have hf := hR.toolFloor (a.invocation_tool I) tm htm
          rw [hf] at hcf
          have hcf' : confA tm.conf_floor = L := hcf
          rw [← hcf', confC_confA]
        · rintro ⟨I, hmem, t, tm, ht, htm, hcf⟩
          refine ⟨I, (hR.inflight agent I).mpr hmem, ?_⟩
          have htI : a.invocation_tool I = t := by
            have h : invToolC st I = some t := ht
            rw [hbind I hmem] at h; exact Option.some.inj h
          rw [htI, hR.toolFloor t tm htm, hcf, confA_confC]
    have hSpecIntegBridge : ∀ L, Tzimtzum.speculative_integ a agent L ↔ vsMem spec_integ (integC L) := by
      intro L
      rw [Tzimtzum.speculative_integ, hsiMem (integC L)]
      apply or_congr
      · exact hR.integ agent L
      · constructor
        · rintro ⟨I, hIfl, hcf⟩
          have hmem := (hR.inflight agent I).mp hIfl
          obtain ⟨tm, htm⟩ := hbindMeta I hmem
          refine ⟨I, hmem, a.invocation_tool I, tm, hbind I hmem, htm, ?_⟩
          have hf := hR.toolOutputInteg (a.invocation_tool I) tm htm
          rw [hf] at hcf
          have hcf' : integA tm.output_integ = L := hcf
          rw [← hcf', integC_integA]
        · rintro ⟨I, hmem, t, tm, ht, htm, hcf⟩
          refine ⟨I, (hR.inflight agent I).mpr hmem, ?_⟩
          have htI : a.invocation_tool I = t := by
            have h : invToolC st I = some t := ht
            rw [hbind I hmem] at h; exact Option.some.inj h
          rw [htI, hR.toolOutputInteg t tm htm, hcf, integA_integC]
    -- override-oracle bridges
    have ovC_iff : ∀ ag L t, ovC st ag L t = true ↔ vmsMemLast st.flow_override ag { tool := t, level := L } :=
      fun ag L t => by
        obtain ⟨b, hb, hbIff⟩ := spec_imp_exists (hasFlowOverride_spec st ag t L)
        rw [ovC_eq st ag L t, Result.ok.injEq] at hb
        rw [hb]; exact hbIff
    have ocC_iff : ∀ ag L t, ocC st ag L t = true ↔ vmsMemLast st.override_used ag { tool := t, level := L } :=
      fun ag L t => by
        obtain ⟨b, hb, hbIff⟩ := spec_imp_exists (overrideConsumed_spec st ag t L)
        rw [ocC_eq st ag L t, Result.ok.injEq] at hb
        rw [hb]; exact hbIff
    -- floor-level bridges (collapse `confC (confA m.conf_floor)` to `m.conf_floor`)
    have hAllowF : ∀ E, a.flow_allows (confA m.conf_floor) E ↔ ceilAdmitsC bg.allow_ceiling m.conf_floor E = true :=
      fun E => by rw [hR.flowAllows, confC_confA]
    have hInspF : ∀ E, a.flow_inspects (confA m.conf_floor) E ↔
        ceilAdmitsC bg.inspect_ceiling m.conf_floor E = true := fun E => by rw [hR.flowInspects, confC_confA]
    have hOvrF : ∀ t, a.flow_override agent t (confA m.conf_floor) ↔
        vmsMemLast st.flow_override agent { tool := t, level := m.conf_floor } := fun t => by
      rw [hR.flowOverride, confC_confA]
    have hUsedF : ∀ t, a.override_used agent t (confA m.conf_floor) ↔
        vmsMemLast st.override_used agent { tool := t, level := m.conf_floor } := fun t => by
      rw [hR.override, confC_confA]
    -- CHECK 2a/2b/2c guards
    have hguard2a : ∀ L E, Tzimtzum.speculative_taint a agent L ∧ a.invocation_egress inv E →
        a.flow_allows L E ∨ (a.flow_inspects L E ∧ a.invocation_gate_passes inv)
        ∨ (a.flow_override agent tool L ∧ ¬ a.override_used agent tool L) := by
      rintro L E ⟨hspec, hegr⟩
      have hL : vsMem spec_taint (confC L) := (hSpecTaintBridge L).mp hspec
      have hE : vsMem attested_egress E := (hEgAgree E).mp hegr
      have hnd : ¬ egressDenied (flowModeC bg (confC L) E) cgValInv (ovC st agent (confC L) tool)
          (ocC st agent (confC L) tool) := fun hc => hNoDen2a ⟨confC L, hL, E, hE, hc⟩
      rcases not_egressDenied_disj _ _ _ _ hnd with hA | ⟨hI, hcgv⟩ | ⟨hovv, hocv⟩
      · exact Or.inl ((hR.flowAllows L E).mpr ((flowModeC_allow_iff bg (confC L) E).mp hA))
      · exact Or.inr (Or.inl ⟨(hR.flowInspects L E).mpr ((flowModeC_inspect_iff bg (confC L) E).mp hI).2,
          hcgAInv.mp hcgv⟩)
      · refine Or.inr (Or.inr ⟨(hR.flowOverride agent tool L).mpr ((ovC_iff agent (confC L) tool).mp hovv), ?_⟩)
        rw [hR.override agent tool L]
        intro hc
        have := (ocC_iff agent (confC L) tool).mpr hc
        rw [hocv] at this; simp at this
    have hguard2b : ∀ I E, a.in_flight agent I ∧ a.invocation_egress I E →
        a.flow_allows (a.tool_conf_floor tool) E
        ∨ (a.flow_inspects (a.tool_conf_floor tool) E ∧ a.invocation_gate_passes I)
        ∨ (a.flow_override agent (a.invocation_tool I) (a.tool_conf_floor tool)
            ∧ ¬ a.override_used agent (a.invocation_tool I) (a.tool_conf_floor tool)) := by
      rintro I E ⟨hIfl, hegr⟩
      have hfloor : a.tool_conf_floor tool = confA m.conf_floor := hR.toolFloor tool m hmeta
      rw [hfloor]
      have hmem := (hR.inflight agent I).mp hIfl
      have hmemFl : I ∈ agent_flights.items.val := (hflMem I).mpr hmem
      have hUsedI : a.invocation_used I := hFlightUsed agent I hIfl
      have hE : vmsMemLast st.invocation_egress I E := (hR.invEgress I hUsedI E).mp hegr
      obtain ⟨t, tm, htTool, _⟩ := hR.wfInflight agent I hmem
      have htI : a.invocation_tool I = t := by
        have h : invToolC st I = some t := htTool
        rw [hbind I hmem] at h; exact Option.some.inj h
      have hnd : ¬ egressDenied (flowModeC bg m.conf_floor E)
          (Classical.choose (hCg agent t I)) (ovC st agent m.conf_floor t) (ocC st agent m.conf_floor t) :=
        fun hc => hNoDen2b ⟨I, hmemFl, t, htTool, E, hE, hc⟩
      rcases not_egressDenied_disj _ _ _ _ hnd with hA | ⟨hIns, hcgv⟩ | ⟨hovv, hocv⟩
      · exact Or.inl ((hAllowF E).mpr ((flowModeC_allow_iff bg m.conf_floor E).mp hA))
      · refine Or.inr (Or.inl ⟨(hInspF E).mpr ((flowModeC_inspect_iff bg m.conf_floor E).mp hIns).2, ?_⟩)
        exact (Classical.choose_spec (hCg agent t I)).2.mp hcgv
      · rw [htI]
        refine Or.inr (Or.inr ⟨(hOvrF t).mpr ((ovC_iff agent m.conf_floor t).mp hovv), ?_⟩)
        rw [hUsedF t]
        intro hc
        have := (ocC_iff agent m.conf_floor t).mpr hc
        rw [hocv] at this; simp at this
    have hguard2c : ∀ E, a.invocation_egress inv E →
        a.flow_allows (a.tool_conf_floor tool) E
        ∨ (a.flow_inspects (a.tool_conf_floor tool) E ∧ a.invocation_gate_passes inv)
        ∨ (a.flow_override agent tool (a.tool_conf_floor tool)
            ∧ ¬ a.override_used agent tool (a.tool_conf_floor tool)) := by
      intro E hegr
      have hfloor : a.tool_conf_floor tool = confA m.conf_floor := hR.toolFloor tool m hmeta
      rw [hfloor]
      have hE : vsMem attested_egress E := (hEgAgree E).mp hegr
      have hnd : ¬ egressDenied (flowModeC bg m.conf_floor E) cgValInv
          (ovC st agent m.conf_floor tool) (ocC st agent m.conf_floor tool) :=
        fun hc => hNoDen2c ⟨E, hE, hc⟩
      rcases not_egressDenied_disj _ _ _ _ hnd with hA | ⟨hIns, hcgv⟩ | ⟨hovv, hocv⟩
      · exact Or.inl ((hAllowF E).mpr ((flowModeC_allow_iff bg m.conf_floor E).mp hA))
      · exact Or.inr (Or.inl ⟨(hInspF E).mpr ((flowModeC_inspect_iff bg m.conf_floor E).mp hIns).2, hcgAInv.mp hcgv⟩)
      · refine Or.inr (Or.inr ⟨(hOvrF tool).mpr ((ovC_iff agent m.conf_floor tool).mp hovv), ?_⟩)
        rw [hUsedF tool]
        intro hc
        have := (ocC_iff agent m.conf_floor tool).mpr hc
        rw [hocv] at this; simp at this
    -- CHECK 4a/4b/4c guards
    have hFloorEq : a.tool_integ_floor tool = integA m.integ_floor := hR.toolIntegFloor tool m hmeta
    have hInspEq : a.tool_integ_inspect_floor tool = integA m.integ_inspect_floor :=
      hR.toolIntegInspectFloor tool m hmeta
    have hguard4a : ∀ L, Tzimtzum.speculative_integ a agent L →
        a.integ_allows L tool ∨ (a.integ_inspects L tool ∧ a.invocation_gate_passes inv) := by
      intro L hspec
      have hL : vsMem spec_integ (integC L) := (hSpecIntegBridge L).mp hspec
      have hnd : integLeC m.integ_floor (integC L) = true
          ∨ (integLeC m.integ_inspect_floor (integC L) = true ∧ cgValInv = true) := by
        by_contra hc; exact hNoInteg4a ⟨integC L, hL, hc⟩
      rcases hnd with hA | ⟨hI, hcgv⟩
      · exact Or.inl (by
          show Tzimtzum.le_integ (a.tool_integ_floor tool) L
          rw [hFloorEq, ← integA_integC L, le_integ_integLeC, integC_integA]; exact hA)
      · exact Or.inr ⟨(by
          show Tzimtzum.le_integ (a.tool_integ_inspect_floor tool) L
          rw [hInspEq, ← integA_integC L, le_integ_integLeC, integC_integA]; exact hI), hcgAInv.mp hcgv⟩
    have hguard4b : ∀ I, a.in_flight agent I →
        a.integ_allows (a.tool_output_integ tool) (a.invocation_tool I)
        ∨ (a.integ_inspects (a.tool_output_integ tool) (a.invocation_tool I)
            ∧ a.invocation_gate_passes I) := by
      intro I hIfl
      have hEmis : a.tool_output_integ tool = integA m.output_integ := hR.toolOutputInteg tool m hmeta
      rw [hEmis]
      have hmem := (hR.inflight agent I).mp hIfl
      have hmemFl : I ∈ agent_flights.items.val := (hflMem I).mpr hmem
      obtain ⟨t, tm, htTool, htmMeta⟩ := hR.wfInflight agent I hmem
      have htI : a.invocation_tool I = t := by
        have h : invToolC st I = some t := htTool
        rw [hbind I hmem] at h; exact Option.some.inj h
      have hFloorEqT : a.tool_integ_floor t = integA tm.integ_floor := hR.toolIntegFloor t tm htmMeta
      have hInspEqT : a.tool_integ_inspect_floor t = integA tm.integ_inspect_floor :=
        hR.toolIntegInspectFloor t tm htmMeta
      rw [htI]
      have hnd : integLeC tm.integ_floor m.output_integ = true
          ∨ (integLeC tm.integ_inspect_floor m.output_integ = true
              ∧ Classical.choose (hCg agent t I) = true) := by
        by_contra hc; exact hNoInteg4b ⟨I, hmemFl, t, tm, htTool, htmMeta, hc⟩
      rcases hnd with hA | ⟨hI', hcgv⟩
      · exact Or.inl (by
          show Tzimtzum.le_integ (a.tool_integ_floor t) (integA m.output_integ)
          rw [hFloorEqT, le_integ_integLeC, integC_integA]; exact hA)
      · exact Or.inr ⟨(by
          show Tzimtzum.le_integ (a.tool_integ_inspect_floor t) (integA m.output_integ)
          rw [hInspEqT, le_integ_integLeC, integC_integA]; exact hI'),
          (Classical.choose_spec (hCg agent t I)).2.mp hcgv⟩
    have hguard4c : a.integ_allows (a.tool_output_integ tool) tool
        ∨ (a.integ_inspects (a.tool_output_integ tool) tool ∧ a.invocation_gate_passes inv) := by
      have hEmis : a.tool_output_integ tool = integA m.output_integ := hR.toolOutputInteg tool m hmeta
      rw [hEmis]
      rcases hid4cA with hA | ⟨hI, hcgv⟩
      · exact Or.inl (by
          show Tzimtzum.le_integ (a.tool_integ_floor tool) (integA m.output_integ)
          rw [hFloorEq, le_integ_integLeC, integC_integA]; exact hA)
      · exact Or.inr ⟨(by
          show Tzimtzum.le_integ (a.tool_integ_inspect_floor tool) (integA m.output_integ)
          rw [hInspEq, le_integ_integLeC, integC_integA]; exact hI), hcgAInv.mp hcgv⟩
    refine ⟨{ a with
        override_used := fun A T L =>
          a.override_used A T L
          ∨ (A = agent ∧ T = tool ∧ a.flow_override agent tool L ∧ Tzimtzum.speculative_taint a agent L)
          ∨ (A = agent ∧ T = tool ∧ L = a.tool_conf_floor tool
              ∧ a.flow_override agent tool (a.tool_conf_floor tool))
          ∨ (A = agent ∧ L = a.tool_conf_floor tool
              ∧ ∃ I, a.in_flight agent I ∧ T = a.invocation_tool I
                 ∧ a.flow_override agent (a.invocation_tool I) (a.tool_conf_floor tool))
        in_flight := fun A I => a.in_flight A I ∨ (A = agent ∧ I = inv)
        invocation_used := fun I => a.invocation_used I ∨ I = inv }, ?_, ?_, ?_⟩
    · -- guard
      exact ⟨hActiveA, hNeRootA, hToolRegA, hinvtool, hFreshFlightA, hFreshUsedA, hNarrowA, hCovA,
        fun C htc => (hR.cap agent C).mpr (hCapOk C ((hR.toolCap tool m C hmeta).mp htc)),
        hguard2a, hguard2b, hguard2c, hauAIff.mp hAuTrue, hguard4a, hguard4b, hguard4c⟩
    · -- next
      simp [Tzimtzum.invoke_start]
    · -- R st' bg a'
      subst hStateEq
      have hFloorTool : a.tool_conf_floor tool = confA m.conf_floor := hR.toolFloor tool m hmeta
      have hOverrideIff : ∀ ag t L,
          (a.override_used ag t L
            ∨ (ag = agent ∧ t = tool ∧ a.flow_override agent tool L ∧ Tzimtzum.speculative_taint a agent L)
            ∨ (ag = agent ∧ t = tool ∧ L = a.tool_conf_floor tool
                ∧ a.flow_override agent tool (a.tool_conf_floor tool))
            ∨ (ag = agent ∧ L = a.tool_conf_floor tool
                ∧ ∃ I, a.in_flight agent I ∧ t = a.invocation_tool I
                   ∧ a.flow_override agent (a.invocation_tool I) (a.tool_conf_floor tool)))
          ↔ vmsMemLast vmOv ag { tool := t, level := confC L } := by
        intro ag t L
        rw [hvmOvMem ag { tool := t, level := confC L }, ← hR.override ag t L]
        apply or_congr_right
        constructor
        · rintro (⟨hag, htT, hflov, hspec⟩ | ⟨hag, htT, hLf, hflov⟩ | ⟨hag, hLf, I, hIfl, htT, hflov⟩)
          · refine ⟨hag, ?_⟩
            rw [htc3Mem]; refine Or.inl ?_
            rw [htc2Mem]; refine Or.inl ?_
            rw [htc1Mem]; refine Or.inr ?_
            refine ⟨confC L, (hSpecTaintBridge L).mp hspec, ?_, hR.flowOverride agent tool L |>.mp hflov⟩
            rw [htT]
          · have hLcf : confC L = m.conf_floor := by rw [hLf, hFloorTool, confC_confA]
            refine ⟨hag, ?_⟩
            rw [htc3Mem]; refine Or.inl ?_
            rw [htc2Mem]; refine Or.inr ⟨?_, by rw [htT, hLcf]⟩
            rw [hFloorTool] at hflov
            exact hb8Iff.mpr ((hOvrF tool).mp hflov)
          · refine ⟨hag, ?_⟩
            rw [htc3Mem]; refine Or.inr ?_
            have hmemFl := (hR.inflight agent I).mp hIfl
            have hmemFlL : I ∈ agent_flights.items.val := (hflMem I).mpr hmemFl
            obtain ⟨t', tm', htTool', _⟩ := hR.wfInflight agent I hmemFl
            have htI : a.invocation_tool I = t' := by
              have h : invToolC st I = some t' := htTool'
              rw [hbind I hmemFl] at h; exact Option.some.inj h
            have hLcf : confC L = m.conf_floor := by rw [hLf, hFloorTool, confC_confA]
            refine ⟨I, hmemFlL, t', htTool', by rw [htT, htI, hLcf], ?_⟩
            rw [htI, hFloorTool] at hflov
            exact (hOvrF t').mp hflov
        · rintro ⟨hag, hC⟩
          rw [htc3Mem, htc2Mem, htc1Mem] at hC
          rcases hC with ((hC0 | ⟨level, hlevel, hk, hov⟩) | hC2c) | hC2b
          · exact absurd hC0 (by simp [vsMem, htc0Nil])
          · rw [types.OverrideKey.mk.injEq] at hk
            obtain ⟨htk, hLk⟩ := hk
            refine Or.inl ⟨hag, htk, ?_, ?_⟩
            · rw [hR.flowOverride agent tool L, hLk]; exact hov
            · exact (hSpecTaintBridge L).mpr (by rw [hLk]; exact hlevel)
          · obtain ⟨hb8true, hk⟩ := hC2c
            rw [types.OverrideKey.mk.injEq] at hk
            obtain ⟨htk, hLk⟩ := hk
            refine Or.inr (Or.inl ⟨hag, htk, ?_, ?_⟩)
            · rw [hFloorTool]; exact (confA_confC L).symm.trans (congrArg confA hLk)
            · rw [hFloorTool]; exact (hOvrF tool).mpr (hb8Iff.mp hb8true)
          · obtain ⟨flight_inv, hfl, t', htTool', hk, hov⟩ := hC2b
            rw [types.OverrideKey.mk.injEq] at hk
            obtain ⟨htk, hLk⟩ := hk
            have hmemFl : vmsMemLast st.in_flight agent flight_inv := (hflMem flight_inv).mp hfl
            have hIfl : a.in_flight agent flight_inv := (hR.inflight agent flight_inv).mpr hmemFl
            have htI : a.invocation_tool flight_inv = t' := by
              have h : invToolC st flight_inv = some t' := htTool'
              rw [hbind flight_inv hmemFl] at h; exact Option.some.inj h
            refine Or.inr (Or.inr ⟨hag, ?_, flight_inv, hIfl, ?_, ?_⟩)
            · rw [hFloorTool]; exact (confA_confC L).symm.trans (congrArg confA hLk)
            · rw [htI]; exact htk
            · rw [htI, hFloorTool, hR.flowOverride, confC_confA]; exact hov
      refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov, hR.active, hR.tool_reg, hR.parent,
        hR.cap, hR.instr, hR.taint, hR.integ, ?_, ?_, hR.budget, ?_, ?_, hR.toolCap, hR.toolEgress,
        hR.toolFloor, hR.toolIntegFloor, hR.toolIntegInspectFloor, hR.toolOutputInteg, hR.toolBounded,
        hR.toolIssuer, hR.trustedIss, hR.instrIssuer, hR.flowAllows, hR.flowInspects, hR.leverFloor,
        hR.leverInspectFloor, hR.flowOverride, ?_, hR.ndParent, hR.ndCap, hR.ndInstr, hR.ndTaint, hR.ndInteg,
        ?_, ?_, hR.ndFlowOverride, hR.ndBudget, ?_⟩
      · -- inflight
        intro ag I
        show (a.in_flight ag I ∨ (ag = agent ∧ I = inv)) ↔ vmsMemLast vm2 ag I
        rw [hvm2Mem ag I]
        exact or_congr (hR.inflight ag I) Iff.rfl
      · -- override
        intro ag t L
        show (a.override_used ag t L ∨ _ ∨ _ ∨ _) ↔ vmsMemLast vmOv ag { tool := t, level := confC L }
        exact hOverrideIff ag t L
      · -- invUsed (global history)
        intro I
        show (a.invocation_used I ∨ I = inv) ↔ vsMem vsUsed I
        rw [hvsUsedMem I]
        exact or_congr (hR.invUsed I) Iff.rfl
      · -- invEgress (used-restricted)
        intro I hUsed E
        show a.invocation_egress I E ↔ vmsMemLast vm3 I E
        by_cases hI : I = inv
        · rw [hI, hEgAgree E]
          unfold vmsMemLast
          rw [hvm3Mem inv]
          simp [vsMem]
        · have hUsed' : a.invocation_used I := hUsed.resolve_right hI
          rw [hR.invEgress I hUsed' E]
          unfold vmsMemLast
          rw [hvm3Mem I, if_neg hI]
      · -- invTool
        intro I t h
        have h' : (vmLastEntry vm1.entries.val I).map Prod.snd = some t := h
        rw [hvm1Mem I] at h'
        by_cases hIinv : I = inv
        · rw [if_pos hIinv] at h'
          simp only [Option.map_some] at h'
          rw [hIinv, hinvtool]
          exact Option.some.inj h'
        · rw [if_neg hIinv] at h'
          exact hR.invTool I t h'
      · -- ndInflight
        exact hvm2Eq2 ▸ hvm2ndNd hR.ndInflight
      · -- ndOverride
        exact hvmOvNd hR.ndOverride
      · -- wfInflight
        intro ag I hmemI
        rw [hvm2Mem ag I] at hmemI
        rcases hmemI with hold | ⟨-, rfl⟩
        · obtain ⟨t, tmeta, ht, htm⟩ := hR.wfInflight ag I hold
          refine ⟨t, tmeta, ?_, htm⟩
          show (vmLastEntry vm1.entries.val I).map Prod.snd = some t
          rw [hvm1Mem I]
          have hIneInv : I ≠ inv := fun hc =>
            hFreshFlightA ag ((hR.inflight ag inv).mpr (hc ▸ hold))
          rw [if_neg hIneInv]
          exact ht
        · refine ⟨tool, m, ?_, hmeta⟩
          show (vmLastEntry vm1.entries.val I).map Prod.snd = some tool
          rw [hvm1Mem I, if_pos rfl]
          rfl
  | Denied =>
    simp only [bind_tc_ok] at hok
    simp only [reduceIte] at hok
    simp at hok

/-! ## `invoke_start` preserves the unified `R`

Two extra hypotheses, local to this action (not part of `R`/`Bridging`):

* `hEgAgree` — the classifier's attested set for the FRESH `inv` literally is `inv`'s abstract
  `invocation_egress`. `RinvocationEgress` is restricted to used invocations (Task 6), so it cannot
  supply this; it is the per-invocation companion to `CgAgree`/`AuAgree`, to be supplied by the
  oracle adapter alongside them when Task 14 assembles `OracleFidelity`.
* `hFlightUsed` — every in-flight invocation is abstractly used (`in_flight_implies_used`, design
  §5.7's strengthening invariant). Needed to route CHECK 2b/4b's in-flight egress/gate reads through
  `R`'s used-only `RinvocationEgress`; carried by Task 14's bundle once the invariant is established. -/


theorem invoke_start_preservesR {A C : Type} (aInst : traits.AuthorizerOracle A)
    (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (authorizer : A) (content_gate : C)
    (a : AbsState) (agent : types.AgentId) (tool : types.ToolId) (inv : types.InvocationId)
    (attested_egress : collections.VecSet types.EgressKind)
    (hR : R st bg a)
    (hCg : CgAgree cgInst content_gate st bg a)
    (hAu : AuAgree aInst authorizer st bg a)
    (hEgAgree : ∀ E, a.invocation_egress inv E ↔ vsMem attested_egress E)
    (hinvtool : a.invocation_tool inv = tool)
    (hFlightUsed : ∀ ag I, a.in_flight ag I → a.invocation_used I)
    (hcapFlow : vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent
      + vmSetLen st.in_flight agent + 1 ≤ Usize.max)
    (hcapInteg : vmSetLen st.integ_levels agent + vmSetLen st.in_flight agent ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJoint : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + (vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent + 1
        + vmSetLen st.in_flight agent) ≤ Usize.max)
    (hcapInvT : st.invocation_tool.entries.val.length < Usize.max)
    (hcapInflE : st.in_flight.entries.val.length < Usize.max)
    (hcapInflS : ∀ p ∈ st.in_flight.entries.val, p.2.items.val.length < Usize.max)
    (hcapUsed : st.invocation_used.items.val.length < Usize.max)
    (hcapEgress : st.invocation_egress.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.invoke_start aInst cgInst st bg authorizer content_gate agent tool inv
      attested_egress = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.invoke_start agent tool inv).guard a ∧
          (Tzimtzum.invoke_start agent tool inv).next a a' ∧ R st' bg a' := by
  simp only [transitions.invoke_start] at hok
  -- Gate: agent active
  obtain ⟨bA, hbAEq, hbAIff⟩ := spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
    types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active agent)
  rw [hbAEq] at hok; simp only [bind_tc_ok] at hok
  have hAgentActive : bA = true := by cases bA with | true => rfl | false => simp at hok
  simp only [hAgentActive, reduceIte] at hok
  -- Gate: agent ≠ root
  obtain ⟨rootVal, hrootEq⟩ : ∃ r, types.AgentId.root = .ok r := by
    cases h : types.AgentId.root with
    | ok r => exact ⟨r, rfl⟩
    | fail e => rw [h] at hok; simp at hok
    | div => rw [h] at hok; simp at hok
  rw [hrootEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨bR, hbREq, hbRIff⟩ : ∃ bb, types.AgentId.Insts.CoreCmpPartialEqAgentId.eq agent rootVal = .ok bb ∧
      (bb = true ↔ agent = rootVal) := ⟨_, agentId_eq_spec agent rootVal, by simp⟩
  rw [hbREq] at hok; simp only [bind_tc_ok] at hok
  have hNotRoot : bR = false := by cases bR with | false => rfl | true => simp at hok
  simp only [hNotRoot, reduceIte, Bool.false_eq_true] at hok
  -- Gate: tool registered
  obtain ⟨bT, hbTEq, hbTIff⟩ := spec_imp_exists (vecSetContains_spec types.ToolId.Insts.CoreCloneClone
    types.ToolId.Insts.CoreCmpPartialEqToolId toolId_eq_spec st.tool_registered tool)
  rw [hbTEq] at hok; simp only [bind_tc_ok] at hok
  have hToolReg : bT = true := by cases bT with | true => rfl | false => simp at hok
  simp only [hToolReg, reduceIte] at hok
  -- Kernel-only check (`InvocationExists`, no abstract counterpart -- `invocation_tool` is a total
  -- background function): treated opaquely, only need it to be `false` on the success path.
  obtain ⟨b3, hb3Eq⟩ : ∃ b3, collections.VecMap.contains_key types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId types.ToolId.Insts.CoreCloneClone
      st.invocation_tool inv = .ok b3 := by
    cases h : collections.VecMap.contains_key types.InvocationId.Insts.CoreCloneClone
        types.InvocationId.Insts.CoreCmpPartialEqInvocationId types.ToolId.Insts.CoreCloneClone
        st.invocation_tool inv with
    | ok b3 => exact ⟨b3, rfl⟩
    | fail e => rw [h] at hok; simp at hok
    | div => rw [h] at hok; simp at hok
  rw [hb3Eq] at hok; simp only [bind_tc_ok] at hok
  have hb3 : b3 = false := by cases b3 with | false => rfl | true => simp at hok
  simp only [hb3, reduceIte, Bool.false_eq_true] at hok
  -- Gate: `∀ AG, ¬ in_flight AG inv` (freshness w.r.t. any agent's flight set)
  obtain ⟨b4, hb4Eq, hb4Iff⟩ := spec_imp_exists
    (anyValueContains_spec types.AgentId.Insts.CoreCloneClone types.AgentId.Insts.CoreCmpPartialEqAgentId
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_eq_spec invocationId_clone_spec st.in_flight inv)
  rw [hb4Eq] at hok; simp only [bind_tc_ok] at hok
  have hb4 : b4 = false := by cases b4 with | false => rfl | true => simp at hok
  simp only [hb4, reduceIte, Bool.false_eq_true] at hok
  have hNotInFlight : ∀ AG, ¬ vmsMemLast st.in_flight AG inv := by
    intro AG hc
    exact absurd (hb4Iff.mpr (vmsMemLast_imp_vmsMem st.in_flight AG inv hc)) (by simp [hb4])
  -- Gate: freshness -- `¬ invocation_used inv`
  obtain ⟨b5, hb5Eq, hb5Iff⟩ := spec_imp_exists (vecSetContains_spec types.InvocationId.Insts.CoreCloneClone
    types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec st.invocation_used inv)
  rw [hb5Eq] at hok; simp only [bind_tc_ok] at hok
  have hb5 : b5 = false := by cases b5 with | false => rfl | true => simp at hok
  simp only [hb5, reduceIte, Bool.false_eq_true] at hok
  have hNotUsed : ¬ vsMem st.invocation_used inv := fun hc => by
    have := hb5Iff.mpr hc; rw [hb5] at this; simp at this
  -- tool metadata
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists (toolMetadata_spec bg tool)
  rw [hoEq] at hok; simp only [bind_tc_ok] at hok
  cases hocase : o with
  | none => rw [hocase] at hok; simp at hok
  | some m =>
  rw [hocase] at hok
  have hmeta : toolMetaC bg tool = some m := by rw [← ho]; exact hocase
  dsimp only [] at hok
  -- narrowing
  obtain ⟨nv, hnvEq, hnvIff⟩ := spec_imp_exists
    (invokeStartLoop0_spec attested_egress m.egress false 0#usize (by simp) (by simp))
  rw [hnvEq] at hok; simp only [bind_tc_ok] at hok
  have hnv : nv = false := by cases nv with | false => rfl | true => simp at hok
  simp only [hnv, reduceIte, Bool.false_eq_true] at hok
  have hNarrow : ∀ E, vsMem attested_egress E → vsMem m.egress E := by
    intro E hE
    by_contra hc
    exact absurd (hnvIff.mpr ⟨E, hE, hc⟩) (by simp [hnv])
  -- coverage split: `b6 = m.egress.is_empty()`
  obtain ⟨b6, hb6Eq, hb6Iff⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.EgressKind.Insts.CoreCloneClone types.EgressKind.Insts.CoreCmpPartialEqEgressKind
      m.egress)
  rw [hb6Eq] at hok; simp only [bind_tc_ok] at hok
  -- Abstract-level guard facts for the shared continuation.
  have hActiveA : a.agent_active agent := (hR.active agent).mpr (hbAIff.mp hAgentActive)
  have hRootEqA : a.root_agent = rootVal := by
    rw [hR.root] at hrootEq; exact Result.ok.inj hrootEq
  have hNeRootA : agent ≠ a.root_agent := fun hc => by
    have hcc := hbRIff.mpr (hc.trans hRootEqA)
    rw [hNotRoot] at hcc; simp at hcc
  have hToolRegA : a.tool_registered tool := (hR.tool_reg tool).mpr (hbTIff.mp hToolReg)
  have hFreshFlightA : ∀ AG, ¬ a.in_flight AG inv :=
    fun AG hc => hNotInFlight AG ((hR.inflight AG inv).mp hc)
  have hFreshUsedA : ¬ a.invocation_used inv := fun hc => hNotUsed ((hR.invUsed inv).mp hc)
  have hEgItemsTool : egItems bg tool = m.egress.items.val := by unfold egItems; rw [hmeta]
  have hNarrowA : ∀ E, a.invocation_egress inv E → a.tool_egress tool E := fun E hegr =>
    (hR.toolEgress tool E).mpr (by rw [hEgItemsTool]; exact hNarrow E ((hEgAgree E).mp hegr))
  cases hb6c : b6 with
  | true =>
    simp only [hb6c, reduceIte] at hok
    -- No declared egress: coverage is vacuous.
    have hCovA : (∃ E, a.tool_egress tool E) → (∃ E, a.invocation_egress inv E) := by
      rintro ⟨E, hE⟩
      rw [hR.toolEgress tool E, hEgItemsTool, hb6Iff.mp hb6c] at hE
      simp at hE
    exact invoke_start_core aInst cgInst st bg authorizer content_gate a agent tool inv
      attested_egress m hR hCg hAu hEgAgree hinvtool hFlightUsed hcapFlow hcapInteg hcapOvE
      hcapOvJoint hcapInvT hcapInflE hcapInflS hcapUsed hcapEgress hmeta hActiveA hNeRootA
      hToolRegA hFreshFlightA hFreshUsedA hNarrowA hCovA st' ev hok
  | false =>
    simp only [hb6c, Bool.false_eq_true, reduceIte] at hok
    -- Egress-bearing tool: the attested set was checked non-empty (coverage), then the
    -- duplicated loops 8-14 run — rewritten to loops 1-7 via the `rfl` equalities.
    obtain ⟨b7, hb7Eq, hb7Iff⟩ := spec_imp_exists
      (vecSetIsEmpty_spec types.EgressKind.Insts.CoreCloneClone
        types.EgressKind.Insts.CoreCmpPartialEqEgressKind attested_egress)
    rw [hb7Eq] at hok; simp only [bind_tc_ok] at hok
    have hb7 : b7 = false := by cases b7 with | false => rfl | true => simp at hok
    simp only [hb7, Bool.false_eq_true, reduceIte] at hok
    simp only [invokeStartLoop8_eq, invokeStartLoop9_eq cgInst, invokeStartLoop10_eq cgInst,
      invokeStartLoop11_eq cgInst, invokeStartLoop12_eq cgInst, invokeStartLoop13_eq,
      invokeStartLoop14_eq] at hok
    have hCovA : (∃ E, a.tool_egress tool E) → (∃ E, a.invocation_egress inv E) := by
      intro _
      have hne : attested_egress.items.val ≠ [] := fun hc => by
        have := hb7Iff.mpr hc; rw [hb7] at this; simp at this
      obtain ⟨E, hE⟩ := List.exists_mem_of_ne_nil _ hne
      exact ⟨E, (hEgAgree E).mpr hE⟩
    exact invoke_start_core aInst cgInst st bg authorizer content_gate a agent tool inv
      attested_egress m hR hCg hAu hEgAgree hinvtool hFlightUsed hcapFlow hcapInteg hcapOvE
      hcapOvJoint hcapInvT hcapInflE hcapInflS hcapUsed hcapEgress hmeta hActiveA hNeRootA
      hToolRegA hFreshFlightA hFreshUsedA hNarrowA hCovA st' ev hok

end ArgusLean.Refinement
