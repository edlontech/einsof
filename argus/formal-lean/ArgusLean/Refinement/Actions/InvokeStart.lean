import ArgusLean.Refinement.Actions.ReturnUnendorsed
import ArgusLean.Refinement.Actions.InvokeComplete

/-! # Refinement — `invoke_start` (loop specs)

`invoke_start agent tool inv` is the three-check invoke gate: capability (CHECK 1), the graduated flow
gate run in three sweeps — 2a (new tool's egress × existing speculative taint), 2b (new tool's floor ×
existing in-flight tools' egress), 2c (new tool's floor × its own egress) — and the authorizer (CHECK
3). On success it records `inv ↦ tool` in `invocation_tool`, adds `inv` to `agent`'s `in_flight`, and
consumes the overrides that justified passing a DENY across all three flow sweeps.

This file holds the four loop specs the transition threads:
* `invokeStartLoop0_spec` — CHECK 1, the capability fold computing `missing_cap`.
* `specTaintLoop_spec` / `specTaint_spec` — `speculative_taint`: held taint ∪ in-flight tools' floors.
* `invokeStartLoop1_spec` — CHECK 2a, the per-`spec_taint`-level `gate_egress` fold (fixed tool/egress).
* `invokeStartLoop2_spec` — CHECK 2b, the per-in-flight-invocation `gate_egress` fold (≈ the
  `return_unendorsed` inner loop, reusing `invDenied`/`invConsumed` at a fixed level). -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option Aeneas.Deprecated.progressWarning false
set_option maxHeartbeats 4000000

/-! ## CHECK 1 — the capability fold -/

/-- `invoke_start_loop0` ORs `missing_cap` with "`agent` lacks `c`" over the prefix of the tool's
    required caps; the result is `true` iff some required cap is missing (last-match `set_contains`). -/
theorem invokeStartLoop0_spec
    (vm : collections.VecMap types.AgentId (collections.VecSet capability.CapKind))
    (agent : types.AgentId) (caps : collections.VecSet capability.CapKind)
    (mc0 : Bool) (ci : Usize)
    (hci : ci.val ≤ caps.items.val.length)
    (hmc : mc0 = true ↔ ∃ c ∈ caps.items.val.take ci.val, ¬ vmsMemLast vm agent c) :
    transitions.invoke_start_loop0 vm agent caps mc0 ci ⦃ res =>
      res = true ↔ ∃ c ∈ caps.items.val, ¬ vmsMemLast vm agent c ⦄ := by
  unfold transitions.invoke_start_loop0
  apply loop.spec_decr_nat
    (measure := fun p => caps.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ caps.items.val.length ∧
      (p.1 = true ↔ ∃ c ∈ caps.items.val.take p.2.val, ¬ vmsMemLast vm agent c))
  · rintro ⟨mc, ci'⟩ ⟨hile, hmcL⟩
    dsimp only at hile hmcL ⊢
    simp only [transitions.invoke_start_loop0.body, collections.VecSet.len,
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

/-! ## `speculative_taint` — held taint ∪ in-flight tools' floors -/

/-- The conf-floor contribution of in-flight invocation `inv`: its bound tool's metadata floor (empty
    when unbound or no metadata). -/
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
        simp only [bind_tc_ok]
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

/-! ## CHECK 2a — the per-`spec_taint`-level flow fold (fixed tool/egress) -/

/-- `invoke_start_loop1` folds `gate_egress` at the fixed new tool/egress over each speculative-taint
    level: it accumulates the per-`(level, E)` `egressDenied` / `egressConsumed` contributions. -/
theorem invokeStartLoop1_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (agent : types.AgentId) (tool : types.ToolId) (egs : collections.VecSet types.EgressKind)
    (cgVal : Bool) (hcg : cgInst.passes content_gate agent tool st bg = .ok cgVal)
    (spec_taint : collections.VecSet types.ConfLevel)
    (accStart : transitions.GateAccum)
    (hcap : accStart.to_consume.items.val.length + spec_taint.items.val.length ≤ Usize.max)
    (acc : transitions.GateAccum) (li : Usize)
    (hli : li.val ≤ spec_taint.items.val.length)
    (hnd : acc.to_consume.items.val.Nodup)
    (hlen : acc.to_consume.items.val.length ≤ accStart.to_consume.items.val.length + li.val)
    (hden : acc.denied = true ↔ accStart.denied = true ∨
      ∃ level ∈ spec_taint.items.val.take li.val, ∃ E ∈ egs.items.val,
        egressDenied (flowModeC bg level E) cgVal (ovC bg agent level tool) (ocC st agent level tool))
    (hcon : ∀ k, vsMem acc.to_consume k ↔ vsMem accStart.to_consume k ∨
      ∃ level ∈ spec_taint.items.val.take li.val, k = gateConsumeKey tool level ∧
        ∃ E ∈ egs.items.val,
          egressConsumed (flowModeC bg level E) (ovC bg agent level tool) (ocC st agent level tool)) :
    transitions.invoke_start_loop1 cgInst st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.in_flight st.invocation_tool st.tool_registered st.gh_taint_invoked
      st.gh_taint_received st.agent_instruction st.override_used st.agent_budget bg content_gate
      agent tool egs acc spec_taint li ⦃ res =>
      (res.denied = true ↔ accStart.denied = true ∨
        ∃ level ∈ spec_taint.items.val, ∃ E ∈ egs.items.val,
          egressDenied (flowModeC bg level E) cgVal (ovC bg agent level tool) (ocC st agent level tool)) ∧
      (∀ k, vsMem res.to_consume k ↔ vsMem accStart.to_consume k ∨
        ∃ level ∈ spec_taint.items.val, k = gateConsumeKey tool level ∧
          ∃ E ∈ egs.items.val,
            egressConsumed (flowModeC bg level E) (ovC bg agent level tool) (ocC st agent level tool)) ∧
      res.to_consume.items.val.Nodup ∧
      res.to_consume.items.val.length ≤
        accStart.to_consume.items.val.length + spec_taint.items.val.length ⦄ := by
  unfold transitions.invoke_start_loop1
  apply loop.spec_decr_nat
    (measure := fun p => spec_taint.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ spec_taint.items.val.length ∧ p.1.to_consume.items.val.Nodup ∧
      p.1.to_consume.items.val.length ≤ accStart.to_consume.items.val.length + p.2.val ∧
      (p.1.denied = true ↔ accStart.denied = true ∨
        ∃ level ∈ spec_taint.items.val.take p.2.val, ∃ E ∈ egs.items.val,
          egressDenied (flowModeC bg level E) cgVal (ovC bg agent level tool) (ocC st agent level tool)) ∧
      (∀ k, vsMem p.1.to_consume k ↔ vsMem accStart.to_consume k ∨
        ∃ level ∈ spec_taint.items.val.take p.2.val, k = gateConsumeKey tool level ∧
          ∃ E ∈ egs.items.val,
            egressConsumed (flowModeC bg level E) (ovC bg agent level tool) (ocC st agent level tool)))
  · rintro ⟨accL, iL⟩ ⟨hile, hndL, hlenL, hdenL, hconL⟩
    dsimp only at hile hndL hlenL hdenL hconL ⊢
    simp only [transitions.invoke_start_loop1.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : iL.val < spec_taint.items.val.length := by scalar_tac
      step as ⟨level, hlevel⟩
      have hext : ∀ (P : types.ConfLevel → Prop),
          (∃ x ∈ spec_taint.items.val.take (iL.val + 1), P x) ↔
          (∃ x ∈ spec_taint.items.val.take iL.val, P x) ∨ P level := by
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
      have hi2 : ∀ (i2 : Usize), i2.val = iL.val + 1 →
          spec_taint.items.val.take i2.val = spec_taint.items.val.take (iL.val + 1) :=
        fun i2 h2 => by rw [h2]
      have hcapAcc : accL.to_consume.items.val.length < Usize.max := by
        have := hlenL; have := hlt; have := hcap; omega
      have hst : ((⟨st.agent_active, st.agent_parent, st.agent_cap, st.taint_levels,
          st.in_flight, st.invocation_tool, st.tool_registered, st.gh_taint_invoked,
          st.gh_taint_received, st.agent_instruction, st.override_used,
          st.agent_budget⟩ : state.KernelState)) = st := by cases st; rfl
      rw [hst]
      obtain ⟨acc2, hacc2Eq, hDen2, hCon2, hNd2⟩ := spec_imp_exists
        (gateEgress_spec cgInst bg content_gate agent tool st level egs
          cgVal (ovC bg agent level tool) (ocC st agent level tool) hcg
          (ovC_eq bg agent level tool) (ocC_eq st agent level tool)
          (flowModeC bg level) (flowMode_eq bg level) accL hcapAcc hndL)
      rw [hacc2Eq]; simp only [bind_tc_ok]
      step*
      refine ⟨by scalar_tac, hNd2, ?_, ?_, ?_, by scalar_tac⟩
      · have hsub : acc2.to_consume.items.val ⊆
            accL.to_consume.items.val ++ [gateConsumeKey tool level] := by
          intro x hx
          rcases (hCon2 x).mp hx with hxL | ⟨hxk, _⟩
          · exact List.mem_append_left _ hxL
          · exact List.mem_append_right _ (by rw [hxk]; exact List.mem_singleton.mpr rfl)
        have hle := (List.Nodup.subperm hNd2 hsub).length_le
        rw [List.length_append, List.length_singleton] at hle
        rw [show li1.val = iL.val + 1 from li1_post]; omega
      · rw [hi2 _ li1_post, hext (fun lev => ∃ E ∈ egs.items.val,
          egressDenied (flowModeC bg lev E) cgVal (ovC bg agent lev tool) (ocC st agent lev tool)),
          hDen2, hdenL, or_assoc]
      · intro k
        rw [hi2 _ li1_post, hCon2 k, hconL k,
          hext (fun lev => k = gateConsumeKey tool lev ∧ ∃ E ∈ egs.items.val,
            egressConsumed (flowModeC bg lev E) (ovC bg agent lev tool) (ocC st agent lev tool)),
          or_assoc]
    case isFalse h =>
      have heq' : iL.val = spec_taint.items.val.length := by scalar_tac
      rw [heq'] at hlenL
      simp only [spec_ok, heq', List.take_length] at hdenL hconL ⊢
      exact ⟨hdenL, hconL, hndL, hlenL⟩
  · exact ⟨hli, hnd, hlen, hden, hcon⟩

/-! ## CHECK 2b — the per-in-flight-invocation flow fold (at the new tool's floor)

Identical machinery to `return_unendorsed`'s inner loop (`returnUnendInner_spec`): per in-flight
invocation, look up its tool, read its egress, fold `gate_egress` at the fixed `conf_floor`; an unbound
invocation contributes nothing. Reuses `invDenied`/`invConsumed`. -/
theorem invokeStartLoop2_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (agent : types.AgentId) (level : types.ConfLevel)
    (cgOf ovOf ocOf : types.ToolId → Bool)
    (hcg : ∀ t, cgInst.passes content_gate agent t st bg = .ok (cgOf t))
    (hov : ∀ t, background.BackgroundTheory.has_flow_override bg agent t level = .ok (ovOf t))
    (hoc : ∀ t, state.KernelState.override_consumed st agent t level = .ok (ocOf t))
    (invs : collections.VecSet types.InvocationId)
    (accStart : transitions.GateAccum)
    (hcapS : accStart.to_consume.items.val.length + invs.items.val.length ≤ Usize.max)
    (acc : transitions.GateAccum) (fi : Usize)
    (hfi : fi.val ≤ invs.items.val.length)
    (hnd : acc.to_consume.items.val.Nodup)
    (hlen : acc.to_consume.items.val.length ≤ accStart.to_consume.items.val.length + fi.val)
    (hden : acc.denied = true ↔ accStart.denied = true ∨
      ∃ inv ∈ invs.items.val.take fi.val, invDenied st bg level cgOf ovOf ocOf inv)
    (hcon : ∀ k, vsMem acc.to_consume k ↔ vsMem accStart.to_consume k ∨
      ∃ inv ∈ invs.items.val.take fi.val, invConsumed st bg level ovOf ocOf inv k) :
    transitions.invoke_start_loop2 cgInst st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.in_flight st.invocation_tool st.tool_registered st.gh_taint_invoked
      st.gh_taint_received st.agent_instruction st.override_used st.agent_budget bg content_gate
      agent level acc invs fi ⦃ res =>
      (res.denied = true ↔ accStart.denied = true ∨
        ∃ inv ∈ invs.items.val, invDenied st bg level cgOf ovOf ocOf inv) ∧
      (∀ k, vsMem res.to_consume k ↔ vsMem accStart.to_consume k ∨
        ∃ inv ∈ invs.items.val, invConsumed st bg level ovOf ocOf inv k) ∧
      res.to_consume.items.val.Nodup ∧
      res.to_consume.items.val.length ≤
        accStart.to_consume.items.val.length + invs.items.val.length ⦄ := by
  unfold transitions.invoke_start_loop2
  apply loop.spec_decr_nat
    (measure := fun p => invs.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ invs.items.val.length ∧ p.1.to_consume.items.val.Nodup ∧
      p.1.to_consume.items.val.length ≤ accStart.to_consume.items.val.length + p.2.val ∧
      (p.1.denied = true ↔ accStart.denied = true ∨
        ∃ inv ∈ invs.items.val.take p.2.val, invDenied st bg level cgOf ovOf ocOf inv) ∧
      (∀ k, vsMem p.1.to_consume k ↔ vsMem accStart.to_consume k ∨
        ∃ inv ∈ invs.items.val.take p.2.val, invConsumed st bg level ovOf ocOf inv k))
  · rintro ⟨accL, iL⟩ ⟨hile, hndL, hlenL, hdenL, hconL⟩
    dsimp only at hile hndL hlenL hdenL hconL ⊢
    simp only [transitions.invoke_start_loop2.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : iL.val < invs.items.val.length := by scalar_tac
      step as ⟨inv, hinv⟩
      have hext : ∀ (P : types.InvocationId → Prop),
          (∃ x ∈ invs.items.val.take (iL.val + 1), P x) ↔
          (∃ x ∈ invs.items.val.take iL.val, P x) ∨ P inv := by
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
      have hi2 : ∀ (i2 : Usize), i2.val = iL.val + 1 →
          invs.items.val.take i2.val = invs.items.val.take (iL.val + 1) := fun i2 h2 => by rw [h2]
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.ToolId.Insts.CoreCloneClone toolId_clone_spec st.invocation_tool inv)
      rw [hoEq]; simp only [bind_tc_ok]
      have hoInv : o = invToolC st inv := by rw [ho]; rfl
      cases hocase : o with
      | none =>
        rw [hocase] at hoInv
        have hmiss : invToolC st inv = none := hoInv.symm
        have hndd : ¬ invDenied st bg level cgOf ovOf ocOf inv := not_invDenied_missing hmiss
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, hndL, by scalar_tac, ?_, ?_, by scalar_tac⟩
        · rw [hi2 _ fi1_post, hext (invDenied st bg level cgOf ovOf ocOf), hdenL]
          constructor
          · rintro (hA | hB)
            · exact Or.inl hA
            · exact Or.inr (Or.inl hB)
          · rintro (hA | hB | hC)
            · exact Or.inl hA
            · exact Or.inr hB
            · exact absurd hC hndd
        · intro k
          have hncc : ¬ invConsumed st bg level ovOf ocOf inv k := not_invConsumed_missing hmiss
          rw [hi2 _ fi1_post, hext (fun i => invConsumed st bg level ovOf ocOf i k), hconL k]
          constructor
          · rintro (hA | hB)
            · exact Or.inl hA
            · exact Or.inr (Or.inl hB)
          · rintro (hA | hB | hC)
            · exact Or.inl hA
            · exact Or.inr hB
            · exact absurd hC hncc
      | some tool =>
        rw [hocase] at hoInv
        have hsome : invToolC st inv = some tool := hoInv.symm
        simp only [bind_tc_ok]
        obtain ⟨tmeta, hmetaEq, hmeta⟩ := spec_imp_exists (toolMetadata_spec bg tool)
        rw [hmetaEq]; simp only [bind_tc_ok]
        have hcapAcc : accL.to_consume.items.val.length < Usize.max := by
          have := hlenL; have := hlt; have := hcapS; omega
        have hst : ((⟨st.agent_active, st.agent_parent, st.agent_cap, st.taint_levels,
            st.in_flight, st.invocation_tool, st.tool_registered, st.gh_taint_invoked,
            st.gh_taint_received, st.agent_instruction, st.override_used,
            st.agent_budget⟩ : state.KernelState)) = st := by cases st; rfl
        have htail : ∀ (eg : collections.VecSet types.EgressKind),
            eg.items.val = egItems bg tool →
            transitions.gate_egress cgInst bg content_gate agent tool st level eg accL ⦃ acc2 =>
              acc2.to_consume.items.val.Nodup ∧
              acc2.to_consume.items.val.length ≤
                accStart.to_consume.items.val.length + (iL.val + 1) ∧
              (acc2.denied = true ↔ accStart.denied = true ∨
                ∃ inv ∈ invs.items.val.take (iL.val + 1),
                  invDenied st bg level cgOf ovOf ocOf inv) ∧
              (∀ k, vsMem acc2.to_consume k ↔ vsMem accStart.to_consume k ∨
                ∃ inv ∈ invs.items.val.take (iL.val + 1),
                  invConsumed st bg level ovOf ocOf inv k) ⦄ := by
          intro eg hegItems
          obtain ⟨acc2, hacc2Eq, hDenied, hConsume, hNd2⟩ := spec_imp_exists
            (gateEgress_spec cgInst bg content_gate agent tool st level eg
              (cgOf tool) (ovOf tool) (ocOf tool) (hcg tool) (hov tool) (hoc tool)
              (flowModeC bg level) (flowMode_eq bg level) accL hcapAcc hndL)
          rw [hacc2Eq]; simp only [spec_ok]
          have hInvDen : invDenied st bg level cgOf ovOf ocOf inv ↔
              ∃ E ∈ eg.items.val,
                egressDenied (flowModeC bg level E) (cgOf tool) (ovOf tool) (ocOf tool) := by
            rw [invDenied, hegItems]
            constructor
            · rintro ⟨tool', htool', hE⟩; rw [hsome, Option.some_inj] at htool'; subst htool'; exact hE
            · intro hE; exact ⟨tool, hsome, hE⟩
          have hInvCon : ∀ k, invConsumed st bg level ovOf ocOf inv k ↔
              (k = gateConsumeKey tool level ∧ ∃ E ∈ eg.items.val,
                egressConsumed (flowModeC bg level E) (ovOf tool) (ocOf tool)) := by
            intro k; rw [invConsumed, hegItems]
            constructor
            · rintro ⟨tool', htool', hk, hE⟩
              rw [hsome, Option.some_inj] at htool'; subst htool'; exact ⟨hk, hE⟩
            · rintro ⟨hk, hE⟩; exact ⟨tool, hsome, hk, hE⟩
          refine ⟨hNd2, ?_, ?_, ?_⟩
          · have hsub : acc2.to_consume.items.val ⊆
                accL.to_consume.items.val ++ [gateConsumeKey tool level] := by
              intro x hx
              rcases (hConsume x).mp hx with hxL | ⟨hxk, _⟩
              · exact List.mem_append_left _ hxL
              · exact List.mem_append_right _ (by rw [hxk]; exact List.mem_singleton.mpr rfl)
            have hle := (List.Nodup.subperm hNd2 hsub).length_le
            rw [List.length_append, List.length_singleton] at hle
            omega
          · rw [hDenied, hext (invDenied st bg level cgOf ovOf ocOf), hdenL, hInvDen, or_assoc]
          · intro k
            rw [hConsume k, hext (fun i => invConsumed st bg level ovOf ocOf i k), hconL k,
              hInvCon k, or_assoc]
        cases htm : tmeta with
        | none =>
          simp only [collections.VecSet.new, bind_tc_ok]
          rw [hst]
          obtain ⟨acc2, hacc2Eq, hNd2, hlen2, hDen2, hCon2⟩ := spec_imp_exists
            (htail ⟨alloc.vec.Vec.new types.EgressKind⟩ (by simp [egItems, ← hmeta, htm]))
          rw [hacc2Eq]; simp only [bind_tc_ok]; step*
          exact ⟨by scalar_tac, hNd2,
            by rw [show fi1.val = iL.val + 1 from fi1_post]; exact hlen2,
            by rw [hi2 _ fi1_post]; exact hDen2,
            by intro k; rw [hi2 _ fi1_post]; exact hCon2 k, by scalar_tac⟩
        | some m =>
          simp only [bind_tc_ok]
          rw [vecSetClone_spec types.EgressKind.Insts.CoreCloneClone egressKind_clone_spec m.egress]
          simp only [bind_tc_ok]
          rw [hst]
          obtain ⟨acc2, hacc2Eq, hNd2, hlen2, hDen2, hCon2⟩ := spec_imp_exists
            (htail m.egress (by simp [egItems, ← hmeta, htm]))
          rw [hacc2Eq]; simp only [bind_tc_ok]; step*
          exact ⟨by scalar_tac, hNd2,
            by rw [show fi1.val = iL.val + 1 from fi1_post]; exact hlen2,
            by rw [hi2 _ fi1_post]; exact hDen2,
            by intro k; rw [hi2 _ fi1_post]; exact hCon2 k, by scalar_tac⟩
    case isFalse h =>
      have heq' : iL.val = invs.items.val.length := by scalar_tac
      rw [heq'] at hlenL
      simp only [spec_ok, heq', List.take_length] at hdenL hconL ⊢
      exact ⟨hdenL, hconL, hndL, hlenL⟩
  · exact ⟨hfi, hnd, hlen, hden, hcon⟩

/-! ## Gate specs: `contains_key` (b3) and `any_value_contains` (b4) -/

/-- `VecMap.contains_key`'s bool fold: `true` iff some scanned entry is keyed by `key`. The
    two-binder `∃ a v` form matches the `loop.spec_decr_nat` invariant's Prod-split shape. -/
theorem containsKeyLoop_spec {K V : Type} [DecidableEq K]
    (eqK : core.cmp.PartialEq K K) (heq : ∀ a b : K, eqK.eq a b = .ok (decide (a = b)))
    (self : collections.VecMap K V) (key : K) (found : Bool) (i : Usize)
    (hi : i.val ≤ self.entries.val.length)
    (hf : found = true ↔ ∃ a v, (a, v) ∈ self.entries.val.take i.val ∧ a = key) :
    collections.VecMap.contains_key_loop eqK self key found i ⦃ b =>
      b = true ↔ ∃ a v, (a, v) ∈ self.entries.val ∧ a = key ⦄ := by
  unfold collections.VecMap.contains_key_loop
  apply loop.spec_decr_nat
    (measure := fun p => self.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ self.entries.val.length ∧
      (p.1 = true ↔ ∃ a v, (a, v) ∈ self.entries.val.take p.2.val ∧ a = key))
  · rintro ⟨fnd, i'⟩ ⟨hile, hfL⟩
    dsimp only at hile hfL ⊢
    simp only [collections.VecMap.contains_key_loop.body, alloc.vec.Vec.len, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i'.val < self.entries.val.length := by scalar_tac
      step as ⟨t, v0, he⟩
      rw [heq t key]; simp only [bind_tc_ok]
      have hext : (∃ a v, (a, v) ∈ self.entries.val.take (i'.val + 1) ∧ a = key) ↔
          (∃ a v, (a, v) ∈ self.entries.val.take i'.val ∧ a = key) ∨ t = key := by
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨a, v, ha | ha, hPa⟩
          · exact Or.inl ⟨a, v, ha, hPa⟩
          · rw [← he, Prod.mk.injEq] at ha; obtain ⟨rfl, rfl⟩ := ha; exact Or.inr hPa
        · rintro (⟨a, v, ha, hPa⟩ | hPt)
          · exact ⟨a, v, Or.inl ha, hPa⟩
          · exact ⟨t, v0, Or.inr he, hPt⟩
      have hval : (if decide (t = key) then (Result.ok true : Result Bool) else Result.ok fnd) =
          Result.ok (fnd || decide (t = key)) := by by_cases ht : t = key <;> simp [ht]
      rw [hval]; simp only [bind_tc_ok]
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [show i2.val = i'.val + 1 from i2_post, Bool.or_eq_true, decide_eq_true_eq, hfL, hext]
    case isFalse h =>
      have heq' : i'.val = self.entries.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hfL ⊢
      exact hfL
  · exact ⟨hi, hf⟩

/-- `VecMap.contains_key self key`: `true` iff some entry is keyed by `key`. -/
theorem containsKey_spec {K V : Type} [DecidableEq K]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (heq : ∀ a b : K, eqK.eq a b = .ok (decide (a = b))) (cloneV : core.clone.Clone V)
    (self : collections.VecMap K V) (key : K) :
    collections.VecMap.contains_key cloneK eqK cloneV self key ⦃ b =>
      b = true ↔ ∃ a v, (a, v) ∈ self.entries.val ∧ a = key ⦄ := by
  unfold collections.VecMap.contains_key
  exact containsKeyLoop_spec eqK heq self key false 0#usize (by scalar_tac) (by simp)

/-- `VecMapKVecSet.any_value_contains`'s bool fold: `true` iff some scanned entry's set holds
    `elem`. -/
theorem anyValueContainsLoop_spec {K T : Type} [DecidableEq T]
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (heqT : ∀ a b : T, eqT.eq a b = .ok (decide (a = b))) (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (self : collections.VecMap K (collections.VecSet T)) (elem : T) (found : Bool) (i : Usize)
    (hi : i.val ≤ self.entries.val.length)
    (hf : found = true ↔ ∃ a v, (a, v) ∈ self.entries.val.take i.val ∧ elem ∈ v.items.val) :
    collections.VecMapKVecSet.any_value_contains_loop cloneT eqT self elem found i ⦃ b =>
      b = true ↔ ∃ a v, (a, v) ∈ self.entries.val ∧ elem ∈ v.items.val ⦄ := by
  unfold collections.VecMapKVecSet.any_value_contains_loop
  apply loop.spec_decr_nat
    (measure := fun p => self.entries.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ self.entries.val.length ∧
      (p.1 = true ↔ ∃ a v, (a, v) ∈ self.entries.val.take p.2.val ∧ elem ∈ v.items.val))
  · rintro ⟨fnd, i'⟩ ⟨hile, hfL⟩
    dsimp only at hile hfL ⊢
    simp only [collections.VecMapKVecSet.any_value_contains_loop.body, alloc.vec.Vec.len, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : i'.val < self.entries.val.length := by scalar_tac
      step as ⟨k0, vs0, he⟩
      rw [vecSetClone_spec cloneT hcloneT vs0]; simp only [bind_tc_ok]
      obtain ⟨b0, hb0Eq, hb0Iff⟩ := spec_imp_exists (vecSetContains_spec cloneT eqT heqT vs0 elem)
      rw [hb0Eq]; simp only [bind_tc_ok]
      have hext : (∃ a v, (a, v) ∈ self.entries.val.take (i'.val + 1) ∧ elem ∈ v.items.val) ↔
          (∃ a v, (a, v) ∈ self.entries.val.take i'.val ∧ elem ∈ v.items.val) ∨
            elem ∈ vs0.items.val := by
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨a, v, ha | ha, hPa⟩
          · exact Or.inl ⟨a, v, ha, hPa⟩
          · rw [← he, Prod.mk.injEq] at ha; obtain ⟨rfl, rfl⟩ := ha; exact Or.inr hPa
        · rintro (⟨a, v, ha, hPa⟩ | hPt)
          · exact ⟨a, v, Or.inl ha, hPa⟩
          · exact ⟨k0, vs0, Or.inr he, hPt⟩
      have hval : (if b0 then (Result.ok true : Result Bool) else Result.ok fnd) =
          Result.ok (fnd || b0) := by cases b0 <;> simp
      rw [hval]; simp only [bind_tc_ok]
      step*
      refine ⟨by scalar_tac, ?_, by scalar_tac⟩
      rw [show i2.val = i'.val + 1 from i2_post, Bool.or_eq_true, hb0Iff, hfL]
      exact hext.symm
    case isFalse h =>
      have heq' : i'.val = self.entries.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hfL ⊢
      exact hfL
  · exact ⟨hi, hf⟩

/-- `any_value_contains self elem`: `true` iff some entry's set holds `elem`. -/
theorem anyValueContains_spec {K T : Type} [DecidableEq T]
    (cloneK : core.clone.Clone K) (eqK : core.cmp.PartialEq K K)
    (cloneT : core.clone.Clone T) (eqT : core.cmp.PartialEq T T)
    (heqT : ∀ a b : T, eqT.eq a b = .ok (decide (a = b))) (hcloneT : ∀ x : T, cloneT.clone x = .ok x)
    (self : collections.VecMap K (collections.VecSet T)) (elem : T) :
    collections.VecMapKVecSet.any_value_contains cloneK eqK cloneT eqT self elem ⦃ b =>
      b = true ↔ ∃ a v, (a, v) ∈ self.entries.val ∧ elem ∈ v.items.val ⦄ := by
  unfold collections.VecMapKVecSet.any_value_contains
  exact anyValueContainsLoop_spec cloneT eqT heqT hcloneT self elem false 0#usize
    (by scalar_tac) (by simp)

/-! ## `insert_into` last-match write (the `in_flight` insertion)

`insert_into self key elem` adds `elem` to the live (last) `key`-keyed set, framing every other key.
The last-match (`vmsMemLast`) counterpart of `vecMapKVecSetInsertInto_spec`'s ∃-entry view — needed
because `invoke_start`'s `in_flight` reads (`get_set_or_empty`/`speculative_taint`) are all last-match,
so the write must be related the same way. The find loop selects the last key-match (sentinel `len` if
none); the `VecSet.insert`/`Vec.push` then mirrors `extend_into` with a singleton. -/

/-! ## State relation `Rstart`

The oracle-agreement relation for `invoke_start`. The read fields are pinned in the views the kernel
observes: `agent_active`/`tool_registered` via `vsMem`; `agent_cap` via the last-match `vmsMemLast`
(`invoke_start_loop0`'s `set_contains`); `in_flight`/`taint_levels`/`override_used` via the last-match
`vmsMemLast` (the `speculative_taint`/`get_set_or_empty` reads, the `override_consumed` read, and the
`extend_into`/`insert_into` writes). The immutable flow oracles pin as in `Rsent`/`Rretu`
(`tool_egress`→`egItems`, `flow_allows`/`flow_inspects`→`flowModeC`, `flow_override`→override-entry
membership), and `invocation_tool` one-directionally. `tool_conf_floor`/`tool_cap` pin to the tool
metadata. The named root agent is pinned by `AgentId.root = .ok a.root_agent` (the baseline every
tree action carries). The last conjunct is the well-formedness invariant that every in-flight
invocation is bound to a tool (maintained by `invoke_start` itself) — it supplies the bound tool the
abstract 2b guard needs. `content_gate_passes`/`authorizer_allows` are the two opaque oracles
(supplied separately to the refines theorem). -/
def Rstart (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  (types.AgentId.root = .ok a.root_agent) ∧
  (∀ x, a.agent_active x ↔ vsMem st.agent_active x) ∧
  (∀ t, a.tool_registered t ↔ vsMem st.tool_registered t) ∧
  (∀ N C, a.agent_cap N C ↔ vmsMemLast st.agent_cap N C) ∧
  (∀ ag I, a.in_flight ag I ↔ vmsMemLast st.in_flight ag I) ∧
  (∀ ag L, a.taint_levels ag L ↔ vmsMemLast st.taint_levels ag (confC L)) ∧
  (∀ ag t L, a.override_used ag t L ↔
    vmsMemLast st.override_used ag { tool := t, level := confC L }) ∧
  (∀ T E, a.tool_egress T E ↔ E ∈ egItems bg T) ∧
  (∀ L E, a.flow_allows L E ↔ flowModeC bg (confC L) E = background.FlowMode.Allow) ∧
  (∀ L E, a.flow_inspects L E ↔ flowModeC bg (confC L) E = background.FlowMode.Inspect) ∧
  (∀ A T L, a.flow_override A T L ↔
    vsMem bg.flow_overrides { agent := A, tool := T, level := confC L }) ∧
  (∀ I t, invToolC st I = some t → a.invocation_tool I = t) ∧
  (∀ t tmeta, toolMetaC bg t = some tmeta → a.tool_conf_floor t = confA tmeta.conf_floor) ∧
  (∀ t tmeta C, toolMetaC bg t = some tmeta → (a.tool_cap t C ↔ C ∈ tmeta.capabilities.items.val)) ∧
  (∀ ag I, vmsMemLast st.in_flight ag I →
    ∃ t tmeta, invToolC st I = some t ∧ toolMetaC bg t = some tmeta)

/-- The kernel's `speculative_taint` membership: `agent`'s held taint plus the conf-floor of every
    in-flight tool (the `specTaint_spec` characterisation, as a standalone predicate). -/
def specTaintMem (st : state.KernelState) (bg : background.BackgroundTheory) (agent : types.AgentId)
    (level : types.ConfLevel) : Prop :=
  vmsMemLast st.taint_levels agent level ∨
    ∃ inv, vmsMemLast st.in_flight agent inv ∧ flightFloor st.invocation_tool bg inv level

/-! ## Inversion -/

/-- Inversion lemma for a successful `invoke_start` step. Peels the active / ¬root / tool-registered /
    invocation-unbound / not-in-flight gates, reads the tool metadata `m`, runs the capability fold
    (CHECK 1), then the three flow sweeps — 2a (`invoke_start_loop1` over `speculative_taint` at the new
    tool's egress), 2b (`invoke_start_loop2` over `agent`'s in-flight tools at the new tool's floor), 2c
    (`gate_egress` for the new tool at its own floor) — discharges the `denied` and `authorizer` gates,
    and reads off the three writes (`override_used` += the consumed keys, `invocation_tool` += `inv ↦
    tool`, `in_flight` += `(agent, inv)`). The content gate / authorizer are the supplied oracles
    `cgOf` / `auOf`; `has_flow_override` / `override_consumed` are the proven `ovC` / `ocC` reductions. -/
theorem invoke_start_ok_inv {A C : Type} (aInst : traits.AuthorizerOracle A)
    (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (authorizer : A) (content_gate : C)
    (agent : types.AgentId) (tool : types.ToolId) (inv : types.InvocationId)
    (cgOf : types.ToolId → Bool) (auOf : Bool)
    (hcg : ∀ t, cgInst.passes content_gate agent t st bg = .ok (cgOf t))
    (hau : aInst.allows authorizer agent tool st bg = .ok auOf)
    (hcapFlow : vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent
      + vmSetLen st.in_flight agent + 1 ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJoint : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + (vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent
        + vmSetLen st.in_flight agent + 1) ≤ Usize.max)
    (hcapInvT : st.invocation_tool.entries.val.length < Usize.max)
    (hcapInflE : st.in_flight.entries.val.length < Usize.max)
    (hcapInflS : ∀ p ∈ st.in_flight.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.invoke_start aInst cgInst st bg authorizer content_gate agent tool inv
      = .ok (.Ok (st', ev))) :
    vsMem st.agent_active agent ∧
    (∃ ai, types.AgentId.root = .ok ai ∧ agent ≠ ai) ∧
    vsMem st.tool_registered tool ∧
    invToolC st inv = none ∧
    (∀ AG, ¬ vmsMemLast st.in_flight AG inv) ∧
    ∃ m, toolMetaC bg tool = some m ∧
    (∀ c ∈ m.capabilities.items.val, vmsMemLast st.agent_cap agent c) ∧
    (∀ level E, specTaintMem st bg agent level → E ∈ m.egress.items.val →
      ¬ egressDenied (flowModeC bg level E) (cgOf tool)
        (ovC bg agent level tool) (ocC st agent level tool)) ∧
    (∀ inv' tool' E, vmsMemLast st.in_flight agent inv' → invToolC st inv' = some tool' →
      E ∈ egItems bg tool' →
      ¬ egressDenied (flowModeC bg m.conf_floor E) (cgOf tool')
        (ovC bg agent m.conf_floor tool') (ocC st agent m.conf_floor tool')) ∧
    (∀ E ∈ m.egress.items.val,
      ¬ egressDenied (flowModeC bg m.conf_floor E) (cgOf tool)
        (ovC bg agent m.conf_floor tool) (ocC st agent m.conf_floor tool)) ∧
    auOf = true ∧
    st'.agent_active = st.agent_active ∧ st'.agent_parent = st.agent_parent ∧
    st'.agent_cap = st.agent_cap ∧ st'.taint_levels = st.taint_levels ∧
    st'.tool_registered = st.tool_registered ∧ st'.gh_taint_invoked = st.gh_taint_invoked ∧
    st'.gh_taint_received = st.gh_taint_received ∧ st'.agent_instruction = st.agent_instruction ∧
    st'.agent_budget = st.agent_budget ∧
    (∀ j, invToolC st' j = if j = inv then some tool else invToolC st j) ∧
    (∀ k v, vmsMemLast st'.in_flight k v ↔ vmsMemLast st.in_flight k v ∨ (k = agent ∧ v = inv)) ∧
    (∀ ag key, vmsMemLast st'.override_used ag key ↔ vmsMemLast st.override_used ag key ∨
      (ag = agent ∧
        ((∃ level, specTaintMem st bg agent level ∧ key = gateConsumeKey tool level ∧
            ∃ E ∈ m.egress.items.val,
              egressConsumed (flowModeC bg level E) (ovC bg agent level tool)
                (ocC st agent level tool))
         ∨ (∃ inv', vmsMemLast st.in_flight agent inv' ∧
              invConsumed st bg m.conf_floor (ovC bg agent m.conf_floor)
                (ocC st agent m.conf_floor) inv' key)
         ∨ (key = gateConsumeKey tool m.conf_floor ∧
              ∃ E ∈ m.egress.items.val,
                egressConsumed (flowModeC bg m.conf_floor E) (ovC bg agent m.conf_floor tool)
                  (ocC st agent m.conf_floor tool))))) := by
  simp only [transitions.invoke_start] at hok
  -- Gate 1: `agent` active.
  obtain ⟨b, hbEq, hbIff⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active agent)
  rw [hbEq] at hok; simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  have hActive : vsMem st.agent_active agent := hbIff.mp hb
  -- Gate 2: `agent ≠ root`.
  obtain ⟨ai, haiEq⟩ : ∃ r, types.AgentId.root = .ok r := by
    cases h : types.AgentId.root with
    | ok r => exact ⟨r, rfl⟩
    | fail e => rw [h] at hok; simp at hok
    | div => rw [h] at hok; simp at hok
  rw [haiEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨b1, hb1Eq, hb1Iff⟩ :
      ∃ bb, types.AgentId.Insts.CoreCmpPartialEqAgentId.eq agent ai = .ok bb ∧ (bb = true ↔ agent = ai) :=
    ⟨_, agentId_eq_spec agent ai, by simp⟩
  rw [hb1Eq] at hok; simp only [bind_tc_ok] at hok
  have hb1 : b1 = false := by cases b1 with | false => rfl | true => simp at hok
  simp only [hb1, reduceIte, Bool.false_eq_true] at hok
  have hNeRoot : agent ≠ ai := fun hc => by simp [hb1Iff.mpr hc] at hb1
  -- Gate 3: `tool` registered.
  obtain ⟨b2, hb2Eq, hb2Iff⟩ := spec_imp_exists
    (vecSetContains_spec types.ToolId.Insts.CoreCloneClone
      types.ToolId.Insts.CoreCmpPartialEqToolId toolId_eq_spec st.tool_registered tool)
  rw [hb2Eq] at hok; simp only [bind_tc_ok] at hok
  have hb2 : b2 = true := by cases b2 with | true => rfl | false => simp at hok
  simp only [hb2, reduceIte] at hok
  have hToolReg : vsMem st.tool_registered tool := hb2Iff.mp hb2
  -- Gate 4: `inv` unbound.
  obtain ⟨b3, hb3Eq, hb3Iff⟩ := spec_imp_exists
    (containsKey_spec types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      types.ToolId.Insts.CoreCloneClone st.invocation_tool inv)
  rw [hb3Eq] at hok; simp only [bind_tc_ok] at hok
  have hb3 : b3 = false := by cases b3 with | false => rfl | true => simp at hok
  simp only [hb3, reduceIte, Bool.false_eq_true] at hok
  have hUnbound : invToolC st inv = none := by
    have hno : ∀ p ∈ st.invocation_tool.entries.val, p.1 ≠ inv := by
      intro p hp hpinv
      exact (by rw [hb3] at hb3Iff; simpa using hb3Iff : ¬ ∃ a v, (a, v) ∈ st.invocation_tool.entries.val ∧ a = inv)
        ⟨p.1, p.2, by simpa using hp, hpinv⟩
    unfold invToolC; rw [vmLastEntry_eq_none _ inv hno]; rfl
  -- Gate 5: `inv` not in any agent's in-flight set.
  obtain ⟨b4, hb4Eq, hb4Iff⟩ := spec_imp_exists
    (anyValueContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      invocationId_clone_spec st.in_flight inv)
  rw [hb4Eq] at hok; simp only [bind_tc_ok] at hok
  have hb4 : b4 = false := by cases b4 with | false => rfl | true => simp at hok
  simp only [hb4, reduceIte, Bool.false_eq_true] at hok
  have hNotInFlight : ∀ AG, ¬ vmsMemLast st.in_flight AG inv := by
    intro AG ⟨vs, hvs, hvmem⟩
    have : b4 = true := hb4Iff.mpr ⟨AG, vs, vmLastEntry_mem _ _ _ hvs, hvmem⟩
    rw [hb4] at this; simp at this
  -- Read the tool metadata `m`.
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists (toolMetadata_spec bg tool)
  rw [hoEq] at hok; simp only [bind_tc_ok] at hok
  cases hmcase : o with
  | none => rw [hmcase] at hok; simp at hok
  | some m =>
  rw [hmcase] at hok; simp only at hok
  have hmeta : toolMetaC bg tool = some m := by rw [← ho]; exact hmcase
  -- CHECK 1: the capability fold.
  obtain ⟨mc, hmcEq, hmcIff⟩ := spec_imp_exists
    (invokeStartLoop0_spec st.agent_cap agent m.capabilities false 0#usize (by simp) (by simp))
  rw [hmcEq] at hok; simp only [bind_tc_ok] at hok
  have hmcF : mc = false := by cases mc with | false => rfl | true => simp at hok
  simp only [hmcF, reduceIte, Bool.false_eq_true] at hok
  have hCap : ∀ c ∈ m.capabilities.items.val, vmsMemLast st.agent_cap agent c := by
    intro c hc
    by_contra hcon
    have : mc = true := hmcIff.mpr ⟨c, hc, hcon⟩
    rw [hmcF] at this; simp at this
  -- empty override set + `speculative_taint`.
  obtain ⟨vs, hvsEq, hvsNil⟩ : ∃ vs, collections.VecSet.new types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey = Result.ok vs ∧ vs.items.val = [] :=
    ⟨_, rfl, rfl⟩
  rw [hvsEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨spec_taint, hstEq, hstMem, hstLen⟩ := spec_imp_exists
    (specTaint_spec st agent bg (by have := hcapFlow; omega))
  rw [hstEq] at hok; simp only [bind_tc_ok] at hok
  have hspecMem : ∀ L, vsMem spec_taint L ↔ specTaintMem st bg agent L := hstMem
  -- 2a: `invoke_start_loop1`.
  obtain ⟨acc, haccEq, hAccDen, hAccCon, hAccNd, hAccLen⟩ := spec_imp_exists
    (invokeStartLoop1_spec cgInst st bg content_gate agent tool m.egress (cgOf tool) (hcg tool)
      spec_taint { denied := false, to_consume := vs }
      (by show vs.items.val.length + spec_taint.items.val.length ≤ Usize.max
          rw [hvsNil]; simp only [List.length_nil, Nat.zero_add]
          have := hstLen; have := hcapFlow; omega)
      { denied := false, to_consume := vs } 0#usize (by simp)
      (by show vs.items.val.Nodup; rw [hvsNil]; exact List.nodup_nil)
      (by simp) (by simp) (by simp))
  rw [haccEq] at hok; simp only [bind_tc_ok] at hok
  have hAccLen' : acc.to_consume.items.val.length ≤
      vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent := by
    have h := hAccLen; rw [hvsNil] at h; simp only [List.length_nil, Nat.zero_add] at h
    exact le_trans h hstLen
  -- `agent_flights`.
  obtain ⟨agent_flights, hflEq, hflMem, hflLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight agent)
  rw [hflEq] at hok; simp only [bind_tc_ok] at hok
  -- 2b: `invoke_start_loop2`.
  obtain ⟨acc1, hacc1Eq, hAcc1Den, hAcc1Con, hAcc1Nd, hAcc1Len⟩ := spec_imp_exists
    (invokeStartLoop2_spec cgInst st bg content_gate agent m.conf_floor cgOf
      (ovC bg agent m.conf_floor) (ocC st agent m.conf_floor) hcg
      (fun t => ovC_eq bg agent m.conf_floor t) (fun t => ocC_eq st agent m.conf_floor t)
      agent_flights acc
      (by rw [hflLen]; have := hAccLen'; have := hcapFlow; omega)
      acc 0#usize (by simp) hAccNd (by simp) (by simp) (by simp))
  rw [hacc1Eq] at hok; simp only [bind_tc_ok] at hok
  have hAcc1Len' : acc1.to_consume.items.val.length ≤
      vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent + vmSetLen st.in_flight agent := by
    have h := hAcc1Len; rw [hflLen] at h; have := hAccLen'; omega
  -- 2c: `gate_egress`.
  obtain ⟨acc2, hacc2Eq, hAcc2Den, hAcc2Con, hAcc2Nd⟩ := spec_imp_exists
    (gateEgress_spec cgInst bg content_gate agent tool st m.conf_floor m.egress
      (cgOf tool) (ovC bg agent m.conf_floor tool) (ocC st agent m.conf_floor tool)
      (hcg tool) (ovC_eq bg agent m.conf_floor tool) (ocC_eq st agent m.conf_floor tool)
      (flowModeC bg m.conf_floor) (flowMode_eq bg m.conf_floor) acc1
      (by have := hAcc1Len'; have := hcapFlow; omega) hAcc1Nd)
  rw [hacc2Eq] at hok; simp only [bind_tc_ok] at hok
  have hAcc2Len : acc2.to_consume.items.val.length ≤
      vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent
        + vmSetLen st.in_flight agent + 1 := by
    have hsub : acc2.to_consume.items.val ⊆
        acc1.to_consume.items.val ++ [gateConsumeKey tool m.conf_floor] := by
      intro x hx
      rcases (hAcc2Con x).mp hx with hxL | ⟨hxk, _⟩
      · exact List.mem_append_left _ hxL
      · exact List.mem_append_right _ (by rw [hxk]; exact List.mem_singleton.mpr rfl)
    have hle := (List.Nodup.subperm hAcc2Nd hsub).length_le
    rw [List.length_append, List.length_singleton] at hle
    have := hAcc1Len'; omega
  -- `denied` gate.
  have hDenF : acc2.denied = false := by
    cases hd : acc2.denied with | false => rfl | true => simp [hd] at hok
  simp only [hDenF, reduceIte, Bool.false_eq_true] at hok
  -- Authorizer gate.
  rw [hau] at hok; simp only [bind_tc_ok] at hok
  have hauT : auOf = true := by cases auOf with | true => rfl | false => simp at hok
  simp only [hauT, reduceIte] at hok
  -- `is_empty acc2.to_consume`, then the `override_used` write (uniform across branches).
  obtain ⟨b6, hb6Eq, hb6Iff⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey acc2.to_consume)
  rw [hb6Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm, hvmEq, hvmMem⟩ : ∃ vm,
      (if b6 = true then Result.ok st.override_used
       else (do
         let ai1 ← types.AgentId.Insts.CoreCloneClone.clone agent
         collections.VecMapKVecSet.extend_into types.AgentId.Insts.CoreCloneClone
           types.AgentId.Insts.CoreCmpPartialEqAgentId types.OverrideKey.Insts.CoreCloneClone
           types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey st.override_used ai1
           acc2.to_consume)) = Result.ok vm ∧
      (∀ ag key, vmsMemLast vm ag key ↔ vmsMemLast st.override_used ag key ∨
        (ag = agent ∧ vsMem acc2.to_consume key)) := by
    cases hb6 : b6 with
    | true =>
      refine ⟨st.override_used, by rw [if_pos rfl], fun ag key => ?_⟩
      have hempty : acc2.to_consume.items.val = [] := hb6Iff.mp hb6
      simp only [vsMem, hempty, List.not_mem_nil, and_false, or_false]
    | false =>
      have hcapJ : ∀ p ∈ st.override_used.entries.val,
          p.2.items.val.length + acc2.to_consume.items.val.length ≤ Usize.max := by
        intro p hp; have := hcapOvJoint p hp; have := hAcc2Len; omega
      obtain ⟨vm', hvm'Eq, hvm'Mem⟩ := spec_imp_exists
        (extendInto_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.OverrideKey.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
          overrideKey_eq_spec overrideKey_clone_spec st.override_used agent acc2.to_consume
          hcapOvE hcapJ (by have := hAcc2Len; have := hcapFlow; omega))
      exact ⟨vm', by rw [if_neg (by simp), agentId_clone_spec]; simp only [bind_tc_ok]; exact hvm'Eq,
        hvm'Mem⟩
  rw [hvmEq] at hok; simp only [bind_tc_ok] at hok
  -- `invocation_tool` write.
  rw [invocationId_clone_spec, toolId_clone_spec] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm1, hvm1Eq, hvm1⟩ := spec_imp_exists
    (vecMapInsert_vmLast_spec types.InvocationId.Insts.CoreCloneClone
      types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
      types.ToolId.Insts.CoreCloneClone st.invocation_tool inv tool hcapInvT)
  rw [hvm1Eq] at hok; simp only [bind_tc_ok] at hok
  -- `in_flight` write.
  rw [agentId_clone_spec] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm2, hvm2Eq, hvm2Mem⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_eq_spec invocationId_clone_spec st.in_flight agent inv hcapInflE hcapInflS)
  rw [hvm2Eq] at hok; simp only [bind_tc_ok] at hok
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _⟩ := hok
  -- characterise `acc2.to_consume` as the three-way consume disjunction
  have hConChain : ∀ key, vsMem acc2.to_consume key ↔
      (∃ level, specTaintMem st bg agent level ∧ key = gateConsumeKey tool level ∧
        ∃ E ∈ m.egress.items.val,
          egressConsumed (flowModeC bg level E) (ovC bg agent level tool) (ocC st agent level tool))
      ∨ (∃ inv', vmsMemLast st.in_flight agent inv' ∧
          invConsumed st bg m.conf_floor (ovC bg agent m.conf_floor) (ocC st agent m.conf_floor)
            inv' key)
      ∨ (key = gateConsumeKey tool m.conf_floor ∧ ∃ E ∈ m.egress.items.val,
          egressConsumed (flowModeC bg m.conf_floor E) (ovC bg agent m.conf_floor tool)
            (ocC st agent m.conf_floor tool)) := by
    intro key
    rw [hAcc2Con key, hAcc1Con key, hAccCon key]
    have h2a : (∃ level ∈ spec_taint.items.val, key = gateConsumeKey tool level ∧
        ∃ E ∈ m.egress.items.val,
          egressConsumed (flowModeC bg level E) (ovC bg agent level tool) (ocC st agent level tool)) ↔
        (∃ level, specTaintMem st bg agent level ∧ key = gateConsumeKey tool level ∧
          ∃ E ∈ m.egress.items.val,
            egressConsumed (flowModeC bg level E) (ovC bg agent level tool)
              (ocC st agent level tool)) := by
      constructor
      · rintro ⟨level, hlevel, hrest⟩; exact ⟨level, (hspecMem level).mp hlevel, hrest⟩
      · rintro ⟨level, hlevel, hrest⟩; exact ⟨level, (hspecMem level).mpr hlevel, hrest⟩
    have h2b : (∃ inv' ∈ agent_flights.items.val,
          invConsumed st bg m.conf_floor (ovC bg agent m.conf_floor) (ocC st agent m.conf_floor)
            inv' key) ↔
        (∃ inv', vmsMemLast st.in_flight agent inv' ∧
          invConsumed st bg m.conf_floor (ovC bg agent m.conf_floor) (ocC st agent m.conf_floor)
            inv' key) := by
      constructor
      · rintro ⟨inv', hinv', hcon⟩; exact ⟨inv', (hflMem inv').mp hinv', hcon⟩
      · rintro ⟨inv', hinv', hcon⟩; exact ⟨inv', (hflMem inv').mpr hinv', hcon⟩
    have hEmpty : vsMem ({ denied := false, to_consume := vs } : transitions.GateAccum).to_consume key
        ↔ False := by simp [vsMem, hvsNil]
    rw [hEmpty, false_or, h2a, h2b, or_assoc]
  -- the per-sweep no-denial facts
  have hNoDen2a : ∀ level E, specTaintMem st bg agent level → E ∈ m.egress.items.val →
      ¬ egressDenied (flowModeC bg level E) (cgOf tool)
        (ovC bg agent level tool) (ocC st agent level tool) := by
    intro level E hlevel hE hden'
    have : acc.denied = true := by
      rw [hAccDen]; exact Or.inr ⟨level, (hspecMem level).mpr hlevel, E, hE, hden'⟩
    have hd2 : acc2.denied = true := by
      rw [hAcc2Den]; left; rw [hAcc1Den]; left; exact this
    rw [hDenF] at hd2; simp at hd2
  have hNoDen2b : ∀ inv' tool' E, vmsMemLast st.in_flight agent inv' → invToolC st inv' = some tool' →
      E ∈ egItems bg tool' →
      ¬ egressDenied (flowModeC bg m.conf_floor E) (cgOf tool')
        (ovC bg agent m.conf_floor tool') (ocC st agent m.conf_floor tool') := by
    intro inv' tool' E hinv' htool' hE hden'
    have : acc1.denied = true := by
      rw [hAcc1Den]; right
      exact ⟨inv', (hflMem inv').mpr hinv', tool', htool', E, hE, hden'⟩
    have hd2 : acc2.denied = true := by rw [hAcc2Den]; left; exact this
    rw [hDenF] at hd2; simp at hd2
  have hNoDen2c : ∀ E ∈ m.egress.items.val,
      ¬ egressDenied (flowModeC bg m.conf_floor E) (cgOf tool)
        (ovC bg agent m.conf_floor tool) (ocC st agent m.conf_floor tool) := by
    intro E hE hden'
    have hd2 : acc2.denied = true := by rw [hAcc2Den]; right; exact ⟨E, hE, hden'⟩
    rw [hDenF] at hd2; simp at hd2
  subst hStateEq
  refine ⟨hActive, ⟨ai, haiEq, hNeRoot⟩, hToolReg, hUnbound, hNotInFlight, m, hmeta, hCap,
    hNoDen2a, hNoDen2b, hNoDen2c, hauT, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · -- invocation_tool
    intro j
    show invToolC { st with in_flight := vm2, invocation_tool := vm1, override_used := vm } j = _
    unfold invToolC; simp only [hvm1 j]
    by_cases hj : j = inv
    · subst hj; simp
    · simp [hj]
  · -- in_flight
    intro k v
    show vmsMemLast ({ st with in_flight := vm2, invocation_tool := vm1, override_used := vm }).in_flight k v ↔ _
    exact hvm2Mem k v
  · -- override_used
    intro ag key
    show vmsMemLast ({ st with in_flight := vm2, invocation_tool := vm1, override_used := vm }).override_used ag key ↔ _
    rw [hvmMem ag key, hConChain key]

/-! ## Forward simulation -/

/-- Forward simulation: a successful `invoke_start` step is matched by the abstract action, preserving
    `Rstart`. The witness records `inv ↦ tool` in `invocation_tool` (its abstract value was already
    `tool` by the `hinvtool` oracle agreement, so the abstract field is unchanged), adds `(agent, inv)`
    to `in_flight`, and adds the three single-use consumed-override clauses. The three abstract flow
    guards (2a/2b/2c) are established from the concrete `denied = false` via `not_egressDenied_disj`;
    the `override_used` correspondence is the per-sweep `egressConsumed_iff_abstractDenied` collapse.
    `content_gate_passes` / `authorizer_allows` are the two opaque oracles (`hcg`/`hcgA`, `hau`/`hauA`),
    and `hinvtool : a.invocation_tool inv = tool` is the abstract's prediction of the new binding. -/
theorem invoke_start_refines {A C : Type} (aInst : traits.AuthorizerOracle A)
    (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (authorizer : A) (content_gate : C)
    (a : AbsState) (agent : types.AgentId) (tool : types.ToolId) (inv : types.InvocationId)
    (cgOf : types.ToolId → Bool) (auOf : Bool)
    (hcg : ∀ t, cgInst.passes content_gate agent t st bg = .ok (cgOf t))
    (hcgA : ∀ t, cgOf t = true ↔ a.content_gate_passes agent t)
    (hau : aInst.allows authorizer agent tool st bg = .ok auOf)
    (hauA : auOf = true ↔ a.authorizer_allows agent tool)
    (hinvtool : a.invocation_tool inv = tool)
    (hR : Rstart st bg a)
    (hcapFlow : vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent
      + vmSetLen st.in_flight agent + 1 ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJoint : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + (vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent
        + vmSetLen st.in_flight agent + 1) ≤ Usize.max)
    (hcapInvT : st.invocation_tool.entries.val.length < Usize.max)
    (hcapInflE : st.in_flight.entries.val.length < Usize.max)
    (hcapInflS : ∀ p ∈ st.in_flight.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.invoke_start aInst cgInst st bg authorizer content_gate agent tool inv
      = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.invoke_start agent tool inv).guard a ∧
          (Tzimtzum.invoke_start agent tool inv).next a a' ∧ Rstart st' bg a' := by
  obtain ⟨hRroot, hRact, hRtoolReg, hRcap, hRinfl, hRtaint, hRov, hReg, hRallow, hRinsp, hRovr,
    hRinvtool, hRcfloor, hRtoolcap, hRwf⟩ := hR
  obtain ⟨hActive, ⟨ai, haiEq, hNeAi⟩, hToolReg, hUnbound, hNotInFlight, m, hmeta, hCap,
    hNoDen2a, hNoDen2b, hNoDen2c, hauT, hAct, hPar, hCap', hTaint, hToolRegF, hGhInv, hGhRec,
    hAgInstr, hBudget, hInvT, hFl, hOvW⟩ :=
    invoke_start_ok_inv aInst cgInst st bg authorizer content_gate agent tool inv cgOf auOf hcg hau
      hcapFlow hcapOvE hcapOvJoint hcapInvT hcapInflE hcapInflS st' ev hok
  -- root agreement
  have hRootEq : ai = a.root_agent := by rw [hRroot] at haiEq; exact (Result.ok.inj haiEq).symm
  -- the abstract floor of `tool`
  have hfloor : a.tool_conf_floor tool = confA m.conf_floor := hRcfloor tool m hmeta
  have hegEq : egItems bg tool = m.egress.items.val := by simp only [egItems, hmeta]
  -- success ⇒ every in-flight invocation of `agent` is bound to its abstract tool, with metadata
  have hbind : ∀ I, vmsMemLast st.in_flight agent I → invToolC st I = some (a.invocation_tool I) := by
    intro I hI
    obtain ⟨t, tm, ht, _⟩ := hRwf agent I hI
    rw [hRinvtool I t ht]; exact ht
  have hbindMeta : ∀ I, vmsMemLast st.in_flight agent I →
      ∃ tm, toolMetaC bg (a.invocation_tool I) = some tm := by
    intro I hI
    obtain ⟨t, tm, ht, htm⟩ := hRwf agent I hI
    exact ⟨tm, by rw [hRinvtool I t ht]; exact htm⟩
  -- oracle iffs at arbitrary level
  have hovIff : ∀ L t, ovC bg agent L t = true ↔
      vsMem bg.flow_overrides { agent := agent, tool := t, level := L } := by
    intro L t
    obtain ⟨b, hb, hbiff⟩ := spec_imp_exists (hasFlowOverride_spec bg agent t L)
    rw [ovC_eq bg agent L t, Result.ok.injEq] at hb; rw [hb]; exact hbiff
  have hocIff : ∀ L t, ocC st agent L t = true ↔
      vmsMemLast st.override_used agent { tool := t, level := L } := by
    intro L t
    obtain ⟨b, hb, hbiff⟩ := spec_imp_exists (overrideConsumed_spec st agent t L)
    rw [ocC_eq st agent L t, Result.ok.injEq] at hb; rw [hb]; exact hbiff
  -- speculative-taint bridge
  have hSpecBridge : ∀ L, Tzimtzum.speculative_taint a agent L ↔ specTaintMem st bg agent (confC L) := by
    intro L
    rw [Tzimtzum.speculative_taint, specTaintMem]
    apply or_congr
    · exact hRtaint agent L
    · constructor
      · rintro ⟨I, hIfl, hcf⟩
        have hmem : vmsMemLast st.in_flight agent I := (hRinfl agent I).mp hIfl
        obtain ⟨tm, htm⟩ := hbindMeta I hmem
        refine ⟨I, hmem, a.invocation_tool I, tm, hbind I hmem, htm, ?_⟩
        have := hRcfloor (a.invocation_tool I) tm htm
        rw [this] at hcf
        have : confA tm.conf_floor = L := hcf
        rw [← this, confC_confA]
      · rintro ⟨I, hmem, t, tm, ht, htm, hcf⟩
        refine ⟨I, (hRinfl agent I).mpr hmem, ?_⟩
        have htI : a.invocation_tool I = t := by
          have h : invToolC st I = some t := ht
          rw [hbind I hmem] at h; exact Option.some.inj h
        rw [htI, hRcfloor t tm htm, hcf, confA_confC]
  -- per-sweep consume / abstract-denied equivalences
  -- 2a: over `spec_taint` at the new tool
  have hCons2a : ∀ L, specTaintMem st bg agent (confC L) →
      ((∃ E ∈ m.egress.items.val, egressConsumed (flowModeC bg (confC L) E)
          (ovC bg agent (confC L) tool) (ocC st agent (confC L) tool)) ↔
       (a.flow_override agent tool L ∧ ∃ E, a.tool_egress tool E ∧ ¬ a.flow_allows L E ∧
          ¬ (a.flow_inspects L E ∧ a.content_gate_passes agent tool))) := by
    intro L hL
    rw [egressConsumed_iff_abstractDenied (m.egress.items.val) (flowModeC bg (confC L))
      (cgOf tool) (ovC bg agent (confC L) tool) (ocC st agent (confC L) tool)
      (fun E hE => hNoDen2a (confC L) E hL hE)]
    apply and_congr
    · rw [hovIff (confC L) tool, hRovr agent tool L]
    · constructor
      · rintro ⟨E, hE, hne, hni⟩
        refine ⟨E, (hReg tool E).mpr (by rw [hegEq]; exact hE), ?_, ?_⟩
        · rw [hRallow L E]; exact hne
        · rw [hRinsp L E, ← hcgA tool]; exact hni
      · rintro ⟨E, hEg, hna, hni⟩
        have hE : E ∈ m.egress.items.val := by rw [← hegEq]; exact (hReg tool E).mp hEg
        refine ⟨E, hE, ?_, ?_⟩
        · exact fun h => hna ((hRallow L E).mpr h)
        · exact fun ⟨h1, h2⟩ => hni ⟨(hRinsp L E).mpr h1, (hcgA tool).mp h2⟩
  -- abstract-floor flow helpers (the 2b/2c level is `a.tool_conf_floor tool = confA m.conf_floor`)
  have hAllowF : ∀ E, a.flow_allows (confA m.conf_floor) E ↔
      flowModeC bg m.conf_floor E = background.FlowMode.Allow := fun E => by
    rw [hRallow (confA m.conf_floor) E, confC_confA]
  have hInspF : ∀ E, a.flow_inspects (confA m.conf_floor) E ↔
      flowModeC bg m.conf_floor E = background.FlowMode.Inspect := fun E => by
    rw [hRinsp (confA m.conf_floor) E, confC_confA]
  have hovIffF : ∀ t, ovC bg agent m.conf_floor t = true ↔
      a.flow_override agent t (confA m.conf_floor) := fun t => by
    rw [hovIff m.conf_floor t, hRovr agent t (confA m.conf_floor), confC_confA]
  -- 2c: the new tool at its own floor
  have hCons2c : (∃ E ∈ m.egress.items.val, egressConsumed (flowModeC bg m.conf_floor E)
        (ovC bg agent m.conf_floor tool) (ocC st agent m.conf_floor tool)) ↔
      (a.flow_override agent tool (confA m.conf_floor) ∧ ∃ E, a.tool_egress tool E ∧
        ¬ a.flow_allows (confA m.conf_floor) E ∧
        ¬ (a.flow_inspects (confA m.conf_floor) E ∧ a.content_gate_passes agent tool)) := by
    rw [egressConsumed_iff_abstractDenied (m.egress.items.val) (flowModeC bg m.conf_floor)
      (cgOf tool) (ovC bg agent m.conf_floor tool) (ocC st agent m.conf_floor tool) hNoDen2c]
    apply and_congr
    · exact hovIffF tool
    · constructor
      · rintro ⟨E, hE, hne, hni⟩
        refine ⟨E, (hReg tool E).mpr (by rw [hegEq]; exact hE), ?_, ?_⟩
        · rw [hAllowF E]; exact hne
        · rw [hInspF E, ← hcgA tool]; exact hni
      · rintro ⟨E, hEg, hna, hni⟩
        have hE : E ∈ m.egress.items.val := by rw [← hegEq]; exact (hReg tool E).mp hEg
        refine ⟨E, hE, ?_, ?_⟩
        · exact fun h => hna ((hAllowF E).mpr h)
        · exact fun ⟨h1, h2⟩ => hni ⟨(hInspF E).mpr h1, (hcgA tool).mp h2⟩
  -- 2b: a fixed in-flight tool at the new tool's floor
  have hCons2b : ∀ I, vmsMemLast st.in_flight agent I →
      ((∃ E ∈ egItems bg (a.invocation_tool I), egressConsumed (flowModeC bg m.conf_floor E)
          (ovC bg agent m.conf_floor (a.invocation_tool I))
          (ocC st agent m.conf_floor (a.invocation_tool I))) ↔
       (a.flow_override agent (a.invocation_tool I) (confA m.conf_floor) ∧
        ∃ E, a.tool_egress (a.invocation_tool I) E ∧ ¬ a.flow_allows (confA m.conf_floor) E ∧
          ¬ (a.flow_inspects (confA m.conf_floor) E ∧
              a.content_gate_passes agent (a.invocation_tool I)))) := by
    intro I hmem
    rw [egressConsumed_iff_abstractDenied (egItems bg (a.invocation_tool I)) (flowModeC bg m.conf_floor)
      (cgOf (a.invocation_tool I)) (ovC bg agent m.conf_floor (a.invocation_tool I))
      (ocC st agent m.conf_floor (a.invocation_tool I))
      (fun E hE => hNoDen2b I (a.invocation_tool I) E hmem (hbind I hmem) hE)]
    apply and_congr
    · exact hovIffF (a.invocation_tool I)
    · constructor
      · rintro ⟨E, hE, hne, hni⟩
        refine ⟨E, (hReg (a.invocation_tool I) E).mpr hE, ?_, ?_⟩
        · rw [hAllowF E]; exact hne
        · rw [hInspF E, ← hcgA (a.invocation_tool I)]; exact hni
      · rintro ⟨E, hEg, hna, hni⟩
        refine ⟨E, (hReg (a.invocation_tool I) E).mp hEg, ?_, ?_⟩
        · exact fun h => hna ((hAllowF E).mpr h)
        · exact fun ⟨h1, h2⟩ => hni ⟨(hInspF E).mpr h1, (hcgA (a.invocation_tool I)).mp h2⟩
  -- the three abstract flow guards
  have hguard2a : ∀ L E, Tzimtzum.speculative_taint a agent L ∧ a.tool_egress tool E →
      a.flow_allows L E ∨ (a.flow_inspects L E ∧ a.content_gate_passes agent tool)
      ∨ (a.flow_override agent tool L ∧ ¬ a.override_used agent tool L) := by
    rintro L E ⟨hspec, hEg⟩
    have hL : specTaintMem st bg agent (confC L) := (hSpecBridge L).mp hspec
    have hE : E ∈ m.egress.items.val := by rw [← hegEq]; exact (hReg tool E).mp hEg
    rcases not_egressDenied_disj (flowModeC bg (confC L) E) (cgOf tool)
      (ovC bg agent (confC L) tool) (ocC st agent (confC L) tool)
      (hNoDen2a (confC L) E hL hE) with hA | ⟨hI, hcgv⟩ | ⟨hovv, hocv⟩
    · exact Or.inl ((hRallow L E).mpr hA)
    · exact Or.inr (Or.inl ⟨(hRinsp L E).mpr hI, (hcgA tool).mp hcgv⟩)
    · refine Or.inr (Or.inr ⟨(hRovr agent tool L).mpr ((hovIff (confC L) tool).mp hovv), ?_⟩)
      rw [hRov agent tool L]; intro hc
      have := (hocIff (confC L) tool).mpr hc; rw [hocv] at this; simp at this
  have hguard2b : ∀ I E, a.in_flight agent I ∧ a.tool_egress (a.invocation_tool I) E →
      a.flow_allows (a.tool_conf_floor tool) E
      ∨ (a.flow_inspects (a.tool_conf_floor tool) E ∧ a.content_gate_passes agent (a.invocation_tool I))
      ∨ (a.flow_override agent (a.invocation_tool I) (a.tool_conf_floor tool)
          ∧ ¬ a.override_used agent (a.invocation_tool I) (a.tool_conf_floor tool)) := by
    rintro I E ⟨hIfl, hEg⟩
    rw [hfloor]
    have hmem : vmsMemLast st.in_flight agent I := (hRinfl agent I).mp hIfl
    have hEItem : E ∈ egItems bg (a.invocation_tool I) := (hReg (a.invocation_tool I) E).mp hEg
    rcases not_egressDenied_disj (flowModeC bg m.conf_floor E) (cgOf (a.invocation_tool I))
      (ovC bg agent m.conf_floor (a.invocation_tool I)) (ocC st agent m.conf_floor (a.invocation_tool I))
      (hNoDen2b I (a.invocation_tool I) E hmem (hbind I hmem) hEItem) with hA | ⟨hI, hcgv⟩ | ⟨hovv, hocv⟩
    · exact Or.inl ((hAllowF E).mpr hA)
    · exact Or.inr (Or.inl ⟨(hInspF E).mpr hI, (hcgA (a.invocation_tool I)).mp hcgv⟩)
    · refine Or.inr (Or.inr ⟨(hovIffF (a.invocation_tool I)).mp hovv, ?_⟩)
      rw [hRov agent (a.invocation_tool I) (confA m.conf_floor), confC_confA]; intro hc
      have := (hocIff m.conf_floor (a.invocation_tool I)).mpr hc; rw [hocv] at this; simp at this
  have hguard2c : ∀ E, a.tool_egress tool E →
      a.flow_allows (a.tool_conf_floor tool) E
      ∨ (a.flow_inspects (a.tool_conf_floor tool) E ∧ a.content_gate_passes agent tool)
      ∨ (a.flow_override agent tool (a.tool_conf_floor tool)
          ∧ ¬ a.override_used agent tool (a.tool_conf_floor tool)) := by
    intro E hEg
    rw [hfloor]
    have hE : E ∈ m.egress.items.val := by rw [← hegEq]; exact (hReg tool E).mp hEg
    rcases not_egressDenied_disj (flowModeC bg m.conf_floor E) (cgOf tool)
      (ovC bg agent m.conf_floor tool) (ocC st agent m.conf_floor tool)
      (hNoDen2c E hE) with hA | ⟨hI, hcgv⟩ | ⟨hovv, hocv⟩
    · exact Or.inl ((hAllowF E).mpr hA)
    · exact Or.inr (Or.inl ⟨(hInspF E).mpr hI, (hcgA tool).mp hcgv⟩)
    · refine Or.inr (Or.inr ⟨(hovIffF tool).mp hovv, ?_⟩)
      rw [hRov agent tool (confA m.conf_floor), confC_confA]; intro hc
      have := (hocIff m.conf_floor tool).mpr hc; rw [hocv] at this; simp at this
  -- WF transported to `st'`
  have hWf' : ∀ ag I, vmsMemLast st'.in_flight ag I →
      ∃ t tmeta, invToolC st' I = some t ∧ toolMetaC bg t = some tmeta := by
    intro ag I hI
    rcases (hFl ag I).mp hI with hold | ⟨rfl, rfl⟩
    · have hIne : I ≠ inv := fun hc => hNotInFlight ag (hc ▸ hold)
      obtain ⟨t, tm, ht, htm⟩ := hRwf ag I hold
      exact ⟨t, tm, by rw [hInvT I, if_neg hIne]; exact ht, htm⟩
    · exact ⟨tool, m, by rw [hInvT I, if_pos rfl], hmeta⟩
  refine ⟨{ a with
    override_used := fun A T L =>
      a.override_used A T L
      ∨ (A = agent ∧ T = tool ∧ a.flow_override agent tool L ∧ Tzimtzum.speculative_taint a agent L
          ∧ (∃ E, a.tool_egress tool E ∧ ¬ a.flow_allows L E
             ∧ ¬ (a.flow_inspects L E ∧ a.content_gate_passes agent tool)))
      ∨ (A = agent ∧ T = tool ∧ L = a.tool_conf_floor tool
          ∧ a.flow_override agent tool (a.tool_conf_floor tool)
          ∧ (∃ E, a.tool_egress tool E ∧ ¬ a.flow_allows (a.tool_conf_floor tool) E
             ∧ ¬ (a.flow_inspects (a.tool_conf_floor tool) E ∧ a.content_gate_passes agent tool)))
      ∨ (A = agent ∧ L = a.tool_conf_floor tool
          ∧ (∃ I, a.in_flight agent I ∧ T = a.invocation_tool I
             ∧ a.flow_override agent (a.invocation_tool I) (a.tool_conf_floor tool)
             ∧ (∃ E, a.tool_egress (a.invocation_tool I) E
                ∧ ¬ a.flow_allows (a.tool_conf_floor tool) E
                ∧ ¬ (a.flow_inspects (a.tool_conf_floor tool) E
                        ∧ a.content_gate_passes agent (a.invocation_tool I)))))
    in_flight := fun A I => a.in_flight A I ∨ (A = agent ∧ I = inv) }, ?_, ?_, ?_⟩
  · -- guard
    exact ⟨(hRact agent).mpr hActive, hRootEq ▸ hNeAi, (hRtoolReg tool).mpr hToolReg, hinvtool,
      fun AG hc => hNotInFlight AG ((hRinfl AG inv).mp hc),
      fun C htc => (hRcap agent C).mpr (hCap C ((hRtoolcap tool m C hmeta).mp htc)),
      hguard2a, hguard2b, hguard2c, hauA.mp hauT⟩
  · -- next
    simp [Tzimtzum.invoke_start]
  · -- Rstart st' bg a'
    refine ⟨hRroot, fun x => by rw [hAct]; exact hRact x, fun t => by rw [hToolRegF]; exact hRtoolReg t,
      fun N C => by rw [hCap']; exact hRcap N C, fun ag I => ?_, fun ag L => by rw [hTaint]; exact hRtaint ag L,
      ?_, hReg, hRallow, hRinsp, hRovr, ?_, hRcfloor, hRtoolcap, hWf'⟩
    · -- in_flight
      show (a.in_flight ag I ∨ (ag = agent ∧ I = inv)) ↔ vmsMemLast st'.in_flight ag I
      rw [hFl ag I]; exact or_congr (hRinfl ag I) Iff.rfl
    · -- override_used
      intro ag t L
      show (a.override_used ag t L ∨ _ ∨ _ ∨ _) ↔ vmsMemLast st'.override_used ag { tool := t, level := confC L }
      rw [hOvW ag { tool := t, level := confC L }, ← hRov ag t L]
      apply or_congr_right
      · -- the three abstract clauses ↔ the concrete three-way consume at `agent`
        constructor
        · rintro (h2a | h2c | h2b)
          · obtain ⟨hag, htT, hflov, hspec, hegr⟩ := h2a
            subst htT
            refine ⟨hag, Or.inl ⟨confC L, (hSpecBridge L).mp hspec, rfl, ?_⟩⟩
            exact (hCons2a L ((hSpecBridge L).mp hspec)).mpr ⟨hflov, hegr⟩
          · obtain ⟨hag, htT, hLf, hflov, hegr⟩ := h2c
            subst htT
            have hLcf : confC L = m.conf_floor := by rw [hLf, hfloor, confC_confA]
            refine ⟨hag, Or.inr (Or.inr ⟨?_, ?_⟩)⟩
            · simp only [gateConsumeKey, types.OverrideKey.mk.injEq, hLcf]
            · exact hCons2c.mpr ⟨hfloor ▸ hflov, hfloor ▸ hegr⟩
          · obtain ⟨hag, hLf, I, hIfl, htI, hflov, hegr⟩ := h2b
            have hmem : vmsMemLast st.in_flight agent I := (hRinfl agent I).mp hIfl
            have hLcf : confC L = m.conf_floor := by rw [hLf, hfloor, confC_confA]
            refine ⟨hag, Or.inr (Or.inl ⟨I, hmem, a.invocation_tool I, hbind I hmem, ?_, ?_⟩)⟩
            · simp only [gateConsumeKey, types.OverrideKey.mk.injEq, hLcf, htI]
            · exact (hCons2b I hmem).mpr ⟨hfloor ▸ hflov, hfloor ▸ hegr⟩
        · rintro ⟨hagE, hc2a | hc2b | hc2c⟩
          · obtain ⟨level, hlevel, hkey, hegr⟩ := hc2a
            simp only [gateConsumeKey, types.OverrideKey.mk.injEq] at hkey
            obtain ⟨htT, hlev⟩ := hkey
            subst hlev
            exact Or.inl ⟨hagE, htT, ((hCons2a L hlevel).mp hegr).1, (hSpecBridge L).mpr hlevel,
              ((hCons2a L hlevel).mp hegr).2⟩
          · obtain ⟨I, hmem, tool', htool', hkey, hcons⟩ := hc2b
            rw [hbind I hmem, Option.some.injEq] at htool'; subst htool'
            simp only [gateConsumeKey, types.OverrideKey.mk.injEq] at hkey
            obtain ⟨htT, hlev⟩ := hkey
            have hLf : L = a.tool_conf_floor tool := by rw [hfloor, ← hlev, confA_confC]
            refine Or.inr (Or.inr ⟨hagE, hLf, I, (hRinfl agent I).mpr hmem, htT, ?_, ?_⟩)
            · rw [hfloor]; exact ((hCons2b I hmem).mp hcons).1
            · rw [hfloor]; exact ((hCons2b I hmem).mp hcons).2
          · obtain ⟨hkey, hegr⟩ := hc2c
            simp only [gateConsumeKey, types.OverrideKey.mk.injEq] at hkey
            obtain ⟨htT, hlev⟩ := hkey
            have hLf : L = a.tool_conf_floor tool := by rw [hfloor, ← hlev, confA_confC]
            refine Or.inr (Or.inl ⟨hagE, htT, hLf, ?_, ?_⟩)
            · rw [hfloor]; exact (hCons2c.mp hegr).1
            · rw [hfloor]; exact (hCons2c.mp hegr).2
    · -- invocation_tool (one-directional)
      intro I t hI
      rw [hInvT I] at hI
      by_cases hII : I = inv
      · subst hII; rw [if_pos rfl] at hI; rw [hinvtool]; exact Option.some.inj hI
      · rw [if_neg hII] at hI; exact hRinvtool I t hI

end ArgusLean.Refinement

-- Trust-base audit. Beyond the three standard axioms: the `register_tool` `String`/id extractor
-- residuals (via `Collections`). All flow / `FlowMode` / `OverrideKey` facts are PROVED; the three
-- single-use `override_used` clauses are the per-sweep `egressConsumed_iff_abstractDenied` collapse;
-- the speculative-taint correspondence is bridged through `Rstart`'s metadata-carrying well-formedness
-- invariant. `content_gate_passes` / `authorizer_allows` are the opaque oracles (state-/agreement-
-- hypotheses, like every other action), `a.invocation_tool inv = tool` the abstract binding prediction.
-- The root IS named here (the `agent ≠ root` gate), so the extracted `types.AgentId.root` constant
-- appears, carrying its `…String.to_owned` / `AgentId.root._native.decide.ax_1` residuals AND the
-- `sorryAx` placeholder of Aeneas' String-literal model (verify: `#print axioms
-- argus_kernel.types.AgentId.root`). This is exactly the baseline the tree actions
-- (`delegate`/`cascade_revoke`/`revoke`) already carry whenever they gate on the root — it is NOT a
-- `sorry` in this proof, which discharges every goal.
#print axioms ArgusLean.Refinement.invoke_start_ok_inv
#print axioms ArgusLean.Refinement.invoke_start_refines
