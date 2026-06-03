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
        simp only [List.take_succ, List.getElem?_eq_getElem hlt, Option.toList_some,
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
      ∀ L, vsMem res L ↔ vsMem taint0 L ∨ ∃ inv ∈ flights.items.val, flightFloor vm bg inv L ⦄ := by
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
        simp only [List.take_succ, List.getElem?_eq_getElem hlt, Option.toList_some,
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
      simp only [spec_ok, heq', List.take_length] at hmemL ⊢
      exact hmemL
  · exact ⟨hj, hlen, hmem⟩

/-- `speculative_taint st agent bg`: `agent`'s held taint plus the conf-floor of every in-flight tool. -/
theorem specTaint_spec (st : state.KernelState) (agent : types.AgentId)
    (bg : background.BackgroundTheory)
    (hcap : vmSetLen st.taint_levels agent + vmSetLen st.in_flight agent ≤ Usize.max) :
    state.KernelState.speculative_taint st agent bg ⦃ res =>
      ∀ L, vsMem res L ↔ vmsMemLast st.taint_levels agent L ∨
        ∃ inv, vmsMemLast st.in_flight agent inv ∧ flightFloor st.invocation_tool bg inv L ⦄ := by
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
  obtain ⟨res, hresEq, hresMem⟩ := spec_imp_exists
    (specTaintLoop_spec st.invocation_tool bg flights taint0
      (by rw [ht0Len, hflLen]; exact hcap) taint0 0#usize (by simp) (by simp) (by simp))
  rw [hresEq]; simp only [spec_ok]
  intro L
  rw [hresMem L, ht0Mem L]
  apply or_congr_right
  constructor
  · rintro ⟨inv, hinv, hfl⟩; exact ⟨inv, (hflMem inv).mp hinv, hfl⟩
  · rintro ⟨inv, hinv, hfl⟩; exact ⟨inv, (hflMem inv).mpr hinv, hfl⟩

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
        simp only [List.take_succ, List.getElem?_eq_getElem hlt, Option.toList_some,
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
        simp only [List.take_succ, List.getElem?_eq_getElem hlt, Option.toList_some,
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

end ArgusLean.Refinement
