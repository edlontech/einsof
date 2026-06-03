import ArgusLean.Refinement.Actions.SentinelElevateTaint

/-! # Refinement — `return_unendorsed`

`return_unendorsed child parent` propagates `child`'s taint set to `parent` on the unendorsed return
path, flow-gated against `parent`'s in-flight tools, consuming the overrides that justified passing a
DENY (the single-use property). Four read gates — `child`'s parent edge is `parent`, both agents
active, `child` has no in-flight invocation — then a **double** loop: for each taint level `L` of
`child` (outer), for each in-flight invocation `I` of `parent` (inner), look up `I`'s tool, read its
egress set, and fold `gate_egress` at level `L`. On success (gate not blocked) it writes three fields:
`taint_levels`/`gh_taint_received` gain `child`'s taint at `parent`, and `override_used` gains the
consumed keys.

This file holds the **concrete loop specs** (`returnUnendInner_spec` per-level, reusing
`SentinelElevateTaint`'s `invDenied`/`invConsumed` per-invocation predicates, and
`returnUnendOuter_spec` over the levels) plus the oracle-agreement relation `Rretu` and the
inversion/refines assembly. The inner loop is the same machinery as `sentinel_elevate_taint`'s, minus
the `missing_binding` tracking (the kernel silently skips an unbound invocation here); the binding
totality the abstract guard needs is carried as a well-formedness invariant in `Rretu`. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option Aeneas.Deprecated.progressWarning false
set_option maxHeartbeats 4000000

/-! ## The in-flight loop (inner, per-level) -/

/-- Generalised spec for `return_unendorsed_loop0_loop0`, the per-level inner loop. Identical in shape
    to `sentinelLoop_spec` minus the `missing_binding` flag: after scanning the prefix `[0, fi)` of
    `invs` the running accumulator's `denied`/`to_consume` are exactly the reference `accStart` extended
    by the per-invocation contributions over that prefix; `to_consume` stays `Nodup` and short of
    `Usize.max`. An unbound invocation (`invToolC = none`) contributes nothing (the kernel returns the
    accumulator unchanged) — consistent with `invDenied`/`invConsumed` being vacuous there. The agent
    is `parent`; the per-tool oracle values `cgOf`/`ovOf`/`ocOf` carry their `= .ok` agreements. -/
theorem returnUnendInner_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (parent : types.AgentId) (level : types.ConfLevel)
    (cgOf ovOf ocOf : types.ToolId → Bool)
    (hcg : ∀ t, cgInst.passes content_gate parent t st bg = .ok (cgOf t))
    (hov : ∀ t, background.BackgroundTheory.has_flow_override bg parent t level = .ok (ovOf t))
    (hoc : ∀ t, state.KernelState.override_consumed st parent t level = .ok (ocOf t))
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
    transitions.return_unendorsed_loop0_loop0 cgInst st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.in_flight st.invocation_tool st.tool_registered st.gh_taint_invoked
      st.gh_taint_received st.agent_instruction st.override_used st.agent_budget bg content_gate
      parent acc invs level fi ⦃ res =>
      (res.denied = true ↔ accStart.denied = true ∨
        ∃ inv ∈ invs.items.val, invDenied st bg level cgOf ovOf ocOf inv) ∧
      (∀ k, vsMem res.to_consume k ↔ vsMem accStart.to_consume k ∨
        ∃ inv ∈ invs.items.val, invConsumed st bg level ovOf ocOf inv k) ∧
      res.to_consume.items.val.Nodup ∧
      res.to_consume.items.val.length ≤
        accStart.to_consume.items.val.length + invs.items.val.length ⦄ := by
  unfold transitions.return_unendorsed_loop0_loop0
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
    simp only [transitions.return_unendorsed_loop0_loop0.body, collections.VecSet.len,
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
            transitions.gate_egress cgInst bg content_gate parent tool st level eg accL ⦃ acc2 =>
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
            (gateEgress_spec cgInst bg content_gate parent tool st level eg
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

/-! ## The outer loop (over child taint levels)

`return_unendorsed_loop0` folds the inner loop over `child_taint`'s levels, threading the accumulator.
The final `denied`/`to_consume` accumulate the per-invocation contributions over **all** `(level, inv)`
pairs (`level ∈ child_taint`, `inv ∈ parent_flights`), with the level-indexed oracles `ovC bg parent
level` / `ocC st parent level`. The capacity bound is the product `|child_taint| * |parent_flights|`
(each level adds at most `|parent_flights|` keys); `cgOf` is level-independent. -/

theorem returnUnendOuter_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (parent : types.AgentId)
    (cgOf : types.ToolId → Bool)
    (hcg : ∀ t, cgInst.passes content_gate parent t st bg = .ok (cgOf t))
    (child_taint : collections.VecSet types.ConfLevel)
    (parent_flights : collections.VecSet types.InvocationId)
    (accStart : transitions.GateAccum)
    (hcap : accStart.to_consume.items.val.length
        + child_taint.items.val.length * parent_flights.items.val.length ≤ Usize.max)
    (acc : transitions.GateAccum) (li : Usize)
    (hli : li.val ≤ child_taint.items.val.length)
    (hnd : acc.to_consume.items.val.Nodup)
    (hlen : acc.to_consume.items.val.length
        ≤ accStart.to_consume.items.val.length + li.val * parent_flights.items.val.length)
    (hden : acc.denied = true ↔ accStart.denied = true ∨
      ∃ level ∈ child_taint.items.val.take li.val, ∃ inv ∈ parent_flights.items.val,
        invDenied st bg level cgOf (ovC bg parent level) (ocC st parent level) inv)
    (hcon : ∀ k, vsMem acc.to_consume k ↔ vsMem accStart.to_consume k ∨
      ∃ level ∈ child_taint.items.val.take li.val, ∃ inv ∈ parent_flights.items.val,
        invConsumed st bg level (ovC bg parent level) (ocC st parent level) inv k) :
    transitions.return_unendorsed_loop0 cgInst st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.in_flight st.invocation_tool st.tool_registered st.gh_taint_invoked
      st.gh_taint_received st.agent_instruction st.override_used st.agent_budget bg content_gate
      parent child_taint acc parent_flights li ⦃ res =>
      (res.denied = true ↔ accStart.denied = true ∨
        ∃ level ∈ child_taint.items.val, ∃ inv ∈ parent_flights.items.val,
          invDenied st bg level cgOf (ovC bg parent level) (ocC st parent level) inv) ∧
      (∀ k, vsMem res.to_consume k ↔ vsMem accStart.to_consume k ∨
        ∃ level ∈ child_taint.items.val, ∃ inv ∈ parent_flights.items.val,
          invConsumed st bg level (ovC bg parent level) (ocC st parent level) inv k) ∧
      res.to_consume.items.val.Nodup ∧
      res.to_consume.items.val.length ≤
        accStart.to_consume.items.val.length
          + child_taint.items.val.length * parent_flights.items.val.length ⦄ := by
  unfold transitions.return_unendorsed_loop0
  apply loop.spec_decr_nat
    (measure := fun p => child_taint.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ child_taint.items.val.length ∧ p.1.to_consume.items.val.Nodup ∧
      p.1.to_consume.items.val.length ≤
        accStart.to_consume.items.val.length + p.2.val * parent_flights.items.val.length ∧
      (p.1.denied = true ↔ accStart.denied = true ∨
        ∃ level ∈ child_taint.items.val.take p.2.val, ∃ inv ∈ parent_flights.items.val,
          invDenied st bg level cgOf (ovC bg parent level) (ocC st parent level) inv) ∧
      (∀ k, vsMem p.1.to_consume k ↔ vsMem accStart.to_consume k ∨
        ∃ level ∈ child_taint.items.val.take p.2.val, ∃ inv ∈ parent_flights.items.val,
          invConsumed st bg level (ovC bg parent level) (ocC st parent level) inv k))
  · rintro ⟨accL, iL⟩ ⟨hile, hndL, hlenL, hdenL, hconL⟩
    dsimp only at hile hndL hlenL hdenL hconL ⊢
    simp only [transitions.return_unendorsed_loop0.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : iL.val < child_taint.items.val.length := by scalar_tac
      step as ⟨level, hlevel⟩
      have hext : ∀ (P : types.ConfLevel → Prop),
          (∃ x ∈ child_taint.items.val.take (iL.val + 1), P x) ↔
          (∃ x ∈ child_taint.items.val.take iL.val, P x) ∨ P level := by
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
          child_taint.items.val.take i2.val = child_taint.items.val.take (iL.val + 1) :=
        fun i2 h2 => by rw [h2]
      -- the inner loop at this level, started from the current outer accumulator
      have hcapInner : accL.to_consume.items.val.length + parent_flights.items.val.length ≤
          Usize.max := by
        have hmul : (iL.val + 1) * parent_flights.items.val.length ≤
            child_taint.items.val.length * parent_flights.items.val.length :=
          Nat.mul_le_mul_right parent_flights.items.val.length (by omega)
        have hexp : (iL.val + 1) * parent_flights.items.val.length =
            iL.val * parent_flights.items.val.length + parent_flights.items.val.length := by ring
        omega
      obtain ⟨acc1, hacc1Eq, hDen1, hCon1, hNd1, hLen1⟩ := spec_imp_exists
        (returnUnendInner_spec cgInst st bg content_gate parent level cgOf
          (ovC bg parent level) (ocC st parent level) hcg
          (fun t => ovC_eq bg parent level t) (fun t => ocC_eq st parent level t)
          parent_flights accL hcapInner accL 0#usize (by simp) hndL (by simp) (by simp) (by simp))
      rw [hacc1Eq]; simp only [bind_tc_ok]
      step*
      refine ⟨by scalar_tac, hNd1, ?_, ?_, ?_, by scalar_tac⟩
      · -- length: accL + pf ≤ accStart + (iL+1)*pf
        rw [show li1.val = iL.val + 1 from li1_post]
        have hexp : (iL.val + 1) * parent_flights.items.val.length =
            iL.val * parent_flights.items.val.length + parent_flights.items.val.length := by ring
        omega
      · -- denied
        rw [hi2 _ li1_post, hext (fun lev => ∃ inv ∈ parent_flights.items.val,
          invDenied st bg lev cgOf (ovC bg parent lev) (ocC st parent lev) inv), hDen1, hdenL,
          or_assoc]
      · -- consume
        intro k
        rw [hi2 _ li1_post, hCon1 k, hconL k,
          hext (fun lev => ∃ inv ∈ parent_flights.items.val,
            invConsumed st bg lev (ovC bg parent lev) (ocC st parent lev) inv k), or_assoc]
    case isFalse h =>
      have heq' : iL.val = child_taint.items.val.length := by scalar_tac
      rw [heq'] at hlenL
      simp only [spec_ok, heq', List.take_length] at hdenL hconL ⊢
      exact ⟨hdenL, hconL, hndL, hlenL⟩
  · exact ⟨hli, hnd, hlen, hden, hcon⟩

/-! ## Length-aware `get_set_or_empty`

`get_set_or_empty self key` returns the live (last) `key`-keyed set; its membership is `vmsMemLast`
and its length the closed form `vmSetLen` (`0` when the key is absent). The length-aware refinement of
`getSetOrEmpty_spec`, used to phrase the loop / `extend_into` capacity bounds over `st`. (Generalises
`getSetOrEmptyInFlight_spec` to any `K`/`T`; used for both `child_taint` and `parent_flights`.) -/

/-! ## State relation `Rretu`

The oracle-agreement relation for `return_unendorsed`. All four mutable fields it touches live in the
**last-match** `vmsMemLast` world: `in_flight` (the `set_nonempty` child gate + the `get_set_or_empty`
parent-flights read), `taint_levels` (the `get_set_or_empty` child read + the `extend_into` parent
write), `gh_taint_received` (the `extend_into` parent write), `override_used` (the `override_consumed`
read + the `extend_into` parent write). `agent_parent` is the get-style edge read (`vmLastEntry`, like
the tree actions); `agent_active` is `vsMem`. The immutable flow oracles pin as in `Rsent`
(`tool_egress`→`egItems`, `flow_allows`/`flow_inspects`→`flowModeC`, `flow_override`→override-entry
membership, `invocation_tool` one-directional). `content_gate_passes` is the one opaque oracle. The
last conjunct is the **well-formedness** invariant that every in-flight invocation is bound to a tool
(maintained by `invoke_start`) — it rules out the kernel's silent skip of an unbound invocation, which
the abstract guard (quantifying over the total `invocation_tool`) cannot see. -/
def Rretu (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  (∀ x, a.agent_active x ↔ vsMem st.agent_active x) ∧
  (∀ C P, a.agent_parent C P ↔ vmLastEntry st.agent_parent.entries.val C = some (C, P)) ∧
  (∀ ag I, a.in_flight ag I ↔ vmsMemLast st.in_flight ag I) ∧
  (∀ ag L, a.taint_levels ag L ↔ vmsMemLast st.taint_levels ag (confC L)) ∧
  (∀ ag L, a.gh_taint_received ag L ↔ vmsMemLast st.gh_taint_received ag (confC L)) ∧
  (∀ ag t L, a.override_used ag t L ↔
    vmsMemLast st.override_used ag { tool := t, level := confC L }) ∧
  (∀ T E, a.tool_egress T E ↔ E ∈ egItems bg T) ∧
  (∀ L E, a.flow_allows L E ↔ flowModeC bg (confC L) E = background.FlowMode.Allow) ∧
  (∀ L E, a.flow_inspects L E ↔ flowModeC bg (confC L) E = background.FlowMode.Inspect) ∧
  (∀ A T L, a.flow_override A T L ↔
    vsMem bg.flow_overrides { agent := A, tool := T, level := confC L }) ∧
  (∀ I t, invToolC st I = some t → a.invocation_tool I = t) ∧
  (∀ ag I, vmsMemLast st.in_flight ag I → invToolC st I ≠ none)

/-! ## Inversion -/

/-- Inversion lemma for a successful `return_unendorsed` step. Peels the parent-edge gate (`VecMap.get`
    + `Option.ne`, like `return_endorsed`/`grant_capability`), the two active gates, the `set_nonempty`
    child-in-flight gate, reads `child`'s taint (`child_taint`) and `parent`'s in-flight invocations
    (`parent_flights`) via `get_set_or_empty`, runs the double loop (`returnUnendOuter_spec`), discharges
    the `denied` error gate, and reads off the three writes uniformly across the `is_empty child_taint`
    / `is_empty to_consume` branches (`extend_into` of `child_taint` into `taint_levels`/
    `gh_taint_received`; of `to_consume` into `override_used`). The content gate is the supplied oracle
    `cgOf`; `has_flow_override`/`override_consumed` are the proven `ovC`/`ocC` reductions. -/
theorem return_unendorsed_ok_inv {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (child parent : types.AgentId)
    (cgOf : types.ToolId → Bool)
    (hcg : ∀ t, cgInst.passes content_gate parent t st bg = .ok (cgOf t))
    (hcapLoop : vmSetLen st.taint_levels child * vmSetLen st.in_flight parent ≤ Usize.max)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintJoint : ∀ p ∈ st.taint_levels.entries.val,
      p.2.items.val.length + vmSetLen st.taint_levels child ≤ Usize.max)
    (hcapTaintChild : vmSetLen st.taint_levels child ≤ Usize.max)
    (hcapGhrE : st.gh_taint_received.entries.val.length < Usize.max)
    (hcapGhrJoint : ∀ p ∈ st.gh_taint_received.entries.val,
      p.2.items.val.length + vmSetLen st.taint_levels child ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJoint : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + vmSetLen st.taint_levels child * vmSetLen st.in_flight parent ≤ Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.return_unendorsed cgInst st bg content_gate child parent
      = .ok (.Ok (st', ev))) :
    vmLastEntry st.agent_parent.entries.val child = some (child, parent) ∧
    vsMem st.agent_active child ∧
    vsMem st.agent_active parent ∧
    (∀ inv, ¬ vmsMemLast st.in_flight child inv) ∧
    (∀ level inv tool E, vmsMemLast st.taint_levels child level →
      vmsMemLast st.in_flight parent inv → invToolC st inv = some tool → E ∈ egItems bg tool →
      ¬ egressDenied (flowModeC bg level E) (cgOf tool)
        (ovC bg parent level tool) (ocC st parent level tool)) ∧
    st'.agent_active = st.agent_active ∧ st'.agent_parent = st.agent_parent ∧
    st'.agent_cap = st.agent_cap ∧ st'.in_flight = st.in_flight ∧
    st'.invocation_tool = st.invocation_tool ∧ st'.tool_registered = st.tool_registered ∧
    st'.gh_taint_invoked = st.gh_taint_invoked ∧ st'.agent_instruction = st.agent_instruction ∧
    st'.agent_budget = st.agent_budget ∧
    (∀ ag v, vmsMemLast st'.taint_levels ag v ↔
      vmsMemLast st.taint_levels ag v ∨ (ag = parent ∧ vmsMemLast st.taint_levels child v)) ∧
    (∀ ag v, vmsMemLast st'.gh_taint_received ag v ↔
      vmsMemLast st.gh_taint_received ag v ∨ (ag = parent ∧ vmsMemLast st.taint_levels child v)) ∧
    (∀ ag key, vmsMemLast st'.override_used ag key ↔ vmsMemLast st.override_used ag key ∨
      (ag = parent ∧ ∃ level, vmsMemLast st.taint_levels child level ∧
        ∃ inv, vmsMemLast st.in_flight parent inv ∧
          invConsumed st bg level (ovC bg parent level) (ocC st parent level) inv key)) := by
  simp only [transitions.return_unendorsed] at hok
  -- Gate 1: the parent edge `child → parent`.
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGet_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.AgentId.Insts.CoreCloneClone st.agent_parent child)
  rw [hoEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨b, hbEq, hbIff⟩ :
      ∃ bb, core.option.Option.Insts.CoreCmpPartialEqOption.ne
        (core.cmp.PartialEqShared types.AgentId.Insts.CoreCmpPartialEqAgentId) o (some parent) =
        .ok bb ∧ (bb = true ↔ o ≠ some parent) :=
    ⟨_, optionAgentId_ne_spec o (some parent), by simp⟩
  rw [hbEq] at hok; simp only [bind_tc_ok] at hok
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
  -- Gate 2: child active.
  obtain ⟨b1, hb1Eq, hb1Iff⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active child)
  rw [hb1Eq] at hok; simp only [bind_tc_ok] at hok
  have hb1 : b1 = true := by cases b1 with | true => rfl | false => simp at hok
  simp only [hb1, reduceIte] at hok
  -- Gate 3: parent active.
  obtain ⟨b2, hb2Eq, hb2Iff⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active parent)
  rw [hb2Eq] at hok; simp only [bind_tc_ok] at hok
  have hb2 : b2 = true := by cases b2 with | true => rfl | false => simp at hok
  simp only [hb2, reduceIte] at hok
  -- Gate 4: child has no in-flight invocation.
  obtain ⟨b3, hb3Eq, hb3Iff⟩ := spec_imp_exists
    (vecMapKVecSetSetNonempty_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight child)
  rw [hb3Eq] at hok; simp only [bind_tc_ok] at hok
  have hb3 : b3 = false := by cases b3 with | false => rfl | true => simp at hok
  simp only [hb3, reduceIte, Bool.false_eq_true] at hok
  have hNoFlight : ∀ inv, ¬ vmsMemLast st.in_flight child inv := by
    intro inv hc; have : b3 = true := hb3Iff.mpr ⟨inv, hc⟩; rw [hb3] at this; simp at this
  -- `child_taint`, the empty override set, `parent_flights`.
  obtain ⟨ct, hctEq, hctMem, hctLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_clone_spec st.taint_levels child)
  rw [hctEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vs, hvsEq, hvsNil⟩ : ∃ vs, collections.VecSet.new types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey = Result.ok vs ∧ vs.items.val = [] :=
    ⟨_, rfl, rfl⟩
  rw [hvsEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨pf, hpfEq, hpfMem, hpfLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight parent)
  rw [hpfEq] at hok; simp only [bind_tc_ok] at hok
  -- The double loop.
  obtain ⟨acc, hloopEq, hDen, hCon, _hNd, hLen⟩ := spec_imp_exists
    (returnUnendOuter_spec cgInst st bg content_gate parent cgOf hcg ct pf
      { denied := false, to_consume := vs }
      (by show vs.items.val.length + ct.items.val.length * pf.items.val.length ≤ Usize.max
          rw [hvsNil, hctLen, hpfLen]; simpa using hcapLoop)
      { denied := false, to_consume := vs } 0#usize
      (by simp) (by show vs.items.val.Nodup; rw [hvsNil]; exact List.nodup_nil)
      (by simp) (by simp) (by simp))
  rw [hloopEq] at hok; simp only [bind_tc_ok] at hok
  have hDenF : acc.denied = false := by
    cases hd : acc.denied with | false => rfl | true => simp [hd] at hok
  simp only [hDenF, reduceIte, Bool.false_eq_true] at hok
  have hAccLen : acc.to_consume.items.val.length ≤
      vmSetLen st.taint_levels child * vmSetLen st.in_flight parent := by
    have h := hLen; rw [hvsNil, hctLen, hpfLen] at h; simpa using h
  have hNotDenied : ∀ level inv tool E, vmsMemLast st.taint_levels child level →
      vmsMemLast st.in_flight parent inv → invToolC st inv = some tool → E ∈ egItems bg tool →
      ¬ egressDenied (flowModeC bg level E) (cgOf tool)
        (ovC bg parent level tool) (ocC st parent level tool) := by
    intro level inv tool E hlevel hinv htool hE hden'
    have hd : acc.denied = true := by
      rw [hDen]; right
      exact ⟨level, (hctMem level).mpr hlevel, inv, (hpfMem inv).mpr hinv, tool, htool, E, hE, hden'⟩
    rw [hDenF] at hd; simp at hd
  have hAcc : ∀ key, vsMem acc.to_consume key ↔ ∃ level, vmsMemLast st.taint_levels child level ∧
      ∃ inv, vmsMemLast st.in_flight parent inv ∧
        invConsumed st bg level (ovC bg parent level) (ocC st parent level) inv key := by
    intro key
    rw [hCon key]
    constructor
    · rintro (h | ⟨level, hlevel, inv, hinv, hcons⟩)
      · simp [vsMem, hvsNil] at h
      · exact ⟨level, (hctMem level).mp hlevel, inv, (hpfMem inv).mp hinv, hcons⟩
    · rintro ⟨level, hlevel, inv, hinv, hcons⟩
      exact Or.inr ⟨level, (hctMem level).mpr hlevel, inv, (hpfMem inv).mpr hinv, hcons⟩
  -- `is_empty child_taint`: the (vm, vm1) writes, uniform across the branches.
  obtain ⟨b4, hb4Eq, hb4Iff⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.ConfLevel.Insts.CoreCloneClone
      types.ConfLevel.Insts.CoreCmpPartialEqConfLevel ct)
  rw [hb4Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm, vm1, hvmEq, hvmMem, hvm1Mem⟩ : ∃ vm vm1,
      (if b4 = true then Result.ok (st.taint_levels, st.gh_taint_received)
       else (do
         let ai ← types.AgentId.Insts.CoreCloneClone.clone parent
         let vm2 ← collections.VecMapKVecSet.extend_into types.AgentId.Insts.CoreCloneClone
           types.AgentId.Insts.CoreCmpPartialEqAgentId types.ConfLevel.Insts.CoreCloneClone
           types.ConfLevel.Insts.CoreCmpPartialEqConfLevel st.taint_levels ai ct
         let vm3 ← collections.VecMapKVecSet.extend_into types.AgentId.Insts.CoreCloneClone
           types.AgentId.Insts.CoreCmpPartialEqAgentId types.ConfLevel.Insts.CoreCloneClone
           types.ConfLevel.Insts.CoreCmpPartialEqConfLevel st.gh_taint_received ai ct
         ok (vm2, vm3))) = Result.ok (vm, vm1) ∧
      (∀ ag v, vmsMemLast vm ag v ↔ vmsMemLast st.taint_levels ag v ∨ (ag = parent ∧ vsMem ct v)) ∧
      (∀ ag v, vmsMemLast vm1 ag v ↔
        vmsMemLast st.gh_taint_received ag v ∨ (ag = parent ∧ vsMem ct v)) := by
    cases hb4 : b4 with
    | true =>
      have hempty : ct.items.val = [] := hb4Iff.mp hb4
      refine ⟨st.taint_levels, st.gh_taint_received, by rw [if_pos rfl], fun ag v => ?_, fun ag v => ?_⟩
      · have : ¬ vsMem ct v := by simp [vsMem, hempty]
        simp [this]
      · have : ¬ vsMem ct v := by simp [vsMem, hempty]
        simp [this]
    | false =>
      obtain ⟨vm2, hvm2Eq, hvm2Mem⟩ := spec_imp_exists
        (extendInto_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_eq_spec confLevel_clone_spec st.taint_levels parent ct hcapTaintE
          (by intro p hp; rw [hctLen]; exact hcapTaintJoint p hp)
          (by rw [hctLen]; exact hcapTaintChild))
      obtain ⟨vm3, hvm3Eq, hvm3Mem⟩ := spec_imp_exists
        (extendInto_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_eq_spec confLevel_clone_spec st.gh_taint_received parent ct hcapGhrE
          (by intro p hp; rw [hctLen]; exact hcapGhrJoint p hp)
          (by rw [hctLen]; exact hcapTaintChild))
      refine ⟨vm2, vm3, ?_, hvm2Mem, hvm3Mem⟩
      simp only [Bool.false_eq_true, reduceIte, agentId_clone_spec, bind_tc_ok, hvm2Eq, hvm3Eq]
  rw [hvmEq] at hok
  -- full `simp` is required to collapse the tuple-bind pattern-`let (vm, vm1) := (vm, vm1)` (it
  -- threads the bind and substitutes `vm`/`vm1` into the records; `simp only`/`dsimp` won't).
  simp only [bind_tc_ok] at hok
  simp at hok
  -- `is_empty to_consume`: the override write, uniform across the branches.
  obtain ⟨b5, hb5Eq, hb5Iff⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey acc.to_consume)
  rw [hb5Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨ou, houEq, houMem⟩ : ∃ ou,
      (if b5 = true then
        Result.ok (core.result.Result.Ok
          (({ st with taint_levels := vm, gh_taint_received := vm1 } : state.KernelState),
           event.KernelAction.ReturnUnendorsed child parent))
       else (do
         let vm2 ← collections.VecMapKVecSet.extend_into types.AgentId.Insts.CoreCloneClone
           types.AgentId.Insts.CoreCmpPartialEqAgentId types.OverrideKey.Insts.CoreCloneClone
           types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey st.override_used parent acc.to_consume
         ok (core.result.Result.Ok
           (({ st with taint_levels := vm, gh_taint_received := vm1, override_used := vm2 }
              : state.KernelState),
            event.KernelAction.ReturnUnendorsed child parent)))) =
      Result.ok (core.result.Result.Ok
        (({ st with taint_levels := vm, gh_taint_received := vm1, override_used := ou }
           : state.KernelState),
         event.KernelAction.ReturnUnendorsed child parent)) ∧
      (∀ ag key, vmsMemLast ou ag key ↔ vmsMemLast st.override_used ag key ∨
        (ag = parent ∧ vsMem acc.to_consume key)) := by
    cases hb5 : b5 with
    | true =>
      have hempty : acc.to_consume.items.val = [] := hb5Iff.mp hb5
      refine ⟨st.override_used, by rw [if_pos rfl], fun ag key => ?_⟩
      have : ¬ vsMem acc.to_consume key := by simp [vsMem, hempty]
      simp [this]
    | false =>
      have hcapJ : ∀ p ∈ st.override_used.entries.val,
          p.2.items.val.length + acc.to_consume.items.val.length ≤ Usize.max := by
        intro p hp; have := hcapOvJoint p hp; omega
      obtain ⟨vm', hvm'Eq, hvm'Mem⟩ := spec_imp_exists
        (extendInto_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.OverrideKey.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
          overrideKey_eq_spec overrideKey_clone_spec st.override_used parent acc.to_consume
          hcapOvE hcapJ (le_trans hAccLen hcapLoop))
      refine ⟨vm', ?_, hvm'Mem⟩
      simp only [Bool.false_eq_true, reduceIte, bind_tc_ok, hvm'Eq]
  rw [houEq] at hok
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _⟩ := hok
  subst hStateEq
  refine ⟨hlast, hb1Iff.mp hb1, hb2Iff.mp hb2, hNoFlight, hNotDenied,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro ag v
    show vmsMemLast vm ag v ↔ _
    rw [hvmMem ag v]
    apply or_congr_right; apply and_congr_right'; rw [hctMem v]
  · intro ag v
    show vmsMemLast vm1 ag v ↔ _
    rw [hvm1Mem ag v]
    apply or_congr_right; apply and_congr_right'; rw [hctMem v]
  · intro ag key
    show vmsMemLast ou ag key ↔ _
    rw [houMem ag key, hAcc key]

/-! ## Forward simulation -/

/-- Forward simulation: a successful `return_unendorsed` step is matched by the abstract action,
    preserving `Rretu`. The witness propagates `child`'s taint set to `parent` (in `taint_levels`/
    `gh_taint_received`) and adds the single-use consumed overrides. The abstract flow guard — quantified
    over `child`'s taint levels `L`, `parent`'s in-flight `I`, and the bound tool's egresses `E` — is
    established from the concrete `denied = false` via the per-egress `not_egressDenied_disj`; the
    single-use `override_used` correspondence is the `egressConsumed_iff_abstractDenied` collapse, valid
    under the guard. The well-formedness invariant (`Rretu`'s last conjunct) supplies the bound tool for
    each in-flight invocation, which the kernel silently skips but the abstract guard needs. The content
    gate is the one opaque oracle (`hcg` totality + `hcgA` agreement). -/
theorem return_unendorsed_refines {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (a : AbsState) (child parent : types.AgentId)
    (cgOf : types.ToolId → Bool)
    (hcg : ∀ t, cgInst.passes content_gate parent t st bg = .ok (cgOf t))
    (hcgA : ∀ t, cgOf t = true ↔ a.content_gate_passes parent t)
    (hR : Rretu st bg a)
    (hcapLoop : vmSetLen st.taint_levels child * vmSetLen st.in_flight parent ≤ Usize.max)
    (hcapTaintE : st.taint_levels.entries.val.length < Usize.max)
    (hcapTaintJoint : ∀ p ∈ st.taint_levels.entries.val,
      p.2.items.val.length + vmSetLen st.taint_levels child ≤ Usize.max)
    (hcapTaintChild : vmSetLen st.taint_levels child ≤ Usize.max)
    (hcapGhrE : st.gh_taint_received.entries.val.length < Usize.max)
    (hcapGhrJoint : ∀ p ∈ st.gh_taint_received.entries.val,
      p.2.items.val.length + vmSetLen st.taint_levels child ≤ Usize.max)
    (hcapOvE : st.override_used.entries.val.length < Usize.max)
    (hcapOvJoint : ∀ p ∈ st.override_used.entries.val,
      p.2.items.val.length + vmSetLen st.taint_levels child * vmSetLen st.in_flight parent ≤ Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.return_unendorsed cgInst st bg content_gate child parent
      = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.return_unendorsed child parent).guard a ∧
          (Tzimtzum.return_unendorsed child parent).next a a' ∧ Rretu st' bg a' := by
  obtain ⟨hRact, hRparent, hRinfl, hRtaint, hRghr, hRov, hReg, hRallow, hRinsp, hRovr, hRinvtool,
      hRwf⟩ := hR
  obtain ⟨hParentEdge, hChildActive, hParentActive, hNoFlight, hNotDenied, hAct, hPar, hCap, hFl,
      hInvT, hToolReg, hGhInv, hAgInstr, hBudget, hTaintW, hGhrW, hOvW⟩ :=
    return_unendorsed_ok_inv cgInst st bg content_gate child parent cgOf hcg hcapLoop
      hcapTaintE hcapTaintJoint hcapTaintChild hcapGhrE hcapGhrJoint hcapOvE hcapOvJoint st' ev hok
  -- success ⇒ every in-flight invocation of `parent` is bound to its abstract tool
  have hbind : ∀ inv, vmsMemLast st.in_flight parent inv →
      invToolC st inv = some (a.invocation_tool inv) := by
    intro inv hmem
    cases hc : invToolC st inv with
    | none => exact absurd hc (hRwf parent inv hmem)
    | some t => rw [hRinvtool inv t hc]
  have hovIff : ∀ L t, ovC bg parent (confC L) t = true ↔
      vsMem bg.flow_overrides { agent := parent, tool := t, level := confC L } := by
    intro L t
    obtain ⟨b, hb, hbiff⟩ := spec_imp_exists (hasFlowOverride_spec bg parent t (confC L))
    rw [ovC_eq bg parent (confC L) t, Result.ok.injEq] at hb
    rw [hb]; exact hbiff
  have hocIff : ∀ L t, ocC st parent (confC L) t = true ↔
      vmsMemLast st.override_used parent { tool := t, level := confC L } := by
    intro L t
    obtain ⟨b, hb, hbiff⟩ := spec_imp_exists (overrideConsumed_spec st parent t (confC L))
    rw [ocC_eq st parent (confC L) t, Result.ok.injEq] at hb
    rw [hb]; exact hbiff
  -- per-tool guard from the concrete `not denied`, packaged for the matched in-flight tool
  have hguardOf : ∀ L inv, vmsMemLast st.taint_levels child (confC L) →
      vmsMemLast st.in_flight parent inv →
      ∀ E ∈ egItems bg (a.invocation_tool inv),
        ¬ egressDenied (flowModeC bg (confC L) E) (cgOf (a.invocation_tool inv))
          (ovC bg parent (confC L) (a.invocation_tool inv))
          (ocC st parent (confC L) (a.invocation_tool inv)) := by
    intro L inv hlevel hmem E hE
    exact hNotDenied (confC L) inv (a.invocation_tool inv) E hlevel hmem (hbind inv hmem) hE
  -- the single-use consume / abstract-denied equivalence, specialised to a matched in-flight tool
  have hConsEquiv : ∀ L inv, vmsMemLast st.taint_levels child (confC L) →
      vmsMemLast st.in_flight parent inv →
      ((∃ E ∈ egItems bg (a.invocation_tool inv),
          egressConsumed (flowModeC bg (confC L) E) (ovC bg parent (confC L) (a.invocation_tool inv))
            (ocC st parent (confC L) (a.invocation_tool inv))) ↔
       (a.flow_override parent (a.invocation_tool inv) L ∧
        ∃ E, a.tool_egress (a.invocation_tool inv) E ∧ ¬ a.flow_allows L E ∧
          ¬ (a.flow_inspects L E ∧ a.content_gate_passes parent (a.invocation_tool inv)))) := by
    intro L inv hlevel hmem
    rw [egressConsumed_iff_abstractDenied (egItems bg (a.invocation_tool inv)) (flowModeC bg (confC L))
      (cgOf (a.invocation_tool inv)) (ovC bg parent (confC L) (a.invocation_tool inv))
      (ocC st parent (confC L) (a.invocation_tool inv)) (hguardOf L inv hlevel hmem)]
    apply and_congr
    · rw [hovIff L (a.invocation_tool inv), hRovr parent (a.invocation_tool inv) L]
    · constructor
      · rintro ⟨E, hE, hne, hni⟩
        refine ⟨E, (hReg (a.invocation_tool inv) E).mpr hE, ?_, ?_⟩
        · rw [hRallow L E]; exact hne
        · rw [hRinsp L E, ← hcgA (a.invocation_tool inv)]; exact hni
      · rintro ⟨E, hEg, hna, hni⟩
        refine ⟨E, (hReg (a.invocation_tool inv) E).mp hEg, ?_, ?_⟩
        · exact fun h => hna ((hRallow L E).mpr h)
        · exact fun ⟨h1, h2⟩ => hni ⟨(hRinsp L E).mpr h1, (hcgA (a.invocation_tool inv)).mp h2⟩
  -- the abstract flow guard
  have hguard : ∀ L I E,
      a.taint_levels child L ∧ a.in_flight parent I ∧ a.tool_egress (a.invocation_tool I) E →
      a.flow_allows L E
      ∨ (a.flow_inspects L E ∧ a.content_gate_passes parent (a.invocation_tool I))
      ∨ (a.flow_override parent (a.invocation_tool I) L
          ∧ ¬ a.override_used parent (a.invocation_tool I) L) := by
    rintro L I E ⟨hLtaint, hIfl, hEg⟩
    have hmem : vmsMemLast st.in_flight parent I := (hRinfl parent I).mp hIfl
    have hlevel : vmsMemLast st.taint_levels child (confC L) := (hRtaint child L).mp hLtaint
    have hEItem : E ∈ egItems bg (a.invocation_tool I) := (hReg (a.invocation_tool I) E).mp hEg
    have hnd := hNotDenied (confC L) I (a.invocation_tool I) E hlevel hmem (hbind I hmem) hEItem
    rcases not_egressDenied_disj (flowModeC bg (confC L) E) (cgOf (a.invocation_tool I))
      (ovC bg parent (confC L) (a.invocation_tool I)) (ocC st parent (confC L) (a.invocation_tool I))
      hnd with hA | ⟨hI, hcgv⟩ | ⟨hovv, hocv⟩
    · exact Or.inl ((hRallow L E).mpr hA)
    · exact Or.inr (Or.inl ⟨(hRinsp L E).mpr hI, (hcgA (a.invocation_tool I)).mp hcgv⟩)
    · refine Or.inr (Or.inr ⟨?_, ?_⟩)
      · rw [hRovr parent (a.invocation_tool I) L]; exact (hovIff L (a.invocation_tool I)).mp hovv
      · rw [hRov parent (a.invocation_tool I) L]
        intro hc
        have := (hocIff L (a.invocation_tool I)).mpr hc
        rw [hocv] at this; simp at this
  refine ⟨{ a with
    taint_levels := fun A L => a.taint_levels A L ∨ (A = parent ∧ a.taint_levels child L),
    gh_taint_received := fun A L => a.gh_taint_received A L ∨ (A = parent ∧ a.taint_levels child L),
    override_used := fun A T L => a.override_used A T L ∨
      (A = parent ∧ a.taint_levels child L ∧ ∃ I, a.in_flight parent I ∧ T = a.invocation_tool I ∧
        a.flow_override parent (a.invocation_tool I) L ∧
        ∃ E, a.tool_egress (a.invocation_tool I) E ∧ ¬ a.flow_allows L E ∧
          ¬ (a.flow_inspects L E ∧ a.content_gate_passes parent (a.invocation_tool I))) },
    ?_, ?_, ?_⟩
  · -- guard
    exact ⟨(hRparent child parent).mpr hParentEdge, (hRact child).mpr hChildActive,
      (hRact parent).mpr hParentActive, fun I hc => hNoFlight I ((hRinfl child I).mp hc), hguard⟩
  · -- next
    simp [Tzimtzum.return_unendorsed]
  · -- Rretu st' bg a'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro x; rw [hAct]; exact hRact x
    · intro C P; rw [hPar]; exact hRparent C P
    · intro ag I; rw [hFl]; exact hRinfl ag I
    · intro ag L
      show (a.taint_levels ag L ∨ (ag = parent ∧ a.taint_levels child L)) ↔
        vmsMemLast st'.taint_levels ag (confC L)
      rw [hTaintW ag (confC L), hRtaint ag L, hRtaint child L]
    · intro ag L
      show (a.gh_taint_received ag L ∨ (ag = parent ∧ a.taint_levels child L)) ↔
        vmsMemLast st'.gh_taint_received ag (confC L)
      rw [hGhrW ag (confC L), hRghr ag L, hRtaint child L]
    · intro ag t L
      show (a.override_used ag t L ∨ (ag = parent ∧ a.taint_levels child L ∧ ∃ I,
          a.in_flight parent I ∧ t = a.invocation_tool I ∧
          a.flow_override parent (a.invocation_tool I) L ∧
          ∃ E, a.tool_egress (a.invocation_tool I) E ∧ ¬ a.flow_allows L E ∧
            ¬ (a.flow_inspects L E ∧ a.content_gate_passes parent (a.invocation_tool I))))
        ↔ vmsMemLast st'.override_used ag { tool := t, level := confC L }
      rw [hOvW ag { tool := t, level := confC L }, hRov ag t L]
      apply or_congr_right
      apply and_congr_right
      intro hag; subst ag
      constructor
      · rintro ⟨hLtaint, I, hIfl, htI, hovr, hegr⟩
        have hmem : vmsMemLast st.in_flight parent I := (hRinfl parent I).mp hIfl
        have hlevel : vmsMemLast st.taint_levels child (confC L) := (hRtaint child L).mp hLtaint
        refine ⟨confC L, hlevel, I, hmem, a.invocation_tool I, hbind I hmem, ?_, ?_⟩
        · simp only [gateConsumeKey, types.OverrideKey.mk.injEq]; exact ⟨htI, trivial⟩
        · exact (hConsEquiv L I hlevel hmem).mpr ⟨hovr, hegr⟩
      · rintro ⟨level, hlevel, inv, hmem, tool', htool', hkey, hcons⟩
        rw [hbind inv hmem, Option.some.injEq] at htool'
        subst htool'
        simp only [gateConsumeKey, types.OverrideKey.mk.injEq] at hkey
        obtain ⟨hteq, hlvl⟩ := hkey
        subst hlvl
        exact ⟨(hRtaint child L).mpr hlevel, inv, (hRinfl parent inv).mpr hmem, hteq,
          (hConsEquiv L inv hlevel hmem).mp hcons⟩
    · exact hReg
    · exact hRallow
    · exact hRinsp
    · exact hRovr
    · intro I t hI
      have heq : invToolC st' I = invToolC st I := by unfold invToolC; rw [hInvT]
      exact hRinvtool I t (heq ▸ hI)
    · intro ag I hI
      have heq : invToolC st' I = invToolC st I := by unfold invToolC; rw [hInvT]
      rw [heq]; exact hRwf ag I (by rw [← hFl]; exact hI)

end ArgusLean.Refinement

-- Trust-base audit. Beyond the three standard axioms: the `register_tool` `String`/id residuals (via
-- `Collections`) plus `optionAgentId_ne_spec` (the `Option AgentId` parent-edge gate, `agentId_ne_spec`
-- class). The flow/`FlowMode`/`OverrideKey` facts are PROVED; the single-use `override_used`
-- correspondence is `egressConsumed_iff_abstractDenied` under the guard. No agent is added/removed and
-- the root is never named — no `sorryAx`/`AgentId.root`. The double loop accumulates the per-`(level,
-- inv)` flow decision; the well-formedness binding-totality invariant (`Rretu`'s last conjunct) supplies
-- the bound tool the kernel's silent skip would otherwise hide from the abstract guard.
#print axioms ArgusLean.Refinement.return_unendorsed_ok_inv
#print axioms ArgusLean.Refinement.return_unendorsed_refines
