import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `return_unendorsed` preserves the unified `R`

Proved by **reuse** of `return_unendorsed_refines`: `Rretu` carries no budget clause and already reads
every field through `R`'s canonical views (`vmsMemLast` for the propagated `taint_levels` /
`gh_taint_received`, the get-style `vmLastEntry` parent edge), so it projects cleanly from `R` and its
output covers 11 of the unified conjuncts verbatim — no taint/gh view bridge is needed (unlike
`sentinel_elevate_taint`). The remaining conjuncts (the untouched fields + the three written maps' nodup
posts + the full metadata `wfInflight`) transport via the abstract frames (`hnext`), the concrete frames
+ nodup posts (`return_unendorsed_inv_full`), and `R.wfInflight`. The content gate is the one opaque
oracle (`cgOf`/`hcg`/`hcgA`, from `CgAgree` in the bundle). -/

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
    (hov : ∀ t, state.KernelState.has_flow_override st parent t level = .ok (ovOf t))
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
      st.gh_taint_received st.agent_instruction st.override_used st.flow_override st.agent_budget
      bg content_gate parent acc invs level fi ⦃ res =>
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
        simp only []
        obtain ⟨tmeta, hmetaEq, hmeta⟩ := spec_imp_exists (toolMetadata_spec bg tool)
        rw [hmetaEq]; simp only [bind_tc_ok]
        have hcapAcc : accL.to_consume.items.val.length < Usize.max := by
          have := hlenL; have := hlt; have := hcapS; omega
        have hst : ((⟨st.agent_active, st.agent_parent, st.agent_cap, st.taint_levels,
            st.in_flight, st.invocation_tool, st.tool_registered, st.gh_taint_invoked,
            st.gh_taint_received, st.agent_instruction, st.override_used, st.flow_override,
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
          simp only []
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
        invDenied st bg level cgOf (ovC st parent level) (ocC st parent level) inv)
    (hcon : ∀ k, vsMem acc.to_consume k ↔ vsMem accStart.to_consume k ∨
      ∃ level ∈ child_taint.items.val.take li.val, ∃ inv ∈ parent_flights.items.val,
        invConsumed st bg level (ovC st parent level) (ocC st parent level) inv k) :
    transitions.return_unendorsed_loop0 cgInst st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.in_flight st.invocation_tool st.tool_registered st.gh_taint_invoked
      st.gh_taint_received st.agent_instruction st.override_used st.flow_override st.agent_budget
      bg content_gate parent child_taint acc parent_flights li ⦃ res =>
      (res.denied = true ↔ accStart.denied = true ∨
        ∃ level ∈ child_taint.items.val, ∃ inv ∈ parent_flights.items.val,
          invDenied st bg level cgOf (ovC st parent level) (ocC st parent level) inv) ∧
      (∀ k, vsMem res.to_consume k ↔ vsMem accStart.to_consume k ∨
        ∃ level ∈ child_taint.items.val, ∃ inv ∈ parent_flights.items.val,
          invConsumed st bg level (ovC st parent level) (ocC st parent level) inv k) ∧
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
          invDenied st bg level cgOf (ovC st parent level) (ocC st parent level) inv) ∧
      (∀ k, vsMem p.1.to_consume k ↔ vsMem accStart.to_consume k ∨
        ∃ level ∈ child_taint.items.val.take p.2.val, ∃ inv ∈ parent_flights.items.val,
          invConsumed st bg level (ovC st parent level) (ocC st parent level) inv k))
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
          (ovC st parent level) (ocC st parent level) hcg
          (fun t => ovC_eq st parent level t) (fun t => ocC_eq st parent level t)
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
          invDenied st bg lev cgOf (ovC st parent lev) (ocC st parent lev) inv), hDen1, hdenL,
          or_assoc]
      · -- consume
        intro k
        rw [hi2 _ li1_post, hCon1 k, hconL k,
          hext (fun lev => ∃ inv ∈ parent_flights.items.val,
            invConsumed st bg lev (ovC st parent lev) (ocC st parent lev) inv k), or_assoc]
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
  (∀ L E, a.flow_allows L E ↔ ceilAdmitsC bg.allow_ceiling (confC L) E = true) ∧
  (∀ L E, a.flow_inspects L E ↔ ceilAdmitsC bg.inspect_ceiling (confC L) E = true) ∧
  (∀ A T L, a.flow_override A T L ↔
    vmsMemLast st.flow_override A { tool := T, level := confC L }) ∧
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
        (ovC st parent level tool) (ocC st parent level tool)) ∧
    st'.agent_active = st.agent_active ∧ st'.agent_parent = st.agent_parent ∧
    st'.agent_cap = st.agent_cap ∧ st'.in_flight = st.in_flight ∧
    st'.invocation_tool = st.invocation_tool ∧ st'.tool_registered = st.tool_registered ∧
    st'.gh_taint_invoked = st.gh_taint_invoked ∧ st'.agent_instruction = st.agent_instruction ∧
    st'.agent_budget = st.agent_budget ∧ st'.flow_override = st.flow_override ∧
    (∀ ag v, vmsMemLast st'.taint_levels ag v ↔
      vmsMemLast st.taint_levels ag v ∨ (ag = parent ∧ vmsMemLast st.taint_levels child v)) ∧
    (∀ ag v, vmsMemLast st'.gh_taint_received ag v ↔
      vmsMemLast st.gh_taint_received ag v ∨ (ag = parent ∧ vmsMemLast st.taint_levels child v)) ∧
    (∀ ag key, vmsMemLast st'.override_used ag key ↔ vmsMemLast st.override_used ag key ∨
      (ag = parent ∧ ∃ level, vmsMemLast st.taint_levels child level ∧
        ∃ inv, vmsMemLast st.in_flight parent inv ∧
          invConsumed st bg level (ovC st parent level) (ocC st parent level) inv key)) := by
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
        (ovC st parent level tool) (ocC st parent level tool) := by
    intro level inv tool E hlevel hinv htool hE hden'
    have hd : acc.denied = true := by
      rw [hDen]; right
      exact ⟨level, (hctMem level).mpr hlevel, inv, (hpfMem inv).mpr hinv, tool, htool, E, hE, hden'⟩
    rw [hDenF] at hd; simp at hd
  have hAcc : ∀ key, vsMem acc.to_consume key ↔ ∃ level, vmsMemLast st.taint_levels child level ∧
      ∃ inv, vmsMemLast st.in_flight parent inv ∧
        invConsumed st bg level (ovC st parent level) (ocC st parent level) inv key := by
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
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
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
      hInvT, hToolReg, hGhInv, hAgInstr, hBudget, hFlowOv, hTaintW, hGhrW, hOvW⟩ :=
    return_unendorsed_ok_inv cgInst st bg content_gate child parent cgOf hcg hcapLoop
      hcapTaintE hcapTaintJoint hcapTaintChild hcapGhrE hcapGhrJoint hcapOvE hcapOvJoint st' ev hok
  -- success ⇒ every in-flight invocation of `parent` is bound to its abstract tool
  have hbind : ∀ inv, vmsMemLast st.in_flight parent inv →
      invToolC st inv = some (a.invocation_tool inv) := by
    intro inv hmem
    cases hc : invToolC st inv with
    | none => exact absurd hc (hRwf parent inv hmem)
    | some t => rw [hRinvtool inv t hc]
  have hovIff : ∀ L t, ovC st parent (confC L) t = true ↔
      vmsMemLast st.flow_override parent { tool := t, level := confC L } := by
    intro L t
    obtain ⟨b, hb, hbiff⟩ := spec_imp_exists (hasFlowOverride_spec st parent t (confC L))
    rw [ovC_eq st parent (confC L) t, Result.ok.injEq] at hb
    rw [hb]; exact hbiff
  have hocIff : ∀ L t, ocC st parent (confC L) t = true ↔
      vmsMemLast st.override_used parent { tool := t, level := confC L } := by
    intro L t
    obtain ⟨b, hb, hbiff⟩ := spec_imp_exists (overrideConsumed_spec st parent t (confC L))
    rw [ocC_eq st parent (confC L) t, Result.ok.injEq] at hb
    rw [hb]; exact hbiff
  -- band tests in `flowModeC` terms. `flow_allows ↔ flowModeC = Allow` STILL holds; `flow_inspects ↔
  -- flowModeC = Inspect` does NOT (inspect band may overlap allow band) — only band membership
  -- survives, and we route the denial form through `hDenForm` (both directions hold).
  have hAllowIff : ∀ L E, a.flow_allows L E ↔ flowModeC bg (confC L) E = background.FlowMode.Allow := by
    intro L E; rw [hRallow L E, flowModeC_allow_iff]
  have hInspBand : ∀ L E, a.flow_inspects L E ↔ ceilAdmitsC bg.inspect_ceiling (confC L) E = true := by
    intro L E; rw [hRinsp L E]
  have hDenForm : ∀ (L : Tzimtzum.ConfLevel) (E : types.EgressKind) (cg : Bool),
      ((flowModeC bg (confC L) E ≠ background.FlowMode.Allow ∧
        ¬ (flowModeC bg (confC L) E = background.FlowMode.Inspect ∧ cg = true))
      ↔ (¬ a.flow_allows L E ∧
          ¬ (a.flow_inspects L E ∧ cg = true))) := by
    intro L E cg
    rw [hAllowIff L E, hInspBand L E]
    constructor
    · rintro ⟨hne, hni⟩
      refine ⟨hne, ?_⟩
      rintro ⟨hib, hcg⟩
      have hab : ceilAdmitsC bg.allow_ceiling (confC L) E = false := by
        by_contra hc
        exact hne ((flowModeC_allow_iff bg (confC L) E).mpr (by simp_all))
      exact hni ⟨(flowModeC_inspect_iff bg (confC L) E).mpr ⟨hab, hib⟩, hcg⟩
    · rintro ⟨hna, hni⟩
      refine ⟨hna, ?_⟩
      rintro ⟨hi, hcg⟩
      exact hni ⟨((flowModeC_inspect_iff bg (confC L) E).mp hi).2, hcg⟩
  -- per-tool guard from the concrete `not denied`, packaged for the matched in-flight tool
  have hguardOf : ∀ L inv, vmsMemLast st.taint_levels child (confC L) →
      vmsMemLast st.in_flight parent inv →
      ∀ E ∈ egItems bg (a.invocation_tool inv),
        ¬ egressDenied (flowModeC bg (confC L) E) (cgOf (a.invocation_tool inv))
          (ovC st parent (confC L) (a.invocation_tool inv))
          (ocC st parent (confC L) (a.invocation_tool inv)) := by
    intro L inv hlevel hmem E hE
    exact hNotDenied (confC L) inv (a.invocation_tool inv) E hlevel hmem (hbind inv hmem) hE
  -- the single-use consume / abstract-denied equivalence, specialised to a matched in-flight tool
  have hConsEquiv : ∀ L inv, vmsMemLast st.taint_levels child (confC L) →
      vmsMemLast st.in_flight parent inv →
      ((∃ E ∈ egItems bg (a.invocation_tool inv),
          egressConsumed (flowModeC bg (confC L) E) (ovC st parent (confC L) (a.invocation_tool inv))
            (ocC st parent (confC L) (a.invocation_tool inv))) ↔
       (a.flow_override parent (a.invocation_tool inv) L ∧
        ∃ E, a.tool_egress (a.invocation_tool inv) E ∧ ¬ a.flow_allows L E ∧
          ¬ (a.flow_inspects L E ∧ a.content_gate_passes parent (a.invocation_tool inv)))) := by
    intro L inv hlevel hmem
    rw [egressConsumed_iff_abstractDenied (egItems bg (a.invocation_tool inv)) (flowModeC bg (confC L))
      (cgOf (a.invocation_tool inv)) (ovC st parent (confC L) (a.invocation_tool inv))
      (ocC st parent (confC L) (a.invocation_tool inv)) (hguardOf L inv hlevel hmem)]
    apply and_congr
    · rw [hovIff L (a.invocation_tool inv), hRovr parent (a.invocation_tool inv) L]
    · constructor
      · rintro ⟨E, hE, hden⟩
        refine ⟨E, (hReg (a.invocation_tool inv) E).mpr hE, ?_⟩
        have := (hDenForm L E (cgOf (a.invocation_tool inv))).mp hden
        rwa [hcgA (a.invocation_tool inv)] at this
      · rintro ⟨E, hEg, hden⟩
        refine ⟨E, (hReg (a.invocation_tool inv) E).mp hEg, ?_⟩
        rw [← hcgA (a.invocation_tool inv)] at hden
        exact (hDenForm L E (cgOf (a.invocation_tool inv))).mpr hden
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
      (ovC st parent (confC L) (a.invocation_tool I)) (ocC st parent (confC L) (a.invocation_tool I))
      hnd with hA | ⟨hI, hcgv⟩ | ⟨hovv, hocv⟩
    · exact Or.inl ((hAllowIff L E).mpr hA)
    · exact Or.inr (Or.inl ⟨(hInspBand L E).mpr ((flowModeC_inspect_iff bg (confC L) E).mp hI).2,
        (hcgA (a.invocation_tool I)).mp hcgv⟩)
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
    · intro A T L; rw [hFlowOv]; exact hRovr A T L
    · intro I t hI
      have heq : invToolC st' I = invToolC st I := by unfold invToolC; rw [hInvT]
      exact hRinvtool I t (heq ▸ hI)
    · intro ag I hI
      have heq : invToolC st' I = invToolC st I := by unfold invToolC; rw [hInvT]
      rw [heq]; exact hRwf ag I (by rw [← hFl]; exact hI)

/-- Re-run of the `return_unendorsed` inversion exposing the concrete frames (every untouched map
    unchanged) and the `vmNodupKeys` posts for the three written maps (`taint_levels` /
    `gh_taint_received` via the `child_taint` extends, `override_used` via the `to_consume` extend). -/
theorem return_unendorsed_inv_full {C : Type} (cgInst : traits.ContentGateOracle C)
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
    st'.agent_active = st.agent_active ∧ st'.agent_parent = st.agent_parent ∧
    st'.agent_cap = st.agent_cap ∧ st'.in_flight = st.in_flight ∧
    st'.invocation_tool = st.invocation_tool ∧ st'.tool_registered = st.tool_registered ∧
    st'.gh_taint_invoked = st.gh_taint_invoked ∧ st'.agent_instruction = st.agent_instruction ∧
    st'.agent_budget = st.agent_budget ∧ st'.flow_override = st.flow_override ∧
    (vmNodupKeys st.taint_levels → vmNodupKeys st'.taint_levels) ∧
    (vmNodupKeys st.gh_taint_received → vmNodupKeys st'.gh_taint_received) ∧
    (vmNodupKeys st.override_used → vmNodupKeys st'.override_used) := by
  simp only [transitions.return_unendorsed] at hok
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
  obtain ⟨b1, hb1Eq, hb1Iff⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active child)
  rw [hb1Eq] at hok; simp only [bind_tc_ok] at hok
  have hb1 : b1 = true := by cases b1 with | true => rfl | false => simp at hok
  simp only [hb1, reduceIte] at hok
  obtain ⟨b2, hb2Eq, hb2Iff⟩ := spec_imp_exists
    (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active parent)
  rw [hb2Eq] at hok; simp only [bind_tc_ok] at hok
  have hb2 : b2 = true := by cases b2 with | true => rfl | false => simp at hok
  simp only [hb2, reduceIte] at hok
  obtain ⟨b3, hb3Eq, hb3Iff⟩ := spec_imp_exists
    (vecMapKVecSetSetNonempty_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight child)
  rw [hb3Eq] at hok; simp only [bind_tc_ok] at hok
  have hb3 : b3 = false := by cases b3 with | false => rfl | true => simp at hok
  simp only [hb3, reduceIte, Bool.false_eq_true] at hok
  obtain ⟨ct, hctEq, _hctMem, hctLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
      confLevel_clone_spec st.taint_levels child)
  rw [hctEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vs, hvsEq, hvsNil⟩ : ∃ vs, collections.VecSet.new types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey = Result.ok vs ∧ vs.items.val = [] :=
    ⟨_, rfl, rfl⟩
  rw [hvsEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨pf, hpfEq, _hpfMem, hpfLen⟩ := spec_imp_exists
    (getSetOrEmptyLen_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.InvocationId.Insts.CoreCloneClone types.InvocationId.Insts.CoreCmpPartialEqInvocationId
      invocationId_clone_spec st.in_flight parent)
  rw [hpfEq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨acc, hloopEq, _hDen, _hCon, _hNd, hLen⟩ := spec_imp_exists
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
  obtain ⟨b4, hb4Eq, _hb4Iff⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.ConfLevel.Insts.CoreCloneClone
      types.ConfLevel.Insts.CoreCmpPartialEqConfLevel ct)
  rw [hb4Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨vm, vm1, hvmEq, hvmNd, hvm1Nd⟩ : ∃ vm vm1,
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
      (vmNodupKeys st.taint_levels → vmNodupKeys vm) ∧
      (vmNodupKeys st.gh_taint_received → vmNodupKeys vm1) := by
    cases hb4 : b4 with
    | true => exact ⟨st.taint_levels, st.gh_taint_received, by rw [if_pos rfl], id, id⟩
    | false =>
      obtain ⟨vm2, hvm2Eq, hvm2Nd⟩ := spec_imp_exists
        (extendInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_eq_spec confLevel_clone_spec st.taint_levels parent ct hcapTaintE
          (by intro p hp; rw [hctLen]; exact hcapTaintJoint p hp)
          (by rw [hctLen]; exact hcapTaintChild))
      obtain ⟨vm3, hvm3Eq, hvm3Nd⟩ := spec_imp_exists
        (extendInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.ConfLevel.Insts.CoreCloneClone types.ConfLevel.Insts.CoreCmpPartialEqConfLevel
          confLevel_eq_spec confLevel_clone_spec st.gh_taint_received parent ct hcapGhrE
          (by intro p hp; rw [hctLen]; exact hcapGhrJoint p hp)
          (by rw [hctLen]; exact hcapTaintChild))
      refine ⟨vm2, vm3, ?_, hvm2Nd, hvm3Nd⟩
      simp only [Bool.false_eq_true, reduceIte, agentId_clone_spec, bind_tc_ok, hvm2Eq, hvm3Eq]
  rw [hvmEq] at hok
  simp only [bind_tc_ok] at hok
  simp at hok
  obtain ⟨b5, hb5Eq, _hb5Iff⟩ := spec_imp_exists
    (vecSetIsEmpty_spec types.OverrideKey.Insts.CoreCloneClone
      types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey acc.to_consume)
  rw [hb5Eq] at hok; simp only [bind_tc_ok] at hok
  obtain ⟨ou, houEq, houNd⟩ : ∃ ou,
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
      (vmNodupKeys st.override_used → vmNodupKeys ou) := by
    cases hb5 : b5 with
    | true => exact ⟨st.override_used, by rw [if_pos rfl], id⟩
    | false =>
      have hcapJ : ∀ p ∈ st.override_used.entries.val,
          p.2.items.val.length + acc.to_consume.items.val.length ≤ Usize.max := by
        intro p hp; have := hcapOvJoint p hp; omega
      obtain ⟨vm', hvm'Eq, hvm'Nd⟩ := spec_imp_exists
        (extendInto_nodup types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
          types.OverrideKey.Insts.CoreCloneClone types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey
          overrideKey_eq_spec overrideKey_clone_spec st.override_used parent acc.to_consume
          hcapOvE hcapJ (le_trans hAccLen hcapLoop))
      refine ⟨vm', ?_, hvm'Nd⟩
      simp only [Bool.false_eq_true, reduceIte, bind_tc_ok, hvm'Eq]
  rw [houEq] at hok
  simp only [Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _⟩ := hok
  subst hStateEq
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hvmNd, hvm1Nd, houNd⟩

/-- `return_unendorsed` preserves the unified `R`. -/
theorem return_unendorsed_preservesR {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (a : AbsState) (child parent : types.AgentId)
    (cgOf : types.ToolId → Bool)
    (hcg : ∀ t, cgInst.passes content_gate parent t st bg = .ok (cgOf t))
    (hcgA : ∀ t, cgOf t = true ↔ a.content_gate_passes parent t)
    (hR : R st bg a)
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
          (Tzimtzum.return_unendorsed child parent).next a a' ∧ R st' bg a' := by
  -- project `R → Rretu` (every view canonical; the binding-totality conjunct from `R.wfInflight`)
  have hRretu : Rretu st bg a := ⟨hR.active, hR.parent, hR.inflight, hR.taint, hR.ghReceived,
    hR.override, hR.toolEgress, hR.flowAllows, hR.flowInspects, hR.flowOverride, hR.invTool,
    fun ag I hmem => by obtain ⟨t, _, ht, _⟩ := hR.wfInflight ag I hmem; rw [ht]; exact Option.some_ne_none t⟩
  obtain ⟨a', hguard, hnext, hRretu'⟩ :=
    return_unendorsed_refines cgInst st bg content_gate a child parent cgOf hcg hcgA hRretu
      hcapLoop hcapTaintE hcapTaintJoint hcapTaintChild hcapGhrE hcapGhrJoint hcapOvE hcapOvJoint
      st' ev hok
  obtain ⟨hf_act, hf_par, hf_cap, hf_infl, hf_invt, hf_reg, hf_ghinv, hf_instr, hf_bud, hf_flowov,
      hNdTaint, hNdGhr, hNdOver⟩ :=
    return_unendorsed_inv_full cgInst st bg content_gate child parent cgOf hcg hcapLoop hcapTaintE
      hcapTaintJoint hcapTaintChild hcapGhrE hcapGhrJoint hcapOvE hcapOvJoint st' ev hok
  obtain ⟨hRact', hRparent', hRinfl', hRtaint', hRghr', hRov', hReg', hAllow', hInsp', hOvr',
      hInvtool', _hRwf'⟩ := hRretu'
  simp only [Tzimtzum.return_unendorsed] at hnext
  obtain ⟨ha_active, ha_parent, ha_cap, ha_instr, ha_taint, ha_bud, ha_infl, ha_reg, ha_ghinv,
      ha_ghrec, ha_over, ha_flowov, ha_toolcap, ha_egress, ha_floor, ha_ob, ha_iss, ha_trust, ha_oc,
      ha_instriss, ha_allowceil, ha_inspceil, ha_au, ha_cg, ha_invtool, ha_root, ha_capdecl,
      ha_caprefresh, ha_capgrantov⟩ := hnext
  refine ⟨a', hguard, ?_, ?_⟩
  · simp only [Tzimtzum.return_unendorsed]
    exact ⟨ha_active, ha_parent, ha_cap, ha_instr, ha_taint, ha_bud, ha_infl, ha_reg, ha_ghinv,
      ha_ghrec, ha_over, ha_flowov, ha_toolcap, ha_egress, ha_floor, ha_ob, ha_iss, ha_trust, ha_oc,
      ha_instriss, ha_allowceil, ha_inspceil, ha_au, ha_cg, ha_invtool, ha_root, ha_capdecl,
      ⟨ha_caprefresh, ha_capgrantov⟩⟩
  · refine ⟨by rw [ha_root]; exact hR.root, by rw [ha_capdecl]; exact hR.cap_declass,
      by rw [ha_caprefresh]; exact hR.cap_refresh, by rw [ha_capgrantov]; exact hR.cap_grantov,
      hRact',
      fun t => by rw [ha_reg, hf_reg]; exact hR.tool_reg t, hRparent',
      fun N Cc => by rw [ha_cap, hf_cap]; exact hR.cap N Cc,
      fun ag ins => by rw [ha_instr, hf_instr]; exact hR.instr ag ins, hRtaint', hRinfl',
      fun ag L => by rw [ha_ghinv, hf_ghinv]; exact hR.ghInvoked ag L, hRghr', hRov',
      fun G L hG => by rw [ha_bud, hf_bud]; rw [ha_active] at hG; exact hR.budget G L hG,
      fun t tmeta Cc h => by rw [ha_toolcap]; exact hR.toolCap t tmeta Cc h, hReg',
      fun t tmeta h => by rw [ha_floor]; exact hR.toolFloor t tmeta h,
      fun t tmeta h => by rw [ha_ob]; exact hR.toolBounded t tmeta h,
      fun t tmeta h => by rw [ha_iss]; exact hR.toolIssuer t tmeta h,
      fun i => by rw [ha_trust]; exact hR.trustedIss i,
      fun i issuer h => by rw [ha_instriss]; exact hR.instrIssuer i issuer h, hAllow', hInsp', hOvr',
      hInvtool', by rw [hf_par]; exact hR.ndParent, by rw [hf_cap]; exact hR.ndCap,
      by rw [hf_instr]; exact hR.ndInstr, hNdTaint hR.ndTaint, by rw [hf_infl]; exact hR.ndInflight,
      by rw [hf_ghinv]; exact hR.ndGhInvoked, hNdGhr hR.ndGhReceived, hNdOver hR.ndOverride,
      by rw [hf_flowov]; exact hR.ndFlowOverride,
      by rw [hf_bud]; exact hR.ndBudget, fun ag I hmem => ?_⟩
    -- wfInflight: in_flight + invocation_tool unchanged
    have hmem' : vmsMemLast st.in_flight ag I := by rw [← hf_infl]; exact hmem
    obtain ⟨t, tmeta, ht, htm⟩ := hR.wfInflight ag I hmem'
    exact ⟨t, tmeta, by unfold invToolC; rw [hf_invt]; exact ht, htm⟩

end ArgusLean.Refinement
