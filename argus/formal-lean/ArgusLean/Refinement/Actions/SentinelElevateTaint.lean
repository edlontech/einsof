import ArgusLean.Refinement.StateRelation
import ArgusLean.Refinement.ReturnUnendorsedFlow

/-! # Refinement — `sentinel_elevate_taint`

`sentinel_elevate_taint a l` raises `a`'s taint to `l`, flow-gated against `a`'s in-flight tools, and
CONSUMES the overrides that justified passing a DENY (the single-use property). Single loop over `a`'s
in-flight invocations: for each, look up the tool (a missing binding is an error), read its egress
set, and fold `gate_egress` at level `l`. On success (no missing binding, gate not blocked) it writes
three fields — `override_used` gains the consumed keys, `taint_levels`/`gh_taint_invoked` gain `l`.

This file holds the **concrete loop spec** (`sentinelLoop_spec`, parametrised by the per-tool oracle
values; the keystone shared with `return_unendorsed`'s inner loop) plus the oracle-agreement relation
`Rsent` and the inversion/refines assembly. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option Aeneas.Deprecated.progressWarning false
set_option maxHeartbeats 4000000

/-! ## Per-invocation contribution predicates (concrete)

`invToolC` = the live (last-match) tool bound to an invocation; `egItems` = a tool's egress list (empty
if no metadata). `invDenied` / `invConsumed` / `invMissing` are one invocation's contribution to the
loop's `denied` flag / `to_consume` set / `missing_binding` flag, in terms of the per-tool oracle
values `cgOf` / `ovOf` / `ocOf` and `flowModeC`. -/

/-- The live tool bound to `inv` (last-match `invocation_tool`), or `none`. -/
def invToolC (st : state.KernelState) (inv : types.InvocationId) : Option types.ToolId :=
  (vmLastEntry st.invocation_tool.entries.val inv).map Prod.snd

/-- A tool's egress list: empty when it has no metadata. -/
def egItems (bg : background.BackgroundTheory) (tool : types.ToolId) : List types.EgressKind :=
  match toolMetaC bg tool with
  | none => []
  | some m => m.egress.items.val

/-- `inv` lacks a tool binding (the `MissingToolBinding` condition). -/
def invMissing (st : state.KernelState) (inv : types.InvocationId) : Prop :=
  invToolC st inv = none

/-- `inv` contributes denial: its bound tool has an egress that the flow gate denies at `level`. -/
def invDenied (st : state.KernelState) (bg : background.BackgroundTheory) (level : types.ConfLevel)
    (cgOf ovOf ocOf : types.ToolId → Bool) (inv : types.InvocationId) : Prop :=
  ∃ tool, invToolC st inv = some tool ∧
    ∃ E ∈ egItems bg tool, egressDenied (flowModeC bg level E) (cgOf tool) (ovOf tool) (ocOf tool)

/-- `inv` contributes the override key `k` to `to_consume`. -/
def invConsumed (st : state.KernelState) (bg : background.BackgroundTheory) (level : types.ConfLevel)
    (ovOf ocOf : types.ToolId → Bool) (inv : types.InvocationId) (k : types.OverrideKey) : Prop :=
  ∃ tool, invToolC st inv = some tool ∧ k = gateConsumeKey tool level ∧
    ∃ E ∈ egItems bg tool, egressConsumed (flowModeC bg level E) (ovOf tool) (ocOf tool)

/-- A missing-binding invocation contributes no denial. -/
theorem not_invDenied_missing {st bg level cgOf ovOf ocOf} {inv : types.InvocationId}
    (h : invToolC st inv = none) : ¬ invDenied st bg level cgOf ovOf ocOf inv := by
  simp only [invDenied]; rintro ⟨tool, htool, _⟩; rw [h] at htool; simp at htool

/-- A missing-binding invocation contributes nothing to `to_consume`. -/
theorem not_invConsumed_missing {st bg level ovOf ocOf} {inv : types.InvocationId}
    {k : types.OverrideKey} (h : invToolC st inv = none) :
    ¬ invConsumed st bg level ovOf ocOf inv k := by
  simp only [invConsumed]; rintro ⟨tool, htool, _⟩; rw [h] at htool; simp at htool

/-! ## The in-flight loop -/

/-- Generalised loop spec for `sentinel_elevate_taint_loop`, relative to a fixed reference
    `(accStart, mbStart)`: after scanning the prefix `[0, fi)` of `invs` the running accumulator's
    `denied`/`to_consume`/`missing_binding` are exactly the reference extended by the per-invocation
    contributions over that prefix; `to_consume` stays `Nodup` and short of `Usize.max`. The per-tool
    oracle values are supplied as `cgOf`/`ovOf`/`ocOf` with their `= .ok` agreement hypotheses (only
    the content gate is opaque; `has_flow_override`/`override_consumed` callers discharge from the
    proven specs). The state args are `st`'s fields (the kernel always calls it that way). -/
theorem sentinelLoop_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (st : state.KernelState) (bg : background.BackgroundTheory) (content_gate : C)
    (agent : types.AgentId) (level : types.ConfLevel)
    (cgOf ovOf ocOf : types.ToolId → Bool)
    (hcg : ∀ t, cgInst.passes content_gate agent t st bg = .ok (cgOf t))
    (hov : ∀ t, background.BackgroundTheory.has_flow_override bg agent t level = .ok (ovOf t))
    (hoc : ∀ t, state.KernelState.override_consumed st agent t level = .ok (ocOf t))
    (invs : collections.VecSet types.InvocationId)
    (accStart : transitions.GateAccum) (mbStart : Bool)
    (hcapS : accStart.to_consume.items.val.length + invs.items.val.length ≤ Usize.max)
    (acc : transitions.GateAccum) (mb : Bool) (fi : Usize)
    (hfi : fi.val ≤ invs.items.val.length)
    (hnd : acc.to_consume.items.val.Nodup)
    (hlen : acc.to_consume.items.val.length ≤ accStart.to_consume.items.val.length + fi.val)
    (hmb : mb = true ↔ mbStart = true ∨ ∃ inv ∈ invs.items.val.take fi.val, invMissing st inv)
    (hden : acc.denied = true ↔ accStart.denied = true ∨
      ∃ inv ∈ invs.items.val.take fi.val, invDenied st bg level cgOf ovOf ocOf inv)
    (hcon : ∀ k, vsMem acc.to_consume k ↔ vsMem accStart.to_consume k ∨
      ∃ inv ∈ invs.items.val.take fi.val, invConsumed st bg level ovOf ocOf inv k) :
    transitions.sentinel_elevate_taint_loop cgInst st.agent_active st.agent_parent st.agent_cap
      st.taint_levels st.in_flight st.invocation_tool st.tool_registered st.gh_taint_invoked
      st.gh_taint_received st.agent_instruction st.override_used st.agent_budget bg content_gate
      agent level acc mb invs fi ⦃ res =>
      (res.2 = true ↔ mbStart = true ∨ ∃ inv ∈ invs.items.val, invMissing st inv) ∧
      (res.1.denied = true ↔ accStart.denied = true ∨
        ∃ inv ∈ invs.items.val, invDenied st bg level cgOf ovOf ocOf inv) ∧
      (∀ k, vsMem res.1.to_consume k ↔ vsMem accStart.to_consume k ∨
        ∃ inv ∈ invs.items.val, invConsumed st bg level ovOf ocOf inv k) ∧
      res.1.to_consume.items.val.Nodup ⦄ := by
  unfold transitions.sentinel_elevate_taint_loop
  apply loop.spec_decr_nat
    (measure := fun p => invs.items.val.length - p.2.2.val)
    (inv := fun p => p.2.2.val ≤ invs.items.val.length ∧ p.1.to_consume.items.val.Nodup ∧
      p.1.to_consume.items.val.length ≤ accStart.to_consume.items.val.length + p.2.2.val ∧
      (p.2.1 = true ↔ mbStart = true ∨
        ∃ inv ∈ invs.items.val.take p.2.2.val, invMissing st inv) ∧
      (p.1.denied = true ↔ accStart.denied = true ∨
        ∃ inv ∈ invs.items.val.take p.2.2.val, invDenied st bg level cgOf ovOf ocOf inv) ∧
      (∀ k, vsMem p.1.to_consume k ↔ vsMem accStart.to_consume k ∨
        ∃ inv ∈ invs.items.val.take p.2.2.val, invConsumed st bg level ovOf ocOf inv k))
  · rintro ⟨accL, mbL, iL⟩ ⟨hile, hndL, hlenL, hmbL, hdenL, hconL⟩
    dsimp only at hile hndL hlenL hmbL hdenL hconL ⊢
    simp only [transitions.sentinel_elevate_taint_loop.body, collections.VecSet.len,
      collections.VecSet.at, bind_tc_ok]
    split
    case isTrue h =>
      have hlt : iL.val < invs.items.val.length := by scalar_tac
      step as ⟨inv, hinv⟩
      -- prefix-extension lemma for `∃ over take`
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
      -- read the bound tool (last-match `invocation_tool`)
      obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
        (vecMapGetCloned_spec types.InvocationId.Insts.CoreCloneClone
          types.InvocationId.Insts.CoreCmpPartialEqInvocationId invocationId_eq_spec
          types.ToolId.Insts.CoreCloneClone toolId_clone_spec st.invocation_tool inv)
      rw [hoEq]; simp only [bind_tc_ok]
      have hoInv : o = invToolC st inv := by rw [ho]; rfl
      cases hocase : o with
      | none =>
        -- missing binding: acc unchanged, mb := true
        rw [hocase] at hoInv
        have hmiss : invMissing st inv := hoInv.symm
        have hndd : ¬ invDenied st bg level cgOf ovOf ocOf inv := not_invDenied_missing hmiss
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, hndL, by scalar_tac, ?_, ?_, ?_, by scalar_tac⟩
        · rw [hi2 _ fi1_post]
          refine iff_of_true ?_ (Or.inr ((hext (invMissing st)).mpr (Or.inr hmiss)))
          trivial
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
        have hnmiss : ¬ invMissing st inv := by rw [invMissing, hsome]; simp
        simp only [bind_tc_ok]
        obtain ⟨tmeta, hmetaEq, hmeta⟩ := spec_imp_exists (toolMetadata_spec bg tool)
        rw [hmetaEq]; simp only [bind_tc_ok]
        have hcapAcc : accL.to_consume.items.val.length < Usize.max := by
          have := hlenL; have := hlt; have := hcapS; omega
        -- the kernel rebuilds the state record from `st`'s fields; it is `st` (structure eta)
        have hst : ((⟨st.agent_active, st.agent_parent, st.agent_cap, st.taint_levels,
            st.in_flight, st.invocation_tool, st.tool_registered, st.gh_taint_invoked,
            st.gh_taint_received, st.agent_instruction, st.override_used,
            st.agent_budget⟩ : state.KernelState)) = st := by cases st; rfl
        -- The remaining body, once the egress set `eg` is fixed (`hegItems`). Proven inline per
        -- egress case (no shared WP `have` — restating the loop's `match`-post compiles to a
        -- different matcher than the goal's, so `exact` would fail on defeq).
        have htail : ∀ (eg : collections.VecSet types.EgressKind),
            eg.items.val = egItems bg tool →
            iL.val < invs.items.val.length →
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
          intro eg hegItems hlt'
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
        -- discharge the egress `match` by cases, feeding the per-case egress set to `htail`
        cases htm : tmeta with
        | none =>
          simp only [collections.VecSet.new, bind_tc_ok]
          rw [hst]
          obtain ⟨acc2, hacc2Eq, hNd2, hlen2, hDen2, hCon2⟩ := spec_imp_exists
            (htail ⟨alloc.vec.Vec.new types.EgressKind⟩ (by simp [egItems, ← hmeta, htm]) hlt)
          rw [hacc2Eq]; simp only [bind_tc_ok]; step*
          exact ⟨by scalar_tac, hNd2,
            by rw [show fi1.val = iL.val + 1 from fi1_post]; exact hlen2,
            by rw [hi2 _ fi1_post, hext (invMissing st), hmbL]
               exact ⟨fun h => h.imp_right Or.inl, fun h => h.elim (fun hs => Or.inl hs)
                 (fun h => h.elim Or.inr (fun hc => absurd hc hnmiss))⟩,
            by rw [hi2 _ fi1_post]; exact hDen2,
            by intro k; rw [hi2 _ fi1_post]; exact hCon2 k, by scalar_tac⟩
        | some m =>
          simp only [bind_tc_ok]
          rw [vecSetClone_spec types.EgressKind.Insts.CoreCloneClone egressKind_clone_spec m.egress]
          simp only [bind_tc_ok]
          rw [hst]
          obtain ⟨acc2, hacc2Eq, hNd2, hlen2, hDen2, hCon2⟩ := spec_imp_exists
            (htail m.egress (by simp [egItems, ← hmeta, htm]) hlt)
          rw [hacc2Eq]; simp only [bind_tc_ok]; step*
          exact ⟨by scalar_tac, hNd2,
            by rw [show fi1.val = iL.val + 1 from fi1_post]; exact hlen2,
            by rw [hi2 _ fi1_post, hext (invMissing st), hmbL]
               exact ⟨fun h => h.imp_right Or.inl, fun h => h.elim (fun hs => Or.inl hs)
                 (fun h => h.elim Or.inr (fun hc => absurd hc hnmiss))⟩,
            by rw [hi2 _ fi1_post]; exact hDen2,
            by intro k; rw [hi2 _ fi1_post]; exact hCon2 k, by scalar_tac⟩
    case isFalse h =>
      have heq' : iL.val = invs.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hmbL hdenL hconL ⊢
      exact ⟨hmbL, hdenL, hconL, hndL⟩
  · exact ⟨hfi, hnd, hlen, hmb, hden, hcon⟩

end ArgusLean.Refinement
