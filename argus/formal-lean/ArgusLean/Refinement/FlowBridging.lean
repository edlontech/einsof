import ArgusLean.Refinement.Collections

/-! # Refinement — flow-gate bridging foundation

Concrete-only bridging for the flow machinery that the egress-gated actions
(`sentinel_elevate_taint`, `invoke_start`, `return_*`) all share but none of the six completed
tree/attestation actions touch. Everything here is stated purely over the extracted kernel
(`flow_decision`, `gate_egress`, `GateAccum`) and the underlying oracle/background *results* — no
abstract `St` appears. The abstract correspondence (oracle-agreement relation) is layered on top in
the per-action assembly.

* `flowDecision_spec` — the three-way `Allowed` / `ConsumedOverride` / `Denied` characterisation of
  `flow_decision` in terms of the `flow_mode`, content-gate, `has_flow_override`, and
  `override_consumed` results.
* `gateEgress_spec` — the inner fold over a tool's egress set: the post-accumulator's `denied` flag
  and `to_consume` set, in terms of the per-egress `flow_decision`.

Supporting collection facts: `confLevel_eq_spec` / `overrideKey_eq_spec` (nullary-enum + struct
decidable equality, *proved*) and `vecSetInsertNodup_spec` (membership + `Nodup` preservation, with
the capacity side condition demanded only on the push path). -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option Aeneas.Deprecated.progressWarning false
set_option maxHeartbeats 4000000

/-! ## Decidable equality for `OverrideKey`

(`DecidableEq types.ConfLevel` + `confLevel_eq_spec` now live in `Collections`.) -/

deriving instance DecidableEq for types.OverrideKey

/-- `OverrideKey.eq` is faithful decidable equality: tool (`String`-backed) then level (enum). -/
@[simp] theorem overrideKey_eq_spec (a b : types.OverrideKey) :
    types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey.eq a b = .ok (decide (a = b)) := by
  obtain ⟨t1, l1⟩ := a; obtain ⟨t2, l2⟩ := b
  simp only [types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey.eq, toolId_eq_spec, bind_tc_ok]
  by_cases ht : t1 = t2
  · subst ht; simp [confLevel_eq_spec]
  · simp [ht]

/-! ## `VecSet.insert` with `Nodup` preservation -/

/-- `VecSet.insert` adds `x` (idempotently) and preserves `Nodup`. The capacity bound is required only
    on the push path (`x` absent) — `insert` is a no-op when `x` is already present, so a caller that
    only re-inserts existing elements needs no bound. -/
theorem vecSetInsertNodup_spec {T : Type} [DecidableEq T]
    (inst_c : core.clone.Clone T) (inst_eq : core.cmp.PartialEq T T)
    (heq : ∀ a b : T, inst_eq.eq a b = .ok (decide (a = b)))
    (vs : collections.VecSet T) (x : T)
    (hcap : x ∉ vs.items.val → vs.items.val.length < Usize.max) :
    collections.VecSet.insert inst_c inst_eq vs x ⦃ vs' =>
      (∀ y, vsMem vs' y ↔ vsMem vs y ∨ y = x) ∧
      (vs.items.val.Nodup → vs'.items.val.Nodup) ⦄ := by
  unfold collections.VecSet.insert
  obtain ⟨b, hcontains, hb⟩ :=
    spec_imp_exists (vecSetContains_spec inst_c inst_eq heq vs x)
  rw [hcontains]
  cases b with
  | true =>
    have hx : x ∈ vs.items.val := hb.mp rfl
    simp only [bind_tc_ok, reduceIte, spec_ok]
    refine ⟨fun y => ⟨Or.inl, ?_⟩, id⟩
    rintro (hy | rfl)
    · exact hy
    · exact hx
  | false =>
    have hx : x ∉ vs.items.val := fun hc => by have := hb.mpr hc; simp at this
    have hcap' : vs.items.val.length < Usize.max := hcap hx
    simp only [bind_tc_ok, Bool.false_eq_true, reduceIte]
    step*
    refine ⟨fun y => ?_, fun hnd => ?_⟩
    · simp only [vsMem, v_post, List.mem_append, List.mem_singleton]
    · simp only [v_post]
      rw [List.nodup_append]
      exact ⟨hnd, List.nodup_singleton x,
        fun a ha b hb hab => hx (by rw [List.mem_singleton] at hb; subst hab; subst hb; exact ha)⟩

/-! ## `flow_decision` -/

/-- The three-way decision of `flow_decision`, fully determined by the four sub-oracle results:
    the `flow_mode` (`Allow`/`Inspect`/`Deny`), the content gate (`cgVal`), the presence of a flow
    override (`ovVal`), and whether that override was already consumed (`ocVal`). Pure case analysis
    on the extracted body. -/
theorem flowDecision_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (bg : background.BackgroundTheory) (content_gate : C) (agent : types.AgentId)
    (tool : types.ToolId) (st : state.KernelState) (level : types.ConfLevel)
    (egress : types.EgressKind)
    (fmVal : background.FlowMode)
    (hfm : background.BackgroundTheory.flow_mode bg level egress = .ok fmVal)
    (cgVal : Bool) (hcg : cgInst.passes content_gate agent tool st bg = .ok cgVal)
    (ovVal : Bool) (hov : background.BackgroundTheory.has_flow_override bg agent tool level = .ok ovVal)
    (ocVal : Bool) (hoc : state.KernelState.override_consumed st agent tool level = .ok ocVal) :
    transitions.flow_decision cgInst bg content_gate agent tool st level egress ⦃ fd =>
      (fd = .Allowed ↔ (fmVal = .Allow ∨ (fmVal = .Inspect ∧ cgVal = true))) ∧
      (fd = .ConsumedOverride ↔ (fmVal = .Deny ∧ ovVal = true ∧ ocVal = false)) ∧
      (fd = .Denied ↔ ((fmVal = .Inspect ∧ cgVal = false)
                        ∨ (fmVal = .Deny ∧ (ovVal = false ∨ ocVal = true)))) ⦄ := by
  unfold transitions.flow_decision
  rw [hfm]
  simp only [bind_tc_ok]
  cases fmVal with
  | Allow => simp [spec_ok]
  | Inspect =>
    rw [hcg]; simp only [bind_tc_ok]
    cases cgVal <;> simp [spec_ok]
  | Deny =>
    rw [hov]; simp only [bind_tc_ok]
    cases ovVal with
    | false => simp [spec_ok]
    | true =>
      rw [hoc]; simp only [bind_tc_ok]
      cases ocVal <;> simp [spec_ok]

/-! ## `gate_egress`

The pure per-egress decision predicates extracted from `flowDecision_spec`. `egressDenied` is the
condition under which a `(level, E)` pair returns `Denied` (Inspect-mode with a failing content gate,
or Deny-mode with no usable override); `egressConsumed` is when it returns `ConsumedOverride` (Deny
with a fresh override). They are mutually exclusive (`flow_decision` returns exactly one variant). -/

/-- The `(level, E)`-pair denial condition: `Inspect`-mode with a failing content gate, or `Deny`-mode
    with no usable override. -/
def egressDenied (fm : background.FlowMode) (cgVal ovVal ocVal : Bool) : Prop :=
  (fm = .Inspect ∧ cgVal = false) ∨ (fm = .Deny ∧ (ovVal = false ∨ ocVal = true))

/-- The `(level, E)`-pair override-consumption condition: `Deny`-mode with a present, not-yet-consumed
    override. Independent of the content gate. -/
def egressConsumed (fm : background.FlowMode) (ovVal ocVal : Bool) : Prop :=
  fm = .Deny ∧ ovVal = true ∧ ocVal = false

/-- The `OverrideKey` that `gate_egress` inserts into `to_consume` whenever a pair consumes an
    override: always the loop's `(tool, level)`. -/
abbrev gateConsumeKey (tool : types.ToolId) (level : types.ConfLevel) : types.OverrideKey :=
  { tool := tool, level := level }

/-- Generalised loop spec for `gate_egress_loop`. Relative to a fixed reference accumulator
    `accStart`, after scanning the prefix `[0, i)` the running accumulator's `denied` flag and
    `to_consume` set are exactly `accStart` extended by the per-egress `egressDenied` / `egressConsumed`
    contributions over that prefix; `to_consume` stays `Nodup`. The capacity bound on `accStart`'s set
    is all the inner `VecSet.insert` needs (the set only ever gains the single `gateConsumeKey`). -/
theorem gateEgressLoop_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (bg : background.BackgroundTheory) (content_gate : C) (agent : types.AgentId)
    (tool : types.ToolId) (st : state.KernelState) (level : types.ConfLevel)
    (egress_set : collections.VecSet types.EgressKind)
    (cgVal ovVal ocVal : Bool)
    (hcg : cgInst.passes content_gate agent tool st bg = .ok cgVal)
    (hov : background.BackgroundTheory.has_flow_override bg agent tool level = .ok ovVal)
    (hoc : state.KernelState.override_consumed st agent tool level = .ok ocVal)
    (fmOf : types.EgressKind → background.FlowMode)
    (hfmOf : ∀ E, background.BackgroundTheory.flow_mode bg level E = .ok (fmOf E))
    (accStart : transitions.GateAccum)
    (hcapS : accStart.to_consume.items.val.length < Usize.max)
    (acc : transitions.GateAccum) (i : Usize)
    (hi : i.val ≤ egress_set.items.val.length)
    (hnd : acc.to_consume.items.val.Nodup)
    (hden : acc.denied = true ↔ accStart.denied = true ∨
      ∃ E ∈ egress_set.items.val.take i.val, egressDenied (fmOf E) cgVal ovVal ocVal)
    (hcon : ∀ k, vsMem acc.to_consume k ↔ vsMem accStart.to_consume k ∨
      (k = gateConsumeKey tool level ∧
        ∃ E ∈ egress_set.items.val.take i.val, egressConsumed (fmOf E) ovVal ocVal)) :
    transitions.gate_egress_loop cgInst bg content_gate agent tool st level egress_set acc i ⦃ accF =>
      (accF.denied = true ↔ accStart.denied = true ∨
        ∃ E ∈ egress_set.items.val, egressDenied (fmOf E) cgVal ovVal ocVal) ∧
      (∀ k, vsMem accF.to_consume k ↔ vsMem accStart.to_consume k ∨
        (k = gateConsumeKey tool level ∧
          ∃ E ∈ egress_set.items.val, egressConsumed (fmOf E) ovVal ocVal)) ∧
      accF.to_consume.items.val.Nodup ⦄ := by
  unfold transitions.gate_egress_loop
  apply loop.spec_decr_nat
    (measure := fun p => egress_set.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ egress_set.items.val.length ∧ p.1.to_consume.items.val.Nodup ∧
      (p.1.denied = true ↔ accStart.denied = true ∨
        ∃ E ∈ egress_set.items.val.take p.2.val, egressDenied (fmOf E) cgVal ovVal ocVal) ∧
      (∀ k, vsMem p.1.to_consume k ↔ vsMem accStart.to_consume k ∨
        (k = gateConsumeKey tool level ∧
          ∃ E ∈ egress_set.items.val.take p.2.val, egressConsumed (fmOf E) ovVal ocVal)))
  · rintro ⟨accL, iL⟩ ⟨hile, hndL, hdenL, hconL⟩
    dsimp only at hile hndL hdenL hconL
    simp only [transitions.gate_egress_loop.body, collections.VecSet.len, collections.VecSet.at,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : iL.val < egress_set.items.val.length := by scalar_tac
      step as ⟨e, he⟩
      obtain ⟨fd, hfdEq, hAll, hCons, hDen⟩ := spec_imp_exists
        (flowDecision_spec cgInst bg content_gate agent tool st level e (fmOf e) (hfmOf e)
          cgVal hcg ovVal hov ocVal hoc)
      rw [hfdEq]
      simp only [bind_tc_ok]
      -- prefix-extension rewrites for the two `∃`-over-`take` characterisations
      have htkD : (∃ E ∈ egress_set.items.val.take (iL.val + 1), egressDenied (fmOf E) cgVal ovVal ocVal)
          ↔ (∃ E ∈ egress_set.items.val.take iL.val, egressDenied (fmOf E) cgVal ovVal ocVal)
            ∨ egressDenied (fmOf e) cgVal ovVal ocVal := by
        simp only [List.take_succ, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨E, hE | hE, hPE⟩
          · exact Or.inl ⟨E, hE, hPE⟩
          · subst hE; rw [he]; exact Or.inr hPE
        · rintro (⟨E, hE, hPE⟩ | hPe)
          · exact ⟨E, Or.inl hE, hPE⟩
          · exact ⟨e, Or.inr he, hPe⟩
      have htkC : (∃ E ∈ egress_set.items.val.take (iL.val + 1), egressConsumed (fmOf E) ovVal ocVal)
          ↔ (∃ E ∈ egress_set.items.val.take iL.val, egressConsumed (fmOf E) ovVal ocVal)
            ∨ egressConsumed (fmOf e) ovVal ocVal := by
        simp only [List.take_succ, List.getElem?_eq_getElem hlt, Option.toList_some,
          List.mem_append, List.mem_singleton]
        constructor
        · rintro ⟨E, hE | hE, hPE⟩
          · exact Or.inl ⟨E, hE, hPE⟩
          · subst hE; rw [he]; exact Or.inr hPE
        · rintro (⟨E, hE, hPE⟩ | hPe)
          · exact ⟨E, Or.inl hE, hPE⟩
          · exact ⟨e, Or.inr he, hPe⟩
      have hi2 : ∀ (i2 : Usize), i2.val = iL.val + 1 →
          egress_set.items.val.take i2.val = egress_set.items.val.take (iL.val + 1) := by
        intro i2 h2; rw [h2]
      cases fd with
      | Allowed =>
        have hnotDen : ¬ egressDenied (fmOf e) cgVal ovVal ocVal := fun hc => by
          have := hDen.mpr hc; simp at this
        have hnotCons : ¬ egressConsumed (fmOf e) ovVal ocVal := fun hc => by
          have := hCons.mpr hc; simp at this
        step*
        refine ⟨by scalar_tac, hndL, ?_, ?_, by scalar_tac⟩
        · rw [hi2 _ i2_post, htkD, hdenL]
          exact ⟨fun h => h.imp_right Or.inl, fun h => h.imp_right (·.resolve_right hnotDen)⟩
        · intro k; rw [hi2 _ i2_post, htkC, hconL k]
          exact ⟨fun h => h.imp_right (And.imp_right Or.inl),
                 fun h => h.imp_right (And.imp_right (·.resolve_right hnotCons))⟩
      | ConsumedOverride =>
        have hcons : egressConsumed (fmOf e) ovVal ocVal := hCons.mp rfl
        have hnotDen : ¬ egressDenied (fmOf e) cgVal ovVal ocVal := fun hc => by
          have := hDen.mpr hc; simp at this
        obtain ⟨vs, hvsEq, hvsMem, hvsNd⟩ := spec_imp_exists
          (vecSetInsertNodup_spec types.OverrideKey.Insts.CoreCloneClone
            types.OverrideKey.Insts.CoreCmpPartialEqOverrideKey overrideKey_eq_spec
            accL.to_consume (gateConsumeKey tool level)
            (by intro hnotmem
                have hsubS : accL.to_consume.items.val ⊆ accStart.to_consume.items.val := by
                  intro k hk
                  rcases (hconL k).mp hk with hk' | ⟨hkk, _⟩
                  · exact hk'
                  · exact absurd (hkk ▸ hk) hnotmem
                have hle := (List.Nodup.subperm hndL hsubS).length_le
                scalar_tac))
        rw [toolId_clone_spec, bind_tc_ok, hvsEq]
        simp only [bind_tc_ok]
        step*
        refine ⟨by scalar_tac, hvsNd hndL, ?_, ?_, by scalar_tac⟩
        · rw [hi2 _ i2_post, htkD, hdenL]
          exact ⟨fun h => h.imp_right Or.inl, fun h => h.imp_right (·.resolve_right hnotDen)⟩
        · intro k; rw [hi2 _ i2_post, htkC, hvsMem k, hconL k]
          constructor
          · rintro ((hs | ⟨hk, _⟩) | hk)
            · exact Or.inl hs
            · exact Or.inr ⟨hk, Or.inr hcons⟩
            · exact Or.inr ⟨hk, Or.inr hcons⟩
          · rintro (hs | ⟨hk, _⟩)
            · exact Or.inl (Or.inl hs)
            · exact Or.inr hk
      | Denied =>
        have hden' : egressDenied (fmOf e) cgVal ovVal ocVal := hDen.mp rfl
        have hnotCons : ¬ egressConsumed (fmOf e) ovVal ocVal := fun hc => by
          have := hCons.mpr hc; simp at this
        step*
        refine ⟨by scalar_tac, hndL, ?_, ?_, by scalar_tac⟩
        · rw [hi2 _ i2_post, htkD]
          exact ⟨fun _ => Or.inr (Or.inr hden'), fun _ => by trivial⟩
        · intro k; rw [hi2 _ i2_post, htkC, hconL k]
          exact ⟨fun h => h.imp_right (And.imp_right Or.inl),
                 fun h => h.imp_right (And.imp_right (·.resolve_right hnotCons))⟩
    case isFalse h =>
      have heq' : iL.val = egress_set.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hdenL hconL ⊢
      exact ⟨hdenL, hconL, hndL⟩
  · exact ⟨hi, hnd, hden, hcon⟩

/-- `gate_egress` started at `acc`: the post-accumulator's `denied`/`to_consume` over the whole egress
    set. The `i = 0` instance of `gateEgressLoop_spec` (empty prefix ⇒ the `∃` are vacuous and the
    accumulator coincides with `acc`). -/
theorem gateEgress_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (bg : background.BackgroundTheory) (content_gate : C) (agent : types.AgentId)
    (tool : types.ToolId) (st : state.KernelState) (level : types.ConfLevel)
    (egress_set : collections.VecSet types.EgressKind)
    (cgVal ovVal ocVal : Bool)
    (hcg : cgInst.passes content_gate agent tool st bg = .ok cgVal)
    (hov : background.BackgroundTheory.has_flow_override bg agent tool level = .ok ovVal)
    (hoc : state.KernelState.override_consumed st agent tool level = .ok ocVal)
    (fmOf : types.EgressKind → background.FlowMode)
    (hfmOf : ∀ E, background.BackgroundTheory.flow_mode bg level E = .ok (fmOf E))
    (acc : transitions.GateAccum)
    (hcap : acc.to_consume.items.val.length < Usize.max)
    (hnd : acc.to_consume.items.val.Nodup) :
    transitions.gate_egress cgInst bg content_gate agent tool st level egress_set acc ⦃ accF =>
      (accF.denied = true ↔ acc.denied = true ∨
        ∃ E ∈ egress_set.items.val, egressDenied (fmOf E) cgVal ovVal ocVal) ∧
      (∀ k, vsMem accF.to_consume k ↔ vsMem acc.to_consume k ∨
        (k = gateConsumeKey tool level ∧
          ∃ E ∈ egress_set.items.val, egressConsumed (fmOf E) ovVal ocVal)) ∧
      accF.to_consume.items.val.Nodup ⦄ := by
  unfold transitions.gate_egress
  exact gateEgressLoop_spec cgInst bg content_gate agent tool st level egress_set
    cgVal ovVal ocVal hcg hov hoc fmOf hfmOf acc hcap acc 0#usize (by simp) hnd
    (by simp) (by simp [vsMem])

end ArgusLean.Refinement

-- Trust-base audit. Beyond the three standard axioms, the only residuals are the `register_tool`
-- `String`/id extractor primitives (via `Collections`). The flow machinery (`flow_decision`,
-- `gate_egress`, the content-gate oracle) is reduced purely by case analysis + loop induction; the
-- `CapKind`/`ConfLevel`/`OverrideKey` eq facts are PROVED (nullary enums / structs), not trusted.
#print axioms ArgusLean.Refinement.flowDecision_spec
#print axioms ArgusLean.Refinement.gateEgress_spec
