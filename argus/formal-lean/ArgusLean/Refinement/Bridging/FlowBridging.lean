import ArgusLean.Refinement.Bridging.Collections

/-! # Refinement — flow/integrity-gate bridging foundation

Concrete-only bridging for the two graduated-gate primitives the egress/integrity-gated actions
(`invoke_start`, `return_unendorsed`, `sentinel_elevate_taint`, `sentinel_degrade_integrity`) share.
Everything here is stated purely over the extracted kernel (`flow_decision`, `gate_egress`,
`integ_decision`) and the underlying oracle/background *results* — no abstract `St` appears. The
abstract correspondence (oracle-agreement relation) is layered on top in `Unified/Relation.lean` and
the per-action assembly.

Two definitionally-independent instantiations of the same graduated ALLOW / INSPECT+vouch / DENY
shape (`tzimtzum/Tzimtzum/State.lean`'s "generic graduated gate" resolution):

* **Confidentiality** — `flow_decision` / `gate_egress`, over the `@[irreducible]` ceiling-map
  ALLOW/INSPECT bands (`ceilAdmitsC`, unchanged from the pre-V3 shape) plus the single-use flow
  override (`has_flow_override` / `override_consumed`). `flow_decision` is now a bare **two-way**
  `Allowed`/`Denied` result — eager override consumption (design "Override consumption semantics")
  is tracked by dedicated per-action loops downstream, not inside `flow_decision` itself, so the old
  V2 `ConsumedOverride` outcome and the `gate_egress` `to_consume` accumulator are both gone;
  `gate_egress` folds a monotone `denied : Bool` over a tool's egress set.
* **Integrity** — `integ_decision`, over the bare transparent `IntegLevel.le` floor comparison (no
  ceiling map to hide behind, so no `irreducible` discipline is needed — dual of `St.integ_allows` /
  `St.integ_inspects`). No override arm: endorsement is the only way up.

Both oracle calls (`ContentGateOracle.passes`) are now keyed by a `vouch_inv : InvocationId` — the
per-invocation verdict rekeying (`invocation_gate_passes`): the invocation being *vouched for*, not
necessarily the invocation being gated (CHECK 2b/4b vouch an in-flight invocation against a newly
examined floor).

Supporting collection facts: `overrideKey_eq_spec` (struct decidable equality, *proved*). -/

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

/-! ## `flow_decision` (confidentiality side) -/

/-- The `(level, E)`-pair denial condition: `Inspect`-mode with a failing content gate, or `Deny`-mode
    with no usable override. The complement (everything else) is what `flow_decision` now returns as
    a bare `Allowed` — there is no separate `ConsumedOverride` outcome in V3. -/
def egressDenied (fm : background.FlowMode) (cgVal ovVal ocVal : Bool) : Prop :=
  (fm = .Inspect ∧ cgVal = false) ∨ (fm = .Deny ∧ (ovVal = false ∨ ocVal = true))

/-- The two-way decision of `flow_decision`, fully determined by the four sub-oracle results:
    the `flow_mode` (`Allow`/`Inspect`/`Deny`), the content gate vouching `vouch_inv` (`cgVal`), the
    presence of a flow override (`ovVal`), and whether that override was already consumed (`ocVal`).
    Pure case analysis on the extracted body. -/
theorem flowDecision_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (bg : background.BackgroundTheory) (content_gate : C) (agent : types.AgentId)
    (tool : types.ToolId) (vouch_inv : types.InvocationId) (st : state.KernelState)
    (level : types.ConfLevel) (egress : types.EgressKind)
    (fmVal : background.FlowMode)
    (hfm : background.BackgroundTheory.flow_mode bg level egress = .ok fmVal)
    (cgVal : Bool) (hcg : cgInst.passes content_gate agent tool vouch_inv st bg = .ok cgVal)
    (ovVal : Bool) (hov : state.KernelState.has_flow_override st agent tool level = .ok ovVal)
    (ocVal : Bool) (hoc : state.KernelState.override_consumed st agent tool level = .ok ocVal) :
    transitions.flow_decision cgInst bg content_gate agent tool vouch_inv st level egress ⦃ fd =>
      (fd = .Denied ↔ egressDenied fmVal cgVal ovVal ocVal) ∧
      (fd = .Allowed ↔ ¬ egressDenied fmVal cgVal ovVal ocVal) ⦄ := by
  unfold transitions.flow_decision
  rw [hfm]
  simp only [bind_tc_ok]
  cases fmVal with
  | Allow => simp [spec_ok, egressDenied]
  | Inspect =>
    rw [hcg]; simp only [bind_tc_ok]
    cases cgVal <;> simp [spec_ok, egressDenied]
  | Deny =>
    rw [hov]; simp only [bind_tc_ok]
    cases ovVal with
    | false => simp [spec_ok, egressDenied]
    | true =>
      rw [hoc]; simp only [bind_tc_ok]
      cases ocVal <;> simp [spec_ok, egressDenied]

/-! ## `gate_egress`

Folds `flow_decision` over a tool's egress set, monotonically setting a `denied : Bool` accumulator
on any `Denied` egress (never cleared) — the V3 shape, no `to_consume` set. -/

/-- Generalised loop spec for `gate_egress_loop`. Relative to a fixed reference flag
    `deniedStart`, after scanning the prefix `[0, i)` the running flag is `deniedStart` extended by
    the per-egress `egressDenied` contributions over that prefix. -/
theorem gateEgressLoop_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (bg : background.BackgroundTheory) (content_gate : C) (agent : types.AgentId)
    (tool : types.ToolId) (vouch_inv : types.InvocationId) (st : state.KernelState)
    (level : types.ConfLevel) (egress_set : collections.VecSet types.EgressKind)
    (cgVal ovVal ocVal : Bool)
    (hcg : cgInst.passes content_gate agent tool vouch_inv st bg = .ok cgVal)
    (hov : state.KernelState.has_flow_override st agent tool level = .ok ovVal)
    (hoc : state.KernelState.override_consumed st agent tool level = .ok ocVal)
    (fmOf : types.EgressKind → background.FlowMode)
    (hfmOf : ∀ E, background.BackgroundTheory.flow_mode bg level E = .ok (fmOf E))
    (deniedStart : Bool) (denied : Bool) (i : Usize)
    (hi : i.val ≤ egress_set.items.val.length)
    (hden : denied = true ↔ deniedStart = true ∨
      ∃ E ∈ egress_set.items.val.take i.val, egressDenied (fmOf E) cgVal ovVal ocVal) :
    transitions.gate_egress_loop cgInst bg content_gate agent tool vouch_inv st level egress_set
        denied i ⦃ deniedF =>
      deniedF = true ↔ deniedStart = true ∨
        ∃ E ∈ egress_set.items.val, egressDenied (fmOf E) cgVal ovVal ocVal ⦄ := by
  unfold transitions.gate_egress_loop
  apply loop.spec_decr_nat
    (measure := fun p => egress_set.items.val.length - p.2.val)
    (inv := fun p => p.2.val ≤ egress_set.items.val.length ∧
      (p.1 = true ↔ deniedStart = true ∨
        ∃ E ∈ egress_set.items.val.take p.2.val, egressDenied (fmOf E) cgVal ovVal ocVal))
  · rintro ⟨deniedL, iL⟩ ⟨hile, hdenL⟩
    dsimp only at hile hdenL
    simp only [transitions.gate_egress_loop.body, collections.VecSet.len, collections.VecSet.at,
      bind_tc_ok]
    split
    case isTrue h =>
      have hlt : iL.val < egress_set.items.val.length := by scalar_tac
      step as ⟨e, he⟩
      obtain ⟨fd, hfdEq, hDenIff, hAllIff⟩ := spec_imp_exists
        (flowDecision_spec cgInst bg content_gate agent tool vouch_inv st level e (fmOf e)
          (hfmOf e) cgVal hcg ovVal hov ocVal hoc)
      rw [hfdEq]
      simp only [bind_tc_ok]
      have htk : (∃ E ∈ egress_set.items.val.take (iL.val + 1), egressDenied (fmOf E) cgVal ovVal ocVal)
          ↔ (∃ E ∈ egress_set.items.val.take iL.val, egressDenied (fmOf E) cgVal ovVal ocVal)
            ∨ egressDenied (fmOf e) cgVal ovVal ocVal := by
        simp only [List.take_add_one, List.getElem?_eq_getElem hlt, Option.toList_some,
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
          have := hDenIff.mpr hc; simp at this
        step*
        have hle : i2.val ≤ egress_set.items.val.length := by scalar_tac
        refine ⟨hle, ?_, by scalar_tac⟩
        rw [hi2 _ i2_post, htk, hdenL]
        apply Iff.intro
        · rintro (h | h)
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · rintro (h | h | h)
          · exact Or.inl h
          · exact Or.inr h
          · exact absurd h hnotDen
      | Denied =>
        have hden' : egressDenied (fmOf e) cgVal ovVal ocVal := hDenIff.mp rfl
        step*
        have hle : i2.val ≤ egress_set.items.val.length := by scalar_tac
        refine ⟨hle, ?_, by scalar_tac⟩
        rw [hi2 _ i2_post, htk]
        apply Iff.intro
        · intro _; exact Or.inr (Or.inr hden')
        · intro _; trivial
    case isFalse h =>
      have heq' : iL.val = egress_set.items.val.length := by scalar_tac
      simp only [spec_ok, heq', List.take_length] at hdenL ⊢
      exact hdenL
  · exact ⟨hi, hden⟩

/-- `gate_egress` started at `denied`: the post-flag over the whole egress set. The `i = 0` instance
    of `gateEgressLoop_spec` (empty prefix ⇒ the `∃` is vacuous and the flag coincides with
    `denied`). -/
theorem gateEgress_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (bg : background.BackgroundTheory) (content_gate : C) (agent : types.AgentId)
    (tool : types.ToolId) (vouch_inv : types.InvocationId) (st : state.KernelState)
    (level : types.ConfLevel) (egress_set : collections.VecSet types.EgressKind)
    (cgVal ovVal ocVal : Bool)
    (hcg : cgInst.passes content_gate agent tool vouch_inv st bg = .ok cgVal)
    (hov : state.KernelState.has_flow_override st agent tool level = .ok ovVal)
    (hoc : state.KernelState.override_consumed st agent tool level = .ok ocVal)
    (fmOf : types.EgressKind → background.FlowMode)
    (hfmOf : ∀ E, background.BackgroundTheory.flow_mode bg level E = .ok (fmOf E))
    (denied : Bool) :
    transitions.gate_egress cgInst bg content_gate agent tool vouch_inv st level egress_set
        denied ⦃ deniedF =>
      deniedF = true ↔ denied = true ∨
        ∃ E ∈ egress_set.items.val, egressDenied (fmOf E) cgVal ovVal ocVal ⦄ := by
  unfold transitions.gate_egress
  exact gateEgressLoop_spec cgInst bg content_gate agent tool vouch_inv st level egress_set
    cgVal ovVal ocVal hcg hov hoc fmOf hfmOf denied denied 0#usize (by simp) (by simp)

/-! ## `integ_decision` (integrity side)

Dual of `flow_decision`, minus the override arm: `IntegDecision` is (and was already, in V2's
absence of an integrity dimension) a bare two-way `Allowed`/`Denied`. No ceiling map — the floor
comparison is a transparent `IntegLevel.le` rank compare, so unlike the conf side there is nothing to
hide behind `irreducible`. -/

/-- The pure rank-compare behind `IntegLevel::le` (dual of `confLeC`). -/
def integLeC (a b : types.IntegLevel) : Bool :=
  match a, b with
  | .Untrusted, _ => true
  | .Standard, .Untrusted => false
  | .Standard, _ => true
  | .Trusted, .Untrusted => false
  | .Trusted, .Standard => false
  | .Trusted, _ => true
  | .Attested, .Attested => true
  | .Attested, _ => false

/-- `IntegLevel.le` is total and computes `integLeC` (16-case rank compare, dual of
    `confLevel_le_spec`). -/
@[simp] theorem integLevel_le_spec (a b : types.IntegLevel) :
    types.IntegLevel.le a b = .ok (integLeC a b) := by
  cases a <;> cases b <;> rfl

/-- The two-way decision of `integ_decision`: ALLOW iff the floor clears outright, or the inspect
    floor clears and the vouched invocation's content gate passes; DENY otherwise. Pure case analysis
    on the extracted body, no override arm. -/
theorem integDecision_spec {C : Type} (cgInst : traits.ContentGateOracle C)
    (content_gate : C) (agent : types.AgentId) (tool : types.ToolId)
    (vouch_inv : types.InvocationId) (st : state.KernelState) (bg : background.BackgroundTheory)
    (floor inspect_floor level : types.IntegLevel)
    (cgVal : Bool) (hcg : cgInst.passes content_gate agent tool vouch_inv st bg = .ok cgVal) :
    transitions.integ_decision cgInst content_gate agent tool vouch_inv st bg floor inspect_floor
        level ⦃ id =>
      (id = .Allowed ↔ (integLeC floor level = true
                          ∨ (integLeC inspect_floor level = true ∧ cgVal = true))) ∧
      (id = .Denied ↔ ¬ (integLeC floor level = true
                          ∨ (integLeC inspect_floor level = true ∧ cgVal = true))) ⦄ := by
  unfold transitions.integ_decision
  rw [integLevel_le_spec]
  simp only [bind_tc_ok]
  cases hf : integLeC floor level with
  | true => simp [spec_ok]
  | false =>
    simp only [Bool.false_eq_true, if_false]
    rw [integLevel_le_spec]
    simp only [bind_tc_ok]
    cases hi : integLeC inspect_floor level with
    | true =>
      simp only [if_true]
      rw [hcg]; simp only [bind_tc_ok]
      cases cgVal <;> simp [spec_ok]
    | false => simp [spec_ok]

end ArgusLean.Refinement

-- Trust-base audit. Beyond the three standard axioms, the only residuals are the `register_tool`
-- `String`/id extractor primitives (via `Collections`). The flow/integrity machinery
-- (`flow_decision`, `gate_egress`, `integ_decision`, the content-gate oracle) is reduced purely by
-- case analysis + loop induction; the `CapKind`/`ConfLevel`/`IntegLevel`/`OverrideKey` eq facts are
-- PROVED (nullary enums / structs), not trusted.
#print axioms ArgusLean.Refinement.flowDecision_spec
#print axioms ArgusLean.Refinement.gateEgress_spec
#print axioms ArgusLean.Refinement.integDecision_spec
