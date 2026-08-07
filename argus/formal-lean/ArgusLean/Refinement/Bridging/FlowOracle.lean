import ArgusLean.Refinement.Bridging.FlowBridging

/-! # Refinement — confidentiality flow reads (V4 ceiling bands)

The V4 flow gate is two per-egress confidentiality ceilings (`allow_ceiling` / `inspect_ceiling`)
read as ALLOW / INSPECT bands. `background.flow_allows` / `flow_inspects` are the concrete Bool
reads (a `VecMap.get_cloned` last-match, absent ⇒ deny), matching the abstract band tests
`St.flow_allows` / `St.flow_inspects` (`ceilingAdmits` over the same ceiling fields). This module
pins:

* `EgressKind` equality / clone (nullary enum, *proved*, no extractor trust);
* the pure confidentiality order `confLeC` and `ConfLevel.le`'s spec;
* the pure ceiling reads `ceilC` / `ceilAdmitsC` (the `@[irreducible] ceilingAdmits` discipline is
  kept on the abstract side; the concrete side is a plain last-match band test);
* `flowAllows_spec` / `flowInspects_spec`, bridging the two background Bool reads to `ceilAdmitsC`.

There is no `FlowMode`, no content-gate oracle, no single-use flow override, and no per-tool
background metadata in V4: tool policy is the per-invocation frozen `ActionPolicySnapshot`, and
inspection/conformance are one-use attestation DATA. The per-check gate-loop bridging
(`check_flow` / `check_integ` / `check_clearance` / `check_capability`) is developed with the
`begin_invocation` preservation proof. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-! ## `EgressKind` equality and clone -/

deriving instance DecidableEq for types.EgressKind

/-- `EgressKind.eq` faithful decidable equality (nullary enum). -/
@[simp] theorem egressKind_eq_spec (a b : types.EgressKind) :
    types.EgressKind.Insts.CoreCmpPartialEqEgressKind.eq a b = .ok (decide (a = b)) := by
  cases a <;> cases b <;>
    simp [types.EgressKind.Insts.CoreCmpPartialEqEgressKind.eq, types.EgressKind.read_discriminant]

/-- `EgressKind.clone` is the identity (nullary enum). -/
@[simp] theorem egressKind_clone_spec (a : types.EgressKind) :
    types.EgressKind.Insts.CoreCloneClone.clone a = .ok a := rfl

/-! ## `ConfLevel.le` (transparent confidentiality order) -/

/-- The pure rank-compare behind `ConfLevel::le` (the kernel's trait-free total order). -/
def confLeC (a b : types.ConfLevel) : Bool :=
  match a, b with
  | .Public, _ => true
  | .Internal, .Public => false
  | .Internal, _ => true
  | .Sensitive, .Public => false
  | .Sensitive, .Internal => false
  | .Sensitive, _ => true
  | .Restricted, .Restricted => true
  | .Restricted, _ => false

/-- `ConfLevel.le` is total and computes `confLeC` (16-case rank compare). -/
@[simp] theorem confLevel_le_spec (a b : types.ConfLevel) :
    types.ConfLevel.le a b = .ok (confLeC a b) := by
  cases a <;> cases b <;> rfl

/-! ## Ceiling-band reads -/

/-- The live ceiling for `E` in a per-egress ceiling map (last-match `get_cloned` read). -/
def ceilC (m : collections.VecMap types.EgressKind types.ConfLevel) (E : types.EgressKind) :
    Option types.ConfLevel :=
  (vmLastEntry m.entries.val E).map Prod.snd

/-- The pure band test: `level` is at or below `E`'s ceiling (absent ceiling admits nothing). -/
def ceilAdmitsC (m : collections.VecMap types.EgressKind types.ConfLevel)
    (level : types.ConfLevel) (E : types.EgressKind) : Bool :=
  match ceilC m E with
  | none => false
  | some c => confLeC level c

/-- `background.flow_allows` computes `ceilAdmitsC` over the allow ceiling (a last-match
    `get_cloned`, absent ⇒ deny, else the `ConfLevel.le` rank compare). -/
theorem flowAllows_spec (bg : background.BackgroundTheory) (level : types.ConfLevel)
    (E : types.EgressKind) :
    background.BackgroundTheory.flow_allows bg level E ⦃ b =>
      b = ceilAdmitsC bg.allow_ceiling level E ⦄ := by
  unfold background.BackgroundTheory.flow_allows
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGetCloned_spec types.EgressKind.Insts.CoreCloneClone
      types.EgressKind.Insts.CoreCmpPartialEqEgressKind egressKind_eq_spec
      types.ConfLevel.Insts.CoreCloneClone confLevel_clone_spec bg.allow_ceiling E)
  rw [hoEq]; simp only [bind_tc_ok]
  unfold ceilAdmitsC ceilC
  rw [← ho]
  cases o with
  | none => simp
  | some c => simp only [confLevel_le_spec, spec_ok]

/-- `background.flow_inspects` computes `ceilAdmitsC` over the inspect ceiling (dual of
    `flowAllows_spec`). -/
theorem flowInspects_spec (bg : background.BackgroundTheory) (level : types.ConfLevel)
    (E : types.EgressKind) :
    background.BackgroundTheory.flow_inspects bg level E ⦃ b =>
      b = ceilAdmitsC bg.inspect_ceiling level E ⦄ := by
  unfold background.BackgroundTheory.flow_inspects
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGetCloned_spec types.EgressKind.Insts.CoreCloneClone
      types.EgressKind.Insts.CoreCmpPartialEqEgressKind egressKind_eq_spec
      types.ConfLevel.Insts.CoreCloneClone confLevel_clone_spec bg.inspect_ceiling E)
  rw [hoEq]; simp only [bind_tc_ok]
  unfold ceilAdmitsC ceilC
  rw [← ho]
  cases o with
  | none => simp
  | some c => simp only [confLevel_le_spec, spec_ok]

end ArgusLean.Refinement

-- Trust-base audit. Beyond the three standard axioms and the `String`/id extractor primitives (via
-- `Collections`), nothing new: the `EgressKind`/`ConfLevel` eq/clone facts are PROVED (nullary
-- enums), and the ceiling reads reduce purely through `get_cloned`.
#print axioms ArgusLean.Refinement.flowAllows_spec
#print axioms ArgusLean.Refinement.flowInspects_spec
