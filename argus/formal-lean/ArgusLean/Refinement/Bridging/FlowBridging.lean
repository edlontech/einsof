import ArgusLean.Refinement.Bridging.Collections

/-! # Refinement — integrity-order bridging foundation

The V4 gate is the nine-check `begin_invocation` (`check_capability` / `check_clearance` /
`check_flow` / `check_integ` loops over a frozen `ActionPolicySnapshot` and the attested egress
set), and `authorize_inspected`'s live re-evaluation. There is no longer a `flow_decision` /
`gate_egress` / `integ_decision` primitive, no `FlowMode`, and no content-gate oracle: inspection and
conformance are one-use attestation DATA, not oracle relations (README "Reshaped refinement
assumptions"). The V3 flow/integrity graduated-gate machinery therefore no longer lives here; the
per-check loop bridging is developed with its preservation proof (`Preservation/BeginInvocation`,
`Preservation/AuthorizeInspected`).

What survives at this foundational layer is the pure integrity total order `integLeC`, the concrete
counterpart the abstract integrity atoms (`integ_allows` / `integ_inspects`) and the frozen-snapshot
floor comparisons are stated against — the dual of `confLeC` in `FlowOracle`. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result ControlFlow argus_kernel
open Aeneas.Std.WP

set_option Aeneas.Deprecated.progressWarning false
set_option maxHeartbeats 1000000

/-! ## `IntegLevel.le` (transparent integrity order)

Dual of `confLeC`, minus any ceiling map: the floor comparison is a transparent `IntegLevel.le`
rank compare, so unlike the confidentiality side there is nothing to hide behind `irreducible`. -/

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

end ArgusLean.Refinement
