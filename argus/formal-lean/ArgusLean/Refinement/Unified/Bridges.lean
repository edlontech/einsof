import ArgusLean.Refinement.Unified.Relation

/-! # Layer 1 — shared bridges for per-action `R`-preservation

Small reused facts that connect the unified `R`'s field views to the forms the per-action
preservation lemmas expose. Kept out of `Relation.lean` so the relation file stays a pure definition.

The V3 economy bridges (`toolMetaC_of_metadata`, `debitBudget_full`, `creditBudget_full`) are gone
with the declassification budget and per-tool background metadata. The V4 frame bridges for the
struct-valued writes (`pending` / `challenges` / `crossing_grants`) are developed alongside their
preservation proofs. What survives here is the mirrored integrity-order compare used wherever the
concrete side of a floor guard is the abstracted level. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel

/-- `le_integ` with the abstracted concrete level on the LEFT is the kernel's rank compare —
    the mirrored companion of `le_integ_integLeC`, for floor guards where the concrete side is the
    floor. -/
theorem le_integ_integLeC' (c : types.IntegLevel) (L : Tzimtzum.IntegLevel) :
    Tzimtzum.le_integ (integA c) L ↔ integLeC c (integC L) = true := by
  cases c <;> cases L <;> simp [Tzimtzum.le_integ, Tzimtzum.integRank, integA, integC, integLeC]

end ArgusLean.Refinement
