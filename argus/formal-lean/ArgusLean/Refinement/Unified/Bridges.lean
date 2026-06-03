import ArgusLean.Refinement.Unified.Relation

/-! # Layer 1 — shared bridges for per-action `R`-preservation

Small reused facts that connect the unified `R`'s field views to the forms the per-action `_ok_inv` /
`_refines` lemmas expose. Kept out of `Relation.lean` so the relation file stays a pure definition. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

/-- `bg.tool_metadata` is deterministic and computes `toolMetaC`, so a `.ok (some tm)` lookup pins
    `toolMetaC bg t = some tm`. Bridges `Rtool`'s `tool_metadata`-phrased clause to `R`'s
    `toolMetaC`-phrased `toolIssuer`/`toolFloor`/`toolBounded`/`toolCap` conjuncts. -/
theorem toolMetaC_of_metadata {bg : background.BackgroundTheory} {t : types.ToolId}
    {tm : background.ToolMetadata} (h : bg.tool_metadata t = .ok (some tm)) :
    toolMetaC bg t = some tm := by
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists (toolMetadata_spec bg t)
  rw [h] at hoEq
  rw [← ho]
  exact (Result.ok.inj hoEq).symm

end ArgusLean.Refinement
