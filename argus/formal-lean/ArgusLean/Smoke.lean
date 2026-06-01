import Tzimtzum
import ArgusLean.Generated.ArgusKernel

/-! # Coexistence smoke test (Phase C build prerequisite)

If this module elaborates, the Kav/Tzimtzum spec and the Aeneas-extracted
`argus-kernel` model build together in a single module scope under one
Lean v4.30.0 stable + mathlib v4.30.0 toolchain — no mathlib clash and no
`Aeneas.Std` / `noncomputable section` collision with the spec.

This is the mechanical prerequisite for the Phase C refinement proofs
(`ArgusLean/Refinement/`), each of which imports both the extracted model and
the spec to relate them. -/

-- Both namespaces resolve in one scope (not merely co-imported): the extracted
-- kernel's egress enum and the spec's confidentiality lattice.
example : argus_kernel.types.EgressKind → argus_kernel.types.EgressKind := id
example : Tzimtzum.ConfLevel → Tzimtzum.ConfLevel := id
example : Tzimtzum.KSt → Tzimtzum.KSt := id
