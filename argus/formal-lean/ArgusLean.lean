-- The Aeneas-extracted argus-kernel model (do not edit Generated/).
import ArgusLean.Generated.ArgusKernel
-- Coexistence smoke test: spec + extracted model build in one scope.
import ArgusLean.Smoke
-- Layer 1: unified R + per-action R-preservation (12/12) + kernelStep/absActionOf dispatch bundle.
-- Transitively pulls the per-action Preservation proofs + the bridging foundation
-- (Bridging/: Collections, StateRelation, FlowBridging, FlowOracle).
import ArgusLean.Refinement.Unified.Bundle
-- Layer 2: init refinement + forward simulation + end-to-end soundness (implementation_sound).
import ArgusLean.Refinement.Unified.Soundness
-- See README.md for the module map and the trust base.
