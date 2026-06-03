-- The Aeneas-extracted argus-kernel model (do not edit Generated/).
import ArgusLean.Generated.ArgusKernel
-- Coexistence smoke test: spec + extracted model build in one scope.
import ArgusLean.Smoke
-- Layer 1: unified R + per-action R-preservation (12/12) + kernelStep/absActionOf dispatch bundle.
-- Transitively pulls the whole per-action layer (Actions/*, Simulation) + the bridging foundation
-- (Collections, StateRelation, FlowBridging, ReturnUnendorsedFlow).
import ArgusLean.Refinement.Unified.Bundle
-- Layer 2: init refinement + forward simulation + end-to-end soundness (implementation_sound).
import ArgusLean.Refinement.Unified.Soundness
-- See README.md for the module map and the trust base.
