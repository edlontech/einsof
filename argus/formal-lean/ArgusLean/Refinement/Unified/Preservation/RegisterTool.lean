import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `register_tool` preserves the unified `R` (V4)

The V4 `register_tool` has no issuer guard (`ToolId` is the composite exact identity): it writes only
`tool_registered` (a `VecSet`), framing every other field as a record update
`{ st with tool_registered := vs }`. Every `R` conjunct except `tool_reg` transports by definitional
reduction of the record projection, and the nested-map `vmNodupKeys` invariants carry over because
those maps are untouched. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Inversion: `register_tool` succeeds iff `tool` was unregistered, and then the post-state is the
    record update inserting `tool` into `tool_registered`. -/
theorem register_tool_inv_full
    (st : state.KernelState) (tool : types.ToolId)
    (hcap : st.tool_registered.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.register_tool st tool = .ok (.Ok (st', ev))) :
    ∃ vs,
      ¬ vsMem st.tool_registered tool ∧
      st' = { st with tool_registered := vs } ∧
      (∀ y, vsMem vs y ↔ vsMem st.tool_registered y ∨ y = tool) := by
  simp only [transitions.register_tool] at hok
  obtain ⟨alreadyRegistered, hContainsEq, hContainsIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.ToolId.Insts.CoreCloneClone
      types.ToolId.Insts.CoreCmpPartialEqToolId toolId_eq_spec st.tool_registered tool)
  rw [hContainsEq] at hok
  simp only [bind_tc_ok] at hok
  have hNotReg : alreadyRegistered = false := by
    cases alreadyRegistered with
    | false => rfl
    | true => simp at hok
  simp only [hNotReg, reduceIte, Bool.false_eq_true] at hok
  simp only [toolId_clone_spec, bind_tc_ok] at hok
  obtain ⟨registeredAfter, hInsertEq, hInsertMem⟩ :=
    spec_imp_exists (vecSetInsert_spec types.ToolId.Insts.CoreCloneClone
      types.ToolId.Insts.CoreCmpPartialEqToolId toolId_eq_spec st.tool_registered tool hcap)
  rw [hInsertEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _hEventEq⟩ := hok
  refine ⟨registeredAfter, ?_, hStateEq.symm, hInsertMem⟩
  intro hmem
  have hc := hContainsIff.mpr hmem
  rw [hNotReg] at hc
  exact Bool.false_ne_true hc

/-- `register_tool` preserves the unified `R`. -/
theorem register_tool_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (tool : types.ToolId)
    (hR : R st bg a)
    (hcap : st.tool_registered.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.register_tool st tool = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.register_tool tool).guard a ∧
          (Tzimtzum.register_tool tool).next a a' ∧ R st' bg a' := by
  obtain ⟨vs, hNotRegistered, rfl, hNewReg⟩ := register_tool_inv_full st tool hcap st' ev hok
  refine ⟨{ a with tool_registered := fun T => a.tool_registered T ∨ T = tool }, ?_, ?_, ?_⟩
  · -- guard: `¬ a.tool_registered tool`
    simp only [Tzimtzum.register_tool]
    rw [hR.tool_reg]; exact hNotRegistered
  · -- next
    simp [Tzimtzum.register_tool]
  · -- R st' bg a' — every field but tool_reg transports definitionally (record update)
    refine ⟨hR.root, hR.mode, hR.active, ?_, hR.parent, hR.cap, hR.taint, hR.integ, hR.pending,
      hR.challenges, hR.grants, hR.consumedIds, hR.consumedAtt, hR.consumedCross, hR.flowAllows,
      hR.flowInspects, hR.ndParent, hR.ndCap, hR.ndTaint, hR.ndInteg, hR.ndPending, hR.ndChallenges,
      hR.ndGrants⟩
    -- tool_reg
    intro t
    show (a.tool_registered t ∨ t = tool) ↔ vsMem _ t
    rw [hNewReg t, hR.tool_reg t]

end ArgusLean.Refinement
