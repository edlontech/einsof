import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `register_tool` preserves the unified `R`

`register_tool` writes only `tool_registered` (a `VecSet`), framing every other field as a record
update `{ st with tool_registered := vs }`. So all of `R`'s conjuncts except `tool_reg` transport by
definitional reduction of the record projection (and the nested-map `vmNodupKeys` invariants carry over
because those maps are untouched). The combined inversion `register_tool_inv_full` exposes the full
structural frame (which `register_tool_ok_inv` substitutes away). -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Comprehensive inversion: like `register_tool_ok_inv` but keeps the structural post-state
    `st' = { st with tool_registered := vs }` (and the membership characterisation of `vs`). -/
theorem register_tool_inv_full
    (st : state.KernelState) (bg : background.BackgroundTheory) (tool : types.ToolId)
    (hcap : st.tool_registered.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.register_tool st bg tool = .ok (.Ok (st', ev))) :
    ∃ toolMeta vs,
      bg.tool_metadata tool = .ok (some toolMeta) ∧
      vsMem bg.trusted_issuers toolMeta.issuer ∧
      ¬ vsMem st.tool_registered tool ∧
      st' = { st with tool_registered := vs } ∧
      (∀ y, vsMem vs y ↔ vsMem st.tool_registered y ∨ y = tool) := by
  simp only [transitions.register_tool] at hok
  obtain ⟨metaOpt, hMetaEq⟩ : ∃ o, bg.tool_metadata tool = .ok o := by
    cases h : bg.tool_metadata tool with
    | ok o => exact ⟨o, rfl⟩
    | fail e => rw [h] at hok; simp at hok
    | div => rw [h] at hok; simp at hok
  rw [hMetaEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨toolMeta, rfl⟩ : ∃ tm, metaOpt = some tm := by
    cases metaOpt with
    | none => simp at hok
    | some tm => exact ⟨tm, rfl⟩
  simp only [issuerId_clone_spec, bind_tc_ok] at hok
  obtain ⟨issuerTrusted, hIssuerTrustedEq, hIssuerTrustedIff⟩ :=
    spec_imp_exists (isTrustedIssuer_spec bg toolMeta.issuer)
  rw [hIssuerTrustedEq] at hok
  simp only [bind_tc_ok] at hok
  have hTrusted : issuerTrusted = true := by
    cases issuerTrusted with
    | true => rfl
    | false => simp at hok
  simp only [hTrusted, reduceIte] at hok
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
  refine ⟨toolMeta, registeredAfter, hMetaEq, hIssuerTrustedIff.mp hTrusted, ?_, hStateEq.symm,
    hInsertMem⟩
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
    (hok : transitions.register_tool st bg tool = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.register_tool tool).guard a ∧
          (Tzimtzum.register_tool tool).next a a' ∧ R st' bg a' := by
  obtain ⟨toolMeta, vs, hMeta, hIssuerTrusted, hNotRegistered, rfl, hNewReg⟩ :=
    register_tool_inv_full st bg tool hcap st' ev hok
  refine ⟨{ a with tool_registered := fun T => a.tool_registered T ∨ T = tool }, ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.register_tool]
    refine ⟨?_, ?_⟩
    · rw [hR.tool_reg]; exact hNotRegistered
    · rw [hR.toolIssuer tool toolMeta (toolMetaC_of_metadata hMeta), hR.trustedIss]
      exact hIssuerTrusted
  · -- next
    simp [Tzimtzum.register_tool]
  · -- R st' bg a' — every field but tool_reg transports definitionally (record update)
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.cap_grantov, hR.active, ?_, hR.parent,
      hR.cap, hR.instr,
      hR.taint, hR.inflight, hR.ghInvoked, hR.ghReceived, hR.override, hR.budget, hR.toolCap,
      hR.toolEgress, hR.toolFloor, hR.toolBounded, hR.toolIssuer, hR.trustedIss, hR.instrIssuer,
      hR.flowAllows, hR.flowInspects, hR.flowOverride, hR.invTool, hR.ndParent, hR.ndCap, hR.ndInstr,
      hR.ndTaint, hR.ndInflight, hR.ndGhInvoked, hR.ndGhReceived, hR.ndOverride, hR.ndFlowOverride,
      hR.ndBudget, hR.wfInflight⟩
    -- tool_reg
    intro t
    show (a.tool_registered t ∨ t = tool) ↔ vsMem _ t
    rw [hNewReg t, hR.tool_reg t]

end ArgusLean.Refinement
