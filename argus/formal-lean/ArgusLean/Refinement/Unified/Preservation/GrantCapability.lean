import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `grant_capability` preserves the unified `R`

`grant_capability` writes only `agent_cap` (via `insert_into`), framing everything else. Same
insert-into shape as `load_instruction`; additionally the capability read-gate (`prnt` holds `cap`,
exposed as `vmsMem`) is bridged to `R`'s canonical `vmsMemLast` cap view via `R.ndCap`. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Comprehensive inversion: structural frame + last-match `agent_cap` membership + nodup post. -/
theorem grant_capability_inv_full
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (parent child : types.AgentId) (cap : capability.CapKind)
    (hcapE : st.agent_cap.entries.val.length < Usize.max)
    (hcapS : ∀ p ∈ st.agent_cap.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.grant_capability st bg parent child cap = .ok (.Ok (st', ev))) :
    ∃ vmAfter,
      vsMem st.agent_active parent ∧
      vsMem st.agent_active child ∧
      vmLastEntry st.agent_parent.entries.val child = some (child, parent) ∧
      vmsMem st.agent_cap parent cap ∧
      st' = { st with agent_cap := vmAfter } ∧
      (∀ N C, vmsMemLast vmAfter N C ↔ vmsMemLast st.agent_cap N C ∨ (N = child ∧ C = cap)) ∧
      (vmNodupKeys st.agent_cap → vmNodupKeys vmAfter) := by
  simp only [transitions.grant_capability] at hok
  obtain ⟨b, hbEq, hbIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active parent)
  rw [hbEq] at hok
  simp only [bind_tc_ok] at hok
  have hb : b = true := by cases b with | true => rfl | false => simp at hok
  simp only [hb, reduceIte] at hok
  obtain ⟨b1, hb1Eq, hb1Iff⟩ :=
    spec_imp_exists (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active child)
  rw [hb1Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb1 : b1 = true := by cases b1 with | true => rfl | false => simp at hok
  simp only [hb1, reduceIte] at hok
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGet_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.AgentId.Insts.CoreCloneClone st.agent_parent child)
  rw [hoEq] at hok
  simp only [bind_tc_ok] at hok
  obtain ⟨b2, hb2Eq, hb2Iff⟩ :
      ∃ bb, core.option.Option.Insts.CoreCmpPartialEqOption.ne
        (core.cmp.PartialEqShared types.AgentId.Insts.CoreCmpPartialEqAgentId) o (some parent) =
        .ok bb ∧ (bb = true ↔ o ≠ some parent) :=
    ⟨_, optionAgentId_ne_spec o (some parent), by simp⟩
  rw [hb2Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb2 : b2 = false := by cases b2 with | false => rfl | true => simp at hok
  simp only [hb2, reduceIte, Bool.false_eq_true] at hok
  have hoP : o = some parent := by
    by_contra hc
    have := hb2Iff.mpr hc; rw [hb2] at this; simp at this
  have hlast : vmLastEntry st.agent_parent.entries.val child = some (child, parent) := by
    have hoP' : (vmLastEntry st.agent_parent.entries.val child).map Prod.snd = some parent := by
      rw [← ho]; exact hoP
    cases hL : vmLastEntry st.agent_parent.entries.val child with
    | none => rw [hL] at hoP'; simp at hoP'
    | some p =>
      have hp1 : p.1 = child := vmLastEntry_fst _ _ _ hL
      rw [hL, Option.map_some] at hoP'
      obtain ⟨x, y⟩ := p
      simp only [Option.some_inj] at hoP'
      simp_all
  obtain ⟨b3, hb3Eq, hb3Imp⟩ := spec_imp_exists
    (vecMapKVecSetSetContains_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      capability.CapKind.Insts.CoreCloneClone capability.CapKind.Insts.CoreCmpPartialEqCapKind
      capKind_eq_spec capKind_clone_spec st.agent_cap parent cap)
  rw [hb3Eq] at hok
  simp only [bind_tc_ok] at hok
  have hb3 : b3 = true := by cases b3 with | true => rfl | false => simp at hok
  simp only [hb3, reduceIte] at hok
  simp only [agentId_clone_spec, bind_tc_ok] at hok
  obtain ⟨vm, hvmEq, hvmLast⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_vmLast_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      capability.CapKind.Insts.CoreCloneClone capability.CapKind.Insts.CoreCmpPartialEqCapKind
      capKind_eq_spec capKind_clone_spec st.agent_cap child cap hcapE hcapS)
  obtain ⟨vm2, hvm2Eq, hvm2nd⟩ := spec_imp_exists
    (vecMapKVecSetInsertInto_nodup types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      capability.CapKind.Insts.CoreCloneClone capability.CapKind.Insts.CoreCmpPartialEqCapKind
      capKind_eq_spec capKind_clone_spec st.agent_cap child cap hcapE hcapS)
  have hvv : vm2 = vm := Result.ok.inj (hvm2Eq.symm.trans hvmEq)
  rw [hvmEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _hEventEq⟩ := hok
  exact ⟨vm, hbIff.mp hb, hb1Iff.mp hb1, hlast, hb3Imp hb3, hStateEq.symm, hvmLast, hvv ▸ hvm2nd⟩

/-- `grant_capability` preserves the unified `R`. -/
theorem grant_capability_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (parent child : types.AgentId) (cap : capability.CapKind)
    (hR : R st bg a)
    (hcapE : st.agent_cap.entries.val.length < Usize.max)
    (hcapS : ∀ p ∈ st.agent_cap.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.grant_capability st bg parent child cap = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.grant_capability parent child cap).guard a ∧
          (Tzimtzum.grant_capability parent child cap).next a a' ∧ R st' bg a' := by
  obtain ⟨vmAfter, hParentActive, hChildActive, hParentEdge, hParentCap, rfl, hvmLast, hvmNd⟩ :=
    grant_capability_inv_full st bg parent child cap hcapE hcapS st' ev hok
  refine ⟨{ a with agent_cap := fun N C => (N = child ∧ C = cap) ∨ a.agent_cap N C }, ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.grant_capability]
    refine ⟨(hR.active parent).mpr hParentActive, (hR.active child).mpr hChildActive,
      (hR.parent child parent).mpr hParentEdge, ?_⟩
    exact (hR.cap parent cap).mpr ((vmsMem_iff_vmsMemLast st.agent_cap hR.ndCap parent cap).mp hParentCap)
  · -- next
    simp [Tzimtzum.grant_capability]
  · -- R st' bg a'
    refine ⟨hR.root, hR.cap_declass, hR.cap_refresh, hR.active, hR.tool_reg, hR.parent, ?_, hR.instr,
      hR.taint, hR.inflight, hR.ghInvoked, hR.ghReceived, hR.override, hR.budget, hR.toolCap,
      hR.toolEgress, hR.toolFloor, hR.toolBounded, hR.toolIssuer, hR.trustedIss, hR.instrIssuer,
      hR.flowAllows, hR.flowInspects, hR.flowOverride, hR.invTool, hR.ndParent, ?_, hR.ndInstr,
      hR.ndTaint, hR.ndInflight, hR.ndGhInvoked, hR.ndGhReceived, hR.ndOverride, hR.ndBudget,
      hR.wfInflight⟩
    · -- cap
      intro N C
      show ((N = child ∧ C = cap) ∨ a.agent_cap N C) ↔ vmsMemLast vmAfter N C
      rw [hvmLast N C, ← hR.cap N C]
      tauto
    · -- ndCap
      exact hvmNd hR.ndCap

end ArgusLean.Refinement
