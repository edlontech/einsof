import ArgusLean.Refinement.Unified.Bridges

/-! # Layer 1 — `grant_capability` preserves the unified `R` (V4)

`grant_capability` writes only `agent_cap` (via `insert_into`), framing everything else. The V4
transition reads the parent edge through `get_cloned` (last-match `Option`) + `AgentId.eq` (no more
raw `VecMap.get` / `Option` compare), and the capability read-gate (`prnt` holds `cap`, exposed as
`vmsMem`) is bridged to `R`'s canonical `vmsMemLast` cap view via `R.ndCap`. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

/-- Comprehensive inversion: structural frame + last-match `agent_cap` membership + nodup post. -/
theorem grant_capability_inv_full
    (st : state.KernelState)
    (parent child : types.AgentId) (cap : capability.CapKind)
    (hcapE : st.agent_cap.entries.val.length < Usize.max)
    (hcapS : ∀ p ∈ st.agent_cap.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.grant_capability st parent child cap = .ok (.Ok (st', ev))) :
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
    (vecMapGetCloned_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.AgentId.Insts.CoreCloneClone agentId_clone_spec st.agent_parent child)
  rw [hoEq] at hok
  simp only [bind_tc_ok] at hok
  cases hL : vmLastEntry st.agent_parent.entries.val child with
  | none =>
    rw [hL] at ho; simp only [Option.map_none] at ho; subst ho; simp at hok
  | some p =>
    obtain ⟨x, y⟩ := p
    rw [hL] at ho; simp only [Option.map_some] at ho; subst ho
    simp only [agentId_eq_spec, bind_tc_ok] at hok
    split at hok
    · rename_i hcond
      have hyp : y = parent := by simpa using hcond
      have hp1 : x = child := vmLastEntry_fst _ _ _ hL
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
      exact ⟨vm, hbIff.mp hb, hb1Iff.mp hb1, by rw [hp1, hyp], hb3Imp hb3, hStateEq.symm, hvmLast,
        hvv ▸ hvm2nd⟩
    · simp at hok

/-- `grant_capability` preserves the unified `R`. -/
theorem grant_capability_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (parent child : types.AgentId) (cap : capability.CapKind)
    (hR : R st bg a)
    (hcapE : st.agent_cap.entries.val.length < Usize.max)
    (hcapS : ∀ p ∈ st.agent_cap.entries.val, p.2.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.grant_capability st parent child cap = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.grant_capability parent child cap).guard a ∧
          (Tzimtzum.grant_capability parent child cap).next a a' ∧ R st' bg a' := by
  obtain ⟨vmAfter, hParentActive, hChildActive, hParentEdge, hParentCap, rfl, hvmLast, hvmNd⟩ :=
    grant_capability_inv_full st parent child cap hcapE hcapS st' ev hok
  refine ⟨{ a with agent_cap := fun N C => (N = child ∧ C = cap) ∨ a.agent_cap N C }, ?_, ?_, ?_⟩
  · -- guard
    simp only [Tzimtzum.grant_capability]
    refine ⟨(hR.active parent).mpr hParentActive, (hR.active child).mpr hChildActive,
      (hR.parent child parent).mpr hParentEdge, ?_⟩
    exact (hR.cap parent cap).mpr ((vmsMem_iff_vmsMemLast st.agent_cap hR.ndCap parent cap).mp hParentCap)
  · -- next
    simp [Tzimtzum.grant_capability]
  · -- R st' bg a'
    refine ⟨hR.root, hR.mode, hR.active, hR.tool_reg, hR.parent, ?_, hR.taint, hR.integ,
      hR.pending, hR.challenges, hR.grants, hR.consumedIds, hR.consumedAtt, hR.consumedCross,
      hR.flowAllows, hR.flowInspects, hR.ndParent, ?_, hR.ndTaint, hR.ndInteg, hR.ndPending,
      hR.ndChallenges, hR.ndGrants⟩
    · -- cap
      intro N C
      show ((N = child ∧ C = cap) ∨ a.agent_cap N C) ↔ vmsMemLast vmAfter N C
      rw [hvmLast N C, ← hR.cap N C]
      tauto
    · -- ndCap
      exact hvmNd hR.ndCap

end ArgusLean.Refinement
