import ArgusLean.Refinement.Unified.Preservation.ClearAgent

/-! # Layer 1 — `grant_crossing` preserves the unified `R` (V4)

`grant_crossing` is root-only and sets the `(agent, assignment)` crossing grant to
`{ remaining := n, provisioned := n }` (a last-match `VecMap.insert`), framing every other field.
The `n < 2^32` bound is a `CapacityOK` obligation (discharged at the bundle), not enforced here; the
concrete counter carries its `Nat` value through `crossingGrantRel`. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

theorem grant_crossing_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (grantor agent : types.AgentId) (assignment : types.AssignmentDigest)
    (n : Std.U32)
    (hR : R st bg a)
    (hcap : st.crossing_grants.entries.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.grant_crossing st bg grantor agent assignment n = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.grant_crossing grantor agent assignment n.val).guard a ∧
          (Tzimtzum.grant_crossing grantor agent assignment n.val).next a a' ∧ R st' bg a' := by
  simp only [transitions.grant_crossing, background.BackgroundTheory.impl.root_agent,
    core.cmp.PartialEq.ne.trait_default, core.cmp.PartialEq.ne.default, agentId_eq_spec,
    bind_tc_ok] at hok
  split at hok
  · rename_i hne; simp at hok
  · rename_i hne
    have hgr : grantor = bg.root_agent := by simpa using hne
    obtain ⟨b1, hb1Eq, hb1Iff⟩ := spec_imp_exists
      (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active grantor)
    rw [hb1Eq] at hok; simp only [bind_tc_ok] at hok
    have hb1 : b1 = true := by cases b1 with | true => rfl | false => simp at hok
    simp only [hb1, reduceIte] at hok
    obtain ⟨b2, hb2Eq, hb2Iff⟩ := spec_imp_exists
      (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
        types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active agent)
    rw [hb2Eq] at hok; simp only [bind_tc_ok] at hok
    have hb2 : b2 = true := by cases b2 with | true => rfl | false => simp at hok
    simp only [hb2, reduceIte, agentId_clone_spec, assignmentDigest_clone_spec, bind_tc_ok] at hok
    obtain ⟨vm, hvmEq, hvm⟩ := spec_imp_exists
      (vecMapInsert_vmLast_spec types.CrossingKey.Insts.CoreCloneClone
        types.CrossingKey.Insts.CoreCmpPartialEqCrossingKey crossingKey_eq_spec
        types.CrossingGrant.Insts.CoreCloneClone st.crossing_grants
        { agent := agent, assignment := assignment } { remaining := n, provisioned := n } hcap)
    obtain ⟨vm2, hvm2Eq, hvm2nd⟩ := spec_imp_exists
      (vecMapInsert_nodup types.CrossingKey.Insts.CoreCloneClone
        types.CrossingKey.Insts.CoreCmpPartialEqCrossingKey crossingKey_eq_spec
        types.CrossingGrant.Insts.CoreCloneClone st.crossing_grants
        { agent := agent, assignment := assignment } { remaining := n, provisioned := n } hcap)
    have hvv : vm2 = vm := Result.ok.inj (hvm2Eq.symm.trans hvmEq)
    rw [hvmEq] at hok
    simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
    obtain ⟨hStateEq, _hEv⟩ := hok
    subst hStateEq
    refine ⟨{ a with crossing_grants := fun A D =>
        if A = agent ∧ D = assignment then some { remaining := n.val, provisioned := n.val }
        else a.crossing_grants A D }, ?_, ?_, ?_⟩
    · -- guard
      simp only [Tzimtzum.grant_crossing]
      exact ⟨by rw [hR.root]; exact hgr, (hR.active grantor).mpr (hb1Iff.mp hb1),
        (hR.active agent).mpr (hb2Iff.mp hb2)⟩
    · -- next
      simp only [Tzimtzum.grant_crossing]
      refine ⟨True.intro, True.intro, True.intro, True.intro, True.intro, True.intro, True.intro,
        True.intro, True.intro, True.intro, ?_, True.intro, True.intro, True.intro, True.intro,
        True.intro⟩
      funext A D; by_cases h : A = agent ∧ D = assignment <;> simp [h]
    · -- R st' bg a'
      refine
        { root := hR.root, mode := hR.mode, active := hR.active, tool_reg := hR.tool_reg
          parent := hR.parent, cap := hR.cap, taint := hR.taint, integ := hR.integ
          pending := hR.pending, challenges := hR.challenges
          grants := ?_
          consumedIds := hR.consumedIds, consumedAtt := hR.consumedAtt
          consumedCross := hR.consumedCross
          flowAllows := hR.flowAllows, flowInspects := hR.flowInspects
          ndParent := hR.ndParent, ndCap := hR.ndCap, ndTaint := hR.ndTaint, ndInteg := hR.ndInteg
          ndPending := hR.ndPending, ndChallenges := hR.ndChallenges
          ndGrants := hvv ▸ hvm2nd hR.ndGrants }
      intro A D
      show optRel crossingGrantRel
        (if A = agent ∧ D = assignment then some { remaining := n.val, provisioned := n.val }
          else a.crossing_grants A D)
        (crossingGrantC { st with crossing_grants := vm } { agent := A, assignment := D })
      have hRg := hR.grants A D
      unfold crossingGrantC at hRg ⊢
      show optRel crossingGrantRel _ (Option.map Prod.snd (vmLastEntry vm.entries.val _))
      rw [hvm { agent := A, assignment := D }]
      by_cases hAD : ({ agent := A, assignment := D } : types.CrossingKey)
          = { agent := agent, assignment := assignment }
      · have hAeq : A = agent ∧ D = assignment := by
          have := hAD; simp only [types.CrossingKey.mk.injEq] at this; exact this
        rw [if_pos hAeq, if_pos hAD]
        simp [optRel, crossingGrantRel]
      · have hAneq : ¬ (A = agent ∧ D = assignment) := by
          intro h; exact hAD (by rw [h.1, h.2])
        rw [if_neg hAneq, if_neg hAD]
        exact hRg

end ArgusLean.Refinement
