import ArgusLean.Refinement.Unified.Preservation.ClearAgent

/-! # Layer 1 — `revoke` preserves the unified `R` (V4)

`revoke parent target` gates on the parent edge (`get_cloned` + `AgentId.eq`), both agents active,
and `target ≠ root`, then destroys `target` via `clear_agent`. The R-transport is the shared
`clear_preservesR`; this module only inverts the guard and threads `clearAgent_spec`. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

theorem revoke_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (parent target : types.AgentId)
    (hR : R st bg a)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.revoke st bg parent target = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.revoke parent target).guard a ∧
          (Tzimtzum.revoke parent target).next a a' ∧ R st' bg a' := by
  simp only [transitions.revoke] at hok
  obtain ⟨o, hoEq, ho⟩ := spec_imp_exists
    (vecMapGetCloned_spec types.AgentId.Insts.CoreCloneClone
      types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec
      types.AgentId.Insts.CoreCloneClone agentId_clone_spec st.agent_parent target)
  rw [hoEq] at hok
  simp only [bind_tc_ok] at hok
  cases hL : vmLastEntry st.agent_parent.entries.val target with
  | none =>
    rw [hL] at ho; simp only [Option.map_none] at ho; subst ho; simp at hok
  | some p =>
    obtain ⟨x, y⟩ := p
    rw [hL] at ho; simp only [Option.map_some] at ho; subst ho
    simp only [agentId_eq_spec, bind_tc_ok] at hok
    split at hok
    · rename_i hpe
      have hyp : y = parent := by simpa using hpe
      have hx : x = target := vmLastEntry_fst _ _ _ hL
      -- active parent
      obtain ⟨bp, hbpEq, hbpIff⟩ := spec_imp_exists
        (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active parent)
      rw [hbpEq] at hok; simp only [bind_tc_ok] at hok
      have hbp : bp = true := by cases bp with | true => rfl | false => simp at hok
      simp only [hbp, reduceIte] at hok
      -- active target
      obtain ⟨bt, hbtEq, hbtIff⟩ := spec_imp_exists
        (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active target)
      rw [hbtEq] at hok; simp only [bind_tc_ok] at hok
      have hbt : bt = true := by cases bt with | true => rfl | false => simp at hok
      simp only [hbt, reduceIte] at hok
      -- target ≠ root
      simp only [background.BackgroundTheory.impl.root_agent, agentId_eq_spec, bind_tc_ok] at hok
      split at hok
      · rename_i hroot; simp at hok
      · rename_i hroot
        have htne : target ≠ bg.root_agent := by simpa using hroot
        -- clear_agent target
        obtain ⟨s1, hs1Eq, hs1a, hs1p, hs1c, hs1t, hs1i, hs1pend, hs1chal, hs1grant, hs1ci, hs1ca,
            hs1cc, hs1tr⟩ := spec_imp_exists
          (clearAgent_spec st target hR.ndPending hR.ndChallenges hR.ndGrants)
        rw [hs1Eq] at hok
        simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨hStateEq, _hEv⟩ := hok
        subst hStateEq
        refine ⟨clearAbs a target, ?_, ?_, clear_preservesR st bg a target hR s1 hs1a hs1p hs1c
          hs1t hs1i hs1pend hs1chal hs1grant hs1ci hs1ca hs1cc hs1tr⟩
        · -- guard
          have hpar : vmLastEntry st.agent_parent.entries.val target = some (target, parent) := by
            rw [hx, hyp] at hL; exact hL
          simp only [Tzimtzum.revoke]
          refine ⟨(hR.parent target parent).mpr hpar,
            (hR.active parent).mpr (hbpIff.mp hbp), (hR.active target).mpr (hbtIff.mp hbt), ?_⟩
          rw [hR.root]; exact htne
        · -- next
          simp [Tzimtzum.revoke, clearAbs]
    · rename_i hpe; simp at hok

end ArgusLean.Refinement
