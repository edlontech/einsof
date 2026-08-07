import ArgusLean.Refinement.Unified.Preservation.ClearAgent

/-! # Layer 1 — `cascade_revoke` preserves the unified `R` (V4)

`cascade_revoke child parent` is the revoke variant for an active child whose parent is already
INACTIVE: it gates on the parent edge, `¬ agent_active parent`, `agent_active child`, and
`child ≠ root`, then destroys `child` via `clear_agent`. Same destruction set as `revoke`, so it
reuses `clear_preservesR`. -/

namespace ArgusLean.Refinement

open Aeneas Aeneas.Std Result argus_kernel
open Aeneas.Std.WP

set_option maxHeartbeats 1000000

theorem cascade_revoke_preservesR
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (child parent : types.AgentId)
    (hR : R st bg a)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.cascade_revoke st bg child parent = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.cascade_revoke child parent).guard a ∧
          (Tzimtzum.cascade_revoke child parent).next a a' ∧ R st' bg a' := by
  simp only [transitions.cascade_revoke] at hok
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
    · rename_i hpe
      have hyp : y = parent := by simpa using hpe
      have hx : x = child := vmLastEntry_fst _ _ _ hL
      -- parent must be inactive
      obtain ⟨bp, hbpEq, hbpIff⟩ := spec_imp_exists
        (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active parent)
      rw [hbpEq] at hok; simp only [bind_tc_ok] at hok
      have hbp : bp = false := by cases bp with | false => rfl | true => simp at hok
      simp only [hbp, Bool.false_eq_true, reduceIte] at hok
      -- active child
      obtain ⟨bc, hbcEq, hbcIff⟩ := spec_imp_exists
        (vecSetContains_spec types.AgentId.Insts.CoreCloneClone
          types.AgentId.Insts.CoreCmpPartialEqAgentId agentId_eq_spec st.agent_active child)
      rw [hbcEq] at hok; simp only [bind_tc_ok] at hok
      have hbc : bc = true := by cases bc with | true => rfl | false => simp at hok
      simp only [hbc, reduceIte] at hok
      -- child ≠ root
      simp only [background.BackgroundTheory.impl.root_agent, agentId_eq_spec, bind_tc_ok] at hok
      split at hok
      · rename_i hroot; simp at hok
      · rename_i hroot
        have hcne : child ≠ bg.root_agent := by simpa using hroot
        obtain ⟨s1, hs1Eq, hs1a, hs1p, hs1c, hs1t, hs1i, hs1pend, hs1chal, hs1grant, hs1ci, hs1ca,
            hs1cc, hs1tr⟩ := spec_imp_exists
          (clearAgent_spec st child hR.ndPending hR.ndChallenges hR.ndGrants)
        rw [hs1Eq] at hok
        simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨hStateEq, _hEv⟩ := hok
        subst hStateEq
        refine ⟨clearAbs a child, ?_, ?_, clear_preservesR st bg a child hR s1 hs1a hs1p hs1c
          hs1t hs1i hs1pend hs1chal hs1grant hs1ci hs1ca hs1cc hs1tr⟩
        · -- guard
          have hpar : vmLastEntry st.agent_parent.entries.val child = some (child, parent) := by
            rw [hx, hyp] at hL; exact hL
          simp only [Tzimtzum.cascade_revoke]
          refine ⟨(hR.parent child parent).mpr hpar, ?_,
            (hR.active child).mpr (hbcIff.mp hbc), ?_⟩
          · rw [hR.active parent]; intro hc
            have := hbpIff.mpr hc; rw [hbp] at this; exact Bool.false_ne_true this
          · rw [hR.root]; exact hcne
        · -- next
          simp [Tzimtzum.cascade_revoke, clearAbs]
    · rename_i hpe; simp at hok

end ArgusLean.Refinement
