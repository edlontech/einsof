import Tzimtzum.Soundness.Common

/-! # C0 — `return_endorsed` preservation

Like `invoke_complete`, the budget debit makes `active_has_budget` resistant to the
cascade (the debit branch needs an explicit post-budget witness), so it is slotted in
manually via `re_pres_ahb` (the proof previously verified as
`return_endorsed_pres_active_has_budget` in `CheckReturnEndorsed`). The other 24
conjuncts — `budget_unique` included — close under the per-goal-fresh cascade. -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Tzimtzum

/-- The resistant VC: `active_has_budget` under `return_endorsed`. `budget_unique` + the
    `¬ bl_exhausted` precondition + `active_has_budget s` pin `prnt` to exactly one
    non-exhausted level, each of which has a debit target. -/
private theorem re_pres_ahb (child prnt : KAgent) (s s' : KSt)
    (hahb : active_has_budget s)
    (hg : (return_endorsed child prnt).guard s)
    (hn : (return_endorsed child prnt).next s s') :
    active_has_budget s' := by
  unfold active_has_budget return_endorsed Kav.Action.guard Kav.Action.next at *
  intro A hactive
  have hactiveS : s.agent_active A := by
    have hfa : s'.agent_active = s.agent_active := by grind
    rw [hfa] at hactive; exact hactive
  by_cases hAp : A = prnt
  · subst hAp
    obtain ⟨L, hL⟩ := hahb A hactiveS
    have hne : ¬ s.agent_budget A BudgetLevel.bl_exhausted := by grind
    have hbeq : ∀ X Y, s'.agent_budget X Y =
        ((X = A ∧
          ( (s.agent_budget A BudgetLevel.bl5 ∧ Y = BudgetLevel.bl4)
          ∨ (s.agent_budget A BudgetLevel.bl4 ∧ Y = BudgetLevel.bl3)
          ∨ (s.agent_budget A BudgetLevel.bl3 ∧ Y = BudgetLevel.bl2)
          ∨ (s.agent_budget A BudgetLevel.bl2 ∧ Y = BudgetLevel.bl1)
          ∨ (s.agent_budget A BudgetLevel.bl1 ∧ Y = BudgetLevel.bl_exhausted) ))
        ∨ (X ≠ A ∧ s.agent_budget X Y)) := by grind
    cases L with
    | bl_exhausted => exact absurd hL hne
    | bl5 => exact ⟨BudgetLevel.bl4, by rw [hbeq]; left; exact ⟨rfl, Or.inl ⟨hL, rfl⟩⟩⟩
    | bl4 => exact ⟨BudgetLevel.bl3, by rw [hbeq]; left; exact ⟨rfl, Or.inr (Or.inl ⟨hL, rfl⟩)⟩⟩
    | bl3 => exact ⟨BudgetLevel.bl2, by rw [hbeq]; left; exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨hL, rfl⟩))⟩⟩
    | bl2 => exact ⟨BudgetLevel.bl1, by rw [hbeq]; left; exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨hL, rfl⟩)))⟩⟩
    | bl1 => exact ⟨BudgetLevel.bl_exhausted, by rw [hbeq]; left; exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨hL, rfl⟩)))⟩⟩
  · obtain ⟨L, hL⟩ := hahb A hactiveS
    refine ⟨L, ?_⟩
    have hbeq : ∀ X Y, s'.agent_budget X Y =
        ((X = prnt ∧
          ( (s.agent_budget prnt BudgetLevel.bl5 ∧ Y = BudgetLevel.bl4)
          ∨ (s.agent_budget prnt BudgetLevel.bl4 ∧ Y = BudgetLevel.bl3)
          ∨ (s.agent_budget prnt BudgetLevel.bl3 ∧ Y = BudgetLevel.bl2)
          ∨ (s.agent_budget prnt BudgetLevel.bl2 ∧ Y = BudgetLevel.bl1)
          ∨ (s.agent_budget prnt BudgetLevel.bl1 ∧ Y = BudgetLevel.bl_exhausted) ))
        ∨ (X ≠ prnt ∧ s.agent_budget X Y)) := by grind
    rw [hbeq]; right; exact ⟨hAp, hL⟩

theorem pres_return_endorsed (s s' : KSt) (hinv : allInv s)
    (hn : (Kav.close2 return_endorsed).next s s') : allInv s' := by
  simp only [Kav.close2] at hn
  obtain ⟨child, prnt, hg, hn⟩ := hn
  have hahb : active_has_budget s := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _⟩ := hinv
    exact h
  have hahb' : active_has_budget s' := re_pres_ahb child prnt s s' hahb hg hn
  unfold allInv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, hahb', ?_, ?_, ?_, ?_⟩
  all_goals_fresh (
    (try simp only [return_endorsed, allInv,
        root_always_active, default_deny, flow_confinement, flow_confinement_weak,
        capability_subsumption, revocation_clean, taint_integrity, tool_attestation_intact,
        instruction_attestation_intact, override_consumed_when_sole_justification,
        parent_implies_active, single_parent, no_self_parent, root_no_parent,
        in_flight_active, in_flight_registered, in_flight_unique, root_all_caps,
        root_no_in_flight, budget_unique, active_has_budget, ghost_invoked_sound,
        ghost_received_sound, in_flight_flow_compat, in_flight_override_consumed,
        Tzimtzum.speculative_taint, Kav.Action.guard, Kav.Action.next] at *) <;>
      (first | trivial | grind | (simp_all <;> grind) | auto | duper [*]))

end Tzimtzum
