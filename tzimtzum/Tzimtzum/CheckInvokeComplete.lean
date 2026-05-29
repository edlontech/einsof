import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 4000000

namespace Tzimtzum

private def invComp : KAgent → KInv → Kav.Action KSt := invoke_complete

-- All invariants except `active_has_budget`, proved manually below (the budget self-debit
-- creates an existential witness the cascade can't reconstruct).
private def invsAuto : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ≠ "active_has_budget")

#kav_check_action invComp invsAuto

-- Manual proof of the one resistant VC: `active_has_budget` under `invoke_complete`.
-- For `A ≠ a` budget is framed. For `A = a`: either the conform/non-exhausted condition
-- fails (budget kept, reuse the `s`-witness), or it holds (debit; enumerate bl5..bl1 — the
-- condition rules out bl_exhausted as the source). `budget_unique` pins `a` to one level.
theorem invoke_complete_pres_active_has_budget
    (a : KAgent) (inv : KInv) (s s' : KSt)
    (hahb : active_has_budget s)
    (hg : (invComp a inv).guard s)
    (hn : (invComp a inv).next s s') :
    active_has_budget s' := by
  unfold active_has_budget invComp invoke_complete Kav.Action.guard Kav.Action.next at *
  intro A hactive
  have hfa : s'.agent_active = s.agent_active := by grind
  have hactiveS : s.agent_active A := by rw [hfa] at hactive; exact hactive
  obtain ⟨L, hL⟩ := hahb A hactiveS
  -- The post agent_budget equation, abstracted over X Y.
  have hbeq : ∀ X Y, s'.agent_budget X Y =
      ((X = a ∧
        ( ( (s.tool_output_bounded (s.invocation_tool inv)
             ∧ s.output_conforms a (s.invocation_tool inv)
             ∧ ¬ s.agent_budget a BudgetLevel.bl_exhausted)
            ∧ ( (s.agent_budget a BudgetLevel.bl5 ∧ Y = BudgetLevel.bl4)
              ∨ (s.agent_budget a BudgetLevel.bl4 ∧ Y = BudgetLevel.bl3)
              ∨ (s.agent_budget a BudgetLevel.bl3 ∧ Y = BudgetLevel.bl2)
              ∨ (s.agent_budget a BudgetLevel.bl2 ∧ Y = BudgetLevel.bl1)
              ∨ (s.agent_budget a BudgetLevel.bl1 ∧ Y = BudgetLevel.bl_exhausted) ) )
          ∨ ( ¬ (s.tool_output_bounded (s.invocation_tool inv)
                 ∧ s.output_conforms a (s.invocation_tool inv)
                 ∧ ¬ s.agent_budget a BudgetLevel.bl_exhausted)
              ∧ s.agent_budget a Y ) ))
      ∨ (X ≠ a ∧ s.agent_budget X Y)) := by grind
  by_cases hAa : A = a
  · subst hAa
    by_cases hcond : (s.tool_output_bounded (s.invocation_tool inv)
        ∧ s.output_conforms A (s.invocation_tool inv)
        ∧ ¬ s.agent_budget A BudgetLevel.bl_exhausted)
    · -- debit path: source level is non-exhausted, enumerate.
      have hne : ¬ s.agent_budget A BudgetLevel.bl_exhausted := hcond.2.2
      cases L with
      | bl_exhausted => exact absurd hL hne
      | bl5 => exact ⟨BudgetLevel.bl4, by rw [hbeq]; left; exact ⟨rfl, Or.inl ⟨hcond, Or.inl ⟨hL, rfl⟩⟩⟩⟩
      | bl4 => exact ⟨BudgetLevel.bl3, by rw [hbeq]; left; exact ⟨rfl, Or.inl ⟨hcond, Or.inr (Or.inl ⟨hL, rfl⟩)⟩⟩⟩
      | bl3 => exact ⟨BudgetLevel.bl2, by rw [hbeq]; left; exact ⟨rfl, Or.inl ⟨hcond, Or.inr (Or.inr (Or.inl ⟨hL, rfl⟩))⟩⟩⟩
      | bl2 => exact ⟨BudgetLevel.bl1, by rw [hbeq]; left; exact ⟨rfl, Or.inl ⟨hcond, Or.inr (Or.inr (Or.inr (Or.inl ⟨hL, rfl⟩)))⟩⟩⟩
      | bl1 => exact ⟨BudgetLevel.bl_exhausted, by rw [hbeq]; left; exact ⟨rfl, Or.inl ⟨hcond, Or.inr (Or.inr (Or.inr (Or.inr ⟨hL, rfl⟩)))⟩⟩⟩
    · -- keep path: reuse the `s`-witness.
      exact ⟨L, by rw [hbeq]; left; exact ⟨rfl, Or.inr ⟨hcond, hL⟩⟩⟩
  · -- A ≠ a: framed.
    exact ⟨L, by rw [hbeq]; right; exact ⟨hAa, hL⟩⟩

-- Axiom audit: must depend only on [propext, Classical.choice, Quot.sound].
#print axioms invoke_complete_pres_active_has_budget

end Tzimtzum
