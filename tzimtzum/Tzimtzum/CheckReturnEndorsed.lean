import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 4000000

namespace Tzimtzum

private def retEnd : KAgent → KAgent → Kav.Action KSt := return_endorsed

-- All invariants except `active_has_budget`, which needs the manual proof below
-- (budget debit creates an existential witness the cascade can't reconstruct).
private def invsAuto : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ≠ "active_has_budget")

#kav_check_action retEnd invsAuto

-- Manual proof of the one resistant VC: `active_has_budget` under `return_endorsed`.
-- The budget-debit branch enumerates bl5..bl1; we must produce a witness for `prnt`'s
-- post-budget. `budget_unique` + the `¬ bl_exhausted` precondition + `active_has_budget s`
-- pin `prnt` to exactly one non-exhausted level, each of which has a debit target.
-- The two bundle conjuncts actually needed (the VC supplies the full 25-invariant bundle,
-- of which `active_has_budget` and `budget_unique` are members) are taken as hypotheses.
theorem return_endorsed_pres_active_has_budget
    (child prnt : KAgent) (s s' : KSt)
    (hahb : active_has_budget s)
    (hg : (retEnd child prnt).guard s)
    (hn : (retEnd child prnt).next s s') :
    active_has_budget s' := by
  unfold active_has_budget retEnd return_endorsed Kav.Action.guard Kav.Action.next at *
  intro A hactive
  -- `agent_active` is framed, so `A` is active in `s` too.
  have hactiveS : s.agent_active A := by
    have hfa : s'.agent_active = s.agent_active := by grind
    rw [hfa] at hactive; exact hactive
  by_cases hAp : A = prnt
  · subst hAp
    -- prnt has some non-exhausted budget level in s; produce its debit target.
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
    -- L cannot be bl_exhausted; case on the remaining 5 levels.
    cases L with
    | bl_exhausted => exact absurd hL hne
    | bl5 => exact ⟨BudgetLevel.bl4, by rw [hbeq]; left; exact ⟨rfl, Or.inl ⟨hL, rfl⟩⟩⟩
    | bl4 => exact ⟨BudgetLevel.bl3, by rw [hbeq]; left; exact ⟨rfl, Or.inr (Or.inl ⟨hL, rfl⟩)⟩⟩
    | bl3 => exact ⟨BudgetLevel.bl2, by rw [hbeq]; left; exact ⟨rfl, Or.inr (Or.inr (Or.inl ⟨hL, rfl⟩))⟩⟩
    | bl2 => exact ⟨BudgetLevel.bl1, by rw [hbeq]; left; exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl ⟨hL, rfl⟩)))⟩⟩
    | bl1 => exact ⟨BudgetLevel.bl_exhausted, by rw [hbeq]; left; exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨hL, rfl⟩)))⟩⟩
  · -- A ≠ prnt: budget framed through the second disjunct.
    obtain ⟨L, hL⟩ := hahb A hactiveS
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

-- Axiom audit: must depend only on [propext, Classical.choice, Quot.sound].
#print axioms return_endorsed_pres_active_has_budget

end Tzimtzum
