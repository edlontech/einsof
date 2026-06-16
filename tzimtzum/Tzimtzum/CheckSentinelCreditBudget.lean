import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 4000000

namespace Tzimtzum

private def creditBudget : KAgent → Nat → Kav.Action KSt := sentinel_credit_budget

-- All invariants except the three budget ones, proved manually below: the saturating credit
-- post (`∀ b, agent_budget a b → L = budget_saturating_credit b n`) needs explicit witnesses /
-- the `≤ budget_capacity` bound the cascade can't reconstruct (the credit is irreducible).
-- The other 23 are frame-trivial w.r.t. `agent_budget` and close under the cascade (which
-- leaves the irreducible credit atom alone).
private def invsAuto : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p =>
    p.1 ≠ "active_has_budget" ∧ p.1 ≠ "budget_unique" ∧ p.1 ≠ "budget_bounded")

#kav_check_action creditBudget invsAuto

-- Manual proof of `active_has_budget` under `sentinel_credit_budget`. Witness
-- `budget_saturating_credit L n` for the `active_has_budget` level `L`; `budget_unique` pins
-- every `b` to `L`. For `A ≠ a` the budget is framed.
theorem sentinel_credit_budget_pres_active_has_budget
    (a : KAgent) (n : Nat) (s s' : KSt)
    (hahb : active_has_budget s)
    (hbu : budget_unique s)
    (hg : (creditBudget a n).guard s)
    (hn : (creditBudget a n).next s s') :
    active_has_budget s' := by
  unfold active_has_budget budget_unique creditBudget sentinel_credit_budget Kav.Action.guard
    Kav.Action.next at *
  intro A hactive
  have hactiveS : s.agent_active A := by
    have hfa : s'.agent_active = s.agent_active := by grind
    rw [hfa] at hactive; exact hactive
  have hbeq : ∀ X Y, s'.agent_budget X Y =
      ((X = a ∧ ∀ b, s.agent_budget a b → Y = budget_saturating_credit b n)
      ∨ (X ≠ a ∧ s.agent_budget X Y)) := by grind
  by_cases hAa : A = a
  · subst hAa
    obtain ⟨L, hL⟩ := hahb A hactiveS
    refine ⟨budget_saturating_credit L n, ?_⟩
    rw [hbeq]; left
    refine ⟨rfl, ?_⟩
    intro b hb
    have hLb : L = b := hbu A L b ⟨hactiveS, hL, hb⟩
    rw [hLb]
  · obtain ⟨L, hL⟩ := hahb A hactiveS
    exact ⟨L, by rw [hbeq]; right; exact ⟨hAa, hL⟩⟩

-- Axiom audit: must depend only on [propext, Classical.choice, Quot.sound].
#print axioms sentinel_credit_budget_pres_active_has_budget

-- Manual proof of `budget_unique` under `sentinel_credit_budget`: for `A = a` both post
-- levels are `budget_saturating_credit b n` for the unique pre-budget; for `A ≠ a` framed.
theorem sentinel_credit_budget_pres_budget_unique
    (a : KAgent) (n : Nat) (s s' : KSt)
    (hahb : active_has_budget s)
    (hbu : budget_unique s)
    (hg : (creditBudget a n).guard s)
    (hn : (creditBudget a n).next s s') :
    budget_unique s' := by
  unfold budget_unique active_has_budget creditBudget sentinel_credit_budget Kav.Action.guard
    Kav.Action.next at *
  intro A L1 L2 ⟨hactive, h1, h2⟩
  have hactiveS : s.agent_active A := by
    have hfa : s'.agent_active = s.agent_active := by grind
    rw [hfa] at hactive; exact hactive
  have hbeq : ∀ X Y, s'.agent_budget X Y =
      ((X = a ∧ ∀ b, s.agent_budget a b → Y = budget_saturating_credit b n)
      ∨ (X ≠ a ∧ s.agent_budget X Y)) := by grind
  rw [hbeq] at h1 h2
  by_cases hAa : A = a
  · subst hAa
    obtain ⟨b, hb⟩ := hahb A hactiveS
    rcases h1 with ⟨_, h1'⟩ | ⟨hne, _⟩
    · rcases h2 with ⟨_, h2'⟩ | ⟨hne, _⟩
      · rw [h1' b hb, h2' b hb]
      · exact absurd rfl hne
    · exact absurd rfl hne
  · rcases h1 with ⟨heq, _⟩ | ⟨_, h1'⟩
    · exact absurd heq hAa
    · rcases h2 with ⟨heq, _⟩ | ⟨_, h2'⟩
      · exact absurd heq hAa
      · exact hbu A L1 L2 ⟨hactiveS, h1', h2'⟩

#print axioms sentinel_credit_budget_pres_budget_unique

-- Manual proof of `budget_bounded` under `sentinel_credit_budget`: the credit
-- `budget_saturating_credit b n = min budget_capacity (b + n)` is `≤ budget_capacity` via
-- `Nat.min_le_left`; framed agents reuse `budget_bounded s`.
theorem sentinel_credit_budget_pres_budget_bounded
    (a : KAgent) (n : Nat) (s s' : KSt)
    (hahb : active_has_budget s)
    (hbb : budget_bounded s)
    (hg : (creditBudget a n).guard s)
    (hn : (creditBudget a n).next s s') :
    budget_bounded s' := by
  unfold budget_bounded active_has_budget creditBudget sentinel_credit_budget Kav.Action.guard
    Kav.Action.next at *
  intro A L hL
  have hbeq : s'.agent_budget A L =
      ((A = a ∧ ∀ b, s.agent_budget a b → L = budget_saturating_credit b n)
      ∨ (A ≠ a ∧ s.agent_budget A L)) := by grind
  rw [hbeq] at hL
  rcases hL with ⟨rfl, hcredit⟩ | ⟨_, hkept⟩
  · have hactiveS : s.agent_active A := by grind
    obtain ⟨b, hb⟩ := hahb A hactiveS
    have hLc : L = budget_saturating_credit b n := hcredit b hb
    rw [hLc, budget_saturating_credit]
    exact Nat.min_le_left _ _
  · exact hbb A L hkept

#print axioms sentinel_credit_budget_pres_budget_bounded

end Tzimtzum
