import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 4000000

namespace Tzimtzum

private def creditBudget : KAgent → Nat → Kav.Action KSt := sentinel_credit_budget

-- All invariants except `revocation_clean` and `budget_bounded`, proved manually below:
-- `revocation_clean` hits the same classical-`ite` cascade stall as every other
-- budget-touching action; `budget_bounded` needs the `≤ budget_capacity` bound the cascade
-- can't reconstruct through the `@[irreducible]` saturating credit (the same reason
-- `ceilingAdmits`/`budget_saturating_credit` are already manual-proof sites elsewhere).
private def invsAuto : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ≠ "revocation_clean" ∧ p.1 ≠ "budget_bounded")

#kav_check_action creditBudget invsAuto

-- Manual proof of `revocation_clean` under `sentinel_credit_budget`.
theorem sentinel_credit_budget_pres_revocation_clean
    (a : KAgent) (n : Nat) (s s' : KSt)
    (hrc : revocation_clean s)
    (_hg : (creditBudget a n).guard s) (hn : (creditBudget a n).next s s') :
    revocation_clean s' := by
  unfold revocation_clean creditBudget sentinel_credit_budget Kav.Action.next at *
  have hactive : s'.agent_active = s.agent_active := by grind
  intro A I L hna
  rw [hactive] at hna
  obtain ⟨hinf, htaint⟩ := hrc A I L hna
  exact ⟨by grind, by grind⟩

-- Axiom audit: must depend only on [propext, Classical.choice, Quot.sound].
set_option pp.fullNames true in
#print axioms sentinel_credit_budget_pres_revocation_clean

-- Manual proof of `budget_bounded` under `sentinel_credit_budget`: the credit
-- `budget_saturating_credit b n = min budget_capacity (b + n)` is `≤ budget_capacity` via
-- `Nat.min_le_left`; framed agents reuse `budget_bounded s`.
open Classical in
theorem sentinel_credit_budget_pres_budget_bounded
    (a : KAgent) (n : Nat) (s s' : KSt)
    (hbb : budget_bounded s)
    (_hg : (creditBudget a n).guard s) (hn : (creditBudget a n).next s s') :
    budget_bounded s' := by
  unfold budget_bounded creditBudget sentinel_credit_budget Kav.Action.next at *
  intro A
  have hbeq : s'.agent_budget A =
      (if A = a then budget_saturating_credit (s.agent_budget a) n else s.agent_budget A) := by
    grind
  rw [hbeq]
  by_cases hAa : A = a
  · rw [if_pos hAa]
    unfold budget_saturating_credit
    exact Nat.min_le_left _ _
  · rw [if_neg hAa]
    exact hbb A

set_option pp.fullNames true in
#print axioms sentinel_credit_budget_pres_budget_bounded

end Tzimtzum
