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
-- The flat-2 debit post is `∀ b, agent_budget prnt b → L = b - 2`; we witness `L - 2` for
-- the `active_has_budget` level `L` and use `budget_unique` to pin every `b` to `L`. The
-- `affordable prnt 2` guard is not even needed for existence here. The bundle conjuncts
-- used (the VC supplies the full invariant bundle, of which `active_has_budget` and
-- `budget_unique` are members) are taken as hypotheses.
theorem return_endorsed_pres_active_has_budget
    (child prnt : KAgent) (s s' : KSt)
    (hahb : active_has_budget s)
    (hbu : budget_unique s)
    (hg : (retEnd child prnt).guard s)
    (hn : (retEnd child prnt).next s s') :
    active_has_budget s' := by
  unfold active_has_budget budget_unique retEnd return_endorsed Kav.Action.guard
    Kav.Action.next at *
  intro A hactive
  -- `agent_active` is framed, so `A` is active in `s` too.
  have hactiveS : s.agent_active A := by
    have hfa : s'.agent_active = s.agent_active := by grind
    rw [hfa] at hactive; exact hactive
  have hbeq : ∀ X Y, s'.agent_budget X Y =
      ((X = prnt ∧ ∀ b, s.agent_budget prnt b → Y = b - 2)
      ∨ (X ≠ prnt ∧ s.agent_budget X Y)) := by grind
  by_cases hAp : A = prnt
  · subst hAp
    obtain ⟨L, hL⟩ := hahb A hactiveS
    refine ⟨L - 2, ?_⟩
    rw [hbeq]; left
    refine ⟨rfl, ?_⟩
    intro b hb
    have hLb : L = b := hbu A L b ⟨hactiveS, hL, hb⟩
    rw [hLb]
  · -- A ≠ prnt: budget framed through the second disjunct.
    obtain ⟨L, hL⟩ := hahb A hactiveS
    exact ⟨L, by rw [hbeq]; right; exact ⟨hAp, hL⟩⟩

-- Axiom audit: must depend only on [propext, Classical.choice, Quot.sound].
#print axioms return_endorsed_pres_active_has_budget

end Tzimtzum
