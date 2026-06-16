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
-- For `A ≠ a` budget is framed. For `A = a`: either the endorsed condition fails (budget
-- kept, reuse the `s`-witness), or it holds (debit; witness `b - declass_weight floor` for
-- the unique current budget `b`). `budget_unique` pins `a` to one level.
theorem invoke_complete_pres_active_has_budget
    (a : KAgent) (inv : KInv) (s s' : KSt)
    (hahb : active_has_budget s)
    (hbu : budget_unique s)
    (hg : (invComp a inv).guard s)
    (hn : (invComp a inv).next s s') :
    active_has_budget s' := by
  unfold active_has_budget budget_unique invComp invoke_complete Kav.Action.guard
    Kav.Action.next at *
  intro A hactive
  have hfa : s'.agent_active = s.agent_active := by grind
  have hactiveS : s.agent_active A := by rw [hfa] at hactive; exact hactive
  obtain ⟨L, hL⟩ := hahb A hactiveS
  -- The post agent_budget equation, abstracted over X Y.
  have hbeq : ∀ X Y, s'.agent_budget X Y =
      ((X = a ∧
        ( ( (s.tool_output_bounded (s.invocation_tool inv)
             ∧ s.output_conforms a (s.invocation_tool inv)
             ∧ s.affordable a (declass_weight (s.tool_conf_floor (s.invocation_tool inv)))
             ∧ ¬ s.taint_levels a (s.tool_conf_floor (s.invocation_tool inv)))
            ∧ ∀ b, s.agent_budget a b →
                Y = b - declass_weight (s.tool_conf_floor (s.invocation_tool inv)) )
          ∨ ( ¬ (s.tool_output_bounded (s.invocation_tool inv)
                 ∧ s.output_conforms a (s.invocation_tool inv)
                 ∧ s.affordable a (declass_weight (s.tool_conf_floor (s.invocation_tool inv)))
                 ∧ ¬ s.taint_levels a (s.tool_conf_floor (s.invocation_tool inv)))
              ∧ s.agent_budget a Y ) ))
      ∨ (X ≠ a ∧ s.agent_budget X Y)) := by grind
  by_cases hAa : A = a
  · subst hAa
    by_cases hcond : (s.tool_output_bounded (s.invocation_tool inv)
        ∧ s.output_conforms A (s.invocation_tool inv)
        ∧ s.affordable A (declass_weight (s.tool_conf_floor (s.invocation_tool inv)))
        ∧ ¬ s.taint_levels A (s.tool_conf_floor (s.invocation_tool inv)))
    · -- debit path: witness `L - declass_weight floor`; budget_unique pins all `b` to `L`.
      refine ⟨L - declass_weight (s.tool_conf_floor (s.invocation_tool inv)), ?_⟩
      rw [hbeq]; left
      refine ⟨rfl, Or.inl ⟨hcond, ?_⟩⟩
      intro b hb
      have hLb : L = b := hbu A L b ⟨hactiveS, hL, hb⟩
      rw [hLb]
    · -- keep path: reuse the `s`-witness.
      exact ⟨L, by rw [hbeq]; left; exact ⟨rfl, Or.inr ⟨hcond, hL⟩⟩⟩
  · -- A ≠ a: framed.
    exact ⟨L, by rw [hbeq]; right; exact ⟨hAa, hL⟩⟩

-- Axiom audit: must depend only on [propext, Classical.choice, Quot.sound].
#print axioms invoke_complete_pres_active_has_budget

end Tzimtzum
