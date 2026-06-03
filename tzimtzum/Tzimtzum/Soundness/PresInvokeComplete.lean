import Tzimtzum.Soundness.Common

/-! # C0 — `invoke_complete` preservation

The structurally largest action: the budget self-debit makes two VCs resistant to the
cascade, so each is slotted in manually and the remaining 23 conjuncts use the
per-goal-fresh cascade.

* `budget_unique`: the 25-way `simp only … at *` flood buries `grind` on the 5-way
  `BudgetLevel` debit; extracting only `budget_unique`/`active_has_budget` pre-facts
  closes it.
* `active_has_budget`: the debit branch needs an explicit post-budget witness the
  cascade cannot reconstruct (it would fall through to `duper` and burn the whole
  heartbeat budget). Proved by `ic_pres_ahb` below (the proof previously verified as
  `invoke_complete_pres_active_has_budget` in `CheckInvokeComplete`). -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId : Type}

/-- The resistant VC: `active_has_budget` under `invoke_complete`. For `A ≠ a` budget is
    framed. For `A = a`: either the conform/non-exhausted condition fails (budget kept,
    reuse the `s`-witness) or it holds (debit; enumerate `bl5..bl1` — the condition rules
    out `bl_exhausted` as the source). -/
private theorem ic_pres_ahb (a : AgentId) (inv : InvocationId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hahb : active_has_budget s)
    (hg : (invoke_complete a inv).guard s)
    (hn : (invoke_complete a inv).next s s') :
    active_has_budget s' := by
  unfold active_has_budget invoke_complete Kav.Action.guard Kav.Action.next at *
  intro A hactive
  have hfa : s'.agent_active = s.agent_active := by grind
  have hactiveS : s.agent_active A := by rw [hfa] at hactive; exact hactive
  obtain ⟨L, hL⟩ := hahb A hactiveS
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
    · have hne : ¬ s.agent_budget A BudgetLevel.bl_exhausted := hcond.2.2
      cases L with
      | bl_exhausted => exact absurd hL hne
      | bl5 => exact ⟨BudgetLevel.bl4, by rw [hbeq]; left; exact ⟨rfl, Or.inl ⟨hcond, Or.inl ⟨hL, rfl⟩⟩⟩⟩
      | bl4 => exact ⟨BudgetLevel.bl3, by rw [hbeq]; left; exact ⟨rfl, Or.inl ⟨hcond, Or.inr (Or.inl ⟨hL, rfl⟩)⟩⟩⟩
      | bl3 => exact ⟨BudgetLevel.bl2, by rw [hbeq]; left; exact ⟨rfl, Or.inl ⟨hcond, Or.inr (Or.inr (Or.inl ⟨hL, rfl⟩))⟩⟩⟩
      | bl2 => exact ⟨BudgetLevel.bl1, by rw [hbeq]; left; exact ⟨rfl, Or.inl ⟨hcond, Or.inr (Or.inr (Or.inr (Or.inl ⟨hL, rfl⟩)))⟩⟩⟩
      | bl1 => exact ⟨BudgetLevel.bl_exhausted, by rw [hbeq]; left; exact ⟨rfl, Or.inl ⟨hcond, Or.inr (Or.inr (Or.inr (Or.inr ⟨hL, rfl⟩)))⟩⟩⟩
    · exact ⟨L, by rw [hbeq]; left; exact ⟨rfl, Or.inr ⟨hcond, hL⟩⟩⟩
  · exact ⟨L, by rw [hbeq]; right; exact ⟨hAa, hL⟩⟩

theorem pres_invoke_complete
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hinv : allInv s)
    (hn : (Kav.close2 invoke_complete).next s s') : allInv s' := by
  simp only [Kav.close2] at hn
  obtain ⟨a, invid, hg, hn⟩ := hn
  have hbudget : budget_unique s' := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbu, hab, _, _, _, _⟩ := hinv
    simp only [budget_unique] at hbu ⊢
    simp only [active_has_budget] at hab
    simp only [invoke_complete] at hn
    simp_all <;> grind
  have hahb : active_has_budget s := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _⟩ := hinv
    exact h
  have hahb' : active_has_budget s' := ic_pres_ahb a invid s s' hahb hg hn
  unfold allInv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hbudget, hahb', ?_, ?_, ?_, ?_⟩
  all_goals_fresh (
    (try simp only [invoke_complete, allInv,
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
