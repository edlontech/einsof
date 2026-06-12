import Tzimtzum.Soundness.Common

/-! # Campaign A — `grant_override` preservation

The third budget action. Like `invoke_complete` / `return_endorsed`, the granter's
5-way budget debit makes `active_has_budget` resistant to the cascade (the debit
branch needs an explicit post-budget witness), so it is slotted in manually via
`go_pres_ahb` (the monomorphic twin was verified as
`grant_override_pres_active_has_budget` in `CheckGrantOverride`). The other 24
conjuncts close under the per-goal-fresh cascade: the re-arm guard
(`∀ I, ¬ s.in_flight target I`) makes the two single-use override invariants vacuous
for the target, and nothing else observable changes for other agents. -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId : Type}

/-- The resistant VC: `active_has_budget` under `grant_override`. `budget_unique` + the
    `¬ bl_exhausted` precondition + `active_has_budget s` pin the granter to exactly one
    non-exhausted level, each of which has a debit target. -/
private theorem go_pres_ahb (granter target : AgentId) (tool : ToolId) (lvl : ConfLevel)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hahb : active_has_budget s)
    (hg : (grant_override granter target tool lvl).guard s)
    (hn : (grant_override granter target tool lvl).next s s') :
    active_has_budget s' := by
  unfold active_has_budget grant_override Kav.Action.guard Kav.Action.next at *
  intro A hactive
  have hactiveS : s.agent_active A := by
    have hfa : s'.agent_active = s.agent_active := by grind
    rw [hfa] at hactive; exact hactive
  by_cases hAg : A = granter
  · subst hAg
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
        ((X = granter ∧
          ( (s.agent_budget granter BudgetLevel.bl5 ∧ Y = BudgetLevel.bl4)
          ∨ (s.agent_budget granter BudgetLevel.bl4 ∧ Y = BudgetLevel.bl3)
          ∨ (s.agent_budget granter BudgetLevel.bl3 ∧ Y = BudgetLevel.bl2)
          ∨ (s.agent_budget granter BudgetLevel.bl2 ∧ Y = BudgetLevel.bl1)
          ∨ (s.agent_budget granter BudgetLevel.bl1 ∧ Y = BudgetLevel.bl_exhausted) ))
        ∨ (X ≠ granter ∧ s.agent_budget X Y)) := by grind
    rw [hbeq]; right; exact ⟨hAg, hL⟩

theorem pres_grant_override
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hinv : allInv s)
    (hn : (Kav.close4 grant_override).next s s') : allInv s' := by
  simp only [Kav.close4] at hn
  obtain ⟨granter, target, tool, lvl, hg, hn⟩ := hn
  have hahb : active_has_budget s := by
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _, _, _, _⟩ := hinv
    exact h
  have hahb' : active_has_budget s' := go_pres_ahb granter target tool lvl s s' hahb hg hn
  unfold allInv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, hahb', ?_, ?_, ?_, ?_⟩
  all_goals_fresh (
    (try simp only [grant_override, allInv,
        root_always_active, default_deny, flow_confinement, flow_confinement_weak,
        capability_subsumption, revocation_clean, taint_integrity, tool_attestation_intact,
        instruction_attestation_intact, override_consumed_when_sole_justification,
        parent_implies_active, single_parent, no_self_parent, root_no_parent,
        in_flight_active, in_flight_registered, in_flight_unique, root_all_caps,
        root_no_in_flight, budget_unique, active_has_budget, ghost_invoked_sound,
        ghost_received_sound, in_flight_flow_compat, in_flight_override_consumed,
        St.flow_allows, St.flow_inspects,
        Tzimtzum.speculative_taint, Kav.Action.guard, Kav.Action.next] at *) <;>
      (first | trivial | grind | (simp_all <;> grind) | auto | duper [*]))

end Tzimtzum
