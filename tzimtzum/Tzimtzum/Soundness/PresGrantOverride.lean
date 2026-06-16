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

/-- The resistant VC: `active_has_budget` under `grant_override`. For `A = granter` the
    `affordable granter 1` guard supplies the current budget `b`; `budget_unique` pins it as
    the sole level, so witness `b - 1` satisfies the `∀ b` debit clause. For `A ≠ granter`
    framed. -/
private theorem go_pres_ahb (granter target : AgentId) (tool : ToolId) (lvl : ConfLevel)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hahb : active_has_budget s)
    (hbu : budget_unique s)
    (hg : (grant_override granter target tool lvl).guard s)
    (hn : (grant_override granter target tool lvl).next s s') :
    active_has_budget s' := by
  unfold active_has_budget budget_unique grant_override Kav.Action.guard Kav.Action.next at *
  intro A hactive
  have hactiveS : s.agent_active A := by
    have hfa : s'.agent_active = s.agent_active := by grind
    rw [hfa] at hactive; exact hactive
  have hbeq : ∀ X Y, s'.agent_budget X Y =
      ((X = granter ∧ ∀ b, s.agent_budget granter b → Y = b - 1)
      ∨ (X ≠ granter ∧ s.agent_budget X Y)) := by grind
  by_cases hAg : A = granter
  · subst hAg
    obtain ⟨L, hL⟩ := hahb A hactiveS
    refine ⟨L - 1, ?_⟩
    rw [hbeq]; left
    refine ⟨rfl, ?_⟩
    intro b hb
    have hLb : L = b := hbu A L b ⟨hactiveS, hL, hb⟩
    rw [hLb]
  · obtain ⟨L, hL⟩ := hahb A hactiveS
    exact ⟨L, by rw [hbeq]; right; exact ⟨hAg, hL⟩⟩

/-- `budget_bounded` under `grant_override`: the granter debit yields `b - 1 ≤ b ≤ capacity`
    (`b` from the `affordable granter 1` guard); other agents are framed. -/
private theorem go_pres_bb (granter target : AgentId) (tool : ToolId) (lvl : ConfLevel)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hbb : budget_bounded s)
    (hg : (grant_override granter target tool lvl).guard s)
    (hn : (grant_override granter target tool lvl).next s s') :
    budget_bounded s' := by
  unfold budget_bounded grant_override Kav.Action.guard Kav.Action.next at *
  intro A L hL
  have hbeq : s'.agent_budget A L =
      ((A = granter ∧ ∀ b, s.agent_budget granter b → L = b - 1)
      ∨ (A ≠ granter ∧ s.agent_budget A L)) := by grind
  rw [hbeq] at hL
  rcases hL with ⟨rfl, hdeb⟩ | ⟨_, hkept⟩
  · obtain ⟨b, hb, _⟩ := hg.2.2.2.1
    have hLb : L = b - 1 := hdeb b hb
    have hbc : b ≤ budget_capacity := hbb A b hb
    omega
  · exact hbb A L hkept

theorem pres_grant_override
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hinv : allInv s)
    (hn : (Kav.close4 grant_override).next s s') : allInv s' := by
  simp only [Kav.close4] at hn
  obtain ⟨granter, target, tool, lvl, hg, hn⟩ := hn
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hbu, hahb, hbb, _, _, _, _⟩ := hinv
  have hahb' : active_has_budget s' := go_pres_ahb granter target tool lvl s s' hahb hbu hg hn
  have hbb' : budget_bounded s' := go_pres_bb granter target tool lvl s s' hbb hg hn
  unfold allInv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, hahb', hbb', ?_, ?_, ?_, ?_⟩
  all_goals_fresh (
    (try simp only [grant_override, allInv,
        root_always_active, default_deny, flow_confinement, flow_confinement_weak,
        capability_subsumption, revocation_clean, taint_integrity, tool_attestation_intact,
        instruction_attestation_intact, override_consumed_when_sole_justification,
        parent_implies_active, single_parent, no_self_parent, root_no_parent,
        in_flight_active, in_flight_registered, in_flight_unique, root_all_caps,
        root_no_in_flight, budget_unique, active_has_budget, budget_bounded, ghost_invoked_sound,
        ghost_received_sound, in_flight_flow_compat, in_flight_override_consumed,
        St.flow_allows, St.flow_inspects,
        Tzimtzum.speculative_taint, Kav.Action.guard, Kav.Action.next] at *) <;>
      (first | trivial | grind | (simp_all <;> grind) | auto | duper [*]))

end Tzimtzum
