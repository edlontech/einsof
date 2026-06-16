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

variable {AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId : Type}

/-- The resistant VC: `active_has_budget` under `return_endorsed`. For `A = prnt` the
    `affordable prnt 2` guard supplies the current budget `b`; `budget_unique` pins it as the
    sole level, so witness `b - 2` satisfies the `∀ b` debit clause. For `A ≠ prnt` framed. -/
private theorem re_pres_ahb (child prnt : AgentId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hahb : active_has_budget s)
    (hbu : budget_unique s)
    (hg : (return_endorsed child prnt).guard s)
    (hn : (return_endorsed child prnt).next s s') :
    active_has_budget s' := by
  unfold active_has_budget budget_unique return_endorsed Kav.Action.guard Kav.Action.next at *
  intro A hactive
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
  · obtain ⟨L, hL⟩ := hahb A hactiveS
    exact ⟨L, by rw [hbeq]; right; exact ⟨hAp, hL⟩⟩

/-- `budget_bounded` under `return_endorsed`: the `prnt` debit yields `b - 2 ≤ b ≤ capacity`
    (`b` from the `affordable prnt 2` guard); other agents are framed. -/
private theorem re_pres_bb (child prnt : AgentId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hbb : budget_bounded s)
    (hg : (return_endorsed child prnt).guard s)
    (hn : (return_endorsed child prnt).next s s') :
    budget_bounded s' := by
  unfold budget_bounded return_endorsed Kav.Action.guard Kav.Action.next at *
  intro A L hL
  have hbeq : s'.agent_budget A L =
      ((A = prnt ∧ ∀ b, s.agent_budget prnt b → L = b - 2)
      ∨ (A ≠ prnt ∧ s.agent_budget A L)) := by grind
  rw [hbeq] at hL
  rcases hL with ⟨rfl, hdeb⟩ | ⟨_, hkept⟩
  · obtain ⟨b, hb, _⟩ := hg.2.2.2.2.2.2
    have hLb : L = b - 2 := hdeb b hb
    have hbc : b ≤ budget_capacity := hbb A b hb
    omega
  · exact hbb A L hkept

theorem pres_return_endorsed
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hinv : allInv s)
    (hn : (Kav.close2 return_endorsed).next s s') : allInv s' := by
  simp only [Kav.close2] at hn
  obtain ⟨child, prnt, hg, hn⟩ := hn
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hbu, hahb, hbb, _, _, _, _⟩ := hinv
  have hahb' : active_has_budget s' := re_pres_ahb child prnt s s' hahb hbu hg hn
  have hbb' : budget_bounded s' := re_pres_bb child prnt s s' hbb hg hn
  unfold allInv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      ?_, hahb', hbb', ?_, ?_, ?_, ?_⟩
  all_goals_fresh (
    (try simp only [return_endorsed, allInv,
        root_always_active, default_deny, flow_confinement, flow_confinement_weak,
        capability_subsumption, revocation_clean, taint_integrity, tool_attestation_intact,
        instruction_attestation_intact, override_consumed_when_sole_justification,
        parent_implies_active, single_parent, no_self_parent, root_no_parent,
        in_flight_active, in_flight_registered, in_flight_unique, root_all_caps,
        root_no_in_flight, budget_unique, active_has_budget, budget_bounded, ghost_invoked_sound,
        ghost_received_sound, in_flight_flow_compat, in_flight_override_consumed,
        Tzimtzum.speculative_taint, Kav.Action.guard, Kav.Action.next] at *) <;>
      (first | trivial | grind | (simp_all <;> grind) | auto | duper [*]))

end Tzimtzum
