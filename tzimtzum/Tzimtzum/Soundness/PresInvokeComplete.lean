import Tzimtzum.Soundness.Common

/-! # C0 — `invoke_complete` preservation

The structurally largest action: the weighted budget self-debit makes three VCs resistant to
the cascade, so each is slotted in manually and the remaining conjuncts use the per-goal-fresh
cascade.

* `budget_unique`: the `simp only … at *` flood buries `grind` on the `∀ b → L = b - w` debit;
  extracting only `budget_unique`/`active_has_budget` pre-facts closes it.
* `active_has_budget`: the debit branch needs an explicit post-budget witness (`b - w` for the
  unique current budget `b`) the cascade cannot reconstruct. Proved by `ic_pres_ahb` below.
* `budget_bounded`: `b - w ≤ b ≤ budget_capacity`; the `b` comes from the endorsed branch's
  `affordable` conjunct. Proved by `ic_pres_bb` below. -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId : Type}

/-- The resistant VC: `active_has_budget` under `invoke_complete`. For `A ≠ a` budget is
    framed. For `A = a`: either the endorsed condition fails (budget kept, reuse the
    `s`-witness) or it holds (debit; witness `b - declass_weight floor` for the unique
    current budget `b`). -/
private theorem ic_pres_ahb (a : AgentId) (inv : InvocationId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hahb : active_has_budget s)
    (hbu : budget_unique s)
    (hg : (invoke_complete a inv).guard s)
    (hn : (invoke_complete a inv).next s s') :
    active_has_budget s' := by
  unfold active_has_budget budget_unique invoke_complete Kav.Action.guard Kav.Action.next at *
  intro A hactive
  have hfa : s'.agent_active = s.agent_active := by grind
  have hactiveS : s.agent_active A := by rw [hfa] at hactive; exact hactive
  obtain ⟨L, hL⟩ := hahb A hactiveS
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
    · refine ⟨L - declass_weight (s.tool_conf_floor (s.invocation_tool inv)), ?_⟩
      rw [hbeq]; left
      refine ⟨rfl, Or.inl ⟨hcond, ?_⟩⟩
      intro b hb
      have hLb : L = b := hbu A L b ⟨hactiveS, hL, hb⟩
      rw [hLb]
    · exact ⟨L, by rw [hbeq]; left; exact ⟨rfl, Or.inr ⟨hcond, hL⟩⟩⟩
  · exact ⟨L, by rw [hbeq]; right; exact ⟨hAa, hL⟩⟩

/-- `budget_bounded` under `invoke_complete`: the debit branch yields `b - w ≤ b ≤ capacity`;
    the kept/framed branches reuse `budget_bounded s`. -/
private theorem ic_pres_bb (a : AgentId) (inv : InvocationId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hbb : budget_bounded s)
    (hn : (invoke_complete a inv).next s s') :
    budget_bounded s' := by
  unfold budget_bounded invoke_complete Kav.Action.next at *
  intro A L hL
  have hbeq : s'.agent_budget A L =
      ((A = a ∧
        ( ( (s.tool_output_bounded (s.invocation_tool inv)
             ∧ s.output_conforms a (s.invocation_tool inv)
             ∧ s.affordable a (declass_weight (s.tool_conf_floor (s.invocation_tool inv)))
             ∧ ¬ s.taint_levels a (s.tool_conf_floor (s.invocation_tool inv)))
            ∧ ∀ b, s.agent_budget a b →
                L = b - declass_weight (s.tool_conf_floor (s.invocation_tool inv)) )
          ∨ ( ¬ (s.tool_output_bounded (s.invocation_tool inv)
                 ∧ s.output_conforms a (s.invocation_tool inv)
                 ∧ s.affordable a (declass_weight (s.tool_conf_floor (s.invocation_tool inv)))
                 ∧ ¬ s.taint_levels a (s.tool_conf_floor (s.invocation_tool inv)))
              ∧ s.agent_budget a L ) ))
      ∨ (A ≠ a ∧ s.agent_budget A L)) := by grind
  rw [hbeq] at hL
  rcases hL with ⟨rfl, hcase⟩ | ⟨_, hkept⟩
  · rcases hcase with ⟨hendorsed, hdeb⟩ | ⟨_, hkept⟩
    · obtain ⟨b, hb, _⟩ := hendorsed.2.2.1
      have hLb : L = b - declass_weight (s.tool_conf_floor (s.invocation_tool inv)) := hdeb b hb
      have hbc : b ≤ budget_capacity := hbb A b hb
      omega
    · exact hbb A L hkept
  · exact hbb A L hkept

theorem pres_invoke_complete
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hinv : allInv s)
    (hn : (Kav.close2 invoke_complete).next s s') : allInv s' := by
  simp only [Kav.close2] at hn
  obtain ⟨a, invid, hg, hn⟩ := hn
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hbu, hahb, hbb, _, _, _, _⟩ := hinv
  have hbudget : budget_unique s' := by
    simp only [budget_unique] at hbu ⊢
    simp only [active_has_budget] at hahb
    simp only [invoke_complete] at hn
    simp_all <;> grind
  have hahb' : active_has_budget s' := ic_pres_ahb a invid s s' hahb hbu hg hn
  have hbb' : budget_bounded s' := ic_pres_bb a invid s s' hbb hn
  unfold allInv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hbudget, hahb', hbb', ?_, ?_, ?_, ?_⟩
  all_goals_fresh (
    (try simp only [invoke_complete, allInv,
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
