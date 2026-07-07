import Tzimtzum.Soundness.Common

/-! # Campaign B — `sentinel_credit_budget` preservation

The saturating budget credit (`budget_saturating_credit b n = min budget_capacity (b + n)`)
is `@[irreducible]` (its `min` corrupts the transitive-unfold discharge — same reason
`ceilingAdmits` is irreducible), so the shared cascade cannot reconstruct the
`≤ budget_capacity` bound for `budget_bounded`. It is slotted in manually; the other 20
conjuncts close under the per-goal-fresh cascade. -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId : Type}

open Classical in
/-- `budget_bounded` under `sentinel_credit_budget`: the credit is `≤ budget_capacity` via
    `Nat.min_le_left`; framed agents reuse `budget_bounded s`. -/
private theorem scb_pres_bb (a : AgentId) (n : Nat)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hbb : budget_bounded s)
    (hn : (sentinel_credit_budget a n).next s s') :
    budget_bounded s' := by
  unfold budget_bounded sentinel_credit_budget Kav.Action.next at *
  intro A
  have hbeq : s'.agent_budget A =
      (if A = a then budget_saturating_credit (s.agent_budget a) n else s.agent_budget A) := by
    grind
  rw [hbeq]
  by_cases hAa : A = a
  · rw [if_pos hAa]; unfold budget_saturating_credit; exact Nat.min_le_left _ _
  · rw [if_neg hAa]; exact hbb A

theorem pres_sentinel_credit_budget
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hinv : allInv s)
    (hn : (Kav.close2 sentinel_credit_budget).next s s') : allInv s' := by
  simp only [Kav.close2] at hn
  obtain ⟨a, n, hg, hn⟩ := hn
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hbb, _, _⟩ := hinv
  have hbb' : budget_bounded s' := scb_pres_bb a n s s' hbb hn
  unfold allInv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hbb', ?_, ?_⟩
  all_goals_fresh (
    (try simp only [sentinel_credit_budget, allInv,
        root_always_active, default_deny, flow_confinement, flow_confinement_weak,
        capability_subsumption, revocation_clean, tool_attestation_intact,
        instruction_attestation_intact, override_consumed_when_sole_justification,
        parent_implies_active, single_parent, no_self_parent, root_no_parent,
        in_flight_active, in_flight_registered, in_flight_unique, root_all_caps,
        root_no_in_flight, budget_bounded,
        in_flight_flow_compat, in_flight_override_consumed,
        Tzimtzum.speculative_taint, Kav.Action.guard, Kav.Action.next] at *) <;>
      (first | trivial | grind | (simp_all <;> grind) | auto | duper [*]))

end Tzimtzum
