import Tzimtzum.Soundness.Common

/-! # Campaign B — `sentinel_credit_budget` preservation

The saturating budget credit (`L = budget_saturating_credit b n = min budget_capacity (b + n)`)
makes the three budget VCs resistant to the per-goal-fresh cascade: `budget_saturating_credit`
is `@[irreducible]` (its `min` corrupts the transitive-unfold discharge — same reason
`ceilingAdmits` is irreducible), so the cascade cannot reconstruct the post-budget witness or
the `≤ budget_capacity` bound. Each is slotted in manually:

* `active_has_budget` / `budget_unique`: witness `budget_saturating_credit L n` for the unique
  `active_has_budget` level `L`.
* `budget_bounded`: `budget_saturating_credit b n ≤ budget_capacity` via `Nat.min_le_left`.

The other 20 conjuncts are frame-trivial w.r.t. `agent_budget` and close under the cascade
(which leaves the irreducible credit atom alone). -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId : Type}

/-- `active_has_budget` under `sentinel_credit_budget`: witness `budget_saturating_credit L n`
    for the unique level `L`; `budget_unique` pins every `b` to `L`. For `A ≠ a` framed. -/
private theorem scb_pres_ahb (a : AgentId) (n : Nat)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hahb : active_has_budget s)
    (hbu : budget_unique s)
    (hg : (sentinel_credit_budget a n).guard s)
    (hn : (sentinel_credit_budget a n).next s s') :
    active_has_budget s' := by
  unfold active_has_budget budget_unique sentinel_credit_budget Kav.Action.guard
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

/-- `budget_unique` under `sentinel_credit_budget`: for `A = a` both post levels are
    `budget_saturating_credit b n` for the unique pre-budget; for `A ≠ a` framed. -/
private theorem scb_pres_bu (a : AgentId) (n : Nat)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hahb : active_has_budget s)
    (hbu : budget_unique s)
    (hg : (sentinel_credit_budget a n).guard s)
    (hn : (sentinel_credit_budget a n).next s s') :
    budget_unique s' := by
  unfold budget_unique active_has_budget sentinel_credit_budget Kav.Action.guard
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

/-- `budget_bounded` under `sentinel_credit_budget`: the credit is `≤ budget_capacity` via
    `Nat.min_le_left`; framed agents reuse `budget_bounded s`. -/
private theorem scb_pres_bb (a : AgentId) (n : Nat)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hahb : active_has_budget s)
    (hbb : budget_bounded s)
    (hg : (sentinel_credit_budget a n).guard s)
    (hn : (sentinel_credit_budget a n).next s s') :
    budget_bounded s' := by
  unfold budget_bounded active_has_budget sentinel_credit_budget Kav.Action.guard
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

theorem pres_sentinel_credit_budget
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hinv : allInv s)
    (hn : (Kav.close2 sentinel_credit_budget).next s s') : allInv s' := by
  simp only [Kav.close2] at hn
  obtain ⟨a, n, hg, hn⟩ := hn
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      hbu, hahb, hbb, _, _⟩ := hinv
  have hbu' : budget_unique s' := scb_pres_bu a n s s' hahb hbu hg hn
  have hahb' : active_has_budget s' := scb_pres_ahb a n s s' hahb hbu hg hn
  have hbb' : budget_bounded s' := scb_pres_bb a n s s' hahb hbb hg hn
  unfold allInv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      hbu', hahb', hbb', ?_, ?_⟩
  all_goals_fresh (
    (try simp only [sentinel_credit_budget, allInv,
        root_always_active, default_deny, flow_confinement, flow_confinement_weak,
        capability_subsumption, revocation_clean, tool_attestation_intact,
        instruction_attestation_intact, override_consumed_when_sole_justification,
        parent_implies_active, single_parent, no_self_parent, root_no_parent,
        in_flight_active, in_flight_registered, in_flight_unique, root_all_caps,
        root_no_in_flight, budget_unique, active_has_budget, budget_bounded,
        in_flight_flow_compat, in_flight_override_consumed,
        Tzimtzum.speculative_taint, Kav.Action.guard, Kav.Action.next] at *) <;>
      (first | trivial | grind | (simp_all <;> grind) | auto | duper [*]))

end Tzimtzum
