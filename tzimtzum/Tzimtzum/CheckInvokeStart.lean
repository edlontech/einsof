import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 8000000

namespace Tzimtzum

private def invStart : KAgent → KTool → KInv → Kav.Action KSt := invoke_start

-- Group A: invariants whose VC the cascade is expected to discharge for `invoke_start`.
-- (Frame-trivial w.r.t. the two modified relations `in_flight` / `override_used`, plus the
-- simpler in_flight monotone ones.)
private def invsA : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ∈
    (["root_always_active", "capability_subsumption", "revocation_clean",
      "tool_attestation_intact", "instruction_attestation_intact", "parent_implies_active",
      "single_parent", "no_self_parent", "root_no_parent", "in_flight_active",
      "in_flight_registered", "in_flight_unique", "root_all_caps", "root_no_in_flight",
      "default_deny", "budget_bounded"] : List String))

#kav_check_action invStart invsA

-- Group B: the flow/override-sensitive invariants (touch the two modified relations
-- directly). Split into small batches so each VC window stays cheap (batch-elaboration
-- cost, not prover cost). The gates stay atomic via `ceilingAdmits` (see State.lean).
private def invsB1 : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ∈
    (["flow_confinement", "flow_confinement_weak"] : List String))

#kav_check_action invStart invsB1

private def invsB2 : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ∈
    (["override_consumed_when_sole_justification"] : List String))

#kav_check_action invStart invsB2

private def invsB3 : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ∈
    (["in_flight_flow_compat", "in_flight_override_consumed"] : List String))

#kav_check_action invStart invsB3

-- Group B4: the new egress-attestation + freshness invariants (Task 6). Made inductive by
-- the narrowing/coverage requires and the freshness require/update respectively.
private def invsB4 : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ∈
    (["in_flight_egress_attested", "in_flight_implies_used"] : List String))

#kav_check_action invStart invsB4

-- Group B5: the integrity invariants (Task 14). CHECK 4a makes `integrity_confinement`
-- inductive for the newly-added invocation; CHECK 4b/4c (both the in-flight and the
-- self-pair) make `in_flight_integ_compat` inductive, which in turn covers
-- `integrity_confinement`'s pre-existing in-flight invocations against the agent's
-- (possibly unchanged) integrity levels.
private def invsB5 : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ∈
    (["integrity_confinement", "integrity_confinement_weak",
      "in_flight_integ_compat"] : List String))

#kav_check_action invStart invsB5

-- Acceptance criterion (Task 11): CHECK 4a is unsatisfiable for an untrusted-tainted agent
-- against a trusted-floor tool — the ALLOW arm fails the rank comparison and the INSPECT
-- band (also pinned to `trusted`) fails it too, regardless of any vouch.
theorem invoke_start_check4a_untrusted_denied
    (a : KAgent) (tool : KTool) (inv : KInv) (s : KSt)
    (hheld : s.integ_levels a IntegLevel.untrusted)
    (hfloor : s.tool_integ_floor tool = IntegLevel.trusted)
    (hinspect : s.tool_integ_inspect_floor tool = IntegLevel.trusted) :
    ¬ (invStart a tool inv).guard s := by
  unfold invStart invoke_start
  intro ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, h4a, _, _⟩
  have hspec : speculative_integ s a IntegLevel.untrusted := Or.inl hheld
  rcases h4a IntegLevel.untrusted hspec with hallow | ⟨hinsp, _⟩
  · unfold St.integ_allows le_integ integRank at hallow
    rw [hfloor] at hallow
    simp at hallow
  · unfold St.integ_inspects le_integ integRank at hinsp
    rw [hinspect] at hinsp
    simp at hinsp

-- Acceptance criterion (Task 11): CHECK 4b is unsatisfiable for an untrusted-emission tool
-- against an in-flight invocation whose tool's floor is `trusted` — the "web_fetch completes
-- while delete_repo is in flight" hazard, structurally blocked regardless of any vouch.
theorem invoke_start_check4b_untrusted_emission_denied
    (a : KAgent) (tool : KTool) (inv I : KInv) (s : KSt)
    (hinflight : s.in_flight a I)
    (hemission : s.tool_output_integ tool = IntegLevel.untrusted)
    (hfloor : s.tool_integ_floor (s.invocation_tool I) = IntegLevel.trusted)
    (hinspect : s.tool_integ_inspect_floor (s.invocation_tool I) = IntegLevel.trusted) :
    ¬ (invStart a tool inv).guard s := by
  unfold invStart invoke_start
  intro ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, h4b, _⟩
  rcases h4b I hinflight with hallow | ⟨hinsp, _⟩
  · unfold St.integ_allows le_integ integRank at hallow
    rw [hemission, hfloor] at hallow
    simp at hallow
  · unfold St.integ_inspects le_integ integRank at hinsp
    rw [hemission, hinspect] at hinsp
    simp at hinsp

end Tzimtzum
