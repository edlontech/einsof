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
    (["root_always_active", "capability_subsumption", "revocation_clean", "taint_integrity",
      "tool_attestation_intact", "instruction_attestation_intact", "parent_implies_active",
      "single_parent", "no_self_parent", "root_no_parent", "in_flight_active",
      "in_flight_registered", "in_flight_unique", "root_all_caps", "root_no_in_flight",
      "budget_unique", "active_has_budget", "ghost_invoked_sound", "ghost_received_sound",
      "default_deny"] : List String))

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

end Tzimtzum
