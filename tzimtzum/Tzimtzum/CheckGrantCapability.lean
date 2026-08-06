import Tzimtzum.Soundness.Common

/-! `grant_capability` preserves the bundle (one theorem per sub-bundle). -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

theorem presS_grant_capability (prnt child : AgentId) (cap : CapKind)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (grant_capability prnt child cap).guard s) (hn : (grant_capability prnt child cap).next s s') : invS s' := by
  kav_discharge_lite grant_capability

theorem presP_grant_capability (prnt child : AgentId) (cap : CapKind)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (grant_capability prnt child cap).guard s) (hn : (grant_capability prnt child cap).next s s') : invP s' := by
  kav_discharge_lite grant_capability

theorem presPP_grant_capability (prnt child : AgentId) (cap : CapKind)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (grant_capability prnt child cap).guard s) (hn : (grant_capability prnt child cap).next s s') : invPP s' := by
  kav_discharge_lite grant_capability

theorem presE_grant_capability (prnt child : AgentId) (cap : CapKind)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (grant_capability prnt child cap).guard s) (hn : (grant_capability prnt child cap).next s s') : invE s' := by
  kav_discharge_lite grant_capability

theorem presC_grant_capability (prnt child : AgentId) (cap : CapKind)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (grant_capability prnt child cap).guard s) (hn : (grant_capability prnt child cap).next s s') : invC s' := by
  kav_discharge_lite grant_capability

/-- Combines preservation of all invariant sub-bundles. -/
theorem pres_grant_capability (prnt child : AgentId) (cap : CapKind)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (grant_capability prnt child cap).guard s) (hn : (grant_capability prnt child cap).next s s') : allInv s' :=
  ⟨presS_grant_capability prnt child cap s s' hinv hg hn,
   presP_grant_capability prnt child cap s s' hinv hg hn,
   presPP_grant_capability prnt child cap s s' hinv hg hn,
   presE_grant_capability prnt child cap s s' hinv hg hn,
   presC_grant_capability prnt child cap s s' hinv hg hn⟩

-- The proof must use only `propext`, `Classical.choice`, and `Quot.sound`.
-- Native reduction would add `Lean.ofReduceBool` to the trust base.
#print axioms pres_grant_capability

end Tzimtzum
