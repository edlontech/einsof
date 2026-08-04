import Tzimtzum.Soundness.Common

/-! # Task 7 — `grant_capability` preserves the bundle (one theorem per sub-bundle). -/

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

/-- The full-bundle preservation lemma Tasks 11+ and the soundness assembly consume. -/
theorem pres_grant_capability (prnt child : AgentId) (cap : CapKind)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (grant_capability prnt child cap).guard s) (hn : (grant_capability prnt child cap).next s s') : allInv s' :=
  ⟨presS_grant_capability prnt child cap s s' hinv hg hn,
   presP_grant_capability prnt child cap s s' hinv hg hn,
   presPP_grant_capability prnt child cap s s' hinv hg hn,
   presE_grant_capability prnt child cap s s' hinv hg hn,
   presC_grant_capability prnt child cap s s' hinv hg hn⟩

-- Axiom audit (in place, per the V3 manual-VC pattern): the cascades end in `auto`/`duper`
-- under `auto.native true`, so a natively-compiled closure would add `Lean.ofReduceBool`
-- to the trust base silently. These must print only `propext`, `Classical.choice`,
-- `Quot.sound`.
#print axioms pres_grant_capability

end Tzimtzum
