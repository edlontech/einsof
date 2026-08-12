import Tzimtzum.Soundness.Common

/-! `grant_crossing` preserves the bundle (one theorem per sub-bundle). Provisioning sets
one active agent's exact-digest grant with `remaining = provisioned`, so `grant_bounded`,
`grant_active`, and `grant_pinned` hold on the new entry directly and everything else is a
frame; every conjunct is fully automated (lite cascade; gates stay atomic). -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-- The state at this file's sort tuple. The ascription in each `Preserves` statement pins
the sorts the action's arguments do not determine. -/
local notation "St!" => St AgentId ToolId InvocationId CapKind EgressKind ChallengeId
  AttestationId CrossingId AssignmentDigest PolicyDigest ContentHash

/-- `invS` (9 structural conjuncts): fully automated. -/
theorem presS_grant_crossing (grantor agent : AgentId) (d : AssignmentDigest) (n : Nat) :
    Preserves (grant_crossing grantor agent d n : Kav.Action St!) invS := by
  intro s s' hinv hg hn
  kav_discharge_lite grant_crossing

/-- `invP` (12 pending/gate conjuncts): fully automated. -/
theorem presP_grant_crossing (grantor agent : AgentId) (d : AssignmentDigest) (n : Nat) :
    Preserves (grant_crossing grantor agent d n : Kav.Action St!) invP := by
  intro s s' hinv hg hn
  kav_discharge_lite grant_crossing

/-- `invPP` (2 pairwise conjuncts): fully automated. -/
theorem presPP_grant_crossing (grantor agent : AgentId) (d : AssignmentDigest) (n : Nat) :
    Preserves (grant_crossing grantor agent d n : Kav.Action St!) invPP := by
  intro s s' hinv hg hn
  kav_discharge_lite grant_crossing

/-- `invE` (6 evidence conjuncts): fully automated. -/
theorem presE_grant_crossing (grantor agent : AgentId) (d : AssignmentDigest) (n : Nat) :
    Preserves (grant_crossing grantor agent d n : Kav.Action St!) invE := by
  intro s s' hinv hg hn
  kav_discharge_lite grant_crossing

/-- `invC` (3 crossing conjuncts): fully automated. -/
theorem presC_grant_crossing (grantor agent : AgentId) (d : AssignmentDigest) (n : Nat) :
    Preserves (grant_crossing grantor agent d n : Kav.Action St!) invC := by
  intro s s' hinv hg hn
  kav_discharge_lite grant_crossing

/-- Combines preservation of all invariant sub-bundles. -/
theorem pres_grant_crossing (grantor agent : AgentId) (d : AssignmentDigest) (n : Nat) :
    Preserves (grant_crossing grantor agent d n : Kav.Action St!) allInv :=
  fun s s' hinv hg hn =>
    ⟨presS_grant_crossing grantor agent d n s s' hinv hg hn,
     presP_grant_crossing grantor agent d n s s' hinv hg hn,
     presPP_grant_crossing grantor agent d n s s' hinv hg hn,
     presE_grant_crossing grantor agent d n s s' hinv hg hn,
     presC_grant_crossing grantor agent d n s s' hinv hg hn⟩

-- The proof must use only `propext`, `Classical.choice`, and `Quot.sound`.
-- Native reduction would add `Lean.ofReduceBool` to the trust base.
#print axioms pres_grant_crossing

end Tzimtzum
