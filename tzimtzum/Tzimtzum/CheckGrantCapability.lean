import Tzimtzum.Soundness.Common

/-! `grant_capability` preserves the bundle (one theorem per sub-bundle). The guard's
`parent_holds` clause keeps `capability_subsumption` inductive and no label, pending, or
grant state changes, so every conjunct is fully automated (lite cascade; gates stay
atomic). -/

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
theorem presS_grant_capability (prnt child : AgentId) (cap : CapKind) :
    Preserves (grant_capability prnt child cap : Kav.Action St!) invS := by
  intro s s' hinv hg hn
  kav_discharge_lite grant_capability

/-- `invP` (12 pending/gate conjuncts): fully automated. -/
theorem presP_grant_capability (prnt child : AgentId) (cap : CapKind) :
    Preserves (grant_capability prnt child cap : Kav.Action St!) invP := by
  intro s s' hinv hg hn
  kav_discharge_lite grant_capability

/-- `invPP` (2 pairwise conjuncts): fully automated. -/
theorem presPP_grant_capability (prnt child : AgentId) (cap : CapKind) :
    Preserves (grant_capability prnt child cap : Kav.Action St!) invPP := by
  intro s s' hinv hg hn
  kav_discharge_lite grant_capability

/-- `invE` (6 evidence conjuncts): fully automated. -/
theorem presE_grant_capability (prnt child : AgentId) (cap : CapKind) :
    Preserves (grant_capability prnt child cap : Kav.Action St!) invE := by
  intro s s' hinv hg hn
  kav_discharge_lite grant_capability

/-- `invC` (3 crossing conjuncts): fully automated. -/
theorem presC_grant_capability (prnt child : AgentId) (cap : CapKind) :
    Preserves (grant_capability prnt child cap : Kav.Action St!) invC := by
  intro s s' hinv hg hn
  kav_discharge_lite grant_capability

/-- Combines preservation of all invariant sub-bundles. -/
theorem pres_grant_capability (prnt child : AgentId) (cap : CapKind) :
    Preserves (grant_capability prnt child cap : Kav.Action St!) allInv :=
  fun s s' hinv hg hn =>
    ⟨presS_grant_capability prnt child cap s s' hinv hg hn,
     presP_grant_capability prnt child cap s s' hinv hg hn,
     presPP_grant_capability prnt child cap s s' hinv hg hn,
     presE_grant_capability prnt child cap s s' hinv hg hn,
     presC_grant_capability prnt child cap s s' hinv hg hn⟩

-- The proof must use only `propext`, `Classical.choice`, and `Quot.sound`.
-- Native reduction would add `Lean.ofReduceBool` to the trust base.
#print axioms pres_grant_capability

end Tzimtzum
