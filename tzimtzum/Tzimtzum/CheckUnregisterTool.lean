import Tzimtzum.Soundness.Common

/-! `unregister_tool` preserves the bundle (one theorem per sub-bundle). The guard's
`no_pending_use`/`no_challenge_use` clauses keep every retained pending or challenged tool
registered, so every conjunct is fully automated (lite cascade; gates stay atomic). -/

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
theorem presS_unregister_tool (tool : ToolId) :
    Preserves (unregister_tool tool : Kav.Action St!) invS := by
  intro s s' hinv hg hn
  kav_discharge_lite unregister_tool

/-- `invP` (12 pending/gate conjuncts): fully automated. -/
theorem presP_unregister_tool (tool : ToolId) :
    Preserves (unregister_tool tool : Kav.Action St!) invP := by
  intro s s' hinv hg hn
  kav_discharge_lite unregister_tool

/-- `invPP` (2 pairwise conjuncts): fully automated. -/
theorem presPP_unregister_tool (tool : ToolId) :
    Preserves (unregister_tool tool : Kav.Action St!) invPP := by
  intro s s' hinv hg hn
  kav_discharge_lite unregister_tool

/-- `invE` (6 evidence conjuncts): fully automated. -/
theorem presE_unregister_tool (tool : ToolId) :
    Preserves (unregister_tool tool : Kav.Action St!) invE := by
  intro s s' hinv hg hn
  kav_discharge_lite unregister_tool

/-- `invC` (3 crossing conjuncts): fully automated. -/
theorem presC_unregister_tool (tool : ToolId) :
    Preserves (unregister_tool tool : Kav.Action St!) invC := by
  intro s s' hinv hg hn
  kav_discharge_lite unregister_tool

/-- Combines preservation of all invariant sub-bundles. -/
theorem pres_unregister_tool (tool : ToolId) :
    Preserves (unregister_tool tool : Kav.Action St!) allInv :=
  fun s s' hinv hg hn =>
    ⟨presS_unregister_tool tool s s' hinv hg hn,
     presP_unregister_tool tool s s' hinv hg hn,
     presPP_unregister_tool tool s s' hinv hg hn,
     presE_unregister_tool tool s s' hinv hg hn,
     presC_unregister_tool tool s s' hinv hg hn⟩

-- The proof must use only `propext`, `Classical.choice`, and `Quot.sound`.
-- Native reduction would add `Lean.ofReduceBool` to the trust base.
#print axioms pres_unregister_tool

end Tzimtzum
