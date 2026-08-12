import Tzimtzum.Soundness.Common

/-! `register_tool` preserves the bundle (one theorem per sub-bundle). The tool registry
grows monotonically and no other state field changes, so every conjunct is fully automated
(lite cascade; gates stay atomic). -/

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
theorem presS_register_tool (tool : ToolId) :
    Preserves (register_tool tool : Kav.Action St!) invS := by
  intro s s' hinv hg hn
  kav_discharge_lite register_tool

/-- `invP` (12 pending/gate conjuncts): fully automated. -/
theorem presP_register_tool (tool : ToolId) :
    Preserves (register_tool tool : Kav.Action St!) invP := by
  intro s s' hinv hg hn
  kav_discharge_lite register_tool

/-- `invPP` (2 pairwise conjuncts): fully automated. -/
theorem presPP_register_tool (tool : ToolId) :
    Preserves (register_tool tool : Kav.Action St!) invPP := by
  intro s s' hinv hg hn
  kav_discharge_lite register_tool

/-- `invE` (6 evidence conjuncts): fully automated. -/
theorem presE_register_tool (tool : ToolId) :
    Preserves (register_tool tool : Kav.Action St!) invE := by
  intro s s' hinv hg hn
  kav_discharge_lite register_tool

/-- `invC` (3 crossing conjuncts): fully automated. -/
theorem presC_register_tool (tool : ToolId) :
    Preserves (register_tool tool : Kav.Action St!) invC := by
  intro s s' hinv hg hn
  kav_discharge_lite register_tool

/-- Combines preservation of all invariant sub-bundles. -/
theorem pres_register_tool (tool : ToolId) :
    Preserves (register_tool tool : Kav.Action St!) allInv :=
  fun s s' hinv hg hn =>
    ⟨presS_register_tool tool s s' hinv hg hn,
     presP_register_tool tool s s' hinv hg hn,
     presPP_register_tool tool s s' hinv hg hn,
     presE_register_tool tool s s' hinv hg hn,
     presC_register_tool tool s s' hinv hg hn⟩

-- The proof must use only `propext`, `Classical.choice`, and `Quot.sound`.
-- Native reduction would add `Lean.ofReduceBool` to the trust base.
#print axioms pres_register_tool

end Tzimtzum
