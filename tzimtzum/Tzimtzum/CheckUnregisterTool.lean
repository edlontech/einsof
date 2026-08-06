import Tzimtzum.Soundness.Common

/-! `unregister_tool` preserves the bundle (one theorem per sub-bundle). -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

theorem presS_unregister_tool (tool : ToolId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (unregister_tool tool).guard s) (hn : (unregister_tool tool).next s s') : invS s' := by
  kav_discharge_lite unregister_tool

theorem presP_unregister_tool (tool : ToolId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (unregister_tool tool).guard s) (hn : (unregister_tool tool).next s s') : invP s' := by
  kav_discharge_lite unregister_tool

theorem presPP_unregister_tool (tool : ToolId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (unregister_tool tool).guard s) (hn : (unregister_tool tool).next s s') : invPP s' := by
  kav_discharge_lite unregister_tool

theorem presE_unregister_tool (tool : ToolId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (unregister_tool tool).guard s) (hn : (unregister_tool tool).next s s') : invE s' := by
  kav_discharge_lite unregister_tool

theorem presC_unregister_tool (tool : ToolId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (unregister_tool tool).guard s) (hn : (unregister_tool tool).next s s') : invC s' := by
  kav_discharge_lite unregister_tool

/-- Combines preservation of all invariant sub-bundles. -/
theorem pres_unregister_tool (tool : ToolId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (unregister_tool tool).guard s) (hn : (unregister_tool tool).next s s') : allInv s' :=
  ⟨presS_unregister_tool tool s s' hinv hg hn,
   presP_unregister_tool tool s s' hinv hg hn,
   presPP_unregister_tool tool s s' hinv hg hn,
   presE_unregister_tool tool s s' hinv hg hn,
   presC_unregister_tool tool s s' hinv hg hn⟩

-- The proof must use only `propext`, `Classical.choice`, and `Quot.sound`.
-- Native reduction would add `Lean.ofReduceBool` to the trust base.
#print axioms pres_unregister_tool

end Tzimtzum
