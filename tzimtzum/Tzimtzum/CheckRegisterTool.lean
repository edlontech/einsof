import Tzimtzum.Soundness.Common

/-! `register_tool` preserves the bundle (one theorem per sub-bundle). -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

theorem presS_register_tool (tool : ToolId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (register_tool tool).guard s) (hn : (register_tool tool).next s s') : invS s' := by
  kav_discharge_lite register_tool

theorem presP_register_tool (tool : ToolId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (register_tool tool).guard s) (hn : (register_tool tool).next s s') : invP s' := by
  kav_discharge_lite register_tool

theorem presPP_register_tool (tool : ToolId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (register_tool tool).guard s) (hn : (register_tool tool).next s s') : invPP s' := by
  kav_discharge_lite register_tool

theorem presE_register_tool (tool : ToolId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (register_tool tool).guard s) (hn : (register_tool tool).next s s') : invE s' := by
  kav_discharge_lite register_tool

theorem presC_register_tool (tool : ToolId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (register_tool tool).guard s) (hn : (register_tool tool).next s s') : invC s' := by
  kav_discharge_lite register_tool

/-- Combines preservation of all invariant sub-bundles. -/
theorem pres_register_tool (tool : ToolId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (register_tool tool).guard s) (hn : (register_tool tool).next s s') : allInv s' :=
  ⟨presS_register_tool tool s s' hinv hg hn,
   presP_register_tool tool s s' hinv hg hn,
   presPP_register_tool tool s s' hinv hg hn,
   presE_register_tool tool s s' hinv hg hn,
   presC_register_tool tool s s' hinv hg hn⟩

-- The proof must use only `propext`, `Classical.choice`, and `Quot.sound`.
-- Native reduction would add `Lean.ofReduceBool` to the trust base.
#print axioms pres_register_tool

end Tzimtzum
