import Tzimtzum.Soundness.Common

/-! # Task 7 — `unregister_tool` preserves the bundle (one theorem per sub-bundle). -/

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

/-- The full-bundle preservation lemma Tasks 11+ and the soundness assembly consume. -/
theorem pres_unregister_tool (tool : ToolId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (unregister_tool tool).guard s) (hn : (unregister_tool tool).next s s') : allInv s' :=
  ⟨presS_unregister_tool tool s s' hinv hg hn,
   presP_unregister_tool tool s s' hinv hg hn,
   presPP_unregister_tool tool s s' hinv hg hn,
   presE_unregister_tool tool s s' hinv hg hn,
   presC_unregister_tool tool s s' hinv hg hn⟩

-- Axiom audit (in place, per the V3 manual-VC pattern): the cascades end in `auto`/`duper`
-- under `auto.native true`, so a natively-compiled closure would add `Lean.ofReduceBool`
-- to the trust base silently. These must print only `propext`, `Classical.choice`,
-- `Quot.sound`.
#print axioms pres_unregister_tool

end Tzimtzum
