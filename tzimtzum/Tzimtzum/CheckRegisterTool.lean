import Tzimtzum.Soundness.Common

/-! # Task 7 — `register_tool` preserves the bundle (one theorem per sub-bundle). -/

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

/-- The full-bundle preservation lemma Tasks 11+ and the soundness assembly consume. -/
theorem pres_register_tool (tool : ToolId)
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (hinv : allInv s) (hg : (register_tool tool).guard s) (hn : (register_tool tool).next s s') : allInv s' :=
  ⟨presS_register_tool tool s s' hinv hg hn,
   presP_register_tool tool s s' hinv hg hn,
   presPP_register_tool tool s s' hinv hg hn,
   presE_register_tool tool s s' hinv hg hn,
   presC_register_tool tool s s' hinv hg hn⟩

-- Axiom audit (in place, per the V3 manual-VC pattern): the cascades end in `auto`/`duper`
-- under `auto.native true`, so a natively-compiled closure would add `Lean.ofReduceBool`
-- to the trust base silently. These must print only `propext`, `Classical.choice`,
-- `Quot.sound`.
#print axioms pres_register_tool

end Tzimtzum
