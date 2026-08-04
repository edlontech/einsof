import Tzimtzum.Soundness.Common

/-! # Campaign A — `grant_override` preservation

Under the function-encoded budget the shared per-goal-fresh cascade (`kav_discharge`)
discharges every conjunct automatically — no manual VC needed (the relational encoding's
`active_has_budget` witness-reconstruction problem no longer exists). -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId : Type}

theorem pres_grant_override
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hinv : allInv s)
    (hn : (Kav.close4 grant_override).next s s') : allInv s' := by
  simp only [Kav.close4] at hn
  obtain ⟨granter, target, tool, lvl, hg, hn⟩ := hn
  kav_discharge grant_override

end Tzimtzum
