import Tzimtzum.Soundness.Common

/-! # C0 — `invoke_complete` preservation

The structurally largest action. The function-encoded budget's self-debit was, in the
relational encoding, resistant enough to need three manual VCs; under the function
encoding the shared per-goal-fresh cascade (`kav_discharge`) discharges every conjunct,
`budget_bounded` included, automatically. -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId : Type}

theorem pres_invoke_complete
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hinv : allInv s)
    (hn : (Kav.close2 invoke_complete).next s s') : allInv s' := by
  simp only [Kav.close2] at hn
  obtain ⟨a, invid, hg, hn⟩ := hn
  kav_discharge invoke_complete

end Tzimtzum
