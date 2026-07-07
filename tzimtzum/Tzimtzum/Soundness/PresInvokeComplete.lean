import Tzimtzum.Soundness.Common

/-! # C0 — `invoke_complete_endorsed` / `invoke_complete_unendorsed` preservation

Split per design "invoke_complete shape" (Task 7): complementary total guards over the
shared `crossing_ok` predicate instead of one embedded conditional. The function-encoded
budget's self-debit was, in the relational encoding, resistant enough to need three manual
VCs; under the function encoding the shared per-goal-fresh cascade (`kav_discharge`)
discharges every conjunct, `budget_bounded` included, automatically for both actions. -/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId : Type}

theorem pres_invoke_complete_endorsed
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hinv : allInv s)
    (hn : (Kav.close2 invoke_complete_endorsed).next s s') : allInv s' := by
  simp only [Kav.close2] at hn
  obtain ⟨a, invid, hg, hn⟩ := hn
  kav_discharge invoke_complete_endorsed

theorem pres_invoke_complete_unendorsed
    (s s' : St AgentId ToolId InvocationId CapKind EgressKind IssuerId InstructionId)
    (hinv : allInv s)
    (hn : (Kav.close2 invoke_complete_unendorsed).next s s') : allInv s' := by
  simp only [Kav.close2] at hn
  obtain ⟨a, invid, hg, hn⟩ := hn
  kav_discharge invoke_complete_unendorsed

end Tzimtzum
