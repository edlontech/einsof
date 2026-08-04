import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 2000000

namespace Tzimtzum

private def unregTool : KTool → Kav.Action KSt := unregister_tool
private def invs : List (Kav.Invariant KSt) := allInvariants

#kav_check_action unregTool invs

-- Acceptance criterion: unregistering a tool with an in-flight invocation is unsatisfiable.
theorem unregister_tool_in_flight_denied
    (tool : KTool) (a : KAgent) (inv : KInv) (s : KSt)
    (hinf : s.in_flight a inv) (htool : s.invocation_tool inv = tool) :
    ¬ (unregTool tool).guard s := by
  unfold unregTool unregister_tool
  intro ⟨_, hguard⟩
  exact hguard a inv hinf htool

end Tzimtzum
