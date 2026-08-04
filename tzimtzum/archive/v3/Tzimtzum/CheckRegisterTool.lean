import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 2000000

namespace Tzimtzum

private def regTool : KTool → Kav.Action KSt := register_tool
private def invs : List (Kav.Invariant KSt) := allInvariants

#kav_check_action regTool invs

end Tzimtzum
