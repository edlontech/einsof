import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 2000000

namespace Tzimtzum

private def grantCap : KAgent → KAgent → KCap → Kav.Action KSt := grant_capability
private def invs : List (Kav.Invariant KSt) := allInvariants

#kav_check_action grantCap invs

end Tzimtzum
