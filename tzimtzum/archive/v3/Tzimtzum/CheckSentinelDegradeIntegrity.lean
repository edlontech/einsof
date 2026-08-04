import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 4000000

namespace Tzimtzum

private def sentDegrade : KAgent → IntegLevel → Kav.Action KSt := sentinel_degrade_integrity
private def invs : List (Kav.Invariant KSt) := allInvariants

#kav_check_action sentDegrade invs

end Tzimtzum
