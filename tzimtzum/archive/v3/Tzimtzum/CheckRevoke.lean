import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 2000000

namespace Tzimtzum

private def rvk : KAgent → KAgent → Kav.Action KSt := revoke
private def invs : List (Kav.Invariant KSt) := allInvariants

#kav_check_action rvk invs

end Tzimtzum
