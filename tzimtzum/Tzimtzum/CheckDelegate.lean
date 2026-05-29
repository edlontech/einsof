import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 2000000

namespace Tzimtzum

private def dlg : KAgent → KAgent → Kav.Action KSt := delegate
private def invs : List (Kav.Invariant KSt) := allInvariants

#kav_check_action dlg invs

end Tzimtzum
