import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 4000000

namespace Tzimtzum

private def retUn : KAgent → KAgent → Kav.Action KSt := return_unendorsed
private def invs : List (Kav.Invariant KSt) := allInvariants

#kav_check_action retUn invs

end Tzimtzum
