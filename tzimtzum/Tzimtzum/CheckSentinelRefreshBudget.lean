import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 2000000

namespace Tzimtzum

private def refreshBudget : KAgent → Kav.Action KSt := sentinel_refresh_budget
private def invs : List (Kav.Invariant KSt) := allInvariants

#kav_check_action refreshBudget invs

end Tzimtzum
