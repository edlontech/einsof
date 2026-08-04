import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 2000000

namespace Tzimtzum

private def cascadeRvk : KAgent → KAgent → Kav.Action KSt := cascade_revoke
private def invs : List (Kav.Invariant KSt) := allInvariants

#kav_check_action cascadeRvk invs

end Tzimtzum
