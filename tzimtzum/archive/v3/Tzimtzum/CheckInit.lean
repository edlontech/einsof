import Tzimtzum.OpaqueTypes
import Kav.CheckInit

set_option maxHeartbeats 2000000

namespace Tzimtzum

private def init : KSt → Prop := initial
private def invs : List (Kav.Invariant KSt) := allInvariants

#kav_check_init init invs

end Tzimtzum
