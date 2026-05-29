import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 2000000

namespace Tzimtzum

private def loadInstr : KAgent → KInstr → Kav.Action KSt := load_instruction
private def invs : List (Kav.Invariant KSt) := allInvariants

#kav_check_action loadInstr invs

end Tzimtzum
