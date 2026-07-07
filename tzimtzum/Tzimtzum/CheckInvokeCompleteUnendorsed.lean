import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 4000000

namespace Tzimtzum

private def invCompUnend : KAgent → KInv → Kav.Action KSt := invoke_complete_unendorsed

-- No `agent_budget` update in this action (the wasted-budget fix: an agent that cannot cross
-- cleanly is never charged), so unlike the endorsed branch this needs no manual proof at all.
-- Split into two `#kav_check_action` calls purely for automation stability: the shared
-- discharge cascade is markedly slower to search when all 26 conjuncts are combined into one
-- premise/goal batch (an automation heuristics quirk, not a logic gap — every invariant,
-- `revocation_clean` included, discharges automatically either way).
private def invsRest : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ≠ "revocation_clean")

private def invsRC : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 = "revocation_clean")

#kav_check_action invCompUnend invsRest
#kav_check_action invCompUnend invsRC

end Tzimtzum
