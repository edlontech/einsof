-- Aggregator: per-action VC checks + axiom audit + C0 soundness bundle for the
-- TzimtzumV2 port.
-- Build with: lake build TzimtzumTest
--
-- All Check modules share opaque types via Tzimtzum.OpaqueTypes, so they can all
-- be co-imported without conflicts.
import Tzimtzum.CheckInit
import Tzimtzum.CheckRegisterTool
import Tzimtzum.CheckLoadInstruction
import Tzimtzum.CheckDelegate
import Tzimtzum.CheckGrantCapability
import Tzimtzum.CheckRevoke
import Tzimtzum.CheckCascadeRevoke
import Tzimtzum.CheckInvokeStart
import Tzimtzum.CheckInvokeComplete
import Tzimtzum.CheckReturnEndorsed
import Tzimtzum.CheckReturnUnendorsed
import Tzimtzum.CheckSentinelElevateTaint
import Tzimtzum.CheckSentinelRefreshBudget
import Tzimtzum.CheckGrantOverride
import Tzimtzum.Audit
import Tzimtzum.Soundness
