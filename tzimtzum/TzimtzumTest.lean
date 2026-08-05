-- TzimtzumV4 verification aggregator.
-- Build with: lake build TzimtzumTest
--
-- Every action check is imported explicitly so this target fails if any preservation
-- module, reachable-state crown, per-transition theorem, or audit theorem stops compiling.
import Tzimtzum.CheckInit
import Tzimtzum.CheckRegisterTool
import Tzimtzum.CheckUnregisterTool
import Tzimtzum.CheckDelegate
import Tzimtzum.CheckGrantCapability
import Tzimtzum.CheckGrantCrossing
import Tzimtzum.CheckRevoke
import Tzimtzum.CheckCascadeRevoke
import Tzimtzum.CheckIngest
import Tzimtzum.CheckBeginInvocation
import Tzimtzum.CheckAuthorizeInspected
import Tzimtzum.CheckSettleInvocation
import Tzimtzum.CheckCrossOutput
import Tzimtzum.Soundness
import Tzimtzum.GrantConservation
import Tzimtzum.Transitions
import Tzimtzum.Audit
