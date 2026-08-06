-- TzimtzumV4 verification aggregator.
--
-- Imports every action-preservation module and every soundness, transition, grant, and audit
-- theorem so this target typechecks the complete verification surface.
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
