import Tzimtzum.Soundness.Common
import Tzimtzum.CheckInit
import Tzimtzum.CheckRegisterTool
import Tzimtzum.CheckUnregisterTool
import Tzimtzum.CheckDelegate
import Tzimtzum.CheckGrantCapability
import Tzimtzum.CheckGrantCrossing
import Tzimtzum.CheckRevoke
import Tzimtzum.CheckCascadeRevoke
import Tzimtzum.CheckIngest
import Tzimtzum.CheckSettleInvocation
import Tzimtzum.CheckAuthorizeInspected
import Tzimtzum.CheckBeginInvocation
import Tzimtzum.CheckCrossOutput

/-!
# TzimtzumV4 — soundness aggregator (Tasks 7–10)

Init VCs plus full-bundle preservation for all twelve actions. The `Kav.reachable_sound`
assembly (`kav_sound` / `kav_soundP`) lands in Task 11.
-/
