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

/-!
# TzimtzumV4 — soundness aggregator (Tasks 7–8 slice)

Init VCs plus the seven structural actions and Task 8's three lighter commands. The remaining
two actions land in Tasks 9–10, and the `Kav.reachable_sound` assembly (`kav_sound` /
`kav_soundP`) lands once all twelve exist.
-/
