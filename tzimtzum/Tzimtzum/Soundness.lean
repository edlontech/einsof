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

/-!
# TzimtzumV4 — soundness aggregator (Tasks 7–9 slice)

Init VCs plus eleven actions: the seven structural actions, Task 8's three lighter commands,
and `begin_invocation`. `cross_output` lands in Task 10, and the `Kav.reachable_sound`
assembly (`kav_sound` / `kav_soundP`) lands once all twelve preservation lemmas exist.
-/
