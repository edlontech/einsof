import Tzimtzum.Soundness.Common
import Tzimtzum.CheckInit
import Tzimtzum.CheckRegisterTool
import Tzimtzum.CheckUnregisterTool
import Tzimtzum.CheckDelegate
import Tzimtzum.CheckGrantCapability
import Tzimtzum.CheckGrantCrossing
import Tzimtzum.CheckRevoke
import Tzimtzum.CheckCascadeRevoke

/-!
# TzimtzumV4 — soundness aggregator (Task 7 slice)

Init VCs plus the seven structural actions' full-bundle preservation lemmas. The remaining
five actions land in Tasks 8–10, and the `Kav.reachable_sound` assembly (`kav_sound` /
`kav_soundP`) lands once all twelve exist.
-/
