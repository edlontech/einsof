import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 4000000

namespace Tzimtzum

private def invComp : KAgent → KInv → Kav.Action KSt := invoke_complete

-- All invariants except `revocation_clean`, proved manually below: the cascade's shared
-- `simp_all`/`grind` call chokes on the classical `Decidable` instance inside the untouched
-- `agent_budget` point-update while trying to case-split it, even though
-- `revocation_clean`'s conclusion never mentions `agent_budget` (same root cause the
-- function-field budget spike documents; `budget_bounded` itself discharges fine here
-- because ITS conclusion is exactly what forces the case split).
private def invsAuto : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ≠ "revocation_clean")

#kav_check_action invComp invsAuto

-- Manual proof of the one resistant VC: `revocation_clean` under `invoke_complete`. Only
-- the `agent_active` frame is needed to relate `s'`'s inactive agents to `s`'s; the
-- `in_flight`/`taint_levels` obligations then close directly without ever touching the
-- `agent_budget` conjunct.
theorem invoke_complete_pres_revocation_clean
    (a : KAgent) (inv : KInv) (s s' : KSt)
    (hrc : revocation_clean s)
    (_hg : (invComp a inv).guard s) (hn : (invComp a inv).next s s') :
    revocation_clean s' := by
  unfold revocation_clean invComp invoke_complete Kav.Action.next at *
  have hactive : s'.agent_active = s.agent_active := by grind
  intro A I L hna
  rw [hactive] at hna
  obtain ⟨hinf, htaint⟩ := hrc A I L hna
  exact ⟨by grind, by grind⟩

-- Axiom audit: must depend only on [propext, Classical.choice, Quot.sound].
#print axioms invoke_complete_pres_revocation_clean

end Tzimtzum
