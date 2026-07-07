import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 4000000

namespace Tzimtzum

private def retEnd : KAgent → KAgent → Kav.Action KSt := return_endorsed

-- All invariants except `revocation_clean`, proved manually below (same cascade stall as
-- `invoke_complete_endorsed`: the classical `ite` inside the untouched `agent_budget`
-- conjunct, not `revocation_clean`'s own logic).
private def invsAuto : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ≠ "revocation_clean")

#kav_check_action retEnd invsAuto

-- Manual proof of the one resistant VC: `revocation_clean` under `return_endorsed`.
theorem return_endorsed_pres_revocation_clean
    (child prnt : KAgent) (s s' : KSt)
    (hrc : revocation_clean s)
    (_hg : (retEnd child prnt).guard s) (hn : (retEnd child prnt).next s s') :
    revocation_clean s' := by
  unfold revocation_clean retEnd return_endorsed Kav.Action.next at *
  have hactive : s'.agent_active = s.agent_active := by grind
  intro A I L hna
  rw [hactive] at hna
  obtain ⟨hinf, htaint⟩ := hrc A I L hna
  exact ⟨by grind, by grind⟩

-- Axiom audit: must depend only on [propext, Classical.choice, Quot.sound].
#print axioms return_endorsed_pres_revocation_clean

end Tzimtzum
