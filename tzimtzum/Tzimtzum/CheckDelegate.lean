import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 2000000

namespace Tzimtzum

private def dlg : KAgent → KAgent → Kav.Action KSt := delegate

-- All invariants except `revocation_clean`, proved manually below (same cascade stall as
-- `invoke_complete`: the classical `ite` inside the untouched `agent_budget` conjunct).
private def invsAuto : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ≠ "revocation_clean")

#kav_check_action dlg invsAuto

-- Manual proof of the one resistant VC: `revocation_clean` under `delegate`. The grantee is
-- active post-state by construction (`agent_active := … ∨ A = grantee`), so the `A = grantee`
-- case is vacuous; every other agent is framed on `agent_active`.
theorem delegate_pres_revocation_clean
    (grantor grantee : KAgent) (s s' : KSt)
    (hrc : revocation_clean s)
    (_hg : (dlg grantor grantee).guard s) (hn : (dlg grantor grantee).next s s') :
    revocation_clean s' := by
  unfold revocation_clean dlg delegate Kav.Action.next at *
  intro A I L hna
  by_cases hAg : A = grantee
  · subst hAg
    exact absurd hna (by grind)
  · have hactive : s'.agent_active A = s.agent_active A := by grind
    rw [hactive] at hna
    obtain ⟨hinf, htaint⟩ := hrc A I L hna
    exact ⟨by grind, by grind⟩

-- Axiom audit: must depend only on [propext, Classical.choice, Quot.sound].
#print axioms delegate_pres_revocation_clean

end Tzimtzum
