import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 4000000

namespace Tzimtzum

private def retEnd : KAgent → KAgent → ConfLevel → IntegLevel → Kav.Action KSt := return_endorsed

-- All invariants except `revocation_clean`, proved manually below (same cascade stall as
-- `invoke_complete_endorsed`: the classical `ite` inside the untouched `agent_budget`
-- conjunct, not `revocation_clean`'s own logic).
private def invsAuto : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ≠ "revocation_clean")

#kav_check_action retEnd invsAuto

-- Manual proof of the one resistant VC: `revocation_clean` under `return_endorsed`.
theorem return_endorsed_pres_revocation_clean
    (child prnt : KAgent) (clvl : ConfLevel) (ilvl : IntegLevel) (s s' : KSt)
    (hrc : revocation_clean s)
    (_hg : (retEnd child prnt clvl ilvl).guard s)
    (hn : (retEnd child prnt clvl ilvl).next s s') :
    revocation_clean s' := by
  unfold revocation_clean retEnd return_endorsed Kav.Action.next at *
  have hactive : s'.agent_active = s.agent_active := by grind
  intro A I L Li hna
  rw [hactive] at hna
  obtain ⟨hinf, htaint, hinteg⟩ := hrc A I L Li hna
  exact ⟨by grind, by grind, by grind⟩

-- Axiom audit: must depend only on [propext, Classical.choice, Quot.sound].
#print axioms return_endorsed_pres_revocation_clean

-- Acceptance criterion: a declared `clvl` strictly below a level the child actually holds
-- fails the coverage guard, so `return_endorsed` cannot fire (no-arbitrage pricing — the
-- declaration cannot omit part of the child's taint set to under-price the return).
theorem return_endorsed_coverage_required
    (child prnt : KAgent) (clvl heldL : ConfLevel) (ilvl : IntegLevel) (s : KSt)
    (hheld : s.taint_levels child heldL) (hbelow : ¬ le_conf heldL clvl) :
    ¬ (retEnd child prnt clvl ilvl).guard s := by
  unfold retEnd return_endorsed
  intro ⟨_, _, _, _, _, _, hcov, _, _⟩
  exact hbelow (hcov heldL hheld)

-- Acceptance criterion: a declared `ilvl` strictly ABOVE a level the child actually holds
-- fails the integ coverage guard (dual direction: `ilvl` must LOWER-bound the child's entire
-- integ set, since integrity is a meet/min lattice — no-arbitrage pricing on the integ side).
theorem return_endorsed_integ_coverage_required
    (child prnt : KAgent) (clvl : ConfLevel) (ilvl heldL : IntegLevel) (s : KSt)
    (hheld : s.integ_levels child heldL) (habove : ¬ le_integ ilvl heldL) :
    ¬ (retEnd child prnt clvl ilvl).guard s := by
  unfold retEnd return_endorsed
  intro ⟨_, _, _, _, _, _, _, hcov, _⟩
  exact habove (hcov heldL hheld)

-- Acceptance criterion: an untainted, clean child returning at `(clvl, ilvl) = (public,
-- attested)` debits 0 (`declass_weight public = integ_weight attested = 0` — endorsing
-- nothing costs nothing on either dimension).
theorem return_endorsed_public_debit_zero : declass_weight ConfLevel.«public» = 0 := rfl

theorem return_endorsed_attested_debit_zero : integ_weight IntegLevel.attested = 0 := rfl

end Tzimtzum
