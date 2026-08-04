import Tzimtzum.OpaqueTypes
import Kav.CheckAction

set_option maxHeartbeats 4000000

namespace Tzimtzum

private def invCompEnd : KAgent → KInv → Kav.Action KSt := invoke_complete_endorsed

-- All invariants except `revocation_clean`, proved manually below: same cascade stall as the
-- pre-split `invoke_complete` (and every other budget-touching action) — the shared
-- `simp_all`/`grind` call chokes on the classical `Decidable` instance inside the untouched
-- `agent_budget` conjunct while trying to case-split it, even though `revocation_clean`'s
-- conclusion never mentions `agent_budget`.
private def invsAuto : List (Kav.Invariant KSt) :=
  allInvariants.filter (fun p => p.1 ≠ "revocation_clean")

#kav_check_action invCompEnd invsAuto

-- Manual proof of the one resistant VC: `revocation_clean` under `invoke_complete_endorsed`.
-- Only the `agent_active` frame is needed to relate `s'`'s inactive agents to `s`'s; the
-- `in_flight`/`taint_levels` obligations then close directly without ever touching the
-- `agent_budget` conjunct.
theorem invoke_complete_endorsed_pres_revocation_clean
    (a : KAgent) (inv : KInv) (s s' : KSt)
    (hrc : revocation_clean s)
    (_hg : (invCompEnd a inv).guard s) (hn : (invCompEnd a inv).next s s') :
    revocation_clean s' := by
  unfold revocation_clean invCompEnd invoke_complete_endorsed Kav.Action.next at *
  have hactive : s'.agent_active = s.agent_active := by grind
  intro A I L Li hna
  rw [hactive] at hna
  obtain ⟨hinf, htaint, hinteg⟩ := hrc A I L Li hna
  exact ⟨by grind, by grind, by grind⟩

-- Axiom audit: must depend only on [propext, Classical.choice, Quot.sound].
#print axioms invoke_complete_endorsed_pres_revocation_clean

-- Acceptance criterion: missing `cap_declassify` routes to the unendorsed action. Since
-- `crossing_ok` requires `agent_cap a s.cap_declassify` as one of its conjuncts, a missing
-- capability negates `crossing_ok` outright — the guard of `invoke_complete_endorsed` is
-- unsatisfiable, so completion can only take the `invoke_complete_unendorsed` branch
-- (fail-safe, design finding 11).
theorem missing_cap_declassify_routes_unendorsed
    (s : KSt) (a : KAgent) (inv : KInv)
    (hcap : ¬ s.agent_cap a s.cap_declassify) :
    ¬ crossing_ok s a inv := by
  unfold crossing_ok
  rintro ⟨_, _, hc, _, _⟩
  exact hcap hc

-- Acceptance criterion (Task 12): neither dimension helping makes `crossing_ok`'s last
-- conjunct (`conf_helps ∨ integ_helps`) unsatisfiable, so the crossing routes to
-- `invoke_complete_unendorsed` with zero debit — the wasted-budget generalization
-- (design §5.4 / §6 "Neither-dimension-helps crossings").
theorem neither_helps_routes_unendorsed
    (s : KSt) (a : KAgent) (inv : KInv)
    (hconf : ¬ conf_helps s a inv) (hinteg : ¬ integ_helps s a inv) :
    ¬ crossing_ok s a inv := by
  unfold crossing_ok
  rintro ⟨_, _, _, _, hc | hi⟩
  exacts [hconf hc, hinteg hi]

-- Acceptance criterion (Task 12): an already-conf-tainted agent (`conf_helps` false)
-- endorsing an untrusted-emission tool (`integ_helps` true) is charged EXACTLY
-- `integ_weight` of the tool's emission — the dimension-adjusted debit skips the conf half
-- entirely rather than wasting budget on a crossing that wouldn't newly cap the taint set.
theorem crossing_weight_conf_tainted
    (s : KSt) (a : KAgent) (inv : KInv)
    (hconf : ¬ conf_helps s a inv) (hinteg : integ_helps s a inv) :
    crossing_weight s a inv = integ_weight (s.tool_output_integ (s.invocation_tool inv)) := by
  unfold crossing_weight
  simp [hconf, hinteg]

end Tzimtzum
