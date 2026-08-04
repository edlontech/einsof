import Tzimtzum.Actions
import Tzimtzum.Soundness.Bundle
import Tzimtzum.OpaqueTypes
import Kav.Reachable
import Kav.Engine
import Lean

/-!
# TzimtzumV4 — shared soundness infrastructure

The discharge machinery every `Check*.lean` module uses, ported from the Task 0 spike
(which measured it) and V3's `Soundness/Common.lean` (which invented it):

* `all_goals_fresh` — run a tactic on each goal under a FRESH heartbeat budget
  (`Core.withCurrHeartbeats`); one saturating conjunct must never starve the others.
* `kav_discharge` — split a (sub-)bundle goal into atomic conjuncts
  (`repeat' apply And.intro` stops exactly at the opaque conjunct names, so the split never
  needs renumbering), then run the pinned cascade per conjunct with the **full** unfold set
  (gate predicates exposed) — for the conjuncts the gate makes inductive.
* `kav_discharge_lite` — same split, but the gate predicates (`beginAllow`,
  `beginAdmissible`, the `check*`s, `authorizeAdmits`, `endorsedOK`, the holds) stay
  **atoms**. Frame-ish conjuncts pay nothing for the gate structure. This is the V4
  analogue of `ceilingAdmits` irreducibility: keep out of the unfold set anything the
  cascade does not need. Which cascade — and whether `cases` on a branch parameter comes
  first — is a **per-conjunct** property, measured, not assumed (spike finding 4:
  `cases v` rescues `bypass_mode_sound` and times out `pending_flow_compat`).

`ksystem` monomorphises the 12-action system at the opaque audit sorts; the concrete-sort
refinement instantiates the polymorphic bundle directly, as V3's `kav_soundP` did.
-/

set_option maxHeartbeats 8000000
set_option auto.native true
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false

namespace Tzimtzum

open Lean Lean.Elab.Tactic in
/-- Run `tac` on every current goal, each under a fresh heartbeat budget. -/
elab "all_goals_fresh " tac:tacticSeq : tactic => do
  let goals ← getGoals
  let mut acc : Array MVarId := #[]
  for g in goals do
    unless (← g.isAssigned) do
      setGoals [g]
      Core.withCurrHeartbeats (evalTactic tac)
      acc := acc ++ (← getGoals).toArray
  setGoals acc.toList

/-- The names every cascade unfolds: the bundle, the conjuncts, the derived gates, and the
`Kav.Action` projections. -/
macro "tzimtzum_simp_core" head:ident : tactic => `(tactic| (
  try simp only [$head:ident, allInv, invS, invP, invPP, invE, invC,
    root_always_active, parent_implies_active, single_parent, no_self_parent,
    root_no_parent, capability_subsumption, root_all_caps, revocation_clean, pending_active,
    pending_unique, pending_registered, root_no_pending, pending_ids_consumed,
    pending_egress_attested, pending_snapshot_coherent, default_deny,
    flow_confinement, flow_confinement_weak,
    integrity_confinement, integrity_confinement_weak, clearance_confinement,
    pending_flow_compat, pending_integ_compat,
    challenge_scoped, challenges_enforce_only, challenge_unique,
    inspected_evidence_consumed, bypass_mode_sound, quarantine_pending,
    grant_bounded, grant_active, grant_pinned,
    St.flow_allows, St.flow_inspects, integ_allows, integ_inspects, clearance_admits,
    contained, vouched,
    Tzimtzum.speculative_taint, Tzimtzum.speculative_taint_contained,
    Tzimtzum.speculative_integ,
    Kav.Action.guard, Kav.Action.next] at *))

/-- Full cascade: gate predicates unfolded. For the conjuncts the gate makes inductive. -/
macro "kav_discharge " head:ident : tactic => `(tactic| (
  (try unfold allInv) <;> (try unfold invS) <;> (try unfold invP) <;> (try unfold invPP) <;>
    (try unfold invE) <;> (try unfold invC) <;>
  (repeat' apply And.intro);
  all_goals_fresh (
    (tzimtzum_simp_core $head) <;>
    (try simp only [beginAllow, beginAdmissible, checkCapability, checkClearance,
        checkFlowStrict, checkFlowAdmissible, checkIntegStrict, checkIntegAdmissible,
        authorizeAdmits, endorsedOK, crossHolds,
        ingestHolds, ingestConfHold, ingestClearHold, ingestIntegHold] at *) <;>
      (first | trivial | grind | (simp_all <;> grind) | auto | duper [*]))))

/-- Lite cascade: gate predicates as atoms. For frame-ish conjuncts. -/
macro "kav_discharge_lite " head:ident : tactic => `(tactic| (
  (try unfold allInv) <;> (try unfold invS) <;> (try unfold invP) <;> (try unfold invPP) <;>
    (try unfold invE) <;> (try unfold invC) <;>
  (repeat' apply And.intro);
  all_goals_fresh (
    (tzimtzum_simp_core $head) <;>
      (first | trivial | grind | (simp_all <;> grind) | auto | duper [*]))))

/-- The TzimtzumV4 transition system at the opaque audit sorts. -/
def ksystem : Kav.TransitionSystem KSt := system

end Tzimtzum
