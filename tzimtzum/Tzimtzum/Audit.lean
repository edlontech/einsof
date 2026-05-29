import Tzimtzum.CheckReturnEndorsed

/-! # TzimtzumV2 — Crown-jewel axiom audit

Named, kernel-checked theorems for headline safeties under the protocol's most
substantive action (`invoke_start`) and for the initial state.  The purpose is to
materialise a small set of explicit preservation obligations — with names and
`#print axioms` — and to confirm that the whole proof depends ONLY on the three
standard Lean kernel axioms (`propext`, `Classical.choice`, `Quot.sound`) with NO
solver or `native_decide` axiom in the trust base.

Each theorem uses the same discharge cascade that `#kav_check_action` employs:
  `intros <;> simp only [<transitive unfolds>] at * <;>
    (first | trivial | grind | (simp_all <;> grind) | auto | duper [*])`

The `opaque` sorts and `abbrev KSt` are defined once in `OpaqueTypes` and shared
by all Check modules (imported transitively via `CheckReturnEndorsed`).  The two
manual `active_has_budget` theorems audit their axioms in-place in
`CheckReturnEndorsed` and `CheckInvokeComplete`; Theorem 5 below re-audits the
ReturnEndorsed one here for visibility.
-/

set_option maxHeartbeats 4000000

namespace Tzimtzum

/-!
## Theorem 1 — `flow_confinement` is preserved by `invoke_start`

The substantive 3-check gate (capability + flow + authorizer) must guarantee that
any newly in-flight invocation does not break flow confinement.
The proof reduces to the `CHECK 2a/2b/2c` preconditions together with the
`override_used` update and the existing `flow_confinement` hypothesis.
-/

theorem audit_flow_confinement
    (a : KAgent) (tool : KTool) (inv : KInv) (s s' : KSt)
    (hinv : flow_confinement s)
    (hg : (invoke_start a tool inv).guard s)
    (hn : (invoke_start a tool inv).next s s') :
    flow_confinement s' := by
  simp only [flow_confinement, invoke_start, speculative_taint] at *
  intros A L I E hpre
  simp_all
  grind

#print axioms audit_flow_confinement

/-!
## Theorem 2 — `taint_integrity` is preserved by `invoke_start`

Taint must always be justified by a completed non-endorsed invocation or an
unendorsed return from a child.  `invoke_start` adds `inv` to `in_flight` but does
not modify `taint_levels`, `gh_taint_invoked`, or `gh_taint_received`, so
`taint_integrity` is preserved by the frame rule.
-/

theorem audit_taint_integrity
    (a : KAgent) (tool : KTool) (inv : KInv) (s s' : KSt)
    (hinv : taint_integrity s)
    (_hg : (invoke_start a tool inv).guard s)
    (hn : (invoke_start a tool inv).next s s') :
    taint_integrity s' := by
  simp only [taint_integrity, invoke_start] at *
  intros A L hpre
  simp_all

#print axioms audit_taint_integrity

/-!
## Theorem 3 — `override_consumed_when_sole_justification` is preserved by `invoke_start`

If a tainted in-flight egress relies solely on a `flow_override`, the override must
already be consumed.  The `invoke_start` action may add new in-flight invocations AND
marks overrides as consumed on the 2a/2b/2c paths; this theorem confirms the
invariant carries through.
-/

theorem audit_override_consumed
    (a : KAgent) (tool : KTool) (inv : KInv) (s s' : KSt)
    (hinv : override_consumed_when_sole_justification s)
    (hg : (invoke_start a tool inv).guard s)
    (hn : (invoke_start a tool inv).next s s') :
    override_consumed_when_sole_justification s' := by
  simp only [override_consumed_when_sole_justification, invoke_start, speculative_taint] at *
  intros A L I E hpre
  simp_all
  grind

#print axioms audit_override_consumed

/-!
## Theorem 4 — `flow_confinement` holds in every initial state

The initial state has no in-flight invocations and no taint, so the body of
`flow_confinement` is vacuously true (the antecedent `s.in_flight A I` is always
false initially).
-/

theorem audit_init_flow_confinement
    (s : KSt) (hinit : initial s) :
    flow_confinement s := by
  simp only [flow_confinement, initial] at *
  intros A L I E hpre
  grind

#print axioms audit_init_flow_confinement

/-!
## Theorem 5 — manual `active_has_budget` theorem axiom audit

`return_endorsed_pres_active_has_budget` (defined in `CheckReturnEndorsed`) and
`invoke_complete_pres_active_has_budget` (defined in `CheckInvokeComplete`) are the
two manual proofs for the budget-debit-resistant VC.  Their `#print axioms` appear
in-place in those modules; this file re-audits the ReturnEndorsed one to confirm
the bound in a single build.
-/

#print axioms return_endorsed_pres_active_has_budget

end Tzimtzum
