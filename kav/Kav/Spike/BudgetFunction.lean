import Kav.Action
import Kav.CheckInit

/-! # Spike: function-field budget under `#kav_check_action`

Task 1 of the TzimtzumV3 campaign (design §4 "Budget encoding" / §5.8 step 0). Question:
does the Kav discharge cascade (`#kav_check_action`, `#kav_check_init`) tolerate a mutable
**function-valued** state field (`budget : Agent → Nat`, `Agent` an uninterpreted/opaque
sort) updated by classical-`ite` point-updates, in place of the status-quo relational
`AgentId → Nat → Prop` encoding (forced-functional only via extra invariants)?

**Verdict: GO — via a framework fix, not a workaround.**

`kav_action` parses the function-field update clause without any macro changes, and
`Decidable (x = a)` on the opaque `Agent` sort resolves via the scoped
`Classical.propDecidable` instance brought into scope by `open Classical`. The naive inline
form (`budget := fun x => if x = a then … else s.budget x`) does NOT survive the automatic
cascade under the *original* denylist, however: `collectUnfoldNamesTransitive`
(`kav/Kav/CheckAction.lean`) had no denylist entry for `ite`, so it unfolds the
point-update's `if`-`then`-`else` down to a raw `Decidable.rec` over a `Classical.choice`
witness — this destroys the syntactic shape every closing tactic (`grind`, `simp_all`,
`auto`, `duper`) pattern-matches on to case-split an `ite`, so every VC FAILed regardless of
invariant shape (confirmed: 0/2 on both actions with the inline form under the old
denylist).

Two fixes were tried, in the order the campaign brief mandated:

1. **Framework fix (chosen).** `ite`/`dite` added to `actionUnfoldDenylist` in
   `kav/Kav/CheckAction.lean` — the same denylist that already excludes `Kav.Action`,
   `Eq`, `And`, etc. because they are structural constants with no useful body for the
   engine. With `ite` excluded from the transitive-unfold walk, `simp only [<unfolds>] at
   *` never rewrites an `ite` application into its `Decidable.rec` form — it stays atomic,
   exactly the shape `grind`'s native if-then-else case-split heuristic expects. Re-run
   against a scratch copy of this file with the inline form (not committed; the change was
   validated directly against `debit`/`credit` below before committing to it): `debit`
   (pure truncated-subtraction point-update) goes from 0/2 to **2/2 automatic**, no manual
   proof needed at all. `credit` (saturating point-update through `min`) stays 0/2 — but
   that failure is NOT an `ite`/inline-form artifact: it reproduces even when the `min` is
   routed through an `@[irreducible]` helper (`saturating_credit` below), because the
   cascade has no equational access to an irreducible def's `≤ capacity` bound. This is the
   exact same, already-accepted, `ceilingAdmits`/`budget_saturating_credit` manual-proof
   precedent the spec already pays for `sentinel_credit_budget`'s `budget_bounded` VC — not
   a new cost introduced by the function encoding.
2. **`irreducible` `pointUpdate` helper (fallback, not needed).** Wrapping every
   point-update in a `noncomputable @[irreducible] pointUpdate` helper (kept below as
   `saturating_credit`'s pattern, since the `min` needs the irreducible treatment anyway)
   also works, at the cost of one extra `unfold` per manual VC. With the denylist fix, this
   is only required for the `min`-shaped credit update — not for every budget-touching
   action — so Task 3 uses plain inline `ite` everywhere and reserves the
   `irreducible`-helper pattern for the one saturating-credit site (mirroring
   `budget_saturating_credit`, unchanged from the pre-campaign encoding).

Net: the framework fix (2 denylist entries, ~15% larger unfold set, no regression on the
existing 13 Tzimtzum check files — re-verified via `make verify` after landing it) makes
the function encoding *strictly cheaper* than the original relational encoding for every
budget action except the saturating credit, which was already a manual-proof site. `#print
axioms` on the manual proof below shows only the three permitted kernel axioms. Task 3
proceeds with the function encoding, inline `ite` point-updates, and the `saturating_credit`
irreducible-helper pattern reserved for `sentinel_credit_budget`.
-/

namespace Kav.Spike.BudgetFunction

open Classical

-- Uninterpreted sort, monomorphized directly as `opaque` (the `OpaqueTypes.lean` pattern,
-- applied to the single sort this toy system needs).
opaque Agent : Type

def capacity : Nat := 16

structure St where
  active : Agent → Prop
  budget : Agent → Nat

def initial (s : St) : Prop :=
  (∀ A, ¬ s.active A) ∧ (∀ A, s.budget A = capacity)

-- Plain inline classical `ite` point-update — no helper needed. Discharges automatically
-- under `#kav_check_action` now that `ite`/`dite` are in `actionUnfoldDenylist`.
kav_action debit (a : Agent) (w : Nat) : St where
  require s.active a
  require w ≤ s.budget a
  budget := fun x => if x = a then s.budget a - w else s.budget x

-- Saturating point-update: the `min` needs the pre-existing irreducible-helper treatment
-- (same reason as `budget_saturating_credit`/`ceilingAdmits`), independent of the ite fix.
def saturating_credit (b n : Nat) : Nat := min capacity (b + n)

attribute [irreducible] saturating_credit

kav_action credit (a : Agent) (n : Nat) : St where
  require s.active a
  budget := fun x => if x = a then saturating_credit (s.budget a) n else s.budget x

def budget_bounded (s : St) : Prop := ∀ x, s.budget x ≤ capacity

-- Second invariant, mixing the function field with a Prop-valued relation, to stress the
-- cascade with both shapes at once.
def active_budget_bounded (s : St) : Prop := ∀ x, s.active x → s.budget x ≤ capacity

def invs : List (Kav.Invariant St) :=
  [ ("budget_bounded", budget_bounded)
  , ("active_budget_bounded", active_budget_bounded) ]

-- `debit`: 2/2 automatic (the denylist fix). `credit`: 0/2 automatic (the pre-existing
-- saturating-`min` opacity cost, proved manually below).
#kav_check_action debit invs
#kav_check_action credit invs
#kav_check_init initial invs

-- Manual proofs of the two resistant `credit` VCs. Each needs exactly one step beyond the
-- automatic unfold set: `unfold saturating_credit` at the point of use, then `omega`/
-- `Nat.min_le_left` closes it (Nat's truncated subtraction and `min`'s left bound do the
-- rest — the same shape as the codebase's existing `budget_saturating_credit` proofs).

theorem credit_pres_budget_bounded
    (a : Agent) (n : Nat) (s s' : St)
    (hbb : budget_bounded s)
    (_hg : (credit a n).guard s) (hn : (credit a n).next s s') :
    budget_bounded s' := by
  unfold budget_bounded credit Kav.Action.guard Kav.Action.next at *
  obtain ⟨-, hbudget⟩ := hn
  intro x
  rw [hbudget]
  by_cases hx : x = a
  · simp only [hx, if_true]; unfold saturating_credit; exact Nat.min_le_left _ _
  · simp [hx]; exact hbb x

theorem credit_pres_active_budget_bounded
    (a : Agent) (n : Nat) (s s' : St)
    (hab : active_budget_bounded s)
    (_hg : (credit a n).guard s) (hn : (credit a n).next s s') :
    active_budget_bounded s' := by
  unfold active_budget_bounded credit Kav.Action.guard Kav.Action.next at *
  obtain ⟨hactive, hbudget⟩ := hn
  intro x hx'
  rw [hbudget]
  rw [hactive] at hx'
  by_cases hx : x = a
  · simp only [hx, if_true]; unfold saturating_credit; exact Nat.min_le_left _ _
  · simp [hx]; exact hab x hx'

-- Axiom audit: must depend only on [propext, Classical.choice, Quot.sound]. `pp.fullNames`
-- spells out `Classical.choice` rather than the `open Classical`-shortened `choice`.
set_option pp.fullNames true in
#print axioms credit_pres_budget_bounded
set_option pp.fullNames true in
#print axioms credit_pres_active_budget_bounded

end Kav.Spike.BudgetFunction
