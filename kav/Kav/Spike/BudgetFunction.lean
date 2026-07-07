import Kav.Action
import Kav.CheckInit

/-! # Spike: function-field budget under `#kav_check_action`

Task 1 of the TzimtzumV3 campaign (design §4 "Budget encoding" / §5.8 step 0). Question:
does the Kav discharge cascade (`#kav_check_action`, `#kav_check_init`) tolerate a mutable
**function-valued** state field (`budget : Agent → Nat`, `Agent` an uninterpreted/opaque
sort) updated by classical-`ite` point-updates, in place of the status-quo relational
`AgentId → Nat → Prop` encoding (forced-functional only via extra invariants)?

**Verdict: GO.**

`kav_action` parses the function-field update clause without any macro changes, and
`Decidable (x = a)` on the opaque `Agent` sort resolves via the scoped
`Classical.propDecidable` instance brought into scope by `open Classical` — exactly the
escape hatch anticipated in the design doc. The naive inline form (`budget := fun x => if
x = a then … else s.budget x`) does NOT survive the automatic cascade, however: the
transitive-unfold collector (`collectUnfoldNamesTransitive`) has no denylist entry for
`ite`, so it unfolds the point-update's `if`-`then`-`else` down to a raw `Decidable.rec`
over a `Classical.choice` witness — this destroys the syntactic shape every closing tactic
(`grind`, `simp_all`, `auto`, `duper`) pattern-matches on to case-split an `ite`, so every
VC FAILs regardless of invariant shape (confirmed: 0/2 on both actions with the inline
form). This is the exact same failure class the spec already works around for
`ceilingAdmits`/`budget_saturating_credit` (design precedent: mark the update helper
`irreducible` so the cascade treats it as an opaque atom instead of unfolding into it).
Applying that fix here — wrapping the point-update in a top-level `noncomputable`
`pointUpdate` helper marked `@[irreducible]` — keeps `ite` out of the transitive-unfold
walk entirely. The automatic cascade still can't discharge the four (action × invariant)
VCs this way (it has no reason to unfold an opaque helper), so all four are proved
manually below with one extra step (`unfold pointUpdate` at the point of use) beyond what
the existing manual VCs in `CheckGrantOverride.lean`/`CheckInvokeComplete.lean` already
need for the relational encoding. `#print axioms` on each manual proof shows only the
three permitted kernel axioms. Net: the encoding is expressible and provable, at the same
manual-proof cost the relational encoding already pays elsewhere — no macro limitation,
no new axiom, no irreducible-helper workaround beyond the existing precedent. Task 3
proceeds with the function encoding.
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

-- Classical point-update on the function field. `noncomputable` (the `Decidable` instance
-- is `Classical.propDecidable`) and `irreducible` for the same reason as
-- `budget_saturating_credit`/`ceilingAdmits`: unfolding the `ite` re-exposes a
-- `Decidable.rec`/`Classical.choice` term that defeats every closing tactic's built-in
-- if-then-else case-split heuristics.
noncomputable def pointUpdate (f : Agent → Nat) (a : Agent) (v : Nat) : Agent → Nat :=
  fun x => if x = a then v else f x

attribute [irreducible] pointUpdate

-- Debit action mirroring `invoke_complete`'s endorsed debit: an affordability require plus
-- an active require, classical point-update subtracting the weight.
kav_action debit (a : Agent) (w : Nat) : St where
  require s.active a
  require w ≤ s.budget a
  budget := pointUpdate s.budget a (s.budget a - w)

-- Credit action mirroring `sentinel_credit_budget`: saturating add, same point-update shape.
kav_action credit (a : Agent) (n : Nat) : St where
  require s.active a
  budget := pointUpdate s.budget a (min capacity (s.budget a + n))

def budget_bounded (s : St) : Prop := ∀ x, s.budget x ≤ capacity

-- Second invariant, mixing the function field with a Prop-valued relation, to stress the
-- cascade with both shapes at once.
def active_budget_bounded (s : St) : Prop := ∀ x, s.active x → s.budget x ≤ capacity

def invs : List (Kav.Invariant St) :=
  [ ("budget_bounded", budget_bounded)
  , ("active_budget_bounded", active_budget_bounded) ]

-- Automatic cascade: 0/2 on both actions (documented failure mode above). Kept as a
-- recorded data point rather than deleted, per the spike's job of characterizing the
-- discharge cascade's behavior, not just its final verdict.
#kav_check_action debit invs
#kav_check_action credit invs
#kav_check_init initial invs

-- Manual proofs of the four resistant VCs. Each needs exactly one step beyond the
-- automatic unfold set: `unfold pointUpdate` at the point of use, then a case split on
-- `x = a` (Nat's truncated subtraction and `min`'s left bound do the rest).

theorem debit_pres_budget_bounded
    (a : Agent) (w : Nat) (s s' : St)
    (hbb : budget_bounded s)
    (_hg : (debit a w).guard s) (hn : (debit a w).next s s') :
    budget_bounded s' := by
  unfold budget_bounded debit Kav.Action.guard Kav.Action.next at *
  obtain ⟨-, hbudget⟩ := hn
  intro x
  rw [hbudget]; unfold pointUpdate
  by_cases hx : x = a
  · simp [hx]; have := hbb a; omega
  · simp [hx]; exact hbb x

theorem debit_pres_active_budget_bounded
    (a : Agent) (w : Nat) (s s' : St)
    (hab : active_budget_bounded s)
    (hg : (debit a w).guard s) (hn : (debit a w).next s s') :
    active_budget_bounded s' := by
  unfold active_budget_bounded debit Kav.Action.guard Kav.Action.next at *
  obtain ⟨hactive, hbudget⟩ := hn
  intro x hx'
  rw [hbudget]; unfold pointUpdate
  rw [hactive] at hx'
  by_cases hx : x = a
  · simp [hx]; have := hab a hg.1; omega
  · simp [hx]; exact hab x hx'

theorem credit_pres_budget_bounded
    (a : Agent) (n : Nat) (s s' : St)
    (hbb : budget_bounded s)
    (_hg : (credit a n).guard s) (hn : (credit a n).next s s') :
    budget_bounded s' := by
  unfold budget_bounded credit Kav.Action.guard Kav.Action.next at *
  obtain ⟨-, hbudget⟩ := hn
  intro x
  rw [hbudget]; unfold pointUpdate
  by_cases hx : x = a
  · simp [hx, Nat.min_le_left]
  · simp [hx]; exact hbb x

theorem credit_pres_active_budget_bounded
    (a : Agent) (n : Nat) (s s' : St)
    (hab : active_budget_bounded s)
    (_hg : (credit a n).guard s) (hn : (credit a n).next s s') :
    active_budget_bounded s' := by
  unfold active_budget_bounded credit Kav.Action.guard Kav.Action.next at *
  obtain ⟨hactive, hbudget⟩ := hn
  intro x hx'
  rw [hbudget]; unfold pointUpdate
  rw [hactive] at hx'
  by_cases hx : x = a
  · simp [hx, Nat.min_le_left]
  · simp [hx]; exact hab x hx'

-- Axiom audit: must depend only on [propext, Classical.choice, Quot.sound]. `pp.fullNames`
-- spells out `Classical.choice` rather than the `open Classical`-shortened `choice`.
set_option pp.fullNames true in
#print axioms debit_pres_budget_bounded
set_option pp.fullNames true in
#print axioms debit_pres_active_budget_bounded
set_option pp.fullNames true in
#print axioms credit_pres_budget_bounded
set_option pp.fullNames true in
#print axioms credit_pres_active_budget_bounded

end Kav.Spike.BudgetFunction
