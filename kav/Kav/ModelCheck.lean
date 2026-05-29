namespace Kav

/-- A finite, computable view of a transition system for explicit-state model
    checking. `states` is the (finite) list of states to explore; `actions` are
    Bool-valued `(label, guardB, nextB)` triples; `inv` is the Bool-valued
    invariant bundle. Everything is Bool-valued so the whole search is
    `decide`/`native_decide`-able — no solver, no mathlib.

    This is the computable mirror the caller supplies; relating it to a
    Prop-valued spec (e.g. `Kav.TransitionSystem`/`Kav.Invariant`) is a separate
    concern handled by the caller, not derived here. -/
structure FiniteModel (σ : Type) where
  /-- The finite set of states to explore. -/
  states  : List σ
  /-- Labeled actions: `(label, guardB, nextB)`. `nextB s s'` is the Bool-valued
      successor relation; the checker quantifies `s'` over `states`. -/
  actions : List (String × (σ → Bool) × (σ → σ → Bool))
  /-- The Bool-valued invariant bundle. -/
  inv     : σ → Bool

namespace FiniteModel

/-- One-step CTI search. Find the first state `s ∈ states` with `inv s`, a guarded
    action `(lbl, g, step)` (`g s = true`), and a successor `s' ∈ states` with
    `step s s'` but `¬ inv s'`. Returns the witness `(s, lbl, s')`, else `none`. -/
def findCTI {σ : Type} (m : FiniteModel σ) : Option (σ × String × σ) :=
  (m.states.filter m.inv).findSome? fun s =>
    m.actions.findSome? fun (lbl, g, step) =>
      if g s then
        (m.states.find? (fun s' => step s s' && ! m.inv s')).map (fun s' => (s, lbl, s'))
      else none

/-- The model-check assertion: every reachable-in-one-step successor (over
    `states`) of an invariant-satisfying, guarded state preserves the invariant.
    Equivalent to `findCTI.isNone` — see `noCTI_eq_findCTI_isNone`. -/
def noCTI {σ : Type} (m : FiniteModel σ) : Bool :=
  (m.states.filter m.inv).all fun s =>
    m.actions.all fun (_lbl, g, step) =>
      ! g s ||
        m.states.all fun s' => ! (step s s' && ! m.inv s')

/-- `xs.all (! p ·)` holds iff `xs.find? p` finds nothing. Bridges the `all`
    form (used by `noCTI`) and the `find?` form (used by `findCTI`). -/
private theorem all_not_eq_find?_isNone {σ : Type} (p : σ → Bool) (xs : List σ) :
    (xs.all fun x => ! p x) = (xs.find? p).isNone := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.all_cons, List.find?_cons]
    cases h : p x with
    | true => simp
    | false => simpa using ih

/-- `noCTI` and `findCTI` are consistent: there is no CTI iff the search finds
    no witness. Keeps the `native_decide` assertion (`noCTI`) and the reporting
    function (`findCTI`) in lockstep. -/
theorem noCTI_eq_findCTI_isNone {σ : Type} (m : FiniteModel σ) :
    m.noCTI = m.findCTI.isNone := by
  simp only [noCTI, findCTI]
  induction m.states.filter m.inv with
  | nil => simp
  | cons s rest ih =>
    simp only [List.all_cons, List.findSome?_cons]
    have hact :
        (m.actions.all fun x =>
          ! x.2.1 s || m.states.all fun s' => ! (x.2.2 s s' && ! m.inv s'))
          = (m.actions.findSome? fun x =>
              if x.2.1 s then
                (m.states.find? fun s' => x.2.2 s s' && ! m.inv s').map
                  (fun s' => (s, x.1, s'))
              else none).isNone := by
      induction m.actions with
      | nil => simp
      | cons a as iha =>
        rw [List.all_cons, List.findSome?_cons]
        by_cases hg : a.2.1 s
        · rw [hg, if_pos rfl]
          rw [all_not_eq_find?_isNone (fun s' => a.2.2 s s' && ! m.inv s') m.states]
          simp only [Bool.not_true, Bool.false_or]
          cases m.states.find? (fun s' => a.2.2 s s' && ! m.inv s') with
          | none => rw [Option.map_none]; simpa using iha
          | some w => rw [Option.map_some]; simp
        · have hgf : a.2.1 s = false := by simp [hg]
          rw [hgf, if_neg (by simp), Bool.not_false, Bool.true_or]
          simpa using iha
    rw [hact, ih]
    cases (m.actions.findSome? fun x =>
        if x.2.1 s then
          (m.states.find? fun s' => x.2.2 s s' && ! m.inv s').map (fun s' => (s, x.1, s'))
        else none) <;> simp

end FiniteModel

end Kav
