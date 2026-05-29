namespace Kav

/-- A labeled transition: a guard (precondition) and a post-relation. Action
    parameters, if any, are existentially closed inside `next` by the caller. -/
structure Action (σ : Type) where
  guard : σ → Prop
  next  : σ → σ → Prop

/-- A transition system: an initial-state predicate and labeled actions. -/
structure TransitionSystem (σ : Type) where
  init    : σ → Prop
  actions : List (String × Action σ)

/-- An invariant is a named state predicate. -/
abbrev Invariant (σ : Type) := String × (σ → Prop)

/-- The preservation VC for one (action, invariant) pair: from any state
    satisfying the full invariant bundle `allInv` and the action's guard, every
    successor state satisfies the target invariant. -/
def preservesVC {σ : Type} (allInv : σ → Prop) (act : Action σ) (inv : σ → Prop) : Prop :=
  ∀ s s', allInv s → act.guard s → act.next s s' → inv s'

/-- The initiation VC for one invariant: every initial state satisfies it. -/
def initVC {σ : Type} (ts : TransitionSystem σ) (inv : σ → Prop) : Prop :=
  ∀ s, ts.init s → inv s

end Kav
