import Kav.Core

/-! # Existential-closure helpers for parameterized actions

`kav_action`s are curried functions (e.g. `invoke_start : AgentId → ToolId → InvocationId →
Action σ`), but `TransitionSystem.actions` needs a bare `Action σ`. These helpers
existentially close the action parameters so a parameterized action can be installed as a
single labeled transition. -/

namespace Kav

def close1 {σ α : Type} (f : α → Action σ) : Action σ :=
  { guard := fun s => ∃ a, (f a).guard s
    next  := fun s s' => ∃ a, (f a).guard s ∧ (f a).next s s' }

def close2 {σ α β : Type} (f : α → β → Action σ) : Action σ :=
  { guard := fun s => ∃ a b, (f a b).guard s
    next  := fun s s' => ∃ a b, (f a b).guard s ∧ (f a b).next s s' }

def close3 {σ α β γ : Type} (f : α → β → γ → Action σ) : Action σ :=
  { guard := fun s => ∃ a b c, (f a b c).guard s
    next  := fun s s' => ∃ a b c, (f a b c).guard s ∧ (f a b c).next s s' }

end Kav
