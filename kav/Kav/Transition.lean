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

def close4 {σ α β γ δ : Type} (f : α → β → γ → δ → Action σ) : Action σ :=
  { guard := fun s => ∃ a b c d, (f a b c d).guard s
    next  := fun s s' => ∃ a b c d, (f a b c d).guard s ∧ (f a b c d).next s s' }

def close5 {σ α β γ δ ε : Type} (f : α → β → γ → δ → ε → Action σ) : Action σ :=
  { guard := fun s => ∃ a b c d e, (f a b c d e).guard s
    next  := fun s s' => ∃ a b c d e, (f a b c d e).guard s ∧ (f a b c d e).next s s' }

def close7 {σ α β γ δ ε ζ η : Type} (f : α → β → γ → δ → ε → ζ → η → Action σ) : Action σ :=
  { guard := fun s => ∃ a b c d e f' g, (f a b c d e f' g).guard s
    next  := fun s s' => ∃ a b c d e f' g, (f a b c d e f' g).guard s ∧ (f a b c d e f' g).next s s' }

def close8 {σ α β γ δ ε ζ η θ : Type} (f : α → β → γ → δ → ε → ζ → η → θ → Action σ) : Action σ :=
  { guard := fun s => ∃ a b c d e f' g h, (f a b c d e f' g h).guard s
    next  := fun s s' => ∃ a b c d e f' g h, (f a b c d e f' g h).guard s ∧ (f a b c d e f' g h).next s s' }

end Kav
