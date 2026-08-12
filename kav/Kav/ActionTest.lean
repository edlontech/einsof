import Kav.Action
namespace Kav.Test
open Kav

structure St where
  flag : Prop
  counter : Nat

kav_action raise (n : Nat) : St where
  require (¬ s.flag)
  flag := True
  counter := n

-- a frame-condition action: only touches flag, counter must be framed
kav_action setflag : St where
  flag := True

-- a no-require, multi-field action
kav_action reset : St where
  flag := False
  counter := 0

-- raise : Nat → Action St
#check (raise : Nat → Action St)
#check (setflag : Action St)

-- guard correctness: require clauses → conjoined guard
example (s : St) : (raise 5).guard s ↔ ¬ s.flag := Iff.rfl
-- setflag has no `require` → guard is `fun _ => True`
example (s : St) : (setflag).guard s ↔ True := Iff.rfl

-- next correctness incl. the mentioned fields (both fields mentioned → no frame)
example (s s' : St) : (raise 5).next s s' ↔ (s'.flag = True ∧ s'.counter = 5) := Iff.rfl

-- FRAME condition: setflag only mentions `flag`, so `counter` must be auto-framed
example (s s' : St) : (setflag).next s s' ↔ (s'.flag = True ∧ s'.counter = s.counter) := Iff.rfl

-- multi-field, no frame needed
example (s s' : St) : (reset).next s s' ↔ (s'.flag = False ∧ s'.counter = 0) := Iff.rfl

-- auto-generated `next_<field>` projections: changed field and framed field
example (s s' : St) (h : (raise 5).next s s') : s'.counter = 5 := raise.next_counter h
example (s s' : St) (h : (raise 5).next s s') : s'.flag = True := raise.next_flag h
example (s s' : St) (h : (setflag).next s s') : s'.counter = s.counter := setflag.next_counter h

-- labeled requires → `guard_<label>` projections (mixed with an unlabeled clause)
kav_action lower (n : Nat) : St where
  require flag_set : s.flag
  require (n ≥ 1)
  require counter_big : s.counter ≥ n
  counter := s.counter - n

example (s : St) (h : (lower 3).guard s) : s.flag := lower.guard_flag_set h
example (s : St) (h : (lower 3).guard s) : s.counter ≥ 3 := lower.guard_counter_big h

-- single labeled require (no `And` to project through)
kav_action toggle : St where
  require was_set : s.flag
  flag := False

example (s : St) (h : (toggle).guard s) : s.flag := toggle.guard_was_set h

-- parameterized state type: head extraction + auto-framing over `St α β`
section
variable {α β : Type}

structure PSt (α β : Type) where
  flag : Prop
  rel  : α → β → Prop

kav_action pset (x : α) (y : β) : PSt α β where
  require True
  rel := fun A B => s.rel A B ∨ (A = x ∧ B = y)

-- frame: flag preserved; rel updated. (α β are section variables.)
example {α β : Type} (x : α) (y : β) (s s' : PSt α β) :
    (pset x y).next s s' ↔ (s'.flag = s.flag ∧ s'.rel = fun A B => s.rel A B ∨ (A = x ∧ B = y)) := by
  rfl

-- generated projections instantiate the section-variable sorts implicitly
example {α β : Type} (x : α) (y : β) (s s' : PSt α β) (h : (pset x y).next s s') :
    s'.flag = s.flag := pset.next_flag h

end

end Kav.Test
