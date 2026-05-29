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

end

end Kav.Test
