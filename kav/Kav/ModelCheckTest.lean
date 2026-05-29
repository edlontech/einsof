import Kav.ModelCheck
import Kav.ModelCheckCmd

namespace Kav.Test
open Kav

/-- Toy model: a `Bool` state with one action `flip` that negates the state
    (relation `nextB s s' := s' == !s`). The invariant `always_false` asserts
    the state is `false` — this is NOT inductive: from `false` (inv holds),
    `flip` reaches `true` (inv fails). -/
def toyModel : FiniteModel Bool :=
  { states  := [false, true]
    actions := [("flip", (fun _ => true), (fun s s' => s' == (! s)))]
    inv     := fun s => s == false }

-- The model checker MUST find a CTI: from `false`, flip → `true` violates the invariant.
example : toyModel.noCTI = false := by native_decide

#eval toyModel.findCTI   -- expect: some (false, "flip", true)

/-- Positive control: an inductive invariant (`always_true`) over the same
    transition system. Every successor satisfies it, so there is no CTI. -/
def toyModelGood : FiniteModel Bool :=
  { states  := [false, true]
    actions := [("flip", (fun _ => true), (fun s s' => s' == (! s)))]
    inv     := fun _ => true }

example : toyModelGood.noCTI = true := by native_decide

#eval toyModelGood.findCTI   -- expect: none

-- The `#kav_model_check` command: read-out verdict for any `FiniteModel σ`.
#kav_model_check toyModel        -- expect: CTI FOUND among 2 states
#kav_model_check toyModelGood    -- expect: no CTI among 2 states

end Kav.Test
