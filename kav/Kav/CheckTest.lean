import Kav.Check
namespace Kav.Test
open Kav

abbrev Toy : Type := Bool
def flip : Action Toy := { guard := fun _ => True, next := fun s s' => s' = !s }
def sys : TransitionSystem Toy := { init := fun s => s = false, actions := [("flip", flip)] }
-- "always_false" is NOT inductive for flip (flip false = true), but IS an init invariant.
def invs : List (Invariant Toy) := [("always_false", fun s => s = false)]

#kav_check_invariants sys invs

-- Dump mode: pretty-print each VC goal type (no discharge).
#kav_check_invariants? sys invs

-- Skeleton mode: emit a `theorem … := by auto` per VC for manual fallback.
#kav_check_invariants! sys invs
end Kav.Test
