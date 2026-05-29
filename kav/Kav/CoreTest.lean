import Kav.Core
namespace Kav.Test
open Kav

-- A trivial 1-action system over a 1-field state; must elaborate.
abbrev Toy : Type := Bool
def flip : Action Toy := { guard := fun _ => True, next := fun s s' => s' = !s }
def sys : TransitionSystem Toy := { init := fun s => s = false, actions := [("flip", flip)] }
example : sys.actions.length = 1 := rfl

end Kav.Test
