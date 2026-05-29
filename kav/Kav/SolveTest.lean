import Kav.Solve
namespace Kav.Test

-- trivial goals kav_solve should close
example (p q : Prop) (h : p ∧ q) : q := by kav_solve
example (p : Prop) (h : p) : p ∨ False := by kav_solve
example : ∀ (n : Nat), n = n := by kav_solve

end Kav.Test
