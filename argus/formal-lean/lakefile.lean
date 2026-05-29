import Lake
open Lake DSL

-- The Kav/Tzimtzum spec (Lean 4.30.0 stable); transitively brings kav + mathlib 4.30.
require tzimtzum from "../../tzimtzum"

-- The realigned Aeneas Lean library (also on mathlib 4.30.0 stable).
require aeneas from "../../tools/aeneas/backends/lean"

package «argus-formal-lean» where

@[default_target]
lean_lib «ArgusLean» where
