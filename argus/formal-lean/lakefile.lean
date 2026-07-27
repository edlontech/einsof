import Lake
open Lake DSL

-- The Kav/Tzimtzum spec (Lean 4.32.1 stable); transitively brings Kav + mathlib.
require tzimtzum from "../../tzimtzum"

-- The Aeneas Lean library, compatibility-checked against this project's toolchain.
require aeneas from "../../tools/aeneas/backends/lean"

-- Lean REPL (latest compatible stable tag) for fast lean-lsp-mcp multi-attempt.
require repl from git "https://github.com/leanprover-community/repl" @ "v4.32.0"

package «argus-formal-lean» where

@[default_target]
lean_lib «ArgusLean» where

-- Opt-in property-test harness (Plausible). NOT in the default build; run with:
--   lake build ArgusChecks
lean_lib «ArgusChecks» where
  roots := #[`ArgusLean.Refinement.PlausibleChecks]
