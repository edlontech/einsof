import Kav.Engine

/-- `kav_solve`: the Kav discharge tactic. Introduces hypotheses, tries
    `simp_all`, then hands the goal to the kernel-checked auto+Duper engine.
    Use for VC goals (e.g. invariant-preservation theorems). -/
macro "kav_solve" : tactic =>
  `(tactic| (intros <;> first
    | assumption
    | rfl
    | (try simp_all) <;> auto))

/-- `kav_solve [hints]`: variant that unfolds `hints` before the standard
    discharge sequence. Useful for VC goals that need definitional unfolding
    (e.g. action/invariant bodies in hand-written theorem stubs). -/
syntax "kav_solve" "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic
macro_rules
  | `(tactic| kav_solve [$hints,*]) =>
    `(tactic| ((try simp only [$hints,*]) <;> intros <;> first
      | assumption
      | rfl
      | (try simp_all) <;> auto))
