import Auto.Tactic
import Duper.Tactic

/-! # Kav verification engine

Shared setup that makes `by auto` / `by duper` available **kernel-checked** to any
module that imports `Kav.Engine`. This is the rebind incantation proven to work by the
`Kav.Spike.InvokeStart` spike: it rebinds Auto's native solver to run Duper, so the
proofs Auto produces are full Lean proof terms checked by the kernel (no external
oracle / `sorry`). -/

open Lean Auto in
def Auto.duperRaw (lemmas : Array Lemma) (inhs : Array Lemma) : MetaM Expr := do
  let lemmas : Array (Expr × Expr × Array Name × Bool) ← lemmas.mapM
    (fun ⟨⟨proof, ty, _⟩, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], true))
  Duper.runDuper lemmas.toList [] 0

attribute [rebind Auto.Native.solverFunc] Auto.duperRaw
set_option auto.native true
