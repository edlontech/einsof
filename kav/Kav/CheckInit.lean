import Kav.Core
import Kav.Engine
import Kav.Check
import Kav.CheckAction
import Lean

/-! # `#kav_check_init` command

A **per-invariant** initiation checker. For an initial-state predicate `init : σ → Prop`
and each invariant `inv : σ → Prop` in the list, it builds and discharges

```
∀ (s : σ), init s → inv s
```

```
#kav_check_init <initTerm> <invListTerm>
```

The two arguments must elaborate over the **same** state type `σ`. Reuses
`CheckAction`'s transitive-unfold collection + discharge cascade. Prints a
PASS/FAIL table.
-/

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

namespace Kav.Check

/-- Build the initiation goal `∀ (s : σ), init s → inv s`. -/
def mkInitVCExpr (initExpr σ invExpr : Expr) : MetaM Expr := do
  withLocalDeclD `s σ fun s => do
    let hInit := mkApp initExpr s
    let concl := mkApp invExpr s
    let body ← mkArrow hInit concl
    mkForallFVars #[s] body

/-- A single generated init VC for one invariant. -/
structure InitVC where
  label  : String
  goalTy : Expr

/-- Elaborate the `init` predicate + invariant list (sharing `σ`, read off `init`'s type),
    and build one initiation VC per invariant. -/
def buildInitVCs (initStx invsStx : Syntax) : TermElabM (Expr × Array InitVC) := do
  let initExpr ← elabTerm initStx none
  synthesizeSyntheticMVarsNoPostponing
  let initExpr ← instantiateMVars initExpr
  let initTy ← whnf (← inferType initExpr)
  let σ ← match initTy.getAppFnArgs with
    | (``Eq, _) => throwError "kav: init term must have type `σ → Prop`"
    | _ =>
      forallTelescopeReducing initTy fun params _ => do
        match params with
        | #[p] => inferType p
        | _ => throwError "kav: init term must have type `σ → Prop`, got {initTy}"
  let invsExpr ← elabTerm invsStx none
  synthesizeSyntheticMVarsNoPostponing
  let invsExpr ← instantiateMVars invsExpr
  let invs ← walkLabeledList invsExpr
  let mut vcs : Array InitVC := #[]
  for inv in invs do
    let goalTy ← mkInitVCExpr initExpr σ inv.expr
    vcs := vcs.push { label := inv.label, goalTy := goalTy }
  return (σ, vcs)

end Kav.Check

namespace Kav

open Lean.Elab.Command Kav.Check

/-- Discharge mode: per-invariant initiation PASS/FAIL table. -/
syntax (name := kavCheckInit)
  "#kav_check_init" term:max term:max : command

@[command_elab kavCheckInit]
def elabKavCheckInit : CommandElab := fun stx =>
  liftTermElabM do
    let (_σ, vcs) ← buildInitVCs stx[1] stx[2]
    let mut lines : Array String := #[]
    let mut passes := 0
    let mut total := 0
    for vc in vcs do
      total := total + 1
      let ok ← tryDischargeAction vc.goalTy
      if ok then passes := passes + 1
      let status := if ok then "PASS" else "FAIL"
      lines := lines.push s!"  [{status}] {vc.label}"
    let header := s!"#kav_check_init: {passes}/{total} VCs discharged"
    logInfo m!"{header}\n{String.intercalate "\n" lines.toList}"

end Kav
