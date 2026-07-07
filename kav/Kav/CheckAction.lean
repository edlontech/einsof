import Kav.Core
import Kav.Engine
import Kav.Check
import Lean

/-! # `#kav_check_action` command

A **per-action** invariant-preservation checker that, unlike `#kav_check_invariants`,
keeps the action parameters **universally quantified and in scope** rather than
existentially closed (`Kav.close1/2/3`). For an action family

```
f : T₁ → … → Tₙ → Kav.Action σ
```

and an invariant `inv : σ → Prop`, it builds and discharges

```
∀ (x₁:T₁) … (xₙ:Tₙ) (s s' : σ),
  <allInvConj> s → (f x₁…xₙ).guard s → (f x₁…xₙ).next s s' → inv s'
```

There is no `∃ params`, which is the shape the Phase-0 spike proved trivially.

```
#kav_check_action <actionTerm> <invListTerm>
```

The two arguments must elaborate over the **same** state type `σ` (monomorphize at
opaque sorts in the caller so they unify). Prints a PASS/FAIL table + `N/M discharged`.
-/

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

namespace Kav.Check

/-! ## Transitive unfold collection

`Check.lean`'s `collectUnfoldNames` is shallow (one level). For the per-action goal we
need every `def` reachable from the goal — the action `def`, the invariant `def`s, and
the `Kav.Action.guard` / `.next` projections — so `simp only [...]` exposes the field
equations before the engine runs. We walk `defnInfo.value.getUsedConstants` to a
fixpoint. -/

/-- Names we never unfold (structural / kernel constants with no useful body for the
    engine). Mirrors `Check.unfoldDenylist`. -/
def actionUnfoldDenylist : Std.HashSet Name :=
  Std.HashSet.ofList
    [``Eq, ``And, ``Or, ``Not, ``Iff, ``True, ``False, ``Bool,
     ``Prod, ``Prod.mk, ``List, ``List.cons, ``List.nil, ``Exists,
     ``Kav.Action, ``Kav.TransitionSystem, ``ite, ``dite]

/-- Transitively collect delta-reducible `def` names reachable from `goalTy`, walking each
    definition's body to a fixpoint. Skips denylisted names, inductives, axioms, ctors, and
    `@[irreducible]` defs — irreducibility is the caller's way of saying "the cascade must
    treat this as an opaque atom" (e.g. `ceilingAdmits`: unfolding it at every gate site
    re-introduces an existential blowup that congruence closure avoids). -/
def collectUnfoldNamesTransitive (goalTy : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let mut acc : Std.HashSet Name := {}
  let mut frontier : Array Name := goalTy.getUsedConstants
  while !frontier.isEmpty do
    let mut next : Array Name := #[]
    for c in frontier do
      if actionUnfoldDenylist.contains c then continue
      if acc.contains c then continue
      if (← getReducibilityStatus c) matches .irreducible then continue
      match env.find? c with
      | some (.defnInfo info) =>
        acc := acc.insert c
        for d in info.value.getUsedConstants do
          unless acc.contains d do next := next.push d
      | _ => pure ()
    frontier := next
  return acc.toArray

/-! ## Goal construction

Build the per-(action, invariant) preservation goal as an `Expr`, with the action
parameters as outer `∀` binders. -/

/-- Build the goal
    `∀ (x₁:T₁)…(xₙ:Tₙ) (s s' : σ), allInv s → (act x₁…xₙ).guard s → (act x₁…xₙ).next s s' → inv s'`
    where `act` is the (possibly curried) action family `Expr`, `σ` the state type, and
    the parameter telescope is read off `act`'s type. -/
def mkPerActionVC (actExpr σ allInv invExpr : Expr) : MetaM Expr := do
  let actTy ← inferType actExpr
  forallTelescopeReducing actTy fun params _resultTy => do
    let actApplied := mkAppN actExpr params
    let guardE ← mkAppM ``Kav.Action.guard #[actApplied]
    let nextE  ← mkAppM ``Kav.Action.next  #[actApplied]
    withLocalDeclD `s σ fun s => do
      withLocalDeclD `s' σ fun s' => do
        let hAll  := mkApp allInv s
        let hG    := mkApp guardE s
        let hN    := mkApp2 nextE s s'
        let concl := mkApp invExpr s'
        -- inv-bundle → guard → next → conclusion, all as nondependent arrows
        let body ← mkArrow hAll (← mkArrow hG (← mkArrow hN concl))
        mkForallFVars (params ++ #[s, s']) body

/-- A single generated VC for one invariant. -/
structure ActionVC where
  label  : String
  goalTy : Expr

/-- Elaborate the action term + invariant list, peel the action's parameter telescope to
    recover the state type `σ`, and build one preservation VC per invariant. -/
def buildActionVCs (actStx invsStx : Syntax) : TermElabM (Expr × Array ActionVC) := do
  let actExpr ← elabTerm actStx none
  synthesizeSyntheticMVarsNoPostponing
  let actExpr ← instantiateMVars actExpr
  -- Peel the Pi binders of the action's TYPE to find the `Kav.Action σ` result.
  let actTy ← inferType actExpr
  let σ ← forallTelescopeReducing actTy fun _params resultTy => do
    let resultTy ← whnf resultTy
    match resultTy.getAppFnArgs with
    | (``Kav.Action, #[σ]) => pure σ
    | _ => throwError "kav: action term must have result type `Kav.Action σ`, got {resultTy}"
  -- Invariant list, sharing `σ`.
  let invsExpr ← elabTerm invsStx none
  synthesizeSyntheticMVarsNoPostponing
  let invsExpr ← instantiateMVars invsExpr
  let invs ← walkLabeledList invsExpr
  let allInv ← buildAllInvConj σ invs
  let mut vcs : Array ActionVC := #[]
  for inv in invs do
    let goalTy ← mkPerActionVC actExpr σ allInv inv.expr
    vcs := vcs.push { label := inv.label, goalTy := goalTy }
  return (σ, vcs)

/-- Discharge a per-action VC by elaborating a `by`-term inside `try … catch` with
    message-log rollback (so a FAIL is table data, not a command error).

    The tactic intros all hypotheses, transitively unfolds the action / invariant `def`s
    and the `guard`/`next` projections, splits the relational `next` into its field
    equations, substitutes them, and then tries cheap closers (`tauto`, `simp_all`)
    before the kernel-checked `auto` / `duper` fallback. -/
def tryDischargeAction (goalTy : Expr) : TermElabM Bool := do
  let unfolds ← collectUnfoldNamesTransitive goalTy
  let unfoldIdents : Array (TSyntax `term) := unfolds.map (fun n => mkIdent n)
  let tac ← `(by
    intros <;> (try simp only [$[$unfoldIdents:term],*] at *) <;>
      (first | (trivial) | (grind) | (simp_all <;> grind) | (auto) | (duper [*])))
  let savedLog ← Core.getMessageLog
  let result : Bool ←
    try
      let pf ← withoutErrToSorry <| elabTermEnsuringType tac (some goalTy)
      synthesizeSyntheticMVarsNoPostponing
      let pf ← instantiateMVars pf
      pure (!(pf.hasSyntheticSorry || pf.hasExprMVar))
    catch _ =>
      pure false
  unless result do
    Core.setMessageLog savedLog
  return result

end Kav.Check

namespace Kav

open Lean.Elab.Command Kav.Check

/-- Discharge mode: per-action PASS/FAIL table. -/
syntax (name := kavCheckAction)
  "#kav_check_action" term:max term:max : command
/-- Dump mode: pretty-print each per-action VC goal type (no discharge). -/
syntax (name := kavCheckActionDump)
  "#kav_check_action?" term:max term:max : command

def runKavCheckAction (dump : Bool) (actStx invsStx : Syntax) : CommandElabM Unit := do
  liftTermElabM do
    let (_σ, vcs) ← buildActionVCs actStx invsStx
    if dump then
      for vc in vcs do
        logInfo m!"{vc.label}:\n  {vc.goalTy}"
    else
      let mut lines : Array String := #[]
      let mut passes := 0
      let mut total := 0
      for vc in vcs do
        total := total + 1
        let ok ← tryDischargeAction vc.goalTy
        if ok then passes := passes + 1
        let status := if ok then "PASS" else "FAIL"
        lines := lines.push s!"  [{status}] {vc.label}"
      let header := s!"#kav_check_action: {passes}/{total} VCs discharged"
      logInfo m!"{header}\n{String.intercalate "\n" lines.toList}"

@[command_elab kavCheckAction]
def elabKavCheckAction : CommandElab := fun stx =>
  runKavCheckAction false stx[1] stx[2]

@[command_elab kavCheckActionDump]
def elabKavCheckActionDump : CommandElab := fun stx =>
  runKavCheckAction true stx[1] stx[2]

end Kav
