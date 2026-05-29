import Kav.Core
import Kav.Engine
import Lean

/-! # `#kav_check_invariants` command

Given a `Kav.TransitionSystem σ` and a `List (Kav.Invariant σ)`, generate the
verification conditions for each (action, invariant) pair plus each invariant's
initiation VC, discharge each with the kernel-checked auto+Duper engine
(see `Kav.Engine`), and print a PASS/FAIL table.

Variants:
* `#kav_check_invariants  <ts> <invs>` — discharge + PASS/FAIL table.
* `#kav_check_invariants? <ts> <invs>` — dump each VC goal type (no discharge).
* `#kav_check_invariants! <ts> <invs>` — emit a `theorem … := by auto` skeleton per VC.
-/

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

namespace Kav.Check

/-- A label paired with the `Expr` it names. -/
structure Labeled where
  label : String
  expr  : Expr

/-- Reduce a `String` literal `Expr` to a Lean `String`. Handles both the raw
    `String.lit`/`OfNat`-style encodings and `whnf`-reducible forms. -/
def reduceStringLit (e : Expr) : MetaM String := do
  let e ← whnf e
  match e with
  | .lit (.strVal s) => return s
  | _ =>
    -- Fall back to pretty-printing if it is not a literal (still useful as a label).
    return toString (← ppExpr e)

/-- Walk a `List (String × α)` `Expr` (the `ts.actions` or `invs` list), reducing
    `List.cons`/`List.nil` and pulling out each pair's label `String` and the second
    component `Expr`. Returns the elements in source order. -/
partial def walkLabeledList (e : Expr) : MetaM (Array Labeled) := do
  go e #[]
where
  go (e : Expr) (acc : Array Labeled) : MetaM (Array Labeled) := do
    let e ← whnf e
    match e.getAppFnArgs with
    | (``List.cons, #[_elemTy, hd, tl]) =>
      -- `hd : String × α`; reduce it to a `Prod.mk` and split.
      let hd ← whnf hd
      match hd.getAppFnArgs with
      | (``Prod.mk, #[_a, _b, labelE, valE]) =>
        let label ← reduceStringLit labelE
        go tl (acc.push { label := label, expr := valE })
      | _ =>
        throwError "kav: list element is not a `Prod.mk` pair: {hd}"
    | (``List.nil, _) => return acc
    | _ => throwError "kav: could not reduce list to cons/nil spine: {e}"

/-- Build the conjunction predicate `fun s => inv₁ s ∧ inv₂ s ∧ … ∧ invₙ s` over the
    state type `σ`, where each `invᵢ` is a `σ → Prop` `Expr`. For a single invariant
    this is just that predicate (eta-reduced via the binder). -/
def buildAllInvConj (σ : Expr) (invs : Array Labeled) : MetaM Expr := do
  withLocalDeclD `s σ fun s => do
    match invs.toList with
    | [] => mkLambdaFVars #[s] (mkConst ``True)
    | inv :: rest => do
      let mut body ← whnf (mkApp inv.expr s)
      for inv in rest do
        let next ← whnf (mkApp inv.expr s)
        body := mkApp2 (mkConst ``And) body next
      mkLambdaFVars #[s] body

/-- Build the preservation VC `Kav.preservesVC σ allInv act inv` as an `Expr`. -/
def mkPreservesVC (σ allInv actExpr invExpr : Expr) : MetaM Expr :=
  mkAppOptM ``Kav.preservesVC #[some σ, some allInv, some actExpr, some invExpr]

/-- Build the initiation VC `Kav.initVC σ ts inv` as an `Expr`. -/
def mkInitVC (σ tsExpr invExpr : Expr) : MetaM Expr :=
  mkAppOptM ``Kav.initVC #[some σ, some tsExpr, some invExpr]

/-- A single generated VC: a human label and its goal type `Expr`. -/
structure VC where
  label   : String
  goalTy  : Expr

/-- Elaborate the two command arguments, extract the action + invariant lists, and
    build every VC (`preservesVC` per (action, invariant) pair + `initVC` per
    invariant). Returns the state type and the VC list. Runs in `TermElabM`. -/
def buildVCs (tsStx invsStx : Syntax) : TermElabM (Expr × Array VC) := do
  let tsExpr ← elabTerm tsStx none
  synthesizeSyntheticMVarsNoPostponing
  let tsExpr ← instantiateMVars tsExpr
  let tsTy ← whnf (← inferType tsExpr)
  let σ ← match tsTy.getAppFnArgs with
    | (``Kav.TransitionSystem, #[σ]) => pure σ
    | _ => throwError "kav: first argument must be a `Kav.TransitionSystem σ`, got type {tsTy}"
  let invsExpr ← elabTerm invsStx none
  synthesizeSyntheticMVarsNoPostponing
  let invsExpr ← instantiateMVars invsExpr
  -- Extract action list from `ts.actions`.
  let actionsE ← mkAppM ``Kav.TransitionSystem.actions #[tsExpr]
  let actions ← walkLabeledList actionsE
  let invs ← walkLabeledList invsExpr
  let allInv ← buildAllInvConj σ invs
  let mut vcs : Array VC := #[]
  for act in actions do
    for inv in invs do
      let goalTy ← mkPreservesVC σ allInv act.expr inv.expr
      vcs := vcs.push { label := s!"{inv.label} × {act.label}", goalTy := goalTy }
  for inv in invs do
    let goalTy ← mkInitVC σ tsExpr inv.expr
    vcs := vcs.push { label := s!"{inv.label} × init", goalTy := goalTy }
  return (σ, vcs)

/-- Names we never try to `unfold`/`simp` (structural / kernel constants that have no
    useful definitional expansion for the engine). -/
def unfoldDenylist : Std.HashSet Name :=
  Std.HashSet.ofList
    [``Eq, ``And, ``Or, ``Not, ``Iff, ``True, ``False, ``Bool,
     ``Prod, ``Prod.mk, ``List, ``List.cons, ``List.nil, ``Exists,
     ``Kav.Action, ``Kav.TransitionSystem]

/-- Collect the user-level (delta-reducible, non-denylisted) constant names appearing
    in the goal type — these are the `def`s (`sys`, `flip`, the invariant predicates, …)
    that the discharge tactic must unfold so `auto`/`simp_all` can see their bodies. -/
def collectUnfoldNames (goalTy : Expr) : MetaM (Array Name) := do
  let env ← getEnv
  let mut names : Std.HashSet Name := {}
  for c in goalTy.getUsedConstants do
    if unfoldDenylist.contains c then continue
    -- Only delta-reducible definitions (skip inductives, axioms, ctors).
    match env.find? c with
    | some (.defnInfo _) => names := names.insert c
    | _ => pure ()
  -- Always unfold the two VC wrappers.
  names := names.insert ``Kav.preservesVC
  names := names.insert ``Kav.initVC
  return names.toArray

/-- Attempt to discharge a goal type with the kernel-checked engine by elaborating a
    `by`-term against it inside `try … catch`. The tactic unfolds the user definitions
    appearing in the goal (so `auto` can see the action/invariant bodies), then runs
    `intros <;> simp_all <;> auto`. Returns `true` on success. -/
def tryDischarge (goalTy : Expr) : TermElabM Bool := do
  let unfolds ← collectUnfoldNames goalTy
  let unfoldIdents : Array (TSyntax `term) := unfolds.map (fun n => mkIdent n)
  let tac ← `(by
    (try simp only [$[$unfoldIdents:term],*]) <;> intros <;> (try simp_all) <;> auto)
  -- Snapshot the message log so we can DISCARD whatever the (possibly failing) engine
  -- logs — a FAIL is data for our table, not a command-level error.
  let savedLog ← Core.getMessageLog
  let result : Bool ←
    try
      -- `withoutErrToSorry` makes a failing tactic THROW (so `catch` sees it) instead of
      -- silently elaborating to `sorry`.
      let pf ← withoutErrToSorry <| elabTermEnsuringType tac (some goalTy)
      synthesizeSyntheticMVarsNoPostponing
      let pf ← instantiateMVars pf
      pure (!(pf.hasSyntheticSorry || pf.hasExprMVar))
    catch _ =>
      pure false
  unless result do
    -- Roll the message log back to before the attempt, dropping the engine's noise.
    Core.setMessageLog savedLog
  return result

end Kav.Check

namespace Kav

open Lean.Elab.Command Kav.Check

/-- Discharge mode: PASS/FAIL table. -/
syntax (name := kavCheckInvariants)
  "#kav_check_invariants" term:max term:max : command
/-- Dump mode: pretty-print each VC goal type, no discharge. -/
syntax (name := kavCheckInvariantsDump)
  "#kav_check_invariants?" term:max term:max : command
/-- Skeleton mode: emit a `theorem … := by auto` per VC for manual fallback. -/
syntax (name := kavCheckInvariantsSkel)
  "#kav_check_invariants!" term:max term:max : command

/-- Shared body: build the VCs then act according to `markerStr` (`none` = discharge,
    `"?"` = dump, `"!"` = skeleton). -/
def runKavCheck (markerStr : Option String) (tsStx invsStx : Syntax) : CommandElabM Unit := do
    liftTermElabM do
      let (_σ, vcs) ← buildVCs tsStx invsStx
      match markerStr with
      | some "?" =>
        -- Dump mode: pretty-print each goal type.
        for vc in vcs do
          logInfo m!"{vc.label}:\n  {vc.goalTy}"
      | some "!" =>
        -- Skeleton mode: emit a paste-ready theorem per VC.
        for vc in vcs do
          let name := (vc.label.replace " × " "_").replace " " "_"
          logInfo m!"theorem {name} : {vc.goalTy} := by auto"
      | _ =>
        -- Discharge mode: PASS/FAIL table.
        let mut lines : Array String := #[]
        let mut passes := 0
        let mut total := 0
        for vc in vcs do
          total := total + 1
          let ok ← tryDischarge vc.goalTy
          if ok then passes := passes + 1
          let status := if ok then "PASS" else "FAIL"
          lines := lines.push s!"  [{status}] {vc.label}"
        let header := s!"#kav_check_invariants: {passes}/{total} VCs discharged"
        logInfo m!"{header}\n{String.intercalate "\n" lines.toList}"

@[command_elab kavCheckInvariants]
def elabKavCheckInvariants : CommandElab := fun stx =>
  runKavCheck none stx[1] stx[2]

@[command_elab kavCheckInvariantsDump]
def elabKavCheckInvariantsDump : CommandElab := fun stx =>
  runKavCheck (some "?") stx[1] stx[2]

@[command_elab kavCheckInvariantsSkel]
def elabKavCheckInvariantsSkel : CommandElab := fun stx =>
  runKavCheck (some "!") stx[1] stx[2]

end Kav
