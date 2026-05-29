import Kav.ModelCheck
import Lean

/-! # `#kav_model_check` command

Sugar over `Kav.FiniteModel.noCTI` / `.findCTI`. Given a `Kav.FiniteModel σ`
term, elaborate `<term>.noCTI`, reduce it, and `logInfo` either a clean result
(`no CTI among N states`) or a CTI-found notice. The witness `(s, label, s')` is
recovered with `#eval <term>.findCTI` (which needs a `Repr σ` instance — not all
state types have one, hence the witness is opt-in via `#eval`, while the
pass/fail verdict here works for any `σ`).

The real, machine-checkable deliverable is `<term>.noCTI = true` discharged by
`native_decide`; this command is a quick read-out for interactive use. -/

open Lean Lean.Meta Lean.Elab Lean.Elab.Command Lean.Elab.Term

namespace Kav

/-- Read-out the model-check verdict for a `Kav.FiniteModel` term. -/
syntax (name := kavModelCheck) "#kav_model_check" term:max : command

@[command_elab kavModelCheck]
def elabKavModelCheck : CommandElab := fun stx => do
  liftTermElabM do
    let mExpr ← elabTerm stx[1] none
    synthesizeSyntheticMVarsNoPostponing
    let mExpr ← instantiateMVars mExpr
    let mTy ← whnf (← inferType mExpr)
    let σ ← match mTy.getAppFnArgs with
      | (``Kav.FiniteModel, #[σ]) => pure σ
      | _ => throwError "kav: argument must be a `Kav.FiniteModel σ`, got type {mTy}"
    -- Count of explored states (for the report).
    let statesE ← mkAppOptM ``Kav.FiniteModel.states #[some σ, some mExpr]
    let lenE ← mkAppM ``List.length #[statesE]
    let nStates ← unsafe evalExpr Nat (mkConst ``Nat) lenE
    -- Verdict: reduce `m.noCTI` to a Bool.
    let noCTIExpr ← mkAppOptM ``Kav.FiniteModel.noCTI #[some σ, some mExpr]
    let clean ← unsafe evalExpr Bool (mkConst ``Bool) noCTIExpr
    if clean then
      logInfo m!"#kav_model_check: no CTI among {nStates} states (invariant inductive over the explored set)"
    else
      logInfo m!"#kav_model_check: CTI FOUND among {nStates} states \
        (invariant NOT inductive). Run `#eval (<model>).findCTI` for the witness (s, label, s')."

end Kav
