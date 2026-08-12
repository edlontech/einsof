import Kav.Core
import Lean

/-! # `kav_action` command

A Veil-like surface syntax for writing `Kav.Action σ` records without spelling
out the frame conditions (`s'.f = s.f`) for every unchanged field.

```
kav_action <name> (<binders>...) : <StateType> where
  require <prop over s>          -- zero or more guard clauses (conjoined)
  require <label> : <prop>       -- optionally labeled guard clause
  <field> := <expr over s>       -- zero or more changed-field updates
```

elaborates to

```
def <name> (<binders>...) : Kav.Action <StateType> :=
  { guard := fun s => <require₁> ∧ … ∧ <requireₙ>      -- `fun _ => True` if none
    next  := fun s s' =>
        s'.<changed₁> = <expr₁> ∧ …                     -- one per mentioned field
        ∧ s'.<framed> = s.<framed> ∧ … }                -- frame for every other field
```

The pre-state binder is literally `s` and the post-state binder is `s'`; both
`require` props and update exprs are written in terms of `s` (and the binders).
`<StateType>` must be a single-constructor structure so its fields can be
enumerated; unmentioned fields get an auto-generated frame condition.

The command also auto-generates named projection lemmas, so proofs never
destructure the `guard`/`next` conjunctions positionally:

- `<name>.next_<field> : (<name> …).next s s' → s'.<field> = <expr | s.<field>>`
  for every state field;
- `<name>.guard_<label> : (<name> …).guard s → <prop>` for every labeled `require`.

All action arguments and the states are implicit in the generated lemmas; they are
inferred from the hypothesis.
-/

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term

namespace Kav

/-- A single item in a `kav_action` body: a `require` clause or a field update. -/
declare_syntax_cat kavActionItem
/-- A `require <prop>` guard clause. -/
syntax "require " term : kavActionItem
/-- A labeled `require <label> : <prop>` guard clause; the label names the generated
`<action>.guard_<label>` projection lemma. -/
syntax "require " ident " : " term : kavActionItem
/-- A `<field> := <expr>` field update. -/
syntax ident " := " term : kavActionItem

/-- Split a right-nested `And` chain into exactly `n` components. -/
private def splitAndN (e : Expr) : Nat → Array Expr
  | 0 => #[]
  | 1 => #[e]
  | n + 2 =>
    match e.and? with
    | some (a, b) => #[a] ++ splitAndN b (n + 1)
    | none => #[e]

/-- The anonymous-projection path to component `i` of an `n`-component `And` chain:
`i` times `And.right`, then `And.left` unless `i` is the last component. -/
private def andProj (h : Expr) (i n : Nat) : Lean.Meta.MetaM Expr := do
  let mut acc := h
  for _ in [0:i] do
    acc ← Lean.Meta.mkAppM ``And.right #[acc]
  if i + 1 < n then
    acc ← Lean.Meta.mkAppM ``And.left #[acc]
  return acc

/-- Set the first `k` binders of a `∀` telescope to implicit. -/
private def implicitizeForalls : Expr → Nat → Expr
  | e, 0 => e
  | .forallE nm ty body _, k + 1 => .forallE nm ty (implicitizeForalls body k) .implicit
  | e, _ => e

/-- The `kav_action` command. See module docstring. The state-type slot is a
    `term` so it can be a parameterized application like `St A B C`; the head
    constant must resolve to a single-constructor structure. -/
syntax (name := kavActionCmd)
  "kav_action " ident (ppSpace bracketedBinder)* " : " term " where"
    manyIndent(ppLine kavActionItem) : command

/-- Elaborate `kav_action`: enumerate the state structure's fields, build the
    guard from the `require` clauses, build `next` from the field updates plus
    auto frame conditions for every unmentioned field, and emit the `def`. -/
elab_rules : command
  | `(command| kav_action $name $binders* : $stateTy:term where $items*) => do
    -- Extract the head constant of the (possibly applied) state-type term and
    -- resolve it to a single-constructor structure. Field NAMES do not depend
    -- on the type arguments, so this suffices for frame-condition generation.
    let headId : Ident ← match stateTy with
      | `($f:ident $_args*) => pure f
      | `($f:ident) => pure f
      | _ => throwErrorAt stateTy
          "kav_action: state type must be a structure name, optionally applied to type arguments"
    let stateName ← liftCoreM <| resolveGlobalConstNoOverload headId
    let env ← getEnv
    let some _ := getStructureInfo? env stateName
      | throwErrorAt stateTy
          "kav_action: `{headId}` is not a structure (needs single-constructor structure for field enumeration)"
    let fields := getStructureFields env stateName

    -- Split body items into requires (with optional labels) and updates.
    let mut requires : Array (TSyntax `term) := #[]
    let mut reqNames : Array (Option Name) := #[]
    let mut updFields : Array Name := #[]
    let mut updExprs : Array (TSyntax `term) := #[]
    for item in items do
      match item with
      | `(kavActionItem| require $p:term) =>
        requires := requires.push p
        reqNames := reqNames.push none
      | `(kavActionItem| require $n:ident : $p:term) =>
        requires := requires.push p
        reqNames := reqNames.push (some n.getId)
      | `(kavActionItem| $f:ident := $e:term) =>
        let fname := f.getId
        if fname ∉ fields then
          throwErrorAt f
            "kav_action: `{f}` is not a field of `{headId}` (fields: {fields.toList})"
        if updFields.contains fname then
          throwErrorAt f "kav_action: field `{f}` updated more than once"
        updFields := updFields.push fname
        updExprs := updExprs.push e
      | _ => throwErrorAt item "kav_action: unexpected body item"

    -- Raw (unhygienic) pre-/post-state binders so the user-written `s` / `s'`
    -- in their `require` props and update exprs resolve to these binders.
    let sId : Ident := mkIdent `s
    let sId' : Ident := mkIdent `s'

    -- guard := fun s => r₁ ∧ … ∧ rₙ   (or `fun _ => True`)
    let guardBody ← do
      if requires.size = 0 then
        `(term| True)
      else
        let mut acc := requires[requires.size - 1]!
        for i in [0:requires.size - 1] do
          let p := requires[requires.size - 2 - i]!
          acc ← `(term| $p ∧ $acc)
        pure acc
    let guard ← `(term| fun $sId => $guardBody)

    -- next conjuncts: one per field. Changed fields → s'.f = <expr>;
    -- unmentioned fields → s'.f = s.f (frame).
    let mut conjs : Array (TSyntax `term) := #[]
    for f in fields do
      let fIdent := mkIdent f
      match updFields.findIdx? (· == f) with
      | some idx =>
        let e := updExprs[idx]!
        conjs := conjs.push (← `(term| $sId'.$fIdent:ident = $e))
      | none =>
        conjs := conjs.push (← `(term| $sId'.$fIdent:ident = $sId.$fIdent:ident))

    let nextBody ← do
      if conjs.size = 0 then
        `(term| True)
      else
        let mut acc := conjs[conjs.size - 1]!
        for i in [0:conjs.size - 1] do
          let c := conjs[conjs.size - 2 - i]!
          acc ← `(term| $c ∧ $acc)
        pure acc
    let next ← `(term| fun $sId $sId' => $nextBody)

    let cmd ← `(command|
      def $name $binders* : Kav.Action ($stateTy) :=
        { guard := $guard, next := $next })
    elabCommand cmd

    -- Auto-generate the named projection lemmas from the elaborated definition, so their
    -- statements are exactly the definition's conjuncts. All action arguments and states
    -- are made implicit; the hypothesis determines them.
    let actionName ← liftCoreM <| resolveGlobalConstNoOverload name
    liftTermElabM do
      let info ← getConstInfo actionName
      let us := info.levelParams
      Meta.forallTelescope info.type fun fnArgs _retTy => do
        let act := mkAppN (mkConst actionName (us.map Level.param)) fnArgs
        let stTy := (← Meta.inferType act).appArg!
        Meta.withLocalDeclD `s stTy fun sVar => do
        Meta.withLocalDeclD `s' stTy fun s'Var => do
          let addProjLemma (lemName : Name) (hyp : Expr) (stmt : Expr) (i n : Nat)
              (stateArgs : Array Expr) : TermElabM Unit :=
            Meta.withLocalDeclD `h hyp fun hVar => do
              let allArgs := fnArgs ++ stateArgs
              let ty ← instantiateMVars (← Meta.mkForallFVars (allArgs ++ #[hVar]) stmt)
              let val ← instantiateMVars
                (← Meta.mkLambdaFVars (allArgs ++ #[hVar]) (← andProj hVar i n))
              addDecl <| Declaration.thmDecl {
                name := lemName
                levelParams := us
                type := implicitizeForalls ty allArgs.size
                value := val }
          -- One `next_<field>` lemma per state field.
          let nextApp ← Meta.mkAppM ``Kav.Action.next #[act, sVar, s'Var]
          let nextComps := splitAndN (← Meta.whnf nextApp) fields.size
          if nextComps.size == fields.size then
            for i in [0:fields.size] do
              addProjLemma (actionName ++ Name.mkSimple s!"next_{fields[i]!}")
                nextApp nextComps[i]! i fields.size #[sVar, s'Var]
          -- One `guard_<label>` lemma per labeled require.
          if reqNames.any Option.isSome then
            let guardApp ← Meta.mkAppM ``Kav.Action.guard #[act, sVar]
            let guardComps := splitAndN (← Meta.whnf guardApp) requires.size
            if guardComps.size == requires.size then
              for i in [0:requires.size] do
                if let some rname := reqNames[i]! then
                  addProjLemma (actionName ++ Name.mkSimple s!"guard_{rname}")
                    guardApp guardComps[i]! i requires.size #[sVar]

end Kav
