import Kav.Core
import Lean

/-! # `kav_action` command

A Veil-like surface syntax for writing `Kav.Action σ` records without spelling
out the frame conditions (`s'.f = s.f`) for every unchanged field.

```
kav_action <name> (<binders>...) : <StateType> where
  require <prop over s>          -- zero or more guard clauses (conjoined)
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
-/

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term

namespace Kav

/-- A single item in a `kav_action` body: a `require` clause or a field update. -/
declare_syntax_cat kavActionItem
/-- A `require <prop>` guard clause. -/
syntax "require " term : kavActionItem
/-- A `<field> := <expr>` field update. -/
syntax ident " := " term : kavActionItem

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

    -- Split body items into requires and updates.
    let mut requires : Array (TSyntax `term) := #[]
    let mut updFields : Array Name := #[]
    let mut updExprs : Array (TSyntax `term) := #[]
    for item in items do
      match item with
      | `(kavActionItem| require $p:term) =>
        requires := requires.push p
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

end Kav
