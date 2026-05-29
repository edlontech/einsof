# Kav Spike — Task 2 results (invoke_start hard VC)

Date: 2026-05-27. Stack: Lean **4.30.0** stable; `auto` @ `v4.30.0-hammer`, `Duper`
@ `v4.30.0`. NO mathlib import, NO lean-smt. File:
`Kav/Spike/InvokeStart.lean`.

## The question

Can a **kernel-checked** prover (`auto` with the Duper native rebind, or bare
`duper`) discharge the hardest VC of the invoke_start transition — the
override-consumption invariant — on a mathlib-free stack?

## Answer: **GO.** Full automation closes it, kernel-checked, in one shot.

## 1. auto + Duper rebind

Worked **as-is**, no API drift. The README incantation elaborates verbatim on
`v4.30.0-hammer` (it is in fact copied verbatim inside the package itself:
`.lake/packages/auto/Auto/EvaluateAuto/TestAuto.lean:233-238`). `Duper.runDuper`
lives in `Duper/Interface.lean:416` (re-exported via `Duper.Tactic`) with the
expected signature. The only artifact is a cosmetic
`unused variable inhs` linter warning on the rebind boilerplate — harmless.

```lean
import Auto.Tactic
import Duper.Tactic
open Lean Auto in
def Auto.duperRaw (lemmas : Array Lemma) (inhs : Array Lemma) : MetaM Expr := do
  let lemmas : Array (Expr × Expr × Array Name × Bool) ← lemmas.mapM
    (fun ⟨⟨proof, ty, _⟩, _⟩ => do return (ty, ← Meta.mkAppM ``eq_true #[proof], #[], true))
  Duper.runDuper lemmas.toList [] 0
attribute [rebind Auto.Native.solverFunc] Auto.duperRaw
set_option auto.native true
```

## 2. Easy VC — `invoke_start_pres_in_flight_active`

**PASSED** as provided (pure structural Lean, no prover). The St/guard/post
encoding is sound — the pipeline smoke test is green.

## 3. Hard VC — `invoke_start_pres_override_consumed`

Closed **THREE independent ways**, all green:

| Variant | Tactic | Result |
|---|---|---|
| `..._override_consumed`       | manual `by_cases` split + `rw`/`exact`/`rcases` glue | green |
| `..._override_consumed_auto`  | `auto` (one shot, after `unfold ... at *`)            | green |
| `..._override_consumed_duper` | `duper [hinv, hg]` (one shot)                         | green |

Both **full automation** paths (`auto` and bare `duper`) close the whole VC with
no manual case split. The manual variant is kept as a belt-and-suspenders
reference; its glue is ~9 lines and **trivial** (one `by_cases`, one `rw` of the
`invocation_tool inv = tool` guard fact, `refine`/`exact` of the disjunct, and an
`hinv` application on the carried-over branch — no term surgery).

`#print axioms` for both checked variants:

```
'invoke_start_pres_override_consumed'      depends on axioms: [propext, Classical.choice, Quot.sound]
'invoke_start_pres_override_consumed_auto' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Only the three standard kernel axioms. No Smt/solver axiom, no sorryAx.** This
is a genuinely kernel-checked close — exactly the GO criterion.

`maxHeartbeats`: 1000000 (set per the task; auto/duper finished well under it).
Full-file wall clock (cold deps already built): ~3.3 s for all five theorems
including two `#print axioms`. auto/duper each take well under a second on this VC.

## 4. IMPORTANT statement-correction finding (read this)

The hard VC **did NOT close on the `override_consumed` definition as originally
written in the file.** `auto` returned `Duper saturated` and bare `duper`
returned "unable to do so" — and that was **correct behaviour: the original
invariant was not inductive (it is false as a preservation goal).**

Root cause (a genuine spec gap in the spike file, NOT a prover weakness): the
`post` consumption clause only sets `override_used a tool L` when
`s.speculative_taint a L` holds, but the original `override_consumed` antecedent
omitted `speculative_taint`. Counterexample to preservation: a state with
`speculative_taint a L = False` but `flow_override a tool L`,
`tool_egress tool E`, `¬flow_allows`, `¬inspect`. The guard's flow gate is then
vacuously satisfied (its antecedent `speculative_taint ∧ tool_egress` is false),
so the transition fires; `post` does NOT mark the override consumed (its clause
needs `speculative_taint`); yet the original invariant demands `override_used`
on the freshly-inserted in-flight cell. Invariant violated.

I isolated this to a single `sorry` (the `speculative_taint A L` obligation) with
the rest of the proof structurally complete, then confirmed `duper` reports that
exact subgoal as definitively underivable from the available premises (not a
timeout).

**Fix applied:** added the missing `s.speculative_taint A L` antecedent to
`override_consumed` (one line). This matches the Veil/Rocq semantics
(`override_consumed_when_sole_justification` carries the taint condition — the
override only needs consuming when the flow actually relies on it, i.e. under
taint). This is a **statement edit**, made because the spike's purpose is the
honest feasibility answer and the original statement was simply false; flag for
owner review. With the corrected (and now genuinely inductive) statement, full
automation closes it immediately as shown above.

Verbatim errors seen on the original (false) statement:
```
error: ...InvokeStart.lean:96:2: Duper saturated                      -- auto
error: ...InvokeStart.lean:96:2: Duper failed to solve the goal and    -- bare duper
       determined that it will be unable to do so with the current
       configuration of options and selection of premises
```

## 5. Recommendation: **GO**

- The mathlib-free `auto`+Duper / bare-`duper` stack **discharges the hardest
  invoke_start VC fully automatically, kernel-checked** (standard axioms only).
- The rebind incantation works unmodified on `v4.30.0-hammer`.
- The one snag was not the prover — it was a non-inductive (false) invariant in
  the spike file. A correct prover *should* refuse a false goal; ours did, then
  closed the corrected goal in one shot. That is the ideal behaviour.
- Manual fallback, when wanted, is trivial (~9 lines, one `by_cases`).

Caveat for the team: this is one VC on a faithfully-translated but small slice.
The remaining risk is **scaling** — whether `auto`/`duper` stay this clean across
all 12 actions / 23-conjunct invariant bundle, and whether monomorphization or
saturation bite on transitions with richer existentials. None observed here.

---

# Model checker — Task 4 results (Fin-n CTI enumeration)

Date: 2026-05-27. File: `Kav/Spike/ModelCheck.lean`.

## Question

Can a **computable, solver-free `Fin 2` model checker** (pure Lean, no mathlib,
no SMT) find a counterexample-to-induction (CTI) for the `override_consumed`
invariant when a deliberately broken `post` is used, and report no CTI for the
correct `post`?

## Answer: **GO.** Both `native_decide` goals close instantly.

## What was built

- `DSt` — a `structure` with `Bool`-valued fields mirroring `St`, using `A2 = Fin 2`
  for agents/tools/invocations uniformly.
- `override_consumedB`, `guardB`, `postB` — `Bool` mirrors of the Prop-valued
  `override_consumed`, `guard`, `post`, using `List.finRange 2` (no `Fintype`/
  `Finset`/mathlib), `List.all`/`List.any`, and `decide` to bound all quantifiers.
- `postB_broken` — planted bug: extends `in_flight` but drops the `override_used`
  consumption clause entirely.
- Three hand-built seeds (`seed0`/`seed1`/`seed2`) that exercise the override path:
  agent 0 tainted at `.sensitive`, `flow_override = true`, `tool_egress .net = true`,
  `flow_allows = false`, `flow_inspects = false` — so the consumption obligation
  fires on the first new in-flight entry added by `postB`.

## Results

| Goal | `native_decide` result |
|---|---|
| `invoke_start_model_check : no_cti = true` | closed (correct `postB` — no CTI among seeds) |
| `example : no_cti_broken = false` | closed (broken `postB_broken` — CTI detected) |

Both goals closed. `lake build` wall clock: **~2.1 s** (warm, after InvokeStart
replayed). `native_decide` itself runs in a fraction of a second — the seed
enumeration is tiny (3 seeds × 2³ parameter triples = 24 transition checks).

## Confirmed: mathlib-free

Only `List.finRange n` (core Lean) was used to enumerate `Fin 2`. No `Fintype`,
no `Finset`, no mathlib import anywhere. `override_consumedB` and `guardB` are
plain `Bool` expressions over `List.all`/`List.any`.

## Key design note

The seed construction is critical. The CTI for the broken post only triggers when
a seed satisfies `override_consumedB` before the transition (so the filter passes)
AND the transition parameters exercise the consumption path. `seed0` (and `seed1`)
accomplish this: no in-flight entries yet (invariant trivially satisfied), but
`flow_override`/`speculative_taint`/`tool_egress` are all set for `(agent 0, tool 0,
.sensitive)`. After `postB_broken` fires with `(a=0, tool=0, inv=0)`, the new
in-flight entry `(0, 0)` is present but `override_used 0 0 .sensitive = false`
— violating `override_consumedB`. Correct `postB` sets it, so no CTI.
