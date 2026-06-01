# A line-by-line walkthrough of the `register_tool` refinement proof

This document explains the two theorems in
[`ArgusLean/Refinement/Simulation.lean`](../ArgusLean/Refinement/Simulation.lean)
**from the ground up**, assuming no prior Lean or formal-methods background. It covers:

- what we are even trying to prove (and why),
- every piece of Lean *syntax* that appears,
- every *tactic* (proof command) we use, and *why* that one,
- the domain-specific helpers (`Rtool`, `vsMem`, the Aeneas `Result` monad).

If you read it top to bottom you should be able to re-derive the proof yourself.

---

## Part 0 — The mental model (read this first)

### What is a "proof" in Lean?

Lean is built on a slogan: **propositions are types, and proofs are programs**.

- A *proposition* (a true-or-false statement, like "3 < 5") is a **type**.
- A *proof* of that proposition is a **value** of that type.

So when you write `theorem foo : P := proof`, you are really saying "`proof` is a value
whose type is `P`". If Lean's type-checker accepts it, the proposition holds; there is no
separate "is this proof valid?" step. **Type-checking *is* proof-checking.** This is why a
green build is the whole verification: if it compiles with no `sorry` and only standard
axioms, it's sound.

Writing proof *values* by hand is painful, so Lean gives you **tactic mode**: you write
`:= by` and then a sequence of *tactics*, commands that manipulate the current
**goal** (the thing left to prove) and the **hypotheses** (facts you already have). Tactics
are just a convenient way to *build* the underlying proof value. Every tactic step
transforms the proof state; when there are no goals left, the proof is done.

A useful picture of the proof state at any moment:

```
hyp1 : SomeFact
hyp2 : AnotherFact
⊢ TheGoalToProve          -- "⊢" (turnstile) means "we must prove..."
```

### What are we proving here? (Refinement / forward simulation)

We have **two** descriptions of the same authorization machine:

1. **The abstract spec** (`Tzimtzum`, in the `tzimtzum/` directory): a clean mathematical
   state machine that has *already* been proven to satisfy the safety properties. This is
   the "source of truth".
2. **The concrete implementation** (`argus-kernel`, written in Rust, then *mechanically
   translated* into Lean by the Aeneas/Charon tool into
   `ArgusLean/Generated/ArgusKernel.lean`). This is what actually ships.

We want the safety proofs about the spec to *transfer* to the real Rust code. The standard
way to connect them is a **refinement** via **forward simulation**:

> Define a relation `R` between concrete states and abstract states. Then prove: whenever
> the concrete machine takes a step from a concrete state `st` related to abstract state
> `a`, the abstract machine can take a *matching* step to some `a'`, and the resulting
> states `st'` and `a'` are *still related*.

Picture it as a commuting square:

```
        st  ───(concrete register_tool)──▶  st'
        │                                    │
     R  │ (related)                          │ R  (still related)
        │                                    │
        a  ───(abstract register_tool)──▶   a'
```

If every concrete step can be mirrored like this, then any safety property the abstract
machine guarantees is also guaranteed by the concrete one. Proving this square for **one**
transition (`register_tool`) is what these two theorems do. (`register_tool` is the
warm-up; the other 11 transitions are the "C2 fan-out" that reuses this exact shape.)

### Why *two* theorems instead of one?

A Lean proof is a term, so you refactor it like you refactor code: pull a self-contained
sub-derivation into its own named lemma. The original proof did two unrelated jobs:

1. **Decode** the concrete step: dig through how the Rust function actually computes, to
   find out *what must have been true* for it to succeed. (No mention of the abstract spec
   at all.)
2. **Simulate**: use those facts to build the matching abstract step and re-establish the
   relation.

Splitting them gives:

- `register_tool_ok_inv` — the **inversion lemma** (job 1). "Inversion" because we run the
  function's logic *backwards*: given that it returned success, we *invert* that to recover
  its inputs/preconditions.
- `register_tool_refines` — the **simulation** (job 2), which calls the inversion lemma.

---

## Part 1 — The supporting definitions

The two theorems lean on definitions from neighbouring files. You need these three.

### `vsMem` — what a concrete set "means" (from `Collections.lean`)

The Rust kernel stores sets as `VecSet`, a vector (growable array) with no duplicates.
Aeneas translated it faithfully, including its internal index loops. We do **not** want to
reason about array loops in every proof, so we define one bridge:

```lean
def vsMem {T : Type} (vs : collections.VecSet T) (x : T) : Prop := x ∈ vs.items.val
```

- `def name ... : Type := body` defines a function/value.
- `{T : Type}` is an **implicit argument** (the curly braces): `T` is the element type, but
  you never pass it explicitly; Lean infers it from the other arguments.
- `vsMem vs x` is a `Prop` (a proposition) meaning "**x is a member of the set vs**",
  defined as `x ∈ vs.items.val`, i.e. `x` is in the underlying list (`.items.val` reaches
  through the `VecSet` wrapper to the raw list). From here on we reason about *membership*,
  never about the loop that computes it.

`Collections.lean` also proves "specs" for the set operations (`vecSetContains_spec`,
`vecSetInsert_spec`, `isTrustedIssuer_spec`) that say things like "`insert` adds `x` to the
set". We consume those as black boxes; see Part 3.

### `AbsState` and `Rtool` — the relation (from `StateRelation.lean`)

```lean
abbrev AbsState := Tzimtzum.St types.AgentId types.ToolId types.InvocationId
  capability.CapKind types.EgressKind types.IssuerId types.InstructionId
```

- `abbrev` is an **abbreviation**, a name for a type expression. `AbsState` is the abstract
  spec's state type `Tzimtzum.St`, *instantiated* at the kernel's concrete id types (tool
  ids are strings, etc.). The spec is generic over these sorts; here we pin them down.

```lean
def Rtool (st : state.KernelState) (bg : background.BackgroundTheory) (a : AbsState) : Prop :=
  (∀ t, a.tool_registered t ↔ vsMem st.tool_registered t) ∧
  (∀ i, a.trusted_issuer i ↔ vsMem bg.trusted_issuers i) ∧
  (∀ t tm, bg.tool_metadata t = .ok (some tm) → a.tool_issuer t = tm.issuer)
```

`Rtool` is the relation `R` from the square, but **narrowed to only the fields
`register_tool` touches** (the full 28-field relation is later work). Read the symbols:

- `∀ t, ...` — "for all `t`, ...". Universal quantifier.
- `P ↔ Q` — "P **if and only if** Q" (logical equivalence).
- `P ∧ Q` — "P **and** Q".
- `→` — logical implication ("if ... then ...").
- `.ok (some tm)` — explained in Part 2 (it's the success result wrapping an `Option`).

So `Rtool st bg a` says three things line up between concrete and abstract:

1. a tool is registered abstractly **iff** it's in the concrete `tool_registered` set;
2. an issuer is trusted abstractly **iff** it's in the concrete `trusted_issuers` set;
3. the abstract `tool_issuer` agrees with whatever issuer the concrete metadata records.

These three conjuncts get the names `hRegRel`, `hTrustRel`, `hIssuerRel` in the simulation
proof (Part 4).

`st` is the *mutable* kernel state; `bg` is the *immutable* "background theory" (the static
config: tool metadata, trusted issuers). `bg` never changes during a step.

---

## Part 2 — The Aeneas `Result` monad (the one genuinely unusual thing)

The Rust function was translated into Lean. Rust functions can **panic** or **loop
forever**, and they often return Rust's own `Result<T, E>` (`Ok`/`Err`). Aeneas models all
of this with **two layers**, and you must keep them straight or the proof reads like noise.

**Layer 1 — the Aeneas `Result` monad** (models panic/divergence). Three constructors:

| Constructor | Meaning |
|-------------|---------|
| `.ok x`     | the computation finished normally with value `x` |
| `.fail e`   | it panicked (e.g. integer overflow, array out of bounds) |
| `.div`      | it might not terminate |

**Layer 2 — Rust's own `Result` type** (the function's *intended* success/error). Here its
constructors are written `.Ok` and `.Err` (capital, from `core.result.Result`).

So the hypothesis we start from,

```lean
hok : transitions.register_tool st bg tool = .ok (.Ok (st', ev))
```

reads: "the function **did not panic and terminated** (`.ok`, layer 1), **and** its Rust
return value was **success** (`.Ok`, layer 2), carrying the new state `st'` and event `ev`."
Both layers said "success". Our whole job in the inversion lemma is to walk through the
function's body and figure out what that forces.

The key rewrite lemma for chaining monadic steps is **`bind_tc_ok`**:

```
(.ok x) >>= f   reduces to   f x
```

`>>=` ("bind") is "do this computation, then feed its result to the next". `bind_tc_ok`
says: if a step already succeeded with value `x`, just continue with `f x`. We apply it
repeatedly to march through the function one operation at a time.

One more helper — **`spec_imp_exists`**. Aeneas states operation specs in a
weakest-precondition style with the triple notation `f ⦃ r => P r ⦄`, meaning "`f`
succeeds and its result `r` satisfies `P r`". `spec_imp_exists` repackages that triple into
an ordinary existential we can take apart:

```
f ⦃ r => P r ⦄      becomes      ∃ r, f = .ok r ∧ P r
```

That lets us write `obtain ⟨r, hfeq, hP⟩ := spec_imp_exists (some_spec ...)` to grab (a) the
actual result value `r`, (b) the equation `hfeq : f = .ok r`, and (c) the property `hP`.

---

## Interlude — how the facts are named

The proof introduces a lot of hypotheses. **None of these names are Lean keywords** — they
are labels *we* chose, and Lean would accept any spelling. The conventions used here:

- An **`h` prefix means "hypothesis"** (a fact in hand). The rest describes what it's about.
- Every `obtain ⟨_, _, _⟩ := spec_imp_exists (..._spec ...)` destructures the **same triple
  in the same order**, so the three positions always play the same roles:

  | position | role | examples in this proof |
  |---|---|---|
  | 1st | the **value** the operation returned | `issuerTrusted`, `alreadyRegistered`, `registeredAfter` |
  | 2nd | the **equation** `operation = .ok value` (suffix `…Eq`) | `hIssuerTrustedEq`, `hContainsEq`, `hInsertEq` |
  | 3rd | the **property** of that value (suffix `…Iff` / `…Mem`) | `hIssuerTrustedIff`, `hContainsIff`, `hInsertMem` |

- A few names come from *other* destructurings: `hStateEq`/`_hEventEq` are the two halves of
  the decoded result (the leading `_` marks the event as deliberately unused), and
  `hRegRel`/`hTrustRel`/`hIssuerRel` are the three components of `Rtool`.
- `rfl` is **not** one of our names — it is a built-in proof, covered where it appears.

---

## Part 3 — `register_tool_ok_inv`, line by line

### The statement

```lean
theorem register_tool_ok_inv
    (st : state.KernelState) (bg : background.BackgroundTheory) (tool : types.ToolId)
    (hcap : st.tool_registered.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.register_tool st bg tool = .ok (.Ok (st', ev))) :
    ∃ toolMeta,
      bg.tool_metadata tool = .ok (some toolMeta) ∧
      vsMem bg.trusted_issuers toolMeta.issuer ∧
      ¬ vsMem st.tool_registered tool ∧
      ∀ y, vsMem st'.tool_registered y ↔ vsMem st.tool_registered y ∨ y = tool := by
```

- `theorem NAME (binders...) : STATEMENT := by` — declare a theorem. Each `(x : T)` is a
  **hypothesis/parameter** the theorem takes; they become available as facts inside the
  proof. Everything before the final `:` is input; the part after is the goal.
- `st`, `bg`, `tool` — the inputs the function is called on.
- `hcap : ... .length < Usize.max` — a **side condition**: the set isn't already at the
  maximum machine-integer size. The underlying `Vec.push` needs this so the length can't
  overflow. `Usize.max` is the largest `usize` value. (Conceptually: real states never get
  that big; the abstract set is unbounded so it has no counterpart constraint.)
- `st'`, `ev`, `hok` — the *claimed* result and the hypothesis that the call produced it.
- The conclusion after `:` is an **existential**: `∃ toolMeta, A ∧ B ∧ C ∧ D`.
  - `∃ toolMeta, ...` — "there exists some tool-metadata `toolMeta` such that ...". Recovering
    this hidden value is the heart of "inversion".
  - `A` = `bg.tool_metadata tool = .ok (some toolMeta)` — the lookup found metadata. (`.ok`
    layer-1 success; `some toolMeta` because a lookup returns an `Option`: `some x` = found,
    `none` = absent.)
  - `B` = `vsMem bg.trusted_issuers toolMeta.issuer` — that metadata's issuer is trusted.
  - `C` = `¬ vsMem st.tool_registered tool` — the tool wasn't already registered. (`¬` is
    "not".)
  - `D` = `∀ y, vsMem st'.tool_registered y ↔ vsMem st.tool_registered y ∨ y = tool` — the
    new set is exactly the old set plus `tool`.
- `:= by` — "the proof follows, in tactic mode".

> **Why these four facts?** They are precisely what the *simulation* theorem needs: B and C
> are the abstract action's preconditions, D is how the abstract state must change, and A
> ties `toolMeta` to the metadata. The inversion lemma's job is to mine them out of `hok`.

### Unfolding the function body

```lean
  simp only [transitions.register_tool] at hok
```

- `simp only [lemmas...] at h` — **simplify** hypothesis `h` using *only* the listed
  rewrite rules (as opposed to bare `simp`, which uses Lean's whole default rule set).
- Passing the *definition name* `transitions.register_tool` tells simp to **unfold** the
  function. After this, `hok` is no longer `register_tool ... = ...`; it's the function's
  actual *body* (a chain of `>>=` binds) `= .ok (.Ok (st', ev))`. Now we can dissect it.

### The flat shape

The function has four runtime gates (metadata present? issuer trusted? already registered?
plus the insert). Rather than nest a `cases` per gate — which builds an indentation staircase —
the proof handles each gate at the **same indentation level**: derive the single fact that says
"we're on the success path", rewrite `hok` forward past that gate, and move on. Two small idioms
carry the whole proof:

- `obtain ⟨x, hx⟩ : ∃ x, <fact> := by cases …` — extract the value and fact we need, dispatching
  the *impossible* shapes inside the `by` (they contradict `hok`). The outer proof never indents.
- `have hx : b = <val> := by cases b …` — for a boolean gate, pin the bool to its only possible
  value, again killing the dead case against `hok` locally.

### Gate 1: the metadata lookup succeeds

```lean
  obtain ⟨metaOpt, hMetaEq⟩ : ∃ o, bg.tool_metadata tool = .ok o := by
    cases h : bg.tool_metadata tool with
    | ok o => exact ⟨o, rfl⟩
    | fail e => rw [h] at hok; simp at hok
    | div => rw [h] at hok; simp at hok
  rw [hMetaEq] at hok
  simp only [bind_tc_ok] at hok
```

- We need just one thing from the lookup: that it returned `.ok` of *some* option `metaOpt`.
  `obtain ⟨metaOpt, hMetaEq⟩ : ∃ o, bg.tool_metadata tool = .ok o := by …` states exactly that
  as a tiny lemma and proves it on the spot:
  - `cases h : bg.tool_metadata tool with` — split the layer-1 `Result` (`ok`/`fail`/`div`),
    naming the equation `h`.
  - `| ok o => exact ⟨o, rfl⟩` — success: hand back the value `o`. (`cases h :` rewrote the
    sub-goal's `bg.tool_metadata tool` to `.ok o`, so the equation is just `rfl`.)
  - `| fail e =>` / `| div =>` — the **impossible** shapes: `rw [h] at hok` turns `hok` into
    `.fail e >>= … = .ok (.Ok …)` (resp. `.div`), and `simp at hok` derives the contradiction,
    closing that sub-goal. **All of this lives inside the `by`** — the outer proof stays flat.
- After the `obtain` we hold `metaOpt` and `hMetaEq : bg.tool_metadata tool = .ok metaOpt`.
- `rw [hMetaEq] at hok` rewrites the call in `hok` to `.ok metaOpt`; `simp only [bind_tc_ok] at
  hok` runs one bind step (`(.ok metaOpt) >>= f` ⇝ `f metaOpt`), advancing `hok` to the next gate.

> Because we keep `hMetaEq` as a **real equation** (instead of casing on the goal), conjunct A of
> the result is later discharged by `hMetaEq` directly — there's no surprising `rfl`. That's one
> small readability win of the flat shape over the nested version.

### Gate 2: the metadata is present (`some`)

```lean
  obtain ⟨toolMeta, rfl⟩ : ∃ tm, metaOpt = some tm := by
    cases metaOpt with
    | none => simp at hok
    | some tm => exact ⟨tm, rfl⟩
  simp only [issuerId_clone_spec, bind_tc_ok] at hok
```

- `obtain ⟨toolMeta, rfl⟩ : ∃ tm, metaOpt = some tm := by …` — extract that the option is
  `some toolMeta`. The `rfl` in the *pattern* is doing real work: the second component is the
  equation `metaOpt = some toolMeta`, and matching it against `rfl` **substitutes** `metaOpt :=
  some toolMeta` everywhere (including in `hok`). `toolMeta` is the existential witness the
  conclusion promised; the rest of the proof works with *this* metadata.
  - `| none => simp at hok` — no metadata ⇒ `register_tool` returns `.Err`, contradicting `hok`.
  - `| some tm => exact ⟨tm, rfl⟩` — the real case.
- `simp only [issuerId_clone_spec, bind_tc_ok] at hok` — `hok` now begins `match some toolMeta
  …`; simp reduces that match to the `some` branch, then `issuerId_clone_spec` erases the
  identity `.clone()` of the issuer and `bind_tc_ok` steps past it.

### Gate 3: the issuer is trusted

```lean
  obtain ⟨issuerTrusted, hIssuerTrustedEq, hIssuerTrustedIff⟩ :=
    spec_imp_exists (isTrustedIssuer_spec bg toolMeta.issuer)
  rw [hIssuerTrustedEq] at hok
  simp only [bind_tc_ok] at hok
  have hTrusted : issuerTrusted = true := by
    cases issuerTrusted with
    | true => rfl
    | false => simp at hok
  simp only [hTrusted, reduceIte] at hok
```

- `obtain ⟨issuerTrusted, hIssuerTrustedEq, hIssuerTrustedIff⟩ := spec_imp_exists (isTrustedIssuer_spec bg toolMeta.issuer)`
  — the `is_trusted_issuer` spec, repackaged into an existential and destructured by position:
  `issuerTrusted` (the bool returned), `hIssuerTrustedEq : is_trusted_issuer … = .ok
  issuerTrusted`, and `hIssuerTrustedIff : issuerTrusted = true ↔ vsMem bg.trusted_issuers
  toolMeta.issuer`. (`⟨…⟩` is the **anonymous constructor** — builds *or* takes apart a
  structure/tuple by position.)
- `rw [hIssuerTrustedEq] at hok; simp only [bind_tc_ok] at hok` — substitute the result into
  `hok` and step past the bind. Now `hok` contains `if issuerTrusted = true then … else .Err`.
- `have hTrusted : issuerTrusted = true := by cases issuerTrusted with | true => rfl | false =>
  simp at hok` — pin the bool. In the `true` case the goal is `true = true` (`rfl`); in the
  `false` case `hok` becomes `… else .Err = .Ok …`, which `simp` refutes. **The dead case is
  handled inside the `have`**, so the main line stays flat. (Note: a separate `have`, rather
  than `cases issuerTrusted` in the main flow, is exactly what avoids the staircase here.)
- `simp only [hTrusted, reduceIte] at hok` — rewrite `issuerTrusted` to `true`, then `reduceIte`
  (a simproc that evaluates decidable `if`s) takes the `then` branch, advancing past the gate.

### Gate 4: the tool is not already registered

```lean
  obtain ⟨alreadyRegistered, hContainsEq, hContainsIff⟩ :=
    spec_imp_exists (vecSetContains_spec types.ToolId.Insts.CoreCloneClone
      types.ToolId.Insts.CoreCmpPartialEqToolId toolId_eq_spec st.tool_registered tool)
  rw [hContainsEq] at hok
  simp only [bind_tc_ok] at hok
  have hNotReg : alreadyRegistered = false := by
    cases alreadyRegistered with
    | false => rfl
    | true => simp at hok
  simp only [hNotReg, reduceIte, Bool.false_eq_true] at hok
```

The same shape as Gate 3, mirrored (here the *live* case is `false`):

- `vecSetContains_spec …` is the proven triple for `VecSet.contains`. It takes three "instance"
  arguments describing how to clone/compare tool ids (`…CoreCloneClone`,
  `…CoreCmpPartialEqToolId`) plus `toolId_eq_spec` (comparison really decides equality) —
  bookkeeping the Rust→Lean translation needs; you thread them through. `spec_imp_exists` then
  gives `alreadyRegistered`, `hContainsEq`, and `hContainsIff : alreadyRegistered = true ↔ vsMem
  st.tool_registered tool`.
- `rw [hContainsEq] at hok; simp only [bind_tc_ok] at hok` — substitute and advance; now `hok`
  has `if alreadyRegistered = true then .Err else <continue>`.
- `have hNotReg : alreadyRegistered = false := by …` — pin the bool to `false` (the success
  path): `false` case is `rfl`; `true` case makes `hok` say `.Err = .Ok …`, refuted by `simp`.
- `simp only [hNotReg, reduceIte, Bool.false_eq_true] at hok` — rewrite to `false`, drop the
  `if` via `reduceIte` (`Bool.false_eq_true` lets it see `false = true` is `False`), continue.

### The insert, and reading off the result

```lean
  simp only [toolId_clone_spec, bind_tc_ok] at hok
  obtain ⟨registeredAfter, hInsertEq, hInsertMem⟩ :=
    spec_imp_exists (vecSetInsert_spec types.ToolId.Insts.CoreCloneClone
      types.ToolId.Insts.CoreCmpPartialEqToolId toolId_eq_spec st.tool_registered tool hcap)
  rw [hInsertEq] at hok
  simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok
  obtain ⟨hStateEq, _hEventEq⟩ := hok
```

We've passed every gate; `hok` is now on the straight-line success path.

- `simp only [toolId_clone_spec, bind_tc_ok] at hok` — erase another identity `.clone()` (of
  `tool` this time) and step forward.
- `obtain ⟨registeredAfter, hInsertEq, hInsertMem⟩ := spec_imp_exists (vecSetInsert_spec ... hcap)`
  — run the `insert` spec. It takes our side condition `hcap` (the capacity bound). We get:
  - `registeredAfter` — the **new** set after inserting `tool`,
  - `hInsertEq : VecSet.insert ... = .ok registeredAfter`,
  - `hInsertMem : ∀ y, vsMem registeredAfter y ↔ vsMem st.tool_registered y ∨ y = tool` — the
    precise "old set plus `tool`" characterisation. **This is conjunct D, almost verbatim.**
- `rw [hInsertEq] at hok` — substitute the insert's result into `hok`.
- `simp only [bind_tc_ok, Result.ok.injEq, core.result.Result.Ok.injEq, Prod.mk.injEq] at hok`
  — peel the final wrapper. (No `reduceIte`/`if_true` needed any more: the gates already
  collapsed both `if`s, so nothing remains but the success `.ok (.Ok (newState, event))`.)
  - `Result.ok.injEq` (layer 1), `core.result.Result.Ok.injEq` (layer 2) — **injectivity**:
    `.ok a = .ok b` reduces to `a = b`, cancelling the wrappers on both sides.
  - `Prod.mk.injEq` — a pair equality `(a, b) = (c, d)` splits into `a = c ∧ b = d`.
  - Net effect: `hok` becomes `st' = ⟨the updated state⟩ ∧ ev = ⟨the event⟩`.
- `obtain ⟨hStateEq, _hEventEq⟩ := hok` — split that conjunction. `hStateEq : st' = {st with
  tool_registered := registeredAfter}`. `_hEventEq` is the event equation; the leading
  underscore marks it **deliberately unused** (the `_` silences the "unused variable" warning).

### Delivering the four facts

```lean
  refine ⟨toolMeta, hMetaEq, hIssuerTrustedIff.mp hTrusted, ?_, ?_⟩
  · intro hmem
    have hc := hContainsIff.mpr hmem
    rw [hNotReg] at hc
    exact Bool.false_ne_true hc
  · subst hStateEq
    exact hInsertMem
```

- `refine TERM` — supply the proof *term* for the goal, leaving **holes** written `?_` for
  sub-proofs you'll provide afterwards. The goal is `∃ toolMeta, A ∧ B ∧ C ∧ D`; the anonymous
  constructor `⟨…⟩` provides the witness then a proof of each conjunct. Here we provide A and B
  inline and defer C and D to two `·` bullets.
  - `toolMeta` — the existential witness (the metadata we found).
  - `hMetaEq` — conjunct **A** (`bg.tool_metadata tool = .ok (some toolMeta)`), *exactly* the
    equation Gate 1 kept (after Gate 2 substituted `metaOpt := some toolMeta`). No `rfl` trick —
    the flat shape lets us hand the real equation straight back.
  - `hIssuerTrustedIff.mp hTrusted` — conjunct **B** (`vsMem bg.trusted_issuers toolMeta.issuer`).
    `hIssuerTrustedIff : issuerTrusted = true ↔ vsMem …`; its `.mp` ("modus ponens", forward `→`)
    direction applied to `hTrusted : issuerTrusted = true` yields the membership fact.
- First `·` bullet — conjunct **C** (`¬ vsMem st.tool_registered tool`). Recall `¬ P` is `P →
  False`, so `intro hmem` assumes `hmem : vsMem st.tool_registered tool` and we derive `False`:
  - `have hc := hContainsIff.mpr hmem` — `.mpr` (reverse `←`) gives `hc : alreadyRegistered = true`.
  - `rw [hNotReg] at hc` — rewrite using `hNotReg : alreadyRegistered = false`, so `hc : false = true`.
  - `exact Bool.false_ne_true hc` — `Bool.false_ne_true : false ≠ true` (i.e. `false = true →
    False`) turns `hc` into the `False` we owe.
- Second `·` bullet — conjunct **D**.
  - `subst hStateEq` — `hStateEq : st' = {st with tool_registered := registeredAfter}`; `subst`
    eliminates `st'`, replacing it everywhere by that record update.
  - `exact hInsertMem` — the goal is now `∀ y, vsMem {st with tool_registered :=
    registeredAfter}.tool_registered y ↔ …`. Reading `.tool_registered` off a record that set it
    to `registeredAfter` *gives back* `registeredAfter`, so the goal is definitionally equal to
    `∀ y, vsMem registeredAfter y ↔ …`, which is exactly `hInsertMem`. Proof complete.

---

## Part 4 — `register_tool_refines`, line by line

### The statement

```lean
theorem register_tool_refines
    (st : state.KernelState) (bg : background.BackgroundTheory)
    (a : AbsState) (tool : types.ToolId)
    (hR : Rtool st bg a)
    (hcap : st.tool_registered.items.val.length < Usize.max)
    (st' : state.KernelState) (ev : event.KernelAction)
    (hok : transitions.register_tool st bg tool = .ok (.Ok (st', ev))) :
    ∃ a', (Tzimtzum.register_tool tool).guard a ∧
          (Tzimtzum.register_tool tool).next a a' ∧ Rtool st' bg a' := by
```

Same inputs as before, plus the abstract state `a` and the hypothesis `hR : Rtool st bg a`
(the states *start out* related). The conclusion is the commuting square's promise:

- `∃ a', ...` — there exists an abstract post-state `a'` such that:
  - `(Tzimtzum.register_tool tool).guard a` — the abstract action is **enabled** in `a` (its
    precondition / "guard" holds). An action in the spec is a record bundling a `guard` (when
    it may fire) and a `next` (the state relation it induces); `.guard`/`.next` project those
    out.
  - `(Tzimtzum.register_tool tool).next a a'` — taking the abstract action from `a` lands in
    `a'`.
  - `Rtool st' bg a'` — and the post-states are **still related**.

### Gathering the ingredients

```lean
  obtain ⟨hRegRel, hTrustRel, hIssuerRel⟩ := hR
  obtain ⟨toolMeta, hMeta, hIssuerTrusted, hNotRegistered, hNewReg⟩ :=
    register_tool_ok_inv st bg tool hcap st' ev hok
```

- `obtain ⟨hRegRel, hTrustRel, hIssuerRel⟩ := hR` — `Rtool` is a triple conjunction, so
  destructure it into its three parts: `hRegRel` (tool-registered correspondence), `hTrustRel`
  (trusted-issuer correspondence), `hIssuerRel` (tool-issuer agreement). (`A ∧ B ∧ C` nests as
  `A ∧ (B ∧ C)`; the `⟨_, _, _⟩` pattern flattens that automatically.)
- `obtain ⟨toolMeta, hMeta, hIssuerTrusted, hNotRegistered, hNewReg⟩ := register_tool_ok_inv st bg tool hcap st' ev hok`
  — **here is the payoff of splitting the proof**: we *call* the inversion lemma like a
  function, passing all its arguments, and destructure the `∃ toolMeta, A ∧ B ∧ C ∧ D` it
  returns. We now have, for free: `toolMeta`, `hMeta` (=A), `hIssuerTrusted` (=B),
  `hNotRegistered` (=C), `hNewReg` (=D). All the monad-bashing lives in the other lemma.

### Choosing the abstract post-state

```lean
  refine ⟨{a with tool_registered := fun T => a.tool_registered T ∨ T = tool}, ?_, ?_, ?_⟩
```

- We must supply the existential witness `a'` and then prove the three conjuncts.
- `{a with tool_registered := fun T => a.tool_registered T ∨ T = tool}` — **record-update
  syntax**: "the state `a`, but with its `tool_registered` field replaced". The new field is
  the predicate "`T` was already registered in `a`, **or** `T` is the tool we just added".
  That's the abstract mirror of "old set plus `tool`".
- The three `?_` are holes for **guard**, **next**, and **Rtool**, proved in the three
  bullet blocks below.

### Bullet 1 — the guard

```lean
  · -- guard
    simp only [Tzimtzum.register_tool]
    refine ⟨?_, ?_⟩
    · rw [hRegRel]; exact hNotRegistered
    · rw [hIssuerRel tool toolMeta hMeta, hTrustRel]; exact hIssuerTrusted
```

- `·` (a centred dot, "cdot") — **focus** on the first remaining goal. It's how you tackle
  the `?_` holes one at a time; everything indented under a `·` must fully close that one
  goal. The `-- guard` is just a comment.
- `simp only [Tzimtzum.register_tool]` — unfold the action definition so `.guard a` becomes
  the concrete proposition it stands for. For `register_tool` that guard is a **conjunction**
  of two preconditions: "tool not already registered" **and** "the tool's issuer is trusted".
- `refine ⟨?_, ?_⟩` — split that conjunction into two sub-goals (two more `·` bullets).
  - `· rw [hRegRel]; exact hNotRegistered` — first precondition is `¬ a.tool_registered tool`
    (abstract "not registered"). `hRegRel` is `∀ t, a.tool_registered t ↔ vsMem
    st.tool_registered t`; `rw [hRegRel]` rewrites the goal's `a.tool_registered tool` into
    the concrete `vsMem st.tool_registered tool`. (`rw` can rewrite with an `↔` because, under
    propositions-as-types, an iff *is* an equality of propositions.) The goal becomes `¬ vsMem
    st.tool_registered tool`, which is exactly `hNotRegistered`; `exact` closes it.
  - `· rw [hIssuerRel tool toolMeta hMeta, hTrustRel]; exact hIssuerTrusted` — second
    precondition is "the issuer of `tool` is trusted", abstractly `a.trusted_issuer
    (a.tool_issuer tool)`. We rewrite in two steps (`rw [l1, l2]` applies `l1` then `l2`):
    - `hIssuerRel tool toolMeta hMeta : a.tool_issuer tool = toolMeta.issuer` — instantiate
      `hIssuerRel` at our tool/metadata and the fact `hMeta` that the metadata is what the
      lookup returned. Rewrite turns `a.tool_issuer tool` into `toolMeta.issuer`.
    - `hTrustRel : ∀ i, a.trusted_issuer i ↔ vsMem bg.trusted_issuers i` — rewrite the
      remaining `a.trusted_issuer toolMeta.issuer` into `vsMem bg.trusted_issuers
      toolMeta.issuer`.
    - The goal is now exactly `hIssuerTrusted`; `exact` closes it.

### Bullet 2 — the next-state relation

```lean
  · -- next
    simp [Tzimtzum.register_tool]
```

- The goal is `(Tzimtzum.register_tool tool).next a a'`, i.e. "the abstract action relates
  `a` to our chosen `a'`". Because we *picked* `a'` to be precisely the update the action
  performs, this is true essentially by definition.
- `simp [Tzimtzum.register_tool]` — here we use **full `simp`** (not `simp only`): unfold the
  action and let simp's default rules verify that `a'` matches what `next` requires (the
  field updates line up, the untouched fields are unchanged). simp closes the goal.

### Bullet 3 — the relation is preserved

```lean
  · -- Rtool st' bg a'
    refine ⟨fun t => ?_, hTrustRel, hIssuerRel⟩
    have hPost := hNewReg t
    have hReg := hRegRel t
    simp only [vsMem] at hReg hPost ⊢
    grind
```

The goal is `Rtool st' bg a'`, another triple conjunction. Look at its three parts:

1. `∀ t, a'.tool_registered t ↔ vsMem st'.tool_registered t` — **changed**, needs work.
2. `∀ i, a'.trusted_issuer i ↔ vsMem bg.trusted_issuers i` — but `a'` only changed its
   `tool_registered` field, so `a'.trusted_issuer` *is* `a.trusted_issuer`, and `bg` didn't
   change. So this is **identical to `hTrustRel`**.
3. `∀ t tm, ... → a'.tool_issuer t = tm.issuer` — likewise `a'.tool_issuer = a.tool_issuer`,
   so this is **identical to `hIssuerRel`**.

- `refine ⟨fun t => ?_, hTrustRel, hIssuerRel⟩` — supply the three parts: reuse `hTrustRel`
  and `hIssuerRel` verbatim for parts 2 and 3, and for part 1 provide `fun t => ?_` (a
  function: "given an arbitrary `t`, here's a proof for that `t`", with the body deferred as a
  hole).
- `have NAME := TERM` — introduce a new named hypothesis. We specialise the two relevant
  facts to *this* `t`:
  - `have hPost := hNewReg t` — `hPost : vsMem st'.tool_registered t ↔ vsMem st.tool_registered
    t ∨ t = tool` (conjunct D from the inversion lemma, at `t`).
  - `have hReg := hRegRel t` — `hReg : a.tool_registered t ↔ vsMem st.tool_registered t` (the
    starting correspondence, at `t`).
- `simp only [vsMem] at hReg hPost ⊢` — unfold the `vsMem` abbreviation in both hypotheses
  **and** the goal. `⊢` (the turnstile) means "apply this to the goal too". This also
  β-reduces the goal's `(fun T => a.tool_registered T ∨ T = tool) t` down to `a.tool_registered
  t ∨ t = tool`. After this everything is stated in the same vocabulary (list membership).
- `grind` — a powerful **finishing tactic** that combines simplification, case-splitting and
  congruence/equality reasoning. The remaining goal is pure propositional logic:
  ```
  (a.tool_registered t ∨ t = tool) ↔ vsMem st'.tool_registered t
  ```
  given `hReg` and `hPost`. Chaining the two equivalences makes both sides equal, and `grind`
  finds that automatically. Goal closed; the whole theorem is proved.

---

## Part 5 — The trust audit

```lean
#print axioms ArgusLean.Refinement.register_tool_ok_inv
#print axioms ArgusLean.Refinement.register_tool_refines
```

- `#print axioms NAME` is a **command** (the `#` prefix marks a query that runs at compile
  time and prints to the build log; it doesn't affect the proof). It lists *every axiom the
  proof transitively relies on* — its **trusted computing base (TCB)**.
- For both theorems the output is:
  - `propext`, `Classical.choice`, `Quot.sound` — Lean's three **standard** axioms (classical
    logic + quotients). Every normal mathlib proof uses these; they're trusted by everyone.
  - `string_eq_spec`, `string_clone_spec` and the matching `...String.eq` / `...String.clone`
    / `...ne` entries — the **documented residual** from the translation. Rust's `String` is a
    built-in with no source body for Aeneas to translate, so its equality/clone come in as
    bare axioms pinned to "faithful equality / identity". This is the only thing these proofs
    add beyond the standard axioms, and it's the same "trust the extractor for `String`"
    assumption recorded in `Collections.lean`.
- Crucially: **no `sorryAx`** (which would mean an unfinished `sorry`) and **no SMT solver**
  in the list — the proofs are checked by Lean's kernel alone. That clean audit is the actual
  deliverable of the refinement spike.

---

## Appendix — tactic & symbol cheat-sheet

| Symbol / keyword | Meaning |
|---|---|
| `∀ x, P` | for all `x`, `P` holds |
| `∃ x, P` | there exists `x` such that `P` |
| `P ∧ Q` / `P ∨ Q` | and / or |
| `P → Q` | implies; also the type of functions |
| `P ↔ Q` | if and only if; `.mp` is `→`, `.mpr` is `←` |
| `¬ P` | not `P`; *defined as* `P → False` |
| `⊢` | the turnstile — "the goal is ..." |
| `⟨ ... ⟩` | anonymous constructor — build/destructure a structure or tuple by position |
| `?_` | a named hole / deferred sub-goal |
| `·` | focus on (and fully discharge) the current goal |
| `{r with f := v}` | record update — `r` but with field `f` set to `v` |
| `fun x => e` | anonymous function (lambda) |
| `.ok` / `.fail` / `.div` | Aeneas `Result` (layer 1: success / panic / divergence) |
| `.Ok` / `.Err` | Rust's `Result` (layer 2: function success / error) |
| `some x` / `none` | `Option` — value present / absent |
| `x >>= f` | monadic bind — run `x`, feed its result to `f` |

| Tactic | What it does |
|---|---|
| `by` | enter tactic mode |
| `intro` / `fun x => ?_` | introduce a `∀`/`→` hypothesis (here via lambda) |
| `cases e with \| c => ..` | split into one branch per constructor of `e` |
| `cases h : e with ..` | same, but also names the per-branch equation `h` |
| `obtain ⟨..⟩ := e` | destructure `e` (existential / conjunction / structure) |
| `refine t` | give the proof term `t`, leaving `?_` holes to prove later |
| `exact t` | give a proof term that matches the goal exactly |
| `rw [h]` (`at hyp`) | rewrite using equation/iff `h`, in the goal (or in `hyp`) |
| `simp only [..]` (`at ..`) | simplify using *only* the listed lemmas |
| `simp` | simplify using the full default rule set (closes `False` hyps) |
| `subst h` | eliminate a variable using equation `h` |
| `have n := t` | add a named intermediate fact |
| `grind` | strong finisher: simp + case-split + congruence/equality |
| `rfl` | prove `x = x` |
| `;` | run the next tactic on the result of the previous |
| `#print axioms n` | list the trusted axioms a proof depends on |

---

## A note on the hypothesis names

The names in this proof (`hMetaEq`, `issuerTrusted`, `hContainsIff`, `registeredAfter`,
`hStateEq`, `hRegRel`, ...) are **chosen for readability, not required by Lean**. They follow
the convention in the *Interlude* above, and the same scheme is meant to be reused for the
other 11 transitions (the C2 fan-out): each per-action inversion lemma destructures its
operation specs into `value` / `…Eq` / `…Iff`-or-`…Mem` triples, and each simulation
destructures the relation into `…Rel` components. Keeping the roles in the names is what lets
you read a new transition's proof without re-deriving what every `h…` stands for.
