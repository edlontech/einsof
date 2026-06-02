import ArgusLean.Refinement.Collections
import Plausible

/-! # Plausible harness — vet candidate bridging clauses before proving them

A property-testing scratchpad for the C2 refinement fan-out. It exercises the **real** pure
bridging definitions from `Collections.lean` (`vmLastEntry`, `removeKept`) at a small finite
key/value type (`Fin 3`), so a candidate `R`-field clause can be falsified in milliseconds
before any `grind` time is spent on it.

Scope: this tests the **abstraction layer** only — the list-level meaning of the Vec-backed
collections. The Aeneas `Result`-monad / loop layer is separately discharged by the `…_spec`
lemmas, so every open "is this clause even true" question lives here, at the list level.

The headline result reproduces, mechanically, the documented reason `delegate`'s
`agent_parent` field is deferred to the unified `R`: the get-style (last-match) bridging clause
disagrees with the abstract post-image under duplicate keys, and agrees once a key-uniqueness
invariant is assumed.

Not part of the default build. Run explicitly:
  lake env lean ArgusLean/Refinement/PlausibleChecks.lean
-/

namespace ArgusLean.Refinement.PlausibleChecks

open ArgusLean.Refinement
open Plausible

/-- Deterministic, reproducible config: fixed seed, many small instances. -/
def cfg : Configuration := { randomSeed := some 42, numInst := 1000, maxSize := 6 }

/-! ## Faithful list models of the `delegate` `agent_parent` rewrite

`agent_parent` is a `VecMap AgentId AgentId`; the extracted rewrite is
`agent_parent_drop_endpoint st.agent_parent grantee` followed by `VecMap.insert grantee grantor`.
We model the two pure list operations exactly as the extracted code computes them. -/

/-- Last-match insert: overwrite the *last* entry whose key matches, else append. Mirrors
    `VecMap.insert` (characterised by `vmLastEntry_set_lastmatch` / `vmLastEntry_append_nomatch`). -/
def insertLast {K V : Type} [DecidableEq K] : List (K × V) → K → V → List (K × V)
  | [], k, v => [(k, v)]
  | (k', v') :: rest, k, v =>
      if k' = k ∧ ∀ p ∈ rest, p.1 ≠ k then (k, v) :: rest
      else (k', v') :: insertLast rest k v

/-- `agent_parent_drop_endpoint`: rebuild the map entry-by-entry via last-match insert, keeping
    only entries where neither the child (key) nor the parent (value) is the dropped agent. -/
def dropEndpoint {K : Type} [DecidableEq K] (l : List (K × K)) (d : K) : List (K × K) :=
  l.foldl (fun kept p => if p.1 ≠ d ∧ p.2 ≠ d then insertLast kept p.1 p.2 else kept) []

/-- Concrete post-state list for `agent_parent` after `delegate grantor grantee`. -/
def parentPost {K : Type} [DecidableEq K] (l : List (K × K)) (grantee grantor : K) : List (K × K) :=
  insertLast (dropEndpoint l grantee) grantee grantor

/-- Candidate get-style abstract relation read off a concrete list: `C`'s parent is `P` iff the
    *last* `C`-keyed entry holds `P`. (Uses the real `vmLastEntry`.) `abbrev` so `Decidable`
    instance search sees through it. -/
abbrev absParent {K : Type} [DecidableEq K] (l : List (K × K)) (C P : K) : Prop :=
  vmLastEntry l C = some (C, P)

/-- Abstract post-image from `Tzimtzum.delegate`'s `next` clause for `agent_parent`. -/
abbrev absPost {K : Type} [DecidableEq K] (l : List (K × K)) (grantee grantor C P : K) : Prop :=
  (C = grantee ∧ P = grantor) ∨ (absParent l C P ∧ C ≠ grantee ∧ P ≠ grantee)

/-- Concrete post-image read with the same get-style relation. -/
abbrev concPost {K : Type} [DecidableEq K] (l : List (K × K)) (grantee grantor C P : K) : Prop :=
  absParent (parentPost l grantee grantor) C P

/-! ## Checks

Each iff is phrased as a `Bool` equation `decide _ = decide _` rather than a raw `↔`. Plausible
prefers `iffTestable`, which *structurally decomposes* a `↔` into `(p∧q)∨(¬p∧¬q)` and recurses;
for `∨`/`∧`-shaped bodies that decomposition blows up instance search. The `decide` form keeps the
body a single decidable `Bool` equation, so `decidableTestable` fires once at the top. -/

-- Check 1 — positive control: a clause that IS proven (`mem_filter_removeKept`). Expect no
-- counter-example, confirming the harness reports cleanly on true statements.
#eval Testable.check (cfg := cfg)
  (∀ (l : List (Fin 3 × Fin 3)) (key k v : Fin 3),
    decide ((k, v) ∈ l.filter (removeKept key)) = decide ((k, v) ∈ l ∧ k ≠ key))

-- Check 2 — the deferred `agent_parent` clause, UNGUARDED. Expect a counter-example of the
-- documented shape `[(C, X), (C, grantee)]`: the entry-wise drop+rebuild keeps the earlier
-- `(C, X)`, while the get-style abstract pre-image only saw `(C, grantee)` and then dropped it.
#eval Testable.check (cfg := cfg)
  (∀ (l : List (Fin 3 × Fin 3)) (grantee grantor C P : Fin 3),
    decide (absPost l grantee grantor C P) = decide (concPost l grantee grantor C P))

-- Check 3 — the same clause GUARDED by key-uniqueness (the invariant the unified `R` will
-- carry). Expect no counter-example, confirming uniqueness is the right and sufficient fix.
#eval Testable.check (cfg := cfg)
  (∀ (l : List (Fin 3 × Fin 3)) (grantee grantor C P : Fin 3),
    (l.map Prod.fst).Nodup →
      decide (absPost l grantee grantor C P) = decide (concPost l grantee grantor C P))

end ArgusLean.Refinement.PlausibleChecks
