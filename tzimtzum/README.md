# Tzimtzum — the TzimtzumV2 authorization protocol

The formally verified TzimtzumV2 protocol: the source of truth for Einsof's
authorization state machine.  It is a pure-Lean specification built on the
[Kav](../kav/) transition-system framework (this project `require`s `kav` as a
library); the discharge engine is kernel-checked mathlib automation, with **no SMT
solver in the trust base** (the replacement for the earlier Veil/cvc5 spec).

## TzimtzumV2 at parity

The full protocol — **12 actions, 10 safety properties, 15 strengthening
invariants** — is ported and verified inductive over all transitions:

- **325 VCs discharged**: 25 initiation VCs (`#kav_check_init`) + 12 × 25 preservation
  VCs (`#kav_check_action`), one per (action, invariant) pair.
- **All kernel-checked**: the automation cascade uses only mathlib tactics (`grind`,
  `simp_all`, `auto`, `duper`).  No SMT solver or `native_decide` in the proof.
- **2 VCs via explicit manual proofs**: `active_has_budget` under `return_endorsed`
  and `invoke_complete` requires an existential witness that the cascade cannot
  reconstruct; these are proved by hand in `Tzimtzum/CheckReturnEndorsed.lean` and
  `Tzimtzum/CheckInvokeComplete.lean`.

### Axiom audit

`#print axioms` on the crown-jewel theorems (see `Tzimtzum/Audit.lean`) confirms
that every proof depends ONLY on the three standard Lean kernel axioms:

```
[propext, Classical.choice, Quot.sound]
```

No `sorryAx`, `Lean.ofReduceBool`, `native_decide`, or solver axiom appears. This is
the key trust advantage over Veil's default (which outsources proof obligations to
cvc5/SMT).

Named theorems audited:
- `audit_flow_confinement` — flow confinement preserved by `invoke_start`
- `audit_taint_integrity` — taint integrity preserved by `invoke_start` (cleaner:
  `[propext, Quot.sound]` only)
- `audit_override_consumed` — single-use override invariant preserved by `invoke_start`
- `audit_init_flow_confinement` — flow confinement holds in the initial state
- `return_endorsed_pres_active_has_budget` — manual `active_has_budget` proof

## Building and running the check suite

```bash
cd tzimtzum/
make build         # lake build Tzimtzum     — spec only (no check modules)
make verify        # lake build Tzimtzum TzimtzumTest — all 325 VCs + manual proofs + audit
```

The `#kav_check_action` commands emit PASS/FAIL tables to the info log. A successful
`lake build TzimtzumTest` means all 325 VCs passed and the axiom audit is clean.

**Toolchain**: Lean 4.30.0 + mathlib v4.30.0 (via the Kav dependency).

## Scope and honest limitations

**What the 325 VCs prove**: the invariant bundle is inductive — for each action and
each invariant, if the bundle holds before the action, it holds after; and the bundle
holds in every initial state.  This is the same content as Veil's `#check_invariants`.

**What is NOT yet assembled**: a single named `∀ s, reachable s → safety s` soundness
theorem.  This is a mechanical meta-induction over the 325 VCs (a one-time lemma
parameterised over the bundle and the transition system), and is noted as the next
step.  The VCs are the substance; the bundling lemma is bookkeeping.

**Refinement**: this project verifies the abstract TzimtzumV2 specification.  The
connection to the Rust kernel (`argus-kernel`) via Aeneas extraction is a separate
follow-on (the Aeneas spike on branch `feat/aeneas-phase0-spike` de-risked the stack).

## File layout

```
tzimtzum/
  lakefile.toml              -- requires ../kav; Tzimtzum + TzimtzumTest targets
  lean-toolchain             -- v4.30.0
  Tzimtzum.lean              -- spec root (State/Actions/Invariants/OpaqueTypes)
  TzimtzumTest.lean          -- aggregator: per-action VC checks + audit
  Tzimtzum/
    OpaqueTypes.lean         -- Shared opaque sorts (KAgent, KTool, ..., KSt)
    State.lean               -- St structure, ConfLevel/BudgetLevel, initial predicate
    Actions.lean             -- 12 kav_action definitions
    Invariants.lean          -- 25 invariant/safety predicates + allInvariants bundle
    Check*.lean              -- Per-action #kav_check_action modules (12 files)
    CheckInit.lean           -- #kav_check_init (25 initiation VCs)
    Audit.lean               -- Crown-jewel named theorems + #print axioms
```
