# Tzimtzum: the TzimtzumV2 authorization protocol

The formally verified TzimtzumV2 protocol; the source of truth for Einsof's authorization
state machine. It is a pure-Lean specification built on the [Kav](../kav/) transition-system
framework (this project `require`s `kav` as a library). The discharge engine is
kernel-checked mathlib automation.

For a plain-language walkthrough of what the proofs show, why that's useful, and where
the guarantee stops, see [PROOFS.md](PROOFS.md).

## The verified protocol

The full protocol is 13 actions, 9 safety properties, and 14 strengthening invariants,
proved inductive over all transitions:

- 322 VCs discharged: 23 initiation VCs (`#kav_check_init`) plus 13 × 23 preservation VCs
  (`#kav_check_action`), one per (action, invariant) pair.
- All kernel-checked: the automation cascade uses only mathlib tactics (`grind`, `simp_all`,
  `auto`, `duper`).
- Six budget-meter VCs proved by hand: `active_has_budget` under `invoke_complete`,
  `return_endorsed`, `grant_override`, and `sentinel_credit_budget`, plus `budget_unique`
  and `budget_bounded` under `sentinel_credit_budget`. The debit and saturating-credit
  branches introduce an existential witness the cascade cannot reconstruct; these live in
  the matching `Tzimtzum/Check*.lean` modules.

### Soundness bundle

The per-action VCs are assembled into a single reachability theorem via the
protocol-independent `Kav.reachable_sound` meta-induction:

```
Tzimtzum.kav_sound : ∀ s, Kav.Reachable ksystem s → allInv s
```

Every reachable state satisfies the full invariant bundle. `kav_soundP` is the same result
over an arbitrary sort instantiation; `kav_sound` is its specialization to the opaque
`KSt`. Both live under `Tzimtzum/Soundness/`.

### Axiom audit

`#print axioms` on the audited theorems (see `Tzimtzum/Audit.lean`) confirms that every
proof depends only on the three standard Lean kernel axioms:

```
[propext, Classical.choice, Quot.sound]
```

No `sorryAx` or `native_decide` axiom appears.

Audited theorems:
- `audit_flow_confinement`: flow confinement preserved by `invoke_start`.
- `audit_override_consumed`: single-use override invariant preserved by `invoke_start`.
- `audit_init_flow_confinement`: flow confinement holds in the initial state.
- `return_endorsed_pres_active_has_budget`: the manual `active_has_budget` proof.

## Building and running the check suite

```bash
cd tzimtzum/
make build         # lake build Tzimtzum: spec only (no check modules)
make verify        # lake build Tzimtzum TzimtzumTest: all VCs + manual proofs + soundness + audit
```

The `#kav_check_action` commands emit PASS/FAIL tables to the info log. A successful
`lake build TzimtzumTest` means all VCs passed, the soundness bundle assembled, and the
axiom audit is clean.

Toolchain: Lean 4.30.0 + mathlib v4.30.0 (via the Kav dependency). After a toolchain
change, run `lake exe cache get` before building, or mathlib rebuilds from source.

## Scope and limitations

What the VCs prove: the invariant bundle is inductive. For each action and each invariant,
if the bundle holds before the action it holds after; and the bundle holds in every initial
state. `kav_sound` then closes this into `∀ s, Reachable s → allInv s`.

Refinement: this project verifies the abstract TzimtzumV2 specification. The connection to
the Rust kernel (`argus-kernel`) is a separate, completed layer: the kernel is mechanically
extracted to Lean via Aeneas/Charon and refined against this spec in
[`argus/formal-lean/`](../argus/formal-lean/), where `implementation_sound` proves the
extracted model refines a safe abstract state (modulo the trusted extractor and two
explicit assumptions).

## File layout

```
tzimtzum/
  lakefile.toml              requires ../kav; Tzimtzum + TzimtzumTest targets
  lean-toolchain             v4.30.0
  Tzimtzum.lean              spec root (State/Actions/Invariants/OpaqueTypes)
  TzimtzumTest.lean          aggregator: per-action VC checks + soundness + audit
  Tzimtzum/
    OpaqueTypes.lean         shared opaque sorts (KAgent, KTool, ..., KSt)
    State.lean               St structure, ConfLevel/BudgetLevel, initial predicate
    Actions.lean             13 kav_action definitions
    Invariants.lean          23 invariant/safety predicates + allInvariants bundle
    Check*.lean              per-action #kav_check_action modules (13 files) + CheckInit
    CheckInit.lean           #kav_check_init (23 initiation VCs)
    Soundness.lean           kav_sound aggregator (over Soundness/)
    Soundness/               reachability bundle (Common, PresMost, per-budget-action Pres, Bundle)
    Audit.lean               audited named theorems + #print axioms
```
