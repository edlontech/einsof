# Tzimtzum: the TzimtzumV2 authorization protocol

The formally verified TzimtzumV2 protocol; the source of truth for Einsof's authorization
state machine. It is a pure-Lean specification built on the [Kav](../kav/) transition-system
framework (this project `require`s `kav` as a library). The discharge engine is
kernel-checked mathlib automation.

For a plain-language walkthrough of what the proofs show, why that's useful, and where
the guarantee stops, see [PROOFS.md](PROOFS.md).

## The verified protocol

The full protocol is 16 actions, 11 safety properties, and 15 strengthening invariants
(26 total), proved inductive over all transitions. `ConfLevel` (confidentiality, rises as
an agent reads secret data) and `IntegLevel` (integrity, falls as an agent ingests
untrusted content) are dual 4-point lattices; the invoke gate checks both (CHECK 1-3 flow
+ authorizer, CHECK 4 integrity), and a single unified crossing guard (`crossing_ok`)
clears both dimensions with one conformance verdict at both declassification sites
(`invoke_complete_endorsed`, `return_endorsed`):

- 442 VCs discharged: 26 initiation VCs (`#kav_check_init`) plus 16 × 26 preservation VCs
  (`#kav_check_action`), one per (action, invariant) pair. Some actions split their 26 VCs
  across several `#kav_check_action` calls (invariant-name filters) purely for
  automation-search stability, not to change the total.
- All kernel-checked: the automation cascade uses only mathlib tactics (`grind`, `simp_all`,
  `auto`, `duper`).
- The declassification budget is a total function field (`agent_budget : AgentId → Nat`),
  updated by classical `ite` point-updates in every action that debits or credits it.
  `delegate` spawns the child's budget at 0 (delegation mints nothing);
  `sentinel_credit_budget` is the only faucet. Debits are weighted, not flat: the unified
  crossing's `crossing_weight` (dimension-adjusted: pays `declass_weight` only if the conf
  insert is new, `integ_weight` only if the integ drop is real), `return_endorsed`'s
  `declass_weight clvl + integ_weight ilvl` (level-parameterized, coverage-guarded), and
  `grant_override`'s `declass_weight lvl`.
- Six VCs proved by hand: `revocation_clean` under `delegate`, `invoke_complete_endorsed`,
  `return_endorsed`, `grant_override`, and `sentinel_credit_budget` (the classical `ite`
  inside the untouched `agent_budget` conjunct stalls the shared cascade for this one
  invariant, even though its own logic never touches the budget), plus `budget_bounded`
  under `sentinel_credit_budget` (the saturating credit's `≤ budget_capacity` bound is
  hidden behind an `@[irreducible]` helper). These live in the matching
  `Tzimtzum/Check*.lean` modules.
- New since the integrity-taint campaign: `unregister_tool` (tool lifecycle -- a
  compromised tool can leave the authorization surface), `sentinel_degrade_integrity`
  (platform-reported ingestion at an integrity level, gated against in-flight tools'
  floors), and `invoke_complete` split into `invoke_complete_endorsed` /
  `invoke_complete_unendorsed` (complementary total guards over `crossing_ok`, so each
  branch of the Rust kernel's `if/else` refines exactly one spec action).
- Oracle verdicts (`invocation_conforms`, `invocation_authorized`, `invocation_gate_passes`,
  `invocation_egress`) are keyed per invocation, not per static (agent, tool) pair, with a
  freshness guard (`invocation_used`) closing invocation-id replay.

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
- `return_endorsed_pres_revocation_clean`: one of the five manual `revocation_clean`
  proofs, re-audited here for visibility.
- `audit_integrity_confinement`: the headline injection-containment guarantee --
  integrity confinement preserved by `invoke_start` (CHECK 4a/4b/4c).
- `audit_crossing_endorsed`: the unified crossing's defining property -- an endorsed
  completion (`invoke_complete_endorsed`) never inserts taint or integrity.

## Building and running the check suite

```bash
cd tzimtzum/
make build         # lake build Tzimtzum: spec only (no check modules)
make verify        # lake build Tzimtzum TzimtzumTest: all VCs + manual proofs + soundness + audit
```

The `#kav_check_action` commands emit PASS/FAIL tables to the info log. A successful
`lake build TzimtzumTest` means all VCs passed, the soundness bundle assembled, and the
axiom audit is clean.

Toolchain: Lean 4.32.1 + mathlib v4.32.1 (via the Kav dependency). After a toolchain
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
  lean-toolchain             v4.32.1
  Tzimtzum.lean              spec root (State/Actions/Invariants/OpaqueTypes)
  TzimtzumTest.lean          aggregator: per-action VC checks + soundness + audit
  Tzimtzum/
    OpaqueTypes.lean         shared opaque sorts (KAgent, KTool, ..., KSt)
    State.lean               St structure, ConfLevel/IntegLevel, initial predicate
    Actions.lean             16 kav_action definitions
    Invariants.lean          26 invariant/safety predicates + allInvariants bundle
    Check*.lean              per-action #kav_check_action modules (16 files) + CheckInit
    CheckInit.lean           #kav_check_init (26 initiation VCs)
    Soundness.lean           kav_sound aggregator (over Soundness/)
    Soundness/               reachability bundle (Common, PresMost, per-budget-action Pres, Bundle)
    Audit.lean               audited named theorems + #print axioms
    BudgetConservation.lean  budget_monotone_except_credit per-action lemmas
```
