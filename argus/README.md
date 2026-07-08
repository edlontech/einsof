# Argus

> Work in progress.

`argus-kernel` is the pure-functional security kernel implementing the
[TzimtzumV3](../tzimtzum/) authorization protocol. It enforces data-flow policy at tool
invocation boundaries to prevent exfiltration via indirect prompt injection (the Lethal
Trifecta), and a dual integrity lattice to prevent ingested-untrusted-content from driving
destructive tools.

## argus-kernel

Pure functional state machine implementing the TzimtzumV3 transitions (16 spec actions;
`invoke_complete`'s `if`/`else` branches refine the split `invoke_complete_endorsed` /
`invoke_complete_unendorsed` pair, so the kernel has 15 transition functions). Zero
dependencies; compatible with Aeneas/Charon (Lean) extraction.

Each transition takes an immutable state and a fixed background theory, and returns a new
state plus an event:

```rust
fn(KernelState, &BackgroundTheory, ...) -> Result<(KernelState, KernelEvent), KernelError>
```

The generic driver
`Kernel<A: AuthorizerOracle, C: ContentGateOracle, F: ConformanceOracle, E: EventStore>`
is fully monomorphized (no `Arc<dyn Trait>`).

Key V3 mechanisms: a dual confidentiality/integrity invoke gate (the flow gate plus CHECK
4a/4b/4c -- graduated ALLOW / INSPECT+vouch, no override arm, since endorsement is the only
way to raise integrity); per-invocation attested oracle verdicts keyed by `InvocationId`
with replay freshness (`invocation_used`) and egress attestation (narrowing + coverage);
one unified two-dimension crossing guard in `invoke_complete` that debits a
dimension-adjusted `crossing_weight` (confidentiality and integrity components charged only
when each dimension actually helps); weighted, no-arbitrage debits on `return_endorsed`
and `grant_override` (`declass_weight`/`integ_weight`, no flat constants); and budget
conservation -- children spawn at budget 0 (`delegate`), `sentinel_credit_budget` is the
only faucet. `sentinel_degrade_integrity` and `unregister_tool` round out the action set.

## argus-explain

`crates/argus-explain` provides read-only DENY diagnostics: gate findings plus rescue
counterfactuals, mirroring the kernel's gated transitions -- including the V3 integrity
gates, attestation/freshness preconditions, `return_endorsed`/`grant_override` lever
floors, and `sentinel_degrade_integrity`. Agreement with the kernel is property-tested. It
is not part of the Charon/Aeneas extraction and is not verified.

## Formal verification

The protocol is verified in Lean 4 (see [`tzimtzum/`](../tzimtzum/), built on the
[Kav](../kav/) framework): TzimtzumV3, 16 actions against 26 invariants (11 safety
properties + 15 strengthening invariants), all kernel-checked.

The Rust kernel implements TzimtzumV3, and the Lean refinement under
[`formal-lean/`](formal-lean/) targets the same V3 kernel (extracted via Charon/Aeneas,
`scripts/charon-aeneas-extract.sh`). `implementation_sound` -- every reachable state of
the extracted kernel refines an abstract state satisfying all safety invariants, forward
simulation composed with the Kav soundness theorem, kernel-checked -- holds over all 16
V3 actions.

The refinement holds modulo the trusted Aeneas/Charon extractor and two explicit
assumptions: `CapacityOK` (the `Vec`-capacity bounds each transition needs, plus
`invoke_start`'s per-invocation tool-binding and attested-egress predictions) and
`OracleFidelity` (the runtime oracles agree with a fixed per-invocation abstract
interpretation). It does not prove the hand-written Rust source, the oracles, or the
external SPIFFE/STS mesh and adapter correct. See
[`formal-lean/README.md`](formal-lean/README.md) for the module map and the full trust
base.

## Building

```bash
cargo build
cargo build --release
cargo test
cargo clippy --workspace
```

To re-extract the kernel to Lean (Aeneas/Charon pipeline):

```bash
./scripts/charon-aeneas-extract.sh
```
