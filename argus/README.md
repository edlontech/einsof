# Argus

> Work in progress.

`argus-kernel` is the pure-functional security kernel implementing the
[TzimtzumV2](../tzimtzum/) authorization protocol. It enforces data-flow policy at tool
invocation boundaries to prevent exfiltration via indirect prompt injection (the Lethal
Trifecta).

## argus-kernel

Pure functional state machine implementing the TzimtzumV2 transitions. Zero dependencies;
compatible with Aeneas/Charon (Lean) extraction.

Each transition takes an immutable state and a fixed background theory, and returns a new
state plus an event:

```rust
fn(KernelState, &BackgroundTheory, ...) -> Result<(KernelState, KernelEvent), KernelError>
```

The generic driver
`Kernel<A: AuthorizerOracle, C: ContentGateOracle, F: ConformanceOracle, E: EventStore>`
is fully monomorphized (no `Arc<dyn Trait>`).

## argus-explain

`crates/argus-explain` provides read-only DENY diagnostics: gate findings plus rescue
counterfactuals, mirroring the kernel's gated transitions. Agreement with the kernel is
property-tested. It is not part of the Charon/Aeneas extraction and is not verified.

## Formal verification

The protocol is verified in Lean 4 (see [`tzimtzum/`](../tzimtzum/), built on the
[Kav](../kav/) framework). The Rust kernel is mechanically extracted to Lean via
Aeneas/Charon (output under [`formal-lean/`](formal-lean/)) and refined against that
specification.

The refinement is complete. `implementation_sound` proves that every reachable state of
the extracted kernel refines an abstract TzimtzumV2 state satisfying all safety
invariants; it is forward simulation composed with the Kav soundness theorem,
kernel-checked.

This holds modulo the trusted Aeneas/Charon extractor and two explicit assumptions:
`CapacityOK` (the `Vec`-capacity bounds each transition needs) and `OracleFidelity` (the
runtime oracles agree with the abstract oracle fields). It does not prove the hand-written
Rust source, the oracles, or the external SPIFFE/STS mesh and adapter correct. See
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
