# Argus

> Work in progress.

`argus-kernel` is the zero-runtime-dependency, pure-functional Rust implementation of the
[TzimtzumV4](../tzimtzum/) authorization protocol. It enforces confidentiality,
integrity, capability, inspection, quarantine, and bounded crossing rules at tool and
agent boundaries.

## Kernel surface

Each transition consumes an immutable `KernelState` and returns a new state plus its exact
`KernelAction`, or a closed `KernelError`:

```rust
fn(KernelState, &BackgroundTheory, ...) -> Result<(KernelState, KernelAction), KernelError>
```

The complete V4 action surface is:

1. `register_tool`
2. `unregister_tool`
3. `delegate`
4. `grant_capability`
5. `grant_crossing`
6. `revoke`
7. `cascade_revoke`
8. `ingest`
9. `begin_invocation`
10. `authorize_inspected`
11. `settle_invocation`
12. `cross_output`

The immutable background contains enforcement mode, exact confidentiality allow/inspect
ceilings for four egress kinds, and the root identity. Invocation policy and evidence are
frozen transition inputs. Mutable state contains the agent tree and capabilities, dual
labels, pending invocations and challenges, consumed-id histories, crossing grants, and
registered tools.

The kernel deliberately uses extraction-compatible `VecMap`/`VecSet` collections,
explicit index loops, owned collection accessors, and no runtime dependencies. Serde and
JSON are development-only dependencies for the shared V4 conformance corpus.

## Verification

TzimtzumV4 proves all 32 invariants over its complete 12-action abstract system. Charon
and Aeneas mechanically extract this Rust kernel to Lean. The refinement in
[`formal-lean/`](formal-lean/) proves that every successful extracted action maps to its
single abstract counterpart and that every reachable extracted state relates to a
TzimtzumV4 state satisfying the full invariant bundle.

The extracted V4 kernel covers exactly 12 actions and yields all 32 invariants modulo
trusted Aeneas/Charon extraction, `CapacityOK`, and narrowed `OracleFidelity`. This does
not verify the handwritten Rust itself. `CapacityOK` supplies governed-root coherence,
exact successful-branch collection bounds, begin-time snapshot prediction, and
`grant_crossing n < 2^32`. `OracleFidelity` is limited to begin-time authorizer verdict
and attested-egress agreement.

Handwritten Rust, ExArgus and telemetry, authentication/identity/evidence truth,
serialization and persistence, the native digest-chain adapter and trusted rollback
anchor, and host one-owner/persist-before-effect ordering are outside formal
verification. The adapter is conformance-tested. See
[`formal-lean/README.md`](formal-lean/README.md) for the theorem closure and exact
hypotheses.

## Building and checking

From `argus/`:

```bash
cargo fmt --check
cargo test --workspace --locked
cargo clippy --workspace --all-targets --locked -- -D warnings
cargo build --workspace --locked --release
```

The shared conformance runner covers the public transition surface in addition to unit,
safety-property, and external-consumer tests.

To build the extracted model and refinement:

```bash
cd formal-lean
lake build
lake build ArgusChecks
```

To regenerate the extracted Lean model with the frozen, locally reconstructed
Aeneas/Charon stack:

```bash
./scripts/charon-aeneas-extract.sh
```

The extraction script validates all tool pins and patches before replacing generated
Lean output. Generated Lean is never hand-edited.
