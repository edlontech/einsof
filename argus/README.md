# Argus

> Work in progress.

`argus-kernel` is the pure-functional security kernel implementing the
[TzimtzumV2](../tzimtzum/) authorization protocol. It enforces data-flow policies at tool
invocation boundaries to prevent exfiltration via indirect prompt injection (the Lethal
Trifecta).

Per the guest-model decision, Argus deploys as a guest inside an external SPIFFE/STS identity
mesh: identity, tokens, credentials, and revocation live in an (unverified, conformance-tested)
Elixir adapter plus the mesh. **The only Rust component is this verified kernel**, wrapped as a
NIF. The former gateway / oracle / registry / analysis / sandbox / audit / config crates and the
CLI have been removed.

## argus-kernel

Pure functional state machine implementing the TzimtzumV2 transitions. Zero dependencies
(`serde`/`serde_json` are dev-only), compatible with Aeneas/Charon (Lean) extraction. State is
held in `Vec`-backed `VecMap`/`VecSet` wrappers (`collections.rs`): Aeneas models `Vec` and its
iterator but has **no** model for `BTreeMap`/`BTreeSet` iteration, so the kernel avoids B-trees.

Each transition takes an immutable state and a fixed background theory, and returns a new state
plus an event:

```
fn(KernelState, &BackgroundTheory, ...) -> Result<(KernelState, KernelEvent), KernelError>
```

The generic driver `Kernel<A: AuthorizerOracle, C: ContentGateOracle, E: EventStore>` is fully
monomorphized (no `Arc<dyn Trait>`).

## Formal Verification

The protocol is verified in Lean 4 (see [`tzimtzum/`](../tzimtzum/) on the [Kav](../kav/)
framework). The Rust kernel is mechanically extracted to Lean via Aeneas/Charon (output under
`formal-lean/`) and refined against that specification. The extracted model is now fully
transparent (12/12 transitions, no axiom/sorry) and elaborates on Lean 4.30; the refinement of
that model against the spec is **work in progress** and is not yet a completed end-to-end proof.

## Building

```bash
cargo build              # debug
cargo build --release    # release (thin LTO, stripped)
cargo test               # kernel tests
cargo clippy --workspace # lint
```

To re-extract the kernel to Lean (Aeneas/Charon pipeline):

```bash
./scripts/charon-aeneas-extract.sh
```
