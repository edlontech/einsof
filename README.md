# Einsof

> Work in progress.

Einsof is a security authorization system for LLM tool execution. It targets the
[Lethal Trifecta](https://simonwillison.net/2025/Jun/16/the-lethal-trifecta/): private
data, untrusted content, and external communication combined into an indirect prompt
injection path.

The core has two components. TzimtzumV4 is the formal source of truth; Argus is its
extraction-compatible Rust implementation and refinement target. ExArgus is the
conformance-tested Elixir deployment adapter around Argus.

## Components

### [Tzimtzum](tzimtzum/): V4 specification

A pure Lean 4 authorization protocol built on the [Kav](kav/) transition-system
framework. Its exact 12-action system preserves all 32 invariants in every reachable
abstract state.

### [Argus](argus/): V4 kernel and refinement

`argus-kernel` is the zero-runtime-dependency, pure-functional Rust implementation of the
same twelve transitions. Charon and Aeneas extract it to Lean; the refinement under
[`argus/formal-lean`](argus/formal-lean/) connects successful extracted transitions to
TzimtzumV4 and composes with the 32-invariant soundness theorem.

### [ExArgus](ex_argus/): deployment adapter

The Elixir/Rustler boundary exposes one opaque live instance, the twelve V4 actions,
read-only V5 state and chain status, strict envelope recovery, fixed capacity limits, and
one bounded telemetry event per transition attempt. Source builds are the default;
precompiled NIFs require explicit opt-in.

## Trust boundary

The extracted V4 kernel covers exactly 12 actions and yields all 32 invariants modulo
trusted Aeneas/Charon extraction, `CapacityOK`, and narrowed `OracleFidelity`. This does
not verify the handwritten Rust itself. Handwritten Rust, ExArgus and telemetry,
authentication/identity/evidence truth, serialization and persistence, the native
digest-chain adapter and trusted rollback anchor, and host one-owner/persist-before-effect
ordering are outside formal verification. The adapter is conformance-tested.

A host must authenticate frozen command and evidence meaning, serialize one owner per
instance, durably store every accepted envelope plus a protected head/length anchor before
the next command or effect, and discard/recover after persistence failure or timeout
ambiguity. SHA-256 chaining does not by itself prevent rollback of a valid prefix.

## Current checks

```bash
# Tzimtzum V4 abstract specification
(cd tzimtzum && make verify)

# Argus Rust kernel
(cd argus && cargo fmt --check)
(cd argus && cargo test --workspace --locked)
(cd argus && cargo clippy --workspace --all-targets --locked -- -D warnings)
(cd argus && cargo build --workspace --locked --release)

# Extracted-kernel refinement
(cd argus/formal-lean && lake build)
(cd argus/formal-lean && lake build ArgusChecks)

# ExArgus adapter
(cd ex_argus && mix format --check-formatted)
(cd ex_argus && MIX_ENV=test RUSTLER_PRECOMPILED_FORCE_BUILD=1 mix test)
(cd ex_argus && mix credo --strict)
(cd ex_argus && mix dialyzer)
```

## Toolchain

Managed through `mise`, Cargo, Mix, and each Lean project's pinned toolchain:

| Tool | Version |
| --- | --- |
| Rust | 1.93.0 |
| Elixir | 1.19-compatible (`~> 1.19`) |
| Tzimtzum/refinement Lean | 4.32.1 |
| Charon extraction Rust | nightly-2026-06-01 |

## References

**Standards and identity ecosystem**

- [SPIFFE: Securing the identity of agentic AI and non-human actors](https://www.hashicorp.com/en/blog/spiffe-securing-the-identity-of-agentic-ai-and-non-human-actors)
- [Uber: Solving the Agent Identity Crisis](https://www.uber.com/us/en/blog/solving-the-agent-identity-crisis/)
- [Agent2Agent Protocol Specification](https://a2a-protocol.org/latest/specification/)
- [AIP: Agent Identity Protocol for Verifiable Delegation Across MCP and A2A](https://arxiv.org/abs/2603.24775)

**Information-flow control and verification**

- Honda, Vasconcelos, Yoshida, [Secure Information Flow as Typed Process Behaviour](https://link.springer.com/chapter/10.1007/3-540-46425-5_12)
- Boudol, [Information flow vs. resource access in the asynchronous pi-calculus](https://link.springer.com/chapter/10.1007/3-540-45022-X_35)
- [Lean 4](https://lean-lang.org/)

## AI usage disclosure

Parts of this project were developed with AI assistance, most heavily in documentation,
Lean work, the Tzimtzum/Kav formalization, and the Aeneas/Charon refinement.

## License

MIT
