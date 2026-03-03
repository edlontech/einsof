# Einsof

> Work in progress.

Einsof is a security authorization system for LLM tool execution. It addresses the
[Lethal Trifecta](https://simonwillison.net/2025/Jun/16/the-lethal-trifecta/) -- the
combination of private data, untrusted content, and external communication that enables
data exfiltration through indirect prompt injection.

The system enforces authorization at tool boundaries so that a confused (prompt-injected)
agent cannot reach egress channels when it carries taint from private data.

## Components

### [Tzimtzum](tzimtzum/) -- Formal Specification

The TzimtzumV2 protocol, written in Lean 4 using the
[Veil](https://github.com/verse-lab/veil) verification framework. All 7 safety properties
and 12 strengthening invariants are verified automatically via push-button SMT

### [Argus](argus/) -- Rust Implementation

A tool authorization gateway implementing the TzimtzumV2 protocol. Rust workspace with
10 crates covering the core state machine, policy engine, MCP server management, LLM proxy,
gRPC API, sandboxing, and more. 512+ tests across the workspace.

### [Formal Proofs](argus/formal/) -- Rocq (Coq) Verification

Mechanized proofs connecting the Lean specification to the Rust implementation. Three layers:
axioms (data structure interfaces), abstract specification (safety properties), and refinement
proofs (simulation relations and soundness guarantees).

## Toolchain

Managed via [mise](https://mise.jdx.dev/):

| Tool  | Version |
|-------|---------|
| Rust  | 1.93.0  |
| Lean  | 4.27.0  |
| Rocq  | 9.0     |

## License

MIT
