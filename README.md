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

The TzimtzumV2 protocol, written in Lean 4 on the [Kav](kav/) transition-system
framework. All 10 safety properties and 15 strengthening invariants are verified
inductive (325 VCs) by kernel-checked mathlib automation -- no SMT solver in the
trust base.

### [Kav](kav/) -- Verification Framework

The pure-Lean transition-system verifier Tzimtzum is built on (`#kav_check_action`,
`#kav_check_init`, finite-model checker). Reusable independent of the protocol.

### [Argus](argus/) -- Rust Implementation

A tool authorization gateway implementing the TzimtzumV2 protocol. Rust workspace with
10 crates covering the core state machine, policy engine, MCP server management, LLM proxy,
gRPC API, sandboxing, and more. 512+ tests across the workspace.

### [Lean Refinement](argus/formal-lean/) -- Rust-to-Spec (in progress)

The Rust kernel is mechanically extracted to Lean via Aeneas/Charon and refined against the
Kav specification. This refinement is **work in progress** -- it does not yet constitute a
completed end-to-end proof that the kernel implements the protocol.

## Toolchain

Managed via [mise](https://mise.jdx.dev/):

| Tool  | Version |
|-------|---------|
| Rust  | 1.93.0  |
| Lean  | 4.30.0  |

## License

MIT
