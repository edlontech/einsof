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
framework. All 10 safety properties and 15 strengthening invariants

### [Kav](kav/) -- Verification Framework

The pure-Lean transition-system verifier Tzimtzum is built on (`#kav_check_action`,
`#kav_check_init`, finite-model checker).

### [Argus](argus/) -- Rust Implementation

`argus-kernel`: the pure-functional state machine implementing the TzimtzumV2 transitions.

### [Lean Refinement](argus/formal-lean/) -- Rust-to-Spec

The Rust kernel is mechanically extracted to Lean via Aeneas/Charon and refined against the Kav
specification. `implementation_sound` is **complete**: every reachable state of the extracted
kernel refines an abstract TzimtzumV2 state satisfying all safety invariants -- modulo the trusted
extractor and two explicit assumptions (`Vec`-capacity bounds and runtime-oracle agreement). It
does not prove the hand-written Rust source or the external mesh.

## Toolchain

Managed via [mise](https://mise.jdx.dev/):

| Tool  | Version |
|-------|---------|
| Rust  | 1.93.0  |
| Lean  | 4.30.0  |

## AI Usage Disclosure

Parts of this project were developed with AI assistance, most heavily in Documentation, Lean work, 
the Tzimtzum/Kav formalization and the Aeneas/Charon refinement.

## License

MIT
