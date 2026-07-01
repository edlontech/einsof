# Einsof

> Work in progress.

Einsof is a security authorization system for LLM tool execution. It targets the
[Lethal Trifecta](https://simonwillison.net/2025/Jun/16/the-lethal-trifecta/): the
combination of private data, untrusted content, and external communication that lets
indirect prompt injection exfiltrate data.

The system enforces authorization at tool boundaries, so a prompt-injected agent cannot
reach an egress channel while it carries taint from private data.

## Components

### [Tzimtzum](tzimtzum/): formal specification

The TzimtzumV2 protocol, written in Lean 4 on the [Kav](kav/) transition-system
framework: 13 actions, 10 safety properties, and 16 strengthening invariants, all proved
inductive and assembled into a single reachability theorem (`kav_sound`).

### [Kav](kav/): verification framework

The pure-Lean transition-system verifier Tzimtzum is built on (`#kav_check_action`,
`#kav_check_init`, and a finite-model checker for bug-finding).

### [Argus](argus/): Rust implementation

`argus-kernel`, the pure-functional state machine that implements the TzimtzumV2
transitions.

### [ExArgus](ex_argus/): Elixir NIF

The Elixir binding for `argus-kernel`; exposes the live authorization API.

### [Lean refinement](argus/formal-lean/): Rust to spec

The Rust kernel is mechanically extracted to Lean via Aeneas/Charon and refined against
the Kav specification. `implementation_sound` is complete: every reachable state of the
extracted kernel refines an abstract TzimtzumV2 state satisfying all safety invariants.
This holds modulo the trusted extractor and two explicit assumptions (`Vec`-capacity
bounds and runtime-oracle agreement); it does not cover the hand-written Rust source or
the external mesh.

## Toolchain

Managed via [mise](https://mise.jdx.dev/):

| Tool | Version |
|------|---------|
| Rust | 1.93.0  |
| Lean | 4.30.0  |

## References

Background reading and prior art behind the protocol design.

**Standards and identity ecosystem**
- [SPIFFE: Securing the identity of agentic AI and non-human actors](https://www.hashicorp.com/en/blog/spiffe-securing-the-identity-of-agentic-ai-and-non-human-actors) -- the mesh Argus is a guest inside of
- [Uber: Solving the Agent Identity Crisis](https://www.uber.com/us/en/blog/solving-the-agent-identity-crisis/) -- SVID + STS + attested `act_chain` per hop, the actor-chain model Einsof's identity plane adopts wholesale
- [Agent2Agent Protocol Specification](https://a2a-protocol.org/latest/specification/)
- [AIP: Agent Identity Protocol for Verifiable Delegation Across MCP and A2A (arXiv 2603.24775)](https://arxiv.org/abs/2603.24775)
- [State of MCP Security: March 2026](https://nimblebrain.ai/blog/state-of-mcp-security-2026/)
- [Macaroon Tokens vs API Keys for AI Agents](https://satgate.io/blog/macaroon-tokens-vs-api-keys)

**Academic (information-flow control)**
- Honda, Vasconcelos, Yoshida -- [Secure Information Flow as Typed Process Behaviour](https://link.springer.com/chapter/10.1007/3-540-46425-5_12)
- Boudol -- [Information flow vs. resource access in the asynchronous pi-calculus](https://link.springer.com/chapter/10.1007/3-540-45022-X_35)
- [Detecting Steganographic Collusion in Multi-Agent LLMs (arXiv 2510.04303)](https://arxiv.org/abs/2510.04303)

**Verification tooling**
- [Veil 2.0](https://github.com/verse-lab/veil)
- [Lean 4](https://lean-lang.org/)

## AI usage disclosure

Parts of this project were developed with AI assistance, most heavily in the
documentation, the Lean work, the Tzimtzum/Kav formalization, and the Aeneas/Charon
refinement.

## License

MIT
