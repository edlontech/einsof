(** Oracle axioms for AuthorizerOracle and ContentGateOracle.
    These are immutable background theory (not part of mutable state).

    In Rust (traits.rs):
      trait AuthorizerOracle { fn allows(&self, agent: &AgentId, tool: &ToolId) -> bool; }
      trait ContentGateOracle { fn passes(&self, agent: &AgentId, tool: &ToolId) -> bool; }

    In Lean (TzimtzumV2.lean:144-145):
      immutable relation authorizer_allows : AgentId -> ToolId -> Bool
      immutable relation content_gate_passes : AgentId -> ToolId -> Bool *)

Require Import ArgusKernel.axioms.DecidableAxioms.

Parameter authorizer_allows : AgentId -> ToolId -> bool.
Parameter content_gate_passes : AgentId -> ToolId -> bool.
