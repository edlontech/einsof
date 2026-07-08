use std::collections::HashMap;

use argus_kernel::{
    AgentId, AuthorizerOracle, BackgroundTheory, ConformanceOracle, ContentGateOracle,
    InvocationId, KernelState, ToolId,
};

pub struct ConstAuthorizer(pub bool);

impl AuthorizerOracle for ConstAuthorizer {
    fn allows(
        &self,
        _: &AgentId,
        _: &ToolId,
        _: &InvocationId,
        _: &KernelState,
        _: &BackgroundTheory,
    ) -> bool {
        self.0
    }
}

pub struct ConstConformance(pub bool);

impl ConformanceOracle for ConstConformance {
    fn conforms(
        &self,
        _: &AgentId,
        _: &ToolId,
        _: &InvocationId,
        _: &KernelState,
        _: &BackgroundTheory,
    ) -> bool {
        self.0
    }

    fn return_conforms(
        &self,
        _: &AgentId,
        _: &AgentId,
        _: &KernelState,
        _: &BackgroundTheory,
    ) -> bool {
        self.0
    }
}

/// Content gate backed by a precomputed per-invocation decision map. The kernel queries the gate
/// keyed on the invocation being VOUCHED for (the new invocation for CHECK 2a/2c/4a/4c, or an
/// in-flight invocation being re-examined for CHECK 2b/4b) -- never the tool alone, since the
/// same tool can appear at multiple invocations with different vouches in flight simultaneously.
/// Absent invocation id ⇒ `false` (fail-closed).
pub struct MapContentGate(pub HashMap<String, bool>);

impl ContentGateOracle for MapContentGate {
    fn passes(
        &self,
        _: &AgentId,
        _: &ToolId,
        inv: &InvocationId,
        _: &KernelState,
        _: &BackgroundTheory,
    ) -> bool {
        *self.0.get(&inv.0).unwrap_or(&false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn map_gate_defaults_closed() {
        let g = MapContentGate(HashMap::from([("inv-a".to_string(), true)]));
        assert!(g.passes(
            &AgentId::root(),
            &ToolId::new("a"),
            &InvocationId::new("inv-a"),
            &KernelState::initial(),
            &argus_kernel::BackgroundTheoryBuilder::new().build()
        ));
        assert!(!g.passes(
            &AgentId::root(),
            &ToolId::new("a"),
            &InvocationId::new("missing"),
            &KernelState::initial(),
            &argus_kernel::BackgroundTheoryBuilder::new().build()
        ));
    }

    #[test]
    fn map_gate_keyed_by_invocation_not_tool() {
        // Same tool, two invocations: the tool id alone is insufficient to disambiguate.
        let g = MapContentGate(HashMap::from([("inv-1".to_string(), true)]));
        assert!(g.passes(
            &AgentId::root(),
            &ToolId::new("shared_tool"),
            &InvocationId::new("inv-1"),
            &KernelState::initial(),
            &argus_kernel::BackgroundTheoryBuilder::new().build()
        ));
        assert!(!g.passes(
            &AgentId::root(),
            &ToolId::new("shared_tool"),
            &InvocationId::new("inv-2"),
            &KernelState::initial(),
            &argus_kernel::BackgroundTheoryBuilder::new().build()
        ));
    }
}
