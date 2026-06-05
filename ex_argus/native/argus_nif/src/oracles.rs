use std::collections::HashMap;

use argus_kernel::{
    AgentId, AuthorizerOracle, BackgroundTheory, ConformanceOracle, ContentGateOracle, KernelState,
    ToolId,
};

pub struct ConstAuthorizer(pub bool);

impl AuthorizerOracle for ConstAuthorizer {
    fn allows(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
        self.0
    }
}

pub struct ConstConformance(pub bool);

impl ConformanceOracle for ConstConformance {
    fn conforms(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
        self.0
    }
}

/// Content gate backed by a precomputed per-tool decision map. The kernel only ever queries the
/// gate with the acting agent fixed (the tool varies), so a `tool -> bool` map is sufficient.
/// Absent tool ⇒ `false` (fail-closed).
pub struct MapContentGate(pub HashMap<String, bool>);

impl ContentGateOracle for MapContentGate {
    fn passes(&self, _: &AgentId, tool: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
        *self.0.get(&tool.0).unwrap_or(&false)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn map_gate_defaults_closed() {
        let g = MapContentGate(HashMap::from([("a".to_string(), true)]));
        assert!(g.passes(
            &AgentId::root(),
            &ToolId::new("a"),
            &KernelState::initial(),
            &argus_kernel::BackgroundTheoryBuilder::new().build()
        ));
        assert!(!g.passes(
            &AgentId::root(),
            &ToolId::new("missing"),
            &KernelState::initial(),
            &argus_kernel::BackgroundTheoryBuilder::new().build()
        ));
    }
}
