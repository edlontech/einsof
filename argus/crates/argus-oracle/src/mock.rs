use std::collections::BTreeSet;

use argus_kernel::{AgentId, AuthorizerOracle, BackgroundTheory, ContentGateOracle, KernelState, ToolId};

pub struct MockAuthorizer {
    allowed: BTreeSet<(AgentId, ToolId)>,
    allow_all: bool,
}

impl Default for MockAuthorizer {
    fn default() -> Self {
        Self::new()
    }
}

impl MockAuthorizer {
    pub fn new() -> Self {
        Self {
            allowed: BTreeSet::new(),
            allow_all: false,
        }
    }

    pub fn allow_all() -> Self {
        Self {
            allowed: BTreeSet::new(),
            allow_all: true,
        }
    }

    pub fn allow(mut self, agent: AgentId, tool: ToolId) -> Self {
        self.allowed.insert((agent, tool));
        self
    }
}

impl AuthorizerOracle for MockAuthorizer {
    fn allows(&self, agent: &AgentId, tool: &ToolId, _state: &KernelState, _bg: &BackgroundTheory) -> bool {
        self.allow_all || self.allowed.contains(&(agent.clone(), tool.clone()))
    }
}

pub struct MockContentGate {
    allowed: BTreeSet<(AgentId, ToolId)>,
    pass_all: bool,
}

impl Default for MockContentGate {
    fn default() -> Self {
        Self::new()
    }
}

impl MockContentGate {
    pub fn new() -> Self {
        Self {
            allowed: BTreeSet::new(),
            pass_all: false,
        }
    }

    pub fn pass_all() -> Self {
        Self {
            allowed: BTreeSet::new(),
            pass_all: true,
        }
    }

    pub fn pass(mut self, agent: AgentId, tool: ToolId) -> Self {
        self.allowed.insert((agent, tool));
        self
    }
}

impl ContentGateOracle for MockContentGate {
    fn passes(&self, agent: &AgentId, tool: &ToolId, _state: &KernelState, _bg: &BackgroundTheory) -> bool {
        self.pass_all || self.allowed.contains(&(agent.clone(), tool.clone()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use argus_kernel::BackgroundTheoryBuilder;

    fn s() -> KernelState {
        KernelState::initial()
    }

    fn bg() -> BackgroundTheory {
        BackgroundTheoryBuilder::new().build()
    }

    #[test]
    fn mock_authorizer_allows_configured_pair() {
        let auth = MockAuthorizer::new().allow(AgentId::new("agent1"), ToolId::new("tool1"));
        assert!(auth.allows(&AgentId::new("agent1"), &ToolId::new("tool1"), &s(), &bg()));
    }

    #[test]
    fn mock_authorizer_denies_unconfigured_pair() {
        let auth = MockAuthorizer::new().allow(AgentId::new("agent1"), ToolId::new("tool1"));
        assert!(!auth.allows(&AgentId::new("agent2"), &ToolId::new("tool1"), &s(), &bg()));
    }

    #[test]
    fn mock_authorizer_allow_all_permits_everything() {
        let auth = MockAuthorizer::allow_all();
        assert!(auth.allows(&AgentId::new("anyone"), &ToolId::new("anything"), &s(), &bg()));
    }

    #[test]
    fn mock_content_gate_passes_configured_pair() {
        let gate = MockContentGate::new().pass(AgentId::new("a"), ToolId::new("t"));
        assert!(gate.passes(&AgentId::new("a"), &ToolId::new("t"), &s(), &bg()));
    }

    #[test]
    fn mock_content_gate_blocks_unconfigured_pair() {
        let gate = MockContentGate::new();
        assert!(!gate.passes(&AgentId::new("a"), &ToolId::new("t"), &s(), &bg()));
    }

    #[test]
    fn mock_content_gate_pass_all_permits_everything() {
        let gate = MockContentGate::pass_all();
        assert!(gate.passes(&AgentId::new("x"), &ToolId::new("y"), &s(), &bg()));
    }
}
