use std::collections::BTreeMap;
use std::collections::BTreeSet;

use crate::capability::CapKind;
use crate::types::{AgentId, ConfLevel, EgressKind, ToolId};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ToolMetadata {
    pub capabilities: BTreeSet<CapKind>,
    pub egress: BTreeSet<EgressKind>,
    pub conf_floor: ConfLevel,
    pub endorsed: bool,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FlowMode {
    Allow,
    Inspect,
    Deny,
}

#[derive(Clone, Debug)]
pub struct BackgroundTheory {
    tools: BTreeMap<ToolId, ToolMetadata>,
    flow_policy: BTreeMap<(ConfLevel, EgressKind), FlowMode>,
    flow_overrides: BTreeSet<(AgentId, ToolId, ConfLevel)>,
}

impl BackgroundTheory {
    pub fn has_tool(&self, tool: &ToolId) -> bool {
        self.tools.contains_key(tool)
    }

    pub fn tool_metadata(&self, tool: &ToolId) -> Option<&ToolMetadata> {
        self.tools.get(tool)
    }

    pub fn flow_mode(&self, level: ConfLevel, egress: EgressKind) -> FlowMode {
        self.flow_policy
            .get(&(level, egress))
            .copied()
            .unwrap_or(FlowMode::Deny)
    }

    pub fn has_flow_override(&self, agent: &AgentId, tool: &ToolId, level: ConfLevel) -> bool {
        self.flow_overrides
            .contains(&(agent.clone(), tool.clone(), level))
    }

    pub fn registered_tools(&self) -> impl Iterator<Item = &ToolId> {
        self.tools.keys()
    }
}

pub struct BackgroundTheoryBuilder {
    tools: BTreeMap<ToolId, ToolMetadata>,
    flow_policy: BTreeMap<(ConfLevel, EgressKind), FlowMode>,
    flow_overrides: BTreeSet<(AgentId, ToolId, ConfLevel)>,
}

impl BackgroundTheoryBuilder {
    pub fn new() -> Self {
        Self {
            tools: BTreeMap::new(),
            flow_policy: BTreeMap::new(),
            flow_overrides: BTreeSet::new(),
        }
    }

    pub fn register_tool(&mut self, id: ToolId, metadata: ToolMetadata) -> &mut Self {
        self.tools.insert(id, metadata);
        self
    }

    pub fn set_flow(
        &mut self,
        level: ConfLevel,
        egress: EgressKind,
        mode: FlowMode,
    ) -> &mut Self {
        self.flow_policy.insert((level, egress), mode);
        self
    }

    pub fn add_override(
        &mut self,
        agent: AgentId,
        tool: ToolId,
        level: ConfLevel,
    ) -> &mut Self {
        self.flow_overrides.insert((agent, tool, level));
        self
    }

    pub fn build(self) -> BackgroundTheory {
        BackgroundTheory {
            tools: self.tools,
            flow_policy: self.flow_policy,
            flow_overrides: self.flow_overrides,
        }
    }
}

impl Default for BackgroundTheoryBuilder {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn deny_is_default_flow_mode() {
        let bg = BackgroundTheoryBuilder::new().build();
        assert_eq!(
            bg.flow_mode(ConfLevel::Sensitive, EgressKind::NetworkExternal),
            FlowMode::Deny,
        );
    }

    #[test]
    fn flow_policy_last_write_wins() {
        let mut builder = BackgroundTheoryBuilder::new();
        builder.set_flow(ConfLevel::Internal, EgressKind::NetworkExternal, FlowMode::Allow);
        builder.set_flow(ConfLevel::Internal, EgressKind::NetworkExternal, FlowMode::Inspect);
        let bg = builder.build();
        assert_eq!(
            bg.flow_mode(ConfLevel::Internal, EgressKind::NetworkExternal),
            FlowMode::Inspect,
        );
    }

    #[test]
    fn tool_metadata_lookup() {
        let mut builder = BackgroundTheoryBuilder::new();
        let meta = ToolMetadata {
            capabilities: BTreeSet::from([CapKind::FilesystemRead]),
            egress: BTreeSet::from([EgressKind::NetworkExternal]),
            conf_floor: ConfLevel::Internal,
            endorsed: false,
        };
        builder.register_tool(ToolId::new("read_file"), meta.clone());
        let bg = builder.build();

        let found = bg.tool_metadata(&ToolId::new("read_file")).unwrap();
        assert_eq!(found, &meta);
        assert!(bg.tool_metadata(&ToolId::new("nonexistent")).is_none());
    }

    #[test]
    fn flow_override_check() {
        let mut builder = BackgroundTheoryBuilder::new();
        builder.add_override(
            AgentId::new("agent-1"),
            ToolId::new("tool-1"),
            ConfLevel::Sensitive,
        );
        let bg = builder.build();

        assert!(bg.has_flow_override(
            &AgentId::new("agent-1"),
            &ToolId::new("tool-1"),
            ConfLevel::Sensitive,
        ));
        assert!(!bg.has_flow_override(
            &AgentId::new("agent-1"),
            &ToolId::new("tool-1"),
            ConfLevel::Public,
        ));
    }
}
