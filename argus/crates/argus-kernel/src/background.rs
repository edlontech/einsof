use crate::capability::CapKind;
use crate::collections::{VecMap, VecSet};
use crate::types::{
    AgentId, ConfLevel, EgressKind, FlowKey, InstructionId, IssuerId, OverrideEntry, ToolId,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ToolMetadata {
    pub capabilities: VecSet<CapKind>,
    pub egress: VecSet<EgressKind>,
    pub conf_floor: ConfLevel,
    pub output_bounded: bool,
    pub issuer: IssuerId,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FlowMode {
    Allow,
    Inspect,
    Deny,
}

#[derive(Clone, Debug)]
pub struct BackgroundTheory {
    tools: VecMap<ToolId, ToolMetadata>,
    flow_policy: VecMap<FlowKey, FlowMode>,
    flow_overrides: VecSet<OverrideEntry>,
    trusted_issuers: VecSet<IssuerId>,
    instruction_issuer: VecMap<InstructionId, IssuerId>,
}

impl BackgroundTheory {
    pub fn has_tool(&self, tool: &ToolId) -> bool {
        self.tools.contains_key(tool)
    }

    pub fn tool_metadata(&self, tool: &ToolId) -> Option<ToolMetadata> {
        self.tools.get_cloned(tool)
    }

    pub fn flow_mode(&self, level: ConfLevel, egress: EgressKind) -> FlowMode {
        match self.flow_policy.get(&FlowKey { level, egress }) {
            Some(mode) => *mode,
            None => FlowMode::Deny,
        }
    }

    pub fn has_flow_override(&self, agent: &AgentId, tool: &ToolId, level: ConfLevel) -> bool {
        self.flow_overrides.contains(&OverrideEntry {
            agent: agent.clone(),
            tool: tool.clone(),
            level,
        })
    }

    pub fn registered_tools(&self) -> impl Iterator<Item = &ToolId> {
        self.tools.iter().map(|(tool, _)| tool)
    }

    pub fn is_trusted_issuer(&self, issuer: &IssuerId) -> bool {
        self.trusted_issuers.contains(issuer)
    }

    pub fn instruction_issuer(&self, instr: &InstructionId) -> Option<&IssuerId> {
        self.instruction_issuer.get(instr)
    }
}

pub struct BackgroundTheoryBuilder {
    tools: VecMap<ToolId, ToolMetadata>,
    flow_policy: VecMap<FlowKey, FlowMode>,
    flow_overrides: VecSet<OverrideEntry>,
    trusted_issuers: VecSet<IssuerId>,
    instruction_issuer: VecMap<InstructionId, IssuerId>,
}

impl BackgroundTheoryBuilder {
    pub fn new() -> Self {
        Self {
            tools: VecMap::new(),
            flow_policy: VecMap::new(),
            flow_overrides: VecSet::new(),
            trusted_issuers: VecSet::new(),
            instruction_issuer: VecMap::new(),
        }
    }

    pub fn register_tool(&mut self, id: ToolId, metadata: ToolMetadata) -> &mut Self {
        self.tools.insert(id, metadata);
        self
    }

    pub fn set_flow(&mut self, level: ConfLevel, egress: EgressKind, mode: FlowMode) -> &mut Self {
        self.flow_policy.insert(FlowKey { level, egress }, mode);
        self
    }

    pub fn add_override(&mut self, agent: AgentId, tool: ToolId, level: ConfLevel) -> &mut Self {
        self.flow_overrides.insert(OverrideEntry { agent, tool, level });
        self
    }

    pub fn trust_issuer(&mut self, issuer: IssuerId) -> &mut Self {
        self.trusted_issuers.insert(issuer);
        self
    }

    pub fn register_instruction(&mut self, instr: InstructionId, issuer: IssuerId) -> &mut Self {
        self.instruction_issuer.insert(instr, issuer);
        self
    }

    pub fn build(self) -> BackgroundTheory {
        BackgroundTheory {
            tools: self.tools,
            flow_policy: self.flow_policy,
            flow_overrides: self.flow_overrides,
            trusted_issuers: self.trusted_issuers,
            instruction_issuer: self.instruction_issuer,
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
        builder.set_flow(
            ConfLevel::Internal,
            EgressKind::NetworkExternal,
            FlowMode::Allow,
        );
        builder.set_flow(
            ConfLevel::Internal,
            EgressKind::NetworkExternal,
            FlowMode::Inspect,
        );
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
            capabilities: VecSet::from([CapKind::FilesystemRead]),
            egress: VecSet::from([EgressKind::NetworkExternal]),
            conf_floor: ConfLevel::Internal,
            output_bounded: false,
            issuer: IssuerId::new("trusted"),
        };
        builder.register_tool(ToolId::new("read_file"), meta.clone());
        let bg = builder.build();

        let found = bg.tool_metadata(&ToolId::new("read_file")).unwrap();
        assert_eq!(found, meta);
        assert!(bg.tool_metadata(&ToolId::new("nonexistent")).is_none());
    }

    #[test]
    fn trusted_issuer_and_instruction_registry() {
        let mut builder = BackgroundTheoryBuilder::new();
        builder.trust_issuer(IssuerId::new("trusted"));
        builder.register_instruction(
            InstructionId::new("sys-prompt"),
            IssuerId::new("trusted"),
        );
        let bg = builder.build();

        assert!(bg.is_trusted_issuer(&IssuerId::new("trusted")));
        assert!(!bg.is_trusted_issuer(&IssuerId::new("rogue")));
        assert_eq!(
            bg.instruction_issuer(&InstructionId::new("sys-prompt")),
            Some(&IssuerId::new("trusted")),
        );
        assert_eq!(bg.instruction_issuer(&InstructionId::new("unknown")), None);
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
