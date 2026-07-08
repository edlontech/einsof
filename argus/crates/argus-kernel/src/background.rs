use crate::capability::CapKind;
use crate::collections::{VecMap, VecSet};
use crate::types::{ConfLevel, EgressKind, InstructionId, IntegLevel, IssuerId, ToolId};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ToolMetadata {
    pub capabilities: VecSet<CapKind>,
    pub egress: VecSet<EgressKind>,
    pub conf_floor: ConfLevel,
    pub output_bounded: bool,
    pub issuer: IssuerId,
    /// Invoke requirement: ALLOW iff the agent's level clears this floor.
    pub integ_floor: IntegLevel,
    /// Vouchable inspect band above `integ_floor`; a band above the allow floor with no
    /// room below it is an empty band -- coherent by construction.
    pub integ_inspect_floor: IntegLevel,
    /// The emission: what ingesting this tool's output does to the invoking agent's
    /// integrity. Distinct from `integ_floor` -- e.g. `delete_repo` floor trusted /
    /// emission attested; `web_fetch` floor untrusted / emission untrusted.
    pub output_integ: IntegLevel,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FlowMode {
    Allow,
    Inspect,
    Deny,
}

/// A (level, egress, mode) matrix that is not representable as ceilings: per egress the
/// ALLOW set must be a downward-closed prefix and the INSPECT band must sit directly
/// above it (absent entries are DENY).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlowMatrixError {
    NonMonotone,
}

#[derive(Clone, Debug)]
pub struct BackgroundTheory {
    tools: VecMap<ToolId, ToolMetadata>,
    allow_ceiling: VecMap<EgressKind, ConfLevel>,
    inspect_ceiling: VecMap<EgressKind, ConfLevel>,
    trusted_issuers: VecSet<IssuerId>,
    instruction_issuer: VecMap<InstructionId, IssuerId>,
    lever_integ_floor: IntegLevel,
    lever_integ_inspect_floor: IntegLevel,
}

impl BackgroundTheory {
    pub fn has_tool(&self, tool: &ToolId) -> bool {
        self.tools.contains_key(tool)
    }

    pub fn tool_metadata(&self, tool: &ToolId) -> Option<ToolMetadata> {
        self.tools.get_cloned(tool)
    }

    /// Flow mode computed from the two per-egress ceilings. Absent entry = no level
    /// passes that band (strict default-deny, including Public). ALLOW wins over
    /// INSPECT where the bands overlap; outside both bands the mode is DENY.
    pub fn flow_mode(&self, level: ConfLevel, egress: EgressKind) -> FlowMode {
        let allows = match self.allow_ceiling.get_cloned(&egress) {
            Some(c) => level.le(c),
            None => false,
        };
        if allows {
            return FlowMode::Allow;
        }
        let inspects = match self.inspect_ceiling.get_cloned(&egress) {
            Some(c) => level.le(c),
            None => false,
        };
        if inspects { FlowMode::Inspect } else { FlowMode::Deny }
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

    /// Robust-declassification floor for the levers (`return_endorsed`/`grant_override`).
    pub fn lever_integ_floor(&self) -> IntegLevel {
        self.lever_integ_floor
    }

    /// Vouchable inspect band above `lever_integ_floor` (used by `return_endorsed`, which
    /// has a conformance verdict to vouch with; `grant_override` has none and stays strict).
    pub fn lever_integ_inspect_floor(&self) -> IntegLevel {
        self.lever_integ_inspect_floor
    }
}

pub struct BackgroundTheoryBuilder {
    tools: VecMap<ToolId, ToolMetadata>,
    allow_ceiling: VecMap<EgressKind, ConfLevel>,
    inspect_ceiling: VecMap<EgressKind, ConfLevel>,
    trusted_issuers: VecSet<IssuerId>,
    instruction_issuer: VecMap<InstructionId, IssuerId>,
    lever_integ_floor: IntegLevel,
    lever_integ_inspect_floor: IntegLevel,
}

impl BackgroundTheoryBuilder {
    pub fn new() -> Self {
        Self {
            tools: VecMap::new(),
            allow_ceiling: VecMap::new(),
            inspect_ceiling: VecMap::new(),
            trusted_issuers: VecSet::new(),
            instruction_issuer: VecMap::new(),
            // Untrusted = levers ungated, preserving V2 behavior until an operator sets
            // real floors. Platforms MUST set real floors -- the robust-declassification
            // posture (design §5.5) is a no-op at this default.
            lever_integ_floor: IntegLevel::Untrusted,
            lever_integ_inspect_floor: IntegLevel::Untrusted,
        }
    }

    pub fn register_tool(&mut self, id: ToolId, metadata: ToolMetadata) -> &mut Self {
        self.tools.insert(id, metadata);
        self
    }

    /// Set (or clear, with `None`) the two confidentiality ceilings for an egress kind.
    pub fn set_egress_ceilings(
        &mut self,
        egress: EgressKind,
        allow: Option<ConfLevel>,
        inspect: Option<ConfLevel>,
    ) -> &mut Self {
        match allow {
            Some(c) => { self.allow_ceiling.insert(egress, c); }
            None => { self.allow_ceiling.remove(&egress); }
        }
        match inspect {
            Some(c) => { self.inspect_ceiling.insert(egress, c); }
            None => { self.inspect_ceiling.remove(&egress); }
        }
        self
    }

    /// Compat constructor: build a fresh builder whose ceilings encode `entries`
    /// (a mode matrix). Errs if the matrix is not ceiling-representable.
    pub fn from_matrix(
        entries: &[(ConfLevel, EgressKind, FlowMode)],
    ) -> Result<Self, FlowMatrixError> {
        const LEVELS: [ConfLevel; 4] = [
            ConfLevel::Public,
            ConfLevel::Internal,
            ConfLevel::Sensitive,
            ConfLevel::Restricted,
        ];
        const EGRESS: [EgressKind; 4] = [
            EgressKind::NetworkExternal,
            EgressKind::NetworkInternal,
            EgressKind::FilesystemWrite,
            EgressKind::Ipc,
        ];
        let mut builder = Self::new();
        let mut gi = 0;
        while gi < EGRESS.len() {
            let egress = EGRESS[gi];
            let mut modes = [FlowMode::Deny; 4];
            let mut ei = 0;
            while ei < entries.len() {
                let (lv, eg, md) = entries[ei];
                if eg == egress {
                    let mut li = 0;
                    while li < LEVELS.len() {
                        if LEVELS[li] == lv {
                            modes[li] = md;
                        }
                        li += 1;
                    }
                }
                ei += 1;
            }
            let mut allow_top: Option<ConfLevel> = None;
            let mut inspect_top: Option<ConfLevel> = None;
            let mut in_allow = true;
            let mut in_inspect = true;
            let mut monotone = true;
            let mut li = 0;
            while li < LEVELS.len() {
                match modes[li] {
                    FlowMode::Allow => {
                        if !in_allow {
                            monotone = false;
                        }
                        allow_top = Some(LEVELS[li]);
                    }
                    FlowMode::Inspect => {
                        in_allow = false;
                        if !in_inspect {
                            monotone = false;
                        }
                        inspect_top = Some(LEVELS[li]);
                    }
                    FlowMode::Deny => {
                        in_allow = false;
                        in_inspect = false;
                    }
                }
                li += 1;
            }
            if !monotone {
                return Err(FlowMatrixError::NonMonotone);
            }
            // Spec semantics: flow_inspects is its own band-from-bottom relation (ALLOW
            // wins where they overlap), so inspect_top is the inspect ceiling directly.
            builder.set_egress_ceilings(egress, allow_top, inspect_top);
            gi += 1;
        }
        Ok(builder)
    }

    pub fn trust_issuer(&mut self, issuer: IssuerId) -> &mut Self {
        self.trusted_issuers.insert(issuer);
        self
    }

    pub fn register_instruction(&mut self, instr: InstructionId, issuer: IssuerId) -> &mut Self {
        self.instruction_issuer.insert(instr, issuer);
        self
    }

    /// Set the robust-declassification floors gating `return_endorsed`/`grant_override`.
    /// Platforms MUST call this with real floors; the default (`Untrusted`/`Untrusted`)
    /// leaves the levers ungated (V2 behavior).
    pub fn set_lever_floors(&mut self, floor: IntegLevel, inspect_floor: IntegLevel) -> &mut Self {
        self.lever_integ_floor = floor;
        self.lever_integ_inspect_floor = inspect_floor;
        self
    }

    pub fn build(self) -> BackgroundTheory {
        BackgroundTheory {
            tools: self.tools,
            allow_ceiling: self.allow_ceiling,
            inspect_ceiling: self.inspect_ceiling,
            trusted_issuers: self.trusted_issuers,
            instruction_issuer: self.instruction_issuer,
            lever_integ_floor: self.lever_integ_floor,
            lever_integ_inspect_floor: self.lever_integ_inspect_floor,
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
    fn tool_metadata_lookup() {
        let mut builder = BackgroundTheoryBuilder::new();
        let meta = ToolMetadata {
            capabilities: VecSet::from([CapKind::FilesystemRead]),
            egress: VecSet::from([EgressKind::NetworkExternal]),
            conf_floor: ConfLevel::Internal,
            output_bounded: false,
            issuer: IssuerId::new("trusted"),
            integ_floor: IntegLevel::Untrusted,
            integ_inspect_floor: IntegLevel::Untrusted,
            output_integ: IntegLevel::Attested,
        };
        builder.register_tool(ToolId::new("read_file"), meta.clone());
        let bg = builder.build();

        let found = bg.tool_metadata(&ToolId::new("read_file")).unwrap();
        assert_eq!(found, meta);
        assert!(bg.tool_metadata(&ToolId::new("nonexistent")).is_none());
    }

    #[test]
    fn tool_metadata_roundtrips_integrity_fields() {
        let mut builder = BackgroundTheoryBuilder::new();
        let meta = ToolMetadata {
            capabilities: VecSet::new(),
            egress: VecSet::new(),
            conf_floor: ConfLevel::Public,
            output_bounded: true,
            issuer: IssuerId::new("trusted"),
            integ_floor: IntegLevel::Trusted,
            integ_inspect_floor: IntegLevel::Standard,
            output_integ: IntegLevel::Untrusted,
        };
        builder.register_tool(ToolId::new("web_fetch"), meta.clone());
        let bg = builder.build();

        let found = bg.tool_metadata(&ToolId::new("web_fetch")).unwrap();
        assert_eq!(found.integ_floor, IntegLevel::Trusted);
        assert_eq!(found.integ_inspect_floor, IntegLevel::Standard);
        assert_eq!(found.output_integ, IntegLevel::Untrusted);
    }

    #[test]
    fn lever_floors_default_to_untrusted() {
        let bg = BackgroundTheoryBuilder::new().build();
        assert_eq!(bg.lever_integ_floor(), IntegLevel::Untrusted);
        assert_eq!(bg.lever_integ_inspect_floor(), IntegLevel::Untrusted);
    }

    #[test]
    fn set_lever_floors_overrides_default() {
        let mut b = BackgroundTheoryBuilder::new();
        b.set_lever_floors(IntegLevel::Trusted, IntegLevel::Standard);
        let bg = b.build();
        assert_eq!(bg.lever_integ_floor(), IntegLevel::Trusted);
        assert_eq!(bg.lever_integ_inspect_floor(), IntegLevel::Standard);
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
    fn ceiling_band_boundaries() {
        let mut b = BackgroundTheoryBuilder::new();
        b.set_egress_ceilings(
            EgressKind::NetworkExternal,
            Some(ConfLevel::Internal),
            Some(ConfLevel::Sensitive),
        );
        let bg = b.build();
        assert_eq!(bg.flow_mode(ConfLevel::Public, EgressKind::NetworkExternal), FlowMode::Allow);
        assert_eq!(bg.flow_mode(ConfLevel::Internal, EgressKind::NetworkExternal), FlowMode::Allow);
        assert_eq!(bg.flow_mode(ConfLevel::Sensitive, EgressKind::NetworkExternal), FlowMode::Inspect);
        assert_eq!(bg.flow_mode(ConfLevel::Restricted, EgressKind::NetworkExternal), FlowMode::Deny);
        assert_eq!(bg.flow_mode(ConfLevel::Public, EgressKind::Ipc), FlowMode::Deny);
    }

    #[test]
    fn empty_inspect_band_is_coherent() {
        let mut b = BackgroundTheoryBuilder::new();
        b.set_egress_ceilings(
            EgressKind::Ipc,
            Some(ConfLevel::Sensitive),
            Some(ConfLevel::Internal),
        );
        let bg = b.build();
        assert_eq!(bg.flow_mode(ConfLevel::Internal, EgressKind::Ipc), FlowMode::Allow);
        assert_eq!(bg.flow_mode(ConfLevel::Restricted, EgressKind::Ipc), FlowMode::Deny);
    }

    #[test]
    fn from_matrix_roundtrip() {
        let b = BackgroundTheoryBuilder::from_matrix(&[
            (ConfLevel::Public, EgressKind::NetworkExternal, FlowMode::Allow),
            (ConfLevel::Internal, EgressKind::NetworkExternal, FlowMode::Inspect),
            (ConfLevel::Sensitive, EgressKind::NetworkExternal, FlowMode::Deny),
        ])
        .unwrap();
        let bg = b.build();
        assert_eq!(bg.flow_mode(ConfLevel::Public, EgressKind::NetworkExternal), FlowMode::Allow);
        assert_eq!(bg.flow_mode(ConfLevel::Internal, EgressKind::NetworkExternal), FlowMode::Inspect);
        assert_eq!(bg.flow_mode(ConfLevel::Sensitive, EgressKind::NetworkExternal), FlowMode::Deny);
        assert_eq!(bg.flow_mode(ConfLevel::Restricted, EgressKind::NetworkExternal), FlowMode::Deny);
    }

    #[test]
    fn from_matrix_rejects_non_monotone() {
        let r = BackgroundTheoryBuilder::from_matrix(&[
            (ConfLevel::Public, EgressKind::NetworkExternal, FlowMode::Deny),
            (ConfLevel::Internal, EgressKind::NetworkExternal, FlowMode::Allow),
        ]);
        assert_eq!(r.err(), Some(FlowMatrixError::NonMonotone));
    }
}
