use crate::collections::VecMap;
use crate::types::{AgentId, ConfLevel, EgressKind, Mode};

/// Immutable governed background. In the single-tenant model the adapter can never choose the
/// enforcement mode; the egress ceilings and root identity are held constant over any trace by the
/// Kav frame rule. Tool policy is no longer here — it is a per-invocation frozen snapshot.
///
/// Flow is exactly two per-egress option-ceilings (`allow` / `inspect`) read atomically, mirroring
/// `St.flow_allows`/`St.flow_inspects` over `ceilingAdmits`. A level flows freely iff it is at or
/// below the allow ceiling, and is inspectable iff at or below the inspect ceiling; absent = deny.
#[derive(Clone, Debug)]
pub struct BackgroundTheory {
    allow_ceiling: VecMap<EgressKind, ConfLevel>,
    inspect_ceiling: VecMap<EgressKind, ConfLevel>,
    mode: Mode,
    root_agent: AgentId,
}

impl BackgroundTheory {
    /// Derived flow-ALLOW: `level` is at or below the egress's allow ceiling (absent = deny).
    pub fn flow_allows(&self, level: ConfLevel, egress: EgressKind) -> bool {
        match self.allow_ceiling.get_cloned(&egress) {
            Some(c) => level.le(c),
            None => false,
        }
    }

    /// Derived flow-INSPECT: `level` is at or below the egress's inspect ceiling (absent = deny).
    pub fn flow_inspects(&self, level: ConfLevel, egress: EgressKind) -> bool {
        match self.inspect_ceiling.get_cloned(&egress) {
            Some(c) => level.le(c),
            None => false,
        }
    }

    pub fn mode(&self) -> Mode {
        self.mode
    }

    pub fn root_agent(&self) -> &AgentId {
        &self.root_agent
    }
}

pub struct BackgroundTheoryBuilder {
    allow_ceiling: VecMap<EgressKind, ConfLevel>,
    inspect_ceiling: VecMap<EgressKind, ConfLevel>,
    mode: Mode,
    root_agent: AgentId,
}

impl BackgroundTheoryBuilder {
    pub fn new() -> Self {
        Self {
            allow_ceiling: VecMap::new(),
            inspect_ceiling: VecMap::new(),
            mode: Mode::Enforce,
            root_agent: AgentId::root(),
        }
    }

    /// Set (or clear, with `None`) the two confidentiality ceilings for an egress kind.
    pub fn set_egress_ceilings(
        &mut self,
        egress: EgressKind,
        allow: Option<ConfLevel>,
        inspect: Option<ConfLevel>,
    ) -> &mut Self {
        match allow {
            Some(c) => {
                self.allow_ceiling.insert(egress, c);
            }
            None => {
                self.allow_ceiling.remove(&egress);
            }
        }
        match inspect {
            Some(c) => {
                self.inspect_ceiling.insert(egress, c);
            }
            None => {
                self.inspect_ceiling.remove(&egress);
            }
        }
        self
    }

    pub fn set_mode(&mut self, mode: Mode) -> &mut Self {
        self.mode = mode;
        self
    }

    pub fn set_root_agent(&mut self, root: AgentId) -> &mut Self {
        self.root_agent = root;
        self
    }

    pub fn build(self) -> BackgroundTheory {
        BackgroundTheory {
            allow_ceiling: self.allow_ceiling,
            inspect_ceiling: self.inspect_ceiling,
            mode: self.mode,
            root_agent: self.root_agent,
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
    fn absent_ceiling_denies_both_bands() {
        let bg = BackgroundTheoryBuilder::new().build();
        assert!(!bg.flow_allows(ConfLevel::Public, EgressKind::NetworkExternal));
        assert!(!bg.flow_inspects(ConfLevel::Public, EgressKind::NetworkExternal));
    }

    #[test]
    fn defaults_to_enforce_and_root() {
        let bg = BackgroundTheoryBuilder::new().build();
        assert_eq!(bg.mode(), Mode::Enforce);
        assert_eq!(bg.root_agent(), &AgentId::root());
    }

    #[test]
    fn mode_and_root_overridable() {
        let mut b = BackgroundTheoryBuilder::new();
        b.set_mode(Mode::Monitor).set_root_agent(AgentId::new("op"));
        let bg = b.build();
        assert_eq!(bg.mode(), Mode::Monitor);
        assert_eq!(bg.root_agent(), &AgentId::new("op"));
    }

    #[test]
    fn ceiling_bands_bound_the_two_relations() {
        let mut b = BackgroundTheoryBuilder::new();
        b.set_egress_ceilings(
            EgressKind::NetworkExternal,
            Some(ConfLevel::Internal),
            Some(ConfLevel::Sensitive),
        );
        let bg = b.build();
        // ALLOW band: at or below Internal.
        assert!(bg.flow_allows(ConfLevel::Public, EgressKind::NetworkExternal));
        assert!(bg.flow_allows(ConfLevel::Internal, EgressKind::NetworkExternal));
        assert!(!bg.flow_allows(ConfLevel::Sensitive, EgressKind::NetworkExternal));
        // INSPECT band: at or below Sensitive.
        assert!(bg.flow_inspects(ConfLevel::Sensitive, EgressKind::NetworkExternal));
        assert!(!bg.flow_inspects(ConfLevel::Restricted, EgressKind::NetworkExternal));
        // A different egress with no ceilings denies both.
        assert!(!bg.flow_allows(ConfLevel::Public, EgressKind::Ipc));
    }

    #[test]
    fn empty_inspect_band_is_coherent() {
        // Inspect ceiling below the allow ceiling = empty inspect band above allow; coherent.
        let mut b = BackgroundTheoryBuilder::new();
        b.set_egress_ceilings(
            EgressKind::Ipc,
            Some(ConfLevel::Sensitive),
            Some(ConfLevel::Internal),
        );
        let bg = b.build();
        assert!(bg.flow_allows(ConfLevel::Internal, EgressKind::Ipc));
        assert!(!bg.flow_allows(ConfLevel::Restricted, EgressKind::Ipc));
        assert!(!bg.flow_inspects(ConfLevel::Restricted, EgressKind::Ipc));
    }
}
