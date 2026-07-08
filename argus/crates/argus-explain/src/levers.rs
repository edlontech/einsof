use argus_kernel::{
    declass_weight, integ_weight, AgentId, BackgroundTheory, CapKind, ConfLevel,
    ConformanceOracle, IntegLevel, KernelError, KernelState,
};

use crate::invoke::{integ_mode, IntegMode};
use crate::report::{ExplainReport, GateCheck, IntegCheckOutcome, LeverGateFinding, Rescue};

/// Mirror of `transitions::return_endorsed`'s robust-declassification lever gate: every level
/// the CHILD holds must clear the shared lever floor, or sit in the inspect band vouched by
/// `return_conforms` -- already required as a precondition, so the vouch is deterministically
/// true whenever this loop runs (mirrored anyway for shape fidelity with the design's graduated
/// gate). Coverage (`DeclarationNotCovering`) is a caller-declaration error, reported verdict-only
/// -- no per-level findings, the same treatment `explain_invoke` gives `AttestationInvalid`.
pub fn explain_return_endorsed<F: ConformanceOracle>(
    st: &KernelState,
    bg: &BackgroundTheory,
    conformance: &F,
    child: &AgentId,
    parent: &AgentId,
    clvl: ConfLevel,
    ilvl: IntegLevel,
) -> ExplainReport {
    let mut report = ExplainReport {
        verdict: None,
        missing_caps: Vec::new(),
        findings: Vec::new(),
        integ_findings: Vec::new(),
        lever_findings: Vec::new(),
        authorizer_denied: false,
    };
    let precondition = if st.agent_parent.get(child) != Some(parent) {
        Some(KernelError::NotDirectChild)
    } else if !st.agent_active.contains(child) || !st.agent_active.contains(parent) {
        Some(KernelError::AgentInactive)
    } else if st.in_flight.set_nonempty(child) {
        Some(KernelError::ChildHasInFlight)
    } else if !st.agent_cap.set_contains(child, &CapKind::Declassify) {
        Some(KernelError::CapabilityMissing)
    } else if !conformance.return_conforms(child, parent, st, bg) {
        Some(KernelError::NotConforming)
    } else {
        None
    };
    if let Some(e) = precondition {
        report.verdict = Some(e);
        return report;
    }

    let floor = bg.lever_integ_floor();
    let inspect_floor = bg.lever_integ_inspect_floor();
    let vouched = conformance.return_conforms(child, parent, st, bg);
    let child_integ = st.integ_levels.get_set_or_empty(child);
    for li in 0..child_integ.len() {
        let level = *child_integ.at(li);
        let mode = integ_mode(floor, inspect_floor, level);
        let outcome = match mode {
            IntegMode::Allow => IntegCheckOutcome::Allowed,
            IntegMode::Inspect if vouched => IntegCheckOutcome::AllowedViaInspect,
            IntegMode::Inspect | IntegMode::Deny => IntegCheckOutcome::Denied,
        };
        let mut rescues = Vec::new();
        if outcome == IntegCheckOutcome::Denied {
            match mode {
                IntegMode::Inspect => rescues.push(Rescue::ReturnConformancePass {
                    child: child.0.clone(),
                    parent: parent.0.clone(),
                }),
                IntegMode::Deny => rescues.push(Rescue::RaiseIntegrity { agent: child.0.clone() }),
                IntegMode::Allow => {}
            }
            rescues.push(Rescue::LeverFloorRelabel { current_floor: floor });
        }
        report.lever_findings.push(LeverGateFinding {
            check: GateCheck::ChildIntegVsLeverFloor,
            level,
            floor,
            inspect_floor,
            outcome,
            rescues,
        });
    }
    if report.denied_lever_findings().next().is_some() {
        report.verdict = Some(KernelError::LeverIntegrityDenied);
        return report;
    }

    let child_taint = st.taint_levels.get_set_or_empty(child);
    let mut conf_denied = false;
    for ci in 0..child_taint.len() {
        let level = *child_taint.at(ci);
        if !level.le(clvl) {
            conf_denied = true;
        }
    }
    let mut integ_denied = false;
    for ii in 0..child_integ.len() {
        let level = *child_integ.at(ii);
        if !ilvl.le(level) {
            integ_denied = true;
        }
    }
    if conf_denied || integ_denied {
        report.verdict = Some(KernelError::DeclarationNotCovering);
        return report;
    }

    let weight = declass_weight(clvl) + integ_weight(ilvl);
    report.verdict =
        if !st.affordable(parent, weight) { Some(KernelError::BudgetExhausted) } else { None };
    report
}

/// Mirror of `transitions::grant_override`'s lever gate: the GRANTER's held integrity must
/// clear the shared lever floor STRICT -- no inspect band, no vouch (`grant_override` has no
/// conformance object to vouch a near-miss granter with). `inspect_floor` is pinned to `floor`
/// so `integ_mode` collapses to a plain Allow/Deny, matching the kernel exactly. `tool` plays no
/// gating role in the real transition (it only tags the armed grant on success), so it is not a
/// parameter here.
pub fn explain_grant_override(
    st: &KernelState,
    bg: &BackgroundTheory,
    granter: &AgentId,
    target: &AgentId,
    level: ConfLevel,
) -> ExplainReport {
    let mut report = ExplainReport {
        verdict: None,
        missing_caps: Vec::new(),
        findings: Vec::new(),
        integ_findings: Vec::new(),
        lever_findings: Vec::new(),
        authorizer_denied: false,
    };
    let precondition = if !st.agent_active.contains(granter) || !st.agent_active.contains(target) {
        Some(KernelError::AgentInactive)
    } else if !st.agent_cap.set_contains(granter, &CapKind::GrantOverride) {
        Some(KernelError::CapabilityMissing)
    } else {
        None
    };
    if let Some(e) = precondition {
        report.verdict = Some(e);
        return report;
    }

    let floor = bg.lever_integ_floor();
    let granter_integ = st.integ_levels.get_set_or_empty(granter);
    for i in 0..granter_integ.len() {
        let level = *granter_integ.at(i);
        let mode = integ_mode(floor, floor, level);
        let outcome = match mode {
            IntegMode::Allow => IntegCheckOutcome::Allowed,
            IntegMode::Inspect | IntegMode::Deny => IntegCheckOutcome::Denied,
        };
        let mut rescues = Vec::new();
        if outcome == IntegCheckOutcome::Denied {
            rescues.push(Rescue::RaiseIntegrity { agent: granter.0.clone() });
            rescues.push(Rescue::LeverFloorRelabel { current_floor: floor });
        }
        report.lever_findings.push(LeverGateFinding {
            check: GateCheck::GranterIntegVsLeverFloor,
            level,
            floor,
            inspect_floor: floor,
            outcome,
            rescues,
        });
    }
    if report.denied_lever_findings().next().is_some() {
        report.verdict = Some(KernelError::LeverIntegrityDenied);
        return report;
    }

    let weight = declass_weight(level);
    if !st.affordable(granter, weight) {
        report.verdict = Some(KernelError::BudgetExhausted);
        return report;
    }
    if st.in_flight.set_nonempty(target) {
        report.verdict = Some(KernelError::TargetHasInFlight);
    }
    report
}

#[cfg(test)]
mod tests {
    use super::*;
    use argus_kernel::{
        transitions, BackgroundTheoryBuilder, InvocationId, IssuerId, KernelState, ToolId, VecSet,
    };

    struct ConformsAll;
    impl ConformanceOracle for ConformsAll {
        fn conforms(
            &self,
            _: &AgentId,
            _: &ToolId,
            _: &InvocationId,
            _: &KernelState,
            _: &BackgroundTheory,
        ) -> bool {
            true
        }
        fn return_conforms(&self, _: &AgentId, _: &AgentId, _: &KernelState, _: &BackgroundTheory) -> bool {
            true
        }
    }
    struct ConformsNone;
    impl ConformanceOracle for ConformsNone {
        fn conforms(
            &self,
            _: &AgentId,
            _: &ToolId,
            _: &InvocationId,
            _: &KernelState,
            _: &BackgroundTheory,
        ) -> bool {
            false
        }
        fn return_conforms(&self, _: &AgentId, _: &AgentId, _: &KernelState, _: &BackgroundTheory) -> bool {
            false
        }
    }

    fn return_fixture(lever_floor: IntegLevel, held: IntegLevel) -> (KernelState, BackgroundTheory) {
        let mut st = KernelState::initial();
        let child = AgentId::new("c");
        let parent = AgentId::new("p");
        st.agent_active.insert(child.clone());
        st.agent_active.insert(parent.clone());
        st.agent_parent.insert(parent.clone(), AgentId::root());
        st.agent_parent.insert(child.clone(), parent.clone());
        st.agent_cap.insert(child.clone(), VecSet::from([CapKind::Declassify]));
        st.integ_levels.insert(child, VecSet::from([held]));

        let mut b = BackgroundTheoryBuilder::new();
        b.trust_issuer(IssuerId::new("trusted"));
        b.set_lever_floors(lever_floor, lever_floor);
        (st, b.build())
    }

    fn agree_return_endorsed(
        st: &KernelState,
        bg: &BackgroundTheory,
        conforms: bool,
        clvl: ConfLevel,
        ilvl: IntegLevel,
    ) -> ExplainReport {
        let (conformance_ok, conformance_bad) = (ConformsAll, ConformsNone);
        let report = if conforms {
            explain_return_endorsed(st, bg, &conformance_ok, &AgentId::new("c"), &AgentId::new("p"), clvl, ilvl)
        } else {
            explain_return_endorsed(st, bg, &conformance_bad, &AgentId::new("c"), &AgentId::new("p"), clvl, ilvl)
        };
        let real = if conforms {
            transitions::return_endorsed(
                st.clone(), bg, &conformance_ok, AgentId::new("c"), AgentId::new("p"), clvl, ilvl,
            )
        } else {
            transitions::return_endorsed(
                st.clone(), bg, &conformance_bad, AgentId::new("c"), AgentId::new("p"), clvl, ilvl,
            )
        };
        match &real {
            Ok(_) => assert_eq!(report.verdict, None),
            Err(e) => assert_eq!(report.verdict, Some(e.clone())),
        }
        report
    }

    #[test]
    fn child_below_lever_floor_denied() {
        let (st, bg) = return_fixture(IntegLevel::Trusted, IntegLevel::Untrusted);
        let report = agree_return_endorsed(&st, &bg, true, ConfLevel::Public, IntegLevel::Attested);
        assert_eq!(report.verdict, Some(KernelError::LeverIntegrityDenied));
        let f = report.denied_lever_findings().next().unwrap();
        assert_eq!(f.check, GateCheck::ChildIntegVsLeverFloor);
        assert!(f.rescues.contains(&Rescue::RaiseIntegrity { agent: "c".into() }));
        assert!(f.rescues.contains(&Rescue::LeverFloorRelabel { current_floor: IntegLevel::Trusted }));
    }

    #[test]
    fn child_at_lever_floor_allowed() {
        let (st, bg) = return_fixture(IntegLevel::Trusted, IntegLevel::Trusted);
        let report = agree_return_endorsed(&st, &bg, true, ConfLevel::Public, IntegLevel::Trusted);
        assert_eq!(report.verdict, None);
    }

    #[test]
    fn declaration_not_covering_denied() {
        let mut st = KernelState::initial();
        let child = AgentId::new("c");
        let parent = AgentId::new("p");
        st.agent_active.insert(child.clone());
        st.agent_active.insert(parent.clone());
        st.agent_parent.insert(parent.clone(), AgentId::root());
        st.agent_parent.insert(child.clone(), parent.clone());
        st.agent_cap.insert(child.clone(), VecSet::from([CapKind::Declassify]));
        st.taint_levels.insert(child, VecSet::from([ConfLevel::Restricted]));
        let bg = BackgroundTheoryBuilder::new().build();

        let report = agree_return_endorsed(&st, &bg, true, ConfLevel::Public, IntegLevel::Attested);
        assert_eq!(report.verdict, Some(KernelError::DeclarationNotCovering));
    }

    fn agree_grant_override(st: &KernelState, bg: &BackgroundTheory, level: ConfLevel) -> ExplainReport {
        let report = explain_grant_override(st, bg, &AgentId::new("granter"), &AgentId::new("target"), level);
        let real = transitions::grant_override(
            st.clone(), bg, AgentId::new("granter"), AgentId::new("target"), ToolId::new("t1"), level,
        );
        match &real {
            Ok(_) => assert_eq!(report.verdict, None),
            Err(e) => assert_eq!(report.verdict, Some(e.clone())),
        }
        report
    }

    #[test]
    fn granter_below_lever_floor_denied_strict() {
        let mut st = KernelState::initial();
        let granter = AgentId::new("granter");
        let target = AgentId::new("target");
        st.agent_active.insert(granter.clone());
        st.agent_active.insert(target);
        st.agent_cap.insert(granter.clone(), VecSet::from([CapKind::GrantOverride]));
        st.integ_levels.insert(granter, VecSet::from([IntegLevel::Untrusted]));
        let mut b = BackgroundTheoryBuilder::new();
        b.set_lever_floors(IntegLevel::Trusted, IntegLevel::Trusted);
        let bg = b.build();

        let report = agree_grant_override(&st, &bg, ConfLevel::Public);
        assert_eq!(report.verdict, Some(KernelError::LeverIntegrityDenied));
        let f = report.denied_lever_findings().next().unwrap();
        assert_eq!(f.check, GateCheck::GranterIntegVsLeverFloor);
        assert_eq!(f.floor, f.inspect_floor, "strict: no inspect band for grant_override");
        assert!(f.rescues.contains(&Rescue::RaiseIntegrity { agent: "granter".into() }));
    }

    #[test]
    fn granter_at_lever_floor_allowed() {
        let mut st = KernelState::initial();
        let granter = AgentId::new("granter");
        let target = AgentId::new("target");
        st.agent_active.insert(granter.clone());
        st.agent_active.insert(target);
        st.agent_cap.insert(granter, VecSet::from([CapKind::GrantOverride]));
        let bg = BackgroundTheoryBuilder::new().build();

        let report = agree_grant_override(&st, &bg, ConfLevel::Public);
        assert_eq!(report.verdict, None);
    }

    #[test]
    fn granter_missing_cap_short_circuits() {
        let mut st = KernelState::initial();
        let granter = AgentId::new("granter");
        let target = AgentId::new("target");
        st.agent_active.insert(granter);
        st.agent_active.insert(target);
        let bg = BackgroundTheoryBuilder::new().build();

        let report = agree_grant_override(&st, &bg, ConfLevel::Public);
        assert_eq!(report.verdict, Some(KernelError::CapabilityMissing));
        assert!(report.lever_findings.is_empty());
    }
}
