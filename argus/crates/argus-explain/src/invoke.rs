use argus_kernel::{
    AgentId, AuthorizerOracle, BackgroundTheory, ConfLevel, ContentGateOracle, EgressKind,
    FlowMode, IntegLevel, InvocationId, KernelError, KernelState, ToolId, VecSet,
};

use crate::report::{
    CheckOutcome, ExplainReport, GateCheck, GateFinding, IntegCheckOutcome, IntegGateFinding,
    Rescue,
};

/// Evaluate one (level, egress) pair exactly as `flow_decision` does, but producing a
/// finding with rescue counterfactuals instead of an accumulator update.
#[allow(clippy::too_many_arguments)]
pub(crate) fn gate_finding(
    bg: &BackgroundTheory,
    st: &KernelState,
    gate_passes: bool,
    check: GateCheck,
    agent: &AgentId,
    tool: &ToolId,
    level: ConfLevel,
    egress: EgressKind,
    floor_of_new_tool: Option<ConfLevel>,
) -> GateFinding {
    let mode = bg.flow_mode(level, egress);
    let outcome = match mode {
        FlowMode::Allow => CheckOutcome::Allowed,
        FlowMode::Inspect if gate_passes => CheckOutcome::AllowedViaInspect,
        FlowMode::Inspect => CheckOutcome::Denied,
        FlowMode::Deny
            if st.has_flow_override(agent, tool, level)
                && !st.override_consumed(agent, tool, level) =>
        {
            CheckOutcome::RescuedByOverride
        }
        FlowMode::Deny => CheckOutcome::Denied,
    };
    let mut rescues = Vec::new();
    if outcome == CheckOutcome::Denied {
        rescues.push(Rescue::CeilingRaise { egress, to_level: level });
        if mode == FlowMode::Inspect {
            rescues.push(Rescue::ContentGatePass { tool: tool.0.clone() });
        } else {
            rescues.push(Rescue::OverrideGrant {
                agent: agent.0.clone(),
                tool: tool.0.clone(),
                level,
            });
        }
        if floor_of_new_tool == Some(level) {
            rescues.push(Rescue::ToolRelabel { tool: tool.0.clone(), current_floor: level });
        }
    }
    GateFinding { check, tool: tool.0.clone(), level, egress, mode, outcome, rescues }
}

/// Three-way integrity mode (dual of `FlowMode`, computed directly from the two floors --
/// no oracle involved, mirroring the branch structure `integ_decision` folds into a bool).
/// `pub(crate)`: shared with `levers.rs`, whose lever gates use the same three-way branch.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum IntegMode {
    Allow,
    Inspect,
    Deny,
}

pub(crate) fn integ_mode(floor: IntegLevel, inspect_floor: IntegLevel, level: IntegLevel) -> IntegMode {
    if floor.le(level) {
        IntegMode::Allow
    } else if inspect_floor.le(level) {
        IntegMode::Inspect
    } else {
        IntegMode::Deny
    }
}

/// Evaluate one (level, floor) integrity pair exactly as `integ_decision` does, but producing
/// a finding with rescue counterfactuals instead of a bare bool. `floor`/`inspect_floor` always
/// belong to `tool` (CHECK 4a/4b/4c and the return/degrade mirrors all gate a tool's own
/// metadata), so a floor relabel is always an available rescue; no override arm exists for
/// integrity -- endorsement is the only way up.
#[allow(clippy::too_many_arguments)]
pub(crate) fn integ_gate_finding(
    content_gate: &impl ContentGateOracle,
    st: &KernelState,
    bg: &BackgroundTheory,
    check: GateCheck,
    agent: &AgentId,
    tool: &ToolId,
    vouch_inv: &InvocationId,
    floor: IntegLevel,
    inspect_floor: IntegLevel,
    level: IntegLevel,
) -> IntegGateFinding {
    let mode = integ_mode(floor, inspect_floor, level);
    let outcome = match mode {
        IntegMode::Allow => IntegCheckOutcome::Allowed,
        IntegMode::Inspect if content_gate.passes(agent, tool, vouch_inv, st, bg) => {
            IntegCheckOutcome::AllowedViaInspect
        }
        IntegMode::Inspect | IntegMode::Deny => IntegCheckOutcome::Denied,
    };
    let mut rescues = Vec::new();
    if outcome == IntegCheckOutcome::Denied {
        match mode {
            IntegMode::Inspect => rescues.push(Rescue::ContentGatePass { tool: tool.0.clone() }),
            IntegMode::Deny => rescues.push(Rescue::EndorseIngestion { tool: tool.0.clone() }),
            IntegMode::Allow => {}
        }
        rescues.push(Rescue::IntegFloorRelabel { tool: tool.0.clone(), current_floor: floor });
    }
    IntegGateFinding { check, tool: tool.0.clone(), level, floor, inspect_floor, outcome, rescues }
}

#[allow(clippy::too_many_arguments)]
pub fn explain_invoke<A: AuthorizerOracle, C: ContentGateOracle>(
    st: &KernelState,
    bg: &BackgroundTheory,
    authorizer: &A,
    content_gate: &C,
    agent: &AgentId,
    tool: &ToolId,
    inv: &InvocationId,
    attested_egress: &VecSet<EgressKind>,
) -> ExplainReport {
    let mut report = ExplainReport {
        verdict: None,
        missing_caps: Vec::new(),
        findings: Vec::new(),
        integ_findings: Vec::new(),
        lever_findings: Vec::new(),
        authorizer_denied: false,
    };
    let precondition = if !st.agent_active.contains(agent) {
        Some(KernelError::AgentInactive)
    } else if *agent == AgentId::root() {
        Some(KernelError::RootNotAllowed)
    } else if !st.tool_registered.contains(tool) {
        Some(KernelError::ToolNotRegistered)
    } else if st.invocation_tool.contains_key(inv) {
        Some(KernelError::InvocationExists)
    } else if st.in_flight.any_value_contains(inv) {
        Some(KernelError::InvocationInFlight)
    } else if st.invocation_used.contains(inv) {
        Some(KernelError::InvocationReplayed)
    } else {
        None
    };
    if let Some(e) = precondition {
        report.verdict = Some(e);
        return report;
    }
    let Some(tool_meta) = bg.tool_metadata(tool) else {
        report.verdict = Some(KernelError::ToolNotInTheory);
        return report;
    };
    let conf_floor = tool_meta.conf_floor;

    // Narrowing: the attested egress cannot exceed the tool's declared set. Coverage: an
    // egress-bearing tool cannot be admitted on an empty attestation.
    let mut narrowing_violated = false;
    for i in 0..attested_egress.len() {
        if !tool_meta.egress.contains(attested_egress.at(i)) {
            narrowing_violated = true;
        }
    }
    let coverage_violated = !tool_meta.egress.is_empty() && attested_egress.is_empty();
    if narrowing_violated || coverage_violated {
        report.verdict = Some(KernelError::AttestationInvalid);
        return report;
    }

    for i in 0..tool_meta.capabilities.len() {
        let cap = *tool_meta.capabilities.at(i);
        if !st.agent_cap.set_contains(agent, &cap) {
            report.missing_caps.push(cap);
        }
    }

    // CHECK 2a/2c vouch the NEW invocation's content-gate verdict.
    let new_tool_gate = content_gate.passes(agent, tool, inv, st, bg);

    // CHECK 2a
    let spec_taint = st.speculative_taint(agent, bg);
    for li in 0..spec_taint.len() {
        let level = *spec_taint.at(li);
        for ei in 0..attested_egress.len() {
            report.findings.push(gate_finding(
                bg, st, new_tool_gate, GateCheck::SpecTaintVsNewEgress,
                agent, tool, level, *attested_egress.at(ei), None,
            ));
        }
    }

    // CHECK 2b. The vouch is the IN-FLIGHT invocation's content-gate verdict (re-examined
    // against the new floor), computed per flight invocation -- not per flight tool. The
    // egress source is the flight invocation's STORED attestation, not the tool's static set.
    let flights = st.in_flight.get_set_or_empty(agent);
    for fi in 0..flights.len() {
        let flight_inv = flights.at(fi);
        let Some(flight_tool) = st.invocation_tool.get_cloned(flight_inv) else {
            continue;
        };
        let egress = st.invocation_egress.get_set_or_empty(flight_inv);
        let flight_gate = content_gate.passes(agent, &flight_tool, flight_inv, st, bg);
        for ei in 0..egress.len() {
            report.findings.push(gate_finding(
                bg, st, flight_gate, GateCheck::NewFloorVsInFlight,
                agent, &flight_tool, conf_floor, *egress.at(ei), Some(conf_floor),
            ));
        }
    }

    // CHECK 2c
    for ei in 0..attested_egress.len() {
        report.findings.push(gate_finding(
            bg, st, new_tool_gate, GateCheck::SelfFloor,
            agent, tool, conf_floor, *attested_egress.at(ei), Some(conf_floor),
        ));
    }

    report.authorizer_denied = !authorizer.allows(agent, tool, inv, st, bg);

    // CHECK 4a: every speculative-integrity level the agent carries against the new tool's
    // floor, vouched by the NEW invocation.
    let spec_integ = st.speculative_integ(agent, bg);
    for li in 0..spec_integ.len() {
        let level = *spec_integ.at(li);
        report.integ_findings.push(integ_gate_finding(
            content_gate, st, bg, GateCheck::SpecIntegVsNewFloor,
            agent, tool, inv, tool_meta.integ_floor, tool_meta.integ_inspect_floor, level,
        ));
    }

    // CHECK 4b: the new tool's emission against every in-flight tool's floor, vouched by the
    // IN-FLIGHT invocation whose floor is being crossed.
    for fi in 0..flights.len() {
        let flight_inv = flights.at(fi);
        let Some(flight_tool) = st.invocation_tool.get_cloned(flight_inv) else {
            continue;
        };
        let Some(flight_meta) = bg.tool_metadata(&flight_tool) else {
            continue;
        };
        report.integ_findings.push(integ_gate_finding(
            content_gate, st, bg, GateCheck::NewEmissionVsInFlightFloor,
            agent, &flight_tool, flight_inv,
            flight_meta.integ_floor, flight_meta.integ_inspect_floor, tool_meta.output_integ,
        ));
    }

    // CHECK 4c: the new tool's own emission against its own floor, vouched by the NEW
    // invocation.
    report.integ_findings.push(integ_gate_finding(
        content_gate, st, bg, GateCheck::SelfEmissionVsOwnFloor,
        agent, tool, inv,
        tool_meta.integ_floor, tool_meta.integ_inspect_floor, tool_meta.output_integ,
    ));

    report.verdict = if !report.missing_caps.is_empty() {
        Some(KernelError::CapabilityMissing)
    } else if report.denied_findings().next().is_some() {
        Some(KernelError::FlowGateBlocked)
    } else if report.authorizer_denied {
        Some(KernelError::AuthorizerDenied)
    } else if report.denied_integ_findings().next().is_some() {
        Some(KernelError::IntegrityFloorDenied)
    } else {
        None
    };
    report
}

#[cfg(test)]
mod tests {
    use super::*;
    use argus_kernel::{
        AgentId, BackgroundTheoryBuilder, CapKind, ConfLevel, EgressKind, IntegLevel,
        InvocationId, IssuerId, KernelError, KernelState, ToolId, ToolMetadata, VecSet,
    };
    use argus_kernel::{transitions, AuthorizerOracle, BackgroundTheory, ContentGateOracle};

    struct ConstAuth(bool);
    impl AuthorizerOracle for ConstAuth {
        fn allows(&self, _: &AgentId, _: &ToolId, _: &InvocationId, _: &KernelState, _: &BackgroundTheory) -> bool {
            self.0
        }
    }
    struct ConstGate(bool);
    impl ContentGateOracle for ConstGate {
        fn passes(&self, _: &AgentId, _: &ToolId, _: &InvocationId, _: &KernelState, _: &BackgroundTheory) -> bool {
            self.0
        }
    }

    fn bg() -> BackgroundTheory {
        let mut b = BackgroundTheoryBuilder::new();
        b.trust_issuer(IssuerId::new("trusted"));
        b.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: VecSet::from([CapKind::NetworkEgress]),
                egress: VecSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        b.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Public), None);
        b.build()
    }

    fn tainted_agent_state() -> KernelState {
        let mut st = KernelState::initial();
        let a = AgentId::new("a1");
        st.agent_active.insert(a.clone());
        st.agent_parent.insert(a.clone(), AgentId::root());
        st.agent_cap.insert(a.clone(), VecSet::from([CapKind::NetworkEgress]));
        st.tool_registered.insert(ToolId::new("send_email"));
        st.taint_levels.insert(a, VecSet::from([ConfLevel::Sensitive]));
        st
    }

    fn agree(st: &KernelState, b: &BackgroundTheory, auth: bool, gate: bool) -> ExplainReport {
        let attested_egress = VecSet::from([EgressKind::NetworkExternal]);
        let report = explain_invoke(
            st, b, &ConstAuth(auth), &ConstGate(gate),
            &AgentId::new("a1"), &ToolId::new("send_email"), &InvocationId::new("i1"),
            &attested_egress,
        );
        let real = transitions::invoke_start(
            st.clone(), b, &ConstAuth(auth), &ConstGate(gate),
            AgentId::new("a1"), ToolId::new("send_email"), InvocationId::new("i1"),
            attested_egress,
        );
        match &real {
            Ok(_) => assert_eq!(report.verdict, None, "explain says deny, kernel succeeded"),
            Err(e) => assert_eq!(report.verdict, Some(e.clone()), "verdict mismatch"),
        }
        report
    }

    #[test]
    fn denied_flow_produces_finding_with_rescues() {
        let report = agree(&tainted_agent_state(), &bg(), true, false);
        assert_eq!(report.verdict, Some(KernelError::FlowGateBlocked));
        let denied: Vec<_> = report.denied_findings().collect();
        assert!(!denied.is_empty());
        let f = denied[0];
        assert_eq!(f.check, GateCheck::SpecTaintVsNewEgress);
        assert_eq!(f.level, ConfLevel::Sensitive);
        assert!(f.rescues.contains(&Rescue::OverrideGrant {
            agent: "a1".into(),
            tool: "send_email".into(),
            level: ConfLevel::Sensitive,
        }));
        assert!(f.rescues.contains(&Rescue::CeilingRaise {
            egress: EgressKind::NetworkExternal,
            to_level: ConfLevel::Sensitive,
        }));
    }

    #[test]
    fn clean_agent_succeeds_and_explain_agrees() {
        let mut st = tainted_agent_state();
        st.taint_levels.remove(&AgentId::new("a1"));
        let report = agree(&st, &bg(), true, false);
        assert_eq!(report.verdict, None);
        assert!(report.denied_findings().next().is_none());
    }

    #[test]
    fn missing_cap_verdict_precedes_flow_gate_but_findings_still_reported() {
        let mut st = tainted_agent_state();
        st.agent_cap.insert(AgentId::new("a1"), VecSet::new());
        let report = agree(&st, &bg(), true, false);
        assert_eq!(report.verdict, Some(KernelError::CapabilityMissing));
        assert_eq!(report.missing_caps, vec![CapKind::NetworkEgress]);
        assert!(report.denied_findings().next().is_some());
    }

    #[test]
    fn authorizer_denial_agrees_and_is_flagged() {
        let mut st = tainted_agent_state();
        st.taint_levels.remove(&AgentId::new("a1"));
        let report = agree(&st, &bg(), false, false);
        assert_eq!(report.verdict, Some(KernelError::AuthorizerDenied));
        assert!(report.authorizer_denied);
    }

    #[test]
    fn inactive_agent_short_circuits() {
        let st = KernelState::initial();
        let report = agree(&st, &bg(), true, true);
        assert_eq!(report.verdict, Some(KernelError::AgentInactive));
        assert!(report.findings.is_empty());
    }

    fn bg_integ_strict_deny() -> BackgroundTheory {
        let mut b = BackgroundTheoryBuilder::new();
        b.trust_issuer(IssuerId::new("trusted"));
        b.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: VecSet::from([CapKind::NetworkEgress]),
                egress: VecSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Trusted,
                integ_inspect_floor: IntegLevel::Trusted,
                output_integ: IntegLevel::Attested,
            },
        );
        b.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Public), None);
        b.build()
    }

    fn bg_integ_inspect_band() -> BackgroundTheory {
        let mut b = BackgroundTheoryBuilder::new();
        b.trust_issuer(IssuerId::new("trusted"));
        b.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: VecSet::from([CapKind::NetworkEgress]),
                egress: VecSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Trusted,
                integ_inspect_floor: IntegLevel::Standard,
                output_integ: IntegLevel::Attested,
            },
        );
        b.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Public), None);
        b.build()
    }

    fn integ_agent_state(level: IntegLevel) -> KernelState {
        let mut st = KernelState::initial();
        let a = AgentId::new("a1");
        st.agent_active.insert(a.clone());
        st.agent_parent.insert(a.clone(), AgentId::root());
        st.agent_cap.insert(a.clone(), VecSet::from([CapKind::NetworkEgress]));
        st.tool_registered.insert(ToolId::new("send_email"));
        st.integ_levels.insert(a, VecSet::from([level]));
        st
    }

    #[test]
    fn denied_integ_finding_carries_check_and_rescues() {
        let report = agree(&integ_agent_state(IntegLevel::Untrusted), &bg_integ_strict_deny(), true, false);
        assert_eq!(report.verdict, Some(KernelError::IntegrityFloorDenied));
        let f = report
            .denied_integ_findings()
            .find(|f| f.check == GateCheck::SpecIntegVsNewFloor)
            .unwrap();
        assert_eq!(f.level, IntegLevel::Untrusted);
        assert_eq!(f.floor, IntegLevel::Trusted);
        assert!(f.rescues.contains(&Rescue::EndorseIngestion { tool: "send_email".into() }));
        assert!(f.rescues.contains(&Rescue::IntegFloorRelabel {
            tool: "send_email".into(),
            current_floor: IntegLevel::Trusted,
        }));
    }

    #[test]
    fn integ_finding_denied_in_inspect_band_rescued_by_gate_pass() {
        let report = agree(&integ_agent_state(IntegLevel::Standard), &bg_integ_inspect_band(), true, false);
        assert_eq!(report.verdict, Some(KernelError::IntegrityFloorDenied));
        let f = report
            .denied_integ_findings()
            .find(|f| f.check == GateCheck::SpecIntegVsNewFloor)
            .unwrap();
        assert!(f.rescues.contains(&Rescue::ContentGatePass { tool: "send_email".into() }));
        assert!(f.rescues.contains(&Rescue::IntegFloorRelabel {
            tool: "send_email".into(),
            current_floor: IntegLevel::Trusted,
        }));
    }

    #[test]
    fn integ_inspect_band_passes_with_content_gate() {
        let report = agree(&integ_agent_state(IntegLevel::Standard), &bg_integ_inspect_band(), true, true);
        assert_eq!(report.verdict, None);
    }

    fn bg_integ_4b() -> BackgroundTheory {
        let mut b = BackgroundTheoryBuilder::new();
        b.trust_issuer(IssuerId::new("trusted"));
        b.register_tool(
            ToolId::new("send_email"),
            ToolMetadata {
                capabilities: VecSet::from([CapKind::NetworkEgress]),
                egress: VecSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Untrusted,
            },
        );
        b.register_tool(
            ToolId::new("flight_tool"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Trusted,
                integ_inspect_floor: IntegLevel::Trusted,
                output_integ: IntegLevel::Attested,
            },
        );
        b.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Public), None);
        b.build()
    }

    fn agent_with_flight_tool() -> KernelState {
        let mut st = KernelState::initial();
        let a = AgentId::new("a1");
        st.agent_active.insert(a.clone());
        st.agent_parent.insert(a.clone(), AgentId::root());
        st.agent_cap.insert(a.clone(), VecSet::from([CapKind::NetworkEgress]));
        st.tool_registered.insert(ToolId::new("send_email"));
        st.tool_registered.insert(ToolId::new("flight_tool"));
        let inv = InvocationId::new("flight-inv");
        st.invocation_tool.insert(inv.clone(), ToolId::new("flight_tool"));
        st.in_flight.insert_into(a, inv);
        st
    }

    #[test]
    fn check_4b_denies_new_emission_vs_in_flight_floor() {
        let report = agree(&agent_with_flight_tool(), &bg_integ_4b(), true, false);
        assert_eq!(report.verdict, Some(KernelError::IntegrityFloorDenied));
        let f = report
            .denied_integ_findings()
            .find(|f| f.check == GateCheck::NewEmissionVsInFlightFloor)
            .unwrap();
        assert_eq!(f.tool, "flight_tool");
        assert_eq!(f.level, IntegLevel::Untrusted);
    }
}
