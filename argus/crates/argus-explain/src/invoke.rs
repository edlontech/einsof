use argus_kernel::{
    AgentId, AuthorizerOracle, BackgroundTheory, ConfLevel, ContentGateOracle, EgressKind,
    FlowMode, InvocationId, KernelError, KernelState, ToolId, VecSet,
};

use crate::report::{CheckOutcome, ExplainReport, GateCheck, GateFinding, Rescue};

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

pub fn explain_invoke<A: AuthorizerOracle, C: ContentGateOracle>(
    st: &KernelState,
    bg: &BackgroundTheory,
    authorizer: &A,
    content_gate: &C,
    agent: &AgentId,
    tool: &ToolId,
    inv: &InvocationId,
) -> ExplainReport {
    let mut report = ExplainReport {
        verdict: None,
        missing_caps: Vec::new(),
        findings: Vec::new(),
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

    for i in 0..tool_meta.capabilities.len() {
        let cap = *tool_meta.capabilities.at(i);
        if !st.agent_cap.set_contains(agent, &cap) {
            report.missing_caps.push(cap);
        }
    }

    let new_tool_gate = content_gate.passes(agent, tool, st, bg);

    // CHECK 2a
    let spec_taint = st.speculative_taint(agent, bg);
    for li in 0..spec_taint.len() {
        let level = *spec_taint.at(li);
        for ei in 0..tool_meta.egress.len() {
            report.findings.push(gate_finding(
                bg, st, new_tool_gate, GateCheck::SpecTaintVsNewEgress,
                agent, tool, level, *tool_meta.egress.at(ei), None,
            ));
        }
    }

    // CHECK 2b
    let flights = st.in_flight.get_set_or_empty(agent);
    for fi in 0..flights.len() {
        let Some(flight_tool) = st.invocation_tool.get_cloned(flights.at(fi)) else {
            continue;
        };
        let egress: VecSet<EgressKind> = match bg.tool_metadata(&flight_tool) {
            Some(m) => m.egress,
            None => VecSet::new(),
        };
        let flight_gate = content_gate.passes(agent, &flight_tool, st, bg);
        for ei in 0..egress.len() {
            report.findings.push(gate_finding(
                bg, st, flight_gate, GateCheck::NewFloorVsInFlight,
                agent, &flight_tool, conf_floor, *egress.at(ei), Some(conf_floor),
            ));
        }
    }

    // CHECK 2c
    for ei in 0..tool_meta.egress.len() {
        report.findings.push(gate_finding(
            bg, st, new_tool_gate, GateCheck::SelfFloor,
            agent, tool, conf_floor, *tool_meta.egress.at(ei), Some(conf_floor),
        ));
    }

    report.authorizer_denied = !authorizer.allows(agent, tool, st, bg);

    report.verdict = if !report.missing_caps.is_empty() {
        Some(KernelError::CapabilityMissing)
    } else if report.denied_findings().next().is_some() {
        Some(KernelError::FlowGateBlocked)
    } else if report.authorizer_denied {
        Some(KernelError::AuthorizerDenied)
    } else {
        None
    };
    report
}

#[cfg(test)]
mod tests {
    use super::*;
    use argus_kernel::{
        AgentId, BackgroundTheoryBuilder, CapKind, ConfLevel, EgressKind,
        InvocationId, IssuerId, KernelError, KernelState, ToolId, ToolMetadata, VecSet,
    };
    use argus_kernel::{transitions, AuthorizerOracle, BackgroundTheory, ContentGateOracle};

    struct ConstAuth(bool);
    impl AuthorizerOracle for ConstAuth {
        fn allows(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
            self.0
        }
    }
    struct ConstGate(bool);
    impl ContentGateOracle for ConstGate {
        fn passes(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
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
        let report = explain_invoke(
            st, b, &ConstAuth(auth), &ConstGate(gate),
            &AgentId::new("a1"), &ToolId::new("send_email"), &InvocationId::new("i1"),
        );
        let real = transitions::invoke_start(
            st.clone(), b, &ConstAuth(auth), &ConstGate(gate),
            AgentId::new("a1"), ToolId::new("send_email"), InvocationId::new("i1"),
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
}
