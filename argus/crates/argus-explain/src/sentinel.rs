use argus_kernel::{
    AgentId, BackgroundTheory, ConfLevel, ContentGateOracle, IntegLevel, KernelError, KernelState,
};

use crate::invoke::{gate_finding, integ_gate_finding};
use crate::report::{ExplainReport, GateCheck};

pub fn explain_sentinel_elevate_taint<C: ContentGateOracle>(
    st: &KernelState,
    bg: &BackgroundTheory,
    content_gate: &C,
    agent: &AgentId,
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
    if !st.agent_active.contains(agent) {
        report.verdict = Some(KernelError::AgentInactive);
        return report;
    }

    let mut missing_binding = false;
    let flights = st.in_flight.get_set_or_empty(agent);
    for fi in 0..flights.len() {
        let flight_inv = flights.at(fi);
        match st.invocation_tool.get_cloned(flight_inv) {
            Some(flight_tool) => {
                let egress = st.invocation_egress.get_set_or_empty(flight_inv);
                // Vouch is the agent's in-flight invocation being gated.
                let gate = content_gate.passes(agent, &flight_tool, flight_inv, st, bg);
                for ei in 0..egress.len() {
                    report.findings.push(gate_finding(
                        bg, st, gate, GateCheck::ElevatedVsInFlight,
                        agent, &flight_tool, level, *egress.at(ei), None,
                    ));
                }
            }
            None => missing_binding = true,
        }
    }

    report.verdict = if missing_binding {
        Some(KernelError::MissingToolBinding)
    } else if report.denied_findings().next().is_some() {
        Some(KernelError::FlowGateBlocked)
    } else {
        None
    };
    report
}

/// Mirror of `transitions::sentinel_degrade_integrity` (design §5.6): the platform reports
/// ingestion at `level`, gated against every in-flight tool's integrity floor. Graduated
/// (ALLOW / INSPECT+vouch), no override arm -- a blocked degrade means the Warden must hold
/// the ingestion until the in-flight invocation completes.
pub fn explain_sentinel_degrade_integrity<C: ContentGateOracle>(
    st: &KernelState,
    bg: &BackgroundTheory,
    content_gate: &C,
    agent: &AgentId,
    level: IntegLevel,
) -> ExplainReport {
    let mut report = ExplainReport {
        verdict: None,
        missing_caps: Vec::new(),
        findings: Vec::new(),
        integ_findings: Vec::new(),
        lever_findings: Vec::new(),
        authorizer_denied: false,
    };
    if !st.agent_active.contains(agent) {
        report.verdict = Some(KernelError::AgentInactive);
        return report;
    }

    let mut missing_binding = false;
    let flights = st.in_flight.get_set_or_empty(agent);
    for fi in 0..flights.len() {
        let flight_inv = flights.at(fi);
        match st.invocation_tool.get_cloned(flight_inv) {
            Some(flight_tool) => {
                let Some(flight_meta) = bg.tool_metadata(&flight_tool) else {
                    continue;
                };
                report.integ_findings.push(integ_gate_finding(
                    content_gate, st, bg, GateCheck::DegradeVsInFlightFloor,
                    agent, &flight_tool, flight_inv,
                    flight_meta.integ_floor, flight_meta.integ_inspect_floor, level,
                ));
            }
            None => missing_binding = true,
        }
    }

    report.verdict = if missing_binding {
        Some(KernelError::MissingToolBinding)
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
        transitions, AgentId, BackgroundTheory, BackgroundTheoryBuilder, ConfLevel,
        ContentGateOracle, EgressKind, IntegLevel, InvocationId, IssuerId, KernelError,
        KernelState, ToolId, ToolMetadata, VecSet,
    };

    struct ConstGate(bool);
    impl ContentGateOracle for ConstGate {
        fn passes(&self, _: &AgentId, _: &ToolId, _: &InvocationId, _: &KernelState, _: &BackgroundTheory) -> bool {
            self.0
        }
    }

    fn fixture() -> (KernelState, BackgroundTheory) {
        let mut st = KernelState::initial();
        let a = AgentId::new("a1");
        st.agent_active.insert(a.clone());
        st.in_flight.insert_into(a, InvocationId::new("i1"));
        st.invocation_tool.insert(InvocationId::new("i1"), ToolId::new("egress_tool"));
        st
            .invocation_egress
            .insert(InvocationId::new("i1"), VecSet::from([EgressKind::NetworkExternal]));

        let mut b = BackgroundTheoryBuilder::new();
        b.trust_issuer(IssuerId::new("trusted"));
        b.register_tool(
            ToolId::new("egress_tool"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::from([EgressKind::NetworkExternal]),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Untrusted,
                integ_inspect_floor: IntegLevel::Untrusted,
                output_integ: IntegLevel::Attested,
            },
        );
        (st, b.build())
    }

    fn agree(st: &KernelState, bg: &BackgroundTheory, level: ConfLevel, gate: bool) -> ExplainReport {
        let report = explain_sentinel_elevate_taint(
            st, bg, &ConstGate(gate), &AgentId::new("a1"), level,
        );
        let real = transitions::sentinel_elevate_taint(
            st.clone(), bg, &ConstGate(gate), AgentId::new("a1"), level,
        );
        match &real {
            Ok(_) => assert_eq!(report.verdict, None),
            Err(e) => assert_eq!(report.verdict, Some(e.clone())),
        }
        report
    }

    #[test]
    fn elevation_blocked_by_in_flight_egress() {
        let (st, bg) = fixture();
        let report = agree(&st, &bg, ConfLevel::Restricted, false);
        assert_eq!(report.verdict, Some(KernelError::FlowGateBlocked));
        let f = report.denied_findings().next().unwrap();
        assert_eq!(f.check, GateCheck::ElevatedVsInFlight);
        assert_eq!(f.level, ConfLevel::Restricted);
    }

    #[test]
    fn missing_binding_beats_flow_gate() {
        let (mut st, bg) = fixture();
        st.invocation_tool.remove(&InvocationId::new("i1"));
        let report = agree(&st, &bg, ConfLevel::Restricted, false);
        assert_eq!(report.verdict, Some(KernelError::MissingToolBinding));
    }

    #[test]
    fn no_flights_elevates_freely() {
        let (mut st, bg) = fixture();
        st.in_flight.remove(&AgentId::new("a1"));
        let report = agree(&st, &bg, ConfLevel::Restricted, false);
        assert_eq!(report.verdict, None);
    }

    fn degrade_fixture(inspect_floor: IntegLevel) -> (KernelState, BackgroundTheory) {
        let mut st = KernelState::initial();
        let a = AgentId::new("a1");
        st.agent_active.insert(a.clone());
        st.in_flight.insert_into(a, InvocationId::new("i1"));
        st.invocation_tool.insert(InvocationId::new("i1"), ToolId::new("destructive"));

        let mut b = BackgroundTheoryBuilder::new();
        b.trust_issuer(IssuerId::new("trusted"));
        b.register_tool(
            ToolId::new("destructive"),
            ToolMetadata {
                capabilities: VecSet::new(),
                egress: VecSet::new(),
                conf_floor: ConfLevel::Public,
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
                integ_floor: IntegLevel::Trusted,
                integ_inspect_floor: inspect_floor,
                output_integ: IntegLevel::Attested,
            },
        );
        (st, b.build())
    }

    fn agree_degrade(
        st: &KernelState,
        bg: &BackgroundTheory,
        level: IntegLevel,
        gate: bool,
    ) -> ExplainReport {
        let report = explain_sentinel_degrade_integrity(
            st, bg, &ConstGate(gate), &AgentId::new("a1"), level,
        );
        let real = transitions::sentinel_degrade_integrity(
            st.clone(), bg, &ConstGate(gate), AgentId::new("a1"), level,
        );
        match &real {
            Ok(_) => assert_eq!(report.verdict, None),
            Err(e) => assert_eq!(report.verdict, Some(e.clone())),
        }
        report
    }

    #[test]
    fn degrade_blocked_by_in_flight_floor() {
        let (st, bg) = degrade_fixture(IntegLevel::Trusted);
        let report = agree_degrade(&st, &bg, IntegLevel::Untrusted, false);
        assert_eq!(report.verdict, Some(KernelError::IntegrityFloorDenied));
        let f = report.denied_integ_findings().next().unwrap();
        assert_eq!(f.check, GateCheck::DegradeVsInFlightFloor);
        assert_eq!(f.tool, "destructive");
    }

    #[test]
    fn degrade_inspect_band_passes_with_gate() {
        let (st, bg) = degrade_fixture(IntegLevel::Standard);
        let report = agree_degrade(&st, &bg, IntegLevel::Standard, true);
        assert_eq!(report.verdict, None);
    }

    #[test]
    fn degrade_missing_binding_beats_integ_gate() {
        let (mut st, bg) = degrade_fixture(IntegLevel::Trusted);
        st.invocation_tool.remove(&InvocationId::new("i1"));
        let report = agree_degrade(&st, &bg, IntegLevel::Untrusted, false);
        assert_eq!(report.verdict, Some(KernelError::MissingToolBinding));
    }

    #[test]
    fn degrade_with_no_flights_succeeds() {
        let (mut st, bg) = degrade_fixture(IntegLevel::Trusted);
        st.in_flight.remove(&AgentId::new("a1"));
        let report = agree_degrade(&st, &bg, IntegLevel::Untrusted, false);
        assert_eq!(report.verdict, None);
    }
}
