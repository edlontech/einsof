use argus_kernel::{
    AgentId, BackgroundTheory, ConfLevel, ContentGateOracle, KernelError, KernelState, VecSet,
};

use crate::invoke::gate_finding;
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
        authorizer_denied: false,
    };
    if !st.agent_active.contains(agent) {
        report.verdict = Some(KernelError::AgentInactive);
        return report;
    }

    let mut missing_binding = false;
    let flights = st.in_flight.get_set_or_empty(agent);
    for fi in 0..flights.len() {
        match st.invocation_tool.get_cloned(flights.at(fi)) {
            Some(flight_tool) => {
                let egress = match bg.tool_metadata(&flight_tool) {
                    Some(m) => m.egress,
                    None => VecSet::new(),
                };
                let gate = content_gate.passes(agent, &flight_tool, st, bg);
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

#[cfg(test)]
mod tests {
    use super::*;
    use argus_kernel::{
        transitions, AgentId, BackgroundTheory, BackgroundTheoryBuilder, ConfLevel,
        ContentGateOracle, EgressKind, InvocationId, IssuerId, KernelError, KernelState,
        ToolId, ToolMetadata, VecSet,
    };

    struct ConstGate(bool);
    impl ContentGateOracle for ConstGate {
        fn passes(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
            self.0
        }
    }

    fn fixture() -> (KernelState, BackgroundTheory) {
        let mut st = KernelState::initial();
        let a = AgentId::new("a1");
        st.agent_active.insert(a.clone());
        st.in_flight.insert_into(a, InvocationId::new("i1"));
        st.invocation_tool.insert(InvocationId::new("i1"), ToolId::new("egress_tool"));

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
}
