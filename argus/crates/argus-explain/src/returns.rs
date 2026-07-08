use argus_kernel::{AgentId, BackgroundTheory, ContentGateOracle, KernelError, KernelState};

use crate::invoke::{gate_finding, integ_check_denied};
use crate::report::{ExplainReport, GateCheck};

pub fn explain_return_unendorsed<C: ContentGateOracle>(
    st: &KernelState,
    bg: &BackgroundTheory,
    content_gate: &C,
    child: &AgentId,
    parent: &AgentId,
) -> ExplainReport {
    let mut report = ExplainReport {
        verdict: None,
        missing_caps: Vec::new(),
        findings: Vec::new(),
        authorizer_denied: false,
    };
    let precondition = if st.agent_parent.get(child) != Some(parent) {
        Some(KernelError::NotDirectChild)
    } else if !st.agent_active.contains(child) || !st.agent_active.contains(parent) {
        Some(KernelError::AgentInactive)
    } else if st.in_flight.set_nonempty(child) {
        Some(KernelError::ChildHasInFlight)
    } else {
        None
    };
    if let Some(e) = precondition {
        report.verdict = Some(e);
        return report;
    }

    let child_taint = st.taint_levels.get_set_or_empty(child);
    let flights = st.in_flight.get_set_or_empty(parent);
    for li in 0..child_taint.len() {
        let level = *child_taint.at(li);
        for fi in 0..flights.len() {
            let flight_inv = flights.at(fi);
            let Some(flight_tool) = st.invocation_tool.get_cloned(flight_inv) else {
                continue;
            };
            let egress = st.invocation_egress.get_set_or_empty(flight_inv);
            // Vouch is the parent's in-flight invocation being gated.
            let gate = content_gate.passes(parent, &flight_tool, flight_inv, st, bg);
            for ei in 0..egress.len() {
                report.findings.push(gate_finding(
                    bg, st, gate, GateCheck::ChildTaintVsParentFlight,
                    parent, &flight_tool, level, *egress.at(ei), None,
                ));
            }
        }
    }

    if report.denied_findings().next().is_some() {
        report.verdict = Some(KernelError::FlowGateBlocked);
        return report;
    }

    // Integrity gate mirror (verdict-level only; Task 16 adds full findings). No override
    // arm -- endorsement is the only way up, so unlike the conf gate this has no
    // consumption clause to mirror.
    let child_integ = st.integ_levels.get_set_or_empty(child);
    let mut integ_denied = false;
    for igi in 0..child_integ.len() {
        let level = *child_integ.at(igi);
        for fi in 0..flights.len() {
            let flight_inv = flights.at(fi);
            let Some(flight_tool) = st.invocation_tool.get_cloned(flight_inv) else {
                continue;
            };
            let Some(flight_meta) = bg.tool_metadata(&flight_tool) else {
                continue;
            };
            if integ_check_denied(
                content_gate, st, bg, parent, &flight_tool, flight_inv,
                flight_meta.integ_floor, flight_meta.integ_inspect_floor, level,
            ) {
                integ_denied = true;
            }
        }
    }

    report.verdict = if integ_denied { Some(KernelError::IntegrityFloorDenied) } else { None };
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
        let child = AgentId::new("c");
        let parent = AgentId::new("p");
        st.agent_active.insert(child.clone());
        st.agent_active.insert(parent.clone());
        st.agent_parent.insert(parent.clone(), AgentId::root());
        st.agent_parent.insert(child.clone(), parent.clone());
        st.taint_levels.insert(child, VecSet::from([ConfLevel::Sensitive]));
        st.in_flight.insert_into(parent, InvocationId::new("pi"));
        st.invocation_tool.insert(InvocationId::new("pi"), ToolId::new("egress_tool"));
        st
            .invocation_egress
            .insert(InvocationId::new("pi"), VecSet::from([EgressKind::NetworkExternal]));

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

    fn agree(st: &KernelState, bg: &BackgroundTheory, gate: bool) -> ExplainReport {
        let report = explain_return_unendorsed(
            st, bg, &ConstGate(gate), &AgentId::new("c"), &AgentId::new("p"),
        );
        let real = transitions::return_unendorsed(
            st.clone(), bg, &ConstGate(gate), AgentId::new("c"), AgentId::new("p"),
        );
        match &real {
            Ok(_) => assert_eq!(report.verdict, None),
            Err(e) => assert_eq!(report.verdict, Some(e.clone())),
        }
        report
    }

    #[test]
    fn child_taint_vs_parent_flight_denied() {
        let (st, bg) = fixture();
        let report = agree(&st, &bg, false);
        assert_eq!(report.verdict, Some(KernelError::FlowGateBlocked));
        let f = report.denied_findings().next().unwrap();
        assert_eq!(f.check, GateCheck::ChildTaintVsParentFlight);
        assert_eq!(f.tool, "egress_tool");
        assert_eq!(f.level, ConfLevel::Sensitive);
    }

    #[test]
    fn no_parent_flights_succeeds() {
        let (mut st, bg) = fixture();
        st.in_flight.remove(&AgentId::new("p"));
        let report = agree(&st, &bg, false);
        assert_eq!(report.verdict, None);
    }

    #[test]
    fn non_child_short_circuits() {
        let (mut st, bg) = fixture();
        st.agent_parent.remove(&AgentId::new("c"));
        let report = agree(&st, &bg, true);
        assert_eq!(report.verdict, Some(KernelError::NotDirectChild));
        assert!(report.findings.is_empty());
    }
}
