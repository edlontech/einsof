use argus_explain::{explain_invoke, explain_return_unendorsed, explain_sentinel_elevate_taint};
use argus_kernel::{
    transitions, AgentId, AuthorizerOracle, BackgroundTheory, BackgroundTheoryBuilder, CapKind,
    ConfLevel, ContentGateOracle, EgressKind, FlowMode, InvocationId, IssuerId, KernelState,
    OverrideKey, ToolId, ToolMetadata, VecSet,
};
use proptest::prelude::*;

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

const AGENTS: [&str; 3] = ["root", "a1", "a2"];
const TOOLS: [&str; 2] = ["t1", "t2"];
const LEVELS: [ConfLevel; 4] = [
    ConfLevel::Public,
    ConfLevel::Internal,
    ConfLevel::Sensitive,
    ConfLevel::Restricted,
];
const EGRESS: [EgressKind; 2] = [EgressKind::NetworkExternal, EgressKind::FilesystemWrite];

fn conf_level() -> impl Strategy<Value = ConfLevel> {
    prop::sample::select(LEVELS.to_vec())
}

fn flow_mode() -> impl Strategy<Value = FlowMode> {
    prop_oneof![Just(FlowMode::Allow), Just(FlowMode::Inspect), Just(FlowMode::Deny)]
}

prop_compose! {
    fn arb_background()(
        floors in prop::collection::vec(conf_level(), TOOLS.len()),
        egress_mask in prop::collection::vec(prop::collection::vec(any::<bool>(), EGRESS.len()), TOOLS.len()),
        cap_mask in prop::collection::vec(any::<bool>(), TOOLS.len()),
        modes in prop::collection::vec(prop::option::of(flow_mode()), LEVELS.len() * EGRESS.len()),
        overrides in prop::collection::vec(any::<bool>(), AGENTS.len() * TOOLS.len() * LEVELS.len()),
    ) -> BackgroundTheory {
        let mut b = BackgroundTheoryBuilder::new();
        b.trust_issuer(IssuerId::new("trusted"));
        for (ti, tool) in TOOLS.iter().enumerate() {
            let mut eg = VecSet::new();
            for (ei, e) in EGRESS.iter().enumerate() {
                if egress_mask[ti][ei] { eg.insert(*e); }
            }
            let mut caps = VecSet::new();
            if cap_mask[ti] { caps.insert(CapKind::NetworkEgress); }
            b.register_tool(ToolId::new(tool), ToolMetadata {
                capabilities: caps,
                egress: eg,
                conf_floor: floors[ti],
                output_bounded: false,
                issuer: IssuerId::new("trusted"),
            });
        }
        let mut k = 0;
        for l in LEVELS {
            for e in EGRESS {
                if let Some(m) = modes[k] { b.set_flow(l, e, m); }
                k += 1;
            }
        }
        let mut k = 0;
        for a in AGENTS {
            for t in TOOLS {
                for l in LEVELS {
                    if overrides[k] {
                        b.add_override(AgentId::new(a), ToolId::new(t), l);
                    }
                    k += 1;
                }
            }
        }
        b.build()
    }
}

prop_compose! {
    fn arb_state()(
        active in prop::collection::vec(any::<bool>(), AGENTS.len()),
        registered in prop::collection::vec(any::<bool>(), TOOLS.len()),
        caps in prop::collection::vec(any::<bool>(), AGENTS.len()),
        taints in prop::collection::vec(prop::collection::vec(any::<bool>(), LEVELS.len()), AGENTS.len()),
        parent_edges in prop::collection::vec(any::<bool>(), AGENTS.len()),
        flights in prop::collection::vec(0usize..3, AGENTS.len()),
        bind_flight in prop::collection::vec(any::<bool>(), AGENTS.len() * 3),
        used in prop::collection::vec(any::<bool>(), AGENTS.len() * TOOLS.len() * LEVELS.len()),
    ) -> KernelState {
        let mut st = KernelState::initial();
        for (ai, a) in AGENTS.iter().enumerate() {
            let agent = AgentId::new(a);
            if active[ai] { st.agent_active.insert(agent.clone()); }
            if caps[ai] {
                st.agent_cap.insert(agent.clone(), VecSet::from([CapKind::NetworkEgress]));
            }
            for (li, l) in LEVELS.iter().enumerate() {
                if taints[ai][li] { st.taint_levels.insert_into(agent.clone(), *l); }
            }
            if ai > 0 && parent_edges[ai] {
                let parent = AgentId::new(AGENTS[ai - 1]);
                st.agent_parent.insert(agent.clone(), parent);
            }
            for f in 0..flights[ai] {
                let inv = InvocationId::new(&format!("{a}-i{f}"));
                st.in_flight.insert_into(agent.clone(), inv.clone());
                if bind_flight[ai * 3 + f] {
                    st.invocation_tool.insert(inv, ToolId::new(TOOLS[f % TOOLS.len()]));
                }
            }
        }
        for (ti, t) in TOOLS.iter().enumerate() {
            if registered[ti] { st.tool_registered.insert(ToolId::new(t)); }
        }
        let mut k = 0;
        for a in AGENTS {
            for t in TOOLS {
                for l in LEVELS {
                    if used[k] {
                        st.override_used.insert_into(
                            AgentId::new(a),
                            OverrideKey { tool: ToolId::new(t), level: l },
                        );
                    }
                    k += 1;
                }
            }
        }
        st
    }
}

fn check_verdict<T>(
    verdict: &Option<argus_kernel::KernelError>,
    real: &Result<T, argus_kernel::KernelError>,
) {
    match real {
        Ok(_) => assert_eq!(*verdict, None, "explain denies, kernel succeeds"),
        Err(e) => assert_eq!(verdict.as_ref(), Some(e), "verdict mismatch"),
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(512))]

    #[test]
    fn invoke_agrees(
        st in arb_state(), bg in arb_background(),
        agent in prop::sample::select(AGENTS.to_vec()),
        tool in prop::sample::select(TOOLS.to_vec()),
        auth in any::<bool>(), gate in any::<bool>(),
    ) {
        let report = explain_invoke(
            &st, &bg, &ConstAuth(auth), &ConstGate(gate),
            &AgentId::new(agent), &ToolId::new(tool), &InvocationId::new("fresh"),
        );
        let real = transitions::invoke_start(
            st.clone(), &bg, &ConstAuth(auth), &ConstGate(gate),
            AgentId::new(agent), ToolId::new(tool), InvocationId::new("fresh"),
        );
        check_verdict(&report.verdict, &real);
    }

    #[test]
    fn return_unendorsed_agrees(
        st in arb_state(), bg in arb_background(),
        child in prop::sample::select(AGENTS.to_vec()),
        parent in prop::sample::select(AGENTS.to_vec()),
        gate in any::<bool>(),
    ) {
        let report = explain_return_unendorsed(
            &st, &bg, &ConstGate(gate), &AgentId::new(child), &AgentId::new(parent),
        );
        let real = transitions::return_unendorsed(
            st.clone(), &bg, &ConstGate(gate), AgentId::new(child), AgentId::new(parent),
        );
        check_verdict(&report.verdict, &real);
    }

    #[test]
    fn sentinel_agrees(
        st in arb_state(), bg in arb_background(),
        agent in prop::sample::select(AGENTS.to_vec()),
        level in conf_level(), gate in any::<bool>(),
    ) {
        let report = explain_sentinel_elevate_taint(
            &st, &bg, &ConstGate(gate), &AgentId::new(agent), level,
        );
        let real = transitions::sentinel_elevate_taint(
            st.clone(), &bg, &ConstGate(gate), AgentId::new(agent), level,
        );
        check_verdict(&report.verdict, &real);
    }
}
