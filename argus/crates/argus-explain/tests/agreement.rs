use argus_explain::{
    explain_grant_override, explain_invoke, explain_return_endorsed, explain_return_unendorsed,
    explain_sentinel_degrade_integrity, explain_sentinel_elevate_taint,
};
use argus_kernel::{
    transitions, AgentId, AuthorizerOracle, BackgroundTheory, BackgroundTheoryBuilder, CapKind,
    ConfLevel, ConformanceOracle, ContentGateOracle, EgressKind, IntegLevel, InvocationId,
    IssuerId, KernelError, KernelState, OverrideKey, ToolId, ToolMetadata, VecSet,
};
use proptest::prelude::*;

struct ConstAuth(bool);
impl AuthorizerOracle for ConstAuth {
    fn allows(&self, _: &AgentId, _: &ToolId, _: &InvocationId, _: &KernelState, _: &BackgroundTheory) -> bool {
        self.0
    }
}

/// Content gate keyed by `(agent, tool)` so the agreement tests can detect explain passing the
/// wrong tool (e.g. the new tool instead of an in-flight tool in check 2b) or the wrong agent
/// (child vs parent in returns) to the gate -- a tool-independent constant gate is blind to both.
#[derive(Debug)]
struct KeyedGate {
    verdicts: Vec<bool>,
}
impl ContentGateOracle for KeyedGate {
    fn passes(
        &self,
        agent: &AgentId,
        tool: &ToolId,
        _: &InvocationId,
        _: &KernelState,
        _: &BackgroundTheory,
    ) -> bool {
        let ai = AGENTS.iter().position(|a| agent.0 == *a);
        let ti = TOOLS.iter().position(|t| tool.0 == *t);
        match (ai, ti) {
            (Some(ai), Some(ti)) => self.verdicts[ai * TOOLS.len() + ti],
            _ => false,
        }
    }
}

fn arb_gate() -> impl Strategy<Value = KeyedGate> {
    prop::collection::vec(any::<bool>(), AGENTS.len() * TOOLS.len())
        .prop_map(|verdicts| KeyedGate { verdicts })
}

/// Conformance oracle keyed by `(child, parent)` for `return_endorsed`'s `return_conforms`
/// vouch. `conforms` (per-invocation) is not exercised by either lever transition, so it is
/// constant true.
#[derive(Debug)]
struct KeyedConformance {
    verdicts: Vec<bool>,
}
impl ConformanceOracle for KeyedConformance {
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

    fn return_conforms(
        &self,
        child: &AgentId,
        parent: &AgentId,
        _: &KernelState,
        _: &BackgroundTheory,
    ) -> bool {
        let ci = AGENTS.iter().position(|a| child.0 == *a);
        let pi = AGENTS.iter().position(|a| parent.0 == *a);
        match (ci, pi) {
            (Some(ci), Some(pi)) => self.verdicts[ci * AGENTS.len() + pi],
            _ => false,
        }
    }
}

fn arb_conformance() -> impl Strategy<Value = KeyedConformance> {
    prop::collection::vec(any::<bool>(), AGENTS.len() * AGENTS.len())
        .prop_map(|verdicts| KeyedConformance { verdicts })
}

const AGENTS: [&str; 3] = ["root", "a1", "a2"];
const TOOLS: [&str; 2] = ["t1", "t2"];
const LEVELS: [ConfLevel; 4] = [
    ConfLevel::Public,
    ConfLevel::Internal,
    ConfLevel::Sensitive,
    ConfLevel::Restricted,
];
const INTEG_LEVELS: [IntegLevel; 4] = [
    IntegLevel::Untrusted,
    IntegLevel::Standard,
    IntegLevel::Trusted,
    IntegLevel::Attested,
];
const EGRESS: [EgressKind; 2] = [EgressKind::NetworkExternal, EgressKind::FilesystemWrite];

fn conf_level() -> impl Strategy<Value = ConfLevel> {
    prop::sample::select(LEVELS.to_vec())
}

fn integ_level() -> impl Strategy<Value = IntegLevel> {
    prop::sample::select(INTEG_LEVELS.to_vec())
}

fn arb_egress_subset() -> impl Strategy<Value = VecSet<EgressKind>> {
    prop::collection::vec(any::<bool>(), EGRESS.len()).prop_map(|mask| {
        let mut s = VecSet::new();
        for (i, e) in EGRESS.iter().enumerate() {
            if mask[i] {
                s.insert(*e);
            }
        }
        s
    })
}

prop_compose! {
    fn arb_background()(
        floors in prop::collection::vec(conf_level(), TOOLS.len()),
        egress_mask in prop::collection::vec(prop::collection::vec(any::<bool>(), EGRESS.len()), TOOLS.len()),
        cap_mask in prop::collection::vec(any::<bool>(), TOOLS.len()),
        ceilings in prop::collection::vec(
            (prop::option::of(conf_level()), prop::option::of(conf_level())),
            EGRESS.len(),
        ),
        integ_floors in prop::collection::vec(integ_level(), TOOLS.len()),
        integ_inspect_floors in prop::collection::vec(integ_level(), TOOLS.len()),
        output_integs in prop::collection::vec(integ_level(), TOOLS.len()),
        lever_floor in integ_level(),
        lever_inspect_floor in integ_level(),
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
                integ_floor: integ_floors[ti],
                integ_inspect_floor: integ_inspect_floors[ti],
                output_integ: output_integs[ti],
            });
        }
        for (ei, e) in EGRESS.iter().enumerate() {
            let (allow, inspect) = ceilings[ei];
            b.set_egress_ceilings(*e, allow, inspect);
        }
        // Lever floors gate return_endorsed/grant_override's lever check.
        b.set_lever_floors(lever_floor, lever_inspect_floor);
        b.build()
    }
}

prop_compose! {
    fn arb_state()(
        active in prop::collection::vec(any::<bool>(), AGENTS.len()),
        registered in prop::collection::vec(any::<bool>(), TOOLS.len()),
        net_egress_caps in prop::collection::vec(any::<bool>(), AGENTS.len()),
        declassify_caps in prop::collection::vec(any::<bool>(), AGENTS.len()),
        grant_override_caps in prop::collection::vec(any::<bool>(), AGENTS.len()),
        taints in prop::collection::vec(prop::collection::vec(any::<bool>(), LEVELS.len()), AGENTS.len()),
        integs in prop::collection::vec(prop::collection::vec(any::<bool>(), INTEG_LEVELS.len()), AGENTS.len()),
        parent_edges in prop::collection::vec(any::<bool>(), AGENTS.len()),
        flights in prop::collection::vec(0usize..3, AGENTS.len()),
        bind_flight in prop::collection::vec(any::<bool>(), AGENTS.len() * 3),
        flight_egress in prop::collection::vec(
            prop::collection::vec(any::<bool>(), EGRESS.len()),
            AGENTS.len() * 3,
        ),
        used in prop::collection::vec(any::<bool>(), AGENTS.len() * TOOLS.len() * LEVELS.len()),
        flow_override in prop::collection::vec(any::<bool>(), AGENTS.len() * TOOLS.len() * LEVELS.len()),
    ) -> KernelState {
        let mut st = KernelState::initial();
        for (ai, a) in AGENTS.iter().enumerate() {
            let agent = AgentId::new(a);
            if active[ai] { st.agent_active.insert(agent.clone()); }
            let mut agent_caps = VecSet::new();
            if net_egress_caps[ai] { agent_caps.insert(CapKind::NetworkEgress); }
            if declassify_caps[ai] { agent_caps.insert(CapKind::Declassify); }
            if grant_override_caps[ai] { agent_caps.insert(CapKind::GrantOverride); }
            st.agent_cap.insert(agent.clone(), agent_caps);
            for (li, l) in LEVELS.iter().enumerate() {
                if taints[ai][li] { st.taint_levels.insert_into(agent.clone(), *l); }
            }
            for (li, l) in INTEG_LEVELS.iter().enumerate() {
                if integs[ai][li] { st.integ_levels.insert_into(agent.clone(), *l); }
            }
            if ai > 0 && parent_edges[ai] {
                let parent = AgentId::new(AGENTS[ai - 1]);
                st.agent_parent.insert(agent.clone(), parent);
            }
            for f in 0..flights[ai] {
                let inv = InvocationId::new(&format!("{a}-i{f}"));
                st.in_flight.insert_into(agent.clone(), inv.clone());
                if bind_flight[ai * 3 + f] {
                    st.invocation_tool.insert(inv.clone(), ToolId::new(TOOLS[f % TOOLS.len()]));
                    let mut egress = VecSet::new();
                    for (ei, e) in EGRESS.iter().enumerate() {
                        if flight_egress[ai * 3 + f][ei] {
                            egress.insert(*e);
                        }
                    }
                    st.invocation_egress.insert(inv, egress);
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
        let mut k = 0;
        for a in AGENTS {
            for t in TOOLS {
                for l in LEVELS {
                    if flow_override[k] {
                        st.flow_override.insert_into(
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
    // 4096, not the default 256/512: the returns agent-misroute mutant needs a valid parent
    // edge + child taint + a bound parent flight + INSPECT mode + differing per-agent verdicts
    // to surface, which 512 cases miss (measured: caught reliably from ~2048).
    #![proptest_config(ProptestConfig::with_cases(4096))]

    #[test]
    fn invoke_agrees(
        st in arb_state(), bg in arb_background(),
        agent in prop::sample::select(AGENTS.to_vec()),
        tool in prop::sample::select(TOOLS.to_vec()),
        auth in any::<bool>(), gate in arb_gate(),
        attested_egress in arb_egress_subset(),
    ) {
        let report = explain_invoke(
            &st, &bg, &ConstAuth(auth), &gate,
            &AgentId::new(agent), &ToolId::new(tool), &InvocationId::new("fresh"),
            &attested_egress,
        );
        let real = transitions::invoke_start(
            st.clone(), &bg, &ConstAuth(auth), &gate,
            AgentId::new(agent), ToolId::new(tool), InvocationId::new("fresh"),
            attested_egress,
        );
        check_verdict(&report.verdict, &real);
    }

    #[test]
    fn return_unendorsed_agrees(
        st in arb_state(), bg in arb_background(),
        child in prop::sample::select(AGENTS.to_vec()),
        parent in prop::sample::select(AGENTS.to_vec()),
        gate in arb_gate(),
    ) {
        let report = explain_return_unendorsed(
            &st, &bg, &gate, &AgentId::new(child), &AgentId::new(parent),
        );
        let real = transitions::return_unendorsed(
            st.clone(), &bg, &gate, AgentId::new(child), AgentId::new(parent),
        );
        check_verdict(&report.verdict, &real);
    }

    #[test]
    fn sentinel_agrees(
        st in arb_state(), bg in arb_background(),
        agent in prop::sample::select(AGENTS.to_vec()),
        level in conf_level(), gate in arb_gate(),
    ) {
        let report = explain_sentinel_elevate_taint(
            &st, &bg, &gate, &AgentId::new(agent), level,
        );
        let real = transitions::sentinel_elevate_taint(
            st.clone(), &bg, &gate, AgentId::new(agent), level,
        );
        check_verdict(&report.verdict, &real);
    }

    #[test]
    fn degrade_agrees(
        st in arb_state(), bg in arb_background(),
        agent in prop::sample::select(AGENTS.to_vec()),
        level in integ_level(), gate in arb_gate(),
    ) {
        let report = explain_sentinel_degrade_integrity(
            &st, &bg, &gate, &AgentId::new(agent), level,
        );
        let real = transitions::sentinel_degrade_integrity(
            st.clone(), &bg, &gate, AgentId::new(agent), level,
        );
        check_verdict(&report.verdict, &real);
    }

    #[test]
    fn return_endorsed_agrees(
        st in arb_state(), bg in arb_background(),
        child in prop::sample::select(AGENTS.to_vec()),
        parent in prop::sample::select(AGENTS.to_vec()),
        clvl in conf_level(), ilvl in integ_level(),
        conformance in arb_conformance(),
    ) {
        let report = explain_return_endorsed(
            &st, &bg, &conformance, &AgentId::new(child), &AgentId::new(parent), clvl, ilvl,
        );
        let real = transitions::return_endorsed(
            st.clone(), &bg, &conformance, AgentId::new(child), AgentId::new(parent), clvl, ilvl,
        );
        check_verdict(&report.verdict, &real);
    }

    #[test]
    fn grant_override_agrees(
        st in arb_state(), bg in arb_background(),
        granter in prop::sample::select(AGENTS.to_vec()),
        target in prop::sample::select(AGENTS.to_vec()),
        tool in prop::sample::select(TOOLS.to_vec()),
        level in conf_level(),
    ) {
        let report = explain_grant_override(
            &st, &bg, &AgentId::new(granter), &AgentId::new(target), level,
        );
        let real = transitions::grant_override(
            st.clone(), &bg, AgentId::new(granter), AgentId::new(target), ToolId::new(tool), level,
        );
        check_verdict(&report.verdict, &real);
    }
}

/// Deterministic agreement cases the fuzz harness structurally cannot reach: `arb_egress_subset`
/// is already unconstrained relative to a tool's declared egress (freely produces both
/// narrowing and coverage violations across the 4096 `invoke_agrees` cases), but `invoke_agrees`
/// always probes the fixed id `"fresh"`, which `arb_state` never seeds into `invocation_used` --
/// so `InvocationReplayed` can never surface there. These three cases nail down exactly the
/// paths the property fuzzing leaves to chance or cannot reach at all.
struct AllTrueGate;
impl ContentGateOracle for AllTrueGate {
    fn passes(
        &self,
        _: &AgentId,
        _: &ToolId,
        _: &InvocationId,
        _: &KernelState,
        _: &BackgroundTheory,
    ) -> bool {
        true
    }
}

fn deterministic_bg() -> BackgroundTheory {
    let mut b = BackgroundTheoryBuilder::new();
    b.trust_issuer(IssuerId::new("trusted"));
    b.register_tool(
        ToolId::new("t1"),
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
    b.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Restricted), None);
    b.build()
}

fn deterministic_active_agent(st: &mut KernelState) -> AgentId {
    let agent = AgentId::new("a1");
    st.agent_active.insert(agent.clone());
    st.agent_parent.insert(agent.clone(), AgentId::root());
    st.tool_registered.insert(ToolId::new("t1"));
    agent
}

#[test]
fn invocation_replay_denied_and_explain_agrees() {
    let bg = deterministic_bg();
    let mut st = KernelState::initial();
    let agent = deterministic_active_agent(&mut st);
    let inv = InvocationId::new("dup");
    st.invocation_used.insert(inv.clone());

    let report = explain_invoke(
        &st, &bg, &ConstAuth(true), &AllTrueGate,
        &agent, &ToolId::new("t1"), &inv, &VecSet::new(),
    );
    let real = transitions::invoke_start(
        st, &bg, &ConstAuth(true), &AllTrueGate,
        agent, ToolId::new("t1"), inv, VecSet::new(),
    );
    assert_eq!(report.verdict, Some(KernelError::InvocationReplayed));
    assert_eq!(real, Err(KernelError::InvocationReplayed));
}

#[test]
fn attestation_narrowing_denied_and_explain_agrees() {
    let bg = deterministic_bg();
    let mut st = KernelState::initial();
    let agent = deterministic_active_agent(&mut st);
    let attested_egress = VecSet::from([EgressKind::FilesystemWrite]);

    let report = explain_invoke(
        &st, &bg, &ConstAuth(true), &AllTrueGate,
        &agent, &ToolId::new("t1"), &InvocationId::new("i1"), &attested_egress,
    );
    let real = transitions::invoke_start(
        st, &bg, &ConstAuth(true), &AllTrueGate,
        agent, ToolId::new("t1"), InvocationId::new("i1"), attested_egress,
    );
    assert_eq!(report.verdict, Some(KernelError::AttestationInvalid));
    assert_eq!(real, Err(KernelError::AttestationInvalid));
}

#[test]
fn attestation_coverage_denied_and_explain_agrees() {
    let bg = deterministic_bg();
    let mut st = KernelState::initial();
    let agent = deterministic_active_agent(&mut st);
    let attested_egress = VecSet::new();

    let report = explain_invoke(
        &st, &bg, &ConstAuth(true), &AllTrueGate,
        &agent, &ToolId::new("t1"), &InvocationId::new("i1"), &attested_egress,
    );
    let real = transitions::invoke_start(
        st, &bg, &ConstAuth(true), &AllTrueGate,
        agent, ToolId::new("t1"), InvocationId::new("i1"), attested_egress,
    );
    assert_eq!(report.verdict, Some(KernelError::AttestationInvalid));
    assert_eq!(real, Err(KernelError::AttestationInvalid));
}

struct AllTrueConformance;
impl ConformanceOracle for AllTrueConformance {
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

/// Deterministic lever-floor denials for both levers -- `set_lever_floors(Trusted, Trusted)`
/// (empty inspect band) with the declassifying party degraded to `Untrusted`.
#[test]
fn return_endorsed_lever_floor_denied_and_explain_agrees() {
    let mut st = KernelState::initial();
    let child = AgentId::new("c");
    let parent = AgentId::new("p");
    st.agent_active.insert(child.clone());
    st.agent_active.insert(parent.clone());
    st.agent_parent.insert(parent.clone(), AgentId::root());
    st.agent_parent.insert(child.clone(), parent.clone());
    st.agent_cap.insert(child.clone(), VecSet::from([CapKind::Declassify]));
    st.integ_levels.insert(child.clone(), VecSet::from([IntegLevel::Untrusted]));
    let mut b = BackgroundTheoryBuilder::new();
    b.set_lever_floors(IntegLevel::Trusted, IntegLevel::Trusted);
    let bg = b.build();

    let report = explain_return_endorsed(
        &st, &bg, &AllTrueConformance, &child, &parent, ConfLevel::Public, IntegLevel::Attested,
    );
    let real = transitions::return_endorsed(
        st, &bg, &AllTrueConformance, child, parent, ConfLevel::Public, IntegLevel::Attested,
    );
    assert_eq!(report.verdict, Some(KernelError::LeverIntegrityDenied));
    assert_eq!(real, Err(KernelError::LeverIntegrityDenied));
}

#[test]
fn grant_override_lever_floor_denied_and_explain_agrees() {
    let mut st = KernelState::initial();
    let granter = AgentId::new("granter");
    let target = AgentId::new("target");
    st.agent_active.insert(granter.clone());
    st.agent_active.insert(target.clone());
    st.agent_cap.insert(granter.clone(), VecSet::from([CapKind::GrantOverride]));
    st.integ_levels.insert(granter.clone(), VecSet::from([IntegLevel::Untrusted]));
    let mut b = BackgroundTheoryBuilder::new();
    b.set_lever_floors(IntegLevel::Trusted, IntegLevel::Trusted);
    let bg = b.build();

    let report = explain_grant_override(&st, &bg, &granter, &target, ConfLevel::Public);
    let real = transitions::grant_override(
        st, &bg, granter, target, ToolId::new("t1"), ConfLevel::Public,
    );
    assert_eq!(report.verdict, Some(KernelError::LeverIntegrityDenied));
    assert_eq!(real, Err(KernelError::LeverIntegrityDenied));
}

#[test]
fn return_endorsed_declaration_not_covering_and_explain_agrees() {
    let mut st = KernelState::initial();
    let child = AgentId::new("c");
    let parent = AgentId::new("p");
    st.agent_active.insert(child.clone());
    st.agent_active.insert(parent.clone());
    st.agent_parent.insert(parent.clone(), AgentId::root());
    st.agent_parent.insert(child.clone(), parent.clone());
    st.agent_cap.insert(child.clone(), VecSet::from([CapKind::Declassify]));
    st.taint_levels.insert(child.clone(), VecSet::from([ConfLevel::Restricted]));
    let bg = BackgroundTheoryBuilder::new().build();

    // Declared clvl (Public) does not cover the held Restricted taint level.
    let report = explain_return_endorsed(
        &st, &bg, &AllTrueConformance, &child, &parent, ConfLevel::Public, IntegLevel::Attested,
    );
    let real = transitions::return_endorsed(
        st, &bg, &AllTrueConformance, child, parent, ConfLevel::Public, IntegLevel::Attested,
    );
    assert_eq!(report.verdict, Some(KernelError::DeclarationNotCovering));
    assert_eq!(real, Err(KernelError::DeclarationNotCovering));
}
