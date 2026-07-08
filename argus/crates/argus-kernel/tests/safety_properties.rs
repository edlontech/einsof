use argus_kernel::*;
use argus_kernel::VecSet;

struct AllowAll;
impl AuthorizerOracle for AllowAll {
    fn allows(&self, _: &AgentId, _: &ToolId, _: &InvocationId, _: &KernelState, _: &BackgroundTheory) -> bool {
        true
    }
}
struct PassAll;
impl ContentGateOracle for PassAll {
    fn passes(&self, _: &AgentId, _: &ToolId, _: &InvocationId, _: &KernelState, _: &BackgroundTheory) -> bool {
        true
    }
}
struct ConformsAll;
impl ConformanceOracle for ConformsAll {
    fn conforms(&self, _: &AgentId, _: &ToolId, _: &InvocationId, _: &KernelState, _: &BackgroundTheory) -> bool {
        true
    }
    fn return_conforms(&self, _: &AgentId, _: &AgentId, _: &KernelState, _: &BackgroundTheory) -> bool {
        true
    }
}
struct NoopStore;
impl EventStore for NoopStore {
    fn append(&self, _: &KernelEvent) -> Result<(), KernelError> {
        Ok(())
    }
}

fn test_kernel() -> Kernel<AllowAll, PassAll, ConformsAll, NoopStore> {
    let mut b = BackgroundTheoryBuilder::new();
    b.trust_issuer(IssuerId::new("trusted"));
    b.register_tool(
        ToolId::new("read_file"),
        ToolMetadata {
            capabilities: VecSet::from([CapKind::FilesystemRead]),
            egress: VecSet::new(),
            conf_floor: ConfLevel::Sensitive,
            output_bounded: false,
            issuer: IssuerId::new("trusted"),
            integ_floor: IntegLevel::Untrusted,
            integ_inspect_floor: IntegLevel::Untrusted,
            output_integ: IntegLevel::Attested,
        },
    );
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
    b.register_tool(
        ToolId::new("check_exists"),
        ToolMetadata {
            capabilities: VecSet::from([CapKind::FilesystemRead]),
            egress: VecSet::new(),
            conf_floor: ConfLevel::Sensitive,
            output_bounded: true,
            issuer: IssuerId::new("trusted"),
            integ_floor: IntegLevel::Untrusted,
            integ_inspect_floor: IntegLevel::Untrusted,
            output_integ: IntegLevel::Attested,
        },
    );
    b.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Public), None);
    Kernel::new(b.build(), AllowAll, PassAll, ConformsAll, NoopStore)
}

/// Safety 1: root_always_active
/// Root must remain active through all operations.
#[test]
fn root_survives_all_operations() {
    let mut k = test_kernel();
    k.register_tool(ToolId::new("read_file")).unwrap();
    k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
    k.grant_capability(AgentId::root(), AgentId::new("a1"), CapKind::FilesystemRead)
        .unwrap();
    k.revoke(AgentId::root(), AgentId::new("a1")).unwrap();
    assert!(k.state().agent_active.contains(&AgentId::root()));
}

/// Safety 2: flow_confinement
/// A tainted agent cannot invoke tools with egress when flow policy denies it.
#[test]
fn tainted_agent_cannot_egress_when_denied() {
    let mut k = test_kernel();
    k.register_tool(ToolId::new("read_file")).unwrap();
    k.register_tool(ToolId::new("send_email")).unwrap();
    k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
    k.grant_capability(AgentId::root(), AgentId::new("a1"), CapKind::FilesystemRead)
        .unwrap();
    k.grant_capability(AgentId::root(), AgentId::new("a1"), CapKind::NetworkEgress)
        .unwrap();

    k.invoke_start(
        AgentId::new("a1"),
        ToolId::new("read_file"),
        InvocationId::new("i1"),
        VecSet::new(),
    )
    .unwrap();
    k.invoke_complete(AgentId::new("a1"), InvocationId::new("i1"))
        .unwrap();

    let result = k.invoke_start(
        AgentId::new("a1"),
        ToolId::new("send_email"),
        InvocationId::new("i2"),
        VecSet::from([EgressKind::NetworkExternal]),
    );
    assert!(result.is_err());
}

/// Safety 3: capability_subsumption
/// A child can never hold a capability its parent does not hold.
#[test]
fn child_cannot_get_cap_parent_lacks() {
    let mut k = test_kernel();
    k.delegate(AgentId::root(), AgentId::new("parent")).unwrap();
    k.grant_capability(
        AgentId::root(),
        AgentId::new("parent"),
        CapKind::FilesystemRead,
    )
    .unwrap();
    k.delegate(AgentId::new("parent"), AgentId::new("child"))
        .unwrap();

    let result = k.grant_capability(
        AgentId::new("parent"),
        AgentId::new("child"),
        CapKind::NetworkEgress,
    );
    assert!(result.is_err());
}

/// Safety 4: taint_isolation
/// A freshly delegated child starts with no taint, regardless of parent state.
#[test]
fn fresh_child_has_no_taint() {
    let mut k = test_kernel();
    k.register_tool(ToolId::new("read_file")).unwrap();
    k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
    k.grant_capability(AgentId::root(), AgentId::new("a1"), CapKind::FilesystemRead)
        .unwrap();
    k.invoke_start(
        AgentId::new("a1"),
        ToolId::new("read_file"),
        InvocationId::new("i1"),
        VecSet::new(),
    )
    .unwrap();
    k.invoke_complete(AgentId::new("a1"), InvocationId::new("i1"))
        .unwrap();

    k.delegate(AgentId::new("a1"), AgentId::new("child"))
        .unwrap();
    assert!(k.state().taint_levels.get(&AgentId::new("child")).is_none());
}

/// Safety 5: revocation_completeness
/// revoke + cascade_revoke cleans the entire subtree.
#[test]
fn revoke_plus_cascade_cleans_subtree() {
    let mut k = test_kernel();
    k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
    k.delegate(AgentId::new("a1"), AgentId::new("a2")).unwrap();

    k.revoke(AgentId::root(), AgentId::new("a1")).unwrap();
    k.cascade_revoke(AgentId::new("a2"), AgentId::new("a1"))
        .unwrap();

    assert!(!k.state().agent_active.contains(&AgentId::new("a1")));
    assert!(!k.state().agent_active.contains(&AgentId::new("a2")));
}

/// Safety 6: taint_integrity
/// Endorsed tools do not add taint.
#[test]
fn endorsed_tool_no_taint() {
    let mut k = test_kernel();
    k.register_tool(ToolId::new("check_exists")).unwrap();
    k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
    k.grant_capability(AgentId::root(), AgentId::new("a1"), CapKind::FilesystemRead)
        .unwrap();
    k.grant_capability(AgentId::root(), AgentId::new("a1"), CapKind::CreditBudget)
        .unwrap();
    // The completion crossing now requires cap_declassify at the invoke_complete site too
    // (design §5.4, finding 11: required at both crossing sites, not just returns).
    k.grant_capability(AgentId::root(), AgentId::new("a1"), CapKind::Declassify)
        .unwrap();
    // Delegated children spawn at budget 0 (design finding 5); credit before the endorsed
    // path can be afforded.
    k.sentinel_credit_budget(AgentId::new("a1"), BUDGET_CAPACITY)
        .unwrap();

    k.invoke_start(
        AgentId::new("a1"),
        ToolId::new("check_exists"),
        InvocationId::new("i1"),
        VecSet::new(),
    )
    .unwrap();
    k.invoke_complete(AgentId::new("a1"), InvocationId::new("i1"))
        .unwrap();

    assert!(k.state().taint_levels.get(&AgentId::new("a1")).is_none());
}

/// return_unendorsed propagates child taint to parent.
#[test]
fn return_unendorsed_propagates_taint_to_parent() {
    let mut k = test_kernel();
    k.register_tool(ToolId::new("read_file")).unwrap();
    k.delegate(AgentId::root(), AgentId::new("parent")).unwrap();
    k.grant_capability(
        AgentId::root(),
        AgentId::new("parent"),
        CapKind::FilesystemRead,
    )
    .unwrap();
    k.delegate(AgentId::new("parent"), AgentId::new("child"))
        .unwrap();
    k.grant_capability(
        AgentId::new("parent"),
        AgentId::new("child"),
        CapKind::FilesystemRead,
    )
    .unwrap();

    k.invoke_start(
        AgentId::new("child"),
        ToolId::new("read_file"),
        InvocationId::new("i1"),
        VecSet::new(),
    )
    .unwrap();
    k.invoke_complete(AgentId::new("child"), InvocationId::new("i1"))
        .unwrap();

    k.return_unendorsed(AgentId::new("child"), AgentId::new("parent"))
        .unwrap();
    assert!(
        k.state()
            .taint_levels
            .get(&AgentId::new("parent"))
            .unwrap()
            .contains(&ConfLevel::Sensitive)
    );
}

/// Root cannot invoke tools directly (root is the orchestrator, not an agent).
#[test]
fn root_cannot_invoke() {
    let mut k = test_kernel();
    k.register_tool(ToolId::new("read_file")).unwrap();

    let result = k.invoke_start(
        AgentId::root(),
        ToolId::new("read_file"),
        InvocationId::new("i1"),
        VecSet::new(),
    );
    assert!(result.is_err());
}

/// Speculative taint prevents exfiltration via parallel invocations.
#[test]
fn speculative_taint_blocks_parallel_exfil() {
    let mut k = test_kernel();
    k.register_tool(ToolId::new("read_file")).unwrap();
    k.register_tool(ToolId::new("send_email")).unwrap();
    k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
    k.grant_capability(AgentId::root(), AgentId::new("a1"), CapKind::FilesystemRead)
        .unwrap();
    k.grant_capability(AgentId::root(), AgentId::new("a1"), CapKind::NetworkEgress)
        .unwrap();

    k.invoke_start(
        AgentId::new("a1"),
        ToolId::new("read_file"),
        InvocationId::new("i1"),
        VecSet::new(),
    )
    .unwrap();

    let result = k.invoke_start(
        AgentId::new("a1"),
        ToolId::new("send_email"),
        InvocationId::new("i2"),
        VecSet::from([EgressKind::NetworkExternal]),
    );
    assert!(result.is_err());
}

/// Deep delegation chain: grandparent -> parent -> child with capability subsumption.
#[test]
fn deep_delegation_chain() {
    let mut k = test_kernel();
    k.register_tool(ToolId::new("read_file")).unwrap();

    k.delegate(AgentId::root(), AgentId::new("p")).unwrap();
    k.grant_capability(AgentId::root(), AgentId::new("p"), CapKind::FilesystemRead)
        .unwrap();

    k.delegate(AgentId::new("p"), AgentId::new("c")).unwrap();
    k.grant_capability(
        AgentId::new("p"),
        AgentId::new("c"),
        CapKind::FilesystemRead,
    )
    .unwrap();

    k.invoke_start(
        AgentId::new("c"),
        ToolId::new("read_file"),
        InvocationId::new("i1"),
        VecSet::new(),
    )
    .unwrap();
    k.invoke_complete(AgentId::new("c"), InvocationId::new("i1"))
        .unwrap();

    k.return_unendorsed(AgentId::new("c"), AgentId::new("p"))
        .unwrap();
    assert!(
        k.state()
            .taint_levels
            .get(&AgentId::new("p"))
            .unwrap()
            .contains(&ConfLevel::Sensitive)
    );
}

/// return_endorsed does NOT propagate child taint to parent.
/// This is the "I vouch for this child's output" path.
#[test]
fn return_endorsed_does_not_propagate_taint() {
    let mut k = test_kernel();
    k.register_tool(ToolId::new("read_file")).unwrap();
    k.delegate(AgentId::root(), AgentId::new("p")).unwrap();
    k.grant_capability(AgentId::root(), AgentId::new("p"), CapKind::FilesystemRead)
        .unwrap();
    k.delegate(AgentId::new("p"), AgentId::new("c")).unwrap();
    k.grant_capability(
        AgentId::new("p"),
        AgentId::new("c"),
        CapKind::FilesystemRead,
    )
    .unwrap();

    k.invoke_start(
        AgentId::new("c"),
        ToolId::new("read_file"),
        InvocationId::new("i1"),
        VecSet::new(),
    )
    .unwrap();
    k.invoke_complete(AgentId::new("c"), InvocationId::new("i1"))
        .unwrap();

    // Cross-boundary declassification now requires cap_declassify down the chain.
    k.grant_capability(AgentId::root(), AgentId::new("p"), CapKind::Declassify)
        .unwrap();
    k.grant_capability(AgentId::new("p"), AgentId::new("c"), CapKind::Declassify)
        .unwrap();

    // `p` is delegated (design finding 5: children spawn at budget 0); credit it so it can
    // afford the recipient-side debit `return_endorsed` charges.
    k.grant_capability(AgentId::root(), AgentId::new("p"), CapKind::CreditBudget)
        .unwrap();
    k.sentinel_credit_budget(AgentId::new("p"), BUDGET_CAPACITY)
        .unwrap();

    k.return_endorsed(
        AgentId::new("c"),
        AgentId::new("p"),
        ConfLevel::Sensitive,
        IntegLevel::Attested,
    )
    .unwrap();
    assert!(k.state().taint_levels.get(&AgentId::new("p")).is_none());
}

fn test_kernel_with_deny_flow() -> Kernel<AllowAll, PassAll, ConformsAll, NoopStore> {
    let mut b = BackgroundTheoryBuilder::new();
    b.trust_issuer(IssuerId::new("trusted"));
    b.register_tool(
        ToolId::new("read_file"),
        ToolMetadata {
            capabilities: VecSet::from([CapKind::FilesystemRead]),
            egress: VecSet::new(),
            conf_floor: ConfLevel::Sensitive,
            output_bounded: false,
            issuer: IssuerId::new("trusted"),
            integ_floor: IntegLevel::Untrusted,
            integ_inspect_floor: IntegLevel::Untrusted,
            output_integ: IntegLevel::Attested,
        },
    );
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
    Kernel::new(b.build(), AllowAll, PassAll, ConformsAll, NoopStore)
}

#[test]
fn sentinel_elevate_taint_basic() {
    let mut k = test_kernel();
    k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();

    let event = k
        .sentinel_elevate_taint(AgentId::new("a1"), ConfLevel::Sensitive)
        .unwrap();
    assert_eq!(
        event.action,
        KernelAction::SentinelElevateTaint {
            agent: AgentId::new("a1"),
            level: ConfLevel::Sensitive,
        }
    );
    assert!(
        k.state()
            .taint_levels
            .get(&AgentId::new("a1"))
            .unwrap()
            .contains(&ConfLevel::Sensitive)
    );
}

#[test]
fn sentinel_elevate_taint_inactive_agent_rejected() {
    let mut k = test_kernel();
    let result = k.sentinel_elevate_taint(AgentId::new("ghost"), ConfLevel::Public);
    assert!(result.is_err());
}

#[test]
fn sentinel_elevate_taint_flow_incompatible_rejected() {
    let mut k = test_kernel_with_deny_flow();
    k.register_tool(ToolId::new("send_email")).unwrap();
    k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
    for cap in CapKind::ALL {
        let _ = k.grant_capability(AgentId::root(), AgentId::new("a1"), cap);
    }

    k.invoke_start(
        AgentId::new("a1"),
        ToolId::new("send_email"),
        InvocationId::new("i1"),
        VecSet::from([EgressKind::NetworkExternal]),
    )
    .unwrap();

    let result = k.sentinel_elevate_taint(AgentId::new("a1"), ConfLevel::Sensitive);
    assert!(result.is_err());
}

#[test]
fn sentinel_elevate_taint_no_in_flight_always_succeeds() {
    let mut k = test_kernel();
    k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();

    k.sentinel_elevate_taint(AgentId::new("a1"), ConfLevel::Restricted)
        .unwrap();
    assert!(
        k.state()
            .taint_levels
            .get(&AgentId::new("a1"))
            .unwrap()
            .contains(&ConfLevel::Restricted)
    );
}

#[test]
fn flow_confinement_holds_after_sentinel_taint() {
    let mut k = test_kernel();
    k.register_tool(ToolId::new("send_email")).unwrap();
    k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
    for cap in CapKind::ALL {
        let _ = k.grant_capability(AgentId::root(), AgentId::new("a1"), cap);
    }

    k.sentinel_elevate_taint(AgentId::new("a1"), ConfLevel::Sensitive)
        .unwrap();

    let result = k.invoke_start(
        AgentId::new("a1"),
        ToolId::new("send_email"),
        InvocationId::new("i1"),
        VecSet::from([EgressKind::NetworkExternal]),
    );
    assert!(result.is_err());
}

/// Event store failure leaves kernel in consistent state.
#[test]
fn event_store_failure_preserves_consistency() {
    struct FailStore;
    impl EventStore for FailStore {
        fn append(&self, _: &KernelEvent) -> Result<(), KernelError> {
            Err(KernelError::EventStore)
        }
    }

    let bg = BackgroundTheoryBuilder::new().build();
    let mut k = Kernel::new(bg, AllowAll, PassAll, ConformsAll, FailStore);

    let result = k.delegate(AgentId::root(), AgentId::new("a1"));
    assert!(result.is_err());
    assert_eq!(k.sequence(), 0);
    assert!(!k.state().agent_active.contains(&AgentId::new("a1")));
}

/// Safety: tool_attestation_intact
/// Only tools with a trusted issuer may be registered; any registered tool has a trusted issuer.
#[test]
fn registered_tools_have_trusted_issuer() {
    let mut b = BackgroundTheoryBuilder::new();
    b.trust_issuer(IssuerId::new("trusted"));
    b.register_tool(
        ToolId::new("good"),
        ToolMetadata {
            capabilities: VecSet::new(),
            egress: VecSet::new(),
            conf_floor: ConfLevel::Public,
            output_bounded: true,
            issuer: IssuerId::new("trusted"),
            integ_floor: IntegLevel::Untrusted,
            integ_inspect_floor: IntegLevel::Untrusted,
            output_integ: IntegLevel::Attested,
        },
    );
    b.register_tool(
        ToolId::new("bad"),
        ToolMetadata {
            capabilities: VecSet::new(),
            egress: VecSet::new(),
            conf_floor: ConfLevel::Public,
            output_bounded: true,
            issuer: IssuerId::new("rogue"),
            integ_floor: IntegLevel::Untrusted,
            integ_inspect_floor: IntegLevel::Untrusted,
            output_integ: IntegLevel::Attested,
        },
    );
    let bg = b.build();
    let mut k = Kernel::new(bg, AllowAll, PassAll, ConformsAll, NoopStore);

    assert!(k.register_tool(ToolId::new("good")).is_ok());
    assert!(k.register_tool(ToolId::new("bad")).is_err());

    for tool in k.state().tool_registered.iter() {
        let issuer = k.background().tool_metadata(tool).unwrap().issuer;
        assert!(k.background().is_trusted_issuer(&issuer));
    }
}

/// Safety: instruction_attestation_intact
/// Only instructions with a trusted issuer may be loaded; any loaded instruction has a trusted issuer.
#[test]
fn loaded_instructions_have_trusted_issuer() {
    let mut b = BackgroundTheoryBuilder::new();
    b.trust_issuer(IssuerId::new("trusted"));
    b.register_instruction(InstructionId::new("sys"), IssuerId::new("trusted"));
    b.register_instruction(InstructionId::new("evil"), IssuerId::new("rogue"));
    let bg = b.build();
    let mut k = Kernel::new(bg, AllowAll, PassAll, ConformsAll, NoopStore);
    k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();

    assert!(
        k.load_instruction(AgentId::new("a1"), InstructionId::new("sys"))
            .is_ok()
    );
    assert!(
        k.load_instruction(AgentId::new("a1"), InstructionId::new("evil"))
            .is_err()
    );

    for (_agent, instrs) in k.state().agent_instruction.iter() {
        for instr in instrs.iter() {
            let issuer = k.background().instruction_issuer(instr).unwrap();
            assert!(k.background().is_trusted_issuer(issuer));
        }
    }
}

/// sentinel_credit_budget saturates at BUDGET_CAPACITY (no overflow past 16).
#[test]
fn sentinel_credit_budget_saturates_at_capacity() {
    let mut k = test_kernel();
    k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
    k.grant_capability(AgentId::root(), AgentId::new("a1"), CapKind::CreditBudget).unwrap();

    k.sentinel_credit_budget(AgentId::new("a1"), 100).unwrap();
    assert_eq!(k.state().budget(&AgentId::new("a1")), BUDGET_CAPACITY);
}

/// After budget drains to 0 via 8 invoke_complete cycles (weight 2 each),
/// a 9th invoke_complete falls to the full-taint branch.
#[test]
fn budget_exhausted_falls_to_full_taint() {
    let mut k = test_kernel();
    k.register_tool(ToolId::new("check_exists")).unwrap();
    k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
    k.grant_capability(AgentId::root(), AgentId::new("a1"), CapKind::FilesystemRead).unwrap();
    k.grant_capability(AgentId::root(), AgentId::new("a1"), CapKind::CreditBudget).unwrap();
    // The completion crossing requires cap_declassify (design §5.4); grant it so this test's
    // budget-exhaustion behavior, not cap absence, is what drives the full-taint fallback.
    k.grant_capability(AgentId::root(), AgentId::new("a1"), CapKind::Declassify).unwrap();
    // Delegated children spawn at budget 0 (design finding 5); credit to capacity to exercise
    // the exhaustion behavior this test is about.
    k.sentinel_credit_budget(AgentId::new("a1"), BUDGET_CAPACITY).unwrap();

    // 8 cycles × weight-2 = 16 debits; budget starts at 16 (explicitly credited).
    let mut i = 0u8;
    while i < 8 {
        let inv = InvocationId::new(&format!("inv-{i}"));
        k.invoke_start(AgentId::new("a1"), ToolId::new("check_exists"), inv.clone(), VecSet::new()).unwrap();
        k.invoke_complete(AgentId::new("a1"), inv).unwrap();
        i += 1;
    }
    assert_eq!(k.state().budget(&AgentId::new("a1")), 0);
    assert!(k.state().taint_levels.get(&AgentId::new("a1")).is_none(), "no taint before exhaustion");

    // 9th cycle: affordable(2) == false → full-taint branch.
    k.invoke_start(AgentId::new("a1"), ToolId::new("check_exists"), InvocationId::new("inv-8"), VecSet::new()).unwrap();
    k.invoke_complete(AgentId::new("a1"), InvocationId::new("inv-8")).unwrap();
    assert_eq!(k.state().budget(&AgentId::new("a1")), 0);
    assert!(
        k.state().taint_levels.get(&AgentId::new("a1")).unwrap().contains(&ConfLevel::Sensitive),
        "Sensitive taint after budget exhaustion"
    );
}

/// Safety: grant_override single-use is preserved across re-arm.
/// Full kernel scenario: root grants, agent uses the override (DENY flow via sentinel), re-arm
/// is refused while in-flight, completes, root re-grants, override is usable exactly once more.
///
/// After the first sentinel raise the agent carries Sensitive taint. The re-armed override is
/// then consumed by invoke_start (CHECK 2a: new tool's egress at existing taint level hits DENY;
/// override is the sole justification and is spent). A subsequent invoke_start with the same tool
/// is blocked — the re-armed override is also single-use.
#[test]
fn grant_override_preserves_single_use_across_rearm() {
    use argus_kernel::ConfLevel;

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
    // Sensitive/NetworkExternal => DENY (no ALLOW ceiling).
    b.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Public), None);
    let mut k = Kernel::new(b.build(), AllowAll, PassAll, ConformsAll, NoopStore);

    let agent = AgentId::new("a");
    k.delegate(AgentId::root(), agent.clone()).unwrap();
    for cap in CapKind::ALL {
        let _ = k.grant_capability(AgentId::root(), agent.clone(), cap);
    }
    k.register_tool(ToolId::new("send_email")).unwrap();

    // Arm the override via the in-band kernel path.
    k.grant_override(
        AgentId::root(),
        agent.clone(),
        ToolId::new("send_email"),
        ConfLevel::Sensitive,
    )
    .expect("root can arm override");

    // Start an invocation so sentinel_elevate_taint has a DENY-mode in-flight to check.
    k.invoke_start(
        agent.clone(),
        ToolId::new("send_email"),
        InvocationId::new("inv-1"),
        VecSet::from([EgressKind::NetworkExternal]),
    )
    .unwrap();

    // First sentinel raise: override rescues and is consumed.
    k.sentinel_elevate_taint(agent.clone(), ConfLevel::Sensitive)
        .expect("first sentinel raise passes via override");
    assert!(
        k.state().override_consumed(&agent, &ToolId::new("send_email"), ConfLevel::Sensitive),
        "override must be consumed after first use"
    );

    // Re-arm while in-flight must be refused.
    let rearm_err = k.grant_override(
        AgentId::root(),
        agent.clone(),
        ToolId::new("send_email"),
        ConfLevel::Sensitive,
    );
    assert!(rearm_err.is_err(), "re-arm while target has in-flight must fail");

    // Complete the flight; now re-arm should succeed.
    k.invoke_complete(agent.clone(), InvocationId::new("inv-1")).unwrap();

    k.grant_override(
        AgentId::root(),
        agent.clone(),
        ToolId::new("send_email"),
        ConfLevel::Sensitive,
    )
    .expect("re-arm after flight clears must succeed");

    assert!(
        !k.state().override_consumed(&agent, &ToolId::new("send_email"), ConfLevel::Sensitive),
        "re-arm clears the consumed flag"
    );

    // Agent now has Sensitive taint (from the sentinel raise). invoke_start on send_email triggers
    // CHECK 2a: Sensitive/NetworkExternal = DENY; the re-armed override rescues exactly once.
    k.invoke_start(
        agent.clone(),
        ToolId::new("send_email"),
        InvocationId::new("inv-2"),
        VecSet::from([EgressKind::NetworkExternal]),
    )
    .expect("invoke_start passes via re-armed override (CHECK 2a)");
    assert!(
        k.state().override_consumed(&agent, &ToolId::new("send_email"), ConfLevel::Sensitive),
        "re-armed override consumed by invoke_start"
    );

    // A second invoke_start with the same tool must be blocked: override spent.
    let blocked = k.invoke_start(
        agent.clone(),
        ToolId::new("send_email"),
        InvocationId::new("inv-3"),
        VecSet::from([EgressKind::NetworkExternal]),
    );
    assert!(blocked.is_err(), "invoke_start must fail: re-armed override also single-use");
}

/// Design §7 safety-scenario suite (Task 15). `v3_kernel` registers `web_fetch`
/// (floor untrusted / emission untrusted, egress network_external), `delete_repo`
/// (floor trusted / emission attested, destructive, no egress) and `send_email`
/// (floor untrusted / emission attested, egress network_external), with lever floors
/// set to trusted and the network_external ceiling allowing up to sensitive.
fn v3_kernel() -> Kernel<AllowAll, PassAll, ConformsAll, NoopStore> {
    let mut b = BackgroundTheoryBuilder::new();
    b.trust_issuer(IssuerId::new("trusted"));
    b.register_tool(
        ToolId::new("web_fetch"),
        ToolMetadata {
            capabilities: VecSet::from([CapKind::NetworkEgress]),
            egress: VecSet::from([EgressKind::NetworkExternal]),
            conf_floor: ConfLevel::Public,
            output_bounded: true,
            issuer: IssuerId::new("trusted"),
            integ_floor: IntegLevel::Untrusted,
            integ_inspect_floor: IntegLevel::Untrusted,
            output_integ: IntegLevel::Untrusted,
        },
    );
    b.register_tool(
        ToolId::new("delete_repo"),
        ToolMetadata {
            capabilities: VecSet::from([CapKind::FilesystemDelete]),
            egress: VecSet::new(),
            conf_floor: ConfLevel::Public,
            output_bounded: false,
            issuer: IssuerId::new("trusted"),
            integ_floor: IntegLevel::Trusted,
            integ_inspect_floor: IntegLevel::Trusted,
            output_integ: IntegLevel::Attested,
        },
    );
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
    b.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Sensitive), None);
    b.set_lever_floors(IntegLevel::Trusted, IntegLevel::Trusted);
    Kernel::new(b.build(), AllowAll, PassAll, ConformsAll, NoopStore)
}

/// Scenario 1: web_fetch (unendorsed) then delete_repo -> denied (4a).
#[test]
fn scenario1_unendorsed_web_fetch_blocks_delete_repo() {
    let mut k = v3_kernel();
    k.register_tool(ToolId::new("web_fetch")).unwrap();
    k.register_tool(ToolId::new("delete_repo")).unwrap();
    let a1 = AgentId::new("a1");
    k.delegate(AgentId::root(), a1.clone()).unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::NetworkEgress)
        .unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::FilesystemDelete)
        .unwrap();

    k.invoke_start(
        a1.clone(),
        ToolId::new("web_fetch"),
        InvocationId::new("i1"),
        VecSet::from([EgressKind::NetworkExternal]),
    )
    .unwrap();
    k.invoke_complete(a1.clone(), InvocationId::new("i1"))
        .unwrap();
    assert!(
        k.state()
            .integ_levels
            .get(&a1)
            .unwrap()
            .contains(&IntegLevel::Untrusted)
    );

    let result = k.invoke_start(
        a1,
        ToolId::new("delete_repo"),
        InvocationId::new("i2"),
        VecSet::new(),
    );
    assert_eq!(result.unwrap_err(), KernelError::IntegrityFloorDenied);
}

/// Scenario 2: delete_repo in flight, then web_fetch -> denied (4b).
#[test]
fn scenario2_delete_repo_in_flight_blocks_web_fetch() {
    let mut k = v3_kernel();
    k.register_tool(ToolId::new("web_fetch")).unwrap();
    k.register_tool(ToolId::new("delete_repo")).unwrap();
    let a1 = AgentId::new("a1");
    k.delegate(AgentId::root(), a1.clone()).unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::FilesystemDelete)
        .unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::NetworkEgress)
        .unwrap();

    k.invoke_start(
        a1.clone(),
        ToolId::new("delete_repo"),
        InvocationId::new("i1"),
        VecSet::new(),
    )
    .unwrap();

    let result = k.invoke_start(
        a1,
        ToolId::new("web_fetch"),
        InvocationId::new("i2"),
        VecSet::from([EgressKind::NetworkExternal]),
    );
    assert_eq!(result.unwrap_err(), KernelError::IntegrityFloorDenied);
}

/// Scenario 3: web_fetch completes endorsed (conformant + affordable + cap) -> delete_repo
/// path stays open, budget debited by `integ_weight`.
#[test]
fn scenario3_endorsed_web_fetch_keeps_delete_repo_open_and_debits_integ_weight() {
    let mut k = v3_kernel();
    k.register_tool(ToolId::new("web_fetch")).unwrap();
    k.register_tool(ToolId::new("delete_repo")).unwrap();
    let a1 = AgentId::new("a1");
    k.delegate(AgentId::root(), a1.clone()).unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::NetworkEgress)
        .unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::FilesystemDelete)
        .unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::Declassify)
        .unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::CreditBudget)
        .unwrap();
    k.sentinel_credit_budget(a1.clone(), BUDGET_CAPACITY)
        .unwrap();

    k.invoke_start(
        a1.clone(),
        ToolId::new("web_fetch"),
        InvocationId::new("i1"),
        VecSet::from([EgressKind::NetworkExternal]),
    )
    .unwrap();
    let ev = k
        .invoke_complete(a1.clone(), InvocationId::new("i1"))
        .unwrap();
    assert_eq!(
        ev.action,
        KernelAction::InvokeComplete {
            agent: a1.clone(),
            inv: InvocationId::new("i1"),
            endorsed: true,
        }
    );
    assert_eq!(
        k.state().budget(&a1),
        BUDGET_CAPACITY - integ_weight(IntegLevel::Untrusted)
    );
    assert!(k.state().integ_levels.get(&a1).is_none());

    k.invoke_start(
        a1,
        ToolId::new("delete_repo"),
        InvocationId::new("i2"),
        VecSet::new(),
    )
    .unwrap();
}

/// Scenario 4: injected child attempts return_endorsed below the lever floor -> denied.
#[test]
fn scenario4_injected_child_below_lever_floor_return_endorsed_denied() {
    let mut k = v3_kernel();
    let parent = AgentId::root();
    let child = AgentId::new("child");
    k.delegate(parent.clone(), child.clone()).unwrap();
    k.grant_capability(parent.clone(), child.clone(), CapKind::Declassify)
        .unwrap();
    k.sentinel_degrade_integrity(child.clone(), IntegLevel::Untrusted)
        .unwrap();

    let result = k.return_endorsed(child, parent, ConfLevel::Public, IntegLevel::Untrusted);
    assert_eq!(result.unwrap_err(), KernelError::LeverIntegrityDenied);
}

/// Scenario 5: degraded granter attempts grant_override -> denied (strict).
#[test]
fn scenario5_degraded_granter_grant_override_denied_strict() {
    let mut k = v3_kernel();
    k.register_tool(ToolId::new("send_email")).unwrap();
    let granter = AgentId::new("granter");
    k.delegate(AgentId::root(), granter.clone()).unwrap();
    k.grant_capability(AgentId::root(), granter.clone(), CapKind::GrantOverride)
        .unwrap();
    k.sentinel_degrade_integrity(granter.clone(), IntegLevel::Untrusted)
        .unwrap();

    let target = AgentId::new("target");
    k.delegate(AgentId::root(), target.clone()).unwrap();

    let result = k.grant_override(granter, target, ToolId::new("send_email"), ConfLevel::Public);
    assert_eq!(result.unwrap_err(), KernelError::LeverIntegrityDenied);
}

/// Scenario 6: sentinel degrade with destructive tool in flight -> denied (hold at adapter);
/// after the invocation completes, the same degrade succeeds.
#[test]
fn scenario6_degrade_blocked_with_destructive_tool_in_flight_then_succeeds() {
    let mut k = v3_kernel();
    k.register_tool(ToolId::new("delete_repo")).unwrap();
    let a1 = AgentId::new("a1");
    k.delegate(AgentId::root(), a1.clone()).unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::FilesystemDelete)
        .unwrap();

    k.invoke_start(
        a1.clone(),
        ToolId::new("delete_repo"),
        InvocationId::new("i1"),
        VecSet::new(),
    )
    .unwrap();

    let blocked = k.sentinel_degrade_integrity(a1.clone(), IntegLevel::Untrusted);
    assert_eq!(blocked.unwrap_err(), KernelError::IntegrityFloorDenied);

    k.invoke_complete(a1.clone(), InvocationId::new("i1"))
        .unwrap();
    k.sentinel_degrade_integrity(a1, IntegLevel::Untrusted)
        .unwrap();
}

/// Scenario 7: delegate child starts clean and at budget 0; endorsed anything before
/// credit -> unendorsed path.
#[test]
fn scenario7_delegated_child_starts_clean_and_at_budget_zero_forces_unendorsed() {
    let mut k = v3_kernel();
    k.register_tool(ToolId::new("web_fetch")).unwrap();
    let child = AgentId::new("child");
    k.delegate(AgentId::root(), child.clone()).unwrap();
    assert_eq!(k.state().budget(&child), 0);
    assert!(!k.state().affordable(&child, 1));
    assert!(k.state().taint_levels.get(&child).is_none());
    assert!(k.state().integ_levels.get(&child).is_none());

    k.grant_capability(AgentId::root(), child.clone(), CapKind::NetworkEgress)
        .unwrap();
    k.grant_capability(AgentId::root(), child.clone(), CapKind::Declassify)
        .unwrap();

    k.invoke_start(
        child.clone(),
        ToolId::new("web_fetch"),
        InvocationId::new("i1"),
        VecSet::from([EgressKind::NetworkExternal]),
    )
    .unwrap();
    let ev = k
        .invoke_complete(child.clone(), InvocationId::new("i1"))
        .unwrap();
    assert_eq!(
        ev.action,
        KernelAction::InvokeComplete {
            agent: child.clone(),
            inv: InvocationId::new("i1"),
            endorsed: false,
        }
    );
    assert!(
        k.state()
            .integ_levels
            .get(&child)
            .unwrap()
            .contains(&IntegLevel::Untrusted)
    );
}

/// Scenario 8: budget-mint attack replay. Delegation mints no budget: an uncredited child
/// cannot self-fund an endorsed crossing; the same tree shape succeeds only after an
/// explicit, audited `sentinel_credit_budget` call (the finding-1 exploit, now dead).
#[test]
fn scenario8_budget_mint_replay_child_cannot_self_fund_without_explicit_credit() {
    let mut k = v3_kernel();
    k.register_tool(ToolId::new("web_fetch")).unwrap();

    let uncredited = AgentId::new("uncredited");
    k.delegate(AgentId::root(), uncredited.clone()).unwrap();
    k.grant_capability(AgentId::root(), uncredited.clone(), CapKind::NetworkEgress)
        .unwrap();
    k.grant_capability(AgentId::root(), uncredited.clone(), CapKind::Declassify)
        .unwrap();
    assert_eq!(k.state().budget(&uncredited), 0);

    k.invoke_start(
        uncredited.clone(),
        ToolId::new("web_fetch"),
        InvocationId::new("i1"),
        VecSet::from([EgressKind::NetworkExternal]),
    )
    .unwrap();
    let ev1 = k
        .invoke_complete(uncredited.clone(), InvocationId::new("i1"))
        .unwrap();
    assert_eq!(
        ev1.action,
        KernelAction::InvokeComplete {
            agent: uncredited.clone(),
            inv: InvocationId::new("i1"),
            endorsed: false,
        }
    );
    assert!(
        k.state()
            .integ_levels
            .get(&uncredited)
            .unwrap()
            .contains(&IntegLevel::Untrusted),
        "an uncredited child cannot launder untrusted content on its own (zero) budget"
    );

    let credited = AgentId::new("credited");
    k.delegate(AgentId::root(), credited.clone()).unwrap();
    k.grant_capability(AgentId::root(), credited.clone(), CapKind::NetworkEgress)
        .unwrap();
    k.grant_capability(AgentId::root(), credited.clone(), CapKind::Declassify)
        .unwrap();
    k.grant_capability(AgentId::root(), credited.clone(), CapKind::CreditBudget)
        .unwrap();
    k.sentinel_credit_budget(credited.clone(), BUDGET_CAPACITY)
        .unwrap();

    k.invoke_start(
        credited.clone(),
        ToolId::new("web_fetch"),
        InvocationId::new("i2"),
        VecSet::from([EgressKind::NetworkExternal]),
    )
    .unwrap();
    let ev2 = k
        .invoke_complete(credited.clone(), InvocationId::new("i2"))
        .unwrap();
    assert_eq!(
        ev2.action,
        KernelAction::InvokeComplete {
            agent: credited,
            inv: InvocationId::new("i2"),
            endorsed: true,
        }
    );
}

/// Scenario 9: dimension-adjusted debit -- an already-conf-tainted agent endorsing an
/// untrusted-emission tool pays only `integ_weight`, no conf component.
fn scenario9_kernel() -> Kernel<AllowAll, PassAll, ConformsAll, NoopStore> {
    let mut b = BackgroundTheoryBuilder::new();
    b.trust_issuer(IssuerId::new("trusted"));
    b.register_tool(
        ToolId::new("web_fetch"),
        ToolMetadata {
            capabilities: VecSet::from([CapKind::NetworkEgress]),
            egress: VecSet::from([EgressKind::NetworkExternal]),
            conf_floor: ConfLevel::Internal,
            output_bounded: true,
            issuer: IssuerId::new("trusted"),
            integ_floor: IntegLevel::Untrusted,
            integ_inspect_floor: IntegLevel::Untrusted,
            output_integ: IntegLevel::Untrusted,
        },
    );
    b.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Internal), None);
    Kernel::new(b.build(), AllowAll, PassAll, ConformsAll, NoopStore)
}

#[test]
fn scenario9_dimension_adjusted_debit_pays_only_integ_weight() {
    let mut k = scenario9_kernel();
    k.register_tool(ToolId::new("web_fetch")).unwrap();
    let a1 = AgentId::new("a1");
    k.delegate(AgentId::root(), a1.clone()).unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::NetworkEgress)
        .unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::Declassify)
        .unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::CreditBudget)
        .unwrap();
    k.sentinel_credit_budget(a1.clone(), BUDGET_CAPACITY)
        .unwrap();

    // Already conf-tainted at the tool's own floor -- the conf dimension cannot help.
    k.sentinel_elevate_taint(a1.clone(), ConfLevel::Internal)
        .unwrap();

    k.invoke_start(
        a1.clone(),
        ToolId::new("web_fetch"),
        InvocationId::new("i1"),
        VecSet::from([EgressKind::NetworkExternal]),
    )
    .unwrap();
    let ev = k
        .invoke_complete(a1.clone(), InvocationId::new("i1"))
        .unwrap();
    assert_eq!(
        ev.action,
        KernelAction::InvokeComplete {
            agent: a1.clone(),
            inv: InvocationId::new("i1"),
            endorsed: true,
        }
    );
    // declass_weight(Internal) = 1 would apply if the conf dimension had helped; only
    // integ_weight(Untrusted) = 4 is charged.
    assert_eq!(
        k.state().budget(&a1),
        BUDGET_CAPACITY - integ_weight(IntegLevel::Untrusted)
    );
}

/// Scenario 10: return_endorsed with clvl below a held child taint level -> denied
/// (coverage); a restricted return costs declass_weight(restricted) + integ_weight
/// (arbitrage closed).
#[test]
fn scenario10_declaration_must_cover_child_taint_and_restricted_return_costs_more() {
    let bg = BackgroundTheoryBuilder::new().build();
    let mut k = Kernel::new(bg, AllowAll, PassAll, ConformsAll, NoopStore);

    let parent = AgentId::root();
    let child = AgentId::new("child");
    k.delegate(parent.clone(), child.clone()).unwrap();
    k.grant_capability(parent.clone(), child.clone(), CapKind::Declassify)
        .unwrap();

    k.sentinel_elevate_taint(child.clone(), ConfLevel::Restricted)
        .unwrap();
    k.sentinel_degrade_integrity(child.clone(), IntegLevel::Standard)
        .unwrap();

    let under_covering = k.return_endorsed(
        child.clone(),
        parent.clone(),
        ConfLevel::Sensitive,
        IntegLevel::Attested,
    );
    assert_eq!(under_covering.unwrap_err(), KernelError::DeclarationNotCovering);

    let budget_before = k.state().budget(&parent);
    k.return_endorsed(child, parent.clone(), ConfLevel::Restricted, IntegLevel::Standard)
        .unwrap();
    assert_eq!(
        budget_before - k.state().budget(&parent),
        4 + integ_weight(IntegLevel::Standard)
    );
}

/// Scenario 11: a tainted agent invoking a generic `http_request` tool, attested only to
/// the corp-api egress kind (network_internal), is allowed where the static worst case
/// (both declared kinds) would deny.
fn scenario11_kernel() -> Kernel<AllowAll, PassAll, ConformsAll, NoopStore> {
    let mut b = BackgroundTheoryBuilder::new();
    b.trust_issuer(IssuerId::new("trusted"));
    b.register_tool(
        ToolId::new("http_request"),
        ToolMetadata {
            capabilities: VecSet::from([CapKind::NetworkEgress]),
            egress: VecSet::from([EgressKind::NetworkExternal, EgressKind::NetworkInternal]),
            conf_floor: ConfLevel::Public,
            output_bounded: false,
            issuer: IssuerId::new("trusted"),
            integ_floor: IntegLevel::Untrusted,
            integ_inspect_floor: IntegLevel::Untrusted,
            output_integ: IntegLevel::Attested,
        },
    );
    b.set_egress_ceilings(EgressKind::NetworkInternal, Some(ConfLevel::Sensitive), None);
    b.set_egress_ceilings(EgressKind::NetworkExternal, Some(ConfLevel::Public), None);
    Kernel::new(b.build(), AllowAll, PassAll, ConformsAll, NoopStore)
}

#[test]
fn scenario11_attested_egress_precision_beats_static_worst_case() {
    let mut k = scenario11_kernel();
    k.register_tool(ToolId::new("http_request")).unwrap();
    let a1 = AgentId::new("a1");
    k.delegate(AgentId::root(), a1.clone()).unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::NetworkEgress)
        .unwrap();
    k.sentinel_elevate_taint(a1.clone(), ConfLevel::Sensitive)
        .unwrap();

    let worst_case = k.invoke_start(
        a1.clone(),
        ToolId::new("http_request"),
        InvocationId::new("i1"),
        VecSet::from([EgressKind::NetworkExternal, EgressKind::NetworkInternal]),
    );
    assert_eq!(worst_case.unwrap_err(), KernelError::FlowGateBlocked);

    k.invoke_start(
        a1,
        ToolId::new("http_request"),
        InvocationId::new("i2"),
        VecSet::from([EgressKind::NetworkInternal]),
    )
    .unwrap();
}

/// Scenario 12: an attested egress kind outside the declared set -> denied (narrowing);
/// an empty attestation on an egress-bearing tool -> denied (coverage).
#[test]
fn scenario12_attestation_narrowing_and_coverage_denied() {
    let mut k = v3_kernel();
    k.register_tool(ToolId::new("web_fetch")).unwrap();
    let a1 = AgentId::new("a1");
    k.delegate(AgentId::root(), a1.clone()).unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::NetworkEgress)
        .unwrap();

    let narrowing = k.invoke_start(
        a1.clone(),
        ToolId::new("web_fetch"),
        InvocationId::new("i1"),
        VecSet::from([EgressKind::NetworkInternal]),
    );
    assert_eq!(narrowing.unwrap_err(), KernelError::AttestationInvalid);

    let coverage = k.invoke_start(
        a1,
        ToolId::new("web_fetch"),
        InvocationId::new("i2"),
        VecSet::new(),
    );
    assert_eq!(coverage.unwrap_err(), KernelError::AttestationInvalid);
}

/// Scenario 13: invocation-id replay -> denied (freshness). `invocation_tool` and
/// `invocation_used` are both global and set together at `invoke_start`, so replaying the
/// exact id a completed invocation used trips the pre-existing `InvocationExists` guard
/// before the dedicated freshness check is reached -- replay is still denied. The
/// `InvocationReplayed` variant itself (a used-but-not-currently-bound id, e.g. under a
/// future `invocation_tool` pruning strategy) is exercised at the transition level by
/// `invoke_start_rejects_replayed_invocation`.
#[test]
fn scenario13_invocation_id_replay_denied() {
    let mut k = v3_kernel();
    k.register_tool(ToolId::new("delete_repo")).unwrap();
    let a1 = AgentId::new("a1");
    k.delegate(AgentId::root(), a1.clone()).unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::FilesystemDelete)
        .unwrap();

    let inv = InvocationId::new("i1");
    k.invoke_start(
        a1.clone(),
        ToolId::new("delete_repo"),
        inv.clone(),
        VecSet::new(),
    )
    .unwrap();
    k.invoke_complete(a1.clone(), inv.clone()).unwrap();

    let replay = k.invoke_start(a1, ToolId::new("delete_repo"), inv, VecSet::new());
    assert_eq!(replay.unwrap_err(), KernelError::InvocationExists);
}

/// Scenario 14: missing cap_declassify at completion -> unendorsed branch (no error,
/// fail-safe).
#[test]
fn scenario14_missing_cap_declassify_routes_unendorsed_fail_safe() {
    let mut k = v3_kernel();
    k.register_tool(ToolId::new("web_fetch")).unwrap();
    let a1 = AgentId::new("a1");
    k.delegate(AgentId::root(), a1.clone()).unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::NetworkEgress)
        .unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::CreditBudget)
        .unwrap();
    k.sentinel_credit_budget(a1.clone(), BUDGET_CAPACITY)
        .unwrap();

    k.invoke_start(
        a1.clone(),
        ToolId::new("web_fetch"),
        InvocationId::new("i1"),
        VecSet::from([EgressKind::NetworkExternal]),
    )
    .unwrap();
    let ev = k
        .invoke_complete(a1.clone(), InvocationId::new("i1"))
        .unwrap();
    assert_eq!(
        ev.action,
        KernelAction::InvokeComplete {
            agent: a1.clone(),
            inv: InvocationId::new("i1"),
            endorsed: false,
        }
    );
    assert!(
        k.state()
            .integ_levels
            .get(&a1)
            .unwrap()
            .contains(&IntegLevel::Untrusted),
        "missing cap_declassify fails safe: routes to the unendorsed branch, not an error"
    );
}

/// Scenario 15: override armed, flow admissible via ALLOW anyway -> override still
/// consumed (eager); re-arm via grant_override restores it at weighted price.
#[test]
fn scenario15_override_consumed_eagerly_via_allow_then_rearmed_at_weighted_price() {
    let mut k = v3_kernel();
    k.register_tool(ToolId::new("send_email")).unwrap();
    let a1 = AgentId::new("a1");
    k.delegate(AgentId::root(), a1.clone()).unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::NetworkEgress)
        .unwrap();

    k.grant_override(
        AgentId::root(),
        a1.clone(),
        ToolId::new("send_email"),
        ConfLevel::Sensitive,
    )
    .unwrap();
    let budget_after_first_arm = k.state().budget(&AgentId::root());
    assert_eq!(budget_after_first_arm, BUDGET_CAPACITY - 2);

    k.sentinel_elevate_taint(a1.clone(), ConfLevel::Sensitive)
        .unwrap();

    // The flow is admissible via ALLOW (the ceiling covers sensitive) -- the override is
    // not needed to justify admission, but eager consumption spends it anyway.
    k.invoke_start(
        a1.clone(),
        ToolId::new("send_email"),
        InvocationId::new("i1"),
        VecSet::from([EgressKind::NetworkExternal]),
    )
    .unwrap();
    assert!(k.state().override_consumed(&a1, &ToolId::new("send_email"), ConfLevel::Sensitive));

    k.invoke_complete(a1.clone(), InvocationId::new("i1"))
        .unwrap();

    k.grant_override(
        AgentId::root(),
        a1.clone(),
        ToolId::new("send_email"),
        ConfLevel::Sensitive,
    )
    .unwrap();
    assert_eq!(k.state().budget(&AgentId::root()), budget_after_first_arm - 2);
    assert!(!k.state().override_consumed(&a1, &ToolId::new("send_email"), ConfLevel::Sensitive));
}

/// Scenario 16: unregister_tool with an in-flight invocation -> denied; after completion
/// -> succeeds; invoking an unregistered tool -> denied.
#[test]
fn scenario16_unregister_blocks_in_flight_then_succeeds_then_denies_invoke() {
    let mut k = v3_kernel();
    k.register_tool(ToolId::new("delete_repo")).unwrap();
    let a1 = AgentId::new("a1");
    k.delegate(AgentId::root(), a1.clone()).unwrap();
    k.grant_capability(AgentId::root(), a1.clone(), CapKind::FilesystemDelete)
        .unwrap();

    k.invoke_start(
        a1.clone(),
        ToolId::new("delete_repo"),
        InvocationId::new("i1"),
        VecSet::new(),
    )
    .unwrap();

    let blocked = k.unregister_tool(ToolId::new("delete_repo"));
    assert_eq!(blocked.unwrap_err(), KernelError::ToolInFlight);

    k.invoke_complete(a1.clone(), InvocationId::new("i1"))
        .unwrap();
    k.unregister_tool(ToolId::new("delete_repo")).unwrap();

    let denied = k.invoke_start(
        a1,
        ToolId::new("delete_repo"),
        InvocationId::new("i2"),
        VecSet::new(),
    );
    assert_eq!(denied.unwrap_err(), KernelError::ToolNotRegistered);
}
