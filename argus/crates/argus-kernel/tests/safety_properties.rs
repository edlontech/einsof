use argus_kernel::*;
use argus_kernel::VecSet;

struct AllowAll;
impl AuthorizerOracle for AllowAll {
    fn allows(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
        true
    }
}
struct PassAll;
impl ContentGateOracle for PassAll {
    fn passes(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
        true
    }
}
struct ConformsAll;
impl ConformanceOracle for ConformsAll {
    fn conforms(&self, _: &AgentId, _: &ToolId, _: &KernelState, _: &BackgroundTheory) -> bool {
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
    )
    .unwrap();
    k.invoke_complete(AgentId::new("a1"), InvocationId::new("i1"))
        .unwrap();

    let result = k.invoke_start(
        AgentId::new("a1"),
        ToolId::new("send_email"),
        InvocationId::new("i2"),
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
    // Delegated children spawn at budget 0 (design finding 5); credit before the endorsed
    // path can be afforded.
    k.sentinel_credit_budget(AgentId::new("a1"), BUDGET_CAPACITY)
        .unwrap();

    k.invoke_start(
        AgentId::new("a1"),
        ToolId::new("check_exists"),
        InvocationId::new("i1"),
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
    )
    .unwrap();

    let result = k.invoke_start(
        AgentId::new("a1"),
        ToolId::new("send_email"),
        InvocationId::new("i2"),
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

    k.return_endorsed(AgentId::new("c"), AgentId::new("p"))
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
    // Delegated children spawn at budget 0 (design finding 5); credit to capacity to exercise
    // the exhaustion behavior this test is about.
    k.sentinel_credit_budget(AgentId::new("a1"), BUDGET_CAPACITY).unwrap();

    // 8 cycles × weight-2 = 16 debits; budget starts at 16 (explicitly credited).
    let mut i = 0u8;
    while i < 8 {
        let inv = InvocationId::new(&format!("inv-{i}"));
        k.invoke_start(AgentId::new("a1"), ToolId::new("check_exists"), inv.clone()).unwrap();
        k.invoke_complete(AgentId::new("a1"), inv).unwrap();
        i += 1;
    }
    assert_eq!(k.state().budget(&AgentId::new("a1")), 0);
    assert!(k.state().taint_levels.get(&AgentId::new("a1")).is_none(), "no taint before exhaustion");

    // 9th cycle: affordable(2) == false → full-taint branch.
    k.invoke_start(AgentId::new("a1"), ToolId::new("check_exists"), InvocationId::new("inv-8")).unwrap();
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
    k.invoke_start(agent.clone(), ToolId::new("send_email"), InvocationId::new("inv-1"))
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
    k.invoke_start(agent.clone(), ToolId::new("send_email"), InvocationId::new("inv-2"))
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
    );
    assert!(blocked.is_err(), "invoke_start must fail: re-armed override also single-use");
}
