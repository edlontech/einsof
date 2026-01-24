use argus_kernel::*;
use std::collections::BTreeSet;

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
struct NoopStore;
impl EventStore for NoopStore {
    fn append(&self, _: &KernelEvent) -> Result<(), KernelError> {
        Ok(())
    }
}

fn test_kernel() -> Kernel<AllowAll, PassAll, NoopStore> {
    let mut b = BackgroundTheoryBuilder::new();
    b.register_tool(
        ToolId::new("read_file"),
        ToolMetadata {
            capabilities: BTreeSet::from([CapKind::FilesystemRead]),
            egress: BTreeSet::new(),
            conf_floor: ConfLevel::Sensitive,
            endorsed: false,
        },
    );
    b.register_tool(
        ToolId::new("send_email"),
        ToolMetadata {
            capabilities: BTreeSet::from([CapKind::NetworkEgress]),
            egress: BTreeSet::from([EgressKind::NetworkExternal]),
            conf_floor: ConfLevel::Public,
            endorsed: false,
        },
    );
    b.register_tool(
        ToolId::new("check_exists"),
        ToolMetadata {
            capabilities: BTreeSet::from([CapKind::FilesystemRead]),
            egress: BTreeSet::new(),
            conf_floor: ConfLevel::Sensitive,
            endorsed: true,
        },
    );
    b.set_flow(
        ConfLevel::Public,
        EgressKind::NetworkExternal,
        FlowMode::Allow,
    );
    Kernel::new(b.build(), AllowAll, PassAll, NoopStore)
}

/// Safety 1: root_always_active
/// Root must remain active through all operations.
#[test]
fn root_survives_all_operations() {
    let mut k = test_kernel();
    k.register_tool(ToolId::new("read_file")).unwrap();
    k.delegate(AgentId::root(), AgentId::new("a1")).unwrap();
    k.grant_capability(
        AgentId::root(),
        AgentId::new("a1"),
        CapKind::FilesystemRead,
    )
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
    k.grant_capability(
        AgentId::root(),
        AgentId::new("a1"),
        CapKind::FilesystemRead,
    )
    .unwrap();
    k.grant_capability(
        AgentId::root(),
        AgentId::new("a1"),
        CapKind::NetworkEgress,
    )
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
    k.delegate(AgentId::root(), AgentId::new("parent"))
        .unwrap();
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
    k.grant_capability(
        AgentId::root(),
        AgentId::new("a1"),
        CapKind::FilesystemRead,
    )
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
    k.grant_capability(
        AgentId::root(),
        AgentId::new("a1"),
        CapKind::FilesystemRead,
    )
    .unwrap();

    k.invoke_start(
        AgentId::new("a1"),
        ToolId::new("check_exists"),
        InvocationId::new("i1"),
    )
    .unwrap();
    k.invoke_complete(AgentId::new("a1"), InvocationId::new("i1"))
        .unwrap();

    assert!(k
        .state()
        .taint_levels
        .get(&AgentId::new("a1"))
        .is_none());
}

/// return_unendorsed propagates child taint to parent.
#[test]
fn return_unendorsed_propagates_taint_to_parent() {
    let mut k = test_kernel();
    k.register_tool(ToolId::new("read_file")).unwrap();
    k.delegate(AgentId::root(), AgentId::new("parent"))
        .unwrap();
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
    assert!(k
        .state()
        .taint_levels
        .get(&AgentId::new("parent"))
        .unwrap()
        .contains(&ConfLevel::Sensitive));
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
    k.grant_capability(
        AgentId::root(),
        AgentId::new("a1"),
        CapKind::FilesystemRead,
    )
    .unwrap();
    k.grant_capability(
        AgentId::root(),
        AgentId::new("a1"),
        CapKind::NetworkEgress,
    )
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
    k.grant_capability(AgentId::new("p"), AgentId::new("c"), CapKind::FilesystemRead)
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
    assert!(k
        .state()
        .taint_levels
        .get(&AgentId::new("p"))
        .unwrap()
        .contains(&ConfLevel::Sensitive));
}

/// return_endorsed does NOT propagate child taint to parent.
/// This is the "I vouch for this child's output" path.
#[test]
fn return_endorsed_does_not_propagate_taint() {
    let mut k = test_kernel();
    k.register_tool(ToolId::new("read_file")).unwrap();
    k.delegate(AgentId::root(), AgentId::new("p")).unwrap();
    k.grant_capability(
        AgentId::root(),
        AgentId::new("p"),
        CapKind::FilesystemRead,
    )
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

    k.return_endorsed(AgentId::new("c"), AgentId::new("p"))
        .unwrap();
    assert!(k.state().taint_levels.get(&AgentId::new("p")).is_none());
}

/// Event store failure leaves kernel in consistent state.
#[test]
fn event_store_failure_preserves_consistency() {
    struct FailStore;
    impl EventStore for FailStore {
        fn append(&self, _: &KernelEvent) -> Result<(), KernelError> {
            Err(KernelError::EventStoreError("simulated failure".into()))
        }
    }

    let bg = BackgroundTheoryBuilder::new().build();
    let mut k = Kernel::new(bg, AllowAll, PassAll, FailStore);

    let result = k.delegate(AgentId::root(), AgentId::new("a1"));
    assert!(result.is_err());
    assert_eq!(k.sequence(), 0);
    assert!(!k.state().agent_active.contains(&AgentId::new("a1")));
}
