//! End-to-end V4 safety-property scenarios exercised through the public `Kernel` API: the
//! prompt-injection (integrity) and confidentiality containment headlines, plus a positive
//! liveness path. These complement the unit tests; the exhaustive proof is the Lean refinement.

use std::cell::RefCell;

use argus_kernel::{
    ActionPolicySnapshot, AgentId, AuthorizerOracle, BackgroundTheory, BackgroundTheoryBuilder,
    ChallengeId, ConfLevel, ContentHash, Disposition, EgressKind, EventStore, IntegLevel,
    InvocationId, Kernel, KernelError, KernelEvent, KernelState, PolicyDigest, ToolId, VecSet,
};

struct AllowAll;
impl AuthorizerOracle for AllowAll {
    fn allows(
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

struct NullStore(RefCell<u64>);
impl EventStore for NullStore {
    fn append(&self, _: &KernelEvent) -> Result<(), KernelError> {
        *self.0.borrow_mut() += 1;
        Ok(())
    }
}

fn kernel() -> Kernel<AllowAll, NullStore> {
    Kernel::new(
        BackgroundTheoryBuilder::new().build(),
        AllowAll,
        NullStore(RefCell::new(0)),
    )
}

fn snapshot(
    conf_clearance: ConfLevel,
    integ_floor: IntegLevel,
    output_conf: ConfLevel,
    output_integ: IntegLevel,
    declared_egress: VecSet<EgressKind>,
) -> ActionPolicySnapshot {
    ActionPolicySnapshot {
        tool: ToolId::new("tool"),
        required_caps: VecSet::new(),
        conf_clearance,
        integ_floor,
        // Coherent band: inspect floor equals the allow floor (empty inspect band).
        integ_inspect: integ_floor,
        output_conf,
        output_integ,
        declared_egress,
        policy_digest: PolicyDigest::new("d"),
    }
}

/// Prompt-injection containment: an agent that has ingested untrusted content cannot drive a
/// destructive tool whose integrity floor it no longer clears.
#[test]
fn ingested_untrusted_content_cannot_drive_a_trusted_floor_tool() {
    let mut k = kernel();
    k.register_tool(ToolId::new("tool")).unwrap();
    k.delegate(AgentId::root(), AgentId::new("a")).unwrap();
    // Ingest untrusted content: the agent's integrity drops to Untrusted.
    k.ingest(
        AgentId::new("a"),
        None,
        ConfLevel::Public,
        IntegLevel::Untrusted,
    )
    .unwrap();
    // A destructive tool requires a Trusted integrity floor -> the integrity gate denies.
    let err = k
        .begin_invocation(
            AgentId::new("a"),
            InvocationId::new("inv"),
            ChallengeId::new("c"),
            snapshot(
                ConfLevel::Restricted,
                IntegLevel::Trusted,
                ConfLevel::Public,
                IntegLevel::Attested,
                VecSet::new(),
            ),
            VecSet::new(),
            ContentHash::new("ah"),
        )
        .unwrap_err();
    assert_eq!(err, KernelError::IntegrityFloorDenied);
    assert!(!k.state().pending.contains_key(&InvocationId::new("inv")));
}

/// Confidentiality containment: a sensitively-tainted agent cannot run an egress-bearing action
/// on a channel with no admitting ceiling.
#[test]
fn sensitive_taint_cannot_egress_on_an_unceilinged_channel() {
    let mut k = kernel();
    k.register_tool(ToolId::new("tool")).unwrap();
    k.delegate(AgentId::root(), AgentId::new("a")).unwrap();
    k.ingest(
        AgentId::new("a"),
        None,
        ConfLevel::Sensitive,
        IntegLevel::Attested,
    )
    .unwrap();
    let err = k
        .begin_invocation(
            AgentId::new("a"),
            InvocationId::new("inv"),
            ChallengeId::new("c"),
            snapshot(
                ConfLevel::Restricted,
                IntegLevel::Untrusted,
                ConfLevel::Public,
                IntegLevel::Attested,
                VecSet::from([EgressKind::NetworkExternal]),
            ),
            VecSet::from([EgressKind::NetworkExternal]),
            ContentHash::new("ah"),
        )
        .unwrap_err();
    assert_eq!(err, KernelError::FlowGateBlocked);
}

/// Liveness: a clean agent invoking a within-clearance tool is admitted and settles, absorbing the
/// frozen output labels.
#[test]
fn clean_agent_admits_and_settles() {
    let mut k = kernel();
    k.register_tool(ToolId::new("tool")).unwrap();
    k.delegate(AgentId::root(), AgentId::new("a")).unwrap();
    k.begin_invocation(
        AgentId::new("a"),
        InvocationId::new("inv"),
        ChallengeId::new("c"),
        snapshot(
            ConfLevel::Restricted,
            IntegLevel::Untrusted,
            ConfLevel::Sensitive,
            IntegLevel::Attested,
            VecSet::new(),
        ),
        VecSet::new(),
        ContentHash::new("ah"),
    )
    .unwrap();
    let rec = k
        .state()
        .pending
        .get_cloned(&InvocationId::new("inv"))
        .unwrap();
    assert_eq!(rec.disposition, Disposition::Permitted);
    k.settle_invocation(
        InvocationId::new("inv"),
        argus_kernel::Outcome::Success,
        None,
    )
    .unwrap();
    assert!(
        k.state()
            .pending
            .get_cloned(&InvocationId::new("inv"))
            .is_none()
    );
    assert!(
        k.state()
            .taint_levels
            .set_contains(&AgentId::new("a"), &ConfLevel::Sensitive)
    );
}
