use argus_kernel::{
    AgentId, AssignmentDigest, BackgroundTheory, BackgroundTheoryBuilder, CrossingId, KernelState,
    ToolId, transitions,
};
use argus_nif::{
    ActionN, CommandN, ConfLevelN, CrossBranchN, CrossInputN, CrossOutputActionN,
    CrossOutputCommandN, DispositionN, FallbackN, IntegLevelN, KernelErrorN, RegisterToolActionN,
    RegisterToolCommandN,
};

fn state_with_crossing_agents(background: &BackgroundTheory) -> KernelState {
    let (state, _) = transitions::delegate(
        KernelState::initial(),
        background,
        AgentId::root(),
        AgentId::new("source"),
    )
    .expect("source delegation should be accepted");
    let (state, _) =
        transitions::delegate(state, background, AgentId::root(), AgentId::new("receiver"))
            .expect("receiver delegation should be accepted");
    state
}

fn cross_command(crossing: &str, fallback: FallbackN) -> CommandN {
    CommandN::CrossOutput(CrossOutputCommandN {
        input: CrossInputN {
            src: "source".to_owned(),
            rcv: "receiver".to_owned(),
            crossing: crossing.to_owned(),
            output_hash: "output".to_owned(),
            descriptor: "descriptor".to_owned(),
            fallback,
            t_integ: IntegLevelN::Trusted,
            t_conf: Some(ConfLevelN::Internal),
            assignment: "assignment".to_owned(),
            evidence: None,
            released_conf: ConfLevelN::Internal,
            released_integ: IntegLevelN::Standard,
        },
    })
}

#[test]
fn register_tool_dispatches_to_the_kernel_transition() {
    let command = CommandN::RegisterTool(RegisterToolCommandN {
        tool: "tool:v1:hash".to_owned(),
    });

    let (state, action) = command
        .apply(
            KernelState::initial(),
            &BackgroundTheoryBuilder::new().build(),
        )
        .expect("register_tool should be accepted");

    assert_eq!(
        (
            state.tool_registered.contains(&ToolId::new("tool:v1:hash")),
            action
        ),
        (
            true,
            ActionN::RegisterTool(RegisterToolActionN {
                tool: "tool:v1:hash".to_owned(),
            }),
        )
    );
}

#[test]
fn duplicate_registration_returns_the_closed_kernel_error() {
    let command = CommandN::RegisterTool(RegisterToolCommandN {
        tool: "tool:v1:hash".to_owned(),
    });
    let (state, _) = command
        .clone()
        .apply(
            KernelState::initial(),
            &BackgroundTheoryBuilder::new().build(),
        )
        .expect("first registration should be accepted");

    assert_eq!(
        command.apply(state, &BackgroundTheoryBuilder::new().build()),
        Err(KernelErrorN::ToolAlreadyRegistered)
    );
}

#[test]
fn cross_output_without_a_grant_uses_the_declared_fail_branch() {
    let background = BackgroundTheoryBuilder::new().build();
    let state = state_with_crossing_agents(&background);

    let (state, action) = cross_command("crossing", FallbackN::Fail)
        .apply(state, &background)
        .expect("the fail fallback is a committed crossing branch");

    assert_eq!(
        (
            state
                .consumed_crossings
                .contains(&CrossingId::new("crossing")),
            action
        ),
        (
            true,
            ActionN::CrossOutput(CrossOutputActionN {
                src: "source".to_owned(),
                rcv: "receiver".to_owned(),
                crossing: "crossing".to_owned(),
                branch: CrossBranchN::Fail,
                disposition: DispositionN::Permitted,
            }),
        )
    );
}

#[test]
fn cross_output_with_an_exhausted_grant_uses_the_unendorsed_fallback() {
    let background = BackgroundTheoryBuilder::new().build();
    let state = state_with_crossing_agents(&background);
    let (state, _) = transitions::grant_crossing(
        state,
        &background,
        AgentId::root(),
        AgentId::new("receiver"),
        AssignmentDigest::new("assignment"),
        0,
    )
    .expect("zero-use grant provisioning should be accepted");

    let (_, action) = cross_command("exhausted", FallbackN::ReleaseUnendorsed)
        .apply(state, &background)
        .expect("an exhausted grant selects the declared fallback");

    assert!(matches!(
        action,
        ActionN::CrossOutput(CrossOutputActionN {
            branch: CrossBranchN::Unendorsed,
            ..
        })
    ));
}

#[test]
fn cross_output_with_a_revoked_grant_uses_the_fail_fallback() {
    let background = BackgroundTheoryBuilder::new().build();
    let state = state_with_crossing_agents(&background);
    let (state, _) = transitions::grant_crossing(
        state,
        &background,
        AgentId::root(),
        AgentId::new("receiver"),
        AssignmentDigest::new("assignment"),
        1,
    )
    .expect("grant provisioning should be accepted");
    let (state, _) = transitions::revoke(
        state,
        &background,
        AgentId::root(),
        AgentId::new("receiver"),
    )
    .expect("receiver revocation should be accepted");
    let (state, _) = transitions::delegate(
        state,
        &background,
        AgentId::root(),
        AgentId::new("receiver"),
    )
    .expect("receiver re-delegation should be accepted");

    let (_, action) = cross_command("revoked", FallbackN::Fail)
        .apply(state, &background)
        .expect("a revoked grant selects the declared fallback");

    assert!(matches!(
        action,
        ActionN::CrossOutput(CrossOutputActionN {
            branch: CrossBranchN::Fail,
            ..
        })
    ));
}
