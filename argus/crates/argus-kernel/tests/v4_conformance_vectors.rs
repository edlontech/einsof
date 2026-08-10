#[path = "../../../../ex_argus/priv/conformance/v4_schema.rs"]
mod schema;

use std::fs;
use std::path::{Path, PathBuf};

use argus_kernel::{
    ActionPolicySnapshot, Admission, AgentId, AssignmentDigest, AttestationId, BackgroundTheory,
    BackgroundTheoryBuilder, CapKind, ChallengeId, ConfLevel, ConformanceAttestation, ContentHash,
    CrossInput, CrossingId, Disposition, EgressKind, Fallback, InspectionAttestation, IntegLevel,
    InvocationId, KernelAction, KernelError, KernelState, Mode, Outcome, PolicyDigest,
    ResolutionAttestation, ToolId, VecSet, transitions,
};
use schema::{Corpus, ResultExpectation};

fn corpus_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../../ex_argus/priv/conformance/v4.json")
}

fn corpus_text() -> String {
    fs::read_to_string(corpus_path()).expect("shared conformance corpus must be readable")
}

fn corpus() -> Corpus {
    Corpus::parse(&corpus_text()).expect("checked-in corpus must validate")
}

#[test]
fn checked_in_corpus_has_a_strict_valid_schema() {
    corpus();
}

#[test]
fn parser_rejects_unknown_missing_duplicate_enum_set_hex_order_and_trailing_content() {
    let input = corpus_text();
    let malformed = [
        input.replacen("\"schema\":", "\"unknown\":true,\"schema\":", 1),
        input.replacen("\"version\": 5,", "", 1),
        input.replacen("\"schema\":", "\"schema\":\"duplicate\",\"schema\":", 1),
        input.replacen("\"mode\": \"enforce\"", "\"mode\": \"unknown\"", 1),
        input.replacen(
            "\"required_caps\": []",
            "\"required_caps\": [\"ipc\",\"ipc\"]",
            1,
        ),
        input.replacen("\"head\": \"", "\"head\": \"GG", 1),
        input.replacen("\"sequence\": 1", "\"sequence\": 3", 1),
        format!("{input} true"),
    ];

    for value in malformed {
        assert!(Corpus::parse(&value).is_err());
    }
}

#[test]
fn pure_public_transitions_match_every_semantic_action_error_and_full_state() {
    for case in corpus().semantic_cases {
        let background = background(&case.background);
        let mut state = KernelState::initial();
        let mut accepted = 0;

        for step in case.steps {
            let before = state.clone();
            match (
                apply(&step.command, state.clone(), &background),
                step.expected.result,
            ) {
                (Ok((next, actual)), ResultExpectation::Accepted { action: expected }) => {
                    assert_eq!(action(actual), expected, "{}:{} action", case.id, step.id);
                    state = next;
                    accepted += 1;
                }
                (Err(actual), ResultExpectation::Error { reason, .. }) => {
                    assert_eq!(
                        actual,
                        kernel_error(&reason),
                        "{}:{} error",
                        case.id,
                        step.id
                    );
                    assert_eq!(state, before, "{}:{} refusal state", case.id, step.id);
                }
                (actual, expected) => panic!(
                    "{}:{} mismatch: {actual:?} vs {expected:?}",
                    case.id, step.id
                ),
            }
            assert_eq!(
                project(&state),
                step.expected.state,
                "{}:{} state",
                case.id,
                step.id
            );
            assert_eq!(
                accepted, step.expected.chain.sequence,
                "{}:{} accepted count",
                case.id, step.id
            );
        }
    }
}

#[test]
fn blocked_disposition_is_closed_but_unreachable_from_the_initial_state() {
    assert!(
        corpus()
            .vocabulary
            .dispositions
            .contains(&schema::Disposition::Blocked)
    );
    for case in corpus().semantic_cases {
        for step in case.steps {
            if let ResultExpectation::Accepted { action } = step.expected.result {
                assert!(!action_has_blocked(&action));
            }
            assert!(
                step.expected
                    .state
                    .pending
                    .iter()
                    .all(|(_, pending)| pending.disposition != schema::Disposition::Blocked)
            );
        }
    }
}

fn apply(
    command: &schema::Command,
    state: KernelState,
    background: &BackgroundTheory,
) -> Result<(KernelState, KernelAction), KernelError> {
    use schema::Command as C;
    match command {
        C::RegisterTool { tool } => transitions::register_tool(state, ToolId(tool.clone())),
        C::UnregisterTool { tool } => transitions::unregister_tool(state, ToolId(tool.clone())),
        C::Delegate { grantor, grantee } => transitions::delegate(
            state,
            background,
            AgentId(grantor.clone()),
            AgentId(grantee.clone()),
        ),
        C::GrantCapability {
            parent,
            child,
            cap: value,
        } => transitions::grant_capability(
            state,
            AgentId(parent.clone()),
            AgentId(child.clone()),
            cap(*value),
        ),
        C::GrantCrossing {
            grantor,
            agent,
            assignment,
            n,
        } => transitions::grant_crossing(
            state,
            background,
            AgentId(grantor.clone()),
            AgentId(agent.clone()),
            AssignmentDigest(assignment.clone()),
            *n,
        ),
        C::Revoke { parent, target } => transitions::revoke(
            state,
            background,
            AgentId(parent.clone()),
            AgentId(target.clone()),
        ),
        C::CascadeRevoke { child, parent } => transitions::cascade_revoke(
            state,
            background,
            AgentId(child.clone()),
            AgentId(parent.clone()),
        ),
        C::Ingest {
            agent,
            src,
            pconf,
            pinteg,
        } => transitions::ingest(
            state,
            background,
            AgentId(agent.clone()),
            src.clone().map(AgentId),
            conf(*pconf),
            integ(*pinteg),
        ),
        C::BeginInvocation {
            agent,
            inv,
            challenge,
            policy: value,
            egress: values,
            args_hash,
            authorized,
        } => transitions::begin_invocation(
            state,
            background,
            AgentId(agent.clone()),
            InvocationId(inv.clone()),
            ChallengeId(challenge.clone()),
            policy(value),
            values.iter().copied().map(egress).collect(),
            ContentHash(args_hash.clone()),
            *authorized,
        ),
        C::AuthorizeInspected { inv, attestation } => transitions::authorize_inspected(
            state,
            background,
            InvocationId(inv.clone()),
            InspectionAttestation {
                id: AttestationId(attestation.id.clone()),
                inv: InvocationId(attestation.inv.clone()),
                challenge: ChallengeId(attestation.challenge.clone()),
                args_hash: ContentHash(attestation.args_hash.clone()),
                policy_digest: PolicyDigest(attestation.policy_digest.clone()),
                positive: attestation.positive,
            },
        ),
        C::SettleInvocation {
            inv,
            outcome: value,
            resolution,
        } => transitions::settle_invocation(
            state,
            InvocationId(inv.clone()),
            outcome(*value),
            resolution.as_ref().map(|item| ResolutionAttestation {
                id: AttestationId(item.id.clone()),
                inv: InvocationId(item.inv.clone()),
                outcome: outcome(item.outcome),
            }),
        ),
        C::CrossOutput { input } => transitions::cross_output(
            state,
            background,
            CrossInput {
                src: AgentId(input.src.clone()),
                rcv: AgentId(input.rcv.clone()),
                crossing: CrossingId(input.crossing.clone()),
                output_hash: ContentHash(input.output_hash.clone()),
                descriptor: ContentHash(input.descriptor.clone()),
                fallback: fallback(input.fallback),
                t_integ: integ(input.t_integ),
                t_conf: input.t_conf.map(conf),
                assignment: AssignmentDigest(input.assignment.clone()),
                evidence: input.evidence.as_ref().map(|item| ConformanceAttestation {
                    id: AttestationId(item.id.clone()),
                    output: ContentHash(item.output.clone()),
                    src: AgentId(item.src.clone()),
                    rcv: AgentId(item.rcv.clone()),
                    descriptor: ContentHash(item.descriptor.clone()),
                    assignment: AssignmentDigest(item.assignment.clone()),
                    positive: item.positive,
                }),
                released_conf: conf(input.released_conf),
                released_integ: integ(input.released_integ),
            },
        ),
    }
}

fn background(value: &schema::Background) -> BackgroundTheory {
    let mut builder = BackgroundTheoryBuilder::new();
    builder.set_mode(match value.mode {
        schema::Mode::Enforce => Mode::Enforce,
        schema::Mode::Monitor => Mode::Monitor,
    });
    for (kind, allow, inspect) in [
        (
            EgressKind::NetworkExternal,
            value.allow_ceiling.network_external,
            value.inspect_ceiling.network_external,
        ),
        (
            EgressKind::NetworkInternal,
            value.allow_ceiling.network_internal,
            value.inspect_ceiling.network_internal,
        ),
        (
            EgressKind::FilesystemWrite,
            value.allow_ceiling.filesystem_write,
            value.inspect_ceiling.filesystem_write,
        ),
        (
            EgressKind::Ipc,
            value.allow_ceiling.ipc,
            value.inspect_ceiling.ipc,
        ),
    ] {
        builder.set_egress_ceilings(kind, allow.map(conf), inspect.map(conf));
    }
    builder.build()
}

fn policy(value: &schema::Policy) -> ActionPolicySnapshot {
    ActionPolicySnapshot {
        tool: ToolId(value.tool.clone()),
        required_caps: value.required_caps.iter().copied().map(cap).collect(),
        conf_clearance: conf(value.conf_clearance),
        integ_floor: integ(value.integ_floor),
        integ_inspect: integ(value.integ_inspect),
        output_conf: conf(value.output_conf),
        output_integ: integ(value.output_integ),
        declared_egress: value.declared_egress.iter().copied().map(egress).collect(),
        policy_digest: PolicyDigest(value.policy_digest.clone()),
    }
}

fn action(value: KernelAction) -> schema::Action {
    match value {
        KernelAction::RegisterTool { tool } => schema::Action::RegisterTool { tool: tool.0 },
        KernelAction::UnregisterTool { tool } => schema::Action::UnregisterTool { tool: tool.0 },
        KernelAction::Delegate { grantor, grantee } => schema::Action::Delegate {
            grantor: grantor.0,
            grantee: grantee.0,
        },
        KernelAction::GrantCapability {
            parent,
            child,
            cap: value,
        } => schema::Action::GrantCapability {
            parent: parent.0,
            child: child.0,
            cap: cap_s(value),
        },
        KernelAction::GrantCrossing {
            grantor,
            agent,
            assignment,
            n,
        } => schema::Action::GrantCrossing {
            grantor: grantor.0,
            agent: agent.0,
            assignment: assignment.0,
            n,
        },
        KernelAction::Revoke { parent, target } => schema::Action::Revoke {
            parent: parent.0,
            target: target.0,
        },
        KernelAction::CascadeRevoke { child, parent } => schema::Action::CascadeRevoke {
            child: child.0,
            parent: parent.0,
        },
        KernelAction::Ingest {
            agent,
            src,
            pconf,
            pinteg,
            disposition,
        } => schema::Action::Ingest {
            agent: agent.0,
            src: src.map(|item| item.0),
            pconf: conf_s(pconf),
            pinteg: integ_s(pinteg),
            disposition: disposition_s(disposition),
        },
        KernelAction::BeginInvocation {
            agent,
            inv,
            tool,
            verdict,
            authorized,
        } => schema::Action::BeginInvocation {
            agent: agent.0,
            inv: inv.0,
            tool: tool.0,
            verdict: verdict_s(verdict),
            authorized,
        },
        KernelAction::AuthorizeInspected {
            inv,
            attestation,
            admitted,
        } => schema::Action::AuthorizeInspected {
            inv: inv.0,
            attestation: attestation.0,
            admitted,
        },
        KernelAction::SettleInvocation {
            inv,
            agent,
            disposition,
            outcome,
            clvl,
            ilvl,
            resolution,
        } => schema::Action::SettleInvocation {
            inv: inv.0,
            agent: agent.0,
            disposition: disposition_s(disposition),
            outcome: outcome_s(outcome),
            clvl: conf_s(clvl),
            ilvl: integ_s(ilvl),
            resolution: resolution.map(|item| item.0),
        },
        KernelAction::CrossOutput {
            src,
            rcv,
            crossing,
            branch,
            disposition,
        } => schema::Action::CrossOutput {
            src: src.0,
            rcv: rcv.0,
            crossing: crossing.0,
            branch: match branch {
                argus_kernel::CrossBranch::Endorsed => schema::CrossBranch::Endorsed,
                argus_kernel::CrossBranch::Unendorsed => schema::CrossBranch::Unendorsed,
                argus_kernel::CrossBranch::Fail => schema::CrossBranch::Fail,
            },
            disposition: disposition_s(disposition),
        },
    }
}

fn project(state: &KernelState) -> schema::State {
    let mut agent_active: Vec<_> = state
        .agent_active
        .iter()
        .map(|item| item.0.clone())
        .collect();
    sort_strings(&mut agent_active);
    let mut agent_parent: Vec<_> = state
        .agent_parent
        .iter()
        .map(|(key, value)| (key.0.clone(), value.0.clone()))
        .collect();
    sort_map(&mut agent_parent);
    let mut agent_cap: Vec<_> = state
        .agent_cap
        .iter()
        .map(|(key, values)| {
            let mut values: Vec<_> = values.iter().copied().map(cap_s).collect();
            values.sort_by_key(|item| schema::CAPABILITIES.iter().position(|value| value == item));
            (key.0.clone(), values)
        })
        .collect();
    sort_map(&mut agent_cap);
    let mut taint_levels: Vec<_> = state
        .taint_levels
        .iter()
        .map(|(key, values)| {
            let mut values: Vec<_> = values.iter().copied().map(conf_s).collect();
            values.sort_by_key(|item| {
                schema::CONFIDENTIALITY
                    .iter()
                    .position(|value| value == item)
            });
            (key.0.clone(), values)
        })
        .collect();
    sort_map(&mut taint_levels);
    let mut integ_levels: Vec<_> = state
        .integ_levels
        .iter()
        .map(|(key, values)| {
            let mut values: Vec<_> = values.iter().copied().map(integ_s).collect();
            values.sort_by_key(|item| schema::INTEGRITY.iter().position(|value| value == item));
            (key.0.clone(), values)
        })
        .collect();
    sort_map(&mut integ_levels);
    let mut pending: Vec<_> = state
        .pending
        .iter()
        .map(|(key, value)| {
            (
                key.0.clone(),
                schema::Pending {
                    agent: value.agent.0.clone(),
                    policy: policy_s(&value.policy),
                    egress: sorted_egress(&value.egress),
                    admission: admission_s(&value.admission),
                    disposition: disposition_s(value.disposition),
                    authorized: value.authorized,
                    quarantined: value.quarantined,
                },
            )
        })
        .collect();
    sort_map(&mut pending);
    let mut challenges: Vec<_> = state
        .challenges
        .iter()
        .map(|(key, value)| {
            (
                key.0.clone(),
                schema::Challenge {
                    challenge: value.challenge.0.clone(),
                    agent: value.agent.0.clone(),
                    policy: policy_s(&value.policy),
                    egress: sorted_egress(&value.egress),
                    args_hash: value.args_hash.0.clone(),
                    authorized: value.authorized,
                },
            )
        })
        .collect();
    sort_map(&mut challenges);
    let mut consumed_ids: Vec<_> = state
        .consumed_ids
        .iter()
        .map(|item| item.0.clone())
        .collect();
    sort_strings(&mut consumed_ids);
    let mut consumed_attestations: Vec<_> = state
        .consumed_attestations
        .iter()
        .map(|item| item.0.clone())
        .collect();
    sort_strings(&mut consumed_attestations);
    let mut consumed_crossings: Vec<_> = state
        .consumed_crossings
        .iter()
        .map(|item| item.0.clone())
        .collect();
    sort_strings(&mut consumed_crossings);
    let mut crossing_grants: Vec<_> = state
        .crossing_grants
        .iter()
        .map(|(key, value)| {
            (
                (key.agent.0.clone(), key.assignment.0.clone()),
                schema::CrossingGrant {
                    remaining: value.remaining,
                    provisioned: value.provisioned,
                },
            )
        })
        .collect();
    crossing_grants.sort_by(|left, right| {
        left.0
            .0
            .as_bytes()
            .cmp(right.0.0.as_bytes())
            .then_with(|| left.0.1.as_bytes().cmp(right.0.1.as_bytes()))
    });
    let mut tool_registered: Vec<_> = state
        .tool_registered
        .iter()
        .map(|item| item.0.clone())
        .collect();
    sort_strings(&mut tool_registered);
    schema::State {
        agent_active,
        agent_parent,
        agent_cap,
        taint_levels,
        integ_levels,
        pending,
        challenges,
        consumed_ids,
        consumed_attestations,
        consumed_crossings,
        crossing_grants,
        tool_registered,
    }
}

fn policy_s(value: &ActionPolicySnapshot) -> schema::Policy {
    schema::Policy {
        tool: value.tool.0.clone(),
        required_caps: {
            let mut items: Vec<_> = value.required_caps.iter().copied().map(cap_s).collect();
            items.sort_by_key(|item| schema::CAPABILITIES.iter().position(|value| value == item));
            items
        },
        conf_clearance: conf_s(value.conf_clearance),
        integ_floor: integ_s(value.integ_floor),
        integ_inspect: integ_s(value.integ_inspect),
        output_conf: conf_s(value.output_conf),
        output_integ: integ_s(value.output_integ),
        declared_egress: sorted_egress(&value.declared_egress),
        policy_digest: value.policy_digest.0.clone(),
    }
}
fn sorted_egress(values: &VecSet<EgressKind>) -> Vec<schema::Egress> {
    let mut items: Vec<_> = values.iter().copied().map(egress_s).collect();
    items.sort_by_key(|item| schema::EGRESS.iter().position(|value| value == item));
    items
}
fn admission_s(value: &Admission) -> schema::Admission {
    match value {
        Admission::Plain => schema::Admission {
            kind: schema::AdmissionTag::Plain,
            attestation: None,
        },
        Admission::Inspected(id) => schema::Admission {
            kind: schema::AdmissionTag::Inspected,
            attestation: Some(id.0.clone()),
        },
        Admission::Bypassed => schema::Admission {
            kind: schema::AdmissionTag::Bypassed,
            attestation: None,
        },
    }
}
fn sort_strings(values: &mut [String]) {
    values.sort_by(|left, right| left.as_bytes().cmp(right.as_bytes()));
}
fn sort_map<T>(values: &mut [(String, T)]) {
    values.sort_by(|left, right| left.0.as_bytes().cmp(right.0.as_bytes()));
}

fn cap(value: schema::Capability) -> CapKind {
    CapKind::ALL[schema::CAPABILITIES
        .iter()
        .position(|item| *item == value)
        .expect("closed capability")]
}
fn cap_s(value: CapKind) -> schema::Capability {
    schema::CAPABILITIES[CapKind::ALL
        .iter()
        .position(|item| *item == value)
        .expect("closed capability")]
}
fn conf(value: schema::Conf) -> ConfLevel {
    match value {
        schema::Conf::Public => ConfLevel::Public,
        schema::Conf::Internal => ConfLevel::Internal,
        schema::Conf::Sensitive => ConfLevel::Sensitive,
        schema::Conf::Restricted => ConfLevel::Restricted,
    }
}
fn conf_s(value: ConfLevel) -> schema::Conf {
    match value {
        ConfLevel::Public => schema::Conf::Public,
        ConfLevel::Internal => schema::Conf::Internal,
        ConfLevel::Sensitive => schema::Conf::Sensitive,
        ConfLevel::Restricted => schema::Conf::Restricted,
    }
}
fn integ(value: schema::Integ) -> IntegLevel {
    match value {
        schema::Integ::Untrusted => IntegLevel::Untrusted,
        schema::Integ::Standard => IntegLevel::Standard,
        schema::Integ::Trusted => IntegLevel::Trusted,
        schema::Integ::Attested => IntegLevel::Attested,
    }
}
fn integ_s(value: IntegLevel) -> schema::Integ {
    match value {
        IntegLevel::Untrusted => schema::Integ::Untrusted,
        IntegLevel::Standard => schema::Integ::Standard,
        IntegLevel::Trusted => schema::Integ::Trusted,
        IntegLevel::Attested => schema::Integ::Attested,
    }
}
fn egress(value: schema::Egress) -> EgressKind {
    match value {
        schema::Egress::NetworkExternal => EgressKind::NetworkExternal,
        schema::Egress::NetworkInternal => EgressKind::NetworkInternal,
        schema::Egress::FilesystemWrite => EgressKind::FilesystemWrite,
        schema::Egress::Ipc => EgressKind::Ipc,
    }
}
fn egress_s(value: EgressKind) -> schema::Egress {
    match value {
        EgressKind::NetworkExternal => schema::Egress::NetworkExternal,
        EgressKind::NetworkInternal => schema::Egress::NetworkInternal,
        EgressKind::FilesystemWrite => schema::Egress::FilesystemWrite,
        EgressKind::Ipc => schema::Egress::Ipc,
    }
}
fn outcome(value: schema::Outcome) -> Outcome {
    match value {
        schema::Outcome::Success => Outcome::Success,
        schema::Outcome::Failure => Outcome::Failure,
        schema::Outcome::Ambiguous => Outcome::Ambiguous,
    }
}
fn outcome_s(value: Outcome) -> schema::Outcome {
    match value {
        Outcome::Success => schema::Outcome::Success,
        Outcome::Failure => schema::Outcome::Failure,
        Outcome::Ambiguous => schema::Outcome::Ambiguous,
    }
}
fn fallback(value: schema::Fallback) -> Fallback {
    match value {
        schema::Fallback::Fail => Fallback::Fail,
        schema::Fallback::ReleaseUnendorsed => Fallback::ReleaseUnendorsed,
    }
}
fn disposition_s(value: Disposition) -> schema::Disposition {
    match value {
        Disposition::Permitted => schema::Disposition::Permitted,
        Disposition::Blocked => schema::Disposition::Blocked,
        Disposition::MonitorBypassed => schema::Disposition::MonitorBypassed,
    }
}
fn verdict_s(value: argus_kernel::Verdict) -> schema::Verdict {
    match value {
        argus_kernel::Verdict::Allow => schema::Verdict::Allow,
        argus_kernel::Verdict::InspectionRequired => schema::Verdict::InspectionRequired,
        argus_kernel::Verdict::Deny => schema::Verdict::Deny,
    }
}
fn action_has_blocked(value: &schema::Action) -> bool {
    match value {
        schema::Action::Ingest { disposition, .. }
        | schema::Action::SettleInvocation { disposition, .. }
        | schema::Action::CrossOutput { disposition, .. } => {
            *disposition == schema::Disposition::Blocked
        }
        _ => false,
    }
}

fn kernel_error(reason: &str) -> KernelError {
    match reason {
        "tool_already_registered" => KernelError::ToolAlreadyRegistered,
        "tool_not_registered" => KernelError::ToolNotRegistered,
        "tool_in_use" => KernelError::ToolInUse,
        "agent_inactive" => KernelError::AgentInactive,
        "agent_already_active" => KernelError::AgentAlreadyActive,
        "root_not_allowed" => KernelError::RootNotAllowed,
        "not_direct_child" => KernelError::NotDirectChild,
        "parent_still_active" => KernelError::ParentStillActive,
        "agent_has_children" => KernelError::AgentHasChildren,
        "capability_missing" => KernelError::CapabilityMissing,
        "not_root" => KernelError::NotRoot,
        "invocation_exists" => KernelError::InvocationExists,
        "invocation_replayed" => KernelError::InvocationReplayed,
        "not_pending" => KernelError::NotPending,
        "egress_not_narrowing" => KernelError::EgressNotNarrowing,
        "egress_not_covering" => KernelError::EgressNotCovering,
        "incoherent_policy" => KernelError::IncoherentPolicy,
        "challenge_already_open" => KernelError::ChallengeAlreadyOpen,
        "clearance_denied" => KernelError::ClearanceDenied,
        "flow_gate_blocked" => KernelError::FlowGateBlocked,
        "authorizer_denied" => KernelError::AuthorizerDenied,
        "integrity_floor_denied" => KernelError::IntegrityFloorDenied,
        "pairwise_conflict" => KernelError::PairwiseConflict,
        "challenge_not_open" => KernelError::ChallengeNotOpen,
        "challenge_scope_mismatch" => KernelError::ChallengeScopeMismatch,
        "attestation_consumed" => KernelError::AttestationConsumed,
        "inspection_negative" => KernelError::InspectionNegative,
        "blocked_pending" => KernelError::BlockedPending,
        "not_quarantined" => KernelError::NotQuarantined,
        "quarantine_resolution_required" => KernelError::QuarantineResolutionRequired,
        "resolution_attestation_invalid" => KernelError::ResolutionAttestationInvalid,
        "ingest_hold_failed" => KernelError::IngestHoldFailed,
        "provenance_not_dominated" => KernelError::ProvenanceNotDominated,
        "crossing_replayed" => KernelError::CrossingReplayed,
        "grant_missing" => KernelError::GrantMissing,
        "grant_exhausted" => KernelError::GrantExhausted,
        "source_in_flight" => KernelError::SourceInFlight,
        "crossing_bound_violated" => KernelError::CrossingBoundViolated,
        "crossing_hold_failed" => KernelError::CrossingHoldFailed,
        "event_store" => KernelError::EventStore,
        _ => panic!("unknown kernel error in corpus: {reason}"),
    }
}
