#[path = "../../../priv/conformance/v4_schema.rs"]
mod schema;

use std::collections::HashMap;
use std::fs;
use std::path::{Path, PathBuf};

use schema::{CAPABILITIES, Corpus, ResultExpectation};

use crate::chain::CanonicalTag;

use crate::*;

fn corpus_path() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../../priv/conformance/v4.json")
}

fn corpus() -> Corpus {
    let input = fs::read_to_string(corpus_path()).expect("shared corpus must be readable");
    Corpus::parse(&input).expect("shared corpus must validate")
}

fn background(value: &schema::Background) -> BackgroundN {
    let allow = &value.allow_ceiling;
    let inspect = &value.inspect_ceiling;
    BackgroundN {
        mode: mode(value.mode),
        allow_ceiling: HashMap::from([
            (
                EgressKindN::NetworkExternal,
                allow.network_external.map(conf),
            ),
            (
                EgressKindN::NetworkInternal,
                allow.network_internal.map(conf),
            ),
            (
                EgressKindN::FilesystemWrite,
                allow.filesystem_write.map(conf),
            ),
            (EgressKindN::Ipc, allow.ipc.map(conf)),
        ]),
        inspect_ceiling: HashMap::from([
            (
                EgressKindN::NetworkExternal,
                inspect.network_external.map(conf),
            ),
            (
                EgressKindN::NetworkInternal,
                inspect.network_internal.map(conf),
            ),
            (
                EgressKindN::FilesystemWrite,
                inspect.filesystem_write.map(conf),
            ),
            (EgressKindN::Ipc, inspect.ipc.map(conf)),
        ]),
    }
}

fn command(value: &schema::Command) -> CommandN {
    use schema::Command as C;
    match value {
        C::RegisterTool { tool } => {
            CommandN::RegisterTool(RegisterToolCommandN { tool: tool.clone() })
        }
        C::UnregisterTool { tool } => {
            CommandN::UnregisterTool(UnregisterToolCommandN { tool: tool.clone() })
        }
        C::Delegate { grantor, grantee } => CommandN::Delegate(DelegateCommandN {
            grantor: grantor.clone(),
            grantee: grantee.clone(),
        }),
        C::GrantCapability {
            parent,
            child,
            cap: value,
        } => CommandN::GrantCapability(GrantCapabilityCommandN {
            parent: parent.clone(),
            child: child.clone(),
            cap: cap(*value),
        }),
        C::GrantCrossing {
            grantor,
            agent,
            assignment,
            n,
        } => CommandN::GrantCrossing(GrantCrossingCommandN {
            grantor: grantor.clone(),
            agent: agent.clone(),
            assignment: assignment.clone(),
            n: *n,
        }),
        C::Revoke { parent, target } => CommandN::Revoke(RevokeCommandN {
            parent: parent.clone(),
            target: target.clone(),
        }),
        C::CascadeRevoke { child, parent } => CommandN::CascadeRevoke(CascadeRevokeCommandN {
            child: child.clone(),
            parent: parent.clone(),
        }),
        C::Ingest {
            agent,
            src,
            pconf,
            pinteg,
        } => CommandN::Ingest(IngestCommandN {
            agent: agent.clone(),
            src: src.clone(),
            pconf: conf(*pconf),
            pinteg: integ(*pinteg),
        }),
        C::BeginInvocation {
            agent,
            inv,
            challenge,
            policy: value,
            egress: values,
            args_hash,
            authorized,
        } => CommandN::BeginInvocation(BeginInvocationCommandN {
            agent: agent.clone(),
            inv: inv.clone(),
            challenge: challenge.clone(),
            policy: policy(value),
            egress: values.iter().copied().map(egress).collect(),
            args_hash: args_hash.clone(),
            authorized: *authorized,
        }),
        C::AuthorizeInspected { inv, attestation } => {
            CommandN::AuthorizeInspected(AuthorizeInspectedCommandN {
                inv: inv.clone(),
                attestation: InspectionAttestationN {
                    id: attestation.id.clone(),
                    inv: attestation.inv.clone(),
                    challenge: attestation.challenge.clone(),
                    args_hash: attestation.args_hash.clone(),
                    policy_digest: attestation.policy_digest.clone(),
                    positive: attestation.positive,
                },
            })
        }
        C::SettleInvocation {
            inv,
            outcome: value,
            resolution,
        } => CommandN::SettleInvocation(SettleInvocationCommandN {
            inv: inv.clone(),
            outcome: outcome(*value),
            resolution: resolution.as_ref().map(|item| ResolutionAttestationN {
                id: item.id.clone(),
                inv: item.inv.clone(),
                outcome: outcome(item.outcome),
            }),
        }),
        C::CrossOutput { input } => CommandN::CrossOutput(CrossOutputCommandN {
            input: CrossInputN {
                src: input.src.clone(),
                rcv: input.rcv.clone(),
                crossing: input.crossing.clone(),
                output_hash: input.output_hash.clone(),
                descriptor: input.descriptor.clone(),
                fallback: fallback(input.fallback),
                t_integ: integ(input.t_integ),
                t_conf: input.t_conf.map(conf),
                assignment: input.assignment.clone(),
                evidence: input.evidence.as_ref().map(|item| ConformanceAttestationN {
                    id: item.id.clone(),
                    output: item.output.clone(),
                    src: item.src.clone(),
                    rcv: item.rcv.clone(),
                    descriptor: item.descriptor.clone(),
                    assignment: item.assignment.clone(),
                    positive: item.positive,
                }),
                released_conf: conf(input.released_conf),
                released_integ: integ(input.released_integ),
            },
        }),
    }
}

fn action(value: &ActionN) -> schema::Action {
    match value {
        ActionN::RegisterTool(v) => schema::Action::RegisterTool {
            tool: v.tool.clone(),
        },
        ActionN::UnregisterTool(v) => schema::Action::UnregisterTool {
            tool: v.tool.clone(),
        },
        ActionN::Delegate(v) => schema::Action::Delegate {
            grantor: v.grantor.clone(),
            grantee: v.grantee.clone(),
        },
        ActionN::GrantCapability(v) => schema::Action::GrantCapability {
            parent: v.parent.clone(),
            child: v.child.clone(),
            cap: cap_s(v.cap),
        },
        ActionN::GrantCrossing(v) => schema::Action::GrantCrossing {
            grantor: v.grantor.clone(),
            agent: v.agent.clone(),
            assignment: v.assignment.clone(),
            n: v.n,
        },
        ActionN::Revoke(v) => schema::Action::Revoke {
            parent: v.parent.clone(),
            target: v.target.clone(),
        },
        ActionN::CascadeRevoke(v) => schema::Action::CascadeRevoke {
            child: v.child.clone(),
            parent: v.parent.clone(),
        },
        ActionN::Ingest(v) => schema::Action::Ingest {
            agent: v.agent.clone(),
            src: v.src.clone(),
            pconf: conf_s(v.pconf),
            pinteg: integ_s(v.pinteg),
            disposition: disposition_s(v.disposition),
        },
        ActionN::BeginInvocation(v) => schema::Action::BeginInvocation {
            agent: v.agent.clone(),
            inv: v.inv.clone(),
            tool: v.tool.clone(),
            verdict: verdict_s(v.verdict),
            authorized: v.authorized,
        },
        ActionN::AuthorizeInspected(v) => schema::Action::AuthorizeInspected {
            inv: v.inv.clone(),
            attestation: v.attestation.clone(),
            admitted: v.admitted,
        },
        ActionN::SettleInvocation(v) => schema::Action::SettleInvocation {
            inv: v.inv.clone(),
            agent: v.agent.clone(),
            disposition: disposition_s(v.disposition),
            outcome: outcome_s(v.outcome),
            clvl: conf_s(v.clvl),
            ilvl: integ_s(v.ilvl),
            resolution: v.resolution.clone(),
        },
        ActionN::CrossOutput(v) => schema::Action::CrossOutput {
            src: v.src.clone(),
            rcv: v.rcv.clone(),
            crossing: v.crossing.clone(),
            branch: branch_s(v.branch),
            disposition: disposition_s(v.disposition),
        },
    }
}

fn state(value: StateN) -> schema::State {
    schema::State {
        agent_active: value.agent_active,
        agent_parent: value.agent_parent,
        agent_cap: value
            .agent_cap
            .into_iter()
            .map(|(key, values)| (key, values.into_iter().map(cap_s).collect()))
            .collect(),
        taint_levels: value
            .taint_levels
            .into_iter()
            .map(|(key, values)| (key, values.into_iter().map(conf_s).collect()))
            .collect(),
        integ_levels: value
            .integ_levels
            .into_iter()
            .map(|(key, values)| (key, values.into_iter().map(integ_s).collect()))
            .collect(),
        pending: value
            .pending
            .into_iter()
            .map(|(key, item)| {
                (
                    key,
                    schema::Pending {
                        agent: item.agent,
                        policy: policy_s(item.policy),
                        egress: item.egress.into_iter().map(egress_s).collect(),
                        admission: admission_s(item.admission),
                        disposition: disposition_s(item.disposition),
                        authorized: item.authorized,
                        quarantined: item.quarantined,
                    },
                )
            })
            .collect(),
        challenges: value
            .challenges
            .into_iter()
            .map(|(key, item)| {
                (
                    key,
                    schema::Challenge {
                        challenge: item.challenge,
                        agent: item.agent,
                        policy: policy_s(item.policy),
                        egress: item.egress.into_iter().map(egress_s).collect(),
                        args_hash: item.args_hash,
                        authorized: item.authorized,
                    },
                )
            })
            .collect(),
        consumed_ids: value.consumed_ids,
        consumed_attestations: value.consumed_attestations,
        consumed_crossings: value.consumed_crossings,
        crossing_grants: value
            .crossing_grants
            .into_iter()
            .map(|(key, grant)| {
                (
                    key,
                    schema::CrossingGrant {
                        remaining: grant.remaining,
                        provisioned: grant.provisioned,
                    },
                )
            })
            .collect(),
        tool_registered: value.tool_registered,
    }
}

fn policy(value: &schema::Policy) -> ActionPolicySnapshotN {
    ActionPolicySnapshotN {
        tool: value.tool.clone(),
        required_caps: value.required_caps.iter().copied().map(cap).collect(),
        conf_clearance: conf(value.conf_clearance),
        integ_floor: integ(value.integ_floor),
        integ_inspect: integ(value.integ_inspect),
        output_conf: conf(value.output_conf),
        output_integ: integ(value.output_integ),
        declared_egress: value.declared_egress.iter().copied().map(egress).collect(),
        policy_digest: value.policy_digest.clone(),
    }
}

fn policy_s(value: ActionPolicySnapshotN) -> schema::Policy {
    schema::Policy {
        tool: value.tool,
        required_caps: value.required_caps.into_iter().map(cap_s).collect(),
        conf_clearance: conf_s(value.conf_clearance),
        integ_floor: integ_s(value.integ_floor),
        integ_inspect: integ_s(value.integ_inspect),
        output_conf: conf_s(value.output_conf),
        output_integ: integ_s(value.output_integ),
        declared_egress: value.declared_egress.into_iter().map(egress_s).collect(),
        policy_digest: value.policy_digest,
    }
}

fn admission_s(value: AdmissionN) -> schema::Admission {
    match value {
        AdmissionN::Plain => schema::Admission {
            kind: schema::AdmissionTag::Plain,
            attestation: None,
        },
        AdmissionN::Inspected(id) => schema::Admission {
            kind: schema::AdmissionTag::Inspected,
            attestation: Some(id),
        },
        AdmissionN::Bypassed => schema::Admission {
            kind: schema::AdmissionTag::Bypassed,
            attestation: None,
        },
    }
}

fn status(value: ChainN) -> schema::Chain {
    schema::Chain {
        version: value.version,
        sequence: value.sequence,
        head: hex(value.head.as_bytes()),
    }
}

fn digest(value: &str) -> DigestN {
    let bytes = (0..value.len())
        .step_by(2)
        .map(|index| u8::from_str_radix(&value[index..index + 2], 16).expect("validated hex"))
        .collect::<Vec<_>>();
    DigestN::new(bytes.try_into().expect("validated digest length"))
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn mode(value: schema::Mode) -> ModeN {
    match value {
        schema::Mode::Enforce => ModeN::Enforce,
        schema::Mode::Monitor => ModeN::Monitor,
    }
}
fn conf(value: schema::Conf) -> ConfLevelN {
    match value {
        schema::Conf::Public => ConfLevelN::Public,
        schema::Conf::Internal => ConfLevelN::Internal,
        schema::Conf::Sensitive => ConfLevelN::Sensitive,
        schema::Conf::Restricted => ConfLevelN::Restricted,
    }
}
fn conf_s(value: ConfLevelN) -> schema::Conf {
    match value {
        ConfLevelN::Public => schema::Conf::Public,
        ConfLevelN::Internal => schema::Conf::Internal,
        ConfLevelN::Sensitive => schema::Conf::Sensitive,
        ConfLevelN::Restricted => schema::Conf::Restricted,
    }
}
fn integ(value: schema::Integ) -> IntegLevelN {
    match value {
        schema::Integ::Untrusted => IntegLevelN::Untrusted,
        schema::Integ::Standard => IntegLevelN::Standard,
        schema::Integ::Trusted => IntegLevelN::Trusted,
        schema::Integ::Attested => IntegLevelN::Attested,
    }
}
fn integ_s(value: IntegLevelN) -> schema::Integ {
    match value {
        IntegLevelN::Untrusted => schema::Integ::Untrusted,
        IntegLevelN::Standard => schema::Integ::Standard,
        IntegLevelN::Trusted => schema::Integ::Trusted,
        IntegLevelN::Attested => schema::Integ::Attested,
    }
}
fn egress(value: schema::Egress) -> EgressKindN {
    match value {
        schema::Egress::NetworkExternal => EgressKindN::NetworkExternal,
        schema::Egress::NetworkInternal => EgressKindN::NetworkInternal,
        schema::Egress::FilesystemWrite => EgressKindN::FilesystemWrite,
        schema::Egress::Ipc => EgressKindN::Ipc,
    }
}
fn egress_s(value: EgressKindN) -> schema::Egress {
    match value {
        EgressKindN::NetworkExternal => schema::Egress::NetworkExternal,
        EgressKindN::NetworkInternal => schema::Egress::NetworkInternal,
        EgressKindN::FilesystemWrite => schema::Egress::FilesystemWrite,
        EgressKindN::Ipc => schema::Egress::Ipc,
    }
}
fn outcome(value: schema::Outcome) -> OutcomeN {
    match value {
        schema::Outcome::Success => OutcomeN::Success,
        schema::Outcome::Failure => OutcomeN::Failure,
        schema::Outcome::Ambiguous => OutcomeN::Ambiguous,
    }
}
fn outcome_s(value: OutcomeN) -> schema::Outcome {
    match value {
        OutcomeN::Success => schema::Outcome::Success,
        OutcomeN::Failure => schema::Outcome::Failure,
        OutcomeN::Ambiguous => schema::Outcome::Ambiguous,
    }
}
fn fallback(value: schema::Fallback) -> FallbackN {
    match value {
        schema::Fallback::Fail => FallbackN::Fail,
        schema::Fallback::ReleaseUnendorsed => FallbackN::ReleaseUnendorsed,
    }
}
fn disposition_s(value: DispositionN) -> schema::Disposition {
    match value {
        DispositionN::Permitted => schema::Disposition::Permitted,
        DispositionN::Blocked => schema::Disposition::Blocked,
        DispositionN::MonitorBypassed => schema::Disposition::MonitorBypassed,
    }
}
fn verdict_s(value: VerdictN) -> schema::Verdict {
    match value {
        VerdictN::Allow => schema::Verdict::Allow,
        VerdictN::InspectionRequired => schema::Verdict::InspectionRequired,
        VerdictN::Deny => schema::Verdict::Deny,
    }
}
fn branch_s(value: CrossBranchN) -> schema::CrossBranch {
    match value {
        CrossBranchN::Endorsed => schema::CrossBranch::Endorsed,
        CrossBranchN::Unendorsed => schema::CrossBranch::Unendorsed,
        CrossBranchN::Fail => schema::CrossBranch::Fail,
    }
}
fn cap(value: schema::Capability) -> CapKindN {
    CapKindN::from_kernel(
        argus_kernel::CapKind::ALL[CAPABILITIES
            .iter()
            .position(|item| *item == value)
            .expect("closed capability")],
    )
}
fn cap_s(value: CapKindN) -> schema::Capability {
    CAPABILITIES[CanonicalTag::canonical_tag(&value) as usize]
}

#[test]
fn native_executes_every_semantic_case_with_exact_atomic_checkpoints() {
    for case in corpus().semantic_cases {
        let semantic_background = background(&case.background);
        let live = LiveInstance::new(semantic_background.clone());
        assert_eq!(
            status(live.status().expect("initial status")),
            case.initial_chain,
            "{} initial chain",
            case.id
        );

        let mut accepted = Vec::new();
        for step in case.steps {
            let before_state = live.state().expect("state before");
            let before_status = live.status().expect("status before");
            let native_command = command(&step.command);
            match step.expected.result {
                ResultExpectation::Accepted {
                    action: expected_action,
                } => {
                    let envelope = live
                        .apply(native_command.clone())
                        .expect("expected accepted command");
                    assert_eq!(
                        action(&envelope.action),
                        expected_action,
                        "{}:{} action",
                        case.id,
                        step.id
                    );
                    assert_eq!(
                        envelope.previous_digest, before_status.head,
                        "{}:{} predecessor",
                        case.id, step.id
                    );
                    assert_eq!(
                        envelope.sequence,
                        before_status.sequence + 1,
                        "{}:{} sequence",
                        case.id,
                        step.id
                    );
                    assert_eq!(
                        envelope.digest,
                        link(
                            envelope.previous_digest,
                            envelope.sequence,
                            &native_command,
                            &envelope.action
                        ),
                        "{}:{} digest",
                        case.id,
                        step.id
                    );
                    if let Some(expected_hex) = step.expected.transcript_hex {
                        assert_eq!(
                            hex(&link_transcript(
                                envelope.previous_digest,
                                envelope.sequence,
                                &native_command,
                                &envelope.action
                            )),
                            expected_hex,
                            "{}:{} transcript",
                            case.id,
                            step.id
                        );
                    }
                    accepted.push(envelope);
                }
                ResultExpectation::Error { reason, .. } => {
                    let error = live.apply(native_command).expect_err("expected refusal");
                    assert_eq!(
                        native_error_name(&error),
                        reason,
                        "{}:{} error",
                        case.id,
                        step.id
                    );
                    assert_eq!(
                        live.state().expect("state after refusal"),
                        before_state,
                        "{}:{} refusal state",
                        case.id,
                        step.id
                    );
                    assert_eq!(
                        live.status().expect("status after refusal"),
                        before_status,
                        "{}:{} refusal status",
                        case.id,
                        step.id
                    );
                }
            }
            assert_eq!(
                state(live.state().expect("checkpoint state")),
                step.expected.state,
                "{}:{} state",
                case.id,
                step.id
            );
            assert_eq!(
                status(live.status().expect("checkpoint status")),
                step.expected.chain,
                "{}:{} status",
                case.id,
                step.id
            );
        }

        for length in 0..=accepted.len() {
            let recovery = RecoveryInstance::new(semantic_background.clone());
            for envelope in accepted.iter().take(length).cloned() {
                recovery.replay(envelope).expect("accepted prefix replay");
            }
            let expected = if length == 0 {
                case.initial_chain.clone()
            } else {
                let envelope = &accepted[length - 1];
                schema::Chain {
                    version: VERSION,
                    sequence: envelope.sequence,
                    head: hex(envelope.digest.as_bytes()),
                }
            };
            let recovered = recovery
                .finalize(ChainN {
                    version: expected.version,
                    sequence: expected.sequence,
                    head: digest(&expected.head),
                })
                .expect("accepted prefix finalize");
            assert_eq!(
                status(recovered.status().expect("recovered status")),
                expected,
                "{} prefix {length}",
                case.id
            );
        }
    }
}

#[test]
fn native_parser_and_capacity_boundaries_are_strict() {
    let input = fs::read_to_string(corpus_path()).expect("corpus");
    let parsed = corpus();
    let first_id = &parsed.semantic_cases[0].id;
    let second_id = &parsed.semantic_cases[1].id;
    for malformed in [
        input.replacen("\"schema\":", "\"extra\":0,\"schema\":", 1),
        input.replacen("\"version\": 5,", "", 1),
        input.replacen("\"version\": 5,", "\"version\": 5,\"version\": 5,", 1),
        input.replacen("\"mode\": \"enforce\"", "\"mode\": \"unknown\"", 1),
        input.replacen(
            "\"required_caps\": []",
            "\"required_caps\": [\"ipc\",\"ipc\"]",
            1,
        ),
        input.replacen("\"head\": \"", "\"head\": \"GG", 1),
        input.replacen("\"sequence\": 1", "\"sequence\": 3", 1),
        input.replacen(
            &format!("\"id\": \"{second_id}\""),
            &format!("\"id\": \"{first_id}\""),
            1,
        ),
        format!("{input} false"),
    ] {
        assert!(Corpus::parse(&malformed).is_err());
    }

    let boundary = parsed.boundary_cases;
    assert_eq!(boundary.len(), 14);
    let live = LiveInstance::new(background(&corpus().semantic_cases[0].background));
    let oversized = CommandN::RegisterTool(RegisterToolCommandN {
        tool: "x".repeat(limits::MAX_OPAQUE_UTF8_BYTES + 1),
    });
    assert_eq!(live.apply(oversized), Err(ErrorN::CapacityExceeded));
}

#[test]
fn native_goldens_pin_canonical_transcripts_and_digests() {
    for golden in corpus().goldens {
        match golden.kind {
            schema::GoldenKind::Genesis => {
                let value = background(golden.background.as_ref().expect("genesis background"));
                assert_eq!(hex(&genesis_transcript(&value)), golden.transcript_hex);
                assert_eq!(hex(genesis(&value).as_bytes()), golden.digest);
            }
            schema::GoldenKind::Link => {
                let case = corpus()
                    .semantic_cases
                    .into_iter()
                    .find(|item| Some(&item.id) == golden.case_id.as_ref())
                    .expect("golden case");
                let live = LiveInstance::new(background(&case.background));
                for step in case.steps {
                    let envelope = live.apply(command(&step.command)).ok();
                    if Some(&step.id) == golden.step_id.as_ref() {
                        let envelope = envelope.expect("link golden must be accepted");
                        assert_eq!(
                            hex(&link_transcript(
                                envelope.previous_digest,
                                envelope.sequence,
                                &envelope.command,
                                &envelope.action
                            )),
                            golden.transcript_hex
                        );
                        assert_eq!(hex(envelope.digest.as_bytes()), golden.digest);
                        break;
                    }
                }
            }
        }
    }
}

fn native_error_name(error: &ErrorN) -> String {
    match error {
        ErrorN::Kernel(cause) => kernel_error_name(*cause).to_owned(),
        ErrorN::InstanceBusy => "instance_busy".to_owned(),
        ErrorN::ResourcePoisoned => "resource_poisoned".to_owned(),
        ErrorN::CapacityExceeded => "capacity_exceeded".to_owned(),
        ErrorN::SequenceExhausted => "sequence_exhausted".to_owned(),
        ErrorN::InvalidVersion => "invalid_version".to_owned(),
        ErrorN::SequenceMismatch => "sequence_mismatch".to_owned(),
        ErrorN::PreviousDigestMismatch => "previous_digest_mismatch".to_owned(),
        ErrorN::ActionMismatch => "action_mismatch".to_owned(),
        ErrorN::DigestMismatch => "digest_mismatch".to_owned(),
        ErrorN::ReplayRefused(cause) => format!("replay_refused:{}", kernel_error_name(*cause)),
        ErrorN::RecoveryConsumed => "recovery_consumed".to_owned(),
        ErrorN::FinalAnchorMismatch => "final_anchor_mismatch".to_owned(),
    }
}

fn kernel_error_name(error: KernelErrorN) -> &'static str {
    use KernelErrorN::*;
    match error {
        ToolAlreadyRegistered => "tool_already_registered",
        ToolNotRegistered => "tool_not_registered",
        ToolInUse => "tool_in_use",
        AgentInactive => "agent_inactive",
        AgentAlreadyActive => "agent_already_active",
        RootNotAllowed => "root_not_allowed",
        NotDirectChild => "not_direct_child",
        ParentStillActive => "parent_still_active",
        AgentHasChildren => "agent_has_children",
        CapabilityMissing => "capability_missing",
        NotRoot => "not_root",
        InvocationExists => "invocation_exists",
        InvocationReplayed => "invocation_replayed",
        NotPending => "not_pending",
        EgressNotNarrowing => "egress_not_narrowing",
        EgressNotCovering => "egress_not_covering",
        IncoherentPolicy => "incoherent_policy",
        ChallengeAlreadyOpen => "challenge_already_open",
        ClearanceDenied => "clearance_denied",
        FlowGateBlocked => "flow_gate_blocked",
        AuthorizerDenied => "authorizer_denied",
        IntegrityFloorDenied => "integrity_floor_denied",
        PairwiseConflict => "pairwise_conflict",
        ChallengeNotOpen => "challenge_not_open",
        ChallengeScopeMismatch => "challenge_scope_mismatch",
        AttestationConsumed => "attestation_consumed",
        InspectionNegative => "inspection_negative",
        BlockedPending => "blocked_pending",
        NotQuarantined => "not_quarantined",
        QuarantineResolutionRequired => "quarantine_resolution_required",
        ResolutionAttestationInvalid => "resolution_attestation_invalid",
        IngestHoldFailed => "ingest_hold_failed",
        ProvenanceNotDominated => "provenance_not_dominated",
        CrossingReplayed => "crossing_replayed",
        GrantMissing => "grant_missing",
        GrantExhausted => "grant_exhausted",
        SourceInFlight => "source_in_flight",
        CrossingBoundViolated => "crossing_bound_violated",
        CrossingHoldFailed => "crossing_hold_failed",
        EventStore => "event_store",
    }
}

#[test]
fn native_recovery_vectors_fail_atomically_and_resources_remain_isolated() {
    let corpus = corpus();
    let source = corpus
        .semantic_cases
        .iter()
        .find(|case| case.id == "structural_lifecycle")
        .expect("source case");
    let semantic_background = background(&source.background);
    let live = LiveInstance::new(semantic_background.clone());
    let history: Vec<_> = source
        .steps
        .iter()
        .map(|step| live.apply(command(&step.command)).expect("source accepts"))
        .collect();
    let anchor = live.status().expect("anchor");

    for vector in &corpus.recovery_cases {
        match vector.mutation {
            schema::RecoveryMutation::StaleAnchor => {
                let recovery = RecoveryInstance::new(semantic_background.clone());
                for envelope in history.iter().cloned() {
                    recovery.replay(envelope).expect("prefix");
                }
                let mut stale = anchor.clone();
                stale.sequence -= 1;
                assert_eq!(
                    recovery.finalize(stale).err(),
                    Some(ErrorN::FinalAnchorMismatch)
                );
                assert!(recovery.finalize(anchor.clone()).is_ok());
            }
            schema::RecoveryMutation::TruncatedAnchor => {
                let recovery = RecoveryInstance::new(semantic_background.clone());
                recovery.replay(history[0].clone()).expect("first link");
                assert_eq!(
                    recovery.finalize(anchor.clone()).err(),
                    Some(ErrorN::FinalAnchorMismatch)
                );
            }
            schema::RecoveryMutation::WrongBackground => {
                let mut wrong = source.background.clone();
                wrong.mode = schema::Mode::Monitor;
                let native_wrong = background(&wrong);
                let recovery = RecoveryInstance::new(native_wrong.clone());
                assert_eq!(
                    recovery.replay(history[0].clone()),
                    Err(ErrorN::PreviousDigestMismatch)
                );
                assert!(
                    recovery
                        .finalize(ChainN {
                            version: VERSION,
                            sequence: 0,
                            head: genesis(&native_wrong)
                        })
                        .is_ok()
                );
            }
            mutation => {
                let (prefix, malformed, expected) = malformed_recovery_link(mutation, &history);
                let recovery = RecoveryInstance::new(semantic_background.clone());
                for envelope in history.iter().take(prefix).cloned() {
                    recovery.replay(envelope).expect("valid prefix");
                }
                assert_eq!(recovery.replay(malformed), Err(expected), "{}", vector.id);
                recovery
                    .replay(history[prefix].clone())
                    .expect("failed link must not commit");
            }
        }
    }

    assert_ne!(
        std::any::TypeId::of::<LiveInstance>(),
        std::any::TypeId::of::<RecoveryInstance>()
    );
    let recovery = RecoveryInstance::new(semantic_background);
    let genesis_anchor = ChainN {
        version: VERSION,
        sequence: 0,
        head: digest(&source.initial_chain.head),
    };
    assert!(recovery.finalize(genesis_anchor.clone()).is_ok());
    assert_eq!(
        recovery.finalize(genesis_anchor).err(),
        Some(ErrorN::RecoveryConsumed)
    );
}

fn malformed_recovery_link(
    mutation: schema::RecoveryMutation,
    history: &[EnvelopeN],
) -> (usize, EnvelopeN, ErrorN) {
    match mutation {
        schema::RecoveryMutation::Edit => {
            let mut value = history[2].clone();
            value.command = CommandN::RegisterTool(RegisterToolCommandN {
                tool: "tool".to_owned(),
            });
            (
                2,
                value,
                ErrorN::ReplayRefused(KernelErrorN::ToolAlreadyRegistered),
            )
        }
        schema::RecoveryMutation::Insertion => (2, history[1].clone(), ErrorN::SequenceMismatch),
        schema::RecoveryMutation::Deletion => (1, history[2].clone(), ErrorN::SequenceMismatch),
        schema::RecoveryMutation::Reorder => (0, history[1].clone(), ErrorN::SequenceMismatch),
        schema::RecoveryMutation::Duplicate => (1, history[0].clone(), ErrorN::SequenceMismatch),
        schema::RecoveryMutation::Gap => {
            let mut value = history[1].clone();
            value.sequence = 3;
            (1, value, ErrorN::SequenceMismatch)
        }
        schema::RecoveryMutation::WrongAction => {
            let mut value = history[0].clone();
            value.action = ActionN::RegisterTool(RegisterToolActionN {
                tool: "edited".to_owned(),
            });
            (0, value, ErrorN::ActionMismatch)
        }
        schema::RecoveryMutation::WrongDigest => {
            let mut value = history[2].clone();
            value.digest = DigestN::new([0; 32]);
            (2, value, ErrorN::DigestMismatch)
        }
        schema::RecoveryMutation::ReplayRefusal => {
            let mut value = history[1].clone();
            value.command = CommandN::RegisterTool(RegisterToolCommandN {
                tool: "tool".to_owned(),
            });
            (
                1,
                value,
                ErrorN::ReplayRefused(KernelErrorN::ToolAlreadyRegistered),
            )
        }
        schema::RecoveryMutation::WrongBackground
        | schema::RecoveryMutation::StaleAnchor
        | schema::RecoveryMutation::TruncatedAnchor => unreachable!("handled separately"),
    }
}
