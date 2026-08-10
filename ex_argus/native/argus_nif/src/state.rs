use argus_kernel::{ActionPolicySnapshot, ChallengeScope, KernelState, PendingInvocation};
use rustler::NifStruct;

use crate::{
    ActionPolicySnapshotN, AdmissionN, CapKindN, ConfLevelN, DispositionN, EgressKindN,
    IntegLevelN, chain::CanonicalTag,
};

#[derive(Debug, Clone, PartialEq, Eq, NifStruct)]
#[module = "ExArgus.Kernel.Types.PendingInvocation"]
#[rustler(encode)]
pub struct PendingInvocationN {
    pub agent: String,
    pub policy: ActionPolicySnapshotN,
    pub egress: Vec<EgressKindN>,
    pub admission: AdmissionN,
    pub disposition: DispositionN,
    pub authorized: bool,
    pub quarantined: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, NifStruct)]
#[module = "ExArgus.Kernel.Types.ChallengeScope"]
#[rustler(encode)]
pub struct ChallengeScopeN {
    pub challenge: String,
    pub agent: String,
    pub policy: ActionPolicySnapshotN,
    pub egress: Vec<EgressKindN>,
    pub args_hash: String,
    pub authorized: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, NifStruct)]
#[module = "ExArgus.Kernel.Types.CrossingGrant"]
#[rustler(encode)]
pub struct CrossingGrantN {
    pub remaining: u32,
    pub provisioned: u32,
}

/// Encoder-only observation; it cannot be used to reconstruct kernel state.
///
/// ```compile_fail
/// fn requires_decoder<T: for<'a> rustler::Decoder<'a>>() {}
/// requires_decoder::<argus_nif::StateN>();
/// ```
#[derive(Debug, Clone, PartialEq, Eq, NifStruct)]
#[module = "ExArgus.Kernel.State"]
#[rustler(encode)]
pub struct StateN {
    pub agent_active: Vec<String>,
    pub agent_parent: Vec<(String, String)>,
    pub agent_cap: Vec<(String, Vec<CapKindN>)>,
    pub taint_levels: Vec<(String, Vec<ConfLevelN>)>,
    pub integ_levels: Vec<(String, Vec<IntegLevelN>)>,
    pub pending: Vec<(String, PendingInvocationN)>,
    pub challenges: Vec<(String, ChallengeScopeN)>,
    pub consumed_ids: Vec<String>,
    pub consumed_attestations: Vec<String>,
    pub consumed_crossings: Vec<String>,
    pub crossing_grants: Vec<((String, String), CrossingGrantN)>,
    pub tool_registered: Vec<String>,
}

impl StateN {
    pub fn from_kernel(state: &KernelState) -> Self {
        let mut agent_active: Vec<_> = state
            .agent_active
            .iter()
            .map(|agent| agent.0.clone())
            .collect();
        sort_strings(&mut agent_active);

        let mut agent_parent: Vec<_> = state
            .agent_parent
            .iter()
            .map(|(child, parent)| (child.0.clone(), parent.0.clone()))
            .collect();
        sort_string_map(&mut agent_parent);

        let mut agent_cap: Vec<_> = state
            .agent_cap
            .iter()
            .map(|(agent, caps)| {
                let mut caps: Vec<_> = caps.iter().copied().map(CapKindN::from_kernel).collect();
                caps.sort_by_key(|cap| cap.canonical_tag());
                (agent.0.clone(), caps)
            })
            .collect();
        sort_string_map(&mut agent_cap);

        let mut taint_levels: Vec<_> = state
            .taint_levels
            .iter()
            .map(|(agent, levels)| {
                let mut levels: Vec<_> = levels
                    .iter()
                    .copied()
                    .map(ConfLevelN::from_kernel)
                    .collect();
                levels.sort_by_key(|level| level.canonical_tag());
                (agent.0.clone(), levels)
            })
            .collect();
        sort_string_map(&mut taint_levels);

        let mut integ_levels: Vec<_> = state
            .integ_levels
            .iter()
            .map(|(agent, levels)| {
                let mut levels: Vec<_> = levels
                    .iter()
                    .copied()
                    .map(IntegLevelN::from_kernel)
                    .collect();
                levels.sort_by_key(|level| level.canonical_tag());
                (agent.0.clone(), levels)
            })
            .collect();
        sort_string_map(&mut integ_levels);

        let mut pending: Vec<_> = state
            .pending
            .iter()
            .map(|(invocation, value)| (invocation.0.clone(), pending_from_kernel(value)))
            .collect();
        sort_string_map(&mut pending);

        let mut challenges: Vec<_> = state
            .challenges
            .iter()
            .map(|(invocation, value)| (invocation.0.clone(), challenge_from_kernel(value)))
            .collect();
        sort_string_map(&mut challenges);

        let mut consumed_ids: Vec<_> = state
            .consumed_ids
            .iter()
            .map(|invocation| invocation.0.clone())
            .collect();
        sort_strings(&mut consumed_ids);

        let mut consumed_attestations: Vec<_> = state
            .consumed_attestations
            .iter()
            .map(|attestation| attestation.0.clone())
            .collect();
        sort_strings(&mut consumed_attestations);

        let mut consumed_crossings: Vec<_> = state
            .consumed_crossings
            .iter()
            .map(|crossing| crossing.0.clone())
            .collect();
        sort_strings(&mut consumed_crossings);

        let mut crossing_grants: Vec<_> = state
            .crossing_grants
            .iter()
            .map(|(key, grant)| {
                (
                    (key.agent.0.clone(), key.assignment.0.clone()),
                    CrossingGrantN {
                        remaining: grant.remaining,
                        provisioned: grant.provisioned,
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
            .map(|tool| tool.0.clone())
            .collect();
        sort_strings(&mut tool_registered);

        Self {
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
}

fn policy_from_kernel(policy: &ActionPolicySnapshot) -> ActionPolicySnapshotN {
    let mut required_caps: Vec<_> = policy
        .required_caps
        .iter()
        .copied()
        .map(CapKindN::from_kernel)
        .collect();
    required_caps.sort_by_key(|cap| cap.canonical_tag());
    let mut declared_egress: Vec<_> = policy
        .declared_egress
        .iter()
        .copied()
        .map(EgressKindN::from_kernel)
        .collect();
    declared_egress.sort_by_key(|egress| egress.canonical_tag());
    ActionPolicySnapshotN {
        tool: policy.tool.0.clone(),
        required_caps,
        conf_clearance: ConfLevelN::from_kernel(policy.conf_clearance),
        integ_floor: IntegLevelN::from_kernel(policy.integ_floor),
        integ_inspect: IntegLevelN::from_kernel(policy.integ_inspect),
        output_conf: ConfLevelN::from_kernel(policy.output_conf),
        output_integ: IntegLevelN::from_kernel(policy.output_integ),
        declared_egress,
        policy_digest: policy.policy_digest.0.clone(),
    }
}

fn pending_from_kernel(pending: &PendingInvocation) -> PendingInvocationN {
    let mut egress: Vec<_> = pending
        .egress
        .iter()
        .copied()
        .map(EgressKindN::from_kernel)
        .collect();
    egress.sort_by_key(|kind| kind.canonical_tag());
    PendingInvocationN {
        agent: pending.agent.0.clone(),
        policy: policy_from_kernel(&pending.policy),
        egress,
        admission: AdmissionN::from_kernel(pending.admission.clone()),
        disposition: DispositionN::from_kernel(pending.disposition),
        authorized: pending.authorized,
        quarantined: pending.quarantined,
    }
}

fn challenge_from_kernel(challenge: &ChallengeScope) -> ChallengeScopeN {
    let mut egress: Vec<_> = challenge
        .egress
        .iter()
        .copied()
        .map(EgressKindN::from_kernel)
        .collect();
    egress.sort_by_key(|kind| kind.canonical_tag());
    ChallengeScopeN {
        challenge: challenge.challenge.0.clone(),
        agent: challenge.agent.0.clone(),
        policy: policy_from_kernel(&challenge.policy),
        egress,
        args_hash: challenge.args_hash.0.clone(),
        authorized: challenge.authorized,
    }
}

fn sort_strings(values: &mut [String]) {
    values.sort_by(|left, right| left.as_bytes().cmp(right.as_bytes()));
}

fn sort_string_map<T>(values: &mut [(String, T)]) {
    values.sort_by(|left, right| left.0.as_bytes().cmp(right.0.as_bytes()));
}

#[cfg(test)]
mod tests {
    use argus_kernel::{
        ActionPolicySnapshot, Admission, AgentId, AssignmentDigest, AttestationId, CapKind,
        ChallengeId, ChallengeScope, ConfLevel, ContentHash, CrossingGrant, CrossingId,
        CrossingKey, Disposition, EgressKind, IntegLevel, InvocationId, KernelState,
        PendingInvocation, PolicyDigest, ToolId, VecSet,
    };

    use crate::{
        ActionPolicySnapshotN, AdmissionN, CapKindN, ConfLevelN, DispositionN, EgressKindN,
        IntegLevelN,
    };

    use super::{ChallengeScopeN, CrossingGrantN, PendingInvocationN, StateN};

    fn policy(reverse: bool, suffix: &str) -> ActionPolicySnapshot {
        let required_caps = if reverse {
            VecSet::from([CapKind::Ipc, CapKind::FilesystemRead])
        } else {
            VecSet::from([CapKind::FilesystemRead, CapKind::Ipc])
        };
        let declared_egress = if reverse {
            VecSet::from([EgressKind::Ipc, EgressKind::NetworkExternal])
        } else {
            VecSet::from([EgressKind::NetworkExternal, EgressKind::Ipc])
        };
        ActionPolicySnapshot {
            tool: ToolId::new(&format!("tool-{suffix}")),
            required_caps,
            conf_clearance: ConfLevel::Sensitive,
            integ_floor: IntegLevel::Standard,
            integ_inspect: IntegLevel::Untrusted,
            output_conf: ConfLevel::Internal,
            output_integ: IntegLevel::Trusted,
            declared_egress,
            policy_digest: PolicyDigest::new(&format!("policy-{suffix}")),
        }
    }

    fn pending(reverse: bool, suffix: &str) -> PendingInvocation {
        let egress = if reverse {
            VecSet::from([EgressKind::Ipc, EgressKind::NetworkInternal])
        } else {
            VecSet::from([EgressKind::NetworkInternal, EgressKind::Ipc])
        };
        PendingInvocation {
            agent: AgentId::new(&format!("agent-{suffix}")),
            policy: policy(reverse, suffix),
            egress,
            admission: Admission::Inspected(AttestationId::new(&format!("attestation-{suffix}"))),
            disposition: Disposition::MonitorBypassed,
            authorized: false,
            quarantined: true,
        }
    }

    fn challenge(reverse: bool, suffix: &str) -> ChallengeScope {
        let egress = if reverse {
            VecSet::from([EgressKind::Ipc, EgressKind::FilesystemWrite])
        } else {
            VecSet::from([EgressKind::FilesystemWrite, EgressKind::Ipc])
        };
        ChallengeScope {
            challenge: ChallengeId::new(&format!("challenge-{suffix}")),
            agent: AgentId::new(&format!("agent-{suffix}")),
            policy: policy(reverse, suffix),
            egress,
            args_hash: ContentHash::new(&format!("args-{suffix}")),
            authorized: true,
        }
    }

    fn state(reverse: bool) -> KernelState {
        let order = if reverse { ["z", "a"] } else { ["a", "z"] };
        let mut state = KernelState::initial();
        state.agent_active = order.into_iter().map(AgentId::new).collect();
        state.agent_parent = order
            .into_iter()
            .map(|id| (AgentId::new(id), AgentId::new(&format!("parent-{id}"))))
            .collect();
        state.agent_cap = order
            .into_iter()
            .map(|id| {
                let values = if reverse {
                    VecSet::from([CapKind::Ipc, CapKind::FilesystemRead])
                } else {
                    VecSet::from([CapKind::FilesystemRead, CapKind::Ipc])
                };
                (AgentId::new(id), values)
            })
            .collect();
        state.taint_levels = order
            .into_iter()
            .map(|id| {
                let values = if reverse {
                    VecSet::from([ConfLevel::Restricted, ConfLevel::Public])
                } else {
                    VecSet::from([ConfLevel::Public, ConfLevel::Restricted])
                };
                (AgentId::new(id), values)
            })
            .collect();
        state.integ_levels = order
            .into_iter()
            .map(|id| {
                let values = if reverse {
                    VecSet::from([IntegLevel::Attested, IntegLevel::Untrusted])
                } else {
                    VecSet::from([IntegLevel::Untrusted, IntegLevel::Attested])
                };
                (AgentId::new(id), values)
            })
            .collect();
        state.pending = order
            .into_iter()
            .map(|id| (InvocationId::new(id), pending(reverse, id)))
            .collect();
        state.challenges = order
            .into_iter()
            .map(|id| (InvocationId::new(id), challenge(reverse, id)))
            .collect();
        state.consumed_ids = order.into_iter().map(InvocationId::new).collect();
        state.consumed_attestations = order.into_iter().map(AttestationId::new).collect();
        state.consumed_crossings = order.into_iter().map(CrossingId::new).collect();
        state.crossing_grants = order
            .into_iter()
            .map(|id| {
                (
                    CrossingKey {
                        agent: AgentId::new(id),
                        assignment: AssignmentDigest::new(&format!("assignment-{id}")),
                    },
                    CrossingGrant {
                        remaining: if id == "a" { 1 } else { 2 },
                        provisioned: if id == "a" { 3 } else { 4 },
                    },
                )
            })
            .collect();
        state.tool_registered = order
            .into_iter()
            .map(|id| ToolId::new(&format!("tool-{id}")))
            .collect();
        state
    }

    #[test]
    fn projection_is_equal_for_every_collection_family_across_insertion_orders() {
        assert_eq!(
            StateN::from_kernel(&state(false)),
            StateN::from_kernel(&state(true))
        );
    }

    #[test]
    fn projection_preserves_all_fields_and_nested_semantics() {
        let projection = StateN::from_kernel(&state(false));
        let expected_policy = ActionPolicySnapshotN {
            tool: "tool-a".to_owned(),
            required_caps: vec![CapKindN::FilesystemRead, CapKindN::Ipc],
            conf_clearance: ConfLevelN::Sensitive,
            integ_floor: IntegLevelN::Standard,
            integ_inspect: IntegLevelN::Untrusted,
            output_conf: ConfLevelN::Internal,
            output_integ: IntegLevelN::Trusted,
            declared_egress: vec![EgressKindN::NetworkExternal, EgressKindN::Ipc],
            policy_digest: "policy-a".to_owned(),
        };

        assert_eq!(
            projection,
            StateN {
                agent_active: vec!["a".to_owned(), "z".to_owned()],
                agent_parent: vec![
                    ("a".to_owned(), "parent-a".to_owned()),
                    ("z".to_owned(), "parent-z".to_owned()),
                ],
                agent_cap: vec![
                    (
                        "a".to_owned(),
                        vec![CapKindN::FilesystemRead, CapKindN::Ipc],
                    ),
                    (
                        "z".to_owned(),
                        vec![CapKindN::FilesystemRead, CapKindN::Ipc],
                    ),
                ],
                taint_levels: vec![
                    (
                        "a".to_owned(),
                        vec![ConfLevelN::Public, ConfLevelN::Restricted],
                    ),
                    (
                        "z".to_owned(),
                        vec![ConfLevelN::Public, ConfLevelN::Restricted],
                    ),
                ],
                integ_levels: vec![
                    (
                        "a".to_owned(),
                        vec![IntegLevelN::Untrusted, IntegLevelN::Attested],
                    ),
                    (
                        "z".to_owned(),
                        vec![IntegLevelN::Untrusted, IntegLevelN::Attested],
                    ),
                ],
                pending: vec![
                    (
                        "a".to_owned(),
                        PendingInvocationN {
                            agent: "agent-a".to_owned(),
                            policy: expected_policy.clone(),
                            egress: vec![EgressKindN::NetworkInternal, EgressKindN::Ipc],
                            admission: AdmissionN::Inspected("attestation-a".to_owned()),
                            disposition: DispositionN::MonitorBypassed,
                            authorized: false,
                            quarantined: true,
                        },
                    ),
                    (
                        "z".to_owned(),
                        PendingInvocationN {
                            agent: "agent-z".to_owned(),
                            policy: ActionPolicySnapshotN {
                                tool: "tool-z".to_owned(),
                                policy_digest: "policy-z".to_owned(),
                                ..expected_policy.clone()
                            },
                            egress: vec![EgressKindN::NetworkInternal, EgressKindN::Ipc],
                            admission: AdmissionN::Inspected("attestation-z".to_owned()),
                            disposition: DispositionN::MonitorBypassed,
                            authorized: false,
                            quarantined: true,
                        },
                    ),
                ],
                challenges: vec![
                    (
                        "a".to_owned(),
                        ChallengeScopeN {
                            challenge: "challenge-a".to_owned(),
                            agent: "agent-a".to_owned(),
                            policy: expected_policy.clone(),
                            egress: vec![EgressKindN::FilesystemWrite, EgressKindN::Ipc],
                            args_hash: "args-a".to_owned(),
                            authorized: true,
                        },
                    ),
                    (
                        "z".to_owned(),
                        ChallengeScopeN {
                            challenge: "challenge-z".to_owned(),
                            agent: "agent-z".to_owned(),
                            policy: ActionPolicySnapshotN {
                                tool: "tool-z".to_owned(),
                                policy_digest: "policy-z".to_owned(),
                                ..expected_policy
                            },
                            egress: vec![EgressKindN::FilesystemWrite, EgressKindN::Ipc],
                            args_hash: "args-z".to_owned(),
                            authorized: true,
                        },
                    ),
                ],
                consumed_ids: vec!["a".to_owned(), "z".to_owned()],
                consumed_attestations: vec!["a".to_owned(), "z".to_owned()],
                consumed_crossings: vec!["a".to_owned(), "z".to_owned()],
                crossing_grants: vec![
                    (
                        ("a".to_owned(), "assignment-a".to_owned()),
                        CrossingGrantN {
                            remaining: 1,
                            provisioned: 3,
                        },
                    ),
                    (
                        ("z".to_owned(), "assignment-z".to_owned()),
                        CrossingGrantN {
                            remaining: 2,
                            provisioned: 4,
                        },
                    ),
                ],
                tool_registered: vec!["tool-a".to_owned(), "tool-z".to_owned()],
            }
        );
    }
}
