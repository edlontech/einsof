use argus_kernel::{AgentId, KernelState};

use crate::wire::{ActionPolicySnapshotN, ConformanceAttestationN, CrossInputN};
use crate::{CommandN, ErrorN};

pub const MAX_OPAQUE_UTF8_BYTES: usize = 1_024;
pub const MAX_AGENTS: usize = 4_096;
pub const MAX_PARENT_OR_LABEL_KEYS: usize = 4_096;
pub const MAX_TOOLS: usize = 1_024;
pub const MAX_PENDING: usize = 4_096;
pub const MAX_CHALLENGES: usize = 4_096;
pub const MAX_CROSSING_GRANTS: usize = 16_384;
pub const MAX_CONSUMED_IDS: usize = 65_536;
pub const MAX_CONSUMED_ATTESTATIONS: usize = 65_536;
pub const MAX_CONSUMED_CROSSINGS: usize = 65_536;
pub const MAX_RETAINED_UTF8_BYTES: usize = 16 * 1024 * 1024;
pub const MAX_ACCEPTED_SEQUENCE: u64 = 100_000;
pub const MAX_RECOVERY_ENVELOPES: usize = 100_000;
pub const MAX_REPLAY_CONTENT_BYTES: usize = 64 * 1024 * 1024;
pub const MAX_CAPABILITIES: usize = 15;
pub const MAX_EGRESS_KINDS: usize = 4;
pub const MAX_CONF_LEVELS: usize = 4;
pub const MAX_INTEG_LEVELS: usize = 4;

fn checked_capacity(current: usize, addition: usize, maximum: usize) -> Result<usize, ErrorN> {
    let total = current
        .checked_add(addition)
        .ok_or(ErrorN::CapacityExceeded)?;
    if total <= maximum {
        Ok(total)
    } else {
        Err(ErrorN::CapacityExceeded)
    }
}

fn check_len(current: usize, maximum: usize) -> Result<(), ErrorN> {
    checked_capacity(current, 0, maximum).map(|_| ())
}

struct TextBudget {
    total: usize,
}

impl TextBudget {
    fn new() -> Self {
        Self { total: 0 }
    }

    #[cfg(test)]
    fn from_total(total: usize) -> Result<Self, ErrorN> {
        check_len(total, MAX_RETAINED_UTF8_BYTES)?;
        Ok(Self { total })
    }

    fn add(&mut self, value: &str) -> Result<(), ErrorN> {
        check_len(value.len(), MAX_OPAQUE_UTF8_BYTES)?;
        self.total = checked_capacity(self.total, value.len(), MAX_RETAINED_UTF8_BYTES)?;
        Ok(())
    }
}

fn check_policy(policy: &ActionPolicySnapshotN) -> Result<(), ErrorN> {
    check_len(policy.required_caps.len(), MAX_CAPABILITIES)?;
    check_len(policy.declared_egress.len(), MAX_EGRESS_KINDS)
}

fn check_evidence(evidence: &ConformanceAttestationN) -> Result<(), ErrorN> {
    for value in [
        &evidence.id,
        &evidence.output,
        &evidence.src,
        &evidence.rcv,
        &evidence.descriptor,
        &evidence.assignment,
    ] {
        check_len(value.len(), MAX_OPAQUE_UTF8_BYTES)?;
    }
    Ok(())
}

fn check_cross_input(input: &CrossInputN) -> Result<(), ErrorN> {
    for value in [
        &input.src,
        &input.rcv,
        &input.crossing,
        &input.output_hash,
        &input.descriptor,
        &input.assignment,
    ] {
        check_len(value.len(), MAX_OPAQUE_UTF8_BYTES)?;
    }
    if let Some(evidence) = &input.evidence {
        check_evidence(evidence)?;
    }
    Ok(())
}

fn check_command(command: &CommandN) -> Result<(), ErrorN> {
    let check = |value: &str| check_len(value.len(), MAX_OPAQUE_UTF8_BYTES);
    match command {
        CommandN::RegisterTool(command) => check(&command.tool),
        CommandN::UnregisterTool(command) => check(&command.tool),
        CommandN::Delegate(command) => {
            check(&command.grantor)?;
            check(&command.grantee)
        }
        CommandN::GrantCapability(command) => {
            check(&command.parent)?;
            check(&command.child)
        }
        CommandN::GrantCrossing(command) => {
            check(&command.grantor)?;
            check(&command.agent)?;
            check(&command.assignment)
        }
        CommandN::Revoke(command) => {
            check(&command.parent)?;
            check(&command.target)
        }
        CommandN::CascadeRevoke(command) => {
            check(&command.child)?;
            check(&command.parent)
        }
        CommandN::Ingest(command) => {
            check(&command.agent)?;
            if let Some(src) = &command.src {
                check(src)?;
            }
            Ok(())
        }
        CommandN::BeginInvocation(command) => {
            for value in [
                &command.agent,
                &command.inv,
                &command.challenge,
                &command.policy.tool,
                &command.policy.policy_digest,
                &command.args_hash,
            ] {
                check(value)?;
            }
            check_policy(&command.policy)?;
            check_len(command.egress.len(), MAX_EGRESS_KINDS)
        }
        CommandN::AuthorizeInspected(command) => {
            for value in [
                &command.inv,
                &command.attestation.id,
                &command.attestation.inv,
                &command.attestation.challenge,
                &command.attestation.args_hash,
                &command.attestation.policy_digest,
            ] {
                check(value)?;
            }
            Ok(())
        }
        CommandN::SettleInvocation(command) => {
            check(&command.inv)?;
            if let Some(resolution) = &command.resolution {
                check(&resolution.id)?;
                check(&resolution.inv)?;
            }
            Ok(())
        }
        CommandN::CrossOutput(command) => check_cross_input(&command.input),
    }
}

fn retained_text(state: &KernelState) -> Result<TextBudget, ErrorN> {
    let mut text = TextBudget::new();
    for agent in state.agent_active.iter() {
        text.add(&agent.0)?;
    }
    for (child, parent) in state.agent_parent.iter() {
        text.add(&child.0)?;
        text.add(&parent.0)?;
    }
    for (agent, _) in state.agent_cap.iter() {
        text.add(&agent.0)?;
    }
    for (agent, _) in state.taint_levels.iter() {
        text.add(&agent.0)?;
    }
    for (agent, _) in state.integ_levels.iter() {
        text.add(&agent.0)?;
    }
    for (inv, pending) in state.pending.iter() {
        text.add(&inv.0)?;
        text.add(&pending.agent.0)?;
        text.add(&pending.policy.tool.0)?;
        text.add(&pending.policy.policy_digest.0)?;
        if let argus_kernel::Admission::Inspected(attestation) = &pending.admission {
            text.add(&attestation.0)?;
        }
    }
    for (inv, challenge) in state.challenges.iter() {
        text.add(&inv.0)?;
        text.add(&challenge.challenge.0)?;
        text.add(&challenge.agent.0)?;
        text.add(&challenge.policy.tool.0)?;
        text.add(&challenge.policy.policy_digest.0)?;
        text.add(&challenge.args_hash.0)?;
    }
    for inv in state.consumed_ids.iter() {
        text.add(&inv.0)?;
    }
    for attestation in state.consumed_attestations.iter() {
        text.add(&attestation.0)?;
    }
    for crossing in state.consumed_crossings.iter() {
        text.add(&crossing.0)?;
    }
    for (key, _) in state.crossing_grants.iter() {
        text.add(&key.agent.0)?;
        text.add(&key.assignment.0)?;
    }
    for tool in state.tool_registered.iter() {
        text.add(&tool.0)?;
    }
    Ok(text)
}

fn check_state_shape(state: &KernelState) -> Result<(), ErrorN> {
    check_len(state.agent_active.len(), MAX_AGENTS)?;
    check_len(state.agent_parent.len(), MAX_PARENT_OR_LABEL_KEYS)?;
    check_len(state.agent_cap.len(), MAX_PARENT_OR_LABEL_KEYS)?;
    check_len(state.taint_levels.len(), MAX_PARENT_OR_LABEL_KEYS)?;
    check_len(state.integ_levels.len(), MAX_PARENT_OR_LABEL_KEYS)?;
    check_len(state.pending.len(), MAX_PENDING)?;
    check_len(state.challenges.len(), MAX_CHALLENGES)?;
    check_len(state.crossing_grants.len(), MAX_CROSSING_GRANTS)?;
    check_len(state.consumed_ids.len(), MAX_CONSUMED_IDS)?;
    check_len(state.consumed_attestations.len(), MAX_CONSUMED_ATTESTATIONS)?;
    check_len(state.consumed_crossings.len(), MAX_CONSUMED_CROSSINGS)?;
    check_len(state.tool_registered.len(), MAX_TOOLS)?;
    for (_, caps) in state.agent_cap.iter() {
        check_len(caps.len(), MAX_CAPABILITIES)?;
    }
    for (_, levels) in state.taint_levels.iter() {
        check_len(levels.len(), MAX_CONF_LEVELS)?;
    }
    for (_, levels) in state.integ_levels.iter() {
        check_len(levels.len(), MAX_INTEG_LEVELS)?;
    }
    for (_, pending) in state.pending.iter() {
        check_len(pending.policy.required_caps.len(), MAX_CAPABILITIES)?;
        check_len(pending.policy.declared_egress.len(), MAX_EGRESS_KINDS)?;
        check_len(pending.egress.len(), MAX_EGRESS_KINDS)?;
    }
    for (_, challenge) in state.challenges.iter() {
        check_len(challenge.policy.required_caps.len(), MAX_CAPABILITIES)?;
        check_len(challenge.policy.declared_egress.len(), MAX_EGRESS_KINDS)?;
        check_len(challenge.egress.len(), MAX_EGRESS_KINDS)?;
    }
    Ok(())
}

fn checked_state_text(state: &KernelState) -> Result<TextBudget, ErrorN> {
    check_state_shape(state)?;
    retained_text(state)
}

pub(crate) fn check_state(state: &KernelState) -> Result<(), ErrorN> {
    checked_state_text(state).map(|_| ())
}

fn add_label_key_if_absent<T: Clone + PartialEq>(
    map: &argus_kernel::VecMap<AgentId, T>,
    agent: &str,
) -> usize {
    usize::from(!map.contains_key(&AgentId::new(agent)))
}

fn check_label_key<T: Clone + PartialEq>(
    map: &argus_kernel::VecMap<AgentId, T>,
    agent: &AgentId,
) -> Result<(), ErrorN> {
    checked_capacity(
        map.len(),
        usize::from(!map.contains_key(agent)),
        MAX_PARENT_OR_LABEL_KEYS,
    )?;
    Ok(())
}

fn check_post_transition(
    state: &KernelState,
    command: &CommandN,
    text: &mut TextBudget,
) -> Result<(), ErrorN> {
    match command {
        CommandN::RegisterTool(command) => {
            checked_capacity(state.tool_registered.len(), 1, MAX_TOOLS)?;
            text.add(&command.tool)
        }
        CommandN::UnregisterTool(_) | CommandN::Revoke(_) | CommandN::CascadeRevoke(_) => Ok(()),
        CommandN::Delegate(command) => {
            checked_capacity(state.agent_active.len(), 1, MAX_AGENTS)?;
            checked_capacity(state.agent_parent.len(), 1, MAX_PARENT_OR_LABEL_KEYS)?;
            text.add(&command.grantee)?;
            text.add(&command.grantee)?;
            text.add(&command.grantor)
        }
        CommandN::GrantCapability(command) => {
            let child = AgentId::new(&command.child);
            checked_capacity(
                state.agent_cap.len(),
                usize::from(!state.agent_cap.contains_key(&child)),
                MAX_PARENT_OR_LABEL_KEYS,
            )?;
            let existing = state.agent_cap.get(&child);
            let addition =
                usize::from(existing.is_none_or(|caps| !caps.contains(&command.cap.into_kernel())));
            checked_capacity(
                existing.map_or(0, argus_kernel::VecSet::len),
                addition,
                MAX_CAPABILITIES,
            )?;
            if existing.is_none() {
                text.add(&command.child)?;
            }
            Ok(())
        }
        CommandN::GrantCrossing(command) => {
            checked_capacity(state.crossing_grants.len(), 1, MAX_CROSSING_GRANTS)?;
            text.add(&command.agent)?;
            text.add(&command.assignment)
        }
        CommandN::Ingest(command) => {
            let taint_addition = add_label_key_if_absent(&state.taint_levels, &command.agent);
            let integ_addition = add_label_key_if_absent(&state.integ_levels, &command.agent);
            checked_capacity(
                state.taint_levels.len(),
                taint_addition,
                MAX_PARENT_OR_LABEL_KEYS,
            )?;
            checked_capacity(
                state.integ_levels.len(),
                integ_addition,
                MAX_PARENT_OR_LABEL_KEYS,
            )?;
            let agent = AgentId::new(&command.agent);
            checked_capacity(
                state
                    .taint_levels
                    .get(&agent)
                    .map_or(0, argus_kernel::VecSet::len),
                usize::from(
                    state
                        .taint_levels
                        .get(&agent)
                        .is_none_or(|levels| !levels.contains(&command.pconf.into_kernel())),
                ),
                MAX_CONF_LEVELS,
            )?;
            checked_capacity(
                state
                    .integ_levels
                    .get(&agent)
                    .map_or(0, argus_kernel::VecSet::len),
                usize::from(
                    state
                        .integ_levels
                        .get(&agent)
                        .is_none_or(|levels| !levels.contains(&command.pinteg.into_kernel())),
                ),
                MAX_INTEG_LEVELS,
            )?;
            if taint_addition == 1 {
                text.add(&command.agent)?;
            }
            if integ_addition == 1 {
                text.add(&command.agent)?;
            }
            Ok(())
        }
        CommandN::BeginInvocation(command) => {
            checked_capacity(state.pending.len(), 1, MAX_PENDING)?;
            checked_capacity(state.challenges.len(), 1, MAX_CHALLENGES)?;
            checked_capacity(state.consumed_ids.len(), 1, MAX_CONSUMED_IDS)?;
            for value in [
                &command.inv,
                &command.inv,
                &command.agent,
                &command.challenge,
                &command.policy.tool,
                &command.policy.policy_digest,
                &command.args_hash,
            ] {
                text.add(value)?;
            }
            Ok(())
        }
        CommandN::AuthorizeInspected(command) => {
            checked_capacity(state.pending.len(), 1, MAX_PENDING)?;
            checked_capacity(
                state.consumed_attestations.len(),
                1,
                MAX_CONSUMED_ATTESTATIONS,
            )?;
            text.add(&command.attestation.id)?;
            text.add(&command.attestation.id)?;
            if let Some(scope) = state
                .challenges
                .get(&argus_kernel::InvocationId::new(&command.inv))
            {
                text.add(&command.inv)?;
                text.add(&scope.agent.0)?;
                text.add(&scope.policy.tool.0)?;
                text.add(&scope.policy.policy_digest.0)?;
            }
            Ok(())
        }
        CommandN::SettleInvocation(command) => {
            if command.resolution.is_some() {
                checked_capacity(
                    state.consumed_attestations.len(),
                    1,
                    MAX_CONSUMED_ATTESTATIONS,
                )?;
            }
            if let Some(pending) = state
                .pending
                .get(&argus_kernel::InvocationId::new(&command.inv))
            {
                check_label_key(&state.taint_levels, &pending.agent)?;
                check_label_key(&state.integ_levels, &pending.agent)?;
                text.add(&pending.agent.0)?;
                text.add(&pending.agent.0)?;
            }
            if let Some(resolution) = &command.resolution {
                text.add(&resolution.id)?;
            }
            Ok(())
        }
        CommandN::CrossOutput(command) => check_cross_post(state, &command.input, text),
    }
}

fn check_cross_post(
    state: &KernelState,
    input: &CrossInputN,
    text: &mut TextBudget,
) -> Result<(), ErrorN> {
    checked_capacity(state.consumed_crossings.len(), 1, MAX_CONSUMED_CROSSINGS)?;
    if input.evidence.is_some() {
        checked_capacity(
            state.consumed_attestations.len(),
            1,
            MAX_CONSUMED_ATTESTATIONS,
        )?;
    }
    let source = AgentId::new(&input.src);
    let receiver = AgentId::new(&input.rcv);
    check_label_key(&state.taint_levels, &receiver)?;
    check_label_key(&state.integ_levels, &receiver)?;
    let source_conf = state.taint_levels.get(&source);
    let receiver_conf = state.taint_levels.get(&receiver);
    let conf_addition = source_conf.map_or(1, |levels| {
        levels
            .iter()
            .filter(|level| receiver_conf.is_none_or(|held| !held.contains(level)))
            .count()
            .max(1)
    });
    checked_capacity(
        receiver_conf.map_or(0, argus_kernel::VecSet::len),
        conf_addition,
        MAX_CONF_LEVELS,
    )?;
    let source_integ = state.integ_levels.get(&source);
    let receiver_integ = state.integ_levels.get(&receiver);
    let integ_addition = source_integ.map_or(1, |levels| {
        levels
            .iter()
            .filter(|level| receiver_integ.is_none_or(|held| !held.contains(level)))
            .count()
            .max(1)
    });
    checked_capacity(
        receiver_integ.map_or(0, argus_kernel::VecSet::len),
        integ_addition,
        MAX_INTEG_LEVELS,
    )?;
    text.add(&input.crossing)?;
    text.add(&input.rcv)?;
    text.add(&input.rcv)?;
    if let Some(evidence) = &input.evidence {
        text.add(&evidence.id)?;
    }
    Ok(())
}

pub fn preflight(state: &KernelState, sequence: u64, command: &CommandN) -> Result<(), ErrorN> {
    let next = sequence.checked_add(1).ok_or(ErrorN::SequenceExhausted)?;
    if next > MAX_ACCEPTED_SEQUENCE {
        return Err(ErrorN::SequenceExhausted);
    }
    let mut text = checked_state_text(state)?;
    check_command(command)?;
    check_post_transition(state, command, &mut text)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wire::{GrantCrossingCommandN, RegisterToolCommandN};

    #[test]
    fn capacity_profile_is_protocol_fixed() {
        assert_eq!(
            [
                MAX_OPAQUE_UTF8_BYTES,
                MAX_AGENTS,
                MAX_PARENT_OR_LABEL_KEYS,
                MAX_TOOLS,
                MAX_PENDING,
                MAX_CHALLENGES,
                MAX_CROSSING_GRANTS,
                MAX_CONSUMED_IDS,
                MAX_CONSUMED_ATTESTATIONS,
                MAX_CONSUMED_CROSSINGS,
                MAX_RETAINED_UTF8_BYTES,
                MAX_ACCEPTED_SEQUENCE as usize,
                MAX_RECOVERY_ENVELOPES,
                MAX_REPLAY_CONTENT_BYTES,
                MAX_CAPABILITIES,
                MAX_EGRESS_KINDS,
                MAX_CONF_LEVELS,
                MAX_INTEG_LEVELS,
            ],
            [
                1_024,
                4_096,
                4_096,
                1_024,
                4_096,
                4_096,
                16_384,
                65_536,
                65_536,
                65_536,
                16 * 1024 * 1024,
                100_000,
                100_000,
                64 * 1024 * 1024,
                15,
                4,
                4,
                4,
            ]
        );
    }

    #[test]
    fn checked_capacity_accepts_exact_limit_and_rejects_one_over() {
        assert_eq!(checked_capacity(4_095, 1, MAX_AGENTS), Ok(4_096));
        assert_eq!(
            checked_capacity(4_096, 1, MAX_AGENTS),
            Err(ErrorN::CapacityExceeded)
        );
    }

    #[test]
    fn text_growth_accepts_exact_limit_and_rejects_one_over() {
        let mut exact = TextBudget::from_total(MAX_RETAINED_UTF8_BYTES - 1).unwrap();
        assert_eq!(exact.add("x"), Ok(()));
        assert_eq!(exact.add("x"), Err(ErrorN::CapacityExceeded));
    }

    #[test]
    fn preflight_checks_sequence_without_allocating_history() {
        let command = CommandN::RegisterTool(RegisterToolCommandN {
            tool: "tool".to_owned(),
        });

        assert_eq!(
            preflight(&KernelState::initial(), MAX_ACCEPTED_SEQUENCE - 1, &command),
            Ok(())
        );
        assert_eq!(
            preflight(&KernelState::initial(), MAX_ACCEPTED_SEQUENCE, &command),
            Err(ErrorN::SequenceExhausted)
        );
    }

    #[test]
    fn preflight_accepts_maximum_u32_crossing_count() {
        let command = CommandN::GrantCrossing(GrantCrossingCommandN {
            grantor: "root".to_owned(),
            agent: "agent".to_owned(),
            assignment: "assignment".to_owned(),
            n: u32::MAX,
        });

        assert_eq!(preflight(&KernelState::initial(), 0, &command), Ok(()));
    }

    #[test]
    fn preflight_rejects_one_over_opaque_limit() {
        let command = CommandN::RegisterTool(RegisterToolCommandN {
            tool: "x".repeat(MAX_OPAQUE_UTF8_BYTES + 1),
        });

        assert_eq!(
            preflight(&KernelState::initial(), 0, &command),
            Err(ErrorN::CapacityExceeded)
        );
    }
}
