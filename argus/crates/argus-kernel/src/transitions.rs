//! TzimtzumV4 pure transitions — the Charon/Aeneas extraction entry points.
//!
//! Each of the 12 V4 actions is a pure
//! `fn(KernelState, ...) -> Result<(KernelState, KernelAction), KernelError>`.
//! The invocation/crossing commands (`ingest`, `begin_invocation`, `authorize_inspected`,
//! `settle_invocation`, `cross_output`) are added in Tasks A3–A5.
//!
//! Every traversal follows the §13 extraction discipline: Vec-backed collections only, explicit
//! index `while` loops, no closures, no early `return` inside loops, owned accessors only.

use crate::background::BackgroundTheory;
use crate::capability::CapKind;
use crate::collections::VecMap;
use crate::error::KernelError;
use crate::event::KernelAction;
use crate::state::KernelState;
use crate::types::{
    AgentId, AssignmentDigest, ConfLevel, CrossingGrant, CrossingKey, Disposition, IntegLevel,
    InvocationId, Mode, Outcome, ResolutionAttestation, ToolId,
};

/// `register_tool` — add an unregistered exact tool identity (E17: `ToolId` is the composite
/// entry/version/hash identity, so registration is per-version).
pub fn register_tool(
    mut s: KernelState,
    tool: ToolId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if s.tool_registered.contains(&tool) {
        return Err(KernelError::ToolAlreadyRegistered);
    }
    s.tool_registered.insert(tool.clone());
    Ok((s, KernelAction::RegisterTool { tool }))
}

/// `unregister_tool` — remove a registered tool only when no pending record or open challenge
/// references it. The two ∀-guards are accumulator scans (no early `return` in the loop).
pub fn unregister_tool(
    mut s: KernelState,
    tool: ToolId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !s.tool_registered.contains(&tool) {
        return Err(KernelError::ToolNotRegistered);
    }
    let mut in_use = false;
    let mut i = 0;
    while i < s.pending.len() {
        let inv = s.pending.key_at(i).clone();
        if let Some(j) = s.pending.get_cloned(&inv) {
            if j.policy.tool == tool {
                in_use = true;
            }
        }
        i += 1;
    }
    let mut i = 0;
    while i < s.challenges.len() {
        let inv = s.challenges.key_at(i).clone();
        if let Some(sc) = s.challenges.get_cloned(&inv) {
            if sc.policy.tool == tool {
                in_use = true;
            }
        }
        i += 1;
    }
    if in_use {
        return Err(KernelError::ToolInUse);
    }
    s.tool_registered.remove(&tool);
    Ok((s, KernelAction::UnregisterTool { tool }))
}

/// `delegate` — create an active child of an active grantor with an empty compartment (no caps,
/// labels, pending records, challenges, or grants). The grantee must not already be some active
/// child's parent, or reusing its id would orphan those children (Task 2 review High).
pub fn delegate(
    mut s: KernelState,
    bg: &BackgroundTheory,
    grantor: AgentId,
    grantee: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !s.agent_active.contains(&grantor) {
        return Err(KernelError::AgentInactive);
    }
    if s.agent_active.contains(&grantee) {
        return Err(KernelError::AgentAlreadyActive);
    }
    if grantee == *bg.root_agent() {
        return Err(KernelError::RootNotAllowed);
    }
    let mut is_parent = false;
    let mut i = 0;
    while i < s.agent_parent.len() {
        let child = s.agent_parent.key_at(i).clone();
        if let Some(p) = s.agent_parent.get_cloned(&child) {
            if p == grantee {
                is_parent = true;
            }
        }
        i += 1;
    }
    if is_parent {
        return Err(KernelError::AgentHasChildren);
    }

    s.agent_active.insert(grantee.clone());
    // agent_parent: keep every edge not touching grantee, then add grantee -> grantor.
    let mut kept: VecMap<AgentId, AgentId> = VecMap::new();
    let mut i = 0;
    while i < s.agent_parent.len() {
        let child = s.agent_parent.key_at(i).clone();
        if let Some(p) = s.agent_parent.get_cloned(&child) {
            if child != grantee && p != grantee {
                kept.insert(child, p);
            }
        }
        i += 1;
    }
    kept.insert(grantee.clone(), grantor.clone());
    s.agent_parent = kept;
    s.agent_cap.remove(&grantee);
    s.taint_levels.remove(&grantee);
    s.integ_levels.remove(&grantee);
    s.drop_pending_of(&grantee);
    s.drop_challenges_of(&grantee);
    s.drop_grants_of(&grantee);
    Ok((s, KernelAction::Delegate { grantor, grantee }))
}

/// `grant_capability` — add one capability to an active child whose active parent holds it.
pub fn grant_capability(
    mut s: KernelState,
    parent: AgentId,
    child: AgentId,
    cap: CapKind,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !s.agent_active.contains(&parent) {
        return Err(KernelError::AgentInactive);
    }
    if !s.agent_active.contains(&child) {
        return Err(KernelError::AgentInactive);
    }
    let parent_ok = match s.agent_parent.get_cloned(&child) {
        Some(p) => p == parent,
        None => false,
    };
    if !parent_ok {
        return Err(KernelError::NotDirectChild);
    }
    if !s.agent_cap.set_contains(&parent, &cap) {
        return Err(KernelError::CapabilityMissing);
    }
    s.agent_cap.insert_into(child.clone(), cap);
    Ok((s, KernelAction::GrantCapability { parent, child, cap }))
}

/// `grant_crossing` — the root-only operator faucet. Sets `(agent, assignment)`'s grant to `n`
/// remaining and provisioned uses (set-to-`n`, so repeated identical provisioning is idempotent).
pub fn grant_crossing(
    mut s: KernelState,
    bg: &BackgroundTheory,
    grantor: AgentId,
    agent: AgentId,
    assignment: AssignmentDigest,
    n: u32,
) -> Result<(KernelState, KernelAction), KernelError> {
    if grantor != *bg.root_agent() {
        return Err(KernelError::NotRoot);
    }
    if !s.agent_active.contains(&grantor) {
        return Err(KernelError::AgentInactive);
    }
    if !s.agent_active.contains(&agent) {
        return Err(KernelError::AgentInactive);
    }
    let key = CrossingKey {
        agent: agent.clone(),
        assignment: assignment.clone(),
    };
    s.crossing_grants.insert(
        key,
        CrossingGrant {
            remaining: n,
            provisioned: n,
        },
    );
    Ok((
        s,
        KernelAction::GrantCrossing {
            grantor,
            agent,
            assignment,
            n,
        },
    ))
}

/// `revoke` — revoke an active child, destroying its capabilities, labels, pending records
/// (quarantined included), open challenges, and crossing grants. Consumed histories are never
/// touched. The target's own parent edge is dropped; its children are left for `cascade_revoke`.
pub fn revoke(
    mut s: KernelState,
    bg: &BackgroundTheory,
    parent: AgentId,
    target: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    let parent_ok = match s.agent_parent.get_cloned(&target) {
        Some(p) => p == parent,
        None => false,
    };
    if !parent_ok {
        return Err(KernelError::NotDirectChild);
    }
    if !s.agent_active.contains(&parent) {
        return Err(KernelError::AgentInactive);
    }
    if !s.agent_active.contains(&target) {
        return Err(KernelError::AgentInactive);
    }
    if target == *bg.root_agent() {
        return Err(KernelError::RootNotAllowed);
    }
    clear_agent(&mut s, &target);
    Ok((s, KernelAction::Revoke { parent, target }))
}

/// `cascade_revoke` — revoke an active child whose parent is already inactive. Same destruction.
pub fn cascade_revoke(
    mut s: KernelState,
    bg: &BackgroundTheory,
    child: AgentId,
    parent: AgentId,
) -> Result<(KernelState, KernelAction), KernelError> {
    let parent_ok = match s.agent_parent.get_cloned(&child) {
        Some(p) => p == parent,
        None => false,
    };
    if !parent_ok {
        return Err(KernelError::NotDirectChild);
    }
    if s.agent_active.contains(&parent) {
        return Err(KernelError::ParentStillActive);
    }
    if !s.agent_active.contains(&child) {
        return Err(KernelError::AgentInactive);
    }
    if child == *bg.root_agent() {
        return Err(KernelError::RootNotAllowed);
    }
    clear_agent(&mut s, &child);
    Ok((s, KernelAction::CascadeRevoke { child, parent }))
}

/// Remove all agent-owned authority/state for `agent` (revoke/cascade_revoke share this exact
/// destruction set). The target's own parent edge (keyed by the target as child) is dropped.
fn clear_agent(s: &mut KernelState, agent: &AgentId) {
    s.agent_active.remove(agent);
    s.agent_parent.remove(agent);
    s.agent_cap.remove(agent);
    s.taint_levels.remove(agent);
    s.integ_levels.remove(agent);
    s.drop_pending_of(agent);
    s.drop_challenges_of(agent);
    s.drop_grants_of(agent);
}

/// The three ingest holds against every pending record of `a`: flow (per egress channel),
/// clearance (per target), and integrity (per target). Accumulator scan (no early return).
fn ingest_holds(
    s: &KernelState,
    bg: &BackgroundTheory,
    a: &AgentId,
    pconf: ConfLevel,
    pinteg: IntegLevel,
) -> bool {
    let mut holds = true;
    let mut i = 0;
    while i < s.pending.len() {
        let inv = s.pending.key_at(i).clone();
        if let Some(j) = s.pending.get_cloned(&inv) {
            if j.agent == *a {
                let vouched = j.vouched();
                // Clearance hold: pconf clears the record's frozen clearance ceiling.
                if !pconf.le(j.policy.conf_clearance) {
                    holds = false;
                }
                // Integrity hold: ALLOW, or INSPECT with the pending party vouched.
                let integ_allows = j.policy.integ_floor.le(pinteg);
                let integ_inspects = j.policy.integ_inspect.le(pinteg);
                if !(integ_allows || (integ_inspects && vouched)) {
                    holds = false;
                }
                // Flow hold: for every attested egress channel, ALLOW or INSPECT+vouch.
                let mut e = 0;
                while e < j.egress.len() {
                    let eg = *j.egress.at(e);
                    let flow_allows = bg.flow_allows(pconf, eg);
                    let flow_inspects = bg.flow_inspects(pconf, eg);
                    if !(flow_allows || (flow_inspects && vouched)) {
                        holds = false;
                    }
                    e += 1;
                }
            }
        }
        i += 1;
    }
    holds
}

/// `ingest` — add a frozen provenance pair `(pconf, pinteg)` to an active agent's labels. The
/// enforcement disposition is COMPUTED (E19): permitted when the three holds pass; monitor-bypassed
/// (demoting the agent's live permits) when a hold fails under monitor mode; otherwise refused. A2A
/// provenance (`src = Some`) must dominate the source agent's held labels in both dimensions (E21).
pub fn ingest(
    mut s: KernelState,
    bg: &BackgroundTheory,
    a: AgentId,
    src: Option<AgentId>,
    pconf: ConfLevel,
    pinteg: IntegLevel,
) -> Result<(KernelState, KernelAction), KernelError> {
    if !s.agent_active.contains(&a) {
        return Err(KernelError::AgentInactive);
    }
    if let Some(src_agent) = &src {
        let mut dominated = true;
        let src_taint = s.taint_levels.get_set_or_empty(src_agent);
        let mut i = 0;
        while i < src_taint.len() {
            let l = *src_taint.at(i);
            if !l.le(pconf) {
                dominated = false;
            }
            i += 1;
        }
        let src_integ = s.integ_levels.get_set_or_empty(src_agent);
        let mut i = 0;
        while i < src_integ.len() {
            let l = *src_integ.at(i);
            if !pinteg.le(l) {
                dominated = false;
            }
            i += 1;
        }
        if !dominated {
            return Err(KernelError::ProvenanceNotDominated);
        }
    }

    let holds = ingest_holds(&s, bg, &a, pconf, pinteg);
    let disposition = if holds {
        Disposition::Permitted
    } else if bg.mode() == Mode::Monitor {
        Disposition::MonitorBypassed
    } else {
        return Err(KernelError::IngestHoldFailed);
    };

    s.taint_levels.insert_into(a.clone(), pconf);
    s.integ_levels.insert_into(a.clone(), pinteg);
    if disposition == Disposition::MonitorBypassed {
        s.demote_all_of(&a);
    }
    Ok((
        s,
        KernelAction::Ingest {
            agent: a,
            src,
            pconf,
            pinteg,
            disposition,
        },
    ))
}

/// `settle_invocation` — close a pending record on `success`/`failure` (absorbing its frozen output
/// provenance) or quarantine it on `ambiguous`. The owning agent, disposition, and absorbed pair
/// are pinned to the record. A quarantined record settles only via a scoped one-use resolution
/// attestation and a non-ambiguous outcome; a non-quarantined record forbids an attestation.
/// Settling a non-contained (bypassed) record demotes the owner's remaining permits (E18).
pub fn settle_invocation(
    mut s: KernelState,
    inv: InvocationId,
    outcome: Outcome,
    att: Option<ResolutionAttestation>,
) -> Result<(KernelState, KernelAction), KernelError> {
    let j = match s.pending.get_cloned(&inv) {
        Some(j) => j,
        None => return Err(KernelError::NotPending),
    };
    let a = j.agent.clone();
    if !s.agent_active.contains(&a) {
        return Err(KernelError::AgentInactive);
    }
    let disposition = j.disposition;
    let clvl = j.policy.output_conf;
    let ilvl = j.policy.output_integ;

    if j.quarantined {
        if outcome == Outcome::Ambiguous {
            return Err(KernelError::QuarantineResolutionRequired);
        }
        let valid = match &att {
            Some(r) => {
                r.inv == inv && r.outcome == outcome && !s.consumed_attestations.contains(&r.id)
            }
            None => false,
        };
        if !valid {
            return Err(KernelError::ResolutionAttestationInvalid);
        }
    } else if att.is_some() {
        return Err(KernelError::NotQuarantined);
    }

    // settleAt: quarantine on ambiguous, else close.
    if outcome == Outcome::Ambiguous {
        let mut jq = j.clone();
        jq.quarantined = true;
        s.pending.insert(inv.clone(), jq);
    } else {
        s.pending.remove(&inv);
    }
    // Non-contained settlement demotes the owner's remaining permits (E18).
    if disposition != Disposition::Permitted {
        s.demote_all_of(&a);
    }
    // Ordinary outcomes absorb both frozen dimensions; ambiguous absorbs nothing.
    if outcome != Outcome::Ambiguous {
        s.taint_levels.insert_into(a.clone(), clvl);
        s.integ_levels.insert_into(a.clone(), ilvl);
    }
    let resolution = match &att {
        Some(r) => {
            s.consumed_attestations.insert(r.id.clone());
            Some(r.id.clone())
        }
        None => None,
    };
    Ok((
        s,
        KernelAction::SettleInvocation {
            inv,
            agent: a,
            disposition,
            outcome,
            clvl,
            ilvl,
            resolution,
        },
    ))
}
