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
use crate::collections::{VecMap, VecSet};
use crate::error::KernelError;
use crate::event::KernelAction;
use crate::state::KernelState;
use crate::types::{
    ActionPolicySnapshot, Admission, AgentId, AssignmentDigest, ChallengeId, ChallengeScope,
    ConfLevel, ContentHash, CrossingGrant, CrossingKey, Disposition, EgressKind,
    InspectionAttestation, IntegLevel, InvocationId, Mode, Outcome, PendingInvocation,
    ResolutionAttestation, ToolId, Verdict,
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

// ---------------------------------------------------------------------------
// begin_invocation / authorize_inspected — the nine-check admission gate (A4).
// Every helper below is extracted: Vec-backed, index `while` loops, no closures,
// no early `return` inside loops, owned accessors. `bool` conjunctions latch a
// single `ok` flag instead of short-circuiting so the loop bodies stay total.
// ---------------------------------------------------------------------------

/// CHECK 1: the agent holds every capability the frozen snapshot requires.
fn check_capability(s: &KernelState, a: &AgentId, snap: &ActionPolicySnapshot) -> bool {
    let mut ok = true;
    let mut i = 0;
    while i < snap.required_caps.len() {
        let c = *snap.required_caps.at(i);
        if !s.agent_cap.set_contains(a, &c) {
            ok = false;
        }
        i += 1;
    }
    ok
}

/// CHECK 2a/2b/2c: speculative taint clears the snapshot clearance; the new output clears every
/// pending record's clearance; and the new output clears its own snapshot clearance.
fn check_clearance(s: &KernelState, a: &AgentId, snap: &ActionPolicySnapshot) -> bool {
    let mut ok = true;
    let st = s.speculative_taint(a);
    let mut i = 0;
    while i < st.len() {
        let l = *st.at(i);
        if !l.le(snap.conf_clearance) {
            ok = false;
        }
        i += 1;
    }
    let mut i = 0;
    while i < s.pending.len() {
        let inv = s.pending.key_at(i).clone();
        if let Some(j) = s.pending.get_cloned(&inv) {
            if j.agent == *a && !snap.output_conf.le(j.policy.conf_clearance) {
                ok = false;
            }
        }
        i += 1;
    }
    if !snap.output_conf.le(snap.conf_clearance) {
        ok = false;
    }
    ok
}

/// CHECK 3a/3b/3c flow, ALLOW arm (strict) or ALLOW-or-INSPECT arm (admissible). The admissible
/// pending arm requires the pending party vouched for its inspect band (E22).
fn check_flow(
    s: &KernelState,
    bg: &BackgroundTheory,
    a: &AgentId,
    snap: &ActionPolicySnapshot,
    egr: &VecSet<EgressKind>,
    strict: bool,
) -> bool {
    let mut ok = true;
    let st = s.speculative_taint(a);
    let mut i = 0;
    while i < st.len() {
        let l = *st.at(i);
        let mut e = 0;
        while e < egr.len() {
            let eg = *egr.at(e);
            let pass = if strict {
                bg.flow_allows(l, eg)
            } else {
                bg.flow_allows(l, eg) || bg.flow_inspects(l, eg)
            };
            if !pass {
                ok = false;
            }
            e += 1;
        }
        i += 1;
    }
    let mut i = 0;
    while i < s.pending.len() {
        let inv = s.pending.key_at(i).clone();
        if let Some(j) = s.pending.get_cloned(&inv) {
            if j.agent == *a {
                let vouched = j.vouched();
                let mut e = 0;
                while e < j.egress.len() {
                    let eg = *j.egress.at(e);
                    let pass = if strict {
                        bg.flow_allows(snap.output_conf, eg)
                    } else {
                        bg.flow_allows(snap.output_conf, eg)
                            || (bg.flow_inspects(snap.output_conf, eg) && vouched)
                    };
                    if !pass {
                        ok = false;
                    }
                    e += 1;
                }
            }
        }
        i += 1;
    }
    let mut e = 0;
    while e < egr.len() {
        let eg = *egr.at(e);
        let pass = if strict {
            bg.flow_allows(snap.output_conf, eg)
        } else {
            bg.flow_allows(snap.output_conf, eg) || bg.flow_inspects(snap.output_conf, eg)
        };
        if !pass {
            ok = false;
        }
        e += 1;
    }
    ok
}

/// CHECK 5a/5b/5c integrity, ALLOW arm (strict) or ALLOW-or-INSPECT arm (admissible). The
/// admissible pending arm requires the pending party vouched for its inspect band (E22).
fn check_integ(s: &KernelState, a: &AgentId, snap: &ActionPolicySnapshot, strict: bool) -> bool {
    let mut ok = true;
    let si = s.speculative_integ(a);
    let mut i = 0;
    while i < si.len() {
        let l = *si.at(i);
        let pass = if strict {
            snap.integ_floor.le(l)
        } else {
            snap.integ_floor.le(l) || snap.integ_inspect.le(l)
        };
        if !pass {
            ok = false;
        }
        i += 1;
    }
    let mut i = 0;
    while i < s.pending.len() {
        let inv = s.pending.key_at(i).clone();
        if let Some(j) = s.pending.get_cloned(&inv) {
            if j.agent == *a {
                let pass = if strict {
                    j.policy.integ_floor.le(snap.output_integ)
                } else {
                    j.policy.integ_floor.le(snap.output_integ)
                        || (j.policy.integ_inspect.le(snap.output_integ) && j.vouched())
                };
                if !pass {
                    ok = false;
                }
            }
        }
        i += 1;
    }
    let self_pass = if strict {
        snap.integ_floor.le(snap.output_integ)
    } else {
        snap.integ_floor.le(snap.output_integ) || snap.integ_inspect.le(snap.output_integ)
    };
    if !self_pass {
        ok = false;
    }
    ok
}

/// Every attested egress kind is within the frozen declared set (narrowing).
fn egress_narrows(egr: &VecSet<EgressKind>, declared: &VecSet<EgressKind>) -> bool {
    let mut ok = true;
    let mut i = 0;
    while i < egr.len() {
        if !declared.contains(egr.at(i)) {
            ok = false;
        }
        i += 1;
    }
    ok
}

/// An egress-bearing action (non-empty declared set) may not be admitted on an empty attestation.
fn egress_covers(declared: &VecSet<EgressKind>, egr: &VecSet<EgressKind>) -> bool {
    if declared.is_empty() {
        true
    } else {
        !egr.is_empty()
    }
}

/// `beginAdmissible`: every check on its ALLOW-or-INSPECT arm.
fn begin_admissible(
    s: &KernelState,
    bg: &BackgroundTheory,
    a: &AgentId,
    snap: &ActionPolicySnapshot,
    egr: &VecSet<EgressKind>,
    authorized: bool,
) -> bool {
    check_capability(s, a, snap)
        && authorized
        && check_clearance(s, a, snap)
        && check_flow(s, bg, a, snap, egr, false)
        && check_integ(s, a, snap, false)
}

/// `begin_invocation` — the nine-check admission gate. The verdict is COMPUTED from the checks and
/// recorded (E8): `allow` when strict, `inspection_required` when admissible-not-strict, otherwise
/// `deny` (a transition only in monitor mode). The (verdict, mode) product selects one effect:
/// plain permitted pend / enforce challenge / monitor-bypassed pend; enforce deny is no transition.
#[allow(clippy::too_many_arguments)]
pub fn begin_invocation(
    mut s: KernelState,
    bg: &BackgroundTheory,
    a: AgentId,
    inv: InvocationId,
    chal: ChallengeId,
    snap: ActionPolicySnapshot,
    egr: VecSet<EgressKind>,
    ah: ContentHash,
    authorized: bool,
) -> Result<(KernelState, KernelAction), KernelError> {
    // Structural guards (boundary rejections in any mode).
    if !s.agent_active.contains(&a) {
        return Err(KernelError::AgentInactive);
    }
    if a == *bg.root_agent() {
        return Err(KernelError::RootNotAllowed);
    }
    if !s.tool_registered.contains(&snap.tool) {
        return Err(KernelError::ToolNotRegistered);
    }
    if !snap.integ_inspect.le(snap.integ_floor) {
        return Err(KernelError::IncoherentPolicy);
    }
    if s.pending.contains_key(&inv) {
        return Err(KernelError::InvocationExists);
    }
    if s.consumed_ids.contains(&inv) {
        return Err(KernelError::InvocationReplayed);
    }
    if s.challenges.contains_key(&inv) {
        return Err(KernelError::ChallengeAlreadyOpen);
    }
    if !egress_narrows(&egr, &snap.declared_egress) {
        return Err(KernelError::EgressNotNarrowing);
    }
    if !egress_covers(&snap.declared_egress, &egr) {
        return Err(KernelError::EgressNotCovering);
    }

    // The nine checks -> verdict.
    let cap = check_capability(&s, &a, &snap);
    let clear = check_clearance(&s, &a, &snap);
    let flow_strict = check_flow(&s, bg, &a, &snap, &egr, true);
    let flow_adm = check_flow(&s, bg, &a, &snap, &egr, false);
    let integ_strict = check_integ(&s, &a, &snap, true);
    let integ_adm = check_integ(&s, &a, &snap, false);
    let allow = cap && authorized && clear && flow_strict && integ_strict;
    let admissible = cap && authorized && clear && flow_adm && integ_adm;
    let verdict = if allow {
        Verdict::Allow
    } else if admissible {
        Verdict::InspectionRequired
    } else {
        Verdict::Deny
    };

    let tool = snap.tool.clone();
    let mode = bg.mode();

    // (verdict, mode) selects exactly one effect.
    match (verdict, mode) {
        (Verdict::Allow, _) => {
            s.pending.insert(
                inv.clone(),
                PendingInvocation {
                    agent: a.clone(),
                    policy: snap,
                    egress: egr,
                    admission: Admission::Plain,
                    disposition: Disposition::Permitted,
                    authorized,
                    quarantined: false,
                },
            );
        }
        (Verdict::InspectionRequired, Mode::Enforce) => {
            s.challenges.insert(
                inv.clone(),
                ChallengeScope {
                    challenge: chal,
                    agent: a.clone(),
                    policy: snap,
                    egress: egr,
                    args_hash: ah,
                    authorized,
                },
            );
        }
        (Verdict::InspectionRequired, Mode::Monitor) | (Verdict::Deny, Mode::Monitor) => {
            s.pending.insert(
                inv.clone(),
                PendingInvocation {
                    agent: a.clone(),
                    policy: snap,
                    egress: egr,
                    admission: Admission::Bypassed,
                    disposition: Disposition::MonitorBypassed,
                    authorized,
                    quarantined: false,
                },
            );
        }
        (Verdict::Deny, Mode::Enforce) => {
            // Not a transition: return the most specific admissible sub-check that failed.
            if !cap {
                return Err(KernelError::CapabilityMissing);
            }
            if !authorized {
                return Err(KernelError::AuthorizerDenied);
            }
            if !clear {
                return Err(KernelError::ClearanceDenied);
            }
            if !flow_adm {
                return Err(KernelError::FlowGateBlocked);
            }
            return Err(KernelError::IntegrityFloorDenied);
        }
    }

    // Consumed on every transitioning arm (freshness + challenge_unique both lean on it).
    s.consumed_ids.insert(inv.clone());
    Ok((
        s,
        KernelAction::BeginInvocation {
            agent: a,
            inv,
            tool,
            verdict,
            authorized,
        },
    ))
}

/// `authorizeAdmits`: the structural conditions plus the live admissible gate re-evaluated against
/// the CURRENT state (E13). Reuses `begin_admissible` over the frozen challenge scope.
fn authorize_admits(
    s: &KernelState,
    bg: &BackgroundTheory,
    inv: &InvocationId,
    sc: &ChallengeScope,
) -> bool {
    s.agent_active.contains(&sc.agent)
        && sc.agent != *bg.root_agent()
        && s.tool_registered.contains(&sc.policy.tool)
        && sc.policy.integ_inspect.le(sc.policy.integ_floor)
        && !s.pending.contains_key(inv)
        && egress_narrows(&sc.egress, &sc.policy.declared_egress)
        && egress_covers(&sc.policy.declared_egress, &sc.egress)
        && begin_admissible(s, bg, &sc.agent, &sc.policy, &sc.egress, sc.authorized)
}

/// `authorize_inspected` — resolve an open challenge. Exact scope match and one-use are boundary
/// rejections that leave the challenge open (E24). A scope-matching attestation closes the
/// challenge and consumes the id; a positive attestation admitted by the live gate creates a
/// permitted `inspected` pending record, otherwise it closes fail-closed (E13).
pub fn authorize_inspected(
    mut s: KernelState,
    bg: &BackgroundTheory,
    inv: InvocationId,
    att: InspectionAttestation,
) -> Result<(KernelState, KernelAction), KernelError> {
    let sc = match s.challenges.get_cloned(&inv) {
        Some(sc) => sc,
        None => return Err(KernelError::ChallengeNotOpen),
    };
    // Exact scope equality (mismatch = boundary rejection, challenge survives, E24).
    if att.inv != inv
        || att.challenge != sc.challenge
        || att.args_hash != sc.args_hash
        || att.policy_digest != sc.policy.policy_digest
    {
        return Err(KernelError::ChallengeScopeMismatch);
    }
    // One-use (also a boundary rejection).
    if s.consumed_attestations.contains(&att.id) {
        return Err(KernelError::AttestationConsumed);
    }
    // NOTE: `s.consumed_ids.contains(&inv)` is guaranteed by the open challenge (begin consumed it),
    // so the abstract's freshness guard needs no runtime check here.

    let admit = att.positive && authorize_admits(&s, bg, &inv, &sc);
    if admit {
        s.pending.insert(
            inv.clone(),
            PendingInvocation {
                agent: sc.agent.clone(),
                policy: sc.policy.clone(),
                egress: sc.egress.clone(),
                admission: Admission::Inspected(att.id.clone()),
                disposition: Disposition::Permitted,
                authorized: sc.authorized,
                quarantined: false,
            },
        );
    }
    // Both branches close the challenge and consume the attestation; labels are framed.
    s.challenges.remove(&inv);
    s.consumed_attestations.insert(att.id.clone());
    Ok((
        s,
        KernelAction::AuthorizeInspected {
            inv,
            attestation: att.id,
            admitted: admit,
        },
    ))
}
