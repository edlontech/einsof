import Tzimtzum.State

/-!
# TzimtzumV4 invariants

The invariants constrain the agent tree, pending admissions, pairwise pending compatibility,
evidence consumption, and crossing grants. Gate-claiming invariants apply only to `contained`
pending records. Monitor-bypassed records remain in unrestricted speculative state so later
admissions account for effects that execute in monitor mode.
-/

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-! ## Structural invariants -/

/-- **root_always_active**: the root agent can never be deactivated. -/
def root_always_active
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  s.agent_active s.root_agent

/-- **parent_implies_active**: the parent relation is consistent with active status. -/
def parent_implies_active
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (C P : AgentId), s.agent_parent C P → s.agent_active C

/-- **single_parent**: an active agent has at most one parent. -/
def single_parent
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (C P1 P2 : AgentId),
    s.agent_parent C P1 → s.agent_parent C P2 → s.agent_active C → P1 = P2

/-- **no_self_parent**: no agent is its own parent. -/
def no_self_parent
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (A : AgentId), ¬ s.agent_parent A A

/-- **root_no_parent**: root has no parent. -/
def root_no_parent
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (P : AgentId), ¬ s.agent_parent s.root_agent P

/-- **capability_subsumption**: an active child can hold only capabilities held by its active
parent. The active-parent premise excludes revoked parents whose capabilities were removed. -/
def capability_subsumption
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (C P : AgentId), s.agent_parent C P → s.agent_active C → s.agent_active P →
    ∀ (Cap : CapKind), s.agent_cap C Cap → s.agent_cap P Cap

/-- **root_all_caps**: root holds every capability. -/
def root_all_caps
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (C : CapKind), s.agent_cap s.root_agent C

/-- **revocation_clean**: inactive agents have no labels, pending records, open challenges,
or crossing grants. Consumed identifier and attestation histories are not agent-owned state. -/
def revocation_clean
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (A : AgentId), ¬ s.agent_active A →
    (∀ (L : ConfLevel), ¬ s.taint_levels A L)
    ∧ (∀ (Li : IntegLevel), ¬ s.integ_levels A Li)
    ∧ (∀ (I : InvocationId)
        (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
        s.pending I = some J → J.agent ≠ A)
    ∧ (∀ (I : InvocationId)
        (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
          ContentHash),
        s.challenges I = some sc → sc.agent ≠ A)
    ∧ (∀ (D : AssignmentDigest), s.crossing_grants A D = none)

/-- **pending_active**: pending invocations only exist for active agents. -/
def pending_active
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J → s.agent_active J.agent

/-! ## Pending and gate invariants -/

/-- **pending_unique**: each invocation key maps to at most one pending record. -/
def pending_unique
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (J1 J2 : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J1 → s.pending I = some J2 → J1 = J2

/-- **pending_registered**: every pending invocation's frozen identity is a registered
tool. -/
def pending_registered
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J → s.tool_registered J.policy.tool

/-- **root_no_pending**: root never invokes tools. -/
def root_no_pending
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J → J.agent ≠ s.root_agent

/-- **pending_ids_consumed**: every pending invocation identifier is in the consumed history. -/
def pending_ids_consumed
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J → s.consumed_ids I

/-- **pending_egress_attested**: narrowing and coverage hold for every pending record. -/
def pending_egress_attested
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J →
      (∀ (E : EgressKind), J.egress E → J.policy.declared_egress E)
      ∧ ((∃ (E : EgressKind), J.policy.declared_egress E) → (∃ (E : EgressKind), J.egress E))

/-- **pending_snapshot_coherent**: every pending snapshot has its inspect floor at or below its allow floor. -/
def pending_snapshot_coherent
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J → le_integ J.policy.integ_inspect J.policy.integ_floor

/-- **default_deny**: every contained pending invocation was authorized and its agent holds
every required capability. -/
def default_deny
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J → contained J →
      J.authorized ∧ (∀ (C : CapKind), J.policy.required_caps C → s.agent_cap J.agent C)

/-- **flow_confinement**: every held taint level of a contained invocation owner is allowed
on its egress, or is in the inspect band with that invocation vouched. -/
def flow_confinement
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (L : ConfLevel) (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (E : EgressKind),
    s.taint_levels J.agent L → s.pending I = some J → contained J → J.egress E →
      s.flow_allows L E ∨ (s.flow_inspects L E ∧ vouched J)

/-- **flow_confinement_weak**: every held taint level of a contained invocation owner is in
its egress allow or inspect band, independent of attestation availability. -/
def flow_confinement_weak
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (L : ConfLevel) (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (E : EgressKind),
    s.taint_levels J.agent L → s.pending I = some J → contained J → J.egress E →
      s.flow_allows L E ∨ s.flow_inspects L E

/-- **integrity_confinement**: every held integrity level of a contained invocation owner
clears its frozen floor, or is in its inspect band with that invocation vouched. -/
def integrity_confinement
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (L : IntegLevel) (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.integ_levels J.agent L → s.pending I = some J → contained J →
      integ_allows L J.policy ∨ (integ_inspects L J.policy ∧ vouched J)

/-- **integrity_confinement_weak**: the oracle-independent variant. -/
def integrity_confinement_weak
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (L : IntegLevel) (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.integ_levels J.agent L → s.pending I = some J → contained J →
      integ_allows L J.policy ∨ integ_inspects L J.policy

/-- **clearance_confinement**: every contained speculative taint level of a contained
invocation owner clears that invocation's frozen confidentiality ceiling. -/
def clearance_confinement
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (L : ConfLevel) (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J → contained J → speculative_taint_contained s J.agent L →
      clearance_admits L J.policy

/-! ## Pairwise invariants -/

/-- **pending_flow_compat**: two contained records of one agent are compatible when the first
record's output is allowed on the second record's egress, or the second record is vouched in the
inspect band. -/
def pending_flow_compat
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I1 I2 : InvocationId)
    (J1 J2 : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (E : EgressKind),
    s.pending I1 = some J1 → s.pending I2 = some J2 → J1.agent = J2.agent →
    contained J1 → contained J2 → J2.egress E →
      s.flow_allows J1.policy.output_conf E
      ∨ (s.flow_inspects J1.policy.output_conf E ∧ vouched J2)

/-- **pending_integ_compat**: two contained records of one agent are compatible when the first
record's output integrity clears the second record's floor, or the second record is vouched in the
inspect band. -/
def pending_integ_compat
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I1 I2 : InvocationId)
    (J1 J2 : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I1 = some J1 → s.pending I2 = some J2 → J1.agent = J2.agent →
    contained J1 → contained J2 →
      integ_allows J1.policy.output_integ J2.policy
      ∨ (integ_inspects J1.policy.output_integ J2.policy ∧ vouched J2)

/-! ## Evidence invariants -/

/-- **challenge_scoped**: every open challenge has an unused pending slot, a consumed invocation
identifier, an active non-root owner, a registered tool, coherent floors, and valid egress scope. -/
def challenge_scoped
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
      ContentHash),
    s.challenges I = some sc →
      s.pending I = none
      ∧ s.consumed_ids I
      ∧ s.agent_active sc.agent
      ∧ sc.agent ≠ s.root_agent
      ∧ s.tool_registered sc.policy.tool
      ∧ le_integ sc.policy.integ_inspect sc.policy.integ_floor
      ∧ (∀ (E : EgressKind), sc.egress E → sc.policy.declared_egress E)
      ∧ ((∃ (E : EgressKind), sc.policy.declared_egress E) → (∃ (E : EgressKind), sc.egress E))

/-- **challenges_enforce_only**: every open challenge exists only in enforce mode. -/
def challenges_enforce_only
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
      ContentHash),
    s.challenges I = some sc → s.mode = Mode.enforce

/-- **challenge_unique**: each invocation key maps to at most one challenge scope. -/
def challenge_unique
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (sc1 sc2 : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
      ContentHash),
    s.challenges I = some sc1 → s.challenges I = some sc2 → sc1 = sc2

/-- **inspected_evidence_consumed**: each inspected admission records its attestation as consumed. -/
def inspected_evidence_consumed
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (att : AttestationId),
    s.pending I = some J → J.admission = Admission.inspected att →
      s.consumed_attestations att

/-- **bypass_mode_sound**: non-contained records and bypassed admissions occur only in
monitor mode. -/
def bypass_mode_sound
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J →
      (¬ contained J → s.mode = Mode.monitor)
      ∧ (J.admission = Admission.bypassed → s.mode = Mode.monitor)

/-- **quarantine_pending**: a quarantined record remains present in `pending` at its invocation
key, so it participates in the same quantifiers as other pending records. -/
def quarantine_pending
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J → J.quarantined →
      ∃ (K : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
        s.pending I = some K ∧ K.quarantined

/-! ## Crossing invariants -/

/-- **grant_bounded**: every crossing grant has no more remaining uses than provisioned uses. -/
def grant_bounded
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (A : AgentId) (D : AssignmentDigest) (g : CrossingGrant),
    s.crossing_grants A D = some g → g.remaining ≤ g.provisioned

/-- **grant_active**: grants only for active agents (revocation destroys them). -/
def grant_active
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (A : AgentId) (D : AssignmentDigest) (g : CrossingGrant),
    s.crossing_grants A D = some g → s.agent_active A

/-- **grant_pinned**: the grant map is functional per (agent, digest). Encoding-trivial;
the composite-key `VecMap` refinement must preserve it. -/
def grant_pinned
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (A : AgentId) (D : AssignmentDigest) (g1 g2 : CrossingGrant),
    s.crossing_grants A D = some g1 → s.crossing_grants A D = some g2 → g1 = g2

end Tzimtzum
