/-!
# TzimtzumV4 state

This module defines the protocol sorts, security lattices, state record, derived gates, and
initial-state predicate. Actions update only kernel state. Policy snapshots, attestations,
contract data, and source provenance are action inputs whose scope, bounds, and one-use
consumption are checked by action guards.

Pending records retain the exact policy used for admission. A record is `contained` exactly
when its disposition is `permitted`; monitor-bypassed records still constrain future decisions
but do not assert that their gates passed. Invocation, attestation, and crossing identifiers are
never removed from their corresponding consumed histories.
-/

namespace Tzimtzum

/-! ## Concrete lattices

`«public»` and `«internal»` are guillemet-escaped because they are Lean 4 keywords. -/

inductive ConfLevel where
  | «public» | «internal» | sensitive | restricted
  deriving DecidableEq, Repr

/-- Numeric rank for the confidentiality total order: public < internal < sensitive < restricted. -/
def confRank : ConfLevel → Nat
  | .«public»    => 0
  | .«internal»  => 1
  | .sensitive   => 2
  | .restricted  => 3

/-- The decidable confidentiality order induced by `confRank`. -/
def le_conf (a b : ConfLevel) : Prop := confRank a ≤ confRank b

instance (a b : ConfLevel) : Decidable (le_conf a b) := inferInstanceAs (Decidable (_ ≤ _))

/-- Integrity is the dual taint dimension: it FALLS as an agent ingests untrusted content,
where confidentiality taint RISES as an agent reads secret data. -/
inductive IntegLevel where
  | untrusted | standard | trusted | attested
  deriving DecidableEq, Repr

/-- Numeric rank for the integrity total order: untrusted < standard < trusted < attested. -/
def integRank : IntegLevel → Nat
  | .untrusted => 0
  | .standard  => 1
  | .trusted   => 2
  | .attested  => 3

/-- The integrity total order (mirrors `le_conf`). -/
def le_integ (a b : IntegLevel) : Prop := integRank a ≤ integRank b

instance (a b : IntegLevel) : Decidable (le_integ a b) := inferInstanceAs (Decidable (_ ≤ _))

/-! ## Verdicts, dispositions, and mode

`Verdict` classifies admission checks. `Disposition` determines whether a pending record is
permitted, blocked, or admitted only in monitor mode. `Mode` is immutable state that controls
whether failed holds reject an action or cause demotion. -/

inductive Verdict where
  | allow | inspection_required | deny
  deriving DecidableEq, Repr

inductive Disposition where
  | permitted | blocked | monitor_bypassed
  deriving DecidableEq, Repr

inductive Mode where
  | enforce | monitor
  deriving DecidableEq, Repr

inductive Outcome where
  | success | failure | ambiguous
  deriving DecidableEq, Repr

inductive Fallback where
  | fail | release_unendorsed
  deriving DecidableEq, Repr

/-- How a pending invocation was admitted; *evidence*, never authority. -/
inductive Admission (AttestationId : Type) where
  | plain
  | inspected (att : AttestationId)
  | bypassed
  deriving DecidableEq

/-- A crossing grant records remaining uses and the bound set by `grant_crossing`.
`grant_bounded` requires `remaining ≤ provisioned`. -/
structure CrossingGrant where
  remaining   : Nat
  provisioned : Nat
  deriving DecidableEq, Repr

/-! ## Frozen policy snapshot

A pending record stores the exact action policy used at admission. Its gates and settlement
therefore use stable required capabilities, floors, output provenance, egress set, and digest. -/

structure ActionPolicySnapshot (ToolId CapKind EgressKind PolicyDigest : Type) where
  /-- Exact registered tool identity bound to this snapshot. -/
  tool            : ToolId
  required_caps   : CapKind → Prop
  /-- Maximum confidentiality level the invoker may hold. -/
  conf_clearance  : ConfLevel
  /-- ALLOW floor. -/
  integ_floor     : IntegLevel
  /-- Inspect-band floor. A floor above the inspect floor is an empty band; coherent by
  construction; the reverse is incoherent and rejected at the boundary. -/
  integ_inspect   : IntegLevel
  /-- Confidentiality provenance of ordinary output. -/
  output_conf     : ConfLevel
  /-- Integrity provenance of ordinary output. -/
  output_integ    : IntegLevel
  /-- Declared egress set; the invocation egress set must narrow to this set. -/
  declared_egress : EgressKind → Prop
  /-- Binds inspection-attestation scope. -/
  policy_digest   : PolicyDigest

/-! ## Pending invocations and challenges -/

structure PendingInvocation
    (AgentId ToolId CapKind EgressKind AttestationId PolicyDigest : Type) where
  agent       : AgentId
  policy      : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest
  /-- The attested per-invocation egress set. -/
  egress      : EgressKind → Prop
  admission   : Admission AttestationId
  /-- `permitted` or `monitor_bypassed`; `blocked` never pends. -/
  disposition : Disposition
  /-- Authorizer verdict recorded at admission. -/
  authorized  : Prop
  /-- Set by `settle_invocation ambiguous`. A quarantined invocation is not closed, absorbs
  nothing yet, and keeps participating in every speculative and pairwise quantifier: a
  dispatched-but-unconfirmed destructive effect may have happened, so it must keep gating. -/
  quarantined : Prop

/-- An inspection challenge scope binds the invocation key, agent, frozen policy, egress set,
arguments hash, and authorizer verdict. A positive, scope-matching resolution creates the
pending record. The kernel has no clock; resolver freshness is external to this state. -/
structure ChallengeScope
    (AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash : Type) where
  /-- Challenge identifier used for attestation attribution; the invocation is the map key. -/
  challenge  : ChallengeId
  agent      : AgentId
  policy     : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest
  egress     : EgressKind → Prop
  args_hash  : ContentHash
  authorized : Prop

/-! ## The state structure -/

structure St (AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
    CrossingId AssignmentDigest PolicyDigest ContentHash : Type) where
 -- Agent tree and label state.
  agent_active          : AgentId → Prop
  agent_parent          : AgentId → AgentId → Prop
  agent_cap             : AgentId → CapKind → Prop
  /-- Levels ingested. Effective taint is the MAX of the set; EMPTY SET = UNTAINTED. -/
  taint_levels          : AgentId → ConfLevel → Prop
  /-- Levels ingested. Effective integrity is the MIN of the set; EMPTY SET = FULLY
  TRUSTED (dual of the taint reading). Every gate quantifies ∀ over the set. -/
  integ_levels          : AgentId → IntegLevel → Prop
 -- Mutable protocol state.
  pending               : InvocationId →
    Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
  /-- Challenges are keyed by invocation, so each invocation has at most one open scope. -/
  challenges            : InvocationId →
    Option (ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
      ContentHash)
  /-- Invocation identifiers consumed at admission and never removed. -/
  consumed_ids          : InvocationId → Prop
  /-- Attestation identifiers consumed by inspected admission, resolution, or endorsement. -/
  consumed_attestations : AttestationId → Prop
  /-- Crossing identifiers consumed by `cross_output` and never removed. -/
  consumed_crossings    : CrossingId → Prop
  /-- Remaining crossing uses, keyed by (holder agent, exact assignment digest).
  Provisioned only by `grant_crossing` (root-only), decremented by exactly one on each
  conforming `cross_output`, destroyed for the agent by `revoke`/`cascade_revoke`. -/
  crossing_grants       : AgentId → AssignmentDigest → Option CrossingGrant
  tool_registered       : ToolId → Prop
 -- Immutable policy background.
  egress_allow_ceiling   : EgressKind → Option ConfLevel
  egress_inspect_ceiling : EgressKind → Option ConfLevel
  /-- Governed enforcement mode. Immutable background in the single-tenant model: the
  adapter can never choose it. -/
  mode                   : Mode
 -- Distinguished agent.
  root_agent             : AgentId

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-! ## Derived gates

Flow, integrity, and clearance checks are separate predicates. `ceilingAdmits` remains
irreducible so preservation proofs can treat flow gates as atomic propositions. -/

/-- Ceiling-band membership: `l` is at or below the ceiling `f e`; `none` = no level
passes (strict default-deny, including Public). Deliberately NOT a simp lemma and
`@[irreducible]`: the discharge cascades keep the flow gates ATOMIC, so frame equations
close by congruence instead of unfolding the existential at every gate site. -/
def ceilingAdmits (f : EgressKind → Option ConfLevel) (l : ConfLevel) (e : EgressKind) : Prop :=
  ∃ c, f e = some c ∧ le_conf l c

attribute [irreducible] ceilingAdmits

/-- Derived flow-ALLOW relation: a level flows freely iff it is at or below the egress's
allow ceiling. -/
@[simp] def St.flow_allows
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (l : ConfLevel) (e : EgressKind) : Prop :=
  ceilingAdmits s.egress_allow_ceiling l e

/-- Derived flow-INSPECT relation: content-gated band, levels at or below the inspect
ceiling. An inspect ceiling below the allow ceiling is an empty inspect band; coherent. -/
@[simp] def St.flow_inspects
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (l : ConfLevel) (e : EgressKind) : Prop :=
  ceilingAdmits s.egress_inspect_ceiling l e

/-- Integrity allow check against a frozen policy floor. -/
@[simp] def integ_allows (l : IntegLevel)
    (p : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) : Prop :=
  le_integ p.integ_floor l

/-- Integrity INSPECT against a frozen snapshot (dual of `St.flow_inspects`). -/
@[simp] def integ_inspects (l : IntegLevel)
    (p : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) : Prop :=
  le_integ p.integ_inspect l

/-- Clearance admission: the agent's taint clears the snapshot's per-target ceiling.
Two-valued; there is no inspect band on clearance. Transparent, like the integrity atoms. -/
@[simp] def clearance_admits (l : ConfLevel)
    (p : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) : Prop :=
  le_conf l p.conf_clearance

/-! ## Record-level predicates -/

/-- A record is vouched exactly when its admission stores an inspection attestation. -/
def vouched
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest) : Prop :=
  ∃ att, J.admission = Admission.inspected att

/-- A pending record is contained exactly when it is `permitted`.
Monitor-bypassed records still affect speculative state but do not claim successful gating. -/
def contained
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest) : Prop :=
  J.disposition = Disposition.permitted

/-! ## Speculative (worst-case) labels

Re-read over pending records, including quarantined **and** monitor-bypassed ones. -/

/-- Held taint ∪ the frozen `output_conf` of every pending record of the agent. -/
def speculative_taint
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (l : ConfLevel) : Prop :=
  s.taint_levels a l ∨ (∃ I J, s.pending I = some J ∧ J.agent = a ∧ J.policy.output_conf = l)

/-- Held integrity ∪ the frozen `output_integ` of every pending record of the agent. -/
def speculative_integ
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (l : IntegLevel) : Prop :=
  s.integ_levels a l ∨ (∃ I J, s.pending I = some J ∧ J.agent = a ∧ J.policy.output_integ = l)

/-- Held taint plus output confidentiality of contained pending records only.
Clearance confinement uses this filtered set, while admission checks use all pending records. -/
def speculative_taint_contained
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (l : ConfLevel) : Prop :=
  s.taint_levels a l
  ∨ (∃ I J, s.pending I = some J ∧ J.agent = a ∧ contained J ∧ J.policy.output_conf = l)

/-! ## Initial states -/

/-- Only `root_agent` is active and holds every capability; no labels, no pending
invocations, no challenges, no consumed history, no grants, no registered tools. `mode` and
the egress ceilings are governed background and are therefore unconstrained here; the Kav
frame rule holds them constant over any trace. -/
def initial
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  (∀ (A : AgentId), s.agent_active A ↔ A = s.root_agent) ∧
  (∀ (A B : AgentId), ¬ s.agent_parent A B) ∧
  (∀ (A : AgentId) (C : CapKind), s.agent_cap A C ↔ A = s.root_agent) ∧
  (∀ (A : AgentId) (L : ConfLevel), ¬ s.taint_levels A L) ∧
  (∀ (A : AgentId) (L : IntegLevel), ¬ s.integ_levels A L) ∧
  (∀ (I : InvocationId), s.pending I = none) ∧
  (∀ (I : InvocationId), s.challenges I = none) ∧
  (∀ (I : InvocationId), ¬ s.consumed_ids I) ∧
  (∀ (Att : AttestationId), ¬ s.consumed_attestations Att) ∧
  (∀ (X : CrossingId), ¬ s.consumed_crossings X) ∧
  (∀ (A : AgentId) (D : AssignmentDigest), s.crossing_grants A D = none) ∧
  (∀ (T : ToolId), ¬ s.tool_registered T)

end Tzimtzum
