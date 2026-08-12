import Tzimtzum.Updates
import Kav.Action

/-!
# TzimtzumV4 `settle_invocation`

Settlement closes a pending record on `success` or `failure` and adds its frozen output provenance
to the owner's labels. `ambiguous` instead marks the record quarantined. A quarantined record can
be closed only by consuming a fresh resolution attestation scoped to that invocation and outcome.
Settling a non-contained record demotes the owner's remaining pending records.
-/

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-- A quarantine-resolution attestation: an *input*, not state. The kernel checks its scope
and its one-use consumption; issuer truth is a named external seam, and issuer attribution
is event-side (which is why there is no issuer field and no `IssuerId` sort in V4). -/
structure ResolutionAttestation (InvocationId AttestationId : Type) where
  id      : AttestationId
  /-- Scope: the exact invocation this resolves. -/
  inv     : InvocationId
  /-- Scope: the declared resolution outcome. -/
  outcome : Outcome

/-! `settle_invocation (inv, outcome)` with the frozen provenance pair `(clvl, ilvl)` pinned
to the record's snapshot by guard, and an optional resolution attestation.

`att = none` is the ordinary path; `att = some r` is the resolution arm. The guards make the
two mutually exclusive: a quarantined record *requires* an attestation, a non-quarantined
one *forbids* it, so no settlement can burn evidence it did not need. -/

open Classical in
kav_action settle_invocation (inv : InvocationId) (a : AgentId) (dispo : Disposition)
    (outcome : Outcome) (clvl : ConfLevel) (ilvl : IntegLevel)
    (att : Option (ResolutionAttestation InvocationId AttestationId)) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require pending_exists : ∃ J, s.pending inv = some J
  require active : s.agent_active a
  require not_blocked : dispo ≠ Disposition.blocked
 -- The owning agent, the record's disposition, and the absorbed pair are all pinned to the
 -- record by guard: each is an input, none is a free choice, and the absorbed pair is
 -- the FROZEN provenance rather than live policy.
  require record_pinned : ∀ (J : PendingInvocation AgentId ToolId CapKind EgressKind
      AttestationId PolicyDigest), s.pending inv = some J →
    a = J.agent ∧ dispo = J.disposition
    ∧ clvl = J.policy.output_conf ∧ ilvl = J.policy.output_integ
 -- Quarantined: only the attested resolution arm, and it may not re-declare `ambiguous`.
  require quarantined_attested : ∀ (J : PendingInvocation AgentId ToolId CapKind EgressKind
      AttestationId PolicyDigest), s.pending inv = some J → J.quarantined →
    outcome ≠ Outcome.ambiguous
    ∧ ∃ r, att = some r ∧ r.inv = inv ∧ r.outcome = outcome
        ∧ ¬ s.consumed_attestations r.id
 -- Not quarantined: no attestation is consumed.
  require unquarantined_plain : ∀ (J : PendingInvocation AgentId ToolId CapKind EgressKind
      AttestationId PolicyDigest), s.pending inv = some J → ¬ J.quarantined → att = none
  pending :=
    if dispo = Disposition.permitted then settleAt s.pending inv outcome
    else demoteAllOf (settleAt s.pending inv outcome) a
  taint_levels := fun A L =>
    s.taint_levels A L ∨ (outcome ≠ Outcome.ambiguous ∧ A = a ∧ L = clvl)
  integ_levels := fun A L =>
    s.integ_levels A L ∨ (outcome ≠ Outcome.ambiguous ∧ A = a ∧ L = ilvl)
  consumed_attestations := fun X =>
    s.consumed_attestations X ∨ (∃ r, att = some r ∧ X = r.id)

end Tzimtzum
