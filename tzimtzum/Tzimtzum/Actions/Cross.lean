import Tzimtzum.Actions.Ingest

/-!
# TzimtzumV4 `cross_output`

`cross_output` performs one atomic boundary crossing. An endorsed branch requires fresh,
scope-matching positive evidence and a remaining receiver grant, then consumes the evidence and
decrements the grant. If endorsement is unavailable, the frozen fallback selects either an
unendorsed source-label release or no release. Release branches satisfy receiver ingestion holds
or, in monitor mode, demote the receiver's pending records.
-/

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-- A conformance attestation: an *input*, not state. Scope is (output hash, source,
receiver, contract descriptor, assignment digest); the kernel checks scope and one-use
consumption, issuer truth is the named external seam. -/
structure ConformanceAttestation (AgentId AttestationId AssignmentDigest ContentHash : Type)
    where
  id         : AttestationId
  output     : ContentHash
  src        : AgentId
  rcv        : AgentId
  descriptor : ContentHash
  assignment : AssignmentDigest
  positive   : Prop

/-- Which arm of the trichotomy fired. -/
inductive CrossBranch where
  | endorsed | unendorsed | fail
  deriving DecidableEq, Repr

/-- The source, receiver, evidence, assignment, fallback, and released labels of one crossing. -/
structure CrossInput (AgentId AttestationId CrossingId AssignmentDigest ContentHash : Type)
    where
  src            : AgentId
  rcv            : AgentId
  crossing       : CrossingId
  output_hash    : ContentHash
  /-- Contract revision: descriptor hash. -/
  descriptor     : ContentHash
  /-- Contract revision: declared fallback. -/
  fallback       : Fallback
  /-- Assignment: max target integrity. -/
  t_integ        : IntegLevel
  /-- Assignment: most-public target confidentiality; `some` iff the contract declassifies. -/
  t_conf         : Option ConfLevel
  /-- Assignment digest; the grant key. -/
  assignment     : AssignmentDigest
  evidence       : Option (ConformanceAttestation AgentId AttestationId AssignmentDigest
    ContentHash)
  released_conf  : ConfLevel
  released_integ : IntegLevel

/-- `endorsedOK` holds exactly when evidence is positive, fresh, scope-matching, and paired
with a receiver grant for the exact assignment that has a remaining use. -/
structure endorsedOK
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash) :
    Prop where
  /-- Fresh, positive, exactly-scoped crossing evidence. -/
  evidence : ∃ e, q.evidence = some e ∧ e.positive ∧ ¬ s.consumed_attestations e.id
    ∧ e.output = q.output_hash ∧ e.src = q.src ∧ e.rcv = q.rcv
    ∧ e.descriptor = q.descriptor ∧ e.assignment = q.assignment
  /-- A live receiver grant with remaining budget. -/
  grant : ∃ g, s.crossing_grants q.rcv q.assignment = some g ∧ 0 < g.remaining

theorem endorsedOK_iff
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash) :
    endorsedOK s q ↔
      ((∃ e, q.evidence = some e ∧ e.positive ∧ ¬ s.consumed_attestations e.id
        ∧ e.output = q.output_hash ∧ e.src = q.src ∧ e.rcv = q.rcv
        ∧ e.descriptor = q.descriptor ∧ e.assignment = q.assignment)
      ∧ (∃ g, s.crossing_grants q.rcv q.assignment = some g ∧ 0 < g.remaining)) :=
  ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩⟩

/-- Holds that protect receiver pending records for each label-releasing branch. -/
structure crossHolds
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) : Prop where
  endorsed : branch = CrossBranch.endorsed →
    ingestHolds s q.rcv q.released_conf q.released_integ
  unendorsed : branch = CrossBranch.unendorsed →
    (∀ (L : ConfLevel), s.taint_levels q.src L →
      ingestConfHold s q.rcv L ∧ ingestClearHold s q.rcv L)
    ∧ (∀ (Li : IntegLevel), s.integ_levels q.src Li → ingestIntegHold s q.rcv Li)

theorem crossHolds_iff
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) :
    crossHolds s q branch ↔
      ((branch = CrossBranch.endorsed → ingestHolds s q.rcv q.released_conf q.released_integ)
      ∧ (branch = CrossBranch.unendorsed →
          (∀ (L : ConfLevel), s.taint_levels q.src L →
            ingestConfHold s q.rcv L ∧ ingestClearHold s q.rcv L)
          ∧ (∀ (Li : IntegLevel), s.integ_levels q.src Li → ingestIntegHold s q.rcv Li))) :=
  ⟨fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩, fun ⟨h1, h2⟩ ↦ ⟨h1, h2⟩⟩

open Classical in
kav_action cross_output
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) (dispo : Disposition) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
 -- `src = rcv` is deliberately not excluded: the no-in-flight-source guard then empties
 -- the receiver's pending set, every hold is vacuous, and min-semantics keeps the label
 -- insertions monotone-safe.
  require s.agent_active q.src
  require s.agent_active q.rcv
 -- A source with pending work has speculative labels, so it cannot cross output.
  require ∀ (I : InvocationId)
      (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
      s.pending I = some J → J.agent ≠ q.src
 -- A crossing identifier is consumed exactly once, regardless of branch.
  require ¬ s.consumed_crossings q.crossing
 -- Branch selection: a total complementary partition over (endorsedOK, declared fallback).
  require branch = CrossBranch.endorsed → endorsedOK s q
  require branch = CrossBranch.unendorsed →
    ¬ endorsedOK s q ∧ q.fallback = Fallback.release_unendorsed
  require branch = CrossBranch.fail → ¬ endorsedOK s q ∧ q.fallback = Fallback.fail
 -- Endorsement obeys the frozen integrity and optional confidentiality bounds.
  require branch = CrossBranch.endorsed → le_integ q.released_integ q.t_integ
  require branch = CrossBranch.endorsed →
    ∀ (c : ConfLevel), q.t_conf = some c → le_conf q.released_conf c
  require branch = CrossBranch.endorsed → q.t_conf = none →
    ∀ (L : ConfLevel), s.taint_levels q.src L → le_conf L q.released_conf
 -- Permitted releases satisfy receiver holds; monitor bypasses demote receiver records.
  require dispo ≠ Disposition.blocked
  require dispo = Disposition.permitted → crossHolds s q branch
  require dispo = Disposition.monitor_bypassed →
    ¬ crossHolds s q branch ∧ s.mode = Mode.monitor
  taint_levels := fun A L =>
    s.taint_levels A L
    ∨ (branch = CrossBranch.endorsed ∧ A = q.rcv ∧ L = q.released_conf)
    ∨ (branch = CrossBranch.unendorsed ∧ A = q.rcv ∧ s.taint_levels q.src L)
  integ_levels := fun A L =>
    s.integ_levels A L
    ∨ (branch = CrossBranch.endorsed ∧ A = q.rcv ∧ L = q.released_integ)
    ∨ (branch = CrossBranch.unendorsed ∧ A = q.rcv ∧ s.integ_levels q.src L)
  consumed_crossings := fun X => s.consumed_crossings X ∨ X = q.crossing
  consumed_attestations := fun X =>
    s.consumed_attestations X
    ∨ (branch = CrossBranch.endorsed ∧ ∃ e, q.evidence = some e ∧ X = e.id)
  crossing_grants :=
    if branch = CrossBranch.endorsed then decrementGrantAt s.crossing_grants q.rcv q.assignment
    else s.crossing_grants
  pending :=
    if dispo = Disposition.monitor_bypassed then demoteAllOf s.pending q.rcv else s.pending

/-! ## Non-vacuity -/

open Classical in
/-- The trichotomy is total: some branch always satisfies the selection guards. Mutual
exclusivity is by construction; `endorsedOK` vs `¬ endorsedOK`, and the two fallback
values are distinct constructors. -/
theorem cross_branch_total
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash) :
    ∃ (branch : CrossBranch),
      (branch = CrossBranch.endorsed → endorsedOK s q)
      ∧ (branch = CrossBranch.unendorsed →
          ¬ endorsedOK s q ∧ q.fallback = Fallback.release_unendorsed)
      ∧ (branch = CrossBranch.fail → ¬ endorsedOK s q ∧ q.fallback = Fallback.fail) := by
  by_cases h : endorsedOK s q
  · exact ⟨CrossBranch.endorsed, fun _ => h, by simp, by simp⟩
  · cases hf : q.fallback with
    | release_unendorsed => exact ⟨CrossBranch.unendorsed, by simp, fun _ => ⟨h, rfl⟩, by simp⟩
    | fail => exact ⟨CrossBranch.fail, by simp, by simp, fun _ => ⟨h, rfl⟩⟩

/-- The three selection guards are pairwise disjoint, so with `cross_branch_total` exactly
one branch fires per invocation. -/
theorem cross_branch_exclusive
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash) :
    ¬ (endorsedOK s q ∧ (¬ endorsedOK s q ∧ q.fallback = Fallback.release_unendorsed))
    ∧ ¬ (endorsedOK s q ∧ (¬ endorsedOK s q ∧ q.fallback = Fallback.fail))
    ∧ ¬ ((¬ endorsedOK s q ∧ q.fallback = Fallback.release_unendorsed)
          ∧ (¬ endorsedOK s q ∧ q.fallback = Fallback.fail)) := by
  refine ⟨fun ⟨h, hn, _⟩ => hn h, fun ⟨h, hn, _⟩ => hn h, fun ⟨⟨_, h1⟩, ⟨_, h2⟩⟩ => ?_⟩
  rw [h1] at h2
  exact Fallback.noConfusion h2

open Classical in
/-- Some disposition always satisfies the enforcement clauses, provided the holds pass or
the mode is `monitor`; the same shape as `ingest_disposition_total`. -/
theorem cross_disposition_total
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch)
    (hmode : crossHolds s q branch ∨ s.mode = Mode.monitor) :
    ∃ (dispo : Disposition),
      dispo ≠ Disposition.blocked
      ∧ (dispo = Disposition.permitted → crossHolds s q branch)
      ∧ (dispo = Disposition.monitor_bypassed →
          ¬ crossHolds s q branch ∧ s.mode = Mode.monitor) := by
  by_cases h : crossHolds s q branch
  · exact ⟨Disposition.permitted, by simp, fun _ => h, by simp⟩
  · exact ⟨Disposition.monitor_bypassed, by simp, by simp,
      fun _ => ⟨h, hmode.resolve_left h⟩⟩

end Tzimtzum
