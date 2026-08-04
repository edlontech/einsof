import Tzimtzum.Actions.Ingest

/-!
# TzimtzumV4 — `cross_output`

The single atomic boundary crossing ([[2026-07-24-tzimtzum-v4/architecture|architecture]]
§6.5): the integrity dual of declassification, the only transition that may produce output
more trusted than its source, and the only sanctioned downward confidentiality step. It
binds contract, assignment, evidence, grant and release in one decision — there is no
endorse-then-fallback sequence for a crash to split. Definitions only — proofs are Task 10.

## Inputs

All frozen at the command and bundled into one `CrossInput` record (its Rust image is a
request struct): the exact contract revision (descriptor hash + declared `Fallback`), the
exact assignment (`t_integ`, optional declassification bound `t_conf`, digest), conformance
evidence or its absence, the fresh crossing id, and the released label pair (E19: computed
outside, bounded by guard). The record *is* the authenticated revision — a missing or
mismatched revision/assignment/pin never reaches the kernel (there is then no authenticated
fallback authority either), which is §6.5's "missing contract authority always fails",
realised as a boundary rejection.

## The trichotomy

`branch` is an action parameter (E8/E19) and `endorsedOK` is the **transparent**
branch-selection predicate (§12.1): its positive and negated forms partition the trichotomy
totally (`cross_branch_total`), so each Rust `if/else` arm refines exactly one spec branch.

1. **endorsed** — scope-exact positive unconsumed conformance evidence + a grant with uses
   remaining. Consumes the attestation, decrements the grant, releases at
   `(released_conf, released_integ)` with `released_integ ≤ t_integ` and, if declassifying,
   `released_conf` within `t_conf`; without a declassifying contract the released
   confidentiality must dominate the source's held taint (no silent downward step). The
   receiver takes the min per dimension by *inserting* into its label sets; the source is
   framed — endorsement never cleans anybody.
2. **unendorsed** — branch 1 unavailable and the contract declares `release_unendorsed`.
   Ordinary source-level release: the receiver's sets absorb the source's sets, exactly an
   `ingest` from agent state (E21's domination is the identity here — the labels *are* the
   source's). No consumption, no decrement, no endorsement.
3. **fail** — branch 1 unavailable and the declared fallback is `fail`. No release, no
   label change; the crossing id is still consumed (freshness is never given back).

## The receiver is protected by the ingest holds (E18/E20 carried)

§6.5 is silent about the receiver's own pending permits, but both release branches degrade
the receiver's labels exactly as `ingest` does, with the same consequence: a live permit of
the *receiver* could be broken mid-flight. So both release branches carry the three ingest
holds on the receiver (for the released pair, or for every source level), `dispo` selects
the enforcement axis per E19, and a monitor-mode bypass demotes the receiver's permits
(E18). `fail` moves no labels and needs no holds.
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

/-- The frozen inputs of one crossing (see module docs). -/
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
  /-- Assignment digest — the grant key. -/
  assignment     : AssignmentDigest
  evidence       : Option (ConformanceAttestation AgentId AttestationId AssignmentDigest
    ContentHash)
  released_conf  : ConfLevel
  released_integ : IntegLevel

/-- The transparent branch-selection predicate (§12.1): branch 1 is available iff the
evidence is present, positive, unconsumed and scope-exact, AND the receiver holds a grant
for the exact assignment with uses remaining. -/
def endorsedOK
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash) : Prop :=
  (∃ e, q.evidence = some e ∧ e.positive ∧ ¬ s.consumed_attestations e.id
    ∧ e.output = q.output_hash ∧ e.src = q.src ∧ e.rcv = q.rcv
    ∧ e.descriptor = q.descriptor ∧ e.assignment = q.assignment)
  ∧ (∃ g, s.crossing_grants q.rcv q.assignment = some g ∧ 0 < g.remaining)

/-- The receiver-side holds, per branch (module docs). `fail` moves no labels. -/
def crossHolds
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (q : CrossInput AgentId AttestationId CrossingId AssignmentDigest ContentHash)
    (branch : CrossBranch) : Prop :=
  (branch = CrossBranch.endorsed → ingestHolds s q.rcv q.released_conf q.released_integ)
  ∧ (branch = CrossBranch.unendorsed →
      (∀ (L : ConfLevel), s.taint_levels q.src L →
        ingestConfHold s q.rcv L ∧ ingestClearHold s q.rcv L)
      ∧ (∀ (Li : IntegLevel), s.integ_levels q.src Li → ingestIntegHold s q.rcv Li))

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
  -- The carried V3 `return_endorsed` guard: a source with in-flight invocations has
  -- undetermined worst-case labels.
  require ∀ (I : InvocationId)
      (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
      s.pending I = some J → J.agent ≠ q.src
  -- Crossing-id freshness (E16); consumed on every arm, never returned.
  require ¬ s.consumed_crossings q.crossing
  -- Branch selection: a total complementary partition over (endorsedOK, declared fallback).
  require branch = CrossBranch.endorsed → endorsedOK s q
  require branch = CrossBranch.unendorsed →
    ¬ endorsedOK s q ∧ q.fallback = Fallback.release_unendorsed
  require branch = CrossBranch.fail → ¬ endorsedOK s q ∧ q.fallback = Fallback.fail
  -- Release bounds (T-6): endorsement bounded by the exact assignment; no downward
  -- confidentiality step without a declassifying contract.
  require branch = CrossBranch.endorsed → le_integ q.released_integ q.t_integ
  require branch = CrossBranch.endorsed →
    ∀ (c : ConfLevel), q.t_conf = some c → le_conf q.released_conf c
  require branch = CrossBranch.endorsed → q.t_conf = none →
    ∀ (L : ConfLevel), s.taint_levels q.src L → le_conf L q.released_conf
  -- Receiver-side enforcement (E18/E19/E20).
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

/-! ## Non-vacuity (E12) -/

open Classical in
/-- The trichotomy is total: some branch always satisfies the selection guards. Mutual
exclusivity is by construction — `endorsedOK` vs `¬ endorsedOK`, and the two fallback
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
one branch fires per invocation (the acceptance criterion, proved rather than asserted). -/
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
the mode is `monitor` — the same shape as `ingest_disposition_total`. -/
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
