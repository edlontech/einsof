import Tzimtzum.Updates
import Kav.Action

/-!
# TzimtzumV4 — `settle_invocation`

Closing (or quarantining) a pending invocation
([[2026-07-24-tzimtzum-v4/architecture|architecture]] §6.4). Definitions only.

Three arms in one action, because E5 makes quarantine resolution an *arm* of this command
rather than a thirteenth action:

1. **`success` / `failure`** — remove the pending record and absorb the *frozen* ordinary
   output provenance in **both** dimensions (E3): `output_conf` into taint, `output_integ`
   into integrity. From the snapshot, never from live policy.
2. **`ambiguous`** — set the quarantine flag. The invocation is not closed and absorbs
   nothing yet, and it keeps participating in every speculative and pairwise quantifier: a
   dispatched-but-unconfirmed destructive effect may have happened, so it must keep gating.
3. **Attested resolution** (quarantined records only) — consume a one-use resolution
   attestation scoped to this invocation and the declared outcome, then settle as declared.
   A quarantined invocation can never become an ordinary success without it.

## Settlement absorbs freely — no gate

This is the assessment's decision and it is a theorem obligation (T-8), not an assumption:
settle-time holding is already excluded at *begin* time by the pairwise gates, so a
settlement can never invalidate another pending invocation's permit. `pending_flow_compat`
and `pending_integ_compat` are exactly what carries it.

## Settling a non-contained record demotes the rest (E18, carried from `ingest`)

`speculative_taint_contained` deliberately keeps a `monitor_bypassed` record's frozen
provenance out of the contained speculative set (E10) — but settlement inserts exactly that
provenance into `taint_levels`/`integ_levels`, where nothing filters it. Settling a bypassed
record would therefore launder its labels into the contained world and falsify
`clearance_confinement`, `flow_confinement` and `integrity_confinement` for the agent's
*other*, genuinely contained permits. So a settlement of a non-contained record demotes the
agent's remaining permits, exactly as a bypassed ingestion does.

## Two deliberate simplifications, both fail-closed

* §6.4 allows a resolution that declares the effect *did not happen* to close without
  absorption. Here every resolved outcome absorbs. Absorbing provenance that never
  materialised only raises taint and lowers integrity, which is conservative, and it keeps
  the arm count down. If the product later needs the non-absorbing close, it is a new
  `Outcome` constructor plus one branch, not a redesign.
* The absorbed levels are action *parameters* pinned to the frozen snapshot by a guard,
  rather than being projected out of the record inside the update expression (the E8
  discipline). This keeps the update a plain disjunction with no existential and no `ite`
  over a large `Prop`.
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
  require ∃ J, s.pending inv = some J
  require s.agent_active a
  require dispo ≠ Disposition.blocked
  -- The owning agent, the record's disposition, and the absorbed pair are all pinned to the
  -- record by guard (E19): each is an input, none is a free choice, and the absorbed pair is
  -- the FROZEN provenance rather than live policy.
  require ∀ (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId
      PolicyDigest), s.pending inv = some J →
    a = J.agent ∧ dispo = J.disposition
    ∧ clvl = J.policy.output_conf ∧ ilvl = J.policy.output_integ
  -- Quarantined: only the attested resolution arm, and it may not re-declare `ambiguous`.
  require ∀ (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId
      PolicyDigest), s.pending inv = some J → J.quarantined →
    outcome ≠ Outcome.ambiguous
    ∧ ∃ r, att = some r ∧ r.inv = inv ∧ r.outcome = outcome
        ∧ ¬ s.consumed_attestations r.id
  -- Not quarantined: no attestation is consumed.
  require ∀ (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId
      PolicyDigest), s.pending inv = some J → ¬ J.quarantined → att = none
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
