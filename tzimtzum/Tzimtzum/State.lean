/-!
# TzimtzumV4 — sorts, lattices, and the state structure

The V4 state space of [[2026-07-24-tzimtzum-v4/architecture|architecture]] §5. Definitions
only — no actions, no invariants, no proofs.

## What changed from V3

**Retired outright** (with every function that priced or gated them): `agent_budget`,
`budget_capacity`, `declass_weight`, `integ_weight`, `budget_saturating_credit`,
`crossing_weight`, `St.affordable`; `flow_override`, `override_used`; `agent_instruction`,
`instruction_issuer`; `tool_issuer`, `trusted_issuer`; `cap_declassify`,
`cap_credit_budget`, `cap_grant_override`. The declassification economy is replaced by
per-instance one-use evidence plus a bounded-use crossing grant (§11); issuer trust flows
through governed policy publication rather than a kernel issuer relation (§9).

**Transformed**: `in_flight` becomes `pending`, a map to a structured record carrying the
*frozen* `ActionPolicySnapshot` the decision was made against; the per-tool background
relations (`tool_cap`, `tool_egress`, `tool_conf_floor`, `tool_integ_floor`,
`tool_integ_inspect_floor`, `tool_output_integ`, `tool_output_bounded`) become fields of
that snapshot; `invocation_used` is subsumed by `pending` + `consumed_ids` (the subsumption
is proved, not assumed — T-9); the static oracle verdicts (`invocation_conforms`,
`return_conforms`, `invocation_gate_passes`) become consumable scoped attestations.

**New**: `challenges`, `consumed_ids`, `consumed_attestations`, `consumed_crossings`,
`crossing_grants`, `mode`.

**Deleted with justification** (§8's rule: deletions are written down, never silent):
`tool_output_bounded`. §2 lists it among the fields that become snapshot fields, but §5.2
omits it and nothing in §6 reads it. Its guarantee — that an endorsed release cannot exceed
a declared ceiling — is carried in V4 by `cross_output`'s frozen assignment bound (`t_integ`,
and `t_conf` for declassifying contracts), which is a per-crossing frozen *input* rather
than a per-tool background flag, and by T-6. A per-tool bound would be strictly weaker: it
could not express a per-assignment ceiling.

**Carried verbatim**: the agent tree, both label sets with their set encodings (empty taint
= untainted, **empty integrity = fully trusted** — every gate quantifies ∀ over the set, so
an empty set passes every gate), the `ConfLevel`/`IntegLevel` inductives with numeric ranks
and decidable orders (zero ordering axioms), and the egress ceilings with the
`ceilingAdmits` irreducibility discipline byte-identical (E7).

## Kernel state vs frozen input (§5.5)

The boundary is normative — every authority sits on exactly one side.

| Authority | Side | Why |
| --- | --- | --- |
| Agent tree, capabilities | Kernel state | Revocation must be immediate and tree-aware |
| Labels (taint, integ) | Kernel state | The guarantee itself |
| Pending invocations, challenges, quarantine | Kernel state | They constrain future decisions and must survive crash via replay |
| Consumed IDs / attestations | Kernel state | One-use is a state property |
| Crossing authority (use counter) | Kernel state | Revocation immediacy + the crossing ceiling must be inside the proof |
| Action policy (floors, clearance, output provenance, declared egress) | **Frozen input**, snapshotted at begin | Governed, versioned, published outside; the kernel proves enforcement, not adequacy |
| Source provenance labels | **Frozen input** at `ingest` (kernel state for agent-to-agent) | Policy must not be able to relabel a contaminated agent as cleaner |
| Contract revision, assignment, declared fallback | **Frozen input** at `cross_output` | Same |
| Inspection / conformance / resolution verdicts | **Input evidence**; consumption is kernel state | The kernel owns scope and one-use; issuer *truth* is a named external seam |
| Enforcement mode | Immutable background | The adapter can never choose it |
| Authorizer verdict | Per-invocation input at begin | Carried V3 CHECK 3 |

## Encoding decisions

Carried from V3: relations are Prop-valued, the sorts are type parameters (the
Aeneas/Charon refinement instantiates them at concrete `String`-backed id types via the
sort-polymorphic soundness bundle), immutable background lives in fields the actions never
update, and `ceilingAdmits` is `@[irreducible]` while the integrity and clearance atoms
stay transparent — there is no existential on those sides to blow up congruence closure.

New, from the Task 0 spike (`V4Spike/SPIKE-NOTES.md`, architecture §14 E8–E13):

* `pending` is `InvocationId → Option (PendingInvocation …)`. Structured records inside an
  `Option`-valued map field, matching the Rust `VecMap` the kernel will carry.
* `PendingInvocation.authorized` records the authorizer verdict. V3 could state
  `default_deny` against a background relation; in V4 the verdict is a per-invocation
  input, so it is not statable at all unless the record records it.
* `contained` (`disposition = permitted`) is the predicate every gate-claiming invariant is
  conditioned on, and `speculative_taint_contained` is the filtered speculative set the
  clearance invariant reads while the gate keeps reading the unrestricted one (E10).

The `Hash` sort of architecture §5.1 is named `ContentHash` here: `Hash` is a core Lean
type class, and shadowing it inside every signature is asking for trouble.
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

/-- The confidentiality total order (replaces Veil's `le_conf` relation + ordering axioms). -/
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

/-! ## Verdicts, dispositions, mode (architecture §4, §5.1)

Concrete decidable inductives, the same philosophy that deleted Veil's ordering axioms.
Every decision computes one canonical **verdict**; the enforcement **disposition** is a
separate dimension, and `bypass_mode_sound` makes a non-contained disposition impossible
under `enforce`. -/

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

/-- How a pending invocation was admitted — *evidence*, never authority. -/
inductive Admission (AttestationId : Type) where
  | plain
  | inspected (att : AttestationId)
  | bypassed
  deriving DecidableEq

/-- A crossing grant: remaining uses against the bound it was provisioned with.

The finite-meter role V3's `budget_capacity` played for `budget_bounded` is played here by
`grant_bounded` (`remaining ≤ provisioned`). The bound is stored **per grant** rather than
being a protocol constant: §8 states the invariant against "its provisioned bound", E4
makes `grant_crossing` set-to-`n` mirroring the application grant record's `granted_uses`,
and a global constant would either cap operator provisioning at a number nobody sanctioned
or make the invariant false. It also gives T-11's per-grant decrement accounting a
state-side anchor. -/
structure CrossingGrant where
  remaining   : Nat
  provisioned : Nat
  deriving DecidableEq, Repr

/-! ## Frozen policy snapshot (architecture §5.2)

The model-side image of a published `ActionPolicyRevision` plus the per-invocation
attestations, frozen into the pending record at `begin_invocation`. Freezing is the point:
the pairwise gates and settlement read this record, so no later policy publication,
ingestion, settlement, or bypass can reinterpret an already-granted durable permit.

Egress ceilings deliberately stay immutable background rather than snapshot fields (E7):
the Kav frame rule already makes background constant over any trace — observationally
equivalent to freezing — and it keeps the `ceilingAdmits` atomicity discipline unchanged. -/

structure ActionPolicySnapshot (ToolId CapKind EgressKind PolicyDigest : Type) where
  /-- The **exact** entry identity the snapshot is bound to. `ToolId` is the composite
  identity of §9 — entry id, version, and code hash together, not an entry name — so
  `tool_registered` is per-version and a mismatched version or hash is a boundary denial
  with no kernel branch. That binding, plus governed publication authority, is what
  subsumes V3's `tool_attestation_intact`; the kernel-side residue is this field together
  with `pending_registered` and `pending_snapshot_coherent`. -/
  tool            : ToolId
  required_caps   : CapKind → Prop
  /-- NEW in V4 — the most-sensitive taint the invoker may hold (CHECK 2). Closes the
  2026-07-21 A2A finding that `conf_floor` is inert at the flow gate, since egress
  decisions key per-*channel* and not per-*target*. -/
  conf_clearance  : ConfLevel
  /-- ALLOW floor. -/
  integ_floor     : IntegLevel
  /-- Inspect-band floor. A floor above the inspect floor is an empty band — coherent by
  construction; the reverse is incoherent and rejected at the boundary. -/
  integ_inspect   : IntegLevel
  /-- Ordinary output provenance, confidentiality dimension (V3 `tool_conf_floor`). -/
  output_conf     : ConfLevel
  /-- Ordinary output provenance, integrity dimension (V3 `tool_output_integ`). Genuinely
  distinct from `integ_floor`: `delete_repo` has floor `trusted` / emission `attested`,
  `web_fetch` has floor `untrusted` / emission `untrusted`. -/
  output_integ    : IntegLevel
  /-- V3 `tool_egress`: the bound the per-invocation attested set must narrow to and, when
  non-empty, cover. -/
  declared_egress : EgressKind → Prop
  /-- Binds inspection-attestation scope. -/
  policy_digest   : PolicyDigest

/-! ## Pending, challenge (architecture §5.3) -/

structure PendingInvocation
    (AgentId ToolId CapKind EgressKind AttestationId PolicyDigest : Type) where
  agent       : AgentId
  policy      : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest
  /-- The attested per-invocation egress set. -/
  egress      : EgressKind → Prop
  admission   : Admission AttestationId
  /-- `permitted` or `monitor_bypassed`; `blocked` never pends. -/
  disposition : Disposition
  /-- The authorizer verdict this invocation was admitted under (spike addition — see the
  module docs). -/
  authorized  : Prop
  /-- Set by `settle_invocation ambiguous`. A quarantined invocation is not closed, absorbs
  nothing yet, and keeps participating in every speculative and pairwise quantifier: a
  dispatched-but-unconfirmed destructive effect may have happened, so it must keep gating. -/
  quarantined : Prop

/-- The exact scope an inspection challenge binds: the invocation (via the map key), the
acting agent, the action identity and frozen policy (via `policy` and its `policy_digest`),
the arguments hash, and the authorizer verdict. Under E1(b) the challenge record alone holds
the frozen snapshot and the pending record is created only on positive resolution, so every
quantifier over `pending` keeps meaning "may actually execute".

There is deliberately no separate `policy_digest` field: the digest is `policy.policy_digest`,
and duplicating it would let scope-match proofs compare the wrong copy. There is also no
expiry field — the kernel has no clock. Wall-clock freshness of an attestation is a resolver
rule and a named external seam; one-use consumption plus digest-scope binding is what closes
replay inside the kernel (§6.3's "expired-by-policy" arm is therefore a boundary denial). -/
structure ChallengeScope
    (AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest ContentHash : Type) where
  /-- Attribution only. The map is keyed by the invocation (E14), so the challenge's own
  identifier lives in the scope rather than in the key. Note the consequence: nothing here
  forces two open challenges to carry *distinct* ids. That is not a soundness hole — scope
  match includes the invocation key — but it leaves audit attribution unconstrained, so
  Task 6 decides explicitly between a `challenge_id_unique` conjunct and a recorded
  non-obligation. -/
  challenge  : ChallengeId
  agent      : AgentId
  policy     : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest
  egress     : EgressKind → Prop
  args_hash  : ContentHash
  authorized : Prop

/-! ## The state structure -/

structure St (AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
    CrossingId AssignmentDigest PolicyDigest ContentHash : Type) where
  -- Agent tree and labels (carried from V3 unchanged)
  agent_active          : AgentId → Prop
  agent_parent          : AgentId → AgentId → Prop
  agent_cap             : AgentId → CapKind → Prop
  /-- Levels ingested. Effective taint is the MAX of the set; EMPTY SET = UNTAINTED. -/
  taint_levels          : AgentId → ConfLevel → Prop
  /-- Levels ingested. Effective integrity is the MIN of the set; EMPTY SET = FULLY
  TRUSTED (dual of the taint reading). Every gate quantifies ∀ over the set. -/
  integ_levels          : AgentId → IntegLevel → Prop
  -- Transformed / new mutable state
  pending               : InvocationId →
    Option (PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
  /-- Keyed by the **invocation**, not by the challenge id (E14): `authorize_inspected`
  looks up by invocation and `challenge_unique` becomes true by construction, which removes
  a nested map scan from the action E13 makes the campaign's cost centre. The challenge's
  own identifier lives inside the scope as attribution. -/
  challenges            : InvocationId →
    Option (ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
      ContentHash)
  /-- Freshness history. Set at admission, NEVER cleared — not by `revoke`, not by
  `cascade_revoke`, not by `delegate`. It is history of invocation ids, not agent state,
  and that is what makes T-9 (freshness subsumption) provable. -/
  consumed_ids          : InvocationId → Prop
  /-- One-use evidence history. Never cleared, same rationale. Note this is a bare set: it
  records *that* an attestation was consumed, not what it authorised. T-11's one-to-one
  claim between band-crossings and consumed attestations is therefore carried at the trace
  level (`Kav.Reachable`) plus `inspected_evidence_consumed`, not by a state-side link. -/
  consumed_attestations : AttestationId → Prop
  /-- Freshness history for boundary crossings. `cross_output` (§6.5) takes a fresh
  `crossing_id` and consumes it exactly like an invocation id; it needs its own set so that
  T-9's freshness subsumption keeps quantifying over invocation ids alone. -/
  consumed_crossings    : CrossingId → Prop
  /-- Remaining crossing uses, keyed by (holder agent, exact assignment digest).
  Provisioned only by `grant_crossing` (root-only), decremented by exactly one on each
  conforming `cross_output`, destroyed for the agent by `revoke`/`cascade_revoke`. -/
  crossing_grants       : AgentId → AssignmentDigest → Option CrossingGrant
  tool_registered       : ToolId → Prop
  -- Immutable background
  egress_allow_ceiling   : EgressKind → Option ConfLevel
  egress_inspect_ceiling : EgressKind → Option ConfLevel
  /-- Governed enforcement mode. Immutable background in the single-tenant model: the
  adapter can never choose it. -/
  mode                   : Mode
  -- Named individuals
  root_agent             : AgentId

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-! ## Derived gates

The conf side is atomic via `ceilingAdmits`; the integrity and clearance sides are bare
comparisons. Design §9's open question ("exact Lean encoding of the generic graduated
gate") stays resolved as **two definitionally-aligned instantiations**, not one polymorphic
gate: same graduated SHAPE (ALLOW / INSPECT + vouch / DENY), two bodies. -/

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
ceiling. An inspect ceiling below the allow ceiling is an empty inspect band — coherent. -/
@[simp] def St.flow_inspects
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (l : ConfLevel) (e : EgressKind) : Prop :=
  ceilingAdmits s.egress_inspect_ceiling l e

/-- Integrity ALLOW against a **frozen snapshot**. V3 read the floor off live tool
background and so had to be a method on the state; in V4 it is state-independent, which is
exactly the point of freezing. Transparent by design — no existential to hide. -/
@[simp] def integ_allows (l : IntegLevel)
    (p : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) : Prop :=
  le_integ p.integ_floor l

/-- Integrity INSPECT against a frozen snapshot (dual of `St.flow_inspects`). -/
@[simp] def integ_inspects (l : IntegLevel)
    (p : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) : Prop :=
  le_integ p.integ_inspect l

/-- Clearance admission: the agent's taint clears the snapshot's per-target ceiling.
Two-valued — there is no inspect band on clearance. Transparent, like the integrity atoms. -/
@[simp] def clearance_admits (l : ConfLevel)
    (p : ActionPolicySnapshot ToolId CapKind EgressKind PolicyDigest) : Prop :=
  le_conf l p.conf_clearance

/-! ## Record-level predicates -/

/-- E2: the vouch is the *pending* party's recorded admission — never a retroactive
re-inspection of an already-admitted invocation, never a synchronous oracle read. -/
def vouched
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest) : Prop :=
  ∃ att, J.admission = Admission.inspected att

/-- A pending record whose gates are actually claimed to have passed.

A monitor bypass deliberately pends an invocation that *failed* its gates (the effect will
really run, so it must really constrain the next decision), so those records appear in
every speculative and pairwise quantifier at decision time but cannot themselves be claimed
gated. `bypass_mode_sound` — stated over `¬ contained`, not over the bypass constructor, so
that `blocked` cannot slip through unconstrained — confines them to `mode = monitor`, which
is what makes the enforce-mode reading of the safety properties full strength. -/
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

/-- Worst-case taint restricted to **contained** records (E10).

The gate reads the unrestricted `speculative_taint` — fail-closed, because a
monitor-bypassed effect really runs and really constrains the next decision — but
`clearance_confinement` must read this one. Otherwise a monitor bypass, admitted precisely
because it failed its gates, injects its `output_conf` into the agent's speculative taint
and retroactively falsifies every *other* pending invocation's clearance, with no guard
available to re-establish it. Stronger guard, weaker claim; under `enforce` the two
coincide by `bypass_mode_sound`.

This generalises: any invariant stated over a speculative set has to decide whether
bypassed records are members, and the gate and the invariant get different answers. -/
def speculative_taint_contained
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (a : AgentId) (l : ConfLevel) : Prop :=
  s.taint_levels a l
  ∨ (∃ I J, s.pending I = some J ∧ J.agent = a ∧ contained J ∧ J.policy.output_conf = l)

/-! ## Initial states -/

/-- Only `root_agent` is active and holds every capability; no labels, no pending
invocations, no challenges, no consumed history, no grants, no registered tools. `mode` and
the egress ceilings are governed background and are therefore unconstrained here — the Kav
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
