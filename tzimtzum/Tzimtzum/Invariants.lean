import Tzimtzum.State

/-!
# TzimtzumV4 — safety properties and strengthening invariants

The conjuncts of [[2026-07-24-tzimtzum-v4/architecture|architecture]] §8 as amended
(E10, E11, E14, E15, E20, E22, E23), adopting the Task 0 spike's five-sub-bundle split.
Definitions only; the sub-bundles and conjunction lemma live in `Soundness/Bundle.lean`,
and proving is Tasks 7–10.

## Conventions (both load-bearing, both spike findings)

1. **`contained J` gating.** Every conjunct that *claims a gate passed* is conditioned on
   `contained J` (`disposition = permitted`). Monitor-bypassed records really run, so they
   really constrain future decisions — they appear in `speculative_*` and in the fail-closed
   gate quantifiers — but they cannot themselves be claimed gated. `bypass_mode_sound`
   (stated over `¬ contained`, E11, so `blocked` cannot slip through unconstrained) confines
   them to `mode = monitor`, which makes the enforce-mode reading full strength.
2. **Vouch keying (E22).** The pairwise inspect arms name the *constrained* party's vouch —
   `vouched J2`, the record whose egress/floor is being crossed — not a disjunction. The
   disjunction was not settlement-stable: when `J1` settles, its frozen `output_conf`
   becomes held taint while `J2` still pends, and `flow_confinement` then demands
   `vouched J2` specifically.

## Deliberately encoding-trivial conjuncts

`pending_unique`, `challenge_unique`, `quarantine_pending` and `grant_pinned` are true by
the `Option`-map encodings. They are kept as *named* conjuncts because they are exactly the
properties the Rust `VecMap` refinement (a `Vec` of pairs, where duplicate keys are
representable) must actually prove — visible obligations at that boundary, free here.

## Recorded non-obligation: `challenge_id_unique`

Under E14 the challenge map is keyed by invocation and the `ChallengeId` is attribution
inside the scope; nothing forces two open challenges to carry distinct ids. This is
deliberate: scope match at resolution includes the invocation key, so no soundness property
depends on id uniqueness, and T-11's one-to-one accounting keys on *attestation* ids
(consumed one-use), not challenge ids. Challenge-id attribution quality is an event-log
concern, not kernel state.

## `grant_bounded` is not a finite meter

Under E15's set-to-`n` provisioning, `remaining ≤ provisioned` is trivially true *at
provisioning*; its content lives entirely in T-7 — no action other than `grant_crossing`
ever raises `remaining` — which together with the decrement on each endorsed crossing gives
the oracle-independent crossing ceiling between operator provisioning actions. It is kept in
the bundle because T-11's per-grant accounting reads it, not because it plays V3's
`budget_bounded` role.
-/

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-! ## S — structural -/

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

/-- **capability_subsumption**: for any active parent-child pair, the child's capabilities
are a subset of the parent's. The `agent_active P` hypothesis is load-bearing (`revoke`
breaks the conjunct outright without it — the Task 2 review's constraint). -/
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

/-- **revocation_clean** (widened per §7): inactive agents leave no residue — no labels, no
pending invocations, no open challenges, no crossing grants. Consumed histories are *not*
agent state and survive. -/
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

/-! ## P — pending / gates -/

/-- **pending_unique**: the pending map is functional. Encoding-trivial (module docs). -/
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

/-- **pending_ids_consumed**: freshness inductiveness — every pending id is in the
never-cleared history (T-9's subsumption of V3's `invocation_used`). -/
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

/-- **pending_snapshot_coherent**: every admitted snapshot has a well-formed band. §8's
"canonical labels" clause is deleted with justification: under the concrete
`ConfLevel`/`IntegLevel` inductives every label value IS canonical — non-canonical label
representations are unrepresentable, so the clause is content-free here (it existed for
encodings where labels carry a normal form). -/
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

/-- **flow_confinement**: a tainted agent's contained pending egress is permitted — ALLOW,
or INSPECT with the pending party vouched. No override arm exists in V4. -/
def flow_confinement
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (L : ConfLevel) (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (E : EgressKind),
    s.taint_levels J.agent L → s.pending I = some J → contained J → J.egress E →
      s.flow_allows L E ∨ (s.flow_inspects L E ∧ vouched J)

/-- **flow_confinement_weak**: oracle-independent — DENY-band pairs are structurally
impossible regardless of inspector behaviour. -/
def flow_confinement_weak
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (L : ConfLevel) (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (E : EgressKind),
    s.taint_levels J.agent L → s.pending I = some J → contained J → J.egress E →
      s.flow_allows L E ∨ s.flow_inspects L E

/-- **integrity_confinement** (headline): an agent holding integrity level `L` has no
contained pending invocation whose frozen floor `L` fails to clear outside the vouched
inspect band. -/
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

/-- **clearance_confinement** (new in V4, E9/E10/E20): no contained pending invocation
while the agent's *contained* speculative taint exceeds the invocation's frozen clearance.
The invariant reads the contained-filtered set; the gates read the unrestricted one. -/
def clearance_confinement
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (L : ConfLevel) (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J → contained J → speculative_taint_contained s J.agent L →
      clearance_admits L J.policy

/-! ## P′ — pairwise -/

/-- **pending_flow_compat** (E22 keying): any two contained pending invocations of one
agent — the self-pair and quarantined records included — are flow-compatible: `J1`'s frozen
output clears `J2`'s attested egress, or the pair sits in the inspect band with the
*constrained* party (`J2`, the egress-bearer) vouched. Why a durable permit is never
invalidated by a later settlement. -/
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

/-- **pending_integ_compat** (E22 keying): the integrity dual — `J1`'s frozen emission
clears `J2`'s frozen floor, or the inspect band with `J2` (the floor-bearer) vouched. -/
def pending_integ_compat
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I1 I2 : InvocationId)
    (J1 J2 : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I1 = some J1 → s.pending I2 = some J2 → J1.agent = J2.agent →
    contained J1 → contained J2 →
      integ_allows J1.policy.output_integ J2.policy
      ∨ (integ_inspects J1.policy.output_integ J2.policy ∧ vouched J2)

/-! ## E — evidence -/

/-- **challenge_scoped**: every open challenge binds a well-formed scope referencing a
real, undecided invocation — not yet pending (E1(b)), freshness burned at creation, an
active non-root agent, a registered tool, a coherent band, and narrowing/coverage. -/
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

/-- **challenges_enforce_only** (E23): challenges are a blocking construct, and monitor
mode never blocks — under `monitor` the challenge map is empty in every reachable state,
which is what makes §6.3's monitor arm dead code. -/
def challenges_enforce_only
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (sc : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
      ContentHash),
    s.challenges I = some sc → s.mode = Mode.enforce

/-- **challenge_unique**: the challenge map is functional. Encoding-trivial under E14
(module docs; V3-style at-most-one-per-invocation is the keying itself). -/
def challenge_unique
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (sc1 sc2 : ChallengeScope AgentId ToolId CapKind EgressKind ChallengeId PolicyDigest
      ContentHash),
    s.challenges I = some sc1 → s.challenges I = some sc2 → sc1 = sc2

/-- **inspected_evidence_consumed**: a lever used is a lever recorded — every inspected
admission's attestation is in the one-use history. -/
def inspected_evidence_consumed
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest)
    (att : AttestationId),
    s.pending I = some J → J.admission = Admission.inspected att →
      s.consumed_attestations att

/-- **bypass_mode_sound** (E11): every non-contained pending record — and every bypassed
admission — implies `mode = monitor`. Stated over `¬ contained`, not the bypass
constructor, so `blocked` cannot satisfy the bundle with every gate conjunct vacuous. -/
def bypass_mode_sound
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J →
      (¬ contained J → s.mode = Mode.monitor)
      ∧ (J.admission = Admission.bypassed → s.mode = Mode.monitor)

/-- **quarantine_pending**: a quarantined invocation is pending. This is a *tautology* —
provable with `K := J` in any state under any encoding, including a Rust kernel that stores
quarantine in a side table — so unlike `pending_unique`/`grant_pinned` it is NOT a
refinement obligation. It is kept as pure nomenclature: the named record, citable from the
docs, that V4 encodes quarantine as a flag *on* the pending record (so it participates in
every P/P′ quantifier by construction) rather than as a separate state component. Costs the
discharge nothing. -/
def quarantine_pending
    (s : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash) : Prop :=
  ∀ (I : InvocationId)
    (J : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
    s.pending I = some J → J.quarantined →
      ∃ (K : PendingInvocation AgentId ToolId CapKind EgressKind AttestationId PolicyDigest),
        s.pending I = some K ∧ K.quarantined

/-! ## C — crossing -/

/-- **grant_bounded** (E15): remaining uses never exceed the provisioned bound. See the
module docs — the content lives in T-7, not here. -/
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
