import Tzimtzum.Updates
import Kav.Action

/-!
# TzimtzumV4 — the structural actions

The seven agent-tree and registry actions of
[[2026-07-24-tzimtzum-v4/architecture|architecture]] §7: `register_tool`,
`unregister_tool`, `delegate`, `grant_capability`, `grant_crossing`, `revoke`,
`cascade_revoke`. Definitions only — proofs are Task 7.

## What changed from V3

* **`register_tool` loses its `trusted_issuer` guard** (§9). V3 established that every
  registered tool's labels come from a trusted issuer; in V4 a tool is invocable only
  through a frozen `ActionPolicySnapshot` bound to its *exact* composite identity (entry
  id, version, code hash — E17), and producing such a snapshot requires a published
  `ActionPolicyRevision`, which requires tenant-admin authority. Issuer trust therefore
  flows through governed policy publication rather than through a kernel issuer relation.
  The kernel-side residue of `tool_attestation_intact` is `pending_registered` +
  `pending_snapshot_coherent` + that identity binding; a mismatched version or hash is a
  boundary denial with no kernel branch. Publication authority itself is a named Dixie-side
  seam, not a kernel invariant.
* **`unregister_tool` widens its guard**: no *pending* invocation — including quarantined
  ones — and no *open challenge* may reference the tool identity. Fail-closed: a quarantined
  invocation blocks unregistration until it is resolved. This preserves `pending_registered`
  by construction.
* **`delegate` spawns a clean compartment**: empty capabilities, empty taint, empty
  integrity (= fully trusted, which is what makes T-12's fresh-compartment lemma true), no
  pending invocations, no open challenges, and **no crossing grants** — the V4 analogue of
  V3's budget-0 spawn. Grants are never inherited or minted by delegation.
* **`grant_crossing` is new** and is the operator plane: root-only, set-to-`n` (E4/E15).
* **`revoke` / `cascade_revoke` widen**: they additionally destroy the target's crossing
  grants, drop its pending invocations *including quarantined ones*, and resolve its open
  challenges fail-closed (the challenge dies, nothing pends). A revoked agent's quarantine
  no longer constrains anything, because the agent can no longer act.

## What is never cleared

`consumed_ids`, `consumed_attestations` and `consumed_crossings` are **history**, not agent
state. No action clears them — V3's rationale for never clearing `invocation_used` carries
verbatim, and it is what makes T-9's freshness subsumption provable across revocation and
re-delegation.
-/

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-! ## Tool registry -/

/-! `register_tool` — guard is `¬ registered` only: the V3 `trusted_issuer` guard is deleted, subsumed by
exact-identity policy publication (§9, E17). Re-registration after unregistration is
permitted; issuer distrust (key revocation) stays in the mesh. -/

kav_action register_tool (tool : ToolId) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require ¬ s.tool_registered tool
  tool_registered := fun T => s.tool_registered T ∨ T = tool

/-! `unregister_tool` — a compromised tool leaves the authorization surface. Fail-closed: nothing pending
(quarantined included) and no open challenge may reference the identity, which preserves
`pending_registered` by construction.

Extraction note (§13): both ∀-guards refine to accumulator loops over the `VecMap`s -- set a
`bool` and keep iterating. They must NOT become early-`return` scans; Aeneas has no model
for an early `return` inside a loop. -/

kav_action unregister_tool (tool : ToolId) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require s.tool_registered tool
  require ∀ (I : InvocationId) (J : PendingInvocation AgentId ToolId CapKind EgressKind
      AttestationId PolicyDigest), s.pending I = some J → J.policy.tool ≠ tool
  require ∀ (I : InvocationId) (sc : ChallengeScope AgentId ToolId CapKind EgressKind
      ChallengeId PolicyDigest ContentHash), s.challenges I = some sc → sc.policy.tool ≠ tool
  tool_registered := fun T => s.tool_registered T ∧ T ≠ tool

/-! ## Agent tree -/

/-! `delegate` — the grantee spawns as a clean compartment. Capabilities and both label sets are cleared
pointwise (V3's shape); pending records, open challenges and crossing grants are dropped by
owner. The clearing is deliberately *defensive* rather than leaning on `revocation_clean` to
supply emptiness for a currently-inactive id: T-12 (fresh compartment) is a headline product
claim, and it should not rest on another invariant staying true. -/

open Classical in
kav_action delegate (grantor grantee : AgentId) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require s.agent_active grantor
  require ¬ s.agent_active grantee
  require grantee ≠ s.root_agent
  -- The id must not still be somebody's parent. Without this, reusing the id of a revoked
  -- agent that still has active children severs those children's parent edge (the
  -- `P ≠ grantee` clause below), leaving them active, capability-holding, grant-holding and
  -- **unrevokable** -- both `revoke` and `cascade_revoke` require a parent edge. That would
  -- defeat §5.5's tree-aware-revocation rationale for keeping crossing authority in kernel
  -- state. Note the `P ≠ grantee` clause itself must stay: without it, an orphan keeping its
  -- capabilities alongside a freshly-empty parent makes `capability_subsumption` false.
  require ∀ (C : AgentId), ¬ s.agent_parent C grantee
  agent_active := fun A => s.agent_active A ∨ A = grantee
  agent_parent := fun C P =>
    (C = grantee ∧ P = grantor) ∨ (s.agent_parent C P ∧ C ≠ grantee ∧ P ≠ grantee)
  agent_cap := fun N C => s.agent_cap N C ∧ N ≠ grantee
  taint_levels := fun A L => s.taint_levels A L ∧ A ≠ grantee
  integ_levels := fun A L => s.integ_levels A L ∧ A ≠ grantee
  pending := dropPendingOf s.pending grantee
  challenges := dropChallengesOf s.challenges grantee
  crossing_grants := dropGrantsOf s.crossing_grants grantee

/-! `grant_capability` — carried from V3 unchanged: incremental, parent-held,
parent-edge-gated. -/

kav_action grant_capability (prnt child : AgentId) (cap : CapKind) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require s.agent_active prnt
  require s.agent_active child
  require s.agent_parent child prnt
  require s.agent_cap prnt cap
  agent_cap := fun N C => (N = child ∧ C = cap) ∨ s.agent_cap N C

/-! ## The operator plane -/

/-! `grant_crossing` — provision or replenish `agent`'s crossing grant for the exact assignment digest `d` to
`n` uses.

**Root-only** (E4): the granting party must be `root_agent`, which keeps replenishment
structurally out-of-band with respect to the automatic crossing loop. A capability-gated
variant is rejected as re-opening a self-service path down the tree — that is the objection
that retired V3's in-band `grant_override`.

**Set-to-`n`, not add-with-clamp** (E4): idempotent provisioning mirrors the application
grant record's `granted_uses`, whereas add semantics would make replayed provisioning
non-idempotent. `provisioned` is set to `n` alongside `remaining`, so `grant_bounded`
(`remaining ≤ provisioned`, E15) holds at the point of provisioning and the counter is
bounded by what the operator actually granted rather than by a protocol constant. -/

open Classical in
kav_action grant_crossing (grantor agent : AgentId) (d : AssignmentDigest) (n : Nat) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require grantor = s.root_agent
  require s.agent_active grantor
  require s.agent_active agent
  crossing_grants := fun A D =>
    if A = agent ∧ D = d then some { remaining := n, provisioned := n }
    else s.crossing_grants A D

/-! ## Revocation

Immediate and tree-aware, which is the reason crossing authority is kernel state at all
(north-star principle 6). Consumed histories survive: they are history, not agent state. -/

/-! `revoke` — revoke an active child, destroying the target's capabilities, labels,
pending invocations (quarantined included), open challenges, and crossing grants. -/

kav_action revoke (prnt target : AgentId) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require s.agent_parent target prnt
  require s.agent_active prnt
  require s.agent_active target
  require target ≠ s.root_agent
  agent_active := fun A => s.agent_active A ∧ A ≠ target
  agent_parent := fun C P => s.agent_parent C P ∧ C ≠ target
  agent_cap := fun A C => s.agent_cap A C ∧ A ≠ target
  taint_levels := fun A L => s.taint_levels A L ∧ A ≠ target
  integ_levels := fun A L => s.integ_levels A L ∧ A ≠ target
  pending := dropPendingOf s.pending target
  challenges := dropChallengesOf s.challenges target
  crossing_grants := dropGrantsOf s.crossing_grants target

/-! `cascade_revoke` — an active child whose parent is already inactive. Same destruction
set. -/

kav_action cascade_revoke (child prnt : AgentId) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require s.agent_parent child prnt
  require ¬ s.agent_active prnt
  require s.agent_active child
  require child ≠ s.root_agent
  agent_active := fun A => s.agent_active A ∧ A ≠ child
  agent_parent := fun C P => s.agent_parent C P ∧ C ≠ child
  agent_cap := fun A C => s.agent_cap A C ∧ A ≠ child
  taint_levels := fun A L => s.taint_levels A L ∧ A ≠ child
  integ_levels := fun A L => s.integ_levels A L ∧ A ≠ child
  pending := dropPendingOf s.pending child
  challenges := dropChallengesOf s.challenges child
  crossing_grants := dropGrantsOf s.crossing_grants child

/-! ## Idempotence of provisioning (E4)

Set-to-`n` semantics, stated rather than asserted: replaying a provisioning action leaves
the grant map unchanged. This is what makes operator provisioning replay-safe, and it is
the property add-with-clamp would lose. -/

-- The `obtain` patterns below destructure `next`'s 16 field equations positionally. That is
-- fragile in principle, but `crossing_grants`'s type is unique among the fields, so a field
-- reorder in `State.lean` breaks this proof at elaboration rather than silently retargeting
-- it. Revisit if two fields ever share a type.
theorem grant_crossing_idempotent
    (grantor agent : AgentId) (d : AssignmentDigest) (n : Nat)
    (s s' s'' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (h1 : (grant_crossing grantor agent d n).next s s')
    (h2 : (grant_crossing grantor agent d n).next s' s'') :
    s''.crossing_grants = s'.crossing_grants := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hg1, -, -, -, -, -⟩ := h1
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hg2, -, -, -, -, -⟩ := h2
  funext A D
  rw [hg2, hg1]
  by_cases h : A = agent ∧ D = d <;> simp [h]

end Tzimtzum
