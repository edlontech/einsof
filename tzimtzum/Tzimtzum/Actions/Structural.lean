import Tzimtzum.Updates
import Kav.Action

/-!
# TzimtzumV4 structural actions

The structural actions register and unregister tools, create child compartments, grant
capabilities and crossing uses, and revoke agents. Tool unregistration requires that no pending
record or open challenge uses the tool. Delegation clears the grantee's capabilities, labels,
pending records, challenges, and grants. Revocation removes the same agent-owned state while
retaining identifier and evidence histories.
-/

namespace Tzimtzum

variable {AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
  CrossingId AssignmentDigest PolicyDigest ContentHash : Type}

/-! ## Tool registry -/

/-! `register_tool` adds an unregistered tool identity. Invocation admission later requires a
pending snapshot to name a registered tool. -/

kav_action register_tool (tool : ToolId) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require fresh : ¬ s.tool_registered tool
  tool_registered := fun T => s.tool_registered T ∨ T = tool

/-! `unregister_tool` removes a registered tool only when no pending record or challenge scope
references it. This keeps every retained pending or challenged tool identity registered. -/

kav_action unregister_tool (tool : ToolId) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require registered : s.tool_registered tool
  require no_pending_use : ∀ (I : InvocationId) (J : PendingInvocation AgentId ToolId CapKind
      EgressKind AttestationId PolicyDigest), s.pending I = some J → J.policy.tool ≠ tool
  require no_challenge_use : ∀ (I : InvocationId) (sc : ChallengeScope AgentId ToolId CapKind
      EgressKind ChallengeId PolicyDigest ContentHash),
    s.challenges I = some sc → sc.policy.tool ≠ tool
  tool_registered := fun T => s.tool_registered T ∧ T ≠ tool

/-! ## Agent tree -/

/-! `delegate` creates an active child of an active grantor. The child starts with no
capabilities, labels, pending records, challenges, or crossing grants. -/

open Classical in
kav_action delegate (grantor grantee : AgentId) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require grantor_active : s.agent_active grantor
  require grantee_fresh : ¬ s.agent_active grantee
  require grantee_not_root : grantee ≠ s.root_agent
 -- The grantee cannot already be a parent. Reusing such an identifier would remove parent
 -- edges from active children, leaving them without a revocable parent and violating
 -- `capability_subsumption`.
  require grantee_no_children : ∀ (C : AgentId), ¬ s.agent_parent C grantee
  agent_active := fun A => s.agent_active A ∨ A = grantee
  agent_parent := fun C P =>
    (C = grantee ∧ P = grantor) ∨ (s.agent_parent C P ∧ C ≠ grantee ∧ P ≠ grantee)
  agent_cap := fun N C => s.agent_cap N C ∧ N ≠ grantee
  taint_levels := fun A L => s.taint_levels A L ∧ A ≠ grantee
  integ_levels := fun A L => s.integ_levels A L ∧ A ≠ grantee
  pending := dropPendingOf s.pending grantee
  challenges := dropChallengesOf s.challenges grantee
  crossing_grants := dropGrantsOf s.crossing_grants grantee

/-! `grant_capability` adds one capability to an active child when its active parent holds it. -/

kav_action grant_capability (prnt child : AgentId) (cap : CapKind) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require parent_active : s.agent_active prnt
  require child_active : s.agent_active child
  require parent_edge : s.agent_parent child prnt
  require parent_holds : s.agent_cap prnt cap
  agent_cap := fun N C => (N = child ∧ C = cap) ∨ s.agent_cap N C

/-! ## The operator plane -/

/-! `grant_crossing` sets an active agent's exact-digest grant to `n` remaining and provisioned
uses. Only `root_agent` may provision the grant, and setting rather than adding uses makes a
repeated identical provisioning action idempotent. -/

open Classical in
kav_action grant_crossing (grantor agent : AgentId) (d : AssignmentDigest) (n : Nat) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require root_grantor : grantor = s.root_agent
  require grantor_active : s.agent_active grantor
  require agent_active : s.agent_active agent
  crossing_grants := fun A D =>
    if A = agent ∧ D = d then some { remaining := n, provisioned := n }
    else s.crossing_grants A D

/-! ## Revocation

Revocation removes the target's agent-owned authority and state immediately. Consumed histories
remain because they record identifiers and evidence rather than agent-owned resources. -/

/-! `revoke`; revoke an active child, destroying the target's capabilities, labels,
pending invocations (quarantined included), open challenges, and crossing grants. -/

kav_action revoke (prnt target : AgentId) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require parent_edge : s.agent_parent target prnt
  require parent_active : s.agent_active prnt
  require target_active : s.agent_active target
  require target_not_root : target ≠ s.root_agent
  agent_active := fun A => s.agent_active A ∧ A ≠ target
  agent_parent := fun C P => s.agent_parent C P ∧ C ≠ target
  agent_cap := fun A C => s.agent_cap A C ∧ A ≠ target
  taint_levels := fun A L => s.taint_levels A L ∧ A ≠ target
  integ_levels := fun A L => s.integ_levels A L ∧ A ≠ target
  pending := dropPendingOf s.pending target
  challenges := dropChallengesOf s.challenges target
  crossing_grants := dropGrantsOf s.crossing_grants target

/-! `cascade_revoke`; an active child whose parent is already inactive. Same destruction
set. -/

kav_action cascade_revoke (child prnt : AgentId) :
    St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId CrossingId
      AssignmentDigest PolicyDigest ContentHash where
  require parent_edge : s.agent_parent child prnt
  require parent_inactive : ¬ s.agent_active prnt
  require child_active : s.agent_active child
  require child_not_root : child ≠ s.root_agent
  agent_active := fun A => s.agent_active A ∧ A ≠ child
  agent_parent := fun C P => s.agent_parent C P ∧ C ≠ child
  agent_cap := fun A C => s.agent_cap A C ∧ A ≠ child
  taint_levels := fun A L => s.taint_levels A L ∧ A ≠ child
  integ_levels := fun A L => s.integ_levels A L ∧ A ≠ child
  pending := dropPendingOf s.pending child
  challenges := dropChallengesOf s.challenges child
  crossing_grants := dropGrantsOf s.crossing_grants child

/-! ## Idempotence of provisioning

Applying the same `grant_crossing` action twice leaves the grant map unchanged after the first
application. -/

theorem grant_crossing_idempotent
    (grantor agent : AgentId) (d : AssignmentDigest) (n : Nat)
    (s s' s'' : St AgentId ToolId InvocationId CapKind EgressKind ChallengeId AttestationId
      CrossingId AssignmentDigest PolicyDigest ContentHash)
    (h1 : (grant_crossing grantor agent d n).next s s')
    (h2 : (grant_crossing grantor agent d n).next s' s'') :
    s''.crossing_grants = s'.crossing_grants := by
  have hg1 := grant_crossing.next_crossing_grants h1
  have hg2 := grant_crossing.next_crossing_grants h2
  funext A D
  rw [hg2, hg1]
  by_cases h : A = agent ∧ D = d <;> simp [h]

end Tzimtzum
