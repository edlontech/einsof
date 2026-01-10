import Veil

/-!
# Tzimtzum v2.3: Tool Authorization Protocol Security Kernel

Formally verified security kernel for LLM tool authorization.

## Problem

The Lethal Trifecta (Simon Willison, 2025): **Private data + Untrusted content +
External communication = Exfiltration**. If all three legs are present, indirect prompt
injection can always extract data. This protocol structurally prevents the third leg
(egress) from connecting to the first two by enforcing authorization at tool boundaries.

## Architecture

Agents form a tree rooted at `root_agent`. Each agent carries:
- **Capabilities**: typed permissions flowing downward only (parent -> child)
- **Taint set**: confidentiality levels the agent has been exposed to (grows monotonically)
- **In-flight set**: currently executing tool invocations (for speculative taint)

Tools are registered with static, immutable labels: required capabilities, egress kinds,
confidentiality floor, and endorsement status. Endorsed tools (bounded output schema)
do not add taint on completion.

Every tool invocation passes through a three-check gate:
1. **Capability gate** -- agent holds all capabilities the tool requires
2. **Flow gate** -- for each (taint_level, egress_kind) pair, policy allows the flow
3. **Authorizer gate** -- external policy engine authorizes the specific (agent, tool) pair

The flow gate uses graduated enforcement: ALLOW (no restriction), INSPECT (permit if
a content gate certifies the arguments are safe), or DENY (hard block). Default is DENY
for all pairs.

## Design Choices

- **Summary taint**: at most 4 confidentiality levels per agent, O(1) flow checks
- **Automatic taint**: no operator choice at result time -- taint is applied on invoke_complete
- **Static tool labels**: labels are immutable background theory, declared at registration
- **Speculative taint**: flow gate checks worst-case taint including all in-flight
  non-endorsed tools, eliminating TOCTOU races without requiring sequential execution
- **Graduated flow enforcement**: ALLOW / INSPECT / DENY per (level, egress) pair

## Verification

6 safety properties + 12 strengthening invariants, all verified via Veil 2.0 push-button
SMT (cvc5). No manual proofs required. See `argus/design/2026-02-16-tzimtzum-v2-protocol-design.md`
for the full protocol design document.
-/

veil module TzimtzumV2

/-!
## Sorts

Six uninterpreted sorts model the protocol's domain. "Uninterpreted" means the SMT solver
reasons about them abstractly -- it doesn't know what an AgentId looks like, only that
agents can be equal or different. This makes the proof hold for ANY concrete instantiation.
-/
type AgentId        -- An LLM agent node in the delegation tree
type ToolId         -- A registered tool (API, MCP server, etc.)
type InvocationId   -- A unique identifier for a single tool invocation (in-flight tracking)
type CapKind        -- A capability kind (filesystem_read, network_write, execution, etc.)
type EgressKind     -- An outbound channel classification (network_external, network_internal, etc.)
type ConfLevel      -- A confidentiality level (public < internal < sensitive < restricted)

/-!
## Ordering

Confidentiality levels form a total order: public < internal < sensitive < restricted.
Since ConfLevel is uninterpreted, we axiomatize the ordering via an immutable Bool relation
`le_conf` with explicit axioms below. This is a standard Veil pattern for ordered sorts.
-/
immutable relation le_conf : ConfLevel -> ConfLevel -> Bool

/-!
## Named Constants

These are distinguished elements of the uninterpreted sorts. `immutable individual`
means they exist in the background theory and never change.

The four confidentiality levels form the lattice: public < internal < sensitive < restricted.
`root_agent` is the top of the delegation tree -- always active, holds all capabilities.
-/
immutable individual cl_public : ConfLevel
immutable individual cl_internal : ConfLevel
immutable individual cl_sensitive : ConfLevel
immutable individual cl_restricted : ConfLevel
immutable individual root_agent : AgentId

/-!
## Immutable Tool Metadata

Tool properties are declared at registration time and never change. This is a key design
simplification over v1: by making tool metadata immutable, we eliminate an entire class of
invariants (tool label consistency) and the promote/demote actions.

- `tool_cap T C`: tool T requires capability C to invoke
- `tool_egress T E`: tool T has outbound channel of kind E (can have multiple)
- `tool_conf_floor T`: the confidentiality floor -- invoking T exposes the agent to data at this level
- `tool_endorsed T`: true if T has a bounded output schema (boolean, enum, bounded int).
  Endorsed tools don't add taint on completion because their output is information-theoretically bounded.

**Trust assumption (A1) -- shared resources**: The protocol tracks data flow at tool
invocation boundaries only. Inter-tool communication via shared resources (filesystem,
database, APIs) is invisible to the protocol. Tools sharing writable resources must
declare `tool_conf_floor` accounting for the worst-case data reachable through those
shared resources. Layer 1 (sandbox) enforces resource isolation so that label
declarations match actual access boundaries.
-/
immutable relation tool_cap : ToolId -> CapKind -> Bool
immutable relation tool_egress : ToolId -> EgressKind -> Bool
immutable function tool_conf_floor : ToolId -> ConfLevel
immutable relation tool_endorsed : ToolId -> Bool

/-!
## Immutable Flow Policy

The flow policy is the core of the information flow control. It maps
(confidentiality_level, egress_kind) pairs to one of three enforcement modes:

- **ALLOW**: `flow_allows L E = true`. No restriction. Data at level L can reach egress E freely.
- **INSPECT**: `flow_inspects L E = true`. Permitted only if `content_gate_passes A T` --
  a deterministic content inspection oracle certifies the arguments don't contain sensitive data.
- **DENY**: neither is true. Hard block. No invocation possible.

We encode this as two Bool relations instead of a FlowMode enum sort. This avoids
Veil elaboration issues with enum sorts and is equivalent: the `flow_exclusive` axiom
ensures ALLOW and INSPECT are mutually exclusive, and DENY is the implicit default.

`flow_override` provides per-(agent, tool, level) exceptions. These are principal-scoped
and NOT inherited by children. Overrides are immutable (part of the background theory) --
temporal scoping is achieved through agent lifecycle: delegate a short-lived child with
the override, revoke it when the task completes. This aligns with least-privilege:
prefer scoped children over long-lived elevated agents.

`authorizer_allows` and `content_gate_passes` are external oracles. The authorizer is the
policy engine; the content gate is a deterministic argument inspection pipeline
(EDM fingerprinting, regex patterns, literal matching, embedding similarity).
-/
immutable relation flow_allows : ConfLevel -> EgressKind -> Bool
immutable relation flow_inspects : ConfLevel -> EgressKind -> Bool
immutable relation flow_override : AgentId -> ToolId -> ConfLevel -> Bool
immutable relation authorizer_allows : AgentId -> ToolId -> Bool
immutable relation content_gate_passes : AgentId -> ToolId -> Bool

/-!
## Mutable State

These relations change as the protocol executes. Uppercase variables in Veil are
implicitly universally quantified, so `relation agent_active : AgentId -> Bool`
defines a predicate over all agents.

- `agent_active A`: agent A exists and is participating in the system
- `agent_parent C P`: C is a direct child of P in the delegation tree
- `agent_cap A C`: agent A holds capability C
- `taint_levels A L`: agent A has been exposed to data at confidentiality level L
- `in_flight A I`: agent A has invocation I currently executing (not yet completed)
- `invocation_tool I`: maps each invocation ID to its tool (immutable -- binding is permanent)
- `tool_registered T`: tool T has been registered in the system
- `gh_taint_invoked A L`: ghost tracking -- A acquired taint at L via invoke_complete
- `gh_taint_received A L`: ghost tracking -- A acquired taint at L via return_unendorsed

The `gh_` (ghost) tracking relations exist solely to prove taint_integrity: that every
taint level is traceable to either an invocation or a receipt from a child. They mirror
the taint_levels updates but record the SOURCE of each taint addition.
-/
relation agent_active : AgentId -> Bool
relation agent_parent : AgentId -> AgentId -> Bool
relation agent_cap : AgentId -> CapKind -> Bool
relation taint_levels : AgentId -> ConfLevel -> Bool
relation in_flight : AgentId -> InvocationId -> Bool
immutable function invocation_tool : InvocationId -> ToolId
relation tool_registered : ToolId -> Bool
relation gh_taint_invoked : AgentId -> ConfLevel -> Bool
relation gh_taint_received : AgentId -> ConfLevel -> Bool

#gen_state

/-!
## Ordering Axioms

These axioms make `le_conf` a total order over the four named confidentiality levels.
The axioms are: reflexivity, transitivity, antisymmetry, totality (any two levels are
comparable), the chain (public < internal < sensitive < restricted), and pairwise
distinctness of all four levels.

Without distinctness axioms, the SMT solver could collapse two levels into one,
producing spurious counterexamples.
-/
assumption [conf_refl] le_conf L L = true
assumption [conf_trans] le_conf L1 L2 /\ le_conf L2 L3 -> le_conf L1 L3 = true
assumption [conf_antisym] le_conf L1 L2 /\ le_conf L2 L1 -> L1 = L2
assumption [conf_total] le_conf L1 L2 = true \/ le_conf L2 L1 = true
assumption [conf_chain_01] le_conf cl_public cl_internal = true
assumption [conf_chain_12] le_conf cl_internal cl_sensitive = true
assumption [conf_chain_23] le_conf cl_sensitive cl_restricted = true
assumption [conf_distinct_01] cl_public != cl_internal
assumption [conf_distinct_02] cl_public != cl_sensitive
assumption [conf_distinct_03] cl_public != cl_restricted
assumption [conf_distinct_12] cl_internal != cl_sensitive
assumption [conf_distinct_13] cl_internal != cl_restricted
assumption [conf_distinct_23] cl_sensitive != cl_restricted

/-!
## Flow Policy Axiom

ALLOW and INSPECT are mutually exclusive. A (level, egress) pair cannot be both
allowed freely AND require inspection. If `flow_allows` is true, `flow_inspects`
must be false. The third mode (DENY) is implicit: when neither is true, the pair
is denied.
-/
assumption [flow_exclusive] flow_allows L E -> flow_inspects L E = false

/-!
## Ghost Relations

`speculative_taint` is a derived predicate (not stored in state). It computes the
worst-case taint an agent could have, accounting for both:
1. Actual taint (`taint_levels`) from completed invocations
2. Potential taint from all in-flight non-endorsed tools

This is the key mechanism enabling safe parallel execution. When the flow gate checks
speculative taint at invoke_start, it guarantees flow confinement holds regardless of
which order the in-flight tools complete.
-/
ghost relation speculative_taint (a : AgentId) (l : ConfLevel) :=
  taint_levels a l
  \/ (exists I, in_flight a I
      /\ tool_conf_floor (invocation_tool I) = l
      /\ not (tool_endorsed (invocation_tool I)))

/-!
## Initial State

The system starts with only root_agent active. Root holds all capabilities (it's the
authority from which all permissions flow). Everything else is empty: no children,
no taint, no in-flight invocations, no registered tools.
-/
after_init {
  agent_active A := decide (A = root_agent);
  agent_parent A B := false;
  agent_cap A C := decide (A = root_agent);
  taint_levels A L := false;
  in_flight A I := false;
  tool_registered T := false;
  gh_taint_invoked A L := false;
  gh_taint_received A L := false
}

/-!
## Actions

The protocol has 9 actions. Each action has:
- **Parameters**: the inputs to the action
- **Preconditions** (`require`): conditions that must hold for the action to fire.
  If any require fails, the action is simply not taken (no error state).
- **State updates** (`:=`): how the mutable state changes. Veil's frame rule preserves
  any relation not explicitly mentioned.
-/

/-!
### register_tool: Add a tool to the system

Simply flips the `tool_registered` flag. All tool metadata (capabilities, egress kinds,
confidentiality floor, endorsement) is immutable background theory -- it exists
regardless of registration. Registration is a gate: invoke_start requires the tool
to be registered.
-/
action register_tool (tool : ToolId) {
  require not (tool_registered tool);
  tool_registered tool := true
}

/-!
### delegate: Create a child agent

A grantor (parent) creates a fresh child agent. The child starts with:
- Empty capabilities (must be granted individually via grant_capability)
- Empty taint set (the child has never seen any data)
- Empty in-flight set (no pending invocations)

The parent link `agent_parent grantee grantor` is established. The update to
`agent_parent` also cleans any stale entries involving the grantee ID (defense-in-depth,
since `not (agent_active grantee)` should mean no entries exist).
-/
action delegate (grantor grantee : AgentId) {
  require agent_active grantor;
  require not (agent_active grantee);
  require grantee != root_agent;
  agent_active grantee := true;
  agent_parent C P := decide $
    (C = grantee /\ P = grantor) \/ (agent_parent C P /\ C != grantee /\ P != grantee);
  agent_cap grantee C := false;
  taint_levels grantee L := false;
  in_flight grantee I := false;
  gh_taint_invoked grantee L := false;
  gh_taint_received grantee L := false
}

/-!
### grant_capability: Give a single capability to a child

Capabilities flow strictly downward: a parent can only grant capabilities it holds.
Separated from delegate for incremental proof -- each grant independently verifies
the parent holds the capability, which directly supports the capability_subsumption safety.
-/
action grant_capability (prnt child : AgentId) (cap : CapKind) {
  require agent_active prnt;
  require agent_active child;
  require agent_parent child prnt;
  require agent_cap prnt cap;
  agent_cap N C := decide $ (N = child /\ C = cap) \/ (agent_cap N C)
}

/-!
### revoke: Remove a child agent (direct parent action)

Parent removes a direct child. All state for the target is cleaned: deactivated,
parent link removed, capabilities cleared, taint cleared, in-flight cleared.

This is a "hard stop" -- any in-flight tool executions for the revoked agent are
effectively aborted (the runtime layer handles this).
-/
action revoke (prnt target : AgentId) {
  require agent_parent target prnt;
  require agent_active prnt;
  require agent_active target;
  require target != root_agent;
  agent_active target := false;
  agent_parent C P := decide $ agent_parent C P /\ C != target;
  agent_cap target C := false;
  taint_levels target L := false;
  in_flight target I := false;
  gh_taint_invoked target L := false;
  gh_taint_received target L := false
}

/-!
### cascade_revoke: Propagate revocation down the tree

When a parent is revoked, its children become orphans. cascade_revoke fires for each
orphaned child (child's parent is inactive). This ensures no agent survives in the tree
without an active parent.

Separated from revoke because the precondition is different: revoke requires the parent
to be ACTIVE (it's choosing to remove the child), while cascade_revoke requires the
parent to be INACTIVE (the child is being cleaned up because its parent is gone).

**Transient window safety**: Between revoke and cascade_revoke, orphaned agents are
active with a dead parent. This is safe: return_endorsed and return_unendorsed both
require `agent_active prnt`, so orphans cannot escalate taint upward. grant_capability
requires an active parent, so orphans cannot gain new permissions. flow_confinement and
default_deny hold independently of parent liveness. The orphan is in a sealed subtree --
it can do work but cannot communicate upward or acquire new capabilities.

**Runtime contract**: cascade_revoke SHOULD fire promptly after revoke to avoid wasted
computation in orphaned subtrees. Safety does not depend on promptness.
-/
action cascade_revoke (child prnt : AgentId) {
  require agent_parent child prnt;
  require not (agent_active prnt);
  require agent_active child;
  require child != root_agent;
  agent_active child := false;
  agent_parent C P := decide $ agent_parent C P /\ C != child;
  agent_cap child C := false;
  taint_levels child L := false;
  in_flight child I := false;
  gh_taint_invoked child L := false;
  gh_taint_received child L := false
}

/-!
### invoke_start: The three-check authorization gate

This is the core action of the protocol. An agent requests to invoke a tool, and the
protocol evaluates three independent checks. If all pass, the invocation is marked
as in-flight.

**Preconditions**: Agent must be active, non-root (root orchestrates but doesn't invoke),
tool must be registered, and the invocation ID must be fresh (not used by any agent).

**Check 1 -- Capability gate**: The agent holds every capability the tool requires.
Simple set containment.

**Check 2 -- Flow gate**: The graduated flow enforcement check. Three sub-checks ensure
flow confinement holds for all combinations of taint and egress:

- **2a**: For each existing speculative taint level and each egress kind of the new tool,
  the flow policy must allow it (ALLOW, INSPECT+pass, or override).
- **2b**: For each already in-flight tool's egress and the new tool's potential taint,
  the flow policy must allow it. This is the "reverse direction" -- the new tool's
  taint could violate existing in-flight tools' egress.
- **2c**: The new tool's own taint against its own egress (self-flow). If it's
  non-endorsed and has egress, the flow policy must permit the combination.

**Check 3 -- Authorizer gate**: The external policy engine authorizes (agent, tool).

Only after all three checks pass does the invocation become in-flight.
-/
action invoke_start (a : AgentId) (tool : ToolId) (inv : InvocationId) {
  require agent_active a;
  require a != root_agent;
  require tool_registered tool;
  require invocation_tool inv = tool;
  require forall AG, not (in_flight AG inv);
  -- CHECK 1: Capability gate
  require forall C, tool_cap tool C -> agent_cap a C;
  -- CHECK 2a: Flow gate (existing speculative taint x new tool's egress)
  require forall L E,
    speculative_taint a L /\ tool_egress tool E ->
      flow_allows L E
      \/ (flow_inspects L E /\ content_gate_passes a tool)
      \/ flow_override a tool L;
  -- CHECK 2b: Flow gate (new tool's taint x existing in-flight's egress)
  require forall I E,
    in_flight a I /\ tool_egress (invocation_tool I) E
    /\ not (tool_endorsed tool) ->
      flow_allows (tool_conf_floor tool) E
      \/ (flow_inspects (tool_conf_floor tool) E
          /\ content_gate_passes a (invocation_tool I))
      \/ flow_override a (invocation_tool I) (tool_conf_floor tool);
  -- CHECK 2c: Self-flow gate (tool's own taint x its own egress)
  require forall E,
    not (tool_endorsed tool) /\ tool_egress tool E ->
      flow_allows (tool_conf_floor tool) E
      \/ (flow_inspects (tool_conf_floor tool) E /\ content_gate_passes a tool)
      \/ flow_override a tool (tool_conf_floor tool);
  -- CHECK 3: Authorizer gate
  require authorizer_allows a tool;
  in_flight a inv := true
}

/-!
### invoke_complete: Tool execution finished

The tool has returned a result. Two things happen:
1. The invocation is removed from the in-flight set
2. If the tool is NOT endorsed, the agent acquires taint at the tool's confidentiality
   floor level. Endorsed tools produce bounded output and don't add taint.

The ghost relation `gh_taint_invoked` mirrors the taint update to track that this
taint came from an invocation (needed for taint_integrity safety).
-/
action invoke_complete (a : AgentId) (inv : InvocationId) {
  require in_flight a inv;
  require agent_active a;
  in_flight a inv := false;
  taint_levels A L := decide $
    taint_levels A L
    \/ (A = a /\ not (tool_endorsed (invocation_tool inv))
        /\ tool_conf_floor (invocation_tool inv) = L);
  gh_taint_invoked A L := decide $
    gh_taint_invoked A L
    \/ (A = a /\ not (tool_endorsed (invocation_tool inv))
        /\ tool_conf_floor (invocation_tool inv) = L)
}

/-!
### return_endorsed: Child returns a bounded result to parent

The child has finished all its work (no in-flight invocations) and returns an endorsed
result to its parent. Because the result has a bounded output schema (boolean, enum,
bounded integer), it carries at most a few bits of information and does NOT propagate
taint to the parent. The parent's taint set is unchanged.

This is a pure guard action -- it verifies the structural preconditions but makes no
state changes.
-/
action return_endorsed (child prnt : AgentId) {
  require agent_parent child prnt;
  require agent_active child;
  require agent_active prnt;
  require forall I, not (in_flight child I);
  pure ()
}

/-!
### return_unendorsed: Child returns an unbounded result to parent

The child returns a non-endorsed result (arbitrary text, data, etc.). The parent
inherits the child's entire taint set via set union. This is conservative but prevents
taint laundering: without this, a parent could delegate to a child, have the child
read sensitive data, and receive it back without acquiring taint.

Additional precondition: the incoming taint from the child must be compatible with all
of the parent's in-flight invocations. For each (child taint level, parent in-flight
egress) pair, the flow policy must permit it (ALLOW, INSPECT+content_gate, or override).
This is structurally identical to invoke_start's Check 2a but evaluated at receive time
against the child's actual taint. The parent can remain busy -- the return only blocks
when there is a genuine flow conflict.

The ghost relation `gh_taint_received` tracks that this taint came from a child return
(needed for taint_integrity safety).
-/
action return_unendorsed (child prnt : AgentId) {
  require agent_parent child prnt;
  require agent_active child;
  require agent_active prnt;
  require forall I, not (in_flight child I);
  -- Flow gate: incoming taint must be compatible with parent's in-flight tools
  require forall L I E,
    taint_levels child L /\ in_flight prnt I /\ tool_egress (invocation_tool I) E ->
      flow_allows L E
      \/ (flow_inspects L E /\ content_gate_passes prnt (invocation_tool I))
      \/ flow_override prnt (invocation_tool I) L;
  taint_levels A L := decide $
    taint_levels A L \/ (A = prnt /\ taint_levels child L);
  gh_taint_received A L := decide $
    gh_taint_received A L \/ (A = prnt /\ taint_levels child L)
}

/-!
## Safety Properties

These are the properties we prove hold in ALL reachable states. Veil verifies them
inductively: they hold in the initial state, and every action preserves them (given
the strengthening invariants).
-/

/-!
**root_always_active**: The root agent can never be deactivated. This is trivially
preserved because no action can deactivate root (revoke and cascade_revoke both
require `target != root_agent`).
-/
safety [root_always_active]
  agent_active root_agent

/-!
**default_deny**: If a tool invocation is in-flight, then it was explicitly authorized.
Specifically: the authorizer allowed (agent, tool) AND the agent holds every capability
the tool requires. This is the "no unauthorized access" property.
-/
safety [default_deny]
  in_flight A I ->
    authorizer_allows A (invocation_tool I)
    /\ (forall C, tool_cap (invocation_tool I) C -> agent_cap A C)

/-!
**flow_confinement**: The core information flow property. If an agent carries taint at
level L, has an in-flight invocation of a tool with egress kind E, then the flow policy
permits (L, E) -- either via ALLOW, INSPECT+content_gate_passes, or a scoped override.

This is the Lethal Trifecta defense: a tainted agent (private data exposure) cannot
reach an egress channel (external communication) unless the flow policy explicitly permits it.
-/
safety [flow_confinement]
  taint_levels A L /\ in_flight A I /\ tool_egress (invocation_tool I) E ->
    flow_allows L E
    \/ (flow_inspects L E /\ content_gate_passes A (invocation_tool I))
    \/ flow_override A (invocation_tool I) L

/-!
**flow_confinement_weak**: Oracle-independent flow safety. If an agent carries taint at
level L and has an in-flight invocation with egress kind E, then the (L, E) pair must be
in ALLOW or INSPECT mode, or have a scoped override. DENY-mode pairs are structurally
blocked regardless of oracle behavior.

This is strictly weaker than flow_confinement (drops the content_gate_passes requirement).
It proves that the operator controls the blast radius of content gate failure: only
INSPECT-mode channels depend on oracle correctness. DENY channels are oracle-free.
-/
safety [flow_confinement_weak]
  taint_levels A L /\ in_flight A I /\ tool_egress (invocation_tool I) E ->
    flow_allows L E
    \/ flow_inspects L E
    \/ flow_override A (invocation_tool I) L

/-!
**capability_subsumption**: For any active parent-child pair, the child's capabilities
are a subset of the parent's. Capabilities only flow downward.
-/
safety [capability_subsumption]
  agent_parent C P /\ agent_active C /\ agent_active P ->
    forall Cap, agent_cap C Cap -> agent_cap P Cap

/-!
**revocation_clean**: Inactive agents leave no residue. If an agent is not active,
it has no in-flight invocations and no taint. This ensures revocation is complete --
no "zombie" state persists after an agent is removed.
-/
safety [revocation_clean]
  not (agent_active A) -> not (in_flight A I) /\ not (taint_levels A L)

/-!
**taint_integrity**: Taint doesn't appear from nowhere. If an active agent has taint
at level L, it's because either:
- The agent completed a non-endorsed tool invocation at that level (gh_taint_invoked), OR
- The agent received an unendorsed return from a tainted child (gh_taint_received)

This proves the taint tracking is sound -- no "phantom taint" can appear.
-/
safety [taint_integrity]
  taint_levels A L /\ agent_active A ->
    gh_taint_invoked A L \/ gh_taint_received A L

/-!
## Strengthening Invariants

These are auxiliary invariants that aren't directly interesting as safety properties
but are needed to make the inductive proof go through. Each one eliminates a
"counterexample to induction" (CTI) -- a state that satisfies the invariants but
where some action could produce a state violating a safety property.

The SMT solver discovers CTIs automatically. The human's job is to add invariants
that rule out the unreachable states the CTIs exploit.
-/

-- Tree well-formedness: the parent relation is consistent with active status
invariant [parent_implies_active] agent_parent C P -> agent_active C
invariant [single_parent] agent_parent C P1 /\ agent_parent C P2 /\ agent_active C -> P1 = P2
invariant [no_self_parent] agent_parent A A = false
invariant [root_no_parent] agent_parent root_agent P = false

-- In-flight well-formedness: invocations only exist for active agents with registered tools
invariant [in_flight_active] in_flight A I -> agent_active A
invariant [in_flight_registered] in_flight A I -> tool_registered (invocation_tool I)
invariant [in_flight_unique] in_flight A1 I /\ in_flight A2 I -> A1 = A2

-- Root properties: root holds all capabilities and never invokes tools directly
invariant [root_all_caps] agent_cap root_agent C = true
invariant [root_no_in_flight] in_flight root_agent I = false

-- Ghost soundness: ghost tracking relations stay in sync with taint_levels.
-- If a ghost relation says taint exists but taint_levels disagrees, the agent must be inactive
-- (revocation cleared taint_levels but we don't bother clearing ghost relations for inactive agents).
invariant [ghost_invoked_sound]
  gh_taint_invoked A L -> taint_levels A L \/ not (agent_active A)
invariant [ghost_received_sound]
  gh_taint_received A L -> taint_levels A L \/ not (agent_active A)

-- In-flight flow compatibility: any two concurrent in-flight invocations for the same
-- agent must be mutually compatible under the flow policy. If tool I1 is non-endorsed
-- (will produce taint at its conf floor), and tool I2 has egress, the policy must permit
-- (conf_floor(I1), egress(I2)). Without this, invoke_complete for I1 could create taint
-- that violates flow_confinement for the still-in-flight I2.
invariant [in_flight_flow_compat]
  in_flight A I1 /\ in_flight A I2
  /\ not (tool_endorsed (invocation_tool I1))
  /\ tool_egress (invocation_tool I2) E ->
    flow_allows (tool_conf_floor (invocation_tool I1)) E
    \/ (flow_inspects (tool_conf_floor (invocation_tool I1)) E
        /\ content_gate_passes A (invocation_tool I2))
    \/ flow_override A (invocation_tool I2) (tool_conf_floor (invocation_tool I1))

/-!
## Verification

`#gen_spec` finalizes the Veil specification (assembles Init + Next into a relational
transition system). `#check_invariants` sends all verification conditions to the SMT
solver (cvc5) and reports results.

Known limitation: `#gen_spec` produces cosmetic `LawfulFieldRepresentation` synthesis
errors in the RTS definition. These are a Veil 2.0 framework bug (header-first
elaboration can't synthesize trivial IsSubStateOf proofs). They do not affect verification
-- `#check_invariants` uses a separate code path and all VCs pass.
-/

set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 1000000
set_option pp.deepTerms false
set_option pp.proofs false
#time #gen_spec

#check_invariants

end TzimtzumV2
