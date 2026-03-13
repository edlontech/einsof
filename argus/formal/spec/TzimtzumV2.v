(** TzimtzumV2.3: Tool Authorization Protocol Security Kernel
    Coq port of tzimtzum/TzimtzumV2.lean

    Architecture: Agents form a tree rooted at root_agent. Each agent carries
    capabilities (typed permissions), taint (confidentiality exposure), and
    in-flight invocations. Tools have immutable metadata. Every invocation
    passes through a three-check gate: capability, flow, and authorizer.

    This file defines:
    - Background theory (tool metadata, flow policy, oracles)
    - Mutable state record (KernelState)
    - Initial state
    - 9 actions as state transformers *)

From Stdlib Require Import Bool.
Require Import ArgusKernel.axioms.DecidableAxioms.
Require Import ArgusKernel.axioms.OracleAxioms.

(** --- Immutable Tool Metadata (Background Theory) ---
    Lean: lines 111-114. Declared at registration, never changes. *)

Parameter tool_cap : ToolId -> CapKind -> bool.
Parameter tool_egress : ToolId -> EgressKind -> bool.
Parameter tool_conf_floor : ToolId -> ConfLevel.
Parameter tool_endorsed : ToolId -> bool.

(** Lean: line 173. Maps each invocation ID to its tool.
    Immutable in the abstract spec -- the binding is part of background theory.
    The Rust implementation stores this mutably; the refinement bridge resolves
    this gap. *)
Parameter invocation_tool : InvocationId -> ToolId.

(** --- Immutable Flow Policy ---
    Lean: lines 141-145. Three modes: ALLOW, INSPECT, DENY.
    Encoded as two Bool relations with mutual exclusivity axiom. *)

Parameter flow_allows : ConfLevel -> EgressKind -> bool.
Parameter flow_inspects : ConfLevel -> EgressKind -> bool.
Parameter flow_override : AgentId -> ToolId -> ConfLevel -> bool.

Axiom flow_exclusive : forall L E,
  flow_allows L E = true -> flow_inspects L E = false.

(** --- Mutable State ---
    Lean: lines 168-176. Function-based representation matching Veil DSL.
    Each field is a total function returning bool (membership predicate). *)

Record KernelState := mkState {
  agent_active : AgentId -> bool;
  agent_parent : AgentId -> AgentId -> bool;
  agent_cap : AgentId -> CapKind -> bool;
  taint_levels : AgentId -> ConfLevel -> bool;
  in_flight : AgentId -> InvocationId -> bool;
  tool_registered : ToolId -> bool;
  gh_taint_invoked : AgentId -> ConfLevel -> bool;
  gh_taint_received : AgentId -> ConfLevel -> bool
}.

(** --- Boolean equality helpers ---
    Wrapper around decidable equality for use in if-then-else. *)

Definition beq_agent (x y : AgentId) : bool :=
  if AgentId_eq_dec x y then true else false.
Definition beq_tool (x y : ToolId) : bool :=
  if ToolId_eq_dec x y then true else false.
Definition beq_inv (x y : InvocationId) : bool :=
  if InvocationId_eq_dec x y then true else false.
Definition beq_cap (x y : CapKind) : bool :=
  if CapKind_eq_dec x y then true else false.
Definition beq_conf (x y : ConfLevel) : bool :=
  if ConfLevel_eq_dec x y then true else false.
Definition beq_egress (x y : EgressKind) : bool :=
  if EgressKind_eq_dec x y then true else false.

(** --- Lemmas for boolean equality reflection --- *)

Lemma beq_agent_refl : forall a, beq_agent a a = true.
Proof. intros. unfold beq_agent. destruct (AgentId_eq_dec a a); [reflexivity | contradiction]. Qed.

Lemma beq_agent_true : forall a b, beq_agent a b = true -> a = b.
Proof. intros. unfold beq_agent in H. destruct (AgentId_eq_dec a b); [auto | discriminate]. Qed.

Lemma beq_agent_false : forall a b, beq_agent a b = false -> a <> b.
Proof. intros. unfold beq_agent in H. destruct (AgentId_eq_dec a b); [discriminate | auto]. Qed.

Lemma beq_agent_neq : forall a b, a <> b -> beq_agent a b = false.
Proof. intros. unfold beq_agent. destruct (AgentId_eq_dec a b); [contradiction | reflexivity]. Qed.

Lemma beq_inv_refl : forall i, beq_inv i i = true.
Proof. intros. unfold beq_inv. destruct (InvocationId_eq_dec i i); [reflexivity | contradiction]. Qed.

Lemma beq_conf_refl : forall l, beq_conf l l = true.
Proof. intros. unfold beq_conf. destruct (ConfLevel_eq_dec l l); [reflexivity | contradiction]. Qed.

Lemma beq_cap_refl : forall c, beq_cap c c = true.
Proof. intros. unfold beq_cap. destruct (CapKind_eq_dec c c); [reflexivity | contradiction]. Qed.

Lemma beq_tool_refl : forall t, beq_tool t t = true.
Proof. intros. unfold beq_tool. destruct (ToolId_eq_dec t t); [reflexivity | contradiction]. Qed.

Lemma beq_tool_true : forall a b, beq_tool a b = true -> a = b.
Proof. intros. unfold beq_tool in H. destruct (ToolId_eq_dec a b); [auto | discriminate]. Qed.

Lemma beq_inv_true : forall a b, beq_inv a b = true -> a = b.
Proof. intros. unfold beq_inv in H. destruct (InvocationId_eq_dec a b); [auto | discriminate]. Qed.

Lemma beq_inv_neq : forall a b, a <> b -> beq_inv a b = false.
Proof. intros. unfold beq_inv. destruct (InvocationId_eq_dec a b); [contradiction | reflexivity]. Qed.

Lemma beq_cap_true : forall a b, beq_cap a b = true -> a = b.
Proof. intros. unfold beq_cap in H. destruct (CapKind_eq_dec a b); [auto | discriminate]. Qed.

Lemma beq_cap_neq : forall a b, a <> b -> beq_cap a b = false.
Proof. intros. unfold beq_cap. destruct (CapKind_eq_dec a b); [contradiction | reflexivity]. Qed.

Lemma beq_conf_true : forall a b, beq_conf a b = true -> a = b.
Proof. intros. unfold beq_conf in H. destruct (ConfLevel_eq_dec a b); [auto | discriminate]. Qed.

Lemma beq_conf_neq : forall a b, a <> b -> beq_conf a b = false.
Proof. intros. unfold beq_conf. destruct (ConfLevel_eq_dec a b); [contradiction | reflexivity]. Qed.

(** --- Speculative Taint (Derived Predicate) ---
    Lean: lines 227-231. Worst-case taint including in-flight non-endorsed tools.
    Prop-level because InvocationId is uninterpreted (cannot enumerate). *)

Definition speculative_taint (st : KernelState) (a : AgentId) (l : ConfLevel) : Prop :=
  taint_levels st a l = true
  \/ (exists I, in_flight st a I = true
      /\ tool_conf_floor (invocation_tool I) = l
      /\ tool_endorsed (invocation_tool I) = false).

(** --- Initial State ---
    Lean: lines 240-249. Only root_agent active, root holds all capabilities,
    everything else empty. *)

Definition initial_state : KernelState := mkState
  (fun a => beq_agent a root_agent)
  (fun _ _ => false)
  (fun a _ => beq_agent a root_agent)
  (fun _ _ => false)
  (fun _ _ => false)
  (fun _ => false)
  (fun _ _ => false)
  (fun _ _ => false).

(** --- Flow Allowed Helper ---
    Matches Rust transitions.rs:11-24 and Lean's flow gate pattern.
    Three-way disjunction: ALLOW, INSPECT+content_gate, or override. *)

Definition flow_allowed (agent : AgentId) (tool : ToolId)
    (level : ConfLevel) (egress : EgressKind) : bool :=
  flow_allows level egress
  || (flow_inspects level egress && content_gate_passes agent tool)
  || flow_override agent tool level.

(** ================================================================ *)
(** --- Actions ---                                                   *)
(** ================================================================ *)

(** register_tool: Lean lines 270-273
    Flips tool_registered flag. Tool metadata is immutable background theory. *)

Definition register_tool (st : KernelState) (tool : ToolId)
    : option KernelState :=
  if tool_registered st tool then None
  else Some (mkState
    (agent_active st)
    (agent_parent st)
    (agent_cap st)
    (taint_levels st)
    (in_flight st)
    (fun t => if beq_tool t tool then true else tool_registered st t)
    (gh_taint_invoked st)
    (gh_taint_received st)).

(** delegate: Lean lines 287-299
    Grantor creates a fresh child. Child starts with empty caps, taint, in-flight.
    Stale parent entries involving grantee are cleared (defense-in-depth). *)

Definition delegate (st : KernelState) (grantor grantee : AgentId)
    : option KernelState :=
  if negb (agent_active st grantor) then None
  else if agent_active st grantee then None
  else if beq_agent grantee root_agent then None
  else Some (mkState
    (fun a => if beq_agent a grantee then true else agent_active st a)
    (fun c p =>
      if beq_agent c grantee && beq_agent p grantor then true
      else if beq_agent c grantee || beq_agent p grantee then false
      else agent_parent st c p)
    (fun a c => if beq_agent a grantee then false else agent_cap st a c)
    (fun a l => if beq_agent a grantee then false else taint_levels st a l)
    (fun a i => if beq_agent a grantee then false else in_flight st a i)
    (tool_registered st)
    (fun a l => if beq_agent a grantee then false else gh_taint_invoked st a l)
    (fun a l => if beq_agent a grantee then false else gh_taint_received st a l)).

(** grant_capability: Lean lines 308-314
    Parent grants a single capability it holds to a direct child.
    Capabilities flow strictly downward. *)

Definition grant_capability (st : KernelState)
    (prnt child : AgentId) (cap : CapKind) : option KernelState :=
  if negb (agent_active st prnt) then None
  else if negb (agent_active st child) then None
  else if negb (agent_parent st child prnt) then None
  else if negb (agent_cap st prnt cap) then None
  else Some (mkState
    (agent_active st)
    (agent_parent st)
    (fun a c =>
      if beq_agent a child && beq_cap c cap then true
      else agent_cap st a c)
    (taint_levels st)
    (in_flight st)
    (tool_registered st)
    (gh_taint_invoked st)
    (gh_taint_received st)).

(** revoke: Lean lines 325-337
    Parent removes a direct child. All state for target is cleared. *)

Definition revoke (st : KernelState) (prnt target : AgentId)
    : option KernelState :=
  if negb (agent_parent st target prnt) then None
  else if negb (agent_active st prnt) then None
  else if negb (agent_active st target) then None
  else if beq_agent target root_agent then None
  else Some (mkState
    (fun a => if beq_agent a target then false else agent_active st a)
    (fun c p => if beq_agent c target then false else agent_parent st c p)
    (fun a c => if beq_agent a target then false else agent_cap st a c)
    (fun a l => if beq_agent a target then false else taint_levels st a l)
    (fun a i => if beq_agent a target then false else in_flight st a i)
    (tool_registered st)
    (fun a l => if beq_agent a target then false else gh_taint_invoked st a l)
    (fun a l => if beq_agent a target then false else gh_taint_received st a l)).

(** cascade_revoke: Lean lines 360-372
    Orphan cleanup: child's parent is inactive, so child is removed.
    Identical to revoke except precondition checks parent is INactive. *)

Definition cascade_revoke (st : KernelState) (child prnt : AgentId)
    : option KernelState :=
  if negb (agent_parent st child prnt) then None
  else if agent_active st prnt then None
  else if negb (agent_active st child) then None
  else if beq_agent child root_agent then None
  else Some (mkState
    (fun a => if beq_agent a child then false else agent_active st a)
    (fun c p => if beq_agent c child then false else agent_parent st c p)
    (fun a c => if beq_agent a child then false else agent_cap st a c)
    (fun a l => if beq_agent a child then false else taint_levels st a l)
    (fun a i => if beq_agent a child then false else in_flight st a i)
    (tool_registered st)
    (fun a l => if beq_agent a child then false else gh_taint_invoked st a l)
    (fun a l => if beq_agent a child then false else gh_taint_received st a l)).

(** invoke_start: Lean lines 402-433
    Three-check authorization gate. Uses Prop-level preconditions because
    universal quantifiers over uninterpreted sorts are not decidable.
    Split into precondition (Prop) and state transform (pure function). *)

Definition invoke_start_pre (st : KernelState)
    (a : AgentId) (tool : ToolId) (inv : InvocationId) : Prop :=
  agent_active st a = true
  /\ a <> root_agent
  /\ tool_registered st tool = true
  /\ invocation_tool inv = tool
  /\ (forall ag, in_flight st ag inv = false)
  (** CHECK 1: Capability gate *)
  /\ (forall c, tool_cap tool c = true -> agent_cap st a c = true)
  (** CHECK 2a: Speculative taint x new tool's egress *)
  /\ (forall l e,
        speculative_taint st a l ->
        tool_egress tool e = true ->
        flow_allowed a tool l e = true)
  (** CHECK 2b: New tool's taint x existing in-flight tool's egress *)
  /\ (forall i e,
        in_flight st a i = true ->
        tool_egress (invocation_tool i) e = true ->
        tool_endorsed tool = false ->
        flow_allowed a (invocation_tool i) (tool_conf_floor tool) e = true)
  (** CHECK 2c: Self-flow (tool's own taint x its own egress) *)
  /\ (forall e,
        tool_endorsed tool = false ->
        tool_egress tool e = true ->
        flow_allowed a tool (tool_conf_floor tool) e = true)
  (** CHECK 3: Authorizer gate *)
  /\ authorizer_allows a tool = true.

Definition invoke_start_state (st : KernelState)
    (a : AgentId) (inv : InvocationId) : KernelState :=
  mkState
    (agent_active st)
    (agent_parent st)
    (agent_cap st)
    (taint_levels st)
    (fun ag i =>
      if beq_agent ag a && beq_inv i inv then true
      else in_flight st ag i)
    (tool_registered st)
    (gh_taint_invoked st)
    (gh_taint_received st).

(** invoke_complete: Lean lines 446-458
    Tool returns a result. Invocation leaves in-flight set.
    Non-endorsed tools add taint at their conf_floor level. *)

Definition invoke_complete (st : KernelState)
    (a : AgentId) (inv : InvocationId) : option KernelState :=
  if negb (in_flight st a inv) then None
  else if negb (agent_active st a) then None
  else
    let tool := invocation_tool inv in
    let add_taint := negb (tool_endorsed tool) in
    let floor := tool_conf_floor tool in
    Some (mkState
      (agent_active st)
      (agent_parent st)
      (agent_cap st)
      (fun ag l =>
        if beq_agent ag a && add_taint && beq_conf l floor
        then true
        else taint_levels st ag l)
      (fun ag i =>
        if beq_agent ag a && beq_inv i inv
        then false
        else in_flight st ag i)
      (tool_registered st)
      (fun ag l =>
        if beq_agent ag a && add_taint && beq_conf l floor
        then true
        else gh_taint_invoked st ag l)
      (gh_taint_received st)).

(** return_endorsed: Lean lines 471-477
    Child returns a bounded result to parent. No taint propagation.
    Pure guard action -- verifies preconditions, no state change. *)

Definition return_endorsed_pre (st : KernelState)
    (child prnt : AgentId) : Prop :=
  agent_parent st child prnt = true
  /\ agent_active st child = true
  /\ agent_active st prnt = true
  /\ (forall i, in_flight st child i = false).

(** return_unendorsed: Lean lines 497-512
    Child returns unbounded result. Parent inherits child's taint via set union.
    Flow gate: incoming taint must be compatible with parent's in-flight tools. *)

Definition return_unendorsed_pre (st : KernelState)
    (child prnt : AgentId) : Prop :=
  agent_parent st child prnt = true
  /\ agent_active st child = true
  /\ agent_active st prnt = true
  /\ (forall i, in_flight st child i = false)
  /\ (forall l i e,
        taint_levels st child l = true ->
        in_flight st prnt i = true ->
        tool_egress (invocation_tool i) e = true ->
        flow_allowed prnt (invocation_tool i) l e = true).

Definition return_unendorsed_state (st : KernelState)
    (child prnt : AgentId) : KernelState :=
  mkState
    (agent_active st)
    (agent_parent st)
    (agent_cap st)
    (fun a l =>
      if beq_agent a prnt && taint_levels st child l
      then true
      else taint_levels st a l)
    (in_flight st)
    (tool_registered st)
    (gh_taint_invoked st)
    (fun a l =>
      if beq_agent a prnt && taint_levels st child l
      then true
      else gh_taint_received st a l).

(** sentinel_elevate_taint: Sentinel adds taint at a given level.
    Precondition ensures flow compatibility with all in-flight tools. *)

Definition sentinel_elevate_taint_pre (st : KernelState)
    (a : AgentId) (l : ConfLevel) : Prop :=
  agent_active st a = true
  /\ (forall i e,
        in_flight st a i = true ->
        tool_egress (invocation_tool i) e = true ->
        flow_allowed a (invocation_tool i) l e = true).

Definition sentinel_elevate_taint_state (st : KernelState)
    (a : AgentId) (l : ConfLevel) : KernelState :=
  mkState
    (agent_active st)
    (agent_parent st)
    (agent_cap st)
    (fun ag lvl =>
      if beq_agent ag a && beq_conf lvl l then true
      else taint_levels st ag lvl)
    (in_flight st)
    (tool_registered st)
    (fun ag lvl =>
      if beq_agent ag a && beq_conf lvl l then true
      else gh_taint_invoked st ag lvl)
    (gh_taint_received st).
