(** Typed Concrete Specification for TzimtzumV2.3
    Uses BTreeAxioms (axiomatized BTreeMap/BTreeSet) to model the Rust
    kernel's state. This bridges the gap between the abstract function-based
    spec (TzimtzumV2.v) and the actual Rust implementation without requiring
    rocq-of-rust extraction link files.

    ANY BTreeMap/BTreeSet-based implementation whose transitions match these
    definitions correctly implements the abstract specification. *)

From Stdlib Require Import Bool.
Require Import ArgusKernel.axioms.BTreeAxioms.
Require Import ArgusKernel.axioms.DecidableAxioms.
Require Import ArgusKernel.axioms.OracleAxioms.
Require Import ArgusKernel.spec.TzimtzumV2.

(** ================================================================ *)
(** Concrete State (mirrors Rust KernelState)                         *)
(** ================================================================ *)

Record ConcreteState := mkCState {
  c_agent_active      : BTreeSet.t AgentId;
  c_agent_parent      : BTreeMap.t AgentId AgentId;
  c_agent_cap         : BTreeMap.t AgentId (BTreeSet.t CapKind);
  c_taint_levels      : BTreeMap.t AgentId (BTreeSet.t ConfLevel);
  c_in_flight         : BTreeMap.t AgentId (BTreeSet.t InvocationId);
  c_invocation_tool   : BTreeMap.t InvocationId ToolId;
  c_tool_registered   : BTreeSet.t ToolId;
  c_gh_taint_invoked  : BTreeMap.t AgentId (BTreeSet.t ConfLevel);
  c_gh_taint_received : BTreeMap.t AgentId (BTreeSet.t ConfLevel)
}.

(** CapKind is an uninterpreted sort, so we axiomatize a set of all
    capabilities for root's initial state. *)
Parameter all_caps_set : BTreeSet.t CapKind.
Axiom all_caps_mem : forall c, BTreeSet.mem c all_caps_set = true.

(** ================================================================ *)
(** Initial Concrete State                                            *)
(** ================================================================ *)

Definition c_initial_state : ConcreteState := mkCState
  (BTreeSet.insert root_agent BTreeSet.empty)
  BTreeMap.empty
  (BTreeMap.insert root_agent all_caps_set BTreeMap.empty)
  BTreeMap.empty
  BTreeMap.empty
  BTreeMap.empty
  BTreeSet.empty
  BTreeMap.empty
  BTreeMap.empty.

(** ================================================================ *)
(** Shorthand notations for nested operations                         *)
(** ================================================================ *)

Definition mem_agent_cap :=
  BTreeMap.mem_nested AgentId CapKind.
Definition mem_taint :=
  BTreeMap.mem_nested AgentId ConfLevel.
Definition mem_in_flight :=
  BTreeMap.mem_nested AgentId InvocationId.

Definition insert_cap :=
  BTreeMap.insert_nested AgentId CapKind.
Definition insert_taint :=
  BTreeMap.insert_nested AgentId ConfLevel.
Definition insert_in_flight :=
  BTreeMap.insert_nested AgentId InvocationId.

Definition union_taint :=
  BTreeMap.union_nested AgentId ConfLevel.

Definition remove_cap :=
  BTreeMap.remove_key_nested AgentId CapKind.
Definition remove_taint :=
  BTreeMap.remove_key_nested AgentId ConfLevel.
Definition remove_in_flight :=
  BTreeMap.remove_key_nested AgentId InvocationId.
Definition remove_gh_invoked :=
  BTreeMap.remove_key_nested AgentId ConfLevel.
Definition remove_gh_received :=
  BTreeMap.remove_key_nested AgentId ConfLevel.

(** ================================================================ *)
(** Concrete Transitions                                              *)
(** ================================================================ *)

(** register_tool: flip tool_registered flag *)
Definition c_register_tool (st : ConcreteState) (tool : ToolId)
    : option ConcreteState :=
  if BTreeSet.mem tool (c_tool_registered st) then None
  else Some (mkCState
    (c_agent_active st)
    (c_agent_parent st)
    (c_agent_cap st)
    (c_taint_levels st)
    (c_in_flight st)
    (c_invocation_tool st)
    (BTreeSet.insert tool (c_tool_registered st))
    (c_gh_taint_invoked st)
    (c_gh_taint_received st)).

(** delegate: grantor creates child grantee with empty state *)
Definition c_delegate (st : ConcreteState)
    (grantor grantee : AgentId) : option ConcreteState :=
  if negb (BTreeSet.mem grantor (c_agent_active st)) then None
  else if BTreeSet.mem grantee (c_agent_active st) then None
  else if AgentId_eq_dec grantee root_agent then None
  else Some (mkCState
    (BTreeSet.insert grantee (c_agent_active st))
    (BTreeMap.insert grantee grantor
      (BTreeMap.remove_by_value grantee (BTreeMap.remove grantee (c_agent_parent st))))
    (BTreeMap.remove grantee (c_agent_cap st))
    (BTreeMap.remove grantee (c_taint_levels st))
    (BTreeMap.remove grantee (c_in_flight st))
    (c_invocation_tool st)
    (c_tool_registered st)
    (BTreeMap.remove grantee (c_gh_taint_invoked st))
    (BTreeMap.remove grantee (c_gh_taint_received st))).

(** grant_capability: parent grants a single cap to direct child *)
Definition c_grant_capability (st : ConcreteState)
    (prnt child : AgentId) (cap : CapKind) : option ConcreteState :=
  if negb (BTreeSet.mem prnt (c_agent_active st)) then None
  else if negb (BTreeSet.mem child (c_agent_active st)) then None
  else if negb (match BTreeMap.get child (c_agent_parent st) with
                | Some p => if AgentId_eq_dec p prnt then true else false
                | None => false
                end) then None
  else if negb (mem_agent_cap prnt cap (c_agent_cap st)) then None
  else Some (mkCState
    (c_agent_active st)
    (c_agent_parent st)
    (insert_cap child cap (c_agent_cap st))
    (c_taint_levels st)
    (c_in_flight st)
    (c_invocation_tool st)
    (c_tool_registered st)
    (c_gh_taint_invoked st)
    (c_gh_taint_received st)).

(** revoke: parent removes a direct child *)
Definition c_revoke (st : ConcreteState)
    (prnt target : AgentId) : option ConcreteState :=
  if negb (match BTreeMap.get target (c_agent_parent st) with
           | Some p => if AgentId_eq_dec p prnt then true else false
           | None => false
           end) then None
  else if negb (BTreeSet.mem prnt (c_agent_active st)) then None
  else if negb (BTreeSet.mem target (c_agent_active st)) then None
  else if AgentId_eq_dec target root_agent then None
  else Some (mkCState
    (BTreeSet.remove target (c_agent_active st))
    (BTreeMap.remove target (c_agent_parent st))
    (BTreeMap.remove target (c_agent_cap st))
    (BTreeMap.remove target (c_taint_levels st))
    (BTreeMap.remove target (c_in_flight st))
    (c_invocation_tool st)
    (c_tool_registered st)
    (BTreeMap.remove target (c_gh_taint_invoked st))
    (BTreeMap.remove target (c_gh_taint_received st))).

(** cascade_revoke: orphan cleanup -- child's parent is inactive *)
Definition c_cascade_revoke (st : ConcreteState)
    (child prnt : AgentId) : option ConcreteState :=
  if negb (match BTreeMap.get child (c_agent_parent st) with
           | Some p => if AgentId_eq_dec p prnt then true else false
           | None => false
           end) then None
  else if BTreeSet.mem prnt (c_agent_active st) then None
  else if negb (BTreeSet.mem child (c_agent_active st)) then None
  else if AgentId_eq_dec child root_agent then None
  else Some (mkCState
    (BTreeSet.remove child (c_agent_active st))
    (BTreeMap.remove child (c_agent_parent st))
    (BTreeMap.remove child (c_agent_cap st))
    (BTreeMap.remove child (c_taint_levels st))
    (BTreeMap.remove child (c_in_flight st))
    (c_invocation_tool st)
    (c_tool_registered st)
    (BTreeMap.remove child (c_gh_taint_invoked st))
    (BTreeMap.remove child (c_gh_taint_received st))).

(** invoke_start: precondition (Prop) + state transform.
    The key difference from abstract: invocation_tool is MUTABLE here. *)
Definition c_invoke_start_pre (st : ConcreteState)
    (a : AgentId) (tool : ToolId) (inv : InvocationId) : Prop :=
  BTreeSet.mem a (c_agent_active st) = true
  /\ a <> root_agent
  /\ BTreeSet.mem tool (c_tool_registered st) = true
  /\ BTreeMap.get inv (c_invocation_tool st) = None
  /\ (forall ag, mem_in_flight ag inv (c_in_flight st) = false)
  /\ (forall c, tool_cap tool c = true ->
        mem_agent_cap a c (c_agent_cap st) = true)
  /\ (forall l e,
        (mem_taint a l (c_taint_levels st) = true
         \/ (exists I, mem_in_flight a I (c_in_flight st) = true
             /\ tool_conf_floor (invocation_tool I) = l
             /\ tool_endorsed (invocation_tool I) = false)) ->
        tool_egress tool e = true ->
        flow_allowed a tool l e = true)
  /\ (forall i e,
        mem_in_flight a i (c_in_flight st) = true ->
        tool_egress (invocation_tool i) e = true ->
        tool_endorsed tool = false ->
        flow_allowed a (invocation_tool i) (tool_conf_floor tool) e = true)
  /\ (forall e,
        tool_endorsed tool = false ->
        tool_egress tool e = true ->
        flow_allowed a tool (tool_conf_floor tool) e = true)
  /\ authorizer_allows a tool = true.

Definition c_invoke_start_state (st : ConcreteState)
    (a : AgentId) (tool : ToolId) (inv : InvocationId) : ConcreteState :=
  mkCState
    (c_agent_active st)
    (c_agent_parent st)
    (c_agent_cap st)
    (c_taint_levels st)
    (insert_in_flight a inv (c_in_flight st))
    (BTreeMap.insert inv tool (c_invocation_tool st))
    (c_tool_registered st)
    (c_gh_taint_invoked st)
    (c_gh_taint_received st).

(** invoke_complete: tool returns, invocation leaves in-flight set *)
Definition c_invoke_complete (st : ConcreteState)
    (a : AgentId) (inv : InvocationId) : option ConcreteState :=
  if negb (mem_in_flight a inv (c_in_flight st)) then None
  else if negb (BTreeSet.mem a (c_agent_active st)) then None
  else
    match BTreeMap.get inv (c_invocation_tool st) with
    | None => None
    | Some tool =>
      let add_taint := negb (tool_endorsed tool) in
      let floor := tool_conf_floor tool in
      let new_taint :=
        if add_taint then insert_taint a floor (c_taint_levels st)
        else c_taint_levels st in
      let new_in_flight :=
        match BTreeMap.get a (c_in_flight st) with
        | Some s => BTreeMap.insert a (BTreeSet.remove inv s) (c_in_flight st)
        | None => c_in_flight st
        end in
      let new_gh :=
        if add_taint then insert_taint a floor (c_gh_taint_invoked st)
        else c_gh_taint_invoked st in
      Some (mkCState
        (c_agent_active st)
        (c_agent_parent st)
        (c_agent_cap st)
        new_taint
        new_in_flight
        (c_invocation_tool st)
        (c_tool_registered st)
        new_gh
        (c_gh_taint_received st))
    end.

(** return_endorsed: pure guard, no state change *)
Definition c_return_endorsed_pre (st : ConcreteState)
    (child prnt : AgentId) : Prop :=
  match BTreeMap.get child (c_agent_parent st) with
  | Some p => p = prnt
  | None => False
  end
  /\ BTreeSet.mem child (c_agent_active st) = true
  /\ BTreeSet.mem prnt (c_agent_active st) = true
  /\ (forall i, mem_in_flight child i (c_in_flight st) = false).

(** return_unendorsed: child taint propagates to parent *)
Definition c_return_unendorsed_pre (st : ConcreteState)
    (child prnt : AgentId) : Prop :=
  match BTreeMap.get child (c_agent_parent st) with
  | Some p => p = prnt
  | None => False
  end
  /\ BTreeSet.mem child (c_agent_active st) = true
  /\ BTreeSet.mem prnt (c_agent_active st) = true
  /\ (forall i, mem_in_flight child i (c_in_flight st) = false)
  /\ (forall l i e,
        mem_taint child l (c_taint_levels st) = true ->
        mem_in_flight prnt i (c_in_flight st) = true ->
        tool_egress (invocation_tool i) e = true ->
        flow_allowed prnt (invocation_tool i) l e = true).

Definition c_return_unendorsed_state (st : ConcreteState)
    (child prnt : AgentId) : ConcreteState :=
  let child_taint :=
    match BTreeMap.get child (c_taint_levels st) with
    | Some s => s
    | None => BTreeSet.empty
    end in
  mkCState
    (c_agent_active st)
    (c_agent_parent st)
    (c_agent_cap st)
    (union_taint prnt child_taint (c_taint_levels st))
    (c_in_flight st)
    (c_invocation_tool st)
    (c_tool_registered st)
    (c_gh_taint_invoked st)
    (union_taint prnt child_taint (c_gh_taint_received st)).

(** ================================================================ *)
(** Step Relation and Reachability                                    *)
(** ================================================================ *)

Inductive c_step : ConcreteState -> ConcreteState -> Prop :=
  | c_step_register_tool : forall st st' tool,
      c_register_tool st tool = Some st' -> c_step st st'
  | c_step_delegate : forall st st' grantor grantee,
      c_delegate st grantor grantee = Some st' -> c_step st st'
  | c_step_grant_capability : forall st st' prnt child cap,
      c_grant_capability st prnt child cap = Some st' -> c_step st st'
  | c_step_revoke : forall st st' prnt target,
      c_revoke st prnt target = Some st' -> c_step st st'
  | c_step_cascade_revoke : forall st st' child prnt,
      c_cascade_revoke st child prnt = Some st' -> c_step st st'
  | c_step_invoke_start : forall st a tool inv,
      c_invoke_start_pre st a tool inv ->
      c_step st (c_invoke_start_state st a tool inv)
  | c_step_invoke_complete : forall st st' a inv,
      c_invoke_complete st a inv = Some st' -> c_step st st'
  | c_step_return_endorsed : forall st child prnt,
      c_return_endorsed_pre st child prnt ->
      c_step st st
  | c_step_return_unendorsed : forall st child prnt,
      c_return_unendorsed_pre st child prnt ->
      c_step st (c_return_unendorsed_state st child prnt).

Inductive c_reachable : ConcreteState -> Prop :=
  | c_reach_init : c_reachable c_initial_state
  | c_reach_step : forall st st',
      c_reachable st -> c_step st st' -> c_reachable st'.

(** ================================================================ *)
(** Concrete Invariant: invocation_tool completeness                  *)
(** ================================================================ *)

Definition c_invocation_tool_complete (st : ConcreteState) : Prop :=
  forall a inv,
    mem_in_flight a inv (c_in_flight st) = true ->
    exists tool, BTreeMap.get inv (c_invocation_tool st) = Some tool.
