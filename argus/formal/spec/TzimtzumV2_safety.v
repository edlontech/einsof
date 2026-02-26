(** TzimtzumV2.3 Safety Properties and Strengthening Invariants
    Ported from tzimtzum/TzimtzumV2.lean lines 514-645.

    Defines:
    - Step relation (one-step state transition via any of 9 actions)
    - Reachability (transitive closure from initial_state)
    - 7 safety properties
    - 12 strengthening invariants
    - Combined invariant bundle *)

From Stdlib Require Import Bool.
Require Import ArgusKernel.axioms.DecidableAxioms.
Require Import ArgusKernel.axioms.OracleAxioms.
Require Import ArgusKernel.spec.TzimtzumV2.

(** ================================================================ *)
(** Step Relation                                                     *)
(** ================================================================ *)

Inductive step : KernelState -> KernelState -> Prop :=
  | step_register_tool : forall st st' tool,
      register_tool st tool = Some st' -> step st st'
  | step_delegate : forall st st' grantor grantee,
      delegate st grantor grantee = Some st' -> step st st'
  | step_grant_capability : forall st st' prnt child cap,
      grant_capability st prnt child cap = Some st' -> step st st'
  | step_revoke : forall st st' prnt target,
      revoke st prnt target = Some st' -> step st st'
  | step_cascade_revoke : forall st st' child prnt,
      cascade_revoke st child prnt = Some st' -> step st st'
  | step_invoke_start : forall st a tool inv,
      invoke_start_pre st a tool inv ->
      step st (invoke_start_state st a inv)
  | step_invoke_complete : forall st st' a inv,
      invoke_complete st a inv = Some st' -> step st st'
  | step_return_endorsed : forall st child prnt,
      return_endorsed_pre st child prnt -> step st st
  | step_return_unendorsed : forall st child prnt,
      return_unendorsed_pre st child prnt ->
      step st (return_unendorsed_state st child prnt).

Inductive reachable : KernelState -> Prop :=
  | reach_init : reachable initial_state
  | reach_step : forall st st',
      reachable st -> step st st' -> reachable st'.

(** ================================================================ *)
(** Safety Properties (Lean lines 527-596)                            *)
(** ================================================================ *)

(** Safety 1: Root agent can never be deactivated.
    Trivially preserved: revoke and cascade_revoke require target != root. *)
Definition root_always_active (st : KernelState) : Prop :=
  agent_active st root_agent = true.

(** Safety 2: In-flight invocations were explicitly authorized.
    Authorizer allowed (agent, tool) AND agent holds all required capabilities. *)
Definition default_deny (st : KernelState) : Prop :=
  forall a i,
    in_flight st a i = true ->
    authorizer_allows a (invocation_tool i) = true
    /\ (forall c, tool_cap (invocation_tool i) c = true ->
         agent_cap st a c = true).

(** Safety 3: Tainted agent with in-flight egress tool implies flow policy permits.
    The Lethal Trifecta defense. *)
Definition flow_confinement (st : KernelState) : Prop :=
  forall a l i e,
    taint_levels st a l = true ->
    in_flight st a i = true ->
    tool_egress (invocation_tool i) e = true ->
    flow_allowed a (invocation_tool i) l e = true.

(** Safety 4: Oracle-independent flow safety.
    DENY-mode pairs are structurally blocked regardless of oracle behavior. *)
Definition flow_confinement_weak (st : KernelState) : Prop :=
  forall a l i e,
    taint_levels st a l = true ->
    in_flight st a i = true ->
    tool_egress (invocation_tool i) e = true ->
    flow_allows l e = true
    \/ flow_inspects l e = true
    \/ flow_override a (invocation_tool i) l = true.

(** Safety 5: Child capabilities are a subset of parent capabilities.
    Capabilities only flow downward in the delegation tree. *)
Definition capability_subsumption (st : KernelState) : Prop :=
  forall c p,
    agent_parent st c p = true ->
    agent_active st c = true ->
    agent_active st p = true ->
    forall cap, agent_cap st c cap = true -> agent_cap st p cap = true.

(** Safety 6: Inactive agents leave no residue.
    No zombie state after revocation. *)
Definition revocation_clean (st : KernelState) : Prop :=
  forall a,
    agent_active st a = false ->
    (forall i, in_flight st a i = false)
    /\ (forall l, taint_levels st a l = false).

(** Safety 7: Taint is traceable to either invocation or child return.
    No phantom taint. *)
Definition taint_integrity (st : KernelState) : Prop :=
  forall a l,
    taint_levels st a l = true ->
    agent_active st a = true ->
    gh_taint_invoked st a l = true \/ gh_taint_received st a l = true.

(** ================================================================ *)
(** Strengthening Invariants (Lean lines 609-645)                     *)
(** ================================================================ *)

(** Tree well-formedness *)

Definition parent_implies_active (st : KernelState) : Prop :=
  forall c p, agent_parent st c p = true -> agent_active st c = true.

Definition single_parent (st : KernelState) : Prop :=
  forall c p1 p2,
    agent_parent st c p1 = true ->
    agent_parent st c p2 = true ->
    agent_active st c = true ->
    p1 = p2.

Definition no_self_parent (st : KernelState) : Prop :=
  forall a, agent_parent st a a = false.

Definition root_no_parent (st : KernelState) : Prop :=
  forall p, agent_parent st root_agent p = false.

(** In-flight well-formedness *)

Definition in_flight_active (st : KernelState) : Prop :=
  forall a i, in_flight st a i = true -> agent_active st a = true.

Definition in_flight_registered (st : KernelState) : Prop :=
  forall a i,
    in_flight st a i = true ->
    tool_registered st (invocation_tool i) = true.

Definition in_flight_unique (st : KernelState) : Prop :=
  forall a1 a2 i,
    in_flight st a1 i = true ->
    in_flight st a2 i = true ->
    a1 = a2.

(** Root properties *)

Definition root_all_caps (st : KernelState) : Prop :=
  forall c, agent_cap st root_agent c = true.

Definition root_no_in_flight (st : KernelState) : Prop :=
  forall i, in_flight st root_agent i = false.

(** Ghost soundness: ghost relations stay in sync with taint_levels *)

Definition ghost_invoked_sound (st : KernelState) : Prop :=
  forall a l,
    gh_taint_invoked st a l = true ->
    taint_levels st a l = true \/ agent_active st a = false.

Definition ghost_received_sound (st : KernelState) : Prop :=
  forall a l,
    gh_taint_received st a l = true ->
    taint_levels st a l = true \/ agent_active st a = false.

(** In-flight flow compatibility: concurrent invocations are mutually compatible.
    If tool I1 is non-endorsed (will produce taint at its conf_floor), and tool I2
    has egress, the policy must permit (conf_floor(I1), egress(I2)). *)

Definition in_flight_flow_compat (st : KernelState) : Prop :=
  forall a i1 i2 e,
    in_flight st a i1 = true ->
    in_flight st a i2 = true ->
    tool_endorsed (invocation_tool i1) = false ->
    tool_egress (invocation_tool i2) e = true ->
    flow_allowed a (invocation_tool i2)
      (tool_conf_floor (invocation_tool i1)) e = true.

(** ================================================================ *)
(** Combined Invariant Bundle                                         *)
(** ================================================================ *)

Definition all_invariants (st : KernelState) : Prop :=
  root_always_active st
  /\ default_deny st
  /\ flow_confinement st
  /\ flow_confinement_weak st
  /\ capability_subsumption st
  /\ revocation_clean st
  /\ taint_integrity st
  /\ parent_implies_active st
  /\ single_parent st
  /\ no_self_parent st
  /\ root_no_parent st
  /\ in_flight_active st
  /\ in_flight_registered st
  /\ in_flight_unique st
  /\ root_all_caps st
  /\ root_no_in_flight st
  /\ ghost_invoked_sound st
  /\ ghost_received_sound st
  /\ in_flight_flow_compat st.

(** ================================================================ *)
(** Top-Level Safety Theorem Statements                               *)
(** ================================================================ *)

(** The invariants_inductive theorem and individual safety extractions
    are proved in TzimtzumV2_proofs.v after all per-action preservation
    lemmas are established. *)
