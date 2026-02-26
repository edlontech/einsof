(** Decidable equality and ordering for all kernel domain types.
    These correspond to Rust's PartialEq/Eq/Ord derives on
    AgentId, ToolId, InvocationId, CapKind, EgressKind, ConfLevel.

    Ported from TzimtzumV2.lean: types (lines 60-66),
    ordering axioms (lines 191-203), named constants (lines 85-89). *)

From Stdlib Require Import Bool.

(** --- Uninterpreted sorts --- *)
Parameter AgentId : Type.
Parameter ToolId : Type.
Parameter InvocationId : Type.
Parameter CapKind : Type.
Parameter EgressKind : Type.
Parameter ConfLevel : Type.

(** --- Decidable equality --- *)
Axiom AgentId_eq_dec : forall (x y : AgentId), {x = y} + {x <> y}.
Axiom ToolId_eq_dec : forall (x y : ToolId), {x = y} + {x <> y}.
Axiom InvocationId_eq_dec : forall (x y : InvocationId), {x = y} + {x <> y}.
Axiom CapKind_eq_dec : forall (x y : CapKind), {x = y} + {x <> y}.
Axiom EgressKind_eq_dec : forall (x y : EgressKind), {x = y} + {x <> y}.
Axiom ConfLevel_eq_dec : forall (x y : ConfLevel), {x = y} + {x <> y}.

(** --- Named constants --- *)
Parameter cl_public : ConfLevel.
Parameter cl_internal : ConfLevel.
Parameter cl_sensitive : ConfLevel.
Parameter cl_restricted : ConfLevel.
Parameter root_agent : AgentId.

(** --- ConfLevel ordering (total order) --- *)
Parameter le_conf : ConfLevel -> ConfLevel -> bool.

Axiom conf_refl : forall L, le_conf L L = true.
Axiom conf_trans : forall L1 L2 L3,
  le_conf L1 L2 = true -> le_conf L2 L3 = true -> le_conf L1 L3 = true.
Axiom conf_antisym : forall L1 L2,
  le_conf L1 L2 = true -> le_conf L2 L1 = true -> L1 = L2.
Axiom conf_total : forall L1 L2,
  le_conf L1 L2 = true \/ le_conf L2 L1 = true.

(** Chain: public < internal < sensitive < restricted *)
Axiom conf_chain_01 : le_conf cl_public cl_internal = true.
Axiom conf_chain_12 : le_conf cl_internal cl_sensitive = true.
Axiom conf_chain_23 : le_conf cl_sensitive cl_restricted = true.

(** Distinctness (prevents SMT-style collapsing) *)
Axiom cl_distinct_01 : cl_public <> cl_internal.
Axiom cl_distinct_02 : cl_public <> cl_sensitive.
Axiom cl_distinct_03 : cl_public <> cl_restricted.
Axiom cl_distinct_12 : cl_internal <> cl_sensitive.
Axiom cl_distinct_13 : cl_internal <> cl_restricted.
Axiom cl_distinct_23 : cl_sensitive <> cl_restricted.
