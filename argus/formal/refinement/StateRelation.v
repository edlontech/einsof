(** Refinement Relation: bridges the concrete BTreeMap-based state
    and the abstract function-based state from TzimtzumV2.v.

    The key insight: invocation_tool is a Parameter (immutable) in the
    abstract spec but a BTreeMap (mutable) in the concrete spec.
    The refinement requires the concrete map to agree with the abstract
    function wherever a binding exists. *)

From Stdlib Require Import Bool.
Require Import ArgusKernel.axioms.BTreeAxioms.
Require Import ArgusKernel.axioms.DecidableAxioms.
Require Import ArgusKernel.axioms.OracleAxioms.
Require Import ArgusKernel.spec.TzimtzumV2.
Require Import ArgusKernel.refinement.ConcreteSpec.

(** ================================================================ *)
(** State Refinement Relation (9 conjuncts)                           *)
(** ================================================================ *)

Definition state_refines (cs : ConcreteState) (as_ : KernelState) : Prop :=
  (forall a, BTreeSet.mem a (c_agent_active cs) = agent_active as_ a)
  /\ (forall c p,
        BTreeMap.get c (c_agent_parent cs) = Some p <->
        agent_parent as_ c p = true)
  /\ (forall a c,
        mem_agent_cap a c (c_agent_cap cs) = agent_cap as_ a c)
  /\ (forall a l,
        mem_taint a l (c_taint_levels cs) = taint_levels as_ a l)
  /\ (forall a i,
        mem_in_flight a i (c_in_flight cs) = in_flight as_ a i)
  /\ (forall inv tool,
        BTreeMap.get inv (c_invocation_tool cs) = Some tool ->
        invocation_tool inv = tool)
  /\ (forall t,
        BTreeSet.mem t (c_tool_registered cs) = tool_registered as_ t)
  /\ (forall a l,
        mem_taint a l (c_gh_taint_invoked cs) = gh_taint_invoked as_ a l)
  /\ (forall a l,
        mem_taint a l (c_gh_taint_received cs) = gh_taint_received as_ a l).

(** ================================================================ *)
(** Initial State Refinement                                          *)
(** ================================================================ *)

Theorem initial_state_refines :
  state_refines c_initial_state initial_state.
Proof.
  unfold state_refines, c_initial_state, initial_state; simpl.
  repeat split; intros.
  - rewrite (BTreeSet.mem_insert AgentId AgentId_eq_dec).
    destruct (AgentId_eq_dec a root_agent) as [->|Hneq].
    + rewrite beq_agent_refl. reflexivity.
    + rewrite BTreeSet.mem_empty.
      rewrite beq_agent_neq; auto.
  - rewrite BTreeMap.get_empty in H. discriminate.
  - discriminate.
  - unfold mem_agent_cap, BTreeMap.mem_nested.
    destruct (AgentId_eq_dec a root_agent) as [->|Hneq].
    + rewrite BTreeMap.get_insert_same.
      rewrite all_caps_mem. rewrite beq_agent_refl. reflexivity.
    + rewrite BTreeMap.get_insert_other; [| exact Hneq].
      rewrite BTreeMap.get_empty.
      rewrite beq_agent_neq; auto.
  - unfold mem_taint, BTreeMap.mem_nested.
    rewrite BTreeMap.get_empty. reflexivity.
  - unfold mem_in_flight, BTreeMap.mem_nested.
    rewrite BTreeMap.get_empty. reflexivity.
  - rewrite BTreeMap.get_empty in H. discriminate.
  - rewrite BTreeSet.mem_empty. reflexivity.
  - unfold mem_taint, BTreeMap.mem_nested.
    rewrite BTreeMap.get_empty. reflexivity.
  - unfold mem_taint, BTreeMap.mem_nested.
    rewrite BTreeMap.get_empty. reflexivity.
Qed.
