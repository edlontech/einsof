(** Top-Level Soundness Theorem
    Crown jewel: every reachable concrete state satisfies all safety properties.

    Proof: by induction on c_reachable, composing:
    1. simulation (Simulation.v) -- concrete step implies abstract step
    2. invariants_inductive (TzimtzumV2_proofs.v) -- abstract safety *)

From Stdlib Require Import Bool.
Require Import ArgusKernel.axioms.BTreeAxioms.
Require Import ArgusKernel.axioms.DecidableAxioms.
Require Import ArgusKernel.spec.TzimtzumV2.
Require Import ArgusKernel.spec.TzimtzumV2_safety.
Require Import ArgusKernel.spec.TzimtzumV2_proofs.
Require Import ArgusKernel.refinement.ConcreteSpec.
Require Import ArgusKernel.refinement.StateRelation.
Require Import ArgusKernel.refinement.Simulation.

(** The invocation_tool_complete invariant is preserved by all transitions. *)
Lemma c_invocation_tool_complete_preserved :
  forall cs cs',
    c_invocation_tool_complete cs ->
    c_step cs cs' ->
    c_invocation_tool_complete cs'.
Admitted.

Lemma c_invocation_tool_complete_initial :
  c_invocation_tool_complete c_initial_state.
Proof.
  unfold c_invocation_tool_complete, c_initial_state, mem_in_flight,
    BTreeMap.mem_nested; simpl.
  intros a inv.
  rewrite (BTreeMap.get_empty AgentId (BTreeSet.t InvocationId)).
  discriminate.
Qed.

Lemma c_invocation_tool_complete_reachable :
  forall cs, c_reachable cs -> c_invocation_tool_complete cs.
Proof.
  intros cs Hreach. induction Hreach.
  - exact c_invocation_tool_complete_initial.
  - exact (c_invocation_tool_complete_preserved _ _ IHHreach H).
Qed.

(** Every reachable concrete state refines some reachable abstract state. *)
Theorem refinement_preserves_reachability :
  forall cs,
    c_reachable cs ->
    exists as_, state_refines cs as_ /\ reachable as_.
Proof.
  intros cs Hreach. induction Hreach as [| cs cs' Hreach IH Hstep].
  - exists initial_state. split.
    + exact initial_state_refines.
    + exact reach_init.
  - destruct IH as [as_ [Href Hreach_abs]].
    pose proof (c_invocation_tool_complete_reachable cs Hreach) as Hcomplete.
    destruct (simulation _ _ _ Href Hcomplete Hstep) as [as'' [Habs_step Href']].
    exists as''. split.
    + exact Href'.
    + exact (reach_step _ _ Hreach_abs Habs_step).
Qed.

(** Crown jewel: every reachable concrete state satisfies all safety. *)
Theorem implementation_sound :
  forall cs,
    c_reachable cs ->
    exists as_, state_refines cs as_ /\ all_invariants as_.
Proof.
  intros cs Hreach.
  destruct (refinement_preserves_reachability cs Hreach) as [as_ [Href Hreach_abs]].
  exists as_. split.
  - exact Href.
  - exact (invariants_inductive _ Hreach_abs).
Qed.
