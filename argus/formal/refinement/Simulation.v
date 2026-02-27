(** Per-Transition Simulation Proofs
    For each concrete transition: if concrete and abstract states agree
    (via state_refines) and the concrete transition succeeds, then the
    corresponding abstract transition also succeeds and the resulting
    states agree.

    Easy proofs: register_tool, grant_capability, revoke,
                 cascade_revoke, return_endorsed
    Admitted:    delegate, invoke_start, invoke_complete,
                 return_unendorsed *)

From Stdlib Require Import Bool.
Require Import ArgusKernel.axioms.BTreeAxioms.
Require Import ArgusKernel.axioms.DecidableAxioms.
Require Import ArgusKernel.axioms.OracleAxioms.
Require Import ArgusKernel.spec.TzimtzumV2.
Require Import ArgusKernel.spec.TzimtzumV2_safety.
Require Import ArgusKernel.refinement.ConcreteSpec.
Require Import ArgusKernel.refinement.StateRelation.

(** ================================================================ *)
(** Auxiliary                                                          *)
(** ================================================================ *)

Ltac destruct_refines H :=
  destruct H as [Hactive [Hparent [Hcap [Htaint [Hflight
    [Hinvtool [Htoolreg [Hghinv Hghrecv]]]]]]]].

(** Split state_refines into exactly 9 subgoals without splitting the iff. *)
Ltac split_refines :=
  unfold state_refines;
  split; [| split; [| split; [| split; [| split; [|
    split; [| split; [| split]]]]]]].


(** ================================================================ *)
(** register_tool simulation                                          *)
(** ================================================================ *)

Lemma register_tool_simulation :
  forall cs as_ tool cs',
    state_refines cs as_ ->
    c_register_tool cs tool = Some cs' ->
    exists as'',
      register_tool as_ tool = Some as'' /\
      state_refines cs' as''.
Proof.
  intros cs as_ tool cs' Href Hconcrete.
  destruct_refines Href.
  unfold c_register_tool in Hconcrete.
  destruct (BTreeSet.mem tool (c_tool_registered cs)) eqn:Hmem; [discriminate|].
  inversion Hconcrete; subst; clear Hconcrete.
  rewrite Htoolreg in Hmem.
  unfold register_tool. rewrite Hmem.
  eexists. split; [reflexivity|].
  split_refines.
  - intros a0. simpl. apply Hactive.
  - intros c0 p0. simpl. exact (Hparent c0 p0).
  - intros a0 c. simpl. apply Hcap.
  - intros a0 l. simpl. apply Htaint.
  - intros a0 i. simpl. apply Hflight.
  - intros inv0 t0. simpl. apply Hinvtool.
  - intros t0. simpl.
    rewrite (BTreeSet.mem_insert ToolId ToolId_eq_dec).
    destruct (ToolId_eq_dec t0 tool) as [->|Hneq].
    + rewrite beq_tool_refl. reflexivity.
    + unfold beq_tool. destruct (ToolId_eq_dec t0 tool); [contradiction|].
      apply Htoolreg.
  - intros a0 l. simpl. apply Hghinv.
  - intros a0 l. simpl. apply Hghrecv.
Qed.

(** ================================================================ *)
(** grant_capability simulation                                       *)
(** ================================================================ *)

Lemma grant_capability_simulation :
  forall cs as_ prnt child cap cs',
    state_refines cs as_ ->
    c_grant_capability cs prnt child cap = Some cs' ->
    exists as'',
      grant_capability as_ prnt child cap = Some as'' /\
      state_refines cs' as''.
Proof.
  intros cs as_ prnt child cap cs' Href Hconcrete.
  destruct_refines Href.
  unfold c_grant_capability in Hconcrete.
  destruct (negb (BTreeSet.mem prnt (c_agent_active cs))) eqn:Hprnt_act;
    [discriminate|].
  apply negb_false_iff in Hprnt_act.
  destruct (negb (BTreeSet.mem child (c_agent_active cs))) eqn:Hchild_act;
    [discriminate|].
  apply negb_false_iff in Hchild_act.
  destruct (negb (match BTreeMap.get child (c_agent_parent cs) with
    | Some p => if AgentId_eq_dec p prnt then true else false
    | None => false
    end)) eqn:Hpar; [discriminate|].
  apply negb_false_iff in Hpar.
  destruct (BTreeMap.get child (c_agent_parent cs)) eqn:Hget_par; [|discriminate].
  destruct (AgentId_eq_dec a prnt) as [->|]; [|discriminate].
  destruct (negb (mem_agent_cap prnt cap (c_agent_cap cs))) eqn:Hcap_check;
    [discriminate|].
  apply negb_false_iff in Hcap_check.
  inversion Hconcrete; subst; clear Hconcrete.
  rewrite Hactive in Hprnt_act.
  rewrite Hactive in Hchild_act.
  assert (Hpar_abs : agent_parent as_ child prnt = true)
    by (exact (proj1 (Hparent _ _) Hget_par)).
  rewrite Hcap in Hcap_check.
  unfold grant_capability.
  rewrite Hprnt_act. simpl.
  rewrite Hchild_act. simpl.
  rewrite Hpar_abs. simpl.
  rewrite Hcap_check. simpl.
  eexists. split; [reflexivity|].
  split_refines.
  - intros a0. simpl. apply Hactive.
  - intros c0 p0. simpl. exact (Hparent c0 p0).
  - intros a0 c. simpl.
    unfold mem_agent_cap, BTreeMap.mem_nested, insert_cap, BTreeMap.insert_nested.
    destruct (AgentId_eq_dec a0 child) as [->|Hneq_a].
    + destruct (BTreeMap.get child (c_agent_cap cs)) eqn:Hget_cap.
      * rewrite BTreeMap.get_insert_same.
        rewrite (BTreeSet.mem_insert CapKind CapKind_eq_dec).
        destruct (CapKind_eq_dec c cap) as [->|Hneq_c].
        -- rewrite beq_agent_refl. rewrite beq_cap_refl. reflexivity.
        -- unfold beq_agent. destruct (AgentId_eq_dec child child); [|contradiction].
           unfold beq_cap. destruct (CapKind_eq_dec c cap); [contradiction|].
           pose proof (Hcap child c) as Hspec.
           unfold mem_agent_cap, BTreeMap.mem_nested in Hspec.
           rewrite Hget_cap in Hspec. exact Hspec.
      * rewrite BTreeMap.get_insert_same.
        rewrite (BTreeSet.mem_insert CapKind CapKind_eq_dec).
        destruct (CapKind_eq_dec c cap) as [->|Hneq_c].
        -- rewrite beq_agent_refl. rewrite beq_cap_refl. reflexivity.
        -- rewrite BTreeSet.mem_empty.
           unfold beq_agent. destruct (AgentId_eq_dec child child); [|contradiction].
           unfold beq_cap. destruct (CapKind_eq_dec c cap); [contradiction|].
           pose proof (Hcap child c) as Hspec.
           unfold mem_agent_cap, BTreeMap.mem_nested in Hspec.
           rewrite Hget_cap in Hspec. exact Hspec.
    + destruct (BTreeMap.get child (c_agent_cap cs)) eqn:Hget_cap.
      * rewrite BTreeMap.get_insert_other; [| exact Hneq_a].
        unfold beq_agent. destruct (AgentId_eq_dec a0 child); [contradiction|].
        apply Hcap.
      * rewrite BTreeMap.get_insert_other; [| exact Hneq_a].
        unfold beq_agent. destruct (AgentId_eq_dec a0 child); [contradiction|].
        apply Hcap.
  - intros a0 l. simpl. apply Htaint.
  - intros a0 i. simpl. apply Hflight.
  - intros inv0 t0. simpl. apply Hinvtool.
  - intros t0. simpl. apply Htoolreg.
  - intros a0 l. simpl. apply Hghinv.
  - intros a0 l. simpl. apply Hghrecv.
Qed.

(** ================================================================ *)
(** Helper tactic for revoke-style proofs                             *)
(** ================================================================ *)

Ltac revoke_field_case target Hfield :=
  destruct (AgentId_eq_dec _ target) as [->|Hneq];
  [ rewrite BTreeMap.get_remove_same;
    rewrite beq_agent_refl; reflexivity
  | rewrite BTreeMap.get_remove_other; [| exact Hneq];
    rewrite beq_agent_neq; auto; apply Hfield ].

(** ================================================================ *)
(** revoke simulation                                                 *)
(** ================================================================ *)

Lemma revoke_simulation :
  forall cs as_ prnt target cs',
    state_refines cs as_ ->
    c_revoke cs prnt target = Some cs' ->
    exists as'',
      revoke as_ prnt target = Some as'' /\
      state_refines cs' as''.
Proof.
  intros cs as_ prnt target cs' Href Hconcrete.
  destruct_refines Href.
  unfold c_revoke in Hconcrete.
  destruct (negb (match BTreeMap.get target (c_agent_parent cs) with
    | Some p => if AgentId_eq_dec p prnt then true else false
    | None => false
    end)) eqn:Hpar; [discriminate|].
  apply negb_false_iff in Hpar.
  destruct (BTreeMap.get target (c_agent_parent cs)) eqn:Hget_par; [|discriminate].
  destruct (AgentId_eq_dec a prnt) as [->|]; [|discriminate].
  destruct (negb (BTreeSet.mem prnt (c_agent_active cs))) eqn:Hprnt_act;
    [discriminate|].
  apply negb_false_iff in Hprnt_act.
  destruct (negb (BTreeSet.mem target (c_agent_active cs))) eqn:Htgt_act;
    [discriminate|].
  apply negb_false_iff in Htgt_act.
  destruct (AgentId_eq_dec target root_agent); [discriminate|].
  inversion Hconcrete; subst; clear Hconcrete.
  rewrite Hactive in Hprnt_act.
  rewrite Hactive in Htgt_act.
  assert (Hpar_abs : agent_parent as_ target prnt = true)
    by (exact (proj1 (Hparent _ _) Hget_par)).
  unfold revoke.
  rewrite Hpar_abs. simpl.
  rewrite Hprnt_act. simpl.
  rewrite Htgt_act. simpl.
  unfold beq_agent at 1. destruct (AgentId_eq_dec target root_agent); [contradiction|]. simpl.
  eexists. split; [reflexivity|].
  split_refines.
  - intros a0. simpl.
    rewrite (BTreeSet.mem_remove AgentId AgentId_eq_dec).
    destruct (AgentId_eq_dec a0 target) as [->|Hneq];
    [ rewrite beq_agent_refl; reflexivity
    | rewrite (beq_agent_neq _ _ Hneq); apply Hactive ].
  - intros c p. simpl. split; intros.
    + destruct (AgentId_eq_dec c target) as [->|Hneq].
      * rewrite BTreeMap.get_remove_same in H. discriminate.
      * rewrite BTreeMap.get_remove_other in H; [|exact Hneq].
        rewrite (beq_agent_neq _ _ Hneq).
        exact (proj1 (Hparent _ _) H).
    + destruct (AgentId_eq_dec c target) as [->|Hneq].
      * rewrite beq_agent_refl in H. discriminate.
      * rewrite (beq_agent_neq _ _ Hneq) in H.
        rewrite BTreeMap.get_remove_other; [|exact Hneq].
        exact (proj2 (Hparent _ _) H).
  - intros a0 c. simpl. unfold mem_agent_cap, BTreeMap.mem_nested.
    destruct (AgentId_eq_dec a0 target) as [->|Hneq];
    [ rewrite BTreeMap.get_remove_same; rewrite beq_agent_refl; reflexivity
    | rewrite BTreeMap.get_remove_other; [|exact Hneq];
      rewrite (beq_agent_neq _ _ Hneq); apply Hcap ].
  - intros a0 l. simpl. unfold mem_taint, BTreeMap.mem_nested.
    destruct (AgentId_eq_dec a0 target) as [->|Hneq];
    [ rewrite BTreeMap.get_remove_same; rewrite beq_agent_refl; reflexivity
    | rewrite BTreeMap.get_remove_other; [|exact Hneq];
      rewrite (beq_agent_neq _ _ Hneq); apply Htaint ].
  - intros a0 i. simpl. unfold mem_in_flight, BTreeMap.mem_nested.
    destruct (AgentId_eq_dec a0 target) as [->|Hneq];
    [ rewrite BTreeMap.get_remove_same; rewrite beq_agent_refl; reflexivity
    | rewrite BTreeMap.get_remove_other; [|exact Hneq];
      rewrite (beq_agent_neq _ _ Hneq); apply Hflight ].
  - intros inv0 t0. simpl. apply Hinvtool.
  - intros t0. simpl. apply Htoolreg.
  - intros a0 l. simpl. unfold mem_taint, BTreeMap.mem_nested.
    destruct (AgentId_eq_dec a0 target) as [->|Hneq];
    [ rewrite BTreeMap.get_remove_same; rewrite beq_agent_refl; reflexivity
    | rewrite BTreeMap.get_remove_other; [|exact Hneq];
      rewrite (beq_agent_neq _ _ Hneq); apply Hghinv ].
  - intros a0 l. simpl. unfold mem_taint, BTreeMap.mem_nested.
    destruct (AgentId_eq_dec a0 target) as [->|Hneq];
    [ rewrite BTreeMap.get_remove_same; rewrite beq_agent_refl; reflexivity
    | rewrite BTreeMap.get_remove_other; [|exact Hneq];
      rewrite (beq_agent_neq _ _ Hneq); apply Hghrecv ].
Qed.

(** ================================================================ *)
(** cascade_revoke simulation                                         *)
(** ================================================================ *)

Lemma cascade_revoke_simulation :
  forall cs as_ child prnt cs',
    state_refines cs as_ ->
    c_cascade_revoke cs child prnt = Some cs' ->
    exists as'',
      cascade_revoke as_ child prnt = Some as'' /\
      state_refines cs' as''.
Proof.
  intros cs as_ child prnt cs' Href Hconcrete.
  destruct_refines Href.
  unfold c_cascade_revoke in Hconcrete.
  destruct (negb (match BTreeMap.get child (c_agent_parent cs) with
    | Some p => if AgentId_eq_dec p prnt then true else false
    | None => false
    end)) eqn:Hpar; [discriminate|].
  apply negb_false_iff in Hpar.
  destruct (BTreeMap.get child (c_agent_parent cs)) eqn:Hget_par; [|discriminate].
  destruct (AgentId_eq_dec a prnt) as [->|]; [|discriminate].
  destruct (BTreeSet.mem prnt (c_agent_active cs)) eqn:Hprnt_act; [discriminate|].
  destruct (negb (BTreeSet.mem child (c_agent_active cs))) eqn:Hchild_act;
    [discriminate|].
  apply negb_false_iff in Hchild_act.
  destruct (AgentId_eq_dec child root_agent); [discriminate|].
  inversion Hconcrete; subst; clear Hconcrete.
  rewrite Hactive in Hprnt_act.
  rewrite Hactive in Hchild_act.
  assert (Hpar_abs : agent_parent as_ child prnt = true)
    by (exact (proj1 (Hparent _ _) Hget_par)).
  unfold cascade_revoke.
  rewrite Hpar_abs. simpl.
  rewrite Hprnt_act. simpl.
  rewrite Hchild_act. simpl.
  unfold beq_agent at 1. destruct (AgentId_eq_dec child root_agent); [contradiction|]. simpl.
  eexists. split; [reflexivity|].
  split_refines.
  - intros a0. simpl.
    rewrite (BTreeSet.mem_remove AgentId AgentId_eq_dec).
    destruct (AgentId_eq_dec a0 child) as [->|Hneq];
    [ rewrite beq_agent_refl; reflexivity
    | rewrite (beq_agent_neq _ _ Hneq); apply Hactive ].
  - intros c p. simpl. split; intros.
    + destruct (AgentId_eq_dec c child) as [->|Hneq].
      * rewrite BTreeMap.get_remove_same in H. discriminate.
      * rewrite BTreeMap.get_remove_other in H; [|exact Hneq].
        rewrite (beq_agent_neq _ _ Hneq).
        exact (proj1 (Hparent _ _) H).
    + destruct (AgentId_eq_dec c child) as [->|Hneq].
      * rewrite beq_agent_refl in H. discriminate.
      * rewrite (beq_agent_neq _ _ Hneq) in H.
        rewrite BTreeMap.get_remove_other; [|exact Hneq].
        exact (proj2 (Hparent _ _) H).
  - intros a0 c. simpl. unfold mem_agent_cap, BTreeMap.mem_nested.
    destruct (AgentId_eq_dec a0 child) as [->|Hneq];
    [ rewrite BTreeMap.get_remove_same; rewrite beq_agent_refl; reflexivity
    | rewrite BTreeMap.get_remove_other; [|exact Hneq];
      rewrite (beq_agent_neq _ _ Hneq); apply Hcap ].
  - intros a0 l. simpl. unfold mem_taint, BTreeMap.mem_nested.
    destruct (AgentId_eq_dec a0 child) as [->|Hneq];
    [ rewrite BTreeMap.get_remove_same; rewrite beq_agent_refl; reflexivity
    | rewrite BTreeMap.get_remove_other; [|exact Hneq];
      rewrite (beq_agent_neq _ _ Hneq); apply Htaint ].
  - intros a0 i. simpl. unfold mem_in_flight, BTreeMap.mem_nested.
    destruct (AgentId_eq_dec a0 child) as [->|Hneq];
    [ rewrite BTreeMap.get_remove_same; rewrite beq_agent_refl; reflexivity
    | rewrite BTreeMap.get_remove_other; [|exact Hneq];
      rewrite (beq_agent_neq _ _ Hneq); apply Hflight ].
  - intros inv0 t0. simpl. apply Hinvtool.
  - intros t0. simpl. apply Htoolreg.
  - intros a0 l. simpl. unfold mem_taint, BTreeMap.mem_nested.
    destruct (AgentId_eq_dec a0 child) as [->|Hneq];
    [ rewrite BTreeMap.get_remove_same; rewrite beq_agent_refl; reflexivity
    | rewrite BTreeMap.get_remove_other; [|exact Hneq];
      rewrite (beq_agent_neq _ _ Hneq); apply Hghinv ].
  - intros a0 l. simpl. unfold mem_taint, BTreeMap.mem_nested.
    destruct (AgentId_eq_dec a0 child) as [->|Hneq];
    [ rewrite BTreeMap.get_remove_same; rewrite beq_agent_refl; reflexivity
    | rewrite BTreeMap.get_remove_other; [|exact Hneq];
      rewrite (beq_agent_neq _ _ Hneq); apply Hghrecv ].
Qed.

(** ================================================================ *)
(** return_endorsed simulation (trivial -- identity)                   *)
(** ================================================================ *)

Lemma return_endorsed_simulation :
  forall cs as_ child prnt,
    state_refines cs as_ ->
    c_return_endorsed_pre cs child prnt ->
    return_endorsed_pre as_ child prnt.
Proof.
  intros cs as_ child prnt Href Hpre.
  destruct_refines Href.
  unfold c_return_endorsed_pre in Hpre.
  destruct Hpre as [Hpar_c [Hchild_c [Hprnt_c Hno_flight]]].
  unfold return_endorsed_pre.
  destruct (BTreeMap.get child (c_agent_parent cs)) eqn:Hget; [|contradiction].
  subst a.
  repeat split.
  - exact (proj1 (Hparent _ _) Hget).
  - rewrite <- Hactive. assumption.
  - rewrite <- Hactive. assumption.
  - intros i. rewrite <- Hflight. apply Hno_flight.
Qed.

(** ================================================================ *)
(** delegate simulation (Admitted -- needs remove_by_value reasoning) *)
(** ================================================================ *)

Lemma delegate_simulation :
  forall cs as_ grantor grantee cs',
    state_refines cs as_ ->
    c_invocation_tool_complete cs ->
    c_delegate cs grantor grantee = Some cs' ->
    exists as'',
      delegate as_ grantor grantee = Some as'' /\
      state_refines cs' as''.
Admitted.

(** ================================================================ *)
(** invoke_start simulation (Admitted -- complex precondition)         *)
(** ================================================================ *)

Lemma invoke_start_simulation :
  forall cs as_ a tool inv,
    state_refines cs as_ ->
    c_invocation_tool_complete cs ->
    c_invoke_start_pre cs a tool inv ->
    invoke_start_pre as_ a tool inv /\
    state_refines
      (c_invoke_start_state cs a tool inv)
      (invoke_start_state as_ a inv).
Admitted.

(** ================================================================ *)
(** invoke_complete simulation (Admitted -- invocation_tool lookup)    *)
(** ================================================================ *)

Lemma invoke_complete_simulation :
  forall cs as_ a inv cs',
    state_refines cs as_ ->
    c_invocation_tool_complete cs ->
    c_invoke_complete cs a inv = Some cs' ->
    exists as'',
      invoke_complete as_ a inv = Some as'' /\
      state_refines cs' as''.
Admitted.

(** ================================================================ *)
(** return_unendorsed simulation (Admitted -- union reasoning)         *)
(** ================================================================ *)

Lemma return_unendorsed_simulation :
  forall cs as_ child prnt,
    state_refines cs as_ ->
    c_return_unendorsed_pre cs child prnt ->
    return_unendorsed_pre as_ child prnt /\
    state_refines
      (c_return_unendorsed_state cs child prnt)
      (return_unendorsed_state as_ child prnt).
Admitted.

(** ================================================================ *)
(** Combined: any concrete step simulates an abstract step            *)
(** ================================================================ *)

Theorem simulation :
  forall cs cs' as_,
    state_refines cs as_ ->
    c_invocation_tool_complete cs ->
    c_step cs cs' ->
    exists as'',
      step as_ as'' /\
      state_refines cs' as''.
Proof.
  intros cs cs' as_ Href Hcomplete Hcstep.
  inversion Hcstep; subst.
  - destruct (register_tool_simulation _ _ _ _ Href H) as [as'' [Habs Href']].
    exists as''. exact (conj (step_register_tool _ _ _ Habs) Href').
  - destruct (delegate_simulation _ _ _ _ _ Href Hcomplete H)
      as [as'' [Habs Href']].
    exists as''. exact (conj (step_delegate _ _ _ _ Habs) Href').
  - destruct (grant_capability_simulation _ _ _ _ _ _ Href H)
      as [as'' [Habs Href']].
    exists as''. exact (conj (step_grant_capability _ _ _ _ _ Habs) Href').
  - destruct (revoke_simulation _ _ _ _ _ Href H) as [as'' [Habs Href']].
    exists as''. exact (conj (step_revoke _ _ _ _ Habs) Href').
  - destruct (cascade_revoke_simulation _ _ _ _ _ Href H)
      as [as'' [Habs Href']].
    exists as''. exact (conj (step_cascade_revoke _ _ _ _ Habs) Href').
  - destruct (invoke_start_simulation _ _ _ _ _ Href Hcomplete H)
      as [Hpre Href'].
    eexists. exact (conj (step_invoke_start _ _ _ _ Hpre) Href').
  - destruct (invoke_complete_simulation _ _ _ _ _ Href Hcomplete H)
      as [as'' [Habs Href']].
    exists as''. exact (conj (step_invoke_complete _ _ _ _ Habs) Href').
  - exists as_.
    exact (conj (step_return_endorsed _ _ _ (return_endorsed_simulation _ _ _ _ Href H)) Href).
  - destruct (return_unendorsed_simulation _ _ _ _ Href H)
      as [Hpre Href'].
    eexists. exact (conj (step_return_unendorsed _ _ _ Hpre) Href').
Qed.
