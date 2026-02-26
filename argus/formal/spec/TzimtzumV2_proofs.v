(** TzimtzumV2.3 Safety Proofs
    Proves all_invariants is inductive:
    1. Base case: initial_state satisfies all invariants
    2. Inductive case: each action preserves all invariants

    Proof structure: 9 per-action preservation lemmas + 1 base case
    = 10 lemmas composing into invariants_inductive. *)

From Stdlib Require Import Bool.
Require Import ArgusKernel.axioms.DecidableAxioms.
Require Import ArgusKernel.axioms.OracleAxioms.
Require Import ArgusKernel.spec.TzimtzumV2.
Require Import ArgusKernel.spec.TzimtzumV2_safety.

(** ================================================================ *)
(** Useful Tactics                                                    *)
(** ================================================================ *)

Ltac unfold_state :=
  unfold initial_state, register_tool, delegate, grant_capability,
         revoke, cascade_revoke, invoke_start_state,
         invoke_complete, return_unendorsed_state in *;
  simpl in *.

Ltac unfold_invariants :=
  unfold all_invariants, root_always_active, default_deny,
         flow_confinement, flow_confinement_weak,
         capability_subsumption, revocation_clean, taint_integrity,
         parent_implies_active, single_parent, no_self_parent,
         root_no_parent, in_flight_active, in_flight_registered,
         in_flight_unique, root_all_caps, root_no_in_flight,
         ghost_invoked_sound, ghost_received_sound,
         in_flight_flow_compat in *.

Ltac beq_crush :=
  repeat match goal with
  | |- context[beq_agent ?a ?a] => rewrite beq_agent_refl
  | |- context[beq_inv ?i ?i] => rewrite beq_inv_refl
  | |- context[beq_conf ?l ?l] => rewrite beq_conf_refl
  | |- context[beq_cap ?c ?c] => rewrite beq_cap_refl
  | |- context[beq_tool ?t ?t] => rewrite beq_tool_refl
  | H : ?a <> ?b |- context[beq_agent ?a ?b] => rewrite (beq_agent_neq _ _ H)
  | H : beq_agent ?a ?b = true |- _ => apply beq_agent_true in H; subst
  | H : beq_agent ?a ?b = false |- _ => apply beq_agent_false in H
  end; simpl in *; try discriminate; auto.

(** ================================================================ *)
(** Base Case: Initial State                                          *)
(** ================================================================ *)

Lemma initial_root_always_active : root_always_active initial_state.
Proof.
  unfold root_always_active, initial_state. simpl.
  apply beq_agent_refl.
Qed.

Lemma initial_default_deny : default_deny initial_state.
Proof.
  unfold default_deny, initial_state. simpl.
  intros a i H. discriminate.
Qed.

Lemma initial_flow_confinement : flow_confinement initial_state.
Proof.
  unfold flow_confinement, initial_state. simpl.
  intros a l i e Htaint _  _. discriminate.
Qed.

Lemma initial_flow_confinement_weak : flow_confinement_weak initial_state.
Proof.
  unfold flow_confinement_weak, initial_state. simpl.
  intros a l i e Htaint _ _. discriminate.
Qed.

Lemma initial_capability_subsumption : capability_subsumption initial_state.
Proof.
  unfold capability_subsumption, initial_state. simpl.
  intros c p Hpar _ _ _. discriminate.
Qed.

Lemma initial_revocation_clean : revocation_clean initial_state.
Proof.
  unfold revocation_clean, initial_state. simpl.
  intros a Hinactive. split; intros; reflexivity.
Qed.

Lemma initial_taint_integrity : taint_integrity initial_state.
Proof.
  unfold taint_integrity, initial_state. simpl.
  intros a l Htaint _. discriminate.
Qed.

Lemma initial_parent_implies_active : parent_implies_active initial_state.
Proof.
  unfold parent_implies_active, initial_state. simpl.
  intros c p H. discriminate.
Qed.

Lemma initial_single_parent : single_parent initial_state.
Proof.
  unfold single_parent, initial_state. simpl.
  intros c p1 p2 H1 _ _. discriminate.
Qed.

Lemma initial_no_self_parent : no_self_parent initial_state.
Proof.
  unfold no_self_parent, initial_state. simpl.
  intros. reflexivity.
Qed.

Lemma initial_root_no_parent : root_no_parent initial_state.
Proof.
  unfold root_no_parent, initial_state. simpl.
  intros. reflexivity.
Qed.

Lemma initial_in_flight_active : in_flight_active initial_state.
Proof.
  unfold in_flight_active, initial_state. simpl.
  intros a i H. discriminate.
Qed.

Lemma initial_in_flight_registered : in_flight_registered initial_state.
Proof.
  unfold in_flight_registered, initial_state. simpl.
  intros a i H. discriminate.
Qed.

Lemma initial_in_flight_unique : in_flight_unique initial_state.
Proof.
  unfold in_flight_unique, initial_state. simpl.
  intros a1 a2 i H1 _. discriminate.
Qed.

Lemma initial_root_all_caps : root_all_caps initial_state.
Proof.
  unfold root_all_caps, initial_state. simpl.
  intros c. apply beq_agent_refl.
Qed.

Lemma initial_root_no_in_flight : root_no_in_flight initial_state.
Proof.
  unfold root_no_in_flight, initial_state. simpl.
  intros. reflexivity.
Qed.

Lemma initial_ghost_invoked_sound : ghost_invoked_sound initial_state.
Proof.
  unfold ghost_invoked_sound, initial_state. simpl.
  intros a l H. discriminate.
Qed.

Lemma initial_ghost_received_sound : ghost_received_sound initial_state.
Proof.
  unfold ghost_received_sound, initial_state. simpl.
  intros a l H. discriminate.
Qed.

Lemma initial_in_flight_flow_compat : in_flight_flow_compat initial_state.
Proof.
  unfold in_flight_flow_compat, initial_state. simpl.
  intros a i1 i2 e H1 _ _ _. discriminate.
Qed.

Theorem initial_all_invariants : all_invariants initial_state.
Proof.
  unfold all_invariants.
  exact (conj initial_root_always_active
  (conj initial_default_deny
  (conj initial_flow_confinement
  (conj initial_flow_confinement_weak
  (conj initial_capability_subsumption
  (conj initial_revocation_clean
  (conj initial_taint_integrity
  (conj initial_parent_implies_active
  (conj initial_single_parent
  (conj initial_no_self_parent
  (conj initial_root_no_parent
  (conj initial_in_flight_active
  (conj initial_in_flight_registered
  (conj initial_in_flight_unique
  (conj initial_root_all_caps
  (conj initial_root_no_in_flight
  (conj initial_ghost_invoked_sound
  (conj initial_ghost_received_sound
        initial_in_flight_flow_compat)))))))))))))))))).
Qed.

(** ================================================================ *)
(** Per-Action Preservation Lemmas                                    *)
(** ================================================================ *)

Lemma register_tool_preserves : forall st st' tool,
  all_invariants st ->
  register_tool st tool = Some st' ->
  all_invariants st'.
Proof.
  intros st st' tool Hinv Hstep.
  unfold register_tool in Hstep.
  destruct (tool_registered st tool) eqn:Hreg; [discriminate|].
  injection Hstep as Heq; subst st'.
  destruct Hinv as (Hraa & Hdd & Hfc & Hfcw & Hcs & Hrc & Hti &
    Hpia & Hsp & Hnsp & Hrnp & Hifa & Hifr & Hifu &
    Hrac & Hrni & Hgis & Hgrs & Hiffc).
  assert (Hifr' : in_flight_registered
    (mkState (agent_active st) (agent_parent st) (agent_cap st)
      (taint_levels st) (in_flight st)
      (fun t => if beq_tool t tool then true else tool_registered st t)
      (gh_taint_invoked st) (gh_taint_received st))).
  { unfold in_flight_registered; simpl; intros a i Hif.
    destruct (beq_tool (invocation_tool i) tool); [reflexivity | exact (Hifr a i Hif)]. }
  unfold all_invariants.
  exact (conj Hraa (conj Hdd (conj Hfc (conj Hfcw (conj Hcs (conj Hrc
    (conj Hti (conj Hpia (conj Hsp (conj Hnsp (conj Hrnp (conj Hifa
    (conj Hifr' (conj Hifu (conj Hrac (conj Hrni (conj Hgis
    (conj Hgrs Hiffc)))))))))))))))))).
Qed.

Ltac deq a b :=
  let H := fresh "Heq" in
  destruct (AgentId_eq_dec a b) as [H|H];
  [rewrite H in *; clear H; try rewrite beq_agent_refl in *; simpl in * |
   try rewrite beq_agent_neq in * by assumption; simpl in *].

Ltac split_all :=
  match goal with
  | |- _ /\ _ => split; [| split_all]
  | _ => idtac
  end.

Ltac deq_inv a b :=
  let H := fresh "Heq" in
  destruct (InvocationId_eq_dec a b) as [H|H];
  [rewrite H in *; clear H; try rewrite beq_inv_refl in *; simpl in * |
   try rewrite beq_inv_neq in * by assumption; simpl in *].

Lemma flow_allowed_to_weak : forall a tool l e,
  flow_allowed a tool l e = true ->
  flow_allows l e = true \/ flow_inspects l e = true \/ flow_override a tool l = true.
Proof.
  intros a0 t l e H. unfold flow_allowed in H.
  apply orb_true_iff in H. destruct H as [H|H].
  - apply orb_true_iff in H. destruct H as [H|H].
    + left. exact H.
    + apply andb_true_iff in H. right. left. exact (proj1 H).
  - right. right. exact H.
Qed.

Lemma delegate_preserves : forall st st' grantor grantee,
  all_invariants st ->
  delegate st grantor grantee = Some st' ->
  all_invariants st'.
Proof.
  intros st st' grantor grantee Hinv Hstep.
  unfold delegate in Hstep.
  destruct (negb (agent_active st grantor)) eqn:E1; [discriminate|].
  apply negb_false_iff in E1.
  destruct (agent_active st grantee) eqn:E2; [discriminate|].
  destruct (beq_agent grantee root_agent) eqn:E3; [discriminate|].
  apply beq_agent_false in E3.
  injection Hstep as Heq; subst st'.
  assert (Hgne : grantor <> grantee).
  { intro Habs; subst; rewrite E1 in E2; discriminate. }
  destruct Hinv as (Hraa & Hdd & Hfc & Hfcw & Hcs & Hrc & Hti &
    Hpia & Hsp & Hnsp & Hrnp & Hifa & Hifr & Hifu &
    Hrac & Hrni & Hgis & Hgrs & Hiffc).
  assert (Hrne : root_agent <> grantee) by (intro; subst; auto).
  assert (Hgne' : grantee <> grantor) by (intro; subst; apply Hgne; reflexivity).
  unfold all_invariants; unfold_invariants; simpl.
  split_all.
  - (* root_always_active *)
    rewrite (beq_agent_neq root_agent grantee Hrne). exact Hraa.
  - (* default_deny *)
    intros a i Hif.
    deq a grantee; [discriminate|].
    exact (Hdd a i Hif).
  - (* flow_confinement *)
    intros a l i e Htaint Hif Hegr.
    deq a grantee; [discriminate|].
    exact (Hfc a l i e Htaint Hif Hegr).
  - (* flow_confinement_weak *)
    intros a l i e Htaint Hif Hegr.
    deq a grantee; [discriminate|].
    exact (Hfcw a l i e Htaint Hif Hegr).
  - (* capability_subsumption *)
    intros c p Hpar Hac Hap cap Hcap.
    deq c grantee; [discriminate|].
    deq p grantee; [discriminate|].
    exact (Hcs c p Hpar Hac Hap cap Hcap).
  - (* revocation_clean *)
    intros a Hinact.
    deq a grantee; [discriminate|].
    exact (Hrc a Hinact).
  - (* taint_integrity *)
    intros a l Htaint Hact.
    deq a grantee; [discriminate|].
    exact (Hti a l Htaint Hact).
  - (* parent_implies_active *)
    intros c p Hpar.
    deq c grantee; [reflexivity|].
    deq p grantee; [discriminate|].
    exact (Hpia c p Hpar).
  - (* single_parent *)
    intros c p1 p2 Hp1 Hp2 Hact.
    deq c grantee.
    + destruct (beq_agent p1 grantor) eqn:E4; [|simpl in Hp1; discriminate].
      destruct (beq_agent p2 grantor) eqn:E5; [|simpl in Hp2; discriminate].
      apply beq_agent_true in E4. apply beq_agent_true in E5. congruence.
    + deq p1 grantee; [discriminate|].
      deq p2 grantee; [discriminate|].
      exact (Hsp c p1 p2 Hp1 Hp2 Hact).
  - (* no_self_parent *)
    intros a. deq a grantee.
    + rewrite (beq_agent_neq grantee grantor Hgne'). simpl. reflexivity.
    + exact (Hnsp a).
  - (* root_no_parent *)
    intros p.
    rewrite (beq_agent_neq root_agent grantee Hrne). simpl.
    destruct (AgentId_eq_dec p grantee) as [Hpe|Hpe].
    + subst. rewrite beq_agent_refl. reflexivity.
    + rewrite (beq_agent_neq p grantee Hpe). exact (Hrnp p).
  - (* in_flight_active *)
    intros a i Hif. deq a grantee; [discriminate|].
    exact (Hifa a i Hif).
  - (* in_flight_registered *)
    intros a i Hif. deq a grantee; [discriminate|]. exact (Hifr a i Hif).
  - (* in_flight_unique *)
    intros a1 a2 i Hif1 Hif2.
    deq a1 grantee; [discriminate|].
    deq a2 grantee; [discriminate|].
    exact (Hifu a1 a2 i Hif1 Hif2).
  - (* root_all_caps *)
    intros c. rewrite (beq_agent_neq root_agent grantee Hrne). exact (Hrac c).
  - (* root_no_in_flight *)
    intros i. rewrite (beq_agent_neq root_agent grantee Hrne). exact (Hrni i).
  - (* ghost_invoked_sound *)
    intros a l Hgi. deq a grantee; [discriminate|].
    exact (Hgis a l Hgi).
  - (* ghost_received_sound *)
    intros a l Hgr. deq a grantee; [discriminate|].
    exact (Hgrs a l Hgr).
  - (* in_flight_flow_compat *)
    intros a i1 i2 e Hif1 Hif2 Hend Hegr.
    deq a grantee; [discriminate|].
    exact (Hiffc a i1 i2 e Hif1 Hif2 Hend Hegr).
Qed.

Ltac cap_case a child cap0 cap :=
  destruct (beq_agent a child && beq_cap cap0 cap) eqn:?; simpl;
  [try reflexivity |
   try match goal with H : _ = true |- _ => idtac end].

Lemma grant_capability_preserves : forall st st' prnt child cap,
  all_invariants st ->
  grant_capability st prnt child cap = Some st' ->
  all_invariants st'.
Proof.
  intros st st' prnt child cap Hinv Hstep.
  unfold grant_capability in Hstep.
  destruct (negb (agent_active st prnt)) eqn:E1; [discriminate|].
  apply negb_false_iff in E1.
  destruct (negb (agent_active st child)) eqn:E2; [discriminate|].
  apply negb_false_iff in E2.
  destruct (negb (agent_parent st child prnt)) eqn:E3; [discriminate|].
  apply negb_false_iff in E3.
  destruct (negb (agent_cap st prnt cap)) eqn:E4; [discriminate|].
  apply negb_false_iff in E4.
  injection Hstep as Heq; subst st'.
  destruct Hinv as (Hraa & Hdd & Hfc & Hfcw & Hcs & Hrc & Hti &
    Hpia & Hsp & Hnsp & Hrnp & Hifa & Hifr & Hifu &
    Hrac & Hrni & Hgis & Hgrs & Hiffc).
  unfold all_invariants; unfold_invariants; simpl.
  split_all.
  - exact Hraa.
  - (* default_deny *)
    intros a i Hif. destruct (Hdd a i Hif) as [Hauth Hcaps].
    split; [exact Hauth|].
    intros c0 Htc.
    destruct (beq_agent a child && beq_cap c0 cap) eqn:Eac; [reflexivity|].
    exact (Hcaps c0 Htc).
  - exact Hfc.
  - exact Hfcw.
  - (* capability_subsumption *)
    intros c0 p Hpar Hac Hap cap0 Hcap0.
    destruct (AgentId_eq_dec c0 child) as [Hce|Hce];
      [subst; rewrite beq_agent_refl in Hcap0 |
       rewrite (beq_agent_neq _ _ Hce) in Hcap0]; simpl in Hcap0.
    + destruct (CapKind_eq_dec cap0 cap) as [Hke|Hke];
        [subst; rewrite beq_cap_refl in Hcap0; simpl in Hcap0 |
         rewrite (beq_cap_neq _ _ Hke) in Hcap0; simpl in Hcap0].
      * destruct (AgentId_eq_dec p child) as [Hpe|Hpe];
          [subst; rewrite beq_agent_refl; rewrite beq_cap_refl; reflexivity |
           rewrite (beq_agent_neq _ _ Hpe); simpl].
        assert (p = prnt) by exact (Hsp child p prnt Hpar E3 Hac).
        subst. exact E4.
      * destruct (AgentId_eq_dec p child) as [Hpe|Hpe];
          [subst; rewrite beq_agent_refl; rewrite (beq_cap_neq _ _ Hke); simpl |
           rewrite (beq_agent_neq _ _ Hpe); simpl];
        exact (Hcs child _ Hpar Hac Hap cap0 Hcap0).
    + destruct (AgentId_eq_dec p child) as [Hpe|Hpe].
      * subst. rewrite beq_agent_refl.
        destruct (CapKind_eq_dec cap0 cap) as [Hke|Hke];
          [subst; rewrite beq_cap_refl; reflexivity |
           rewrite (beq_cap_neq _ _ Hke); simpl;
           exact (Hcs c0 child Hpar Hac Hap cap0 Hcap0)].
      * rewrite (beq_agent_neq _ _ Hpe). simpl.
        exact (Hcs c0 p Hpar Hac Hap cap0 Hcap0).
  - exact Hrc.
  - exact Hti.
  - exact Hpia.
  - exact Hsp.
  - exact Hnsp.
  - exact Hrnp.
  - exact Hifa.
  - exact Hifr.
  - exact Hifu.
  - (* root_all_caps *)
    intros c0. destruct (beq_agent root_agent child && beq_cap c0 cap) eqn:Erc;
    [reflexivity | exact (Hrac c0)].
  - exact Hrni.
  - exact Hgis.
  - exact Hgrs.
  - exact Hiffc.
Qed.

Lemma revoke_preserves : forall st st' prnt target,
  all_invariants st ->
  revoke st prnt target = Some st' ->
  all_invariants st'.
Proof.
  intros st st' prnt target Hinv Hstep.
  unfold revoke in Hstep.
  destruct (negb (agent_parent st target prnt)) eqn:E1; [discriminate|].
  apply negb_false_iff in E1.
  destruct (negb (agent_active st prnt)) eqn:E2; [discriminate|].
  apply negb_false_iff in E2.
  destruct (negb (agent_active st target)) eqn:E3; [discriminate|].
  apply negb_false_iff in E3.
  destruct (beq_agent target root_agent) eqn:E4; [discriminate|].
  apply beq_agent_false in E4.
  injection Hstep as Heq; subst st'.
  destruct Hinv as (Hraa & Hdd & Hfc & Hfcw & Hcs & Hrc & Hti &
    Hpia & Hsp & Hnsp & Hrnp & Hifa & Hifr & Hifu &
    Hrac & Hrni & Hgis & Hgrs & Hiffc).
  assert (Hrne : root_agent <> target) by (intro; subst; auto).
  unfold all_invariants; unfold_invariants; simpl.
  split_all.
  - rewrite (beq_agent_neq root_agent target Hrne). exact Hraa.
  - intros a i Hif. deq a target; [discriminate|]. exact (Hdd a i Hif).
  - intros a l i e Ht Hif He.
    deq a target; [discriminate|]. exact (Hfc a l i e Ht Hif He).
  - intros a l i e Ht Hif He.
    deq a target; [discriminate|]. exact (Hfcw a l i e Ht Hif He).
  - intros c p Hpar Hac Hap cap Hcap.
    deq c target; [discriminate|].
    deq p target; [discriminate|].
    exact (Hcs c p Hpar Hac Hap cap Hcap).
  - intros a Hinact. deq a target.
    + split; intros; reflexivity.
    + exact (Hrc a Hinact).
  - intros a l Ht Hact.
    deq a target; [discriminate|]. exact (Hti a l Ht Hact).
  - intros c p Hpar.
    deq c target; [discriminate|]. exact (Hpia c p Hpar).
  - intros c p1 p2 Hp1 Hp2 Hact.
    deq c target; [discriminate|]. exact (Hsp c p1 p2 Hp1 Hp2 Hact).
  - intros a. deq a target; [reflexivity|]. exact (Hnsp a).
  - intros p. rewrite (beq_agent_neq root_agent target Hrne). exact (Hrnp p).
  - intros a i Hif. deq a target; [discriminate|]. exact (Hifa a i Hif).
  - intros a i Hif. deq a target; [discriminate|]. exact (Hifr a i Hif).
  - intros a1 a2 i Hif1 Hif2.
    deq a1 target; [discriminate|].
    deq a2 target; [discriminate|].
    exact (Hifu a1 a2 i Hif1 Hif2).
  - intros c. rewrite (beq_agent_neq root_agent target Hrne). exact (Hrac c).
  - intros i. rewrite (beq_agent_neq root_agent target Hrne). exact (Hrni i).
  - intros a l Hgi. deq a target; [discriminate|]. exact (Hgis a l Hgi).
  - intros a l Hgr. deq a target; [discriminate|]. exact (Hgrs a l Hgr).
  - intros a i1 i2 e Hif1 Hif2 Hend Hegr.
    deq a target; [discriminate|]. exact (Hiffc a i1 i2 e Hif1 Hif2 Hend Hegr).
Qed.

Lemma cascade_revoke_preserves : forall st st' child prnt,
  all_invariants st ->
  cascade_revoke st child prnt = Some st' ->
  all_invariants st'.
Proof.
  intros st st' child prnt Hinv Hstep.
  unfold cascade_revoke in Hstep.
  destruct (negb (agent_parent st child prnt)) eqn:E1; [discriminate|].
  apply negb_false_iff in E1.
  destruct (agent_active st prnt) eqn:E2; [discriminate|].
  destruct (negb (agent_active st child)) eqn:E3; [discriminate|].
  apply negb_false_iff in E3.
  destruct (beq_agent child root_agent) eqn:E4; [discriminate|].
  apply beq_agent_false in E4.
  injection Hstep as Heq; subst st'.
  destruct Hinv as (Hraa & Hdd & Hfc & Hfcw & Hcs & Hrc & Hti &
    Hpia & Hsp & Hnsp & Hrnp & Hifa & Hifr & Hifu &
    Hrac & Hrni & Hgis & Hgrs & Hiffc).
  assert (Hrne : root_agent <> child) by (intro; subst; auto).
  unfold all_invariants; unfold_invariants; simpl.
  split_all.
  - rewrite (beq_agent_neq root_agent child Hrne). exact Hraa.
  - intros a i Hif. deq a child; [discriminate|]. exact (Hdd a i Hif).
  - intros a l i e Ht Hif He.
    deq a child; [discriminate|]. exact (Hfc a l i e Ht Hif He).
  - intros a l i e Ht Hif He.
    deq a child; [discriminate|]. exact (Hfcw a l i e Ht Hif He).
  - intros c p Hpar Hac Hap cap Hcap.
    deq c child; [discriminate|].
    deq p child; [discriminate|].
    exact (Hcs c p Hpar Hac Hap cap Hcap).
  - intros a Hinact. deq a child.
    + split; intros; reflexivity.
    + exact (Hrc a Hinact).
  - intros a l Ht Hact.
    deq a child; [discriminate|]. exact (Hti a l Ht Hact).
  - intros c p Hpar.
    deq c child; [discriminate|]. exact (Hpia c p Hpar).
  - intros c p1 p2 Hp1 Hp2 Hact.
    deq c child; [discriminate|]. exact (Hsp c p1 p2 Hp1 Hp2 Hact).
  - intros a. deq a child; [reflexivity|]. exact (Hnsp a).
  - intros p. rewrite (beq_agent_neq root_agent child Hrne). exact (Hrnp p).
  - intros a i Hif. deq a child; [discriminate|]. exact (Hifa a i Hif).
  - intros a i Hif. deq a child; [discriminate|]. exact (Hifr a i Hif).
  - intros a1 a2 i Hif1 Hif2.
    deq a1 child; [discriminate|].
    deq a2 child; [discriminate|].
    exact (Hifu a1 a2 i Hif1 Hif2).
  - intros c. rewrite (beq_agent_neq root_agent child Hrne). exact (Hrac c).
  - intros i. rewrite (beq_agent_neq root_agent child Hrne). exact (Hrni i).
  - intros a l Hgi. deq a child; [discriminate|]. exact (Hgis a l Hgi).
  - intros a l Hgr. deq a child; [discriminate|]. exact (Hgrs a l Hgr).
  - intros a i1 i2 e Hif1 Hif2 Hend Hegr.
    deq a child; [discriminate|]. exact (Hiffc a i1 i2 e Hif1 Hif2 Hend Hegr).
Qed.

Lemma invoke_start_preserves : forall st a tool inv,
  all_invariants st ->
  invoke_start_pre st a tool inv ->
  all_invariants (invoke_start_state st a inv).
Proof.
  intros st a tool inv Hinv Hpre.
  destruct Hpre as (Hact & Hnroot & Hreg & Htool & Hfresh &
    Hcap_gate & Hspec_flow & Hrev_flow & Hself_flow & Hauth).
  destruct Hinv as (Hraa & Hdd & Hfc & Hfcw & Hcs & Hrc & Hti &
    Hpia & Hsp & Hnsp & Hrnp & Hifa & Hifr & Hifu &
    Hrac & Hrni & Hgis & Hgrs & Hiffc).
  unfold all_invariants; unfold invoke_start_state; unfold_invariants; simpl.
  split_all.
  - exact Hraa.
  - intros a0 i0 Hif0.
    deq a0 a.
    + deq_inv i0 inv.
      * rewrite Htool in *.
        split; [exact Hauth | intros c0 Htc; exact (Hcap_gate c0 Htc)].
      * exact (Hdd a i0 Hif0).
    + exact (Hdd a0 i0 Hif0).
  - intros a0 l i0 e Htaint Hif0 Hegr.
    deq a0 a.
    + deq_inv i0 inv.
      * rewrite Htool in *.
        apply Hspec_flow; [left; exact Htaint | exact Hegr].
      * exact (Hfc a l i0 e Htaint Hif0 Hegr).
    + exact (Hfc a0 l i0 e Htaint Hif0 Hegr).
  - intros a0 l i0 e Htaint Hif0 Hegr.
    deq a0 a.
    + deq_inv i0 inv.
      * rewrite Htool in *.
        apply flow_allowed_to_weak.
        apply Hspec_flow; [left; exact Htaint | exact Hegr].
      * exact (Hfcw a l i0 e Htaint Hif0 Hegr).
    + exact (Hfcw a0 l i0 e Htaint Hif0 Hegr).
  - exact Hcs.
  - intros a0 Hinact. deq a0 a; [rewrite Hact in Hinact; discriminate|].
    exact (Hrc a0 Hinact).
  - exact Hti.
  - exact Hpia.
  - exact Hsp.
  - exact Hnsp.
  - exact Hrnp.
  - intros a0 i0 Hif0. deq a0 a.
    + deq_inv i0 inv; [exact Hact | exact (Hifa a i0 Hif0)].
    + exact (Hifa a0 i0 Hif0).
  - intros a0 i0 Hif0. deq a0 a.
    + deq_inv i0 inv; [rewrite Htool; exact Hreg | exact (Hifr a i0 Hif0)].
    + exact (Hifr a0 i0 Hif0).
  - intros a1 a2 i0 Hif1 Hif2.
    deq a1 a.
    + deq a2 a; [reflexivity|].
      deq_inv i0 inv.
      * rewrite (Hfresh a2) in Hif2; discriminate.
      * exact (Hifu a a2 i0 Hif1 Hif2).
    + deq a2 a.
      * deq_inv i0 inv.
        -- rewrite (Hfresh a1) in Hif1; discriminate.
        -- exact (Hifu a1 a i0 Hif1 Hif2).
      * exact (Hifu a1 a2 i0 Hif1 Hif2).
  - exact Hrac.
  - intros i0.
    assert (Hne : root_agent <> a) by (intro; subst; auto).
    rewrite (beq_agent_neq root_agent a Hne). simpl. exact (Hrni i0).
  - exact Hgis.
  - exact Hgrs.
  - intros a0 i1 i2 e Hif1 Hif2 Hend Hegr.
    deq a0 a.
    + deq_inv i1 inv.
      * deq_inv i2 inv.
        -- rewrite Htool in *. exact (Hself_flow e Hend Hegr).
        -- rewrite Htool in *. exact (Hrev_flow i2 e Hif2 Hegr Hend).
      * deq_inv i2 inv.
        -- rewrite Htool in *.
           apply Hspec_flow; [| exact Hegr].
           right. exists i1. exact (conj Hif1 (conj eq_refl Hend)).
        -- exact (Hiffc a i1 i2 e Hif1 Hif2 Hend Hegr).
    + exact (Hiffc a0 i1 i2 e Hif1 Hif2 Hend Hegr).
Qed.

Lemma invoke_complete_preserves : forall st st' a inv,
  all_invariants st ->
  invoke_complete st a inv = Some st' ->
  all_invariants st'.
Proof.
  intros st st' a inv Hinv Hstep.
  unfold invoke_complete in Hstep.
  destruct (negb (in_flight st a inv)) eqn:E1; [discriminate|].
  apply negb_false_iff in E1.
  destruct (negb (agent_active st a)) eqn:E2; [discriminate|].
  apply negb_false_iff in E2.
  injection Hstep as Heq; subst st'.
  destruct Hinv as (Hraa & Hdd & Hfc & Hfcw & Hcs & Hrc & Hti &
    Hpia & Hsp & Hnsp & Hrnp & Hifa & Hifr & Hifu &
    Hrac & Hrni & Hgis & Hgrs & Hiffc).
  assert (Hne : a <> root_agent).
  { intro Habs; subst. rewrite (Hrni inv) in E1. discriminate. }
  unfold all_invariants; unfold_invariants; simpl.
  split_all.
  - exact Hraa.
  - intros a0 i0 Hif0. deq a0 a.
    + deq_inv i0 inv; [discriminate|]. exact (Hdd a i0 Hif0).
    + exact (Hdd a0 i0 Hif0).
  - intros a0 l i0 e Htaint Hif0 Hegr. deq a0 a.
    + deq_inv i0 inv; [discriminate|].
      destruct (negb (tool_endorsed (invocation_tool inv)) &&
        beq_conf l (tool_conf_floor (invocation_tool inv))) eqn:Econd.
      * apply andb_true_iff in Econd. destruct Econd as [Hne_tool Hlf].
        apply negb_true_iff in Hne_tool. apply beq_conf_true in Hlf. subst l.
        exact (Hiffc a inv i0 e E1 Hif0 Hne_tool Hegr).
      * exact (Hfc a l i0 e Htaint Hif0 Hegr).
    + exact (Hfc a0 l i0 e Htaint Hif0 Hegr).
  - intros a0 l i0 e Htaint Hif0 Hegr. deq a0 a.
    + deq_inv i0 inv; [discriminate|].
      destruct (negb (tool_endorsed (invocation_tool inv)) &&
        beq_conf l (tool_conf_floor (invocation_tool inv))) eqn:Econd.
      * apply andb_true_iff in Econd. destruct Econd as [Hne_tool Hlf].
        apply negb_true_iff in Hne_tool. apply beq_conf_true in Hlf. subst l.
        apply flow_allowed_to_weak.
        exact (Hiffc a inv i0 e E1 Hif0 Hne_tool Hegr).
      * exact (Hfcw a l i0 e Htaint Hif0 Hegr).
    + exact (Hfcw a0 l i0 e Htaint Hif0 Hegr).
  - exact Hcs.
  - intros a0 Hinact. deq a0 a; [rewrite E2 in Hinact; discriminate|].
    exact (Hrc a0 Hinact).
  - intros a0 l Htaint Hact0. deq a0 a.
    + destruct (negb (tool_endorsed (invocation_tool inv)) &&
        beq_conf l (tool_conf_floor (invocation_tool inv))) eqn:Econd.
      * left. reflexivity.
      * exact (Hti a l Htaint Hact0).
    + exact (Hti a0 l Htaint Hact0).
  - exact Hpia.
  - exact Hsp.
  - exact Hnsp.
  - exact Hrnp.
  - intros a0 i0 Hif0. deq a0 a.
    + deq_inv i0 inv; [discriminate|]. exact (Hifa a i0 Hif0).
    + exact (Hifa a0 i0 Hif0).
  - intros a0 i0 Hif0. deq a0 a.
    + deq_inv i0 inv; [discriminate|]. exact (Hifr a i0 Hif0).
    + exact (Hifr a0 i0 Hif0).
  - intros a1 a2 i0 Hif1 Hif2. deq a1 a.
    + deq_inv i0 inv; [discriminate|].
      deq a2 a; [reflexivity|].
      exact (Hifu a a2 i0 Hif1 Hif2).
    + deq a2 a.
      * deq_inv i0 inv; [discriminate|].
        exact (Hifu a1 a i0 Hif1 Hif2).
      * exact (Hifu a1 a2 i0 Hif1 Hif2).
  - exact Hrac.
  - intros i0.
    assert (Hne2 : root_agent <> a) by (intro; subst; auto).
    rewrite (beq_agent_neq root_agent a Hne2). simpl. exact (Hrni i0).
  - intros a0 l Hgi. deq a0 a.
    + destruct (negb (tool_endorsed (invocation_tool inv)) &&
        beq_conf l (tool_conf_floor (invocation_tool inv))) eqn:Econd.
      * left. reflexivity.
      * exact (Hgis a l Hgi).
    + exact (Hgis a0 l Hgi).
  - intros a0 l Hgr. deq a0 a.
    + destruct (Hgrs a l Hgr) as [Ht|Ha].
      * left.
        destruct (negb (tool_endorsed (invocation_tool inv)) &&
          beq_conf l (tool_conf_floor (invocation_tool inv)));
        [reflexivity | exact Ht].
      * rewrite E2 in Ha. discriminate.
    + exact (Hgrs a0 l Hgr).
  - intros a0 i1 i2 e Hif1 Hif2 Hend Hegr. deq a0 a.
    + deq_inv i1 inv; [discriminate|].
      deq_inv i2 inv; [discriminate|].
      exact (Hiffc a i1 i2 e Hif1 Hif2 Hend Hegr).
    + exact (Hiffc a0 i1 i2 e Hif1 Hif2 Hend Hegr).
Qed.

Lemma return_endorsed_preserves : forall st child prnt,
  all_invariants st ->
  return_endorsed_pre st child prnt ->
  all_invariants st.
Proof.
  intros st child prnt Hinv _. exact Hinv.
Qed.

Lemma return_unendorsed_preserves : forall st child prnt,
  all_invariants st ->
  return_unendorsed_pre st child prnt ->
  all_invariants (return_unendorsed_state st child prnt).
Proof.
  intros st child prnt Hinv Hpre.
  destruct Hpre as (Hpar & Hact_child & Hact_prnt & Hno_flight & Hflow_gate).
  destruct Hinv as (Hraa & Hdd & Hfc & Hfcw & Hcs & Hrc & Hti &
    Hpia & Hsp & Hnsp & Hrnp & Hifa & Hifr & Hifu &
    Hrac & Hrni & Hgis & Hgrs & Hiffc).
  unfold all_invariants; unfold return_unendorsed_state; unfold_invariants; simpl.
  split_all.
  - exact Hraa.
  - exact Hdd.
  - intros a l i0 e Htaint Hif0 Hegr. deq a prnt.
    + destruct (taint_levels st child l) eqn:Echild.
      * exact (Hflow_gate l i0 e Echild Hif0 Hegr).
      * simpl in Htaint. exact (Hfc prnt l i0 e Htaint Hif0 Hegr).
    + exact (Hfc a l i0 e Htaint Hif0 Hegr).
  - intros a l i0 e Htaint Hif0 Hegr. deq a prnt.
    + destruct (taint_levels st child l) eqn:Echild.
      * apply flow_allowed_to_weak.
        exact (Hflow_gate l i0 e Echild Hif0 Hegr).
      * simpl in Htaint. exact (Hfcw prnt l i0 e Htaint Hif0 Hegr).
    + exact (Hfcw a l i0 e Htaint Hif0 Hegr).
  - exact Hcs.
  - intros a Hinact. deq a prnt; [rewrite Hact_prnt in Hinact; discriminate|].
    exact (Hrc a Hinact).
  - intros a l Htaint Hact0. deq a prnt.
    + destruct (taint_levels st child l) eqn:Echild.
      * right. reflexivity.
      * simpl in Htaint. exact (Hti prnt l Htaint Hact0).
    + exact (Hti a l Htaint Hact0).
  - exact Hpia.
  - exact Hsp.
  - exact Hnsp.
  - exact Hrnp.
  - exact Hifa.
  - exact Hifr.
  - exact Hifu.
  - exact Hrac.
  - exact Hrni.
  - intros a l Hgi.
    destruct (Hgis a l Hgi) as [Ht|Ha].
    + left. destruct (beq_agent a prnt && taint_levels st child l);
      [reflexivity | exact Ht].
    + right. exact Ha.
  - intros a l Hgr. deq a prnt.
    + destruct (taint_levels st child l) eqn:Echild.
      * left. reflexivity.
      * simpl in Hgr. exact (Hgrs prnt l Hgr).
    + exact (Hgrs a l Hgr).
  - exact Hiffc.
Qed.

(** ================================================================ *)
(** Top-Level Inductive Theorem                                       *)
(** ================================================================ *)

Theorem invariants_inductive : forall st,
  reachable st -> all_invariants st.
Proof.
  intros st Hreach. induction Hreach as [| st st' _ IH Hstep].
  - exact initial_all_invariants.
  - inversion Hstep; subst;
    eauto using register_tool_preserves, delegate_preserves,
      grant_capability_preserves, revoke_preserves,
      cascade_revoke_preserves, invoke_start_preserves,
      invoke_complete_preserves, return_endorsed_preserves,
      return_unendorsed_preserves.
Qed.

(** ================================================================ *)
(** Individual Safety Extractions                                     *)
(** ================================================================ *)

Ltac extract_invariant :=
  match goal with
  | H : all_invariants _ |- _ =>
    unfold all_invariants in H; decompose [and] H; assumption
  end.

Theorem safety_root_always_active : forall st,
  reachable st -> root_always_active st.
Proof. intros st H. pose proof (invariants_inductive st H). extract_invariant. Qed.

Theorem safety_default_deny : forall st,
  reachable st -> default_deny st.
Proof. intros st H. pose proof (invariants_inductive st H). extract_invariant. Qed.

Theorem safety_flow_confinement : forall st,
  reachable st -> flow_confinement st.
Proof. intros st H. pose proof (invariants_inductive st H). extract_invariant. Qed.

Theorem safety_flow_confinement_weak : forall st,
  reachable st -> flow_confinement_weak st.
Proof. intros st H. pose proof (invariants_inductive st H). extract_invariant. Qed.

Theorem safety_capability_subsumption : forall st,
  reachable st -> capability_subsumption st.
Proof. intros st H. pose proof (invariants_inductive st H). extract_invariant. Qed.

Theorem safety_revocation_clean : forall st,
  reachable st -> revocation_clean st.
Proof. intros st H. pose proof (invariants_inductive st H). extract_invariant. Qed.

Theorem safety_taint_integrity : forall st,
  reachable st -> taint_integrity st.
Proof. intros st H. pose proof (invariants_inductive st H). extract_invariant. Qed.
