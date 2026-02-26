(** Axiomatized interface for Rust's BTreeSet and BTreeMap.
    Trust boundary: we assume these operations match their
    mathematical set/map counterparts. *)

From Stdlib Require Import Bool.

Module BTreeSet.
  Parameter t : Type -> Type.

  Parameter empty : forall {A : Type}, t A.
  Parameter insert : forall {A : Type}, A -> t A -> t A.
  Parameter remove : forall {A : Type}, A -> t A -> t A.
  Parameter mem : forall {A : Type}, A -> t A -> bool.
  Parameter is_empty : forall {A : Type}, t A -> bool.
  Parameter union : forall {A : Type}, t A -> t A -> t A.

  Section Axioms.
    Variable A : Type.
    Variable eq_dec : forall (x y : A), {x = y} + {x <> y}.

    Axiom mem_empty : forall (x : A),
      mem x empty = false.

    Axiom mem_insert : forall (x y : A) (s : t A),
      mem x (insert y s) = (if eq_dec x y then true else mem x s).

    Axiom mem_remove : forall (x y : A) (s : t A),
      mem x (remove y s) = (if eq_dec x y then false else mem x s).

    Axiom mem_union : forall (x : A) (s1 s2 : t A),
      mem x (union s1 s2) = mem x s1 || mem x s2.

    Axiom is_empty_empty :
      is_empty (@empty A) = true.

    Axiom is_empty_insert : forall (x : A) (s : t A),
      is_empty (insert x s) = false.
  End Axioms.
End BTreeSet.

Module BTreeMap.
  Parameter t : Type -> Type -> Type.

  Parameter empty : forall {K V : Type}, t K V.
  Parameter insert : forall {K V : Type}, K -> V -> t K V -> t K V.
  Parameter remove : forall {K V : Type}, K -> t K V -> t K V.
  Parameter get : forall {K V : Type}, K -> t K V -> option V.
  Parameter contains_key : forall {K V : Type}, K -> t K V -> bool.

  Parameter remove_by_value : forall {K V : Type}, V -> t K V -> t K V.

  Section Axioms.
    Variable K V : Type.

    Axiom get_empty : forall (k : K),
      get k (@empty K V) = None.

    Axiom get_insert_same : forall (k : K) (v : V) (m : t K V),
      get k (insert k v m) = Some v.

    Axiom get_insert_other : forall (k k' : K) (v : V) (m : t K V),
      k <> k' -> get k (insert k' v m) = get k m.

    Axiom get_remove_same : forall (k : K) (m : t K V),
      get k (remove k m) = None.

    Axiom get_remove_other : forall (k k' : K) (m : t K V),
      k <> k' -> get k (remove k' m) = get k m.

    Axiom contains_key_spec : forall (k : K) (m : t K V),
      contains_key k m = match get k m with Some _ => true | None => false end.
  End Axioms.

  Section RemoveByValueAxioms.
    Variable K V : Type.
    Variable eq_dec_v : forall (x y : V), {x = y} + {x <> y}.

    Axiom get_remove_by_value_hit : forall (k : K) (v : V) (m : t K V),
      get k m = Some v ->
      get k (remove_by_value v m) = None.

    Axiom get_remove_by_value_miss : forall (k : K) (v v' : V) (m : t K V),
      get k m = Some v' -> v <> v' ->
      get k (remove_by_value v m) = Some v'.

    Axiom get_remove_by_value_none : forall (k : K) (v : V) (m : t K V),
      get k m = None ->
      get k (remove_by_value v m) = None.
  End RemoveByValueAxioms.

  Section NestedOps.
    Variable K V : Type.

    Definition mem_nested (k : K) (v : V) (m : t K (BTreeSet.t V)) : bool :=
      match get k m with
      | Some s => BTreeSet.mem v s
      | None => false
      end.

    Definition insert_nested (k : K) (v : V) (m : t K (BTreeSet.t V))
        : t K (BTreeSet.t V) :=
      match get k m with
      | Some s => insert k (BTreeSet.insert v s) m
      | None => insert k (BTreeSet.insert v BTreeSet.empty) m
      end.

    Definition union_nested (k : K) (vs : BTreeSet.t V)
        (m : t K (BTreeSet.t V)) : t K (BTreeSet.t V) :=
      match get k m with
      | Some s => insert k (BTreeSet.union s vs) m
      | None => insert k vs m
      end.

    Definition remove_key_nested (k : K) (m : t K (BTreeSet.t V))
        : t K (BTreeSet.t V) :=
      remove k m.
  End NestedOps.

  Section NestedLemmas.
    Variable K V : Type.
    Variable eq_dec_k : forall (x y : K), {x = y} + {x <> y}.
    Variable eq_dec_v : forall (x y : V), {x = y} + {x <> y}.

    Lemma mem_nested_empty : forall (k : K) (v : V),
      mem_nested K V k v (@empty K (BTreeSet.t V)) = false.
    Proof.
      intros. unfold mem_nested. rewrite get_empty. reflexivity.
    Qed.

    Lemma mem_nested_insert_same : forall k v1 v2 m,
      mem_nested K V k v1 (insert_nested K V k v2 m) =
        (if eq_dec_v v1 v2 then true else mem_nested K V k v1 m).
    Proof.
      intros. unfold mem_nested, insert_nested.
      destruct (get k m) eqn:Hget;
        rewrite get_insert_same;
        rewrite (BTreeSet.mem_insert V eq_dec_v);
        destruct (eq_dec_v v1 v2); auto.
      rewrite BTreeSet.mem_empty. reflexivity.
    Qed.

    Lemma mem_nested_insert_other : forall k1 k2 v1 v2 m,
      k1 <> k2 ->
      mem_nested K V k1 v1 (insert_nested K V k2 v2 m) =
        mem_nested K V k1 v1 m.
    Proof.
      intros k1 k2 v1 v2 m Hneq. unfold mem_nested, insert_nested.
      destruct (get k2 m) eqn:Hget;
        (rewrite get_insert_other; [reflexivity | exact Hneq]).
    Qed.

    Lemma mem_nested_union_same : forall k v vs m,
      mem_nested K V k v (union_nested K V k vs m) =
        mem_nested K V k v m || BTreeSet.mem v vs.
    Proof.
      intros. unfold mem_nested, union_nested.
      destruct (get k m) eqn:Hget.
      - rewrite get_insert_same.
        rewrite BTreeSet.mem_union.
        reflexivity.
      - rewrite get_insert_same.
        reflexivity.
    Qed.

    Lemma mem_nested_union_other : forall k1 k2 v vs m,
      k1 <> k2 ->
      mem_nested K V k1 v (union_nested K V k2 vs m) =
        mem_nested K V k1 v m.
    Proof.
      intros k1 k2 v vs m Hneq. unfold mem_nested, union_nested.
      destruct (get k2 m) eqn:Hget;
        (rewrite get_insert_other; [reflexivity | exact Hneq]).
    Qed.

    Lemma mem_nested_remove_key_same : forall k v m,
      mem_nested K V k v (remove_key_nested K V k m) = false.
    Proof.
      intros. unfold mem_nested, remove_key_nested.
      rewrite get_remove_same. reflexivity.
    Qed.

    Lemma mem_nested_remove_key_other : forall k1 k2 v m,
      k1 <> k2 ->
      mem_nested K V k1 v (remove_key_nested K V k2 m) =
        mem_nested K V k1 v m.
    Proof.
      intros k1 k2 v m Hneq. unfold mem_nested, remove_key_nested.
      rewrite get_remove_other; [reflexivity | exact Hneq].
    Qed.
  End NestedLemmas.
End BTreeMap.
