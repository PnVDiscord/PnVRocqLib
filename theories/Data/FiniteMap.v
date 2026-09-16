Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Prelude.X.
Require Export PnV.Math.ThN.
Require Export PnV.Math.OrderTheory.
Require Export PnV.Data.HsOrd.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Data.BalancedTree.

#[local] Infix "=~=" := is_similar_to : type_scope.
#[local] Infix "\in" := E.In.
#[local] Infix "∈" := L.In.

#[local] Hint Resolve S_lt_S_intro : core.

#[universes(template)]
Variant alist {K : Type} {V : Type} : Type :=
  | mk_alist (kvlist : list (K * V)).

#[global] Arguments alist : clear implicits.

Section ALIST.

#[universes(polymorphic=yes)]
Definition kvlist@{k v u | k <= u, v <= u} {K : Type@{k}} {V : Type@{v}} (al : alist K V) : fin_ensemble@{u} (K * V) :=
  match al with
  | mk_alist kvlist => kvlist
  end.

Universe U_alist_key.

Universe U_alist_val.

#[global]
Instance alist_is_similar_to_option_kleisli {K : Type@{U_alist_key}} {V : Type@{U_alist_val}} {V' : Type@{U_alist_val}} (Sim_V_V' : Similarity V V') : Similarity (alist K V) (K -> option V') :=
  fun m => fun m' => forall k : K, forall v : V, forall v' : V', forall v_sim_v' : v =~= v', (k, v) ∈ kvlist m <-> m' k = Some v'.

#[local]
Instance alist_isSetoid {K : Type@{U_alist_key}} {V : Type@{U_alist_val}} (K_hasEqDec : hasEqDec K) (V_isSetoid : isSetoid V) : isSetoid (alist K V) :=
  { eqProp (lhs : alist K V) (rhs : alist K V) := forall k : K, eqProp (isSetoid := option_isSetoid V_isSetoid) (L.lookup k (kvlist lhs)) (L.lookup k (kvlist rhs))
  ; eqProp_Equivalence := relation_on_image_liftsEquivalence (pi_isSetoid (fun _ => option_isSetoid V_isSetoid)).(eqProp_Equivalence) (fun al : alist K V => fun k : K => L.lookup k (kvlist al))
  }.

Context {K : Type@{U_alist_key}}.

#[global]
Instance alist_isFunctor : isFunctor (alist K) :=
  fun V : Type@{U_alist_val} => fun V' : Type@{U_alist_val} => fun v_to_v' : V -> V' => fun al : alist K V => mk_alist (map (fun '(k, v) => (k, v_to_v' v)) (kvlist al)).

Context `(K_hasEqDec : hasEqDec K).

#[global]
Instance alist_isSetoid1 : isSetoid1 (alist K) :=
  fun V : Type@{U_alist_val} => alist_isSetoid (V := V) K_hasEqDec.

Lemma lookup_map_kvlist {V : Type@{U_alist_val}} {V' : Type@{U_alist_val}} (v_to_v' : V -> V') (k : K) (kvs : list (K * V))
  : L.lookup k (map (fun '(k, v) => (k, v_to_v' v)) kvs) = option_map v_to_v' (L.lookup k kvs).
Proof.
  induction kvs as [ | [k' v'] kvs' IH]; simpl; eauto.
  destruct (B.decide (k = k')) as [? | ?]; eauto.
Qed.

#[global]
Instance alist_FunctorLaws
  : FunctorLaws (alist K) (SETOID1 := alist_isSetoid1) (FUNCTOR := alist_isFunctor).
Proof.
  assert (SIMP : forall A : Type@{U_alist_val}, forall B : Type@{U_alist_val}, forall f : A -> B, forall al : alist K A, forall k : K, L.lookup k (kvlist (fmap f al)) = option_map f (L.lookup k (kvlist al))).
  { intros A B f [kvs] k. eapply lookup_map_kvlist. }
  split; ii; unfold compose, id; rewrite !SIMP; simpl; rewrite option_eqProp_iff_eq.
  - f_equal. rewrite <- option_eqProp_iff_eq. exact (x_EQ k).
  - destruct (L.lookup k (kvlist x)) as [v | ]; reflexivity.
  - destruct (L.lookup k (kvlist x)) as [v | ]; reflexivity.
  - destruct (L.lookup k (kvlist x)) as [v | ]; simpl; congruence.
Qed.

End ALIST.

Module FinitePartialMap.

#[universes(template), projections(primitive)]
Record t {K : Type} {isSorted : list K -> bool} {V : Type} : Type :=
  { tree : BalancedTree.t (K * V)
  ; data_isSorted : isSorted (map fst (BalancedTree.data tree)) = true
  } as m.

#[global] Arguments t : clear implicits.

Definition data {K : Type} {V : Type} {isSorted : list K -> bool} (m : t K isSorted V) : list (K * V) :=
  BalancedTree.data m.(tree).

#[refine]
Definition mk {K : Type} {V : Type} {isSorted : list K -> bool} (xs : list (K * V)) (SORTED : isSorted (map fst xs) = true) : FinitePartialMap.t K isSorted V :=
  {| tree := BalancedTree.of_list xs; data_isSorted := _ |}.
Proof.
  rewrite BalancedTree.data_of_list. exact SORTED.
Defined.

Lemma data_mk {K : Type} {V : Type} {isSorted : list K -> bool} (xs : list (K * V))
  (SORTED : isSorted (map fst xs) = true)
  : data (FinitePartialMap.mk xs SORTED) = xs.
Proof.
  unfold data, mk. cbn. eapply BalancedTree.data_of_list.
Qed.

End FinitePartialMap.

#[global] Abbreviation fpmap K := (FinitePartialMap.t K (isSorted compare)).

Module FPM.

Section BASICS.

Context {K : Type} {V : Type} {PROSET : isProset K} {ORD : hsOrd K}.

Definition lookup' (k : K) (xs : list (K * V)) : option V :=
  option_map snd (OrderedList.lookup fst k xs).

Definition lookup (k : K) (m : fpmap K V) : option V :=
  option_map snd (BalancedTree.lookup (fun p => compare k (fst p)) m.(FinitePartialMap.tree)).

Lemma lookup_data (k : K) (m : fpmap K V)
  : lookup k m = lookup' k (FinitePartialMap.data m).
Proof.
  unfold lookup, lookup', FinitePartialMap.data.
  now rewrite BalancedTree.lookup_data by eapply FinitePartialMap.data_isSorted.
Qed.

Lemma lookup_compat_key (k : K) (k' : K) (m : fpmap K V)
  (EQ : k == k')
  : lookup k m = lookup k' m.
Proof.
  rewrite !lookup_data. unfold lookup'. now rewrite OrderedList.lookup_compat_key with (k' := k') by exact EQ.
Qed.

Theorem lookup_spec (m : fpmap K V) (k : K) (v : V)
  : lookup k m = Some v <-> (exists k', k == k' /\ L.In (k', v) (FinitePartialMap.data m)).
Proof.
  rewrite lookup_data. unfold lookup'. destruct (OrderedList.lookup _ _ _) as [[k' v'] | ] eqn: OBS; simpl.
  - rewrite OrderedList.lookup_spec in OBS by eapply FinitePartialMap.data_isSorted.
    find* [IN EQ] by OBS. simpl fst in EQ. split.
    + intros EQ'. inv EQ'. now exists k'.
    + intros (q & EQ' & IN').
      assert (LOOK : OrderedList.lookup fst k (FinitePartialMap.data m) = Some (q, v)).
      { rewrite OrderedList.lookup_spec by eapply FinitePartialMap.data_isSorted. auto. }
      assert (LOOK' : OrderedList.lookup fst k (FinitePartialMap.data m) = Some (k', v')).
      { rewrite OrderedList.lookup_spec by eapply FinitePartialMap.data_isSorted. auto. }
      congruence.
  - split; [congruence | intros (q & EQ & IN)].
    assert (LOOK : OrderedList.lookup fst k (FinitePartialMap.data m) = Some (q, v)).
    { rewrite OrderedList.lookup_spec by eapply FinitePartialMap.data_isSorted. auto. }
    congruence.
Qed.

Definition empty : fpmap K V :=
  FinitePartialMap.mk [] eq_refl.

Theorem lookup_empty (k : K)
  : lookup k empty = None.
Proof.
  rewrite lookup_data. unfold empty. rewrite FinitePartialMap.data_mk. reflexivity.
Qed.

#[refine]
Definition insert (k : K) (v : V) (m : fpmap K V) : fpmap K V :=
  {| FinitePartialMap.tree := BalancedTree.add (fun p => fun q => compare (fst p) (fst q)) (k, v) m.(FinitePartialMap.tree); FinitePartialMap.data_isSorted := _ |}.
Proof.
  rewrite BalancedTree.data_add by eapply FinitePartialMap.data_isSorted.
  eapply OrderedList.insert_sorted. eapply FinitePartialMap.data_isSorted.
Defined.

Lemma data_insert (k : K) (v : V) (m : fpmap K V)
  : FinitePartialMap.data (insert k v m) = OrderedList.insert fst (k, v) (FinitePartialMap.data m).
Proof.
  unfold insert, FinitePartialMap.data. simpl. eapply BalancedTree.data_add. eapply FinitePartialMap.data_isSorted.
Qed.

Theorem lookup_insert_eq (k : K) (v : V) (m : fpmap K V)
  : lookup k (insert k v m) = Some v.
Proof.
  rewrite lookup_data, data_insert. unfold lookup'.
  now rewrite OrderedList.lookup_insert_eq with (key := fst) (x := (k, v)).
Qed.

Theorem lookup_insert_ne (k : K) (v : V) (m : fpmap K V) (k0 : K)
  (NE : ~ k0 == k)
  : lookup k0 (insert k v m) = lookup k0 m.
Proof.
  rewrite !lookup_data, data_insert. unfold lookup'.
  now rewrite OrderedList.lookup_insert_ne.
Qed.

#[refine]
Definition remove (k : K) (m : fpmap K V) : fpmap K V :=
  {| FinitePartialMap.tree := BalancedTree.remove (fun p => compare k (fst p)) m.(FinitePartialMap.tree); FinitePartialMap.data_isSorted := _ |}.
Proof.
  rewrite BalancedTree.data_remove by eapply FinitePartialMap.data_isSorted.
  eapply OrderedList.remove_sorted. eapply FinitePartialMap.data_isSorted.
Defined.

Lemma data_remove (k : K) (m : fpmap K V)
  : FinitePartialMap.data (remove k m) = OrderedList.remove fst k (FinitePartialMap.data m).
Proof.
  unfold remove, FinitePartialMap.data. cbn [FinitePartialMap.tree].
  eapply BalancedTree.data_remove. eapply FinitePartialMap.data_isSorted.
Qed.

Theorem lookup_remove_eq (k : K) (m : fpmap K V)
  : lookup k (remove k m) = None.
Proof.
  rewrite lookup_data, data_remove. unfold lookup'.
  now rewrite OrderedList.lookup_remove_eq by eapply FinitePartialMap.data_isSorted.
Qed.

Theorem lookup_remove_ne (k : K) (m : fpmap K V) (k0 : K)
  (NE : ~ k0 == k)
  : lookup k0 (remove k m) = lookup k0 m.
Proof.
  rewrite !lookup_data, data_remove. unfold lookup'.
  now rewrite OrderedList.lookup_remove_ne by (try exact NE; eapply FinitePartialMap.data_isSorted).
Qed.

#[refine]
Definition keys (m : fpmap K V) : fset K :=
  {| FSet.tree := BalancedTree.map (@fst K V) m.(FinitePartialMap.tree); FSet.data_isSorted := _ |}.
Proof.
  rewrite BalancedTree.data_map. eapply FinitePartialMap.data_isSorted.
Defined.

Lemma data_keys (m : fpmap K V)
  : FSet.data (keys m) = L.map fst (FinitePartialMap.data m).
Proof.
  unfold keys, FSet.data, FinitePartialMap.data. cbn [FSet.tree]. eapply BalancedTree.data_map.
Qed.

Theorem in_keys_iff (m : fpmap K V) (k : K)
  : FS.In k (keys m) <-> (exists v, lookup k m = Some v).
Proof.
  unfold FS.In. rewrite data_keys, InA_alt. split.
  - intros (q & EQ & IN). rewrite L.in_map_iff in IN. find* ([q' v] & EQ' & IN') by IN.
    cbn [fst] in EQ'. subst q'. exists v. rewrite lookup_spec. exists q. auto.
  - intros [v LOOK]. rewrite lookup_spec in LOOK. find* [q [EQ IN]] by LOOK. exists q. split; auto.
    rewrite L.in_map_iff. exists (q, v). auto.
Qed.

End BASICS.

Section SETOID.

Context {K : Type} {V : Type} {PROSET : isProset K} {ORD : hsOrd K} {SETOID : isSetoid V}.
Let pair_setoid := @prod_isSetoid K V PROSET.(Proset_isSetoid) SETOID.
Let list_setoid := L.list_isSetoid pair_setoid.
Let option_setoid := option_isSetoid SETOID.
#[local] Existing Instance option_setoid.

#[global]
Instance fpmap_isSetoid : isSetoid (fpmap K V) | 0 :=
  { eqProp (m : fpmap K V) (m' : fpmap K V) := forall k : K, lookup k m == lookup k m'
  ; eqProp_Equivalence := relation_on_image_liftsEquivalence (pi_isSetoid (fun _ : K => option_setoid)).(eqProp_Equivalence) (fun m : fpmap K V => fun k : K => lookup k m)
  }.

Theorem fpmap_eq_spec (m : fpmap K V) (m' : fpmap K V)
  : m == m' <-> (forall k, lookup k m == lookup k m').
Proof.
  reflexivity.
Qed.

Theorem extensionality (m : fpmap K V) (m' : fpmap K V)
  (EXT : forall k, lookup k m == lookup k m')
  : m == m'.
Proof.
  exact EXT.
Qed.

#[global]
Instance lookup_eqPropCompatible2
  : eqPropCompatible2 (@lookup K V PROSET ORD).
Proof.
  intros k k' m m' EQ EXT. rewrite lookup_compat_key with (k' := k') by exact EQ. exact (EXT k').
Qed.

Definition In (p : K * V) (m : fpmap K V) : Prop :=
  InA (@eqProp (K * V) pair_setoid) p (FinitePartialMap.data m).

Theorem lookup_setoid_spec (m : fpmap K V) (k : K) (v : V)
  : lookup k m == Some v <-> In (k, v) m.
Proof.
  split.
  - intros LOOK. inversion LOOK as [ | v' v'' EQ]; subst.
    symmetry in H. rewrite lookup_spec in H. find* [q [KEY IN]] by H. unfold In. rewrite InA_alt. exists (q, v'). split; auto.
    split; [exact KEY | symmetry; exact EQ].
  - intros IN. unfold In in IN. rewrite InA_alt in IN. find* ([q v'] & [KEY VALUE] & IN') by IN. cbn [fst snd] in KEY, VALUE.
    assert (LOOK : lookup k m = Some v').
    { rewrite lookup_spec. exists q. auto. }
    rewrite LOOK. constructor. symmetry. exact VALUE.
Qed.

#[global]
Instance insert_compat
  : Proper (eqProp ==> eqProp ==> eqProp ==> eqProp) (@insert K V PROSET ORD).
Proof.
  intros k k' KEY v v' VALUE m m' EXT q.
  destruct (compare q k) eqn: OBS.
  - assert (QK : q == k) by now rewrite <- compare_Eq_iff.
    assert (QK' : q == k') by (transitivity k; assumption).
    rewrite lookup_compat_key with (m := insert k v m) (k' := k) by exact QK.
    rewrite lookup_compat_key with (m := insert k' v' m') (k' := k') by exact QK'.
    rewrite !lookup_insert_eq. constructor. exact VALUE.
  - assert (NE : ~ q == k) by (intros EQ; rewrite <- compare_Eq_iff in EQ; congruence).
    assert (NE' : ~ q == k') by (intros EQ; eapply NE; transitivity k'; [exact EQ | symmetry; exact KEY]).
    rewrite !lookup_insert_ne by assumption. exact (EXT q).
  - assert (NE : ~ q == k) by (intros EQ; rewrite <- compare_Eq_iff in EQ; congruence).
    assert (NE' : ~ q == k') by (intros EQ; eapply NE; transitivity k'; [exact EQ | symmetry; exact KEY]).
    rewrite !lookup_insert_ne by assumption. exact (EXT q).
Qed.

#[global]
Instance remove_eqPropCompatible2
  : eqPropCompatible2 (@remove K V PROSET ORD).
Proof.
  intros k k' m m' KEY EXT q.
  destruct (compare q k) eqn: OBS.
  - assert (QK : q == k) by now rewrite <- compare_Eq_iff.
    assert (QK' : q == k') by (transitivity k; assumption).
    rewrite lookup_compat_key with (m := remove k m) (k' := k) by exact QK.
    rewrite lookup_compat_key with (m := remove k' m') (k' := k') by exact QK'.
    rewrite !lookup_remove_eq. reflexivity.
  - assert (NE : ~ q == k) by (intros EQ; rewrite <- compare_Eq_iff in EQ; congruence).
    assert (NE' : ~ q == k') by (intros EQ; eapply NE; transitivity k'; [exact EQ | symmetry; exact KEY]).
    rewrite !lookup_remove_ne by assumption. exact (EXT q).
  - assert (NE : ~ q == k) by (intros EQ; rewrite <- compare_Eq_iff in EQ; congruence).
    assert (NE' : ~ q == k') by (intros EQ; eapply NE; transitivity k'; [exact EQ | symmetry; exact KEY]).
    rewrite !lookup_remove_ne by assumption. exact (EXT q).
Qed.

Lemma lookup'_compat (xs : list (K * V)) (ys : list (K * V))
  (EQ : @eqProp _ list_setoid xs ys)
  : forall k, lookup' k xs == lookup' k ys.
Proof.
  revert ys EQ. induction xs as [ | [q v] xs IH]; intros [ | [q' v'] ys] EQ k.
  - reflexivity.
  - specialize (EQ 0). inv EQ.
  - specialize (EQ 0). inv EQ.
  - obtain HEAD with 0 by EQ. inversion HEAD as [ | p p' [KEY VALUE]]; subst.
    change (q == q') in KEY. change (v == v') in VALUE.
    assert (TAIL : @eqProp _ list_setoid xs ys) by exact (fun n => EQ (S n)).
    unfold lookup'. cbn [OrderedList.lookup fst].
    rewrite compare_compatWith_eqProp with (x' := k) (y' := q') by (assumption || reflexivity).
    destruct (compare k q'); simpl; [constructor; exact VALUE | reflexivity | ].
    eapply IH. exact TAIL.
Qed.

Lemma lookup'_extensionality (xs : list (K * V)) (ys : list (K * V))
  (SORTED_XS : isSorted compare (map fst xs) = true)
  (SORTED_YS : isSorted compare (map fst ys) = true)
  (EXT : forall k, lookup' k xs == lookup' k ys)
  : @eqProp _ list_setoid xs ys.
Proof.
  revert ys SORTED_XS SORTED_YS EXT. induction xs as [ | [q v] xs IH]; intros [ | [q' v'] ys] SX SY EXT.
  - reflexivity.
  - specialize (EXT q'). unfold lookup' in EXT. cbn [OrderedList.lookup fst] in EXT.
    rewrite compare_refl in EXT. inv EXT.
  - specialize (EXT q). unfold lookup' in EXT. cbn [OrderedList.lookup fst] in EXT.
    rewrite compare_refl in EXT. inv EXT.
  - rewrite OrderedList.sorted_cons_iff in SX, SY.
    find* [HX TX] by SX. find* [HY TY] by SY. cbn [fst] in HX, HY.
    assert (KEY : q == q').
    { destruct (compare q q') eqn: OBS; [now rewrite <- compare_Eq_iff | | ].
      - specialize (EXT q). unfold lookup' in EXT. cbn [OrderedList.lookup fst] in EXT.
        rewrite compare_refl, OBS in EXT. inv EXT.
      - specialize (EXT q'). unfold lookup' in EXT. cbn [OrderedList.lookup fst] in EXT.
        rewrite compare_refl in EXT. rewrite compare_Gt_flip in EXT by exact OBS. inv EXT.
    }
    assert (VALUE : v == v').
    { specialize (EXT q). unfold lookup' in EXT. cbn [OrderedList.lookup fst] in EXT.
      rewrite <- compare_Eq_iff in KEY. rewrite compare_refl, KEY in EXT. inv EXT. assumption.
    }
    assert (TAIL : forall k, lookup' k xs == lookup' k ys).
    { intros k. destruct (compare k q) eqn: OBS.
      - assert (LX : OrderedList.lookup (@fst K V) k xs = None).
        { eapply OrderedList.lookup_lt_None. intros p IN.
          rewrite compare_compatWith_eqProp with (x' := q) (y' := fst p) by (reflexivity || now rewrite <- compare_Eq_iff).
          now eapply HX.
        }
        assert (LY : OrderedList.lookup (@fst K V) k ys = None).
        { eapply OrderedList.lookup_lt_None. intros p IN.
          assert (KQ : k == q') by (transitivity q; [now rewrite <- compare_Eq_iff | exact KEY]).
          rewrite compare_compatWith_eqProp with (x' := q') (y' := fst p) by (assumption || reflexivity).
          now eapply HY.
        }
        unfold lookup'. rewrite LX, LY. reflexivity.
      - assert (LX : OrderedList.lookup (@fst K V) k xs = None).
        { eapply OrderedList.lookup_lt_None. intros p IN. eapply compare_Lt_trans; [exact OBS | now eapply HX]. }
        assert (LY : OrderedList.lookup (@fst K V) k ys = None).
        { eapply OrderedList.lookup_lt_None. i. eapply compare_Lt_trans; [ | now eapply HY].
          rewrite <- compare_compatWith_eqProp with (x := k) (x' := k) (y := q) (y' := q') by (assumption || reflexivity). exact OBS.
        }
        unfold lookup'. rewrite LX, LY. reflexivity.
      - specialize (EXT k). unfold lookup' in EXT. cbn [OrderedList.lookup fst] in EXT.
        rewrite <- compare_compatWith_eqProp with (x := k) (x' := k) (y := q) (y' := q') in EXT by (assumption || reflexivity).
        rewrite OBS in EXT. exact EXT.
    }
    obtain REST with ys TX TY TAIL by IH.
    intros [ | n]; simpl; [constructor; split; assumption | exact (REST n)].
Qed.

Theorem data_eq_spec (m : fpmap K V) (m' : fpmap K V)
  : m == m' <-> @eqProp _ list_setoid (FinitePartialMap.data m) (FinitePartialMap.data m').
Proof.
  split.
  - intros EXT. eapply lookup'_extensionality; try eapply FinitePartialMap.data_isSorted.
    intros k. rewrite <- !lookup_data. exact (EXT k).
  - intros EQ k. rewrite !lookup_data. now eapply lookup'_compat.
Qed.

End SETOID.

Section ORDERED_MAP.

Context {K : Type} {V : Type} {PK : isProset K} {OK : hsOrd K} {PV : isProset V} {OV : hsOrd V}.

#[local] Existing Instances pair_isProset pair_hsOrd.

Let entries_proset := @list_lexicographical_order (K * V) (@pair_isProset K V PK PV OK OV) (@pair_hsOrd K V PK PV OK OV).

Let entries_ord := @list_hsOrd (K * V) (@pair_isProset K V PK PV OK OV) (@pair_hsOrd K V PK PV OK OV).

#[global, refine]
Instance fpmap_isProset : isProset (fpmap K V) :=
  { leProp (m : fpmap K V) (m' : fpmap K V) := lex_le (FinitePartialMap.data m) (FinitePartialMap.data m')
  ; Proset_isSetoid := fpmap_isSetoid
  }.
Proof.
  - exact (relation_on_image_liftsPreOrder (@lex_le_PreOrder (K * V) (@pair_isProset K V PK PV OK OV) (@pair_hsOrd K V PK PV OK OV)) (@FinitePartialMap.data K V _)).
  - intros m m'. change (m == m' <-> (lex_le (FinitePartialMap.data m) (FinitePartialMap.data m') /\ lex_le (FinitePartialMap.data m') (FinitePartialMap.data m))).
    rewrite data_eq_spec. rewrite <- @lex_eq_iff with (PROSET := @pair_isProset K V PK PV OK OV) (ORD := @pair_hsOrd K V PK PV OK OV).
    eapply lex_le_PartialOrder.
Defined.

#[global, refine]
Instance fpmap_hsOrd : hsOrd (fpmap K V) (PROSET := fpmap_isProset) :=
  { compare (m : fpmap K V) (m' : fpmap K V) := lex_compare (FinitePartialMap.data m) (FinitePartialMap.data m') }.
Proof.
  - intros m m' OBS. obtain [LE NE] with OBS by (@compare_Lt _ entries_proset entries_ord).
    split; [exact LE | intros EQ; eapply NE]. now eapply data_eq_spec.
  - intros m m' OBS. eapply data_eq_spec.
    exact (@compare_Eq _ entries_proset entries_ord (FinitePartialMap.data m) (FinitePartialMap.data m') OBS).
  - intros m m' OBS. obtain [LE NE] with OBS by (@compare_Gt _ entries_proset entries_ord).
    split; [exact LE | intros EQ; eapply NE]. now eapply data_eq_spec.
Defined.

End ORDERED_MAP.

Section MAP.

Context {K : Type} {V : Type} {W : Type} {PROSET : isProset K} {ORD : hsOrd K}.

#[refine]
Definition map (f : V -> W) (m : fpmap K V) : fpmap K W :=
  {| FinitePartialMap.tree := BalancedTree.map (fun p => (fst p, f (snd p))) m.(FinitePartialMap.tree); FinitePartialMap.data_isSorted := _ |}.
Proof.
  rewrite BalancedTree.data_map, L.map_map. cbn [fst]. eapply FinitePartialMap.data_isSorted.
Defined.

Lemma data_map (f : V -> W) (m : fpmap K V)
  : FinitePartialMap.data (map f m) = L.map (fun p => (fst p, f (snd p))) (FinitePartialMap.data m).
Proof.
  unfold map, FinitePartialMap.data. cbn [FinitePartialMap.tree]. eapply BalancedTree.data_map.
Qed.

Lemma lookup_map (f : V -> W) (m : fpmap K V) (k : K)
  : lookup k (map f m) = option_map f (lookup k m).
Proof.
  rewrite !lookup_data, data_map. unfold lookup'.
  generalize (FinitePartialMap.data m) as xs. intros xs.
  induction xs as [ | [q v] xs IH]; simpl; auto.
  destruct (compare k q); simpl; auto.
Qed.

End MAP.

Section MAP_SETOID.

Context {K : Type} {V : Type} {W : Type} {PROSET : isProset K} {ORD : hsOrd K} {SV : isSetoid V} {SW : isSetoid W}.

#[global]
Instance map_compat
  : Proper ((eqProp ==> eqProp) ==> eqProp ==> eqProp) (@map K V W PROSET ORD).
Proof.
  intros f g FG m m' EXT k. rewrite !lookup_map.
  specialize (EXT k). destruct (lookup k m), (lookup k m'); inv EXT; simpl; constructor.
  now eapply FG.
Qed.

End MAP_SETOID.

#[global]
Instance fpmap_isFunctor {K : Type} {PROSET : isProset K} {ORD : hsOrd K} : isFunctor (fpmap K) :=
  fun V => fun W => @map K V W PROSET ORD.

#[global]
Instance fpmap_isSetoid1 {K : Type} {PROSET : isProset K} {ORD : hsOrd K} : isSetoid1 (fpmap K) :=
  fun V => @fpmap_isSetoid K V PROSET ORD.

#[global]
Instance fpmap_FunctorLaws {K : Type} {PROSET : isProset K} {ORD : hsOrd K}
  : FunctorLaws (fpmap K) (SETOID1 := fpmap_isSetoid1) (FUNCTOR := fpmap_isFunctor).
Proof.
  split.
  - intros A B f m m' EQ k. change (option_eqProp eq (lookup k (map f m)) (lookup k (map f m'))).
    rewrite !lookup_map. specialize (EQ k). apply option_eqProp_iff_eq in EQ.
    rewrite EQ. reflexivity.
  - intros A B C f g m k. change (option_eqProp eq (lookup k (map (compose g f) m)) (lookup k (map g (map f m)))).
    rewrite !lookup_map. destruct (lookup k m); reflexivity.
  - intros A m k. change (option_eqProp eq (lookup k (map id m)) (lookup k m)).
    rewrite lookup_map. destruct (lookup k m); reflexivity.
  - intros A B f g EQ m k. change (option_eqProp eq (lookup k (map f m)) (lookup k (map g m))).
    rewrite !lookup_map. destruct (lookup k m); simpl; constructor. eapply EQ.
Qed.

Section SIMILARITY.

#[local] Existing Instance Similarity_option_option.

Definition Similarity_fpmap_partial_map {K : Type} {V : Type} {PROSET : isProset K} {ORD : hsOrd K} {K' : Type} {V' : Type} (KEYS : Similarity K K') (VALUES : Similarity V V') : Similarity (fpmap K V) (K' -> option V') :=
  fun m => fun f => forall k, forall k', k =~= k' -> lookup k m =~= f k'.

Context {K : Type} {V : Type} {PROSET : isProset K} {ORD : hsOrd K} {SETOID : isSetoid V}.

#[global]
Instance fpmap_corresponds_to_partial_map : Similarity (fpmap K V) (K -> option V) :=
  fun m => fun f => forall k, option_eqProp eqProp (lookup k m) (f k).

Theorem fpmap_corresponds_to_partial_map_iff (m : fpmap K V) (f : K -> option V)
  : m =~= f <-> (forall k, option_eqProp eqProp (lookup k m) (f k)).
Proof.
  reflexivity.
Qed.

End SIMILARITY.

Section DISCRETE.

Context {K : Type} {V : Type} {POSET : isPoset K} {ORD : HsOrd K}.

Theorem lookup_spec_eq (m : fpmap K V) (k : K) (v : V)
  : lookup k m = Some v <-> L.In (k, v) (FinitePartialMap.data m).
Proof.
  rewrite lookup_spec. split.
  - intros [k' [EQ IN]]. rewrite Poset_eqProp_spec in EQ. now subst k'.
  - intros IN. exists k. split; [reflexivity | exact IN].
Qed.

Theorem lookup_insert_ne_eq (k : K) (v : V) (m : fpmap K V) (k0 : K)
  (NE : k0 <> k)
  : lookup k0 (insert k v m) = lookup k0 m.
Proof.
  eapply lookup_insert_ne. now rewrite Poset_eqProp_spec.
Qed.

Theorem lookup_remove_ne_eq (k : K) (m : fpmap K V) (k0 : K)
  (NE : k0 <> k)
  : lookup k0 (remove k m) = lookup k0 m.
Proof.
  eapply lookup_remove_ne. now rewrite Poset_eqProp_spec.
Qed.

End DISCRETE.

Section FSET_MAP.

Context {K : Type} {Y : Type} {PK : isProset K} {OK : hsOrd K} {PY : isProset Y} {OY : hsOrd Y}.

#[local] Existing Instances pair_isProset pair_hsOrd.

Let table_setoid := @fpmap_isSetoid K (fset Y) PK OK (@fset_isSetoid Y PY OY).

#[local] Existing Instance table_setoid.

Definition lookup_set (table : fpmap K (fset Y)) (k : K) : fset Y :=
  match lookup k table with
  | None => FS.empty
  | Some ys => ys
  end.

Lemma lookup_set_compat_key (table : fpmap K (fset Y)) (k : K) (k' : K)
  (EQ : k == k')
  : lookup_set table k = lookup_set table k'.
Proof.
  unfold lookup_set. now rewrite lookup_compat_key with (k' := k') by exact EQ.
Qed.

#[global]
Instance lookup_set_eqPropCompatible2
  : eqPropCompatible2 (@lookup_set).
Proof.
  intros table table' k k' EXT EQ. rewrite lookup_set_compat_key with (k' := k') by exact EQ.
  specialize (EXT k'). unfold lookup_set.
  destruct (lookup k' table), (lookup k' table'); inv EXT; reflexivity || assumption.
Qed.

Definition add (k : K) (y : Y) (table : fpmap K (fset Y)) : fpmap K (fset Y) :=
  insert k (FS.add y (lookup_set table k)) table.

#[global]
Instance add_compat
  : Proper (eqProp ==> eqProp ==> eqProp ==> eqProp) (@add).
Proof.
  intros k k' KEY y y' VALUE table table' EXT. unfold add.
  eapply insert_compat; auto. eapply FS.add_eqPropCompatible2; auto.
  now eapply lookup_set_eqPropCompatible2.
Qed.

Lemma in_add_iff (k : K) (y : Y) (table : fpmap K (fset Y)) (k' : K) (y' : Y)
  : FS.In y' (lookup_set (add k y table) k') <-> ((k' == k /\ y' == y) \/ FS.In y' (lookup_set table k')).
Proof.
  unfold add. destruct (compare k' k) eqn: OBS.
  - assert (EQ : k' == k) by now rewrite <- compare_Eq_iff.
    unfold lookup_set at 1. rewrite lookup_compat_key with (k' := k) by exact EQ. rewrite lookup_insert_eq.
    rewrite FS.in_add_iff. rewrite lookup_set_compat_key with (k := k') (k' := k) by exact EQ. tauto.
  - assert (NE : ~ k' == k) by (intros EQ; rewrite <- compare_Eq_iff in EQ; congruence).
    unfold lookup_set at 1. rewrite lookup_insert_ne by exact NE.
    fold (lookup_set table k'). tauto.
  - assert (NE : ~ k' == k) by (intros EQ; rewrite <- compare_Eq_iff in EQ; congruence).
    unfold lookup_set at 1. rewrite lookup_insert_ne by exact NE.
    fold (lookup_set table k'). tauto.
Qed.

Definition fromList (facts : list (K * Y)) : fpmap K (fset Y) :=
  fold_left (fun table => fun p => add (fst p) (snd p) table) (rev_append facts []) empty.

Lemma fromList_spec (facts : list (K * Y))
  : fromList facts = fold_right (fun p => add (fst p) (snd p)) empty facts.
Proof.
  unfold fromList. rewrite rev_append_rev, app_nil_r.
  rewrite <- fold_left_rev_right, rev_involutive. reflexivity.
Qed.

Theorem fromList_correct (facts : list (K * Y)) (k : K) (y : Y)
  : FS.In y (lookup_set (fromList facts) k) <-> InA eqProp (k, y) facts.
Proof.
  rewrite fromList_spec. induction facts as [ | [k' y'] facts IH]; cbn [fold_right fst snd].
  - unfold lookup_set. rewrite lookup_empty, FS.in_empty_iff, InA_nil. reflexivity.
  - rewrite in_add_iff, IH, InA_cons. reflexivity.
Qed.

Lemma fromList_nonempty (facts : list (K * Y)) (k : K) (ys : fset Y)
  (LOOK : lookup k (fromList facts) = Some ys)
  : exists y, FS.In y ys.
Proof.
  rewrite fromList_spec in LOOK. revert LOOK.
  induction facts as [ | [q y] facts IH]; cbn [fold_right fst snd]; intros LOOK.
  - rewrite lookup_empty in LOOK. discriminate.
  - unfold add in LOOK. destruct (compare k q) eqn: OBS.
    + rewrite lookup_compat_key with (k' := q) in LOOK by now rewrite <- compare_Eq_iff.
      rewrite lookup_insert_eq in LOOK.
      inv LOOK. exists y. rewrite FS.in_add_iff. left. reflexivity.
    + rewrite lookup_insert_ne in LOOK by (intros EQ; rewrite <- compare_Eq_iff in EQ; congruence).
      now eapply IH.
    + rewrite lookup_insert_ne in LOOK by (intros EQ; rewrite <- compare_Eq_iff in EQ; congruence).
      now eapply IH.
Qed.

#[global]
Instance fromList_compat
  : Proper (equivlistA eqProp ==> eqProp) (@fromList).
Proof.
  intros facts facts' EXT k.
  assert (MEM : forall y, FS.In y (lookup_set (fromList facts) k) <-> FS.In y (lookup_set (fromList facts') k)).
  { intros y. rewrite !fromList_correct. eapply EXT. }
  destruct (lookup k (fromList facts)) as [ys | ] eqn: LOOK; destruct (lookup k (fromList facts')) as [ys' | ] eqn: LOOK'; constructor || idtac.
  - rewrite FS.eq_spec. intros y. specialize (MEM y). unfold lookup_set in MEM.
    now rewrite LOOK, LOOK' in MEM.
  - obtain (y & IN) with LOOK by fromList_nonempty.
    specialize (MEM y). unfold lookup_set in MEM. rewrite LOOK, LOOK', FS.in_empty_iff in MEM. tauto.
  - obtain (y & IN) with LOOK' by fromList_nonempty.
    specialize (MEM y). unfold lookup_set in MEM. rewrite LOOK, LOOK', FS.in_empty_iff in MEM. tauto.
Qed.

Definition fromFSet (facts : fset (K * Y)) : fpmap K (fset Y) :=
  FS.fold_right (fun p => add (fst p) (snd p)) facts empty.

Lemma fromFSet_spec (facts : fset (K * Y))
  : fromFSet facts = fromList (FSet.data facts).
Proof.
  unfold fromFSet. rewrite FS.fold_right_spec, fromList_spec. reflexivity.
Qed.

Theorem fromFSet_correct (facts : fset (K * Y)) (k : K) (y : Y)
  : FS.In y (lookup_set (fromFSet facts) k) <-> FS.In (k, y) facts.
Proof.
  rewrite fromFSet_spec, fromList_correct. reflexivity.
Qed.

#[global]
Instance fromFSet_compat
  : Proper (eqProp ==> eqProp) (@fromFSet).
Proof.
  intros facts facts' EXT. rewrite !fromFSet_spec. eapply fromList_compat. intros p.
  exact (proj1 (@FS.eq_spec (K * Y) (@pair_isProset K Y PK PY OK OY) (@pair_hsOrd K Y PK PY OK OY) facts facts') EXT p).
Qed.

Variable nodes : fset K.

Variable seed : fpmap K (fset Y).

Lemma fold_values_app (q : K) (ys : list Y) (acc : list (K * Y))
  : L.fold_right (fun y => cons (q, y)) acc ys = L.map (pair q) ys ++ acc.
Proof.
  induction ys as [ | y ys IH]; cbn [L.fold_right L.map app]; congruence.
Qed.

Lemma fold_nodes_app (ks : list K) (acc : list (K * Y))
  : L.fold_right (fun k => FS.fold_right (fun y => cons (k, y)) (lookup_set seed k)) acc ks = flat_map (fun k => L.map (pair k) (FSet.data (lookup_set seed k))) ks ++ acc.
Proof.
  induction ks as [ | k ks IH]; cbn [L.fold_right flat_map]; auto.
  rewrite FS.fold_right_spec, fold_values_app, IH, app_assoc. reflexivity.
Qed.

Definition seed_facts : list (K * Y) :=
  FS.fold_right (fun k => FS.fold_right (fun y => cons (k, y)) (lookup_set seed k)) nodes [].

Lemma seed_facts_spec
  : seed_facts = flat_map (fun k => L.map (pair k) (FSet.data (lookup_set seed k))) (FSet.data nodes).
Proof.
  unfold seed_facts. rewrite FS.fold_right_spec, fold_nodes_app, app_nil_r. reflexivity.
Qed.

Lemma in_seed_facts_iff (k : K) (y : Y)
  : InA eqProp (k, y) seed_facts <-> (FS.In k nodes /\ FS.In y (lookup_set seed k)).
Proof.
  rewrite seed_facts_spec. unfold FS.In. rewrite !InA_alt. split.
  - intros ([q w] & [KEY VALUE] & IN). cbn [fst snd] in KEY, VALUE.
    rewrite in_flat_map in IN. find* (q' & IN_Q & IN') by IN.
    rewrite L.in_map_iff in IN'. find* (w' & EQ & IN_W) by IN'. inv EQ.
    split.
    + exists q. auto.
    + rewrite lookup_set_compat_key with (k' := q) by exact KEY. exists w. auto.
  - intros [(q & KEY & IN_Q) IN_Y].
    rewrite lookup_set_compat_key with (k' := q) in IN_Y by exact KEY.
    find* (w & VALUE & IN_W) by IN_Y.
    exists (q, w). split; [split; assumption | ].
    rewrite in_flat_map. exists q. split; auto. rewrite L.in_map_iff. exists w. auto.
Qed.

Lemma in_fold_values (q : K) (ys : list Y) (acc : fset (K * Y)) (p : K * Y)
  : FS.In p (L.fold_right (fun y => FS.add (q, y)) acc ys) <-> (FS.In p acc \/ InA eqProp p (L.map (pair q) ys)).
Proof.
  induction ys as [ | y ys IH]; cbn [L.fold_right L.map].
  - rewrite InA_nil. tauto.
  - rewrite FS.in_add_iff, IH, InA_cons. tauto.
Qed.

Lemma in_fold_nodes (ks : list K) (acc : fset (K * Y)) (p : K * Y)
  : FS.In p (L.fold_right (fun k => FS.fold_right (fun y => FS.add (k, y)) (lookup_set seed k)) acc ks) <-> (FS.In p acc \/ InA eqProp p (flat_map (fun k => L.map (pair k) (FSet.data (lookup_set seed k))) ks)).
Proof.
  induction ks as [ | q ks IH]; cbn [L.fold_right flat_map].
  - rewrite InA_nil. tauto.
  - rewrite FS.fold_right_spec, in_fold_values, IH, InA_app_iff. tauto.
Qed.

Definition initial_facts : fset (K * Y) :=
  FS.fold_right (fun k => FS.fold_right (fun y => FS.add (k, y)) (lookup_set seed k)) nodes FS.empty.

Lemma in_initial_facts_iff (k : K) (y : Y)
  : FS.In (k, y) initial_facts <-> (FS.In k nodes /\ FS.In y (lookup_set seed k)).
Proof.
  unfold initial_facts. rewrite FS.fold_right_spec, in_fold_nodes, FS.in_empty_iff.
  rewrite <- seed_facts_spec, in_seed_facts_iff. tauto.
Qed.

End FSET_MAP.

Section INITIAL_COMPAT.

Context {K : Type} {Y : Type} {PK : isProset K} {OK : hsOrd K} {PY : isProset Y} {OY : hsOrd Y}.

#[local] Existing Instances pair_isProset pair_hsOrd.

#[global]
Instance initial_facts_eqPropCompatible2
  : eqPropCompatible2 (@initial_facts K Y PK OK PY OY).
Proof.
  intros nodes nodes' seed seed' EQ_N EQ_S. rewrite FS.eq_spec. intros [k y].
  rewrite !in_initial_facts_iff.
  rewrite FS.In_compat with (x := k) (y := k) (X := nodes) (Y := nodes') by (reflexivity || exact EQ_N).
  rewrite FS.In_compat with (x := y) (y := y) (X := lookup_set seed k) (Y := lookup_set seed' k) by (reflexivity || now eapply lookup_set_eqPropCompatible2).
  reflexivity.
Qed.

End INITIAL_COMPAT.

Section FSET_MAP_DISCRETE.

Context {K : Type} {Y : Type} {PK : isPoset K} {OK : HsOrd K} {PY : isPoset Y} {OY : HsOrd Y}.

Theorem fromList_correct_eq (facts : list (K * Y)) (k : K) (y : Y)
  : L.In y (FSet.data (lookup_set (fromList facts) k)) <-> L.In (k, y) facts.
Proof.
  rewrite <- !InA_eqProp_iff. eapply fromList_correct.
Qed.

Theorem fromFSet_correct_eq (facts : fset (K * Y)) (k : K) (y : Y)
  : L.In y (FSet.data (lookup_set (fromFSet facts) k)) <-> L.In (k, y) (FSet.data facts).
Proof.
  rewrite <- !InA_eqProp_iff. eapply fromFSet_correct.
Qed.

Theorem in_initial_facts_eq_iff (nodes : fset K) (seed : fpmap K (fset Y)) (k : K) (y : Y)
  : L.In (k, y) (FSet.data (initial_facts nodes seed)) <-> (L.In k (FSet.data nodes) /\ L.In y (FSet.data (lookup_set seed k))).
Proof.
  rewrite <- !InA_eqProp_iff. eapply in_initial_facts_iff.
Qed.

End FSET_MAP_DISCRETE.

End FPM.
