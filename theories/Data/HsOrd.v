Require Import Stdlib.NArith.BinNat.
Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.X.
Require Export PnV.Math.ThN.
Require Export PnV.Math.OrderTheory.

#[global]
Instance comparison_hasEqDec
  : hasEqDec comparison.
Proof.
  red. decide equality.
Defined.

#[universes(template), projections(primitive)]
Class HsOrd `(A : Type) `{POSET : isPoset A} : Type :=
  { HsOrd_hsOrd : hsOrd A (PROSET := POSET.(Poset_isProset)) }.

#[global] Existing Instance HsOrd_hsOrd.

Definition isSorted {A : Type} (compare : A -> A -> comparison) : list A -> bool :=
  fix go (xs : list A) {struct xs} : bool :=
  match xs with
  | [] => true
  | x :: xs' => forallb (fun x' : A => Prelude.eqb (compare x x') Lt) xs' && go xs'
  end.

Section PROSET_FACTS.

Context {A : Type} {PROSET : isProset A} {ORD : hsOrd A (PROSET := PROSET)}.

Lemma compare_refl (x : A)
  : compare x x = Eq.
Proof.
  destruct (compare x x) as [ | | ] eqn: H_OBS; trivial.
  - pose proof (compare_Lt x x H_OBS) as [_ x_ne_x]. contradiction x_ne_x. reflexivity.
  - pose proof (compare_Gt x x H_OBS) as [_ x_ne_x]. contradiction x_ne_x. reflexivity.
Qed.

Lemma compare_Eq_iff (x : A) (y : A)
  : compare x y = Eq <-> x == y.
Proof.
  split.
  - exact (compare_Eq x y).
  - intros x_eq_y. destruct (compare x y) as [ | | ] eqn: H_OBS; trivial.
    + pose proof (compare_Lt x y H_OBS) as [_ x_ne_y]. contradiction.
    + pose proof (compare_Gt x y H_OBS) as [_ x_ne_y]. contradiction.
Qed.

Lemma compare_Gt_flip (x : A) (y : A)
  (OBS_Gt : compare x y = Gt)
  : compare y x = Lt.
Proof.
  pose proof (compare_Gt x y OBS_Gt) as [y_le_x x_ne_y].
  destruct (compare y x) as [ | | ] eqn: H_OBS; trivial.
  - contradiction x_ne_y. symmetry. exact (compare_Eq y x H_OBS).
  - pose proof (compare_Gt y x H_OBS) as [x_le_y _].
    contradiction x_ne_y. now eapply leProp_antisymmetry.
Qed.

Lemma compare_Lt_flip (x : A) (y : A)
  (OBS_Lt : compare x y = Lt)
  : compare y x = Gt.
Proof.
  pose proof (compare_Lt x y OBS_Lt) as [x_le_y x_ne_y].
  destruct (compare y x) as [ | | ] eqn: H_OBS; trivial.
  - contradiction x_ne_y. symmetry. exact (compare_Eq y x H_OBS).
  - pose proof (compare_Lt y x H_OBS) as [y_le_x _].
    contradiction x_ne_y. now eapply leProp_antisymmetry.
Qed.

Corollary compare_Gt_iff (x : A) (y : A)
  : compare x y = Gt <-> compare y x = Lt.
Proof.
  split; [exact (compare_Gt_flip x y) | exact (compare_Lt_flip y x)].
Qed.

Lemma compare_compatWith_eqProp (x : A) (x' : A) (y : A) (y' : A)
  (x_EQ : x == x')
  (y_EQ : y == y')
  : compare x y = compare x' y'.
Proof.
  assert (LEMMA : forall u : A, forall u' : A, forall v : A, forall v' : A, u == u' -> v == v' -> compare u v = Lt -> compare u' v' = Lt).
  { intros u u' v v' u_EQ v_EQ OBS_Lt.
    pose proof (compare_Lt u v OBS_Lt) as [u_le_v u_ne_v].
    assert (u'_le_v' : u' =< v').
    { transitivity u. { eapply eqProp_implies_leProp. now symmetry. }
      transitivity v; [exact u_le_v | now eapply eqProp_implies_leProp].
    }
    assert (u'_ne_v' : ~ u' == v').
    { intros CONTRA. contradiction u_ne_v.
      transitivity u'; [exact u_EQ | ]. transitivity v'; [exact CONTRA | now symmetry].
    }
    destruct (compare u' v') as [ | | ] eqn: H_OBS; trivial.
    - contradiction u'_ne_v'. exact (compare_Eq u' v' H_OBS).
    - pose proof (compare_Gt u' v' H_OBS) as [v'_le_u' _].
      contradiction u'_ne_v'. now eapply leProp_antisymmetry.
  }
  destruct (compare x y) as [ | | ] eqn: H_OBS; symmetry.
  - eapply compare_Eq_iff. transitivity x; [now symmetry | ].
    transitivity y; [eapply compare_Eq_iff; exact H_OBS | exact y_EQ].
  - exact (LEMMA x x' y y' x_EQ y_EQ H_OBS).
  - eapply compare_Lt_flip. exact (LEMMA y y' x x' y_EQ x_EQ (compare_Gt_flip x y H_OBS)).
Qed.

Lemma compare_Lt_trans (x : A) (y : A) (z : A)
  (OBS_Lt1 : compare x y = Lt)
  (OBS_Lt2 : compare y z = Lt)
  : compare x z = Lt.
Proof.
  pose proof (compare_Lt x y OBS_Lt1) as [x_le_y x_ne_y].
  pose proof (compare_Lt y z OBS_Lt2) as [y_le_z y_ne_z].
  assert (x_le_z : x =< z) by now transitivity y.
  destruct (compare x z) as [ | | ] eqn: H_OBS; trivial.
  - pose proof (compare_Eq x z H_OBS) as x_eq_z.
    contradiction x_ne_y. eapply leProp_antisymmetry; [exact x_le_y | ].
    transitivity z; [exact y_le_z | eapply eqProp_implies_leProp; now symmetry].
  - pose proof (compare_Gt x z H_OBS) as [z_le_x x_ne_z].
    contradiction x_ne_z. now eapply leProp_antisymmetry.
Qed.

Lemma isSorted_cons_iff (x : A) (xs : list A)
  : isSorted compare (x :: xs) = true <-> ((forall z : A, L.In z xs -> compare x z = Lt) /\ isSorted compare xs = true).
Proof.
  simpl. rewrite andb_true_iff, forallb_forall. split.
  - intros [SORTED_hd SORTED_tl]. split; auto.
    intros z z_in. rewrite <- eqb_eq. exact (SORTED_hd z z_in).
  - intros [SORTED_hd SORTED_tl]. split; auto.
    intros z z_in. rewrite -> eqb_eq. exact (SORTED_hd z z_in).
Qed.

Lemma isSorted_app (l1 : list A) (l2 : list A)
  (H1_isSorted : isSorted compare l1 = true)
  (H2_isSorted : isSorted compare l2 = true)
  (CROSS : forall x : A, forall y : A, L.In x l1 -> L.In y l2 -> compare x y = Lt)
  : isSorted compare (l1 ++ l2) = true.
Proof.
  revert H1_isSorted CROSS. induction l1 as [ | x l1 IH]; intros H1_isSorted CROSS; [exact H2_isSorted | simpl app].
  rewrite isSorted_cons_iff in H1_isSorted |- *. destruct H1_isSorted as [x_lt_l1 l1_sorted]. split.
  - intros z z_in. rewrite L.in_app_iff in z_in. destruct z_in as [z_in | z_in].
    + exact (x_lt_l1 z z_in).
    + eapply CROSS; [now left | exact z_in].
  - eapply IH; [exact l1_sorted | intros u v u_in v_in].
    eapply CROSS; [now right | exact v_in].
Qed.

End PROSET_FACTS.

Class hsOrdLaws {A : Type} {SETOID : isSetoid A} (cmp : A -> A -> comparison) : Prop :=
  { cmp_Eq_iff (x : A) (y : A)
    : cmp x y = Eq <-> x == y
  ; cmp_Gt_flip (x : A) (y : A)
    (OBS_Gt : cmp x y = Gt)
    : cmp y x = Lt
  ; cmp_Lt_trans (x : A) (y : A) (z : A)
    (OBS_Lt1 : cmp x y = Lt)
    (OBS_Lt2 : cmp y z = Lt)
    : cmp x z = Lt
  ; cmp_compatWith_eqProp (x : A) (x' : A) (y : A) (y' : A)
    (x_EQ : x == x')
    (y_EQ : y == y')
    : cmp x y = cmp x' y'
  } as LAWS.

Section MAKE_hsOrd.

Context {A : Type} {SETOID : isSetoid A}.

Variable cmp : A -> A -> comparison.

Hypothesis LAWS : hsOrdLaws cmp.

Lemma cmp_refl (x : A)
  : cmp x x = Eq.
Proof.
  eapply LAWS.(cmp_Eq_iff). reflexivity.
Qed.

Definition leProp_of_compare (x : A) (y : A) : Prop :=
  cmp x y = Lt \/ cmp x y = Eq.

Lemma leProp_of_compare_intro_Lt (x : A) (y : A)
  (OBS_Lt : cmp x y = Lt)
  : leProp_of_compare x y.
Proof.
  left. exact OBS_Lt.
Qed.

#[local]
Instance leProp_of_compare_PreOrder
  : PreOrder leProp_of_compare.
Proof.
  split.
  - intros x. right. exact (cmp_refl x).
  - intros x y z [LT1 | EQ1] [LT2 | EQ2].
    + left. exact (LAWS.(cmp_Lt_trans) x y z LT1 LT2).
    + left. rewrite <- LT1. eapply LAWS.(cmp_compatWith_eqProp).
      * reflexivity.
      * symmetry. eapply LAWS.(cmp_Eq_iff). exact EQ2.
    + left. rewrite <- LT2. eapply LAWS.(cmp_compatWith_eqProp).
      * eapply LAWS.(cmp_Eq_iff). exact EQ1.
      * reflexivity.
    + right. eapply LAWS.(cmp_Eq_iff). transitivity y; eapply LAWS.(cmp_Eq_iff); assumption.
Qed.

#[local]
Instance leProp_of_compare_PartialOrder
  : PartialOrder eqProp leProp_of_compare.
Proof.
  intros x y. cbn. unfold flip. split.
  - intros x_eq_y. split.
    + right. eapply LAWS.(cmp_Eq_iff). exact x_eq_y.
    + right. eapply LAWS.(cmp_Eq_iff). now symmetry.
  - intros [[LT1 | EQ1] [LT2 | EQ2]].
    + pose proof (LAWS.(cmp_Lt_trans) x y x LT1 LT2) as LT.
      rewrite cmp_refl in LT. discriminate LT.
    + symmetry. eapply LAWS.(cmp_Eq_iff). exact EQ2.
    + eapply LAWS.(cmp_Eq_iff). exact EQ1.
    + eapply LAWS.(cmp_Eq_iff). exact EQ1.
Qed.

Definition mkProsetFrom_compare : isProset A :=
  {|
    leProp := leProp_of_compare;
    Proset_isSetoid := SETOID;
    leProp_PreOrder := leProp_of_compare_PreOrder;
    leProp_PartialOrder := leProp_of_compare_PartialOrder;
  |}.

#[local] Obligation Tactic := idtac.

#[local, program]
Instance mkHsOrdFrom_compare : hsOrd A (PROSET := mkProsetFrom_compare) :=
  { compare := cmp }.
Next Obligation.
  intros x y OBS_Lt. split.
  - exact (leProp_of_compare_intro_Lt x y OBS_Lt).
  - intros CONTRA. rewrite (proj2 (LAWS.(cmp_Eq_iff) x y) CONTRA) in OBS_Lt. discriminate OBS_Lt.
Qed.
Next Obligation.
  intros x y OBS_Eq. exact (proj1 (LAWS.(cmp_Eq_iff) x y) OBS_Eq).
Qed.
Next Obligation.
  intros x y OBS_Gt. split.
  - exact (leProp_of_compare_intro_Lt y x (LAWS.(cmp_Gt_flip) x y OBS_Gt)).
  - intros CONTRA. rewrite (proj2 (LAWS.(cmp_Eq_iff) x y) CONTRA) in OBS_Gt. discriminate OBS_Gt.
Qed.

End MAKE_hsOrd.

Section POSET_FACTS.

Context {A : Type} {POSET : isPoset A} {HS_ORD : HsOrd A (POSET := POSET)}.

Lemma compare_eq_iff (x : A) (y : A)
  : compare x y = Eq <-> x = y.
Proof.
  rewrite compare_Eq_iff. exact (Poset_eqProp_spec x y).
Qed.

End POSET_FACTS.

#[global]
Instance HsOrd_implies_EqDec {A : Type} `{POSET_A : isPoset A}
  (HsOrd_A : HsOrd A)
  : hasEqDec A.
Proof.
  intros x y.
  destruct (compare x y) as [ | | ] eqn: H_OBS.
  - left. rewrite compare_eq_iff in H_OBS. exact H_OBS.
  - right. intros H_eq. rewrite <- compare_eq_iff in H_eq. congruence.
  - right. intros H_eq. rewrite <- compare_eq_iff in H_eq. congruence.
Defined.

Section HsOrd_list.

Context {A : Type} {POSET : isPoset A} {HS_ORD : HsOrd A (POSET := POSET)}.

#[global, program]
Instance list_isPoset : isPoset (list A) :=
  { Poset_isProset := @list_lexicographical_order A POSET.(Poset_isProset) HS_ORD.(HsOrd_hsOrd) }.
Next Obligation.
  rename x into xs, y into ys. change (eqProp (isSetoid := L.list_isSetoid POSET.(Poset_isProset).(Proset_isSetoid)) xs ys <-> xs = ys). split.
  - rewrite <- lex_eq_iff. intros H_eq. red in H_eq. revert xs ys H_eq.
    induction xs as [ | x xs IH], ys as [ | y ys]; simpl in *; ii; [congruence .. | ].
    destruct (compare x y) as [ | | ] eqn: H_OBS; [f_equal | congruence ..].
    + rewrite <- Poset_eqProp_spec. now eapply compare_Eq.
    + now eapply IH.
  - intros H_eq. subst ys. reflexivity.
Qed.

#[global]
Instance HsOrd_list : HsOrd (list A) (POSET := list_isPoset) :=
  { HsOrd_hsOrd := list_hsOrd }.

End HsOrd_list.

#[global] Arguments HsOrd_list {A} {POSET} HS_ORD.

Section HsOrd_nat.

#[global, program]
Instance nat_isPoset : isPoset nat :=
  { Poset_isProset := nat_isProset }.

#[global]
Instance HsOrd_nat : HsOrd nat (POSET := nat_isPoset) :=
  { HsOrd_hsOrd := nat_hsOrd }.

End HsOrd_nat.

Section HsOrd_N.

#[global]
Instance N_isProset : isProset N :=
  { leProp := N.le
  ; Proset_isSetoid := mkSetoid_from_eq
  ; leProp_PreOrder := N.le_preorder
  ; leProp_PartialOrder := N.le_partialorder
  }.

Lemma N_compare_lt (x : N) (y : N)
  (hyp_lt : N.compare x y = Lt)
  : (x <= y)%N /\ x ≠ y.
Proof.
  rewrite N.compare_lt_iff in hyp_lt. split; lia.
Qed.

Lemma N_compare_eq (x : N) (y : N)
  (hyp_eq : N.compare x y = Eq)
  : x = y.
Proof.
  rewrite N.compare_eq_iff in hyp_eq. exact hyp_eq.
Qed.

Lemma N_compare_gt (x : N) (y : N)
  (hyp_gt : N.compare x y = Gt)
  : (y <= x)%N /\ x ≠ y.
Proof.
  rewrite N.compare_gt_iff in hyp_gt. split; lia.
Qed.

#[local]
Instance N_hsOrd : hsOrd N (PROSET := N_isProset) :=
  { compare := N.compare
  ; compare_Lt := N_compare_lt
  ; compare_Eq := N_compare_eq
  ; compare_Gt := N_compare_gt
  }.

#[global, program]
Instance N_isPoset : isPoset N :=
  { Poset_isProset := N_isProset }.

#[global]
Instance HsOrd_N : HsOrd N (POSET := N_isPoset) :=
  { HsOrd_hsOrd := N_hsOrd }.

Lemma compare_N_Lt_iff (x : N) (y : N)
  : compare x y = Lt <-> (x < y)%N.
Proof.
  exact (N.compare_lt_iff x y).
Qed.

End HsOrd_N.

Section hsOrd_unit.

Definition unit_compare (x : unit) (y : unit) : comparison :=
  Eq.

Lemma unit_compare_Eq_iff (x : unit) (y : unit)
  : unit_compare x y = Eq <-> x == y.
Proof.
  split; intros _; [exact I | reflexivity].
Qed.

Lemma unit_compare_Gt_flip (x : unit) (y : unit)
  (OBS_Gt : unit_compare x y = Gt)
  : unit_compare y x = Lt.
Proof.
  discriminate OBS_Gt.
Qed.

Lemma unit_compare_Lt_trans (x : unit) (y : unit) (z : unit)
  (OBS_Lt1 : unit_compare x y = Lt)
  (OBS_Lt2 : unit_compare y z = Lt)
  : unit_compare x z = Lt.
Proof.
  discriminate OBS_Lt1.
Qed.

Lemma unit_compare_compatWith_eqProp (x : unit) (x' : unit) (y : unit) (y' : unit)
  (x_EQ : x == x')
  (y_EQ : y == y')
  : unit_compare x y = unit_compare x' y'.
Proof.
  reflexivity.
Qed.

Lemma unit_compare_good
  : hsOrdLaws (SETOID := unit_isSetoid) unit_compare.
Proof.
  split.
  - exact unit_compare_Eq_iff.
  - exact unit_compare_Gt_flip.
  - exact unit_compare_Lt_trans.
  - exact unit_compare_compatWith_eqProp.
Qed.

#[local]
Instance unit_isProset : isProset unit :=
  @mkProsetFrom_compare unit unit_isSetoid unit_compare unit_compare_good.

#[local]
Instance unit_hsOrd : hsOrd unit (PROSET := unit_isProset) :=
  @mkHsOrdFrom_compare unit unit_isSetoid unit_compare unit_compare_good.

End hsOrd_unit.

Section HsOrd_unit.

#[local] Obligation Tactic := idtac.

#[global, program]
Instance unit_isPoset : isPoset unit :=
  { Poset_isProset := unit_isProset }.
Next Obligation.
  intros x y. destruct x, y. split; intros _; reflexivity.
Qed.

#[global]
Instance HsOrd_unit : HsOrd unit (POSET := unit_isPoset) :=
  { HsOrd_hsOrd := unit_hsOrd }.

End HsOrd_unit.

Section hsOrd_pair.

Context {A : Type} {B : Type} {A_isProset : isProset A} {B_isProset : isProset B}.

Context {A_hsOrd : hsOrd A (PROSET := A_isProset)} {B_hsOrd : hsOrd B (PROSET := B_isProset)}.

#[local] Existing Instance directProduct_of_two_Setoids.

Definition pair_compare (p : A * B) (p' : A * B) : comparison :=
  match compare (fst p) (fst p') with
  | Lt => Lt
  | Eq => compare (snd p) (snd p')
  | Gt => Gt
  end.

Lemma pair_compare_Eq_iff (p : A * B) (p' : A * B)
  : pair_compare p p' = Eq <-> p == p'.
Proof.
  destruct p as [x1 y1], p' as [x2 y2]. unfold pair_compare. simpl. split.
  - intros OBS_Eq. destruct (compare x1 x2) as [ | | ] eqn: H_OBS; try congruence.
    split; [rewrite <- compare_Eq_iff; exact H_OBS | rewrite <- compare_Eq_iff; exact OBS_Eq].
  - intros [EQ1 EQ2]. rewrite <- compare_Eq_iff in EQ1. rewrite EQ1. now rewrite compare_Eq_iff.
Qed.

Lemma pair_compare_Gt_flip (p : A * B) (p' : A * B)
  (OBS_Gt : pair_compare p p' = Gt)
  : pair_compare p' p = Lt.
Proof.
  destruct p as [x1 y1], p' as [x2 y2]. unfold pair_compare in *. simpl in *.
  destruct (compare x1 x2) as [ | | ] eqn: H_OBS; try congruence.
  - assert (H_OBS' : compare x2 x1 = Eq).
    { eapply compare_Eq_iff. symmetry. eapply compare_Eq_iff. exact H_OBS. }
    rewrite H_OBS'. exact (compare_Gt_flip y1 y2 OBS_Gt).
  - rewrite compare_Gt_flip by exact H_OBS. reflexivity.
Qed.

Lemma pair_compare_Lt_trans (p : A * B) (p' : A * B) (p'' : A * B)
  (OBS_Lt1 : pair_compare p p' = Lt)
  (OBS_Lt2 : pair_compare p' p'' = Lt)
  : pair_compare p p'' = Lt.
Proof.
  destruct p as [x1 y1], p' as [x2 y2], p'' as [x3 y3]. unfold pair_compare in *. simpl in *.
  destruct (compare x1 x2) as [ | | ] eqn: H_OBS1; destruct (compare x2 x3) as [ | | ] eqn: H_OBS2; try congruence.
  - assert (H_OBS : compare x1 x3 = Eq).
    { eapply compare_Eq_iff. transitivity x2; eapply compare_Eq_iff; assumption. }
    rewrite H_OBS. exact (compare_Lt_trans y1 y2 y3 OBS_Lt1 OBS_Lt2).
  - assert (H_OBS : compare x1 x3 = Lt).
    { rewrite (compare_compatWith_eqProp x1 x2 x3 x3 (compare_Eq x1 x2 H_OBS1) (reflexivity x3)). exact H_OBS2. }
    rewrite H_OBS. reflexivity.
  - assert (H_OBS : compare x1 x3 = Lt).
    { rewrite <- (compare_compatWith_eqProp x1 x1 x2 x3 (reflexivity x1) (compare_Eq x2 x3 H_OBS2)). exact H_OBS1. }
    rewrite H_OBS. reflexivity.
  - rewrite (compare_Lt_trans x1 x2 x3 H_OBS1 H_OBS2). reflexivity.
Qed.

Lemma pair_compare_compatWith_eqProp (z : A * B) (p1 : A * B) (p' : A * B) (p1' : A * B)
  (p_EQ : p == p1)
  (p'_EQ : p' == p1')
  : pair_compare p p' = pair_compare p1 p1'.
Proof.
  destruct p as [x1 y1], p1 as [x2 y2], p' as [x3 y3], p1' as [x4 y4].
  destruct p_EQ as [x1_EQ y1_EQ], p'_EQ as [x3_EQ y3_EQ]. unfold pair_compare. simpl in *.
  rewrite (compare_compatWith_eqProp x1 x2 x3 x4 x1_EQ x3_EQ).
  rewrite (compare_compatWith_eqProp y1 y2 y3 y4 y1_EQ y3_EQ). reflexivity.
Qed.

Lemma pair_compare_good
  : hsOrdLaws (SETOID := directProduct_of_two_Setoids A_isProset.(Proset_isSetoid) B_isProset.(Proset_isSetoid)) pair_compare.
Proof.
  split.
  - exact pair_compare_Eq_iff.
  - exact pair_compare_Gt_flip.
  - exact pair_compare_Lt_trans.
  - exact pair_compare_compatWith_eqProp.
Qed.

#[local]
Instance pair_isProset : isProset (A * B) :=
  @mkProsetFrom_compare (A * B) (directProduct_of_two_Setoids A_isProset.(Proset_isSetoid) B_isProset.(Proset_isSetoid)) pair_compare pair_compare_good.

#[local]
Instance pair_hsOrd : hsOrd (A * B) (PROSET := pair_isProset) :=
  @mkHsOrdFrom_compare (A * B) (directProduct_of_two_Setoids A_isProset.(Proset_isSetoid) B_isProset.(Proset_isSetoid)) pair_compare pair_compare_good.

End hsOrd_pair.

Section HsOrd_pair.

Context {A : Type} {B : Type} {A_isPoset : isPoset A} {B_isPoset : isPoset B}.

Context {HsOrd_A : HsOrd A (POSET := A_isPoset)} {HsOrd_B : HsOrd B (POSET := B_isPoset)}.

#[local] Obligation Tactic := idtac.

#[global, program]
Instance pair_isPoset : isPoset (A * B) :=
  { Poset_isProset := @pair_isProset A B A_isPoset.(Poset_isProset) B_isPoset.(Poset_isProset) HsOrd_A.(HsOrd_hsOrd) HsOrd_B.(HsOrd_hsOrd) }.
Next Obligation.
  intros p p'. destruct p as [x1 y1], p' as [x2 y2]. split.
  - intros [x_EQ y_EQ]. simpl in *.
    rewrite Poset_eqProp_spec in x_EQ. rewrite Poset_eqProp_spec in y_EQ. congruence.
  - intros H_eq. inversion H_eq; subst x2 y2. split; reflexivity.
Qed.

#[global]
Instance HsOrd_pair : HsOrd (A * B) (POSET := pair_isPoset) :=
  { HsOrd_hsOrd := @pair_hsOrd A B A_isPoset.(Poset_isProset) B_isPoset.(Poset_isProset) HsOrd_A.(HsOrd_hsOrd) HsOrd_B.(HsOrd_hsOrd) }.

End HsOrd_pair.

#[global] Arguments HsOrd_pair {A} {B} {A_isPoset} {B_isPoset} HsOrd_A HsOrd_B.

Section hsOrd_sum.

Context {A : Type} {B : Type}.

#[global, program]
Instance sum_isSetoid (A_isSetoid : isSetoid A) (B_isSetoid : isSetoid B) : isSetoid (A + B) :=
  { eqProp (z : A + B) (z' : A + B) :=
    match z, z' with
    | inl x, inl x' => x == x'
    | inl _, inr _ => False
    | inr _, inl _ => False
    | inr y, inr y' => y == y'
    end
  }.
Next Obligation.
  split.
  - intros [x | y]; reflexivity.
  - intros [x | y] [x' | y'] EQ; try contradiction; now symmetry.
  - intros [x | y] [x' | y'] [x'' | y''] EQ EQ'; try contradiction; now transitivity x' || now transitivity y'.
Qed.

Context {A_isProset : isProset A} {B_isProset : isProset B} {A_hsOrd : hsOrd A (PROSET := A_isProset)} {B_hsOrd : hsOrd B (PROSET := B_isProset)}.

Definition sum_compare (z : A + B) (z' : A + B) : comparison :=
  match z, z' with
  | inl x, inl x' => compare x x'
  | inl _, inr _ => Lt
  | inr _, inl _ => Gt
  | inr y, inr y' => compare y y'
  end.

Lemma sum_compare_Eq_iff (z : A + B) (z' : A + B)
  : sum_compare z z' = Eq <-> z == z'.
Proof.
  destruct z as [x | y], z' as [x' | y']; simpl.
  - exact (compare_Eq_iff x x').
  - split; [discriminate | contradiction].
  - split; [discriminate | contradiction].
  - exact (compare_Eq_iff y y').
Qed.

Lemma sum_compare_Gt_flip (z : A + B) (z' : A + B)
  (OBS_Gt : sum_compare z z' = Gt)
  : sum_compare z' z = Lt.
Proof.
  destruct z as [x | y], z' as [x' | y']; simpl in *; try congruence.
  - exact (compare_Gt_flip x x' OBS_Gt).
  - exact (compare_Gt_flip y y' OBS_Gt).
Qed.

Lemma sum_compare_Lt_trans (z : A + B) (z' : A + B) (z'' : A + B)
  (OBS_Lt1 : sum_compare z z' = Lt)
  (OBS_Lt2 : sum_compare z' z'' = Lt)
  : sum_compare z z'' = Lt.
Proof.
  destruct z as [x | y], z' as [x' | y'], z'' as [x'' | y'']; simpl in *; try congruence.
  - exact (compare_Lt_trans x x' x'' OBS_Lt1 OBS_Lt2).
  - exact (compare_Lt_trans y y' y'' OBS_Lt1 OBS_Lt2).
Qed.

Lemma sum_compare_compatWith_eqProp (z1 : A + B) (z1' : A + B) (z2 : A + B) (z2' : A + B)
  (z1_EQ : z1 == z1')
  (z2_EQ : z2 == z2')
  : sum_compare z1 z2 = sum_compare z1' z2'.
Proof.
  repeat match goal with [ z : A + B |- _ ] => destruct z end; simpl in *; try contradiction; try reflexivity.
  - now eapply compare_compatWith_eqProp.
  - now eapply compare_compatWith_eqProp.
Qed.

Lemma sum_compare_good
  : hsOrdLaws (SETOID := sum_isSetoid A_isProset.(Proset_isSetoid) B_isProset.(Proset_isSetoid)) sum_compare.
Proof.
  split.
  - exact sum_compare_Eq_iff.
  - exact sum_compare_Gt_flip.
  - exact sum_compare_Lt_trans.
  - exact sum_compare_compatWith_eqProp.
Qed.

#[local]
Instance sum_isProset : isProset (A + B) :=
  @mkProsetFrom_compare (A + B) (sum_isSetoid A_isProset.(Proset_isSetoid) B_isProset.(Proset_isSetoid)) sum_compare sum_compare_good.

#[local]
Instance sum_hsOrd : hsOrd (A + B) (PROSET := sum_isProset) :=
  @mkHsOrdFrom_compare (A + B) (sum_isSetoid A_isProset.(Proset_isSetoid) B_isProset.(Proset_isSetoid)) sum_compare sum_compare_good.

End hsOrd_sum.

Section HsOrd_sum.

Context {A : Type} {B : Type} {A_isPoset : isPoset A} {B_isPoset : isPoset B}.

Context {HsOrd_A : HsOrd A (POSET := A_isPoset)} {HsOrd_B : HsOrd B (POSET := B_isPoset)}.

#[local] Obligation Tactic := idtac.

#[global, program]
Instance sum_isPoset : isPoset (A + B) :=
  { Poset_isProset := @sum_isProset A B A_isPoset.(Poset_isProset) B_isPoset.(Poset_isProset) HsOrd_A.(HsOrd_hsOrd) HsOrd_B.(HsOrd_hsOrd) }.
Next Obligation.
  intros z z'. destruct z as [x | y], z' as [x' | y']; simpl.
  - split.
    + intros x_EQ. f_equal. now rewrite <- Poset_eqProp_spec.
    + intros H_eq. inv H_eq. reflexivity.
  - split; firstorder congruence.
  - split; firstorder congruence.
  - split.
    + intros y_EQ. f_equal. now rewrite <- Poset_eqProp_spec.
    + intros H_eq. inversion H_eq; subst y'. reflexivity.
Qed.

#[global]
Instance HsOrd_sum : HsOrd (A + B) (POSET := sum_isPoset) :=
  { HsOrd_hsOrd := @sum_hsOrd A B A_isPoset.(Poset_isProset) B_isPoset.(Poset_isProset) HsOrd_A.(HsOrd_hsOrd) HsOrd_B.(HsOrd_hsOrd) }.

End HsOrd_sum.

#[global] Arguments HsOrd_sum {A} {B} {A_isPoset} {B_isPoset} HsOrd_A HsOrd_B.

Section hsOrd_of_injection.

Context {A : Type} {B : Type} {B_isProset : isProset B} {B_hsOrd : hsOrd B (PROSET := B_isProset)}.

Variable code : A -> B.

#[local]
Instance inj_isSetoid : isSetoid A :=
  { eqProp := binary_relation_on_image eqProp code
  ; eqProp_Equivalence := relation_on_image_liftsEquivalence B_isProset.(Proset_isSetoid).(eqProp_Equivalence) code
  }.

Definition inj_compare (x : A) (y : A) : comparison :=
  compare (code x) (code y).

Lemma inj_compare_Eq_iff (x : A) (y : A)
  : inj_compare x y = Eq <-> x == y.
Proof.
  exact (compare_Eq_iff (code x) (code y)).
Qed.

Lemma inj_compare_Gt_flip (x : A) (y : A)
  (OBS_Gt : inj_compare x y = Gt)
  : inj_compare y x = Lt.
Proof.
  exact (compare_Gt_flip (code x) (code y) OBS_Gt).
Qed.

Lemma inj_compare_Lt_trans (x : A) (y : A) (z : A)
  (OBS_Lt1 : inj_compare x y = Lt)
  (OBS_Lt2 : inj_compare y z = Lt)
  : inj_compare x z = Lt.
Proof.
  exact (compare_Lt_trans (code x) (code y) (code z) OBS_Lt1 OBS_Lt2).
Qed.

Lemma inj_compare_compatWith_eqProp (x : A) (x' : A) (y : A) (y' : A)
  (x_EQ : x == x')
  (y_EQ : y == y')
  : inj_compare x y = inj_compare x' y'.
Proof.
  exact (compare_compatWith_eqProp (code x) (code x') (code y) (code y') x_EQ y_EQ).
Qed.

Lemma inj_compare_good
  : hsOrdLaws (SETOID := inj_isSetoid) inj_compare.
Proof.
  split.
  - exact inj_compare_Eq_iff.
  - exact inj_compare_Gt_flip.
  - exact inj_compare_Lt_trans.
  - exact inj_compare_compatWith_eqProp.
Qed.

#[local]
Instance inj_isProset : isProset A :=
  @mkProsetFrom_compare A inj_isSetoid inj_compare inj_compare_good.

#[local]
Instance inj_hsOrd : hsOrd A (PROSET := inj_isProset) :=
  @mkHsOrdFrom_compare A inj_isSetoid inj_compare inj_compare_good.

End hsOrd_of_injection.

Section HsOrd_of_injection.

Context {A : Type} {B : Type} {B_isPoset : isPoset B} {HsOrd_B : HsOrd B (POSET := B_isPoset)}.

Variable code : A -> B.

Hypothesis code_inj : forall x : A, forall y : A, code x = code y -> x = y.

#[local] Obligation Tactic := idtac.

#[local, program]
Instance inj_isPoset : isPoset A :=
  { Poset_isProset := @inj_isProset A B B_isPoset.(Poset_isProset) HsOrd_B.(HsOrd_hsOrd) code }.
Next Obligation.
  intros x y. split.
  - intros x_EQ. eapply code_inj. now rewrite <- Poset_eqProp_spec.
  - intros H_eq. subst y. reflexivity.
Qed.

#[local]
Instance inj_HsOrd : HsOrd A (POSET := inj_isPoset) :=
  { HsOrd_hsOrd := @inj_hsOrd A B B_isPoset.(Poset_isProset) HsOrd_B.(HsOrd_hsOrd) code }.

Definition mkPoset_inj : isPoset A :=
  inj_isPoset.

Definition mkHsOrd_inj : HsOrd A (POSET := mkPoset_inj) :=
  inj_HsOrd.

End HsOrd_of_injection.

#[global] Arguments mkPoset_inj {A} {B} {B_isPoset} HsOrd_B code code_inj.
#[global] Arguments mkHsOrd_inj {A} {B} {B_isPoset} HsOrd_B code code_inj.
