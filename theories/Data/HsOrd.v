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
Class HsOrd (A : Type) `{POSET : isPoset A} : Type :=
  { HsOrd_hsOrd : hsOrd A (PROSET := POSET.(Poset_isProset)) }.

#[global] Existing Instance HsOrd_hsOrd.

#[global, program]
Instance list_isPoset {A : Type} {POSET : isPoset A} (HS_ORD : HsOrd A) : isPoset (list A) :=
  { Poset_isProset := @list_lexicographical_order A POSET.(Poset_isProset) HS_ORD.(HsOrd_hsOrd) }.
Next Obligation.
  split.
  - intros H_eq. red in H_eq. rename x into xs, y into ys. revert xs ys H_eq.
    induction xs as [ | x xs IH], ys as [ | y ys]; simpl in *; ii; [congruence .. | ].
    destruct (compare x y) as [ | | ] eqn: H_OBS; [f_equal | congruence ..].
    + rewrite <- Poset_eqProp_spec. now eapply compare_Eq.
    + now eapply IH.
  - intros H_eq. subst y. reflexivity.
Qed.

#[global, program]
Instance nat_isPoset : isPoset nat :=
  { Poset_isProset := nat_isProset }.

#[global]
Instance HsOrd_list {A : Type} `{POSET : isPoset A} (HsOrd_A : HsOrd A (POSET := POSET)) : HsOrd (list A) (POSET := list_isPoset HsOrd_A) :=
  { HsOrd_hsOrd := list_hsOrd }.

#[global]
Instance HsOrd_nat : HsOrd nat (POSET := nat_isPoset) :=
  { HsOrd_hsOrd := nat_hsOrd }.

#[universes(polymorphic=yes)]
Definition isSorted@{u} {A : Type@{u}} (compare : A -> A -> comparison) : list A -> bool :=
  fix go (xs : list A) {struct xs} : bool :=
  match xs with
  | [] => true
  | x :: xs => forallb (fun x' : A => Prelude.eqb (compare x x') Lt) xs && go xs
  end.

Section FACTS.

Context {A : Type} {POSET : isPoset A} {HS_ORD : HsOrd A (POSET := POSET)}.

Lemma compare_refl (x : A)
  : compare x x = Eq.
Proof.
  destruct (compare x x) as [ | | ] eqn: H_OBS; auto.
  - pose proof (compare_Lt x x H_OBS) as [_ x_ne_x]. now contradiction x_ne_x.
  - pose proof (compare_Gt x x H_OBS) as [_ x_ne_x]. now contradiction x_ne_x.
Qed.

Lemma compare_eq_iff (x : A) (y : A)
  : compare x y = Eq <-> x = y.
Proof.
  split.
  - intros OBS_Eq. rewrite <- Poset_eqProp_spec. exact (compare_Eq x y OBS_Eq).
  - intros x_eq_y. subst y. exact (compare_refl x).
Qed.

Lemma compare_Gt_flip (x : A) (y : A)
  (OBS_Gt : compare x y = Gt)
  : compare y x = Lt.
Proof.
  pose proof (compare_Gt x y OBS_Gt) as [y_le_x x_ne_y].
  destruct (compare y x) as [ | | ] eqn: H_OBS; auto.
  - contradiction x_ne_y. symmetry. exact (compare_Eq y x H_OBS).
  - pose proof (compare_Gt y x H_OBS) as [x_le_y _].
    contradiction x_ne_y. now eapply leProp_antisymmetry.
Qed.

Lemma compare_Lt_trans (x : A) (y : A) (z : A)
  (OBS_Lt1 : compare x y = Lt)
  (OBS_Lt2 : compare y z = Lt)
  : compare x z = Lt.
Proof.
  pose proof (compare_Lt x y OBS_Lt1) as [x_le_y x_ne_y].
  pose proof (compare_Lt y z OBS_Lt2) as [y_le_z y_ne_z].
  assert (x_le_z : x =< z) by now transitivity y.
  destruct (compare x z) as [ | | ] eqn: H_OBS; auto.
  - pose proof (compare_Eq x z H_OBS) as x_eq_z.
    contradiction x_ne_y. eapply leProp_antisymmetry; auto.
    transitivity z; auto with *. now rewrite <- x_eq_z.
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

End FACTS.

Section HsOrd_pair.

Context {A : Type} {B : Type} {A_isPoset : isPoset A} {B_isPoset : isPoset B} {HsOrd_A : HsOrd A} {HsOrd_B : HsOrd B}.

Definition pair_compare (p : A * B) (q : A * B) : comparison :=
  match compare (fst p) (fst q) with
  | Lt => Lt
  | Eq => compare (snd p) (snd q)
  | Gt => Gt
  end.

Lemma pair_compare_eq_iff (p : A * B) (q : A * B)
  : pair_compare p q = Eq <-> p = q.
Proof.
  destruct p as [x1 y1], q as [x2 y2]. unfold pair_compare. simpl. split.
  - intros OBS_Eq. destruct (compare x1 x2) as [ | | ] eqn: H_OBS; try discriminate OBS_Eq.
    rewrite compare_eq_iff in H_OBS. rewrite compare_eq_iff in OBS_Eq. congruence.
  - intros H_eq. inversion H_eq; subst x2 y2.
    rewrite compare_refl. exact (compare_refl y1).
Qed.

Lemma pair_compare_Gt_flip (p : A * B) (q : A * B)
  (OBS_Gt : pair_compare p q = Gt)
  : pair_compare q p = Lt.
Proof.
  destruct p as [x1 y1], q as [x2 y2]. unfold pair_compare in *. simpl in *.
  destruct (compare x1 x2) as [ | | ] eqn: H_OBS; try congruence.
  - rewrite compare_eq_iff in H_OBS. subst x2.
    rewrite compare_refl. exact (compare_Gt_flip y1 y2 OBS_Gt).
  - rewrite (compare_Gt_flip x1 x2 H_OBS). reflexivity.
Qed.

Lemma pair_compare_Lt_trans (p : A * B) (q : A * B) (r : A * B)
  (OBS_Lt1 : pair_compare p q = Lt)
  (OBS_Lt2 : pair_compare q r = Lt)
  : pair_compare p r = Lt.
Proof.
  destruct p as [x1 y1], q as [x2 y2], r as [x3 y3]. unfold pair_compare in *. simpl in *.
  destruct (compare x1 x2) as [ | | ] eqn: H_OBS1; destruct (compare x2 x3) as [ | | ] eqn: H_OBS2; try congruence.
  - rewrite compare_eq_iff in H_OBS1, H_OBS2. subst x2 x3. rewrite compare_refl.
    exact (compare_Lt_trans y1 y2 y3 OBS_Lt1 OBS_Lt2).
  - rewrite compare_eq_iff in H_OBS1. subst x2. rewrite H_OBS2. reflexivity.
  - rewrite compare_eq_iff in H_OBS2. subst x3. rewrite H_OBS1. reflexivity.
  - enough (WTS : compare x1 x3 = Lt) by now rewrite WTS.
    exact (compare_Lt_trans x1 x2 x3 H_OBS1 H_OBS2).
Qed.

Lemma pair_compare_Lt_StrictOrder
  : StrictOrder (fun p : A * B => fun p' : A * B => pair_compare p p' = Lt).
Proof.
  split.
  - intros p OBS_Lt. pose proof (proj2 (pair_compare_eq_iff p p) eq_refl) as OBS_Eq. congruence.
  - intros p p' p''. exact (pair_compare_Lt_trans p p' p'').
Qed.

#[global]
Instance pair_isPoset : isPoset (A * B) :=
  mkProsetFrom_ltProp_isPoset pair_compare_Lt_StrictOrder.

#[local] Obligation Tactic := idtac.

#[local, program]
Instance pair_hsOrd : hsOrd (A * B) (PROSET := Poset_isProset) :=
  { compare := pair_compare }.
Next Obligation.
  intros p p' OBS_Lt. split.
  - left. exact OBS_Lt.
  - intros p_eq_p'. change (p = p') in p_eq_p'. subst p'.
    enough (pair_compare p p = Eq) by congruence.
    exact (proj2 (pair_compare_eq_iff p p) eq_refl).
Qed.
Next Obligation.
  intros p p' OBS_Eq. exact (proj1 (pair_compare_eq_iff p p') OBS_Eq).
Qed.
Next Obligation.
  intros p p' OBS_Gt. split.
  - left. exact (pair_compare_Gt_flip p p' OBS_Gt).
  - intros p_eq_p'. change (p = p') in p_eq_p'. subst p'.
    enough (pair_compare p p = Eq) by congruence.
    exact (proj2 (pair_compare_eq_iff p p) eq_refl).
Qed.

#[global]
Instance HsOrd_pair : HsOrd (A * B) (POSET := pair_isPoset) :=
  { HsOrd_hsOrd := pair_hsOrd }.

End HsOrd_pair.

#[global] Arguments HsOrd_pair {A} {B} {_} {_} _ _.
