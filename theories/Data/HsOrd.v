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

#[global, program]
Instance list_isPoset {A : Type} {POSET : isPoset A} (HS_ORD : HsOrd A) : isPoset (list A) :=
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

Definition pair_compare (p : A * B) (p' : A * B) : comparison :=
  match compare (fst p) (fst p') with
  | Lt => Lt
  | Eq => compare (snd p) (snd p')
  | Gt => Gt
  end.

Lemma pair_compare_eq_iff (p : A * B) (p' : A * B)
  : pair_compare p p' = Eq <-> p = p'.
Proof.
  destruct p as [x1 y1], p' as [x2 y2]. unfold pair_compare. simpl. split.
  - intros OBS_Eq. destruct (compare x1 x2) as [ | | ] eqn: H_OBS; try discriminate OBS_Eq.
    rewrite compare_eq_iff in H_OBS. rewrite compare_eq_iff in OBS_Eq. congruence.
  - intros H_eq. inversion H_eq; subst x2 y2.
    rewrite compare_refl. exact (compare_refl y1).
Qed.

Lemma pair_compare_Gt_flip (p : A * B) (p' : A * B)
  (OBS_Gt : pair_compare p p' = Gt)
  : pair_compare p' p = Lt.
Proof.
  destruct p as [x1 y1], p' as [x2 y2]. unfold pair_compare in *. simpl in *.
  destruct (compare x1 x2) as [ | | ] eqn: H_OBS; try congruence.
  - rewrite compare_eq_iff in H_OBS. subst x2.
    rewrite compare_refl. exact (compare_Gt_flip y1 y2 OBS_Gt).
  - rewrite (compare_Gt_flip x1 x2 H_OBS). reflexivity.
Qed.

Lemma pair_compare_Lt_trans (p : A * B) (p' : A * B) (p'' : A * B)
  (OBS_Lt1 : pair_compare p p' = Lt)
  (OBS_Lt2 : pair_compare p' p'' = Lt)
  : pair_compare p p'' = Lt.
Proof.
  destruct p as [x1 y1], p' as [x2 y2], p'' as [x3 y3]. unfold pair_compare in *. simpl in *.
  destruct (compare x1 x2) as [ | | ] eqn: H_OBS1; destruct (compare x2 x3) as [ | | ] eqn: H_OBS2; try congruence.
  - rewrite compare_eq_iff in H_OBS1, H_OBS2. subst x2 x3. rewrite compare_refl.
    exact (compare_Lt_trans y1 y2 y3 OBS_Lt1 OBS_Lt2).
  - rewrite compare_eq_iff in H_OBS1. subst x2. rewrite H_OBS2. reflexivity.
  - rewrite compare_eq_iff in H_OBS2. subst x3. rewrite H_OBS1. reflexivity.
  - enough (WTS : compare x1 x3 = Lt) by now rewrite WTS.
    exact (compare_Lt_trans x1 x2 x3 H_OBS1 H_OBS2).
Qed.

#[global]
Instance pair_compare_Lt_StrictOrder
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

Section HsOrd_unit.

Definition unit_compare (x : unit) (y : unit) : comparison :=
  Eq.

Lemma unit_compare_eq_iff (x : unit) (y : unit)
  : unit_compare x y = Eq <-> x = y.
Proof.
  destruct x, y. split; intros _; reflexivity.
Qed.

#[global]
Instance unit_compare_Lt_StrictOrder
  : StrictOrder (fun x : unit => fun y : unit => unit_compare x y = Lt).
Proof.
  split.
  - intros x OBS_Lt. discriminate OBS_Lt.
  - intros x y z OBS_Lt. discriminate OBS_Lt.
Qed.

#[global]
Instance unit_isPoset : isPoset unit :=
  mkProsetFrom_ltProp_isPoset unit_compare_Lt_StrictOrder.

#[local] Obligation Tactic := idtac.

#[local, program]
Instance unit_hsOrd : hsOrd unit (PROSET := Poset_isProset) :=
  { compare := unit_compare }.
Next Obligation.
  intros x y OBS_Lt. discriminate OBS_Lt.
Qed.
Next Obligation.
  intros x y OBS_Eq. exact (proj1 (unit_compare_eq_iff x y) OBS_Eq).
Qed.
Next Obligation.
  intros x y OBS_Gt. discriminate OBS_Gt.
Qed.

#[global]
Instance HsOrd_unit : HsOrd unit (POSET := unit_isPoset) :=
  { HsOrd_hsOrd := unit_hsOrd }.

End HsOrd_unit.

Section HsOrd_sum.

Context {A : Type} {B : Type} {A_isPoset : isPoset A} {B_isPoset : isPoset B} {HsOrd_A : HsOrd A} {HsOrd_B : HsOrd B}.

Definition sum_compare (s : A + B) (s' : A + B) : comparison :=
  match s, s' with
  | inl x, inl x' => compare x x'
  | inl _, inr _ => Lt
  | inr _, inl _ => Gt
  | inr y, inr y' => compare y y'
  end.

Lemma sum_compare_eq_iff (s : A + B) (s' : A + B)
  : sum_compare s s' = Eq <-> s = s'.
Proof.
  destruct s as [x | y], s' as [x' | y']; simpl; split; try congruence.
  - intros OBS_Eq. f_equal. exact (proj1 (compare_eq_iff x x') OBS_Eq).
  - intros H_eq. inversion H_eq; subst x'. exact (compare_refl x).
  - intros OBS_Eq. f_equal. exact (proj1 (compare_eq_iff y y') OBS_Eq).
  - intros H_eq. inversion H_eq; subst y'. exact (compare_refl y).
Qed.

Lemma sum_compare_Gt_flip (s : A + B) (s' : A + B)
  (OBS_Gt : sum_compare s s' = Gt)
  : sum_compare s' s = Lt.
Proof.
  destruct s as [x | y], s' as [x' | y']; simpl in *; try congruence.
  - exact (compare_Gt_flip x x' OBS_Gt).
  - exact (compare_Gt_flip y y' OBS_Gt).
Qed.

Lemma sum_compare_Lt_trans (s : A + B) (s' : A + B) (s'' : A + B)
  (OBS_Lt1 : sum_compare s s' = Lt)
  (OBS_Lt2 : sum_compare s' s'' = Lt)
  : sum_compare s s'' = Lt.
Proof.
  destruct s as [x | y], s' as [x' | y'], s'' as [x'' | y'']; simpl in *; try congruence.
  - exact (compare_Lt_trans x x' x'' OBS_Lt1 OBS_Lt2).
  - exact (compare_Lt_trans y y' y'' OBS_Lt1 OBS_Lt2).
Qed.

#[global]
Instance sum_compare_Lt_StrictOrder
  : StrictOrder (fun s : A + B => fun s' : A + B => sum_compare s s' = Lt).
Proof.
  split.
  - intros s OBS_Lt. pose proof (proj2 (sum_compare_eq_iff s s) eq_refl) as OBS_Eq. congruence.
  - intros s s' s''. exact (sum_compare_Lt_trans s s' s'').
Qed.

#[global]
Instance sum_isPoset : isPoset (A + B) :=
  mkProsetFrom_ltProp_isPoset sum_compare_Lt_StrictOrder.

#[local] Obligation Tactic := idtac.

#[local, program]
Instance sum_hsOrd : hsOrd (A + B) (PROSET := Poset_isProset) :=
  { compare := sum_compare }.
Next Obligation.
  intros s s' OBS_Lt. split.
  - left. exact OBS_Lt.
  - intros s_eq_s'. change (s = s') in s_eq_s'. subst s'.
    enough (sum_compare s s = Eq) by congruence.
    exact (proj2 (sum_compare_eq_iff s s) eq_refl).
Qed.
Next Obligation.
  intros s s' OBS_Eq. exact (proj1 (sum_compare_eq_iff s s') OBS_Eq).
Qed.
Next Obligation.
  intros s s' OBS_Gt. split.
  - left. exact (sum_compare_Gt_flip s s' OBS_Gt).
  - intros s_eq_s'. change (s = s') in s_eq_s'. subst s'.
    enough (sum_compare s s = Eq) by congruence.
    exact (proj2 (sum_compare_eq_iff s s) eq_refl).
Qed.

#[global]
Instance HsOrd_sum : HsOrd (A + B) (POSET := sum_isPoset) :=
  { HsOrd_hsOrd := sum_hsOrd }.

End HsOrd_sum.

#[global] Arguments HsOrd_sum {A} {B} {_} {_} _ _.

Section HsOrd_of_injection.

Context {A : Type} {B : Type} {B_isPoset : isPoset B} {HsOrd_B : HsOrd B}.

Variable code : A -> B.

Hypothesis code_inj : forall x : A, forall y : A, code x = code y -> x = y.

Definition inj_compare (x : A) (y : A) : comparison :=
  compare (code x) (code y).

Lemma inj_compare_eq_iff (x : A) (y : A)
  : inj_compare x y = Eq <-> x = y.
Proof.
  unfold inj_compare. rewrite compare_eq_iff. split.
  - exact (code_inj x y).
  - intros H_eq. now subst y.
Qed.

Lemma inj_compare_Gt_flip (x : A) (y : A)
  (OBS_Gt : inj_compare x y = Gt)
  : inj_compare y x = Lt.
Proof.
  unfold inj_compare in *. exact (compare_Gt_flip (code x) (code y) OBS_Gt).
Qed.

Lemma inj_compare_Lt_trans (x : A) (y : A) (z : A)
  (OBS_Lt1 : inj_compare x y = Lt)
  (OBS_Lt2 : inj_compare y z = Lt)
  : inj_compare x z = Lt.
Proof.
  unfold inj_compare in *.
  exact (compare_Lt_trans (code x) (code y) (code z) OBS_Lt1 OBS_Lt2).
Qed.

#[local]
Instance inj_compare_Lt_StrictOrder
  : StrictOrder (fun x : A => fun y : A => inj_compare x y = Lt).
Proof.
  split.
  - intros x OBS_Lt. pose proof (proj2 (inj_compare_eq_iff x x) eq_refl) as OBS_Eq. congruence.
  - intros x y z. exact (inj_compare_Lt_trans x y z).
Qed.

#[local]
Instance inj_isPoset : isPoset A :=
  mkProsetFrom_ltProp_isPoset inj_compare_Lt_StrictOrder.

#[local] Obligation Tactic := idtac.

#[local, program]
Instance inj_hsOrd : hsOrd A (PROSET := Poset_isProset) :=
  { compare := inj_compare }.
Next Obligation.
  intros x y OBS_Lt. split.
  - left. exact OBS_Lt.
  - intros x_eq_y. change (x = y) in x_eq_y. subst y.
    enough (inj_compare x x = Eq) by congruence.
    exact (proj2 (inj_compare_eq_iff x x) eq_refl).
Qed.
Next Obligation.
  intros x y OBS_Eq. exact (proj1 (inj_compare_eq_iff x y) OBS_Eq).
Qed.
Next Obligation.
  intros x y OBS_Gt. split.
  - left. exact (inj_compare_Gt_flip x y OBS_Gt).
  - intros x_eq_y. change (x = y) in x_eq_y. subst y.
    enough (inj_compare x x = Eq) by congruence.
    exact (proj2 (inj_compare_eq_iff x x) eq_refl).
Qed.

#[local]
Instance inj_HsOrd_local : HsOrd A (POSET := inj_isPoset) :=
  { HsOrd_hsOrd := inj_hsOrd }.

Definition mkPoset_inj : isPoset A :=
  inj_isPoset.

Definition mkHsOrd_inj : HsOrd A (POSET := mkPoset_inj) :=
  inj_HsOrd_local.

End HsOrd_of_injection.

#[global] Arguments mkPoset_inj {A} {B} {_} {_} code code_inj.
#[global] Arguments mkHsOrd_inj {A} {B} {_} {_} code code_inj.

Section HsOrd_N.

#[global]
Instance N_compare_Lt_StrictOrder
  : StrictOrder (fun x : N => fun y : N => N.compare x y = Lt).
Proof.
  split.
  - intros x LT. rewrite N.compare_lt_iff in LT. lia.
  - intros x y z LT1 LT2. rewrite N.compare_lt_iff in LT1, LT2 |- *. lia.
Qed.

#[global]
Instance N_isPoset : isPoset N :=
  mkProsetFrom_ltProp_isPoset N_compare_Lt_StrictOrder.

#[local] Obligation Tactic := idtac.

#[local, program]
Instance N_hsOrd : hsOrd N (PROSET := Poset_isProset) :=
  { compare := N.compare }.
Next Obligation.
  intros x y OBS_Lt. split.
  - left. exact OBS_Lt.
  - intros x_eq_y. change (x = y) in x_eq_y. subst y.
    rewrite N.compare_refl in OBS_Lt. discriminate OBS_Lt.
Qed.
Next Obligation.
  intros x y OBS_Eq. exact (proj1 (N.compare_eq_iff x y) OBS_Eq).
Qed.
Next Obligation.
  intros x y OBS_Gt. split.
  - left. rewrite N.compare_gt_iff in OBS_Gt.
    rewrite N.compare_lt_iff. lia.
  - intros x_eq_y. change (x = y) in x_eq_y. subst y.
    rewrite N.compare_refl in OBS_Gt. discriminate OBS_Gt.
Qed.

#[global]
Instance HsOrd_N : HsOrd N (POSET := N_isPoset) :=
  { HsOrd_hsOrd := N_hsOrd }.

End HsOrd_N.

Lemma compare_N_Lt_iff (x : N) (y : N)
  : compare x y = Lt <-> (x < y)%N.
Proof.
  exact (N.compare_lt_iff x y).
Qed.

Section SORTED_APP.

Context {A : Type} {A_isPoset : isPoset A}
  {HsOrd_A : HsOrd A (POSET := A_isPoset)}.

Lemma isSorted_app (l1 : list A) (l2 : list A)
  (H1 : isSorted compare l1 = true)
  (H2 : isSorted compare l2 = true)
  (CROSS : forall x : A, forall y : A,
    L.In x l1 -> L.In y l2 -> compare x y = Lt)
  : isSorted compare (l1 ++ l2) = true.
Proof.
  revert H1 CROSS. induction l1 as [ | x l1 IH]; intros H1 CROSS;
    [exact H2 | ].
  pose proof (proj1 (isSorted_cons_iff x l1) H1) as
    [x_lt_l1 l1_sorted].
  cbn [L.app].
  eapply (proj2 (isSorted_cons_iff x (l1 ++ l2))). split.
  - intros z z_in. rewrite L.in_app_iff in z_in.
    destruct z_in as [z_in | z_in].
    + exact (x_lt_l1 z z_in).
    + eapply CROSS; [now left | exact z_in].
  - eapply IH; [exact l1_sorted | ]. intros u v u_in v_in.
    eapply CROSS; [now right | exact v_in].
Qed.

End SORTED_APP.
