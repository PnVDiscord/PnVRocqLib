Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Prelude.X.
Require Export PnV.Math.ThN.
Require Export PnV.Math.OrderTheory.
Require Export PnV.Data.HsOrd.

#[local] Infix "=~=" := is_similar_to : type_scope.
#[local] Infix "\in" := E.In.
#[local] Infix "∈" := L.In.

#[local] Hint Resolve S_lt_S_intro : core.

Module FSet.

#[universes(template), projections(primitive)]
Record t {A : Type} {isSorted : list A -> bool} : Type :=
  mk
  { data : list A
  ; data_isSorted : isSorted data = true
  }.

#[global] Arguments t : clear implicits.
#[global] Arguments mk {A} {isSorted}.

Lemma t_eq_iff {A : Type} {isSorted : list A -> bool} (X : FSet.t A isSorted) (X' : FSet.t A isSorted)
  : X = X' <-> X.(data) = X'.(data).
Proof.
  split.
  - intros H_eq. subst X'. reflexivity.
  - revert X X'.
    assert (claim : forall data1 : list A, forall data2 : list A, forall data1_isSorted : isSorted data1 = true, forall data2_isSorted : isSorted data2 = true, data1 = data2 -> {| data := data1; data_isSorted := data1_isSorted |} = {| data := data2; data_isSorted := data2_isSorted |}).
    { ii. subst data2. enough (HH : data1_isSorted = data2_isSorted) by now rewrite HH. eapply eq_pirrel_fromEqDec. }
    intros X X' H_eq. exact (claim X.(data) X'.(data) X.(data_isSorted) X'.(data_isSorted) H_eq).
Qed.

End FSet.

Abbreviation fset A := (FSet.t A (isSorted compare)).

Theorem fset_eq_spec (A : Type) (POSET : isPoset A) (HS_ORD : HsOrd A (POSET := POSET)) (X : fset A) (X' : fset A)
  : X = X' <-> (forall z : A, L.In z X.(FSet.data) <-> L.In z X'.(FSet.data)).
Proof.
  rewrite FSet.t_eq_iff. split.
  - ii. rewrite H. reflexivity.
  - intros EXT.
    assert (LT_asym : forall x1 : A, forall x2 : A, compare x1 x2 = Lt -> compare x2 x1 = Lt -> False).
    { intros x1 x2 LT1 LT2.
      pose proof (compare_Lt x1 x2 LT1) as [x1_le_x2 x1_ne_x2].
      pose proof (compare_Lt x2 x1 LT2) as [x2_le_x1 _].
      contradiction x1_ne_x2. eapply leProp_antisymmetry; assumption.
    }
    assert (LT_neq : forall x1 : A, forall x2 : A, compare x1 x2 = Lt -> x1 <> x2).
    { intros x1 x2 LT x1_eq_x2. subst x2.
      pose proof (compare_Lt x1 x1 LT) as [_ x1_ne_x1].
      contradiction x1_ne_x1. reflexivity.
    }
    assert (HD_TL : forall x : A, forall zs : list A, isSorted compare (x :: zs) = true -> ((forall z : A, z ∈ zs -> compare x z = Lt) /\ isSorted compare zs = true)).
    { intros x zs SORTED. simpl in SORTED. rewrite andb_true_iff in SORTED.
      destruct SORTED as [SORTED_hd SORTED_tl]. rewrite forallb_forall in SORTED_hd.
      split; trivial. intros z z_in. rewrite <- eqb_eq. exact (SORTED_hd z z_in).
    }
    pose proof (X.(FSet.data_isSorted)) as xs_isSorted.
    pose proof (X'.(FSet.data_isSorted)) as ys_isSorted.
    set (xs := X.(FSet.data)) in *. set (ys := X'.(FSet.data)) in *.
    clearbody xs ys. clear X X'. revert xs_isSorted ys ys_isSorted EXT.
    induction xs as [ | x xs IH]; intros xs_isSorted [ | y ys] ys_isSorted EXT.
    + reflexivity.
    + exfalso. exact (proj2 (EXT y) (or_introl eq_refl)).
    + exfalso. exact (proj1 (EXT x) (or_introl eq_refl)).
    + pose proof (HD_TL x xs xs_isSorted) as [x_lt_xs xs_isSorted'].
      pose proof (HD_TL y ys ys_isSorted) as [y_lt_ys ys_isSorted'].
      assert (x_eq_y : x = y).
      { pose proof (proj1 (EXT x) (or_introl eq_refl)) as [y_eq_x | x_in_ys].
        - symmetry. exact y_eq_x.
        - pose proof (proj2 (EXT y) (or_introl eq_refl)) as [x_eq_y | y_in_xs].
          + exact x_eq_y.
          + exfalso. exact (LT_asym x y (x_lt_xs y y_in_xs) (y_lt_ys x x_in_ys)).
      }
      subst y. f_equal. eapply IH; trivial. intros z. split.
      * intros z_in_xs. pose proof (proj1 (EXT z) (or_intror z_in_xs)) as [x_eq_z | z_in_ys].
        { exfalso. exact (LT_neq x z (x_lt_xs z z_in_xs) x_eq_z). }
        { exact z_in_ys. }
      * intros z_in_ys. pose proof (proj2 (EXT z) (or_intror z_in_ys)) as [x_eq_z | z_in_xs].
        { exfalso. exact (LT_neq x z (y_lt_ys z z_in_ys) x_eq_z). }
        { exact z_in_xs. }
Qed.

Section HsOrd_fset.

#[local] Obligation Tactic := idtac.

Context {A : Type} {POSET : isPoset A} {HS_ORD : HsOrd A (POSET := POSET)}.

#[local, program]
Instance fset_isProset : isProset (fset A) :=
  { leProp (X : fset A) (X' : fset A) := X.(FSet.data) =< X'.(FSet.data)
  ; Proset_isSetoid := mkSetoid_from_eq
  }.
Next Obligation.
  split.
  - intros X. reflexivity.
  - intros X X' X'' X_le_X' X'_le_X''. transitivity X'.(FSet.data); assumption.
Qed.
Next Obligation.
  intros X X'. unfold flip. split.
  - intros X_eq_X'. change (X = X') in X_eq_X'. subst X'. split; reflexivity.
  - intros [X_le_X' X'_le_X]. change (X = X'). rewrite FSet.t_eq_iff. rewrite <- Poset_eqProp_spec.
    exact (leProp_antisymmetry X.(FSet.data) X'.(FSet.data) X_le_X' X'_le_X).
Qed.

#[global]
Instance fset_isPoset : isPoset (fset A) :=
  { Poset_isProset := fset_isProset
  ; Poset_eqProp_spec (X : fset A) (X' : fset A) := conj (fun H : X = X' => H) (fun H : X = X' => H)
  }.

#[local, program]
Instance fset_hsOrd : hsOrd (fset A) (PROSET := Poset_isProset) :=
  { compare (X : fset A) (X' : fset A) := compare X.(FSet.data) X'.(FSet.data) }.
Next Obligation.
  intros X X' OBS_Lt. pose proof (compare_Lt X.(FSet.data) X'.(FSet.data) OBS_Lt) as [LE NE]. split.
  - exact LE.
  - intros X_eq_X'. contradiction NE. do 6 red in X_eq_X' |- *. subst X'. reflexivity.
Qed.
Next Obligation.
  intros X X' OBS_Eq. pose proof (compare_Eq X.(FSet.data) X'.(FSet.data) OBS_Eq) as H_eq.
  rewrite Poset_eqProp_spec in H_eq. exact (proj2 (FSet.t_eq_iff X X') H_eq).
Qed.
Next Obligation.
  intros X X' OBS_Gt. pose proof (compare_Gt X.(FSet.data) X'.(FSet.data) OBS_Gt) as [LE NE]. split.
  - exact LE.
  - intros X_eq_X'. contradiction NE. do 6 red in X_eq_X' |- *. subst X'. reflexivity.
Qed.

#[global]
Instance HsOrd_fset : HsOrd (fset A) (POSET := fset_isPoset) :=
  { HsOrd_hsOrd := fset_hsOrd }.

End HsOrd_fset.

Module FS.

Section SIMILARITY.

Definition Similarity_fset_ensemble {A : Type} {A' : Type} {POSET : isPoset A} {HS_ORD : HsOrd A (POSET := POSET)} (Sim_A_A' : Similarity A A') : Similarity (fset A) (ensemble A') :=
  fun X : fset A => fun X' : ensemble A' => forall x : A, forall x' : A', x =~= x' -> (x ∈ X.(FSet.data) <-> x' \in X').

Context {A : Type} {POSET : isPoset A} {HS_ORD : HsOrd A (POSET := POSET)}.

#[global]
Instance fset_corresponds_to_ensemble : Similarity (fset A) (ensemble A) :=
  Similarity_fset_ensemble eq.

Theorem fset_corresponds_to_ensemble_iff (X : fset A) (X' : ensemble A)
  : X =~= X' <-> (forall z : A, z ∈ X.(FSet.data) <-> z \in X').
Proof.
  done.
Qed.

End SIMILARITY.

Section BASICS.

Context {A : Type} {POSET : isPoset A} {HS_ORD : HsOrd A (POSET := POSET)}.

Definition insert (x : A) : list A -> list A :=
  fix go (xs : list A) {struct xs} : list A :=
  match xs with
  | [] => [x]
  | y :: ys =>
    match compare x y with
    | Lt => x :: y :: ys
    | Eq => y :: ys
    | Gt => y :: go ys
    end
  end.

Lemma in_insert_iff (x : A) (xs : list A)
  : forall z : A, z ∈ insert x xs <-> (x = z \/ z ∈ xs).
Proof.
  induction xs as [ | y ys IH]; intros z; simpl.
  - tauto.
  - destruct (compare x y) as [ | | ] eqn: H_OBS.
    + rewrite compare_eq_iff in H_OBS. subst y. simpl. tauto.
    + simpl. tauto.
    + simpl. rewrite IH. tauto.
Qed.

Lemma isSorted_insert (x : A) (xs : list A)
  (xs_isSorted : isSorted compare xs = true)
  : isSorted compare (insert x xs) = true.
Proof.
  revert xs_isSorted. induction xs as [ | y ys IH]; intros xs_isSorted; simpl; trivial.
  rewrite isSorted_cons_iff in xs_isSorted. destruct xs_isSorted as [y_lt_ys ys_isSorted].
  destruct (compare x y) as [ | | ] eqn: H_OBS.
  - rewrite isSorted_cons_iff. split; assumption.
  - rewrite isSorted_cons_iff. split.
    + intros z [y_eq_z | z_in_ys]; [congruence | ].
      exact (compare_Lt_trans x y z H_OBS (y_lt_ys z z_in_ys)).
    + rewrite isSorted_cons_iff. split; assumption.
  - rewrite isSorted_cons_iff. split.
    + intros z z_in. rewrite in_insert_iff in z_in. destruct z_in as [x_eq_z | z_in_ys].
      * subst z. exact (compare_Gt_flip x y H_OBS).
      * exact (y_lt_ys z z_in_ys).
    + exact (IH ys_isSorted).
Qed.

Lemma length_insert (x : A) (xs : list A)
  (NOT_IN : ~ x ∈ xs)
  : length (insert x xs) = S (length xs).
Proof.
  revert NOT_IN. induction xs as [ | y ys IH]; intros NOT_IN; simpl; trivial.
  destruct (compare x y) as [ | | ] eqn: H_OBS; simpl.
  - rewrite compare_eq_iff in H_OBS. subst y. contradiction NOT_IN. now left.
  - reflexivity.
  - f_equal. eapply IH. intros z_in. contradiction NOT_IN. now right.
Qed.

Lemma isSorted_fold_right_insert (xs : list A) (ys : list A)
  (ys_isSorted : isSorted compare ys = true)
  : isSorted compare (L.fold_right insert ys xs) = true.
Proof.
  induction xs as [ | x xs IH]; simpl; trivial.
  exact (isSorted_insert x (L.fold_right insert ys xs) IH).
Qed.

Lemma in_fold_right_insert_iff (xs : list A) (ys : list A)
  : forall z : A, z ∈ L.fold_right insert ys xs <-> (z ∈ xs \/ z ∈ ys).
Proof.
  induction xs as [ | x xs IH]; intros z; simpl.
  - tauto.
  - rewrite in_insert_iff, IH. tauto.
Qed.

Definition empty : fset A :=
  FSet.mk [] eq_refl.

Definition add (x : A) (X : fset A) : fset A :=
  FSet.mk (insert x X.(FSet.data)) (isSorted_insert x X.(FSet.data) X.(FSet.data_isSorted)).

Definition fromList (xs : list A) : fset A :=
  FSet.mk (L.fold_right insert [] xs) (isSorted_fold_right_insert xs [] eq_refl).

Definition union (X : fset A) (X' : fset A) : fset A :=
  FSet.mk (L.fold_right insert X'.(FSet.data) X.(FSet.data)) (isSorted_fold_right_insert X.(FSet.data) X'.(FSet.data) X'.(FSet.data_isSorted)).

Definition unions (Xs : fset (fset A)) : fset A :=
  L.fold_right union empty Xs.(FSet.data).

Fixpoint mem' (x : A) (xs : list A) {struct xs} : bool :=
  match xs with
  | [] => false
  | y :: ys =>
    match compare x y with
    | Eq => true
    | _ => mem' x ys
    end
  end.

Fixpoint memSorted' (x : A) (xs : list A) {struct xs} : bool :=
  match xs with
  | [] => false
  | y :: ys =>
    match compare x y with
    | Lt => false
    | Eq => true
    | Gt => memSorted' x ys
    end
  end.

Lemma mem'_all_lt_false (x : A) (xs : list A)
  (ALL_LT : forall y : A, y ∈ xs -> compare x y = Lt)
  : mem' x xs = false.
Proof.
  induction xs as [ | y ys IH]; trivial.
  cbn [mem']. rewrite (ALL_LT y (or_introl eq_refl)).
  eapply IH. intros z z_in. eapply ALL_LT. now right.
Qed.

Lemma memSorted'_eq_mem' (x : A) (xs : list A)
  (SORTED : isSorted compare xs = true)
  : memSorted' x xs = mem' x xs.
Proof.
  revert SORTED. induction xs as [ | y ys IH]; intros SORTED; trivial.
  rewrite isSorted_cons_iff in SORTED.
  destruct SORTED as [y_lt_ys ys_isSorted].
  cbn [memSorted' mem'].
  destruct (compare x y) as [ | | ] eqn: OBS; trivial.
  - symmetry. eapply mem'_all_lt_false. intros z z_in.
    exact (compare_Lt_trans x y z OBS (y_lt_ys z z_in)).
  - exact (IH ys_isSorted).
Qed.

Definition mem (x : A) (X : fset A) : bool :=
  memSorted' x X.(FSet.data).

Definition isSubsetOf (X : fset A) (X' : fset A) : Prop :=
  forall z : A, z ∈ X.(FSet.data) -> z ∈ X'.(FSet.data).

Theorem in_empty_iff
  : forall z : A, z ∈ empty.(FSet.data) <-> False.
Proof.
  intros z. reflexivity.
Qed.

Theorem in_add_iff (x : A) (X : fset A)
  : forall z : A, z ∈ (add x X).(FSet.data) <-> (x = z \/ z ∈ X.(FSet.data)).
Proof.
  exact (in_insert_iff x X.(FSet.data)).
Qed.

Theorem in_fromList_iff (xs : list A)
  : forall z : A, z ∈ (fromList xs).(FSet.data) <-> z ∈ xs.
Proof.
  intros z. unfold fromList. simpl. rewrite in_fold_right_insert_iff. simpl. tauto.
Qed.

Lemma length_fromList (xs : list A)
  (NO_DUP : L.NoDup xs)
  : length (fromList xs).(FSet.data) = length xs.
Proof.
  induction NO_DUP as [ | x xs NOT_IN NO_DUP IH]; trivial.
  change (length (insert x (fromList xs).(FSet.data)) = S (length xs)).
  rewrite length_insert.
  - f_equal. exact IH.
  - rewrite in_fromList_iff. exact NOT_IN.
Qed.

Theorem in_union_iff (X : fset A) (X' : fset A)
  : forall z : A, z ∈ (union X X').(FSet.data) <-> (z ∈ X.(FSet.data) \/ z ∈ X'.(FSet.data)).
Proof.
  exact (in_fold_right_insert_iff X.(FSet.data) X'.(FSet.data)).
Qed.

Theorem in_unions_iff (Xs : fset (fset A))
  : forall z : A, z ∈ (unions Xs).(FSet.data) <-> (exists X : fset A, X ∈ Xs.(FSet.data) /\ z ∈ X.(FSet.data)).
Proof.
  unfold unions. generalize Xs.(FSet.data) as Ys. clear Xs.
  induction Ys as [ | Y Ys IH]; intros z; cbn [L.fold_right].
  - simpl. split; [tauto | intros (X & [] & _)].
  - rewrite in_union_iff, IH. simpl. split.
    + intros [z_in_Y | (X & X_in & z_in_X)].
      * exists Y. split; [now left | exact z_in_Y].
      * exists X. split; [now right | exact z_in_X].
    + intros (X & [Y_eq_X | X_in] & z_in_X).
      * left. subst X. exact z_in_X.
      * right. exists X. split; assumption.
Qed.

Theorem mem_spec (x : A) (X : fset A)
  : forall b : bool, mem x X = b <-> (if b then x ∈ X.(FSet.data) else ~ x ∈ X.(FSet.data)).
Proof.
  assert (claim : mem x X = true <-> x ∈ X.(FSet.data)).
  { unfold mem. rewrite (memSorted'_eq_mem' x X.(FSet.data) X.(FSet.data_isSorted)).
    generalize X.(FSet.data) as xs. clear X.
    induction xs as [ | y ys IH]; simpl.
    - split; [congruence | tauto].
    - destruct (compare x y) as [ | | ] eqn: H_OBS.
      + rewrite compare_eq_iff in H_OBS. subst y. split; [intros _; now left | reflexivity].
      + rewrite IH. split; [now right | ].
        intros [y_eq_x | x_in_ys]; trivial.
        subst y. rewrite compare_refl in H_OBS. discriminate H_OBS.
      + rewrite IH. split; [now right | ].
        intros [y_eq_x | x_in_ys]; trivial.
        subst y. rewrite compare_refl in H_OBS. discriminate H_OBS.
  }
  intros [ | ].
  - exact claim.
  - split.
    + intros H_eq x_in. rewrite <- claim in x_in. congruence.
    + intros NOT_IN. destruct (mem x X) as [ | ] eqn: H_OBS; trivial.
      contradiction NOT_IN. now rewrite <- claim.
Qed.

End BASICS.

Section MAP_and_BIND.

Context {A : Type} {POSET_A : isPoset A} {HS_ORD_A : HsOrd A (POSET := POSET_A)}.
Context {B : Type} {POSET_B : isPoset B} {HS_ORD_B : HsOrd B (POSET := POSET_B)}.

Definition map (f : A -> B) (X : fset A) : fset B :=
  fromList (L.map f X.(FSet.data)).

Theorem in_map_iff (f : A -> B) (X : fset A)
  : forall y : B, y ∈ (map f X).(FSet.data) <-> (exists x : A, f x = y /\ x ∈ X.(FSet.data)).
Proof.
  intros y. unfold map. rewrite in_fromList_iff. eapply L.in_map_iff.
Qed.

Definition bind (X : fset A) (k : A -> fset B) : fset B :=
  L.fold_right (fun x : A => fun Y : fset B => union (k x) Y) empty X.(FSet.data).

Theorem in_bind_iff (X : fset A) (k : A -> fset B)
  : forall y : B, y ∈ (bind X k).(FSet.data) <-> (exists x : A, x ∈ X.(FSet.data) /\ y ∈ (k x).(FSet.data)).
Proof.
  unfold bind. generalize X.(FSet.data) as xs. clear X.
  induction xs as [ | x xs IH]; intros y; cbn [L.fold_right].
  - simpl. split; [tauto | intros (? & [] & _)].
  - rewrite in_union_iff, IH. simpl. split.
    + intros [y_in_kx | (x' & x'_in & y_in)].
      * exists x. split; [now left | exact y_in_kx].
      * exists x'. split; [now right | exact y_in].
    + intros (x' & [x_eq_x' | x'_in] & y_in).
      * left. subst x'. exact y_in.
      * right. exists x'. split; assumption.
Qed.

End MAP_and_BIND.

Section PRODUCT.

Context {A : Type} {POSET_A : isPoset A} {HS_ORD_A : HsOrd A (POSET := POSET_A)}.
Context {B : Type} {POSET_B : isPoset B} {HS_ORD_B : HsOrd B (POSET := POSET_B)}.

Definition product (X : fset A) (Y : fset B) : fset (A * B) :=
  bind X (fun x : A => map (fun y : B => (x, y)) Y).

Theorem product_iff (X : fset A) (Y : fset B)
  : forall x : A, forall y : B, (x, y) ∈ (product X Y).(FSet.data) <-> (x ∈ X.(FSet.data) /\ y ∈ Y.(FSet.data)).
Proof.
  intros x y. unfold product. rewrite in_bind_iff. split.
  - intros (x' & x'_in_X & xy_in). rewrite in_map_iff in xy_in.
    destruct xy_in as (y' & H_eq & y'_in_Y). inversion H_eq; subst x' y'.
    split; assumption.
  - intros [x_in_X y_in_Y]. exists x. split; trivial.
    rewrite in_map_iff. exists y. split; trivial.
Qed.

End PRODUCT.

Section POWERSET.

Context {A : Type} {POSET : isPoset A} {HS_ORD : HsOrd A (POSET := POSET)}.

Lemma isSorted_filter (p : A -> bool) (xs : list A)
  (xs_isSorted : isSorted compare xs = true)
  : isSorted compare (L.filter p xs) = true.
Proof.
  revert xs_isSorted. induction xs as [ | x xs IH]; intros xs_isSorted; simpl; trivial.
  rewrite isSorted_cons_iff in xs_isSorted. destruct xs_isSorted as [x_lt_xs xs_isSorted].
  destruct (p x) as [ | ]; [ | exact (IH xs_isSorted)].
  rewrite isSorted_cons_iff. split; [ | exact (IH xs_isSorted)].
  intros z z_in. rewrite L.filter_In in z_in. exact (x_lt_xs z (proj1 z_in)).
Qed.

Definition filter (p : A -> bool) (X : fset A) : fset A :=
  FSet.mk (L.filter p X.(FSet.data)) (isSorted_filter p X.(FSet.data) X.(FSet.data_isSorted)).

Theorem in_filter_iff (p : A -> bool) (X : fset A)
  : forall z : A, z ∈ (filter p X).(FSet.data) <-> (z ∈ X.(FSet.data) /\ p z = true).
Proof.
  intros z. exact (L.filter_In p z X.(FSet.data)).
Qed.

Fixpoint powerset' (xs : list A) {struct xs} : list (fset A) :=
  match xs with
  | [] => [empty]
  | x :: xs' =>
    let ps := powerset' xs' in
    ps ++ L.map (add x) ps
  end.

Definition powerset (X : fset A) : fset (fset A) :=
  fromList (powerset' X.(FSet.data)).

Lemma in_powerset'_iff (xs : list A)
  (xs_isSorted : isSorted compare xs = true)
  : forall Y : fset A, Y ∈ powerset' xs <-> (forall z : A, z ∈ Y.(FSet.data) -> z ∈ xs).
Proof.
  revert xs_isSorted. induction xs as [ | x xs IH]; intros xs_isSorted Y.
  - simpl. split.
    + intros [empty_eq_Y | []]. subst Y. simpl. tauto.
    + intros NO_MEM. left. symmetry. rewrite FSet.t_eq_iff.
      destruct Y as [ys ys_isSorted]. simpl in *.
      destruct ys as [ | y ys]; trivial.
      exfalso. exact (NO_MEM y (or_introl eq_refl)).
  - rewrite isSorted_cons_iff in xs_isSorted. destruct xs_isSorted as [x_lt_xs xs_isSorted].
    pose proof (IH xs_isSorted) as SPEC. clear IH.
    cbn [powerset']. rewrite L.in_app_iff, L.in_map_iff. split.
    + intros [Y_in_ps | (Z & add_eq_Y & Z_in_ps)] z z_in_Y.
      * right. exact (proj1 (SPEC Y) Y_in_ps z z_in_Y).
      * subst Y. rewrite in_add_iff in z_in_Y. destruct z_in_Y as [x_eq_z | z_in_Z].
        { now left. }
        { right. exact (proj1 (SPEC Z) Z_in_ps z z_in_Z). }
    + intros Y_sub. destruct (mem x Y) as [ | ] eqn: H_mem.
      * right. rewrite mem_spec in H_mem.
        exists (filter (fun z : A => match compare x z with Eq => false | _ => true end) Y). split.
        { rewrite fset_eq_spec. intros w. rewrite in_add_iff, in_filter_iff. split.
          - intros [x_eq_w | [w_in _]]; [subst w; exact H_mem | exact w_in].
          - intros w_in_Y. cbv beta. destruct (compare x w) as [ | | ] eqn: H_OBS.
            + left. exact (proj1 (compare_eq_iff x w) H_OBS).
            + right. split; [exact w_in_Y | reflexivity].
            + right. split; [exact w_in_Y | reflexivity].
        }
        { rewrite SPEC. intros z z_in. rewrite in_filter_iff in z_in.
          destruct z_in as [z_in_Y H_p]. cbv beta in H_p.
          pose proof (Y_sub z z_in_Y) as [x_eq_z | z_in_xs]; trivial.
          subst z. rewrite compare_refl in H_p. discriminate H_p.
        }
      * left. rewrite SPEC. intros z z_in_Y.
        pose proof (Y_sub z z_in_Y) as [x_eq_z | z_in_xs]; trivial.
        subst z. exfalso. rewrite mem_spec in H_mem. contradiction (H_mem z_in_Y).
Qed.

Theorem in_powerset_iff (X : fset A)
  : forall Y : fset A, Y ∈ (powerset X).(FSet.data) <-> isSubsetOf Y X.
Proof.
  intros Y. unfold powerset. rewrite in_fromList_iff.
  exact (in_powerset'_iff X.(FSet.data) X.(FSet.data_isSorted) Y).
Qed.

Theorem filter_in_powerset (p : A -> bool) (X : fset A)
  : filter p X ∈ (powerset X).(FSet.data).
Proof.
  rewrite in_powerset_iff. intros z z_in.
  rewrite in_filter_iff in z_in. exact (proj1 z_in).
Qed.

Lemma NoDup_powerset' (xs : list A)
  (xs_isSorted : isSorted compare xs = true)
  : L.NoDup (powerset' xs).
Proof.
  revert xs_isSorted. induction xs as [ | x xs IH]; intros xs_isSorted.
  - simpl. econstructor; [intros [] | econstructor].
  - rewrite isSorted_cons_iff in xs_isSorted. destruct xs_isSorted as [x_lt_xs xs_isSorted].
    pose proof (IH xs_isSorted) as NO_DUP. clear IH.
    pose proof (in_powerset'_iff xs xs_isSorted) as SPEC.
    assert (x_not_in_xs : ~ x ∈ xs).
    { intros x_in. pose proof (x_lt_xs x x_in) as LT.
      rewrite compare_refl in LT. discriminate LT.
    }
    assert (claim : forall Y : fset A, Y ∈ powerset' xs -> ~ x ∈ Y.(FSet.data)).
    { intros Y Y_in x_in_Y. contradiction x_not_in_xs. exact (proj1 (SPEC Y) Y_in x x_in_Y). }
    cbn [powerset']. eapply L.NoDup_app; trivial.
    + eapply NoDup_map_inj; trivial. intros Y Z Y_in Z_in H_eq.
      rewrite fset_eq_spec. intros w. rewrite fset_eq_spec in H_eq.
      specialize (H_eq w). rewrite !in_add_iff in H_eq.
      destruct (compare x w) as [ | | ] eqn: H_OBS.
      * rewrite compare_eq_iff in H_OBS. subst w. split.
        { intros w_in. contradiction (claim Y Y_in w_in). }
        { intros w_in. contradiction (claim Z Z_in w_in). }
      * split.
        { intros w_in. pose proof (proj1 H_eq (or_intror w_in)) as [x_eq_w | H]; trivial.
          subst w. rewrite compare_refl in H_OBS. discriminate H_OBS.
        }
        { intros w_in. pose proof (proj2 H_eq (or_intror w_in)) as [x_eq_w | H]; trivial.
          subst w. rewrite compare_refl in H_OBS. discriminate H_OBS.
        }
      * split.
        { intros w_in. pose proof (proj1 H_eq (or_intror w_in)) as [x_eq_w | H]; trivial.
          subst w. rewrite compare_refl in H_OBS. discriminate H_OBS.
        }
        { intros w_in. pose proof (proj2 H_eq (or_intror w_in)) as [x_eq_w | H]; trivial.
          subst w. rewrite compare_refl in H_OBS. discriminate H_OBS.
        }
    + intros Y Y_in Y_in'. rewrite L.in_map_iff in Y_in'.
      destruct Y_in' as (Z & add_eq_Y & Z_in). contradiction (claim Y Y_in).
      rewrite <- add_eq_Y. rewrite in_add_iff. now left.
Qed.

Lemma length_powerset' (xs : list A)
  : length (powerset' xs) = pow2 (length xs).
Proof.
  induction xs as [ | x xs IH]; trivial.
  cbn [powerset' length pow2]. rewrite length_app, length_map, IH. lia.
Qed.

Theorem powerset_length (X : fset A)
  : length (powerset X).(FSet.data) = pow2 (length X.(FSet.data)).
Proof.
  unfold powerset. rewrite length_fromList.
  - exact (length_powerset' X.(FSet.data)).
  - exact (NoDup_powerset' X.(FSet.data) X.(FSet.data_isSorted)).
Qed.

End POWERSET.

#[global] Hint Rewrite @in_empty_iff @in_add_iff @in_fromList_iff @in_union_iff @in_unions_iff @in_filter_iff @in_map_iff @in_bind_iff @product_iff @in_powerset_iff @mem_spec : simplication_hints.

End FS.

Lemma fset_NoDup {A : Type} {POSET_A : isPoset A} {HsOrd_A : HsOrd A} (X : fset A)
  : L.NoDup X.(FSet.data).
Proof.
  destruct X as [xs SORTED]. cbn [FSet.data]. revert SORTED.
  induction xs as [ | x xs IH]; intros SORTED; [econstructor | ].
  rewrite isSorted_cons_iff in SORTED. destruct SORTED as [LT SORTED].
  econstructor; [ | exact (IH SORTED)].
  intros IN. pose proof (LT x IN) as CONTRA. rewrite compare_refl in CONTRA. discriminate CONTRA.
Qed.

Module LazyList.

Inductive tail {A : Type} : list A -> list A -> Prop :=
  | tail_step (x : A) (xs : list A)
      : tail xs (x :: xs).

Fixpoint tailWf {A : Type} (xs : list A) : Acc tail xs.
Proof.
  destruct xs as [ | x xs].
  - constructor. intros next STEP. inversion STEP.
  - constructor. intros next STEP. inversion STEP; subst.
    exact (@tailWf A xs).
Defined.

Definition wf {A : Type} : well_founded (@tail A) := tailWf.

End LazyList.

Section SET_OPERATIONS.

Context {A : Type} {A_isPoset : isPoset A}
  {HsOrd_A : HsOrd A (POSET := A_isPoset)}.

Lemma fset_length_le (X : fset A) (Y : fset A)
  (SUB : forall z : A,
    L.In z X.(FSet.data) -> L.In z Y.(FSet.data))
  : length X.(FSet.data) <= length Y.(FSet.data).
Proof.
  eapply L.NoDup_incl_length; [exact (fset_NoDup X) | exact SUB].
Qed.

Definition fsetSaturationInv (V X : fset A) : Prop :=
  forall z : A, L.In z X.(FSet.data) -> L.In z V.(FSet.data).

Definition fsetSaturationMeasure (V X : fset A) : nat :=
  length V.(FSet.data) - length X.(FSet.data).

Inductive fsetSaturationRel
  (step : fset A -> fset A) : fset A -> fset A -> Prop :=
  | fsetSaturationRel_step (X : fset A)
      (CHANGED : step X <> X)
      : fsetSaturationRel step (step X) X.

Lemma fsetSaturationStep_lt
  (V : fset A) (step : fset A -> fset A)
  (MONO : forall X : fset A, forall z : A,
    L.In z X.(FSet.data) -> L.In z (step X).(FSet.data))
  (CLOSED : forall X : fset A,
    fsetSaturationInv V X -> fsetSaturationInv V (step X))
  (X : fset A) (INV : fsetSaturationInv V X)
  (CHANGED : step X <> X)
  : fsetSaturationMeasure V (step X) < fsetSaturationMeasure V X.
Proof.
  set (Y := step X) in *.
  assert (XY : forall z : A,
    L.In z X.(FSet.data) -> L.In z Y.(FSet.data)).
  { exact (MONO X). }
  assert (LT : length X.(FSet.data) < length Y.(FSet.data)).
  { pose proof (fset_length_le X Y XY) as LE.
    assert (NE_LENGTH :
      length X.(FSet.data) <> length Y.(FSet.data)).
    { intros EQ. apply CHANGED. rewrite fset_eq_spec. intros z. split.
      - intros IN.
        assert (LEN_REV :
          length Y.(FSet.data) <= length X.(FSet.data)) by lia.
        pose proof
          (L.NoDup_length_incl (fset_NoDup X) LEN_REV XY) as REV.
        exact (REV z IN).
      - exact (XY z). }
    lia. }
  pose proof (fset_length_le Y V (CLOSED X INV)) as YV.
  unfold fsetSaturationMeasure. lia.
Qed.

Definition fsetSaturationRelAcc
  (V : fset A) (step : fset A -> fset A)
  (MONO : forall X : fset A, forall z : A,
    L.In z X.(FSet.data) -> L.In z (step X).(FSet.data))
  (CLOSED : forall X : fset A,
    fsetSaturationInv V X -> fsetSaturationInv V (step X))
  : forall X : fset A,
      fsetSaturationInv V X ->
      Acc Nat.lt (fsetSaturationMeasure V X) ->
      Acc (fsetSaturationRel step) X.
Proof.
  refine (fix go (X : fset A) (INV : fsetSaturationInv V X)
    (H_Acc : Acc Nat.lt (fsetSaturationMeasure V X)) {struct H_Acc}
    : Acc (fsetSaturationRel step) X := _).
  constructor. intros Y REL. destruct REL as [X NE].
  exact (go (step X) (CLOSED X INV)
    (Acc_inv H_Acc
      (fsetSaturationStep_lt V step MONO CLOSED X INV NE))).
Defined.

Definition fsetSaturationCounter
  (V X : fset A) (credit : list A) : Prop :=
  fsetSaturationMeasure V X <= length credit.

Lemma fsetSaturationCounter_start
  (V X : fset A) (credit : list A)
  (CARRIER : length V.(FSet.data) <= length credit)
  : fsetSaturationCounter V X credit.
Proof.
  unfold fsetSaturationCounter, fsetSaturationMeasure. lia.
Qed.

Lemma fsetSaturationCounter_step
  (V : fset A) (step : fset A -> fset A)
  (MONO : forall X : fset A, forall z : A,
    L.In z X.(FSet.data) -> L.In z (step X).(FSet.data))
  (CLOSED : forall X : fset A,
    fsetSaturationInv V X -> fsetSaturationInv V (step X))
  (X : fset A) (INV : fsetSaturationInv V X)
  (CHANGED : step X <> X) (x : A) (credit : list A)
  (COUNTER : fsetSaturationCounter V X (x :: credit))
  : fsetSaturationCounter V (step X) credit.
Proof.
  unfold fsetSaturationCounter in *. cbn [length] in COUNTER.
  pose proof
    (fsetSaturationStep_lt V step MONO CLOSED X INV CHANGED).
  lia.
Qed.

Lemma fsetSaturationCounter_empty
  (V : fset A) (step : fset A -> fset A)
  (MONO : forall X : fset A, forall z : A,
    L.In z X.(FSet.data) -> L.In z (step X).(FSet.data))
  (CLOSED : forall X : fset A,
    fsetSaturationInv V X -> fsetSaturationInv V (step X))
  (X : fset A) (INV : fsetSaturationInv V X)
  (CHANGED : step X <> X)
  (COUNTER : fsetSaturationCounter V X [])
  : False.
Proof.
  unfold fsetSaturationCounter in COUNTER. cbn [length] in COUNTER.
  pose proof
    (fsetSaturationStep_lt V step MONO CLOSED X INV CHANGED).
  lia.
Qed.

Definition fsetSaturationRelAccList
  (V : fset A) (step : fset A -> fset A)
  (MONO : forall X : fset A, forall z : A,
    L.In z X.(FSet.data) -> L.In z (step X).(FSet.data))
  (CLOSED : forall X : fset A,
    fsetSaturationInv V X -> fsetSaturationInv V (step X))
  : forall (X : fset A) (credit : list A),
      fsetSaturationInv V X ->
      fsetSaturationCounter V X credit ->
      Acc LazyList.tail credit ->
      Acc (fsetSaturationRel step) X.
Proof.
  refine (fix go (X : fset A) (credit : list A)
    (INV : fsetSaturationInv V X)
    (COUNTER : fsetSaturationCounter V X credit)
    (H_Acc : Acc LazyList.tail credit) {struct H_Acc}
    : Acc (fsetSaturationRel step) X := _).
  constructor. intros Y REL. destruct REL as [X CHANGED].
  destruct credit as [ | x credit].
  - exact (False_ind _
      (fsetSaturationCounter_empty
        V step MONO CLOSED X INV CHANGED COUNTER)).
  - exact (go (step X) credit (CLOSED X INV)
      (fsetSaturationCounter_step
        V step MONO CLOSED X INV CHANGED x credit COUNTER)
      (Acc_inv H_Acc (LazyList.tail_step x credit))).
Defined.

Definition fsetSaturationRun (step : fset A -> fset A)
  : forall X : fset A, Acc (fsetSaturationRel step) X -> fset A.
Proof.
  refine (fix go (X : fset A)
    (H_Acc : Acc (fsetSaturationRel step) X) {struct H_Acc}
    : fset A := _).
  set (Y := step X).
  destruct (eqb Y X) eqn: SAME.
  - exact X.
  - exact (go Y
      (Acc_inv H_Acc
        (fsetSaturationRel_step step X
          (proj1 (eqb_neq Y X) SAME)))).
Defined.

Definition inter (X : fset A) (Y : fset A) : fset A :=
  FS.filter (fun z : A => FS.mem z Y) X.

Lemma in_inter_iff (X : fset A) (Y : fset A) (z : A)
  : L.In z (inter X Y).(FSet.data) <->
    (L.In z X.(FSet.data) /\ L.In z Y.(FSet.data)).
Proof.
  unfold inter. rewrite FS.in_filter_iff.
  split; intros [H1 H2]; split; trivial.
  - exact (proj1 (FS.mem_spec z Y true) H2).
  - exact (proj2 (FS.mem_spec z Y true) H2).
Qed.

Definition diff (X : fset A) (Y : fset A) : fset A :=
  FS.filter (fun z : A => negb (FS.mem z Y)) X.

Lemma in_diff_iff (X : fset A) (Y : fset A) (z : A)
  : L.In z (diff X Y).(FSet.data) <->
    (L.In z X.(FSet.data) /\ ~ L.In z Y.(FSet.data)).
Proof.
  unfold diff. rewrite FS.in_filter_iff.
  split; intros [H1 H2]; split; trivial.
  - rewrite negb_true_iff in H2.
    exact (proj1 (FS.mem_spec z Y false) H2).
  - rewrite negb_true_iff.
    exact (proj2 (FS.mem_spec z Y false) H2).
Qed.

End SET_OPERATIONS.

Lemma compare_nat_Lt_iff (m : nat) (n : nat)
  : compare m n = Lt <-> m < n.
Proof.
  revert n. induction m as [ | m IH]; intros [ | n]; cbn.
  - split; [intros H; discriminate H | lia].
  - split; [intros _; lia | reflexivity].
  - split; [intros H; discriminate H | lia].
  - rewrite (IH n). lia.
Qed.

Lemma isSorted_natSeq (len : nat) (start : nat)
  : isSorted compare (L.seq start len) = true.
Proof.
  revert start. induction len as [ | len IH]; intros start;
    [reflexivity | ].
  cbn [L.seq].
  eapply (proj2 (isSorted_cons_iff start (L.seq (S start) len))). split.
  - intros z z_in. rewrite L.in_seq in z_in.
    rewrite compare_nat_Lt_iff. lia.
  - eapply IH.
Qed.

Definition natRange (start : nat) (len : nat) : fset nat :=
  FSet.mk (L.seq start len) (isSorted_natSeq len start).

Lemma in_natRange_iff (start : nat) (len : nat) (z : nat)
  : L.In z (natRange start len).(FSet.data) <->
    start <= z < start + len.
Proof.
  cbn [natRange FSet.data]. exact (L.in_seq len start z).
Qed.

Section SORTED_BUILD.

Context {A : Type} {A_isPoset : isPoset A}
  {HsOrd_A : HsOrd A (POSET := A_isPoset)}.
Context {B : Type} {B_isPoset : isPoset B}
  {HsOrd_B : HsOrd B (POSET := B_isPoset)}.

Definition prodList (xs : list A) (ys : list B) : list (A * B) :=
  L.concat (L.map (fun x : A => L.map (fun y : B => (x, y)) ys) xs).

Lemma in_prodList_iff (xs : list A) (ys : list B) (p : A * B)
  : L.In p (prodList xs ys) <->
    (L.In (fst p) xs /\ L.In (snd p) ys).
Proof.
  unfold prodList. rewrite L.in_concat. split.
  - intros (l & l_in & p_in). rewrite L.in_map_iff in l_in.
    destruct l_in as (x & EQ & x_in). subst l.
    rewrite L.in_map_iff in p_in. destruct p_in as (y & EQ & y_in).
    subst p. split; assumption.
  - intros [fst_in snd_in].
    exists (L.map (fun y : B => (fst p, y)) ys). split.
    + rewrite L.in_map_iff. exists (fst p). split;
        [reflexivity | exact fst_in].
    + rewrite L.in_map_iff. exists (snd p). split;
        [ | exact snd_in].
      destruct p as [x y]. reflexivity.
Qed.

Lemma isSorted_map_pair (x : A) (ys : list B)
  (Hy : isSorted compare ys = true)
  : isSorted compare (L.map (fun y : B => (x, y)) ys) = true.
Proof.
  revert Hy. induction ys as [ | y ys IH]; intros Hy;
    [reflexivity | ].
  pose proof (proj1 (isSorted_cons_iff y ys) Hy) as
    [y_lt_ys ys_sorted].
  cbn [L.map].
  eapply (proj2
    (isSorted_cons_iff (x, y) (L.map (fun y' : B => (x, y')) ys))).
  split.
  - intros z z_in. rewrite L.in_map_iff in z_in.
    destruct z_in as (y' & EQ & y'_in). subst z.
    change (compare (x, y) (x, y')) with
      (pair_compare (x, y) (x, y')).
    unfold pair_compare. cbn [fst snd]. rewrite compare_refl.
    exact (y_lt_ys y' y'_in).
  - exact (IH ys_sorted).
Qed.

Lemma isSorted_prodList (xs : list A) (ys : list B)
  (Hx : isSorted compare xs = true)
  (Hy : isSorted compare ys = true)
  : isSorted compare (prodList xs ys) = true.
Proof.
  revert Hx. induction xs as [ | x xs IH]; intros Hx;
    [reflexivity | ].
  pose proof (proj1 (isSorted_cons_iff x xs) Hx) as
    [x_lt_xs xs_sorted].
  unfold prodList. cbn [L.map L.concat].
  eapply isSorted_app.
  - exact (isSorted_map_pair x ys Hy).
  - exact (IH xs_sorted).
  - intros u v u_in v_in. rewrite L.in_map_iff in u_in.
    destruct u_in as (y & EQ & _). subst u.
    change (prodList xs ys) with
      (L.concat
        (L.map (fun x' : A => L.map (fun y' : B => (x', y')) ys) xs))
      in v_in.
    pose proof (proj1 (in_prodList_iff xs ys v) v_in) as [v_fst_in _].
    change (compare (x, y) v) with (pair_compare (x, y) v).
    unfold pair_compare. cbn [fst].
    rewrite (x_lt_xs (fst v) v_fst_in). reflexivity.
Qed.

Definition fprod (X : fset A) (Y : fset B) : fset (A * B) :=
  FSet.mk (prodList X.(FSet.data) Y.(FSet.data))
    (isSorted_prodList X.(FSet.data) Y.(FSet.data)
      X.(FSet.data_isSorted) Y.(FSet.data_isSorted)).

Lemma in_fprod_iff (X : fset A) (Y : fset B) (p : A * B)
  : L.In p (fprod X Y).(FSet.data) <->
    (L.In (fst p) X.(FSet.data) /\ L.In (snd p) Y.(FSet.data)).
Proof.
  exact (in_prodList_iff X.(FSet.data) Y.(FSet.data) p).
Qed.

End SORTED_BUILD.
