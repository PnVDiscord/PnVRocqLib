Require Import PnV.Prelude.Prelude.

#[local] Infix "=~=" := is_similar_to : type_scope.
#[local] Infix "\in" := E.In.
#[local] Infix "∈" := L.In.

#[universes(polymorphic=yes)]
Definition Similarity_list_finite_ensemble {ELEM : Type} {ELEM' : Type} (ELEM_sim : Similarity ELEM ELEM') : Similarity (list ELEM) (ensemble ELEM') :=
  fun xs : list ELEM => fun X' : ensemble ELEM' => ⟪ SUBSET1 : forall x, x ∈ xs -> (exists x', x =~= x' /\ x' \in X') ⟫ /\ ⟪ SUBSET2 : forall x', x' \in X' -> (exists x, x =~= x' /\ x ∈ xs) ⟫.

#[global, universes(polymorphic=yes)]
Instance list_corresponds_to_finite_ensemble {ELEM : Type} : Similarity (list ELEM) (ensemble ELEM) :=
  Similarity_list_finite_ensemble eq.

#[universes(polymorphic=yes)]
Theorem list_corresponds_to_finite_ensemble_iff (ELEM : Type) (xs : list ELEM) (X : ensemble ELEM)
  : xs =~= X <-> (forall x, x ∈ xs <-> x \in X).
Proof.
  done!.
Qed.

#[global] Hint Rewrite list_corresponds_to_finite_ensemble_iff : simplication_hints.

#[universes(polymorphic=yes)]
Theorem list_corresponds_to_finite_ensemble_flat_map {A : Type} {B : Type} (xs : list A) (X : ensemble A) (f : A -> list B) (F : A -> ensemble B)
  (xs_sim : xs =~= X)
  (f_sim : forall x, f x =~= F x)
  : L.flat_map f xs =~= (X >>= F).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff.
  intros b. rewrite L.in_flat_map. split.
  - intros [x [x_in b_in]].
    exists x. split.
    + pose proof xs_sim as XS_SIM.
      rewrite list_corresponds_to_finite_ensemble_iff in XS_SIM.
      exact (proj1 (XS_SIM x) x_in).
    + pose proof (f_sim x) as F_SIM.
      rewrite list_corresponds_to_finite_ensemble_iff in F_SIM.
      exact (proj1 (F_SIM b) b_in).
  - intros [x [x_in b_in]].
    exists x. split.
    + pose proof xs_sim as XS_SIM.
      rewrite list_corresponds_to_finite_ensemble_iff in XS_SIM.
      exact (proj2 (XS_SIM x) x_in).
    + pose proof (f_sim x) as F_SIM.
      rewrite list_corresponds_to_finite_ensemble_iff in F_SIM.
      exact (proj2 (F_SIM b) b_in).
Qed.

Definition mem@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (x : A) (xs : list A) : bool :=
  if in_dec eq_dec x xs then true else false.

Definition add@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (x : A) (xs : list A) : list A :=
  if mem x xs then xs else x :: xs.

Fixpoint union@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (xs : list A) (ys : list A) {struct xs} : list A :=
  match xs with
  | [] => ys
  | x :: xs' => union xs' (add x ys)
  end.

Lemma mem_true_iff@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (x : A) (xs : list A)
  : mem x xs = true <-> x ∈ xs.
Proof.
  unfold mem. destruct (in_dec eq_dec x xs) as [IN | NOT_IN]; done.
Qed.

Lemma mem_false_iff@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (x : A) (xs : list A)
  : mem x xs = false <-> ~ x ∈ xs.
Proof.
  unfold mem. destruct (in_dec eq_dec x xs) as [IN | NOT_IN]; done.
Qed.

Lemma add_sound@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (x : A) (y : A) (xs : list A)
  (IN : y ∈ add x xs)
  : y = x \/ y ∈ xs.
Proof.
  unfold add, mem in IN. destruct (in_dec eq_dec x xs) as [IN_x | NOT_IN_x].
  - right. exact IN.
  - simpl in IN. destruct IN as [EQ | IN].
    + left. symmetry. exact EQ.
    + right. exact IN.
Qed.

Lemma add_complete@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (x : A) (y : A) (xs : list A)
  (IN : y = x \/ y ∈ xs)
  : y ∈ add x xs.
Proof.
  unfold add, mem. destruct (in_dec eq_dec x xs) as [IN_x | NOT_IN_x].
  - destruct IN as [EQ | IN].
    + subst y. exact IN_x.
    + exact IN.
  - simpl. destruct IN as [EQ | IN].
    + left. symmetry. exact EQ.
    + right. exact IN.
Qed.

Lemma union_sound@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (xs : list A) (ys : list A) (z : A)
  (IN : z ∈ union xs ys)
  : z ∈ xs \/ z ∈ ys.
Proof.
  revert ys IN. induction xs as [ | x xs IH]; simpl; intros ys IN.
  - right. exact IN.
  - pose proof (IH (add x ys) IN) as [IN_xs | IN_add].
    + left. right. exact IN_xs.
    + pose proof (add_sound x z ys IN_add) as [EQ | IN_ys].
      * left. left. symmetry. exact EQ.
      * right. exact IN_ys.
Qed.

Lemma union_complete@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (xs : list A) (ys : list A) (z : A)
  (IN : z ∈ xs \/ z ∈ ys)
  : z ∈ union xs ys.
Proof.
  revert ys IN. induction xs as [ | x xs IH]; simpl; intros ys IN.
  - destruct IN as [IN | IN]; [contradiction | exact IN].
  - eapply IH. destruct IN as [[EQ | IN_xs] | IN_ys].
    + right. eapply add_complete. left. symmetry. exact EQ.
    + left. exact IN_xs.
    + right. eapply add_complete. right. exact IN_ys.
Qed.

Lemma remove_length_lt@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (x : A) (xs : list A)
  (IN : x ∈ xs)
  : length (remove eq_dec x xs) < length xs.
Proof.
  induction xs as [ | y ys IH]; simpl in IN |- *.
  - contradiction.
  - destruct (eq_dec x y) as [EQ | NE].
    + pose proof (remove_length_le eq_dec ys x). lia.
    + simpl. destruct IN as [EQ | IN].
      * subst y. contradiction.
      * pose proof (IH IN) as LT. lia.
Qed.

Fixpoint powerset@{u} {A : Type@{u}} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x :: xs' =>
    let ps := powerset xs' in
    ps ++ map (fun ys => x :: ys) ps
  end.

Lemma filter_in_powerset@{u} {A : Type@{u}} (p : A -> bool) (xs : list A)
  : filter p xs ∈ powerset xs.
Proof.
  induction xs as [ | x xs IH]; simpl.
  - left. reflexivity.
  - destruct (p x) eqn: H.
    + rewrite in_app_iff. right. rewrite in_map_iff.
      exists (filter p xs). split; [reflexivity | exact IH].
    + rewrite in_app_iff. left. exact IH.
Qed.

Definition product@{u v} {A : Type@{u}} {B : Type@{v}} (xs : list A) (ys : list B)
  : list (A * B) :=
  flat_map (fun x => map (fun y => (x, y)) ys) xs.

Lemma product_sound@{u v} {A : Type@{u}} {B : Type@{v}} (xs : list A) (ys : list B) x y
  (IN : (x, y) ∈ product xs ys)
  : x ∈ xs /\ y ∈ ys.
Proof.
  unfold product in IN. rewrite in_flat_map in IN.
  destruct IN as (x0 & IN_X & IN_PAIR).
  rewrite in_map_iff in IN_PAIR.
  destruct IN_PAIR as (y0 & EQ & IN_Y). inv EQ.
  split; [exact IN_X | exact IN_Y].
Qed.

Lemma product_complete@{u v} {A : Type@{u}} {B : Type@{v}} (xs : list A) (ys : list B) x y
  (IN_X : x ∈ xs)
  (IN_Y : y ∈ ys)
  : (x, y) ∈ product xs ys.
Proof.
  unfold product. rewrite in_flat_map.
  exists x. split; [exact IN_X | ].
  rewrite in_map_iff. exists y. split; [reflexivity | exact IN_Y].
Qed.

Lemma NoDup_map_injective_on
  {A : Type}
  {B : Type}
  (f : A -> B)
  (xs : list A)
  (INJ : forall x y, x ∈ xs -> y ∈ xs -> f x = f y -> x = y)
  (NO_DUP : NoDup xs)
  : NoDup (map f xs).
Proof.
  induction NO_DUP as [ | x xs NOT_IN NO_DUP IH]; simpl.
  - econs.
  - econs.
    + intros IN_MAP. rewrite in_map_iff in IN_MAP.
      destruct IN_MAP as (y & EQ & IN_Y).
      assert (x = y) as X_EQ_Y.
      { eapply INJ; [left; reflexivity | right; exact IN_Y | symmetry; exact EQ]. }
      subst y. contradiction.
    + eapply IH. intros y z IN_Y IN_Z EQ.
      eapply INJ; [right; exact IN_Y | right; exact IN_Z | exact EQ].
Qed.

Lemma list_bind_flat_map {A : Type} {B : Type} (xs : list A) (k : A -> list B)
  : (xs >>= k) = L.flat_map k xs.
Proof.
  change (concat (map k xs) = L.flat_map k xs).
  induction xs as [ | x xs IH]; simpl; congruence.
Qed.

Lemma list_bind_complete {A : Type} {B : Type} (xs : list A) (k : A -> list B) (x : A) (y : B)
  (IN_X : x ∈ xs)
  (IN_Y : y ∈ k x)
  : y ∈ (xs >>= k).
Proof.
  rewrite list_bind_flat_map. rewrite in_flat_map.
  exists x. split; [exact IN_X | exact IN_Y].
Qed.

Lemma list_pure_complete {A : Type} (x : A)
  : x ∈ pure x.
Proof.
  change (x ∈ [x]). left. reflexivity.
Qed.
