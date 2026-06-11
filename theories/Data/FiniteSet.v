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

#[universes(polymorphic=yes)]
Definition mem@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (x : A) (xs : list A) : bool :=
  if in_dec eq_dec x xs then true else false.

#[universes(polymorphic=yes)]
Definition add@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (x : A) (xs : list A) : list A :=
  if mem x xs then xs else x :: xs.

#[universes(polymorphic=yes)]
Fixpoint union@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (xs : list A) (ys : list A) {struct xs} : list A :=
  match xs with
  | [] => ys
  | x :: xs' => union xs' (add x ys)
  end.

#[universes(polymorphic=yes)]
Fixpoint iter@{u} {A : Type@{u}} (fuel : nat) (step : A -> A) (x : A) {struct fuel} : A :=
  match fuel with
  | O => x
  | S fuel' => iter fuel' step (step x)
  end.

#[universes(polymorphic=yes)]
Lemma iter_succ@{u} {A : Type@{u}} (fuel : nat) (step : A -> A) (x : A)
  : iter (S fuel) step x = step (iter fuel step x).
Proof.
  revert x. induction fuel as [ | fuel IH]; intros x; simpl.
  - reflexivity.
  - change (iter (S fuel) step (step x) = step (iter fuel step (step x))).
    eapply IH.
Qed.

Fixpoint pow2 (n : nat) {struct n} : nat :=
  match n with
  | O => 1
  | S n' => 2 * pow2 n'
  end.

#[universes(polymorphic=yes)]
Definition nonempty@{u} {A : Type@{u}} (xs : list A) : bool :=
  match xs with
  | [] => false
  | _ :: _ => true
  end.

#[universes(polymorphic=yes)]
Fixpoint normalize@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (xs : list A) {struct xs} : list A :=
  match xs with
  | [] => []
  | x :: xs' => add x (normalize xs')
  end.

#[universes(polymorphic=yes)]
Fixpoint unions@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (xss : list (list A)) {struct xss} : list A :=
  match xss with
  | [] => []
  | xs :: xss' => union xs (unions xss')
  end.

#[universes(polymorphic=yes)]
Lemma mem_true_iff@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (x : A) (xs : list A)
  : mem x xs = true <-> x ∈ xs.
Proof.
  unfold mem. destruct (in_dec eq_dec x xs) as [IN | NOT_IN]; done.
Qed.

#[universes(polymorphic=yes)]
Lemma mem_false_iff@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (x : A) (xs : list A)
  : mem x xs = false <-> ~ x ∈ xs.
Proof.
  unfold mem. destruct (in_dec eq_dec x xs) as [IN | NOT_IN]; done.
Qed.

#[universes(polymorphic=yes)]
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

#[universes(polymorphic=yes)]
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

#[universes(polymorphic=yes)]
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

#[universes(polymorphic=yes)]
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

#[universes(polymorphic=yes)]
Lemma normalize_sound@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (xs : list A) (z : A)
  (IN : z ∈ normalize xs)
  : z ∈ xs.
Proof.
  induction xs as [ | x xs IH]; simpl in IN |- *.
  - exact IN.
  - pose proof (add_sound x z (normalize xs) IN) as [EQ | IN'].
    + left. symmetry. exact EQ.
    + right. eapply IH. exact IN'.
Qed.

#[universes(polymorphic=yes)]
Lemma normalize_complete@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (xs : list A) (z : A)
  (IN : z ∈ xs)
  : z ∈ normalize xs.
Proof.
  induction xs as [ | x xs IH]; simpl in IN |- *.
  - exact IN.
  - eapply add_complete. destruct IN as [EQ | IN'].
    + left. symmetry. exact EQ.
    + right. eapply IH. exact IN'.
Qed.

#[universes(polymorphic=yes)]
Lemma unions_sound@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (xss : list (list A)) (z : A)
  (IN : z ∈ unions xss)
  : exists xs, xs ∈ xss /\ z ∈ xs.
Proof.
  induction xss as [ | xs xss IH]; simpl in IN.
  - contradiction.
  - pose proof (union_sound xs (unions xss) z IN) as [IN_XS | IN_XSS].
    + exists xs. split; [left; reflexivity | exact IN_XS].
    + pose proof (IH IN_XSS) as (xs' & IN_XSS' & IN_XS').
      exists xs'. split; [right; exact IN_XSS' | exact IN_XS'].
Qed.

#[universes(polymorphic=yes)]
Lemma unions_complete@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (xss : list (list A)) (xs : list A) (z : A)
  (IN_XSS : xs ∈ xss)
  (IN_XS : z ∈ xs)
  : z ∈ unions xss.
Proof.
  induction xss as [ | xs' xss IH]; simpl in IN_XSS |- *.
  - contradiction.
  - eapply union_complete. destruct IN_XSS as [EQ | IN_XSS].
    + left. congruence.
    + right. eapply IH; eauto.
Qed.

#[universes(polymorphic=yes)]
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

#[universes(polymorphic=yes)]
Fixpoint powerset@{u} {A : Type@{u}} (xs : list A) : list (list A) :=
  match xs with
  | [] => [[]]
  | x :: xs' =>
    let ps := powerset xs' in
    ps ++ map (fun ys => x :: ys) ps
  end.

#[universes(polymorphic=yes)]
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

#[universes(polymorphic=yes)]
Lemma powerset_length@{u} {A : Type@{u}} (xs : list A)
  : length (powerset xs) = pow2 (length xs).
Proof.
  induction xs as [ | x xs IH]; simpl.
  - reflexivity.
  - rewrite length_app. rewrite length_map. rewrite IH. lia.
Qed.

#[universes(polymorphic=yes)]
Fixpoint index_of@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (x : A) (xs : list A) {struct xs} : nat :=
  match xs with
  | [] => O
  | x' :: xs' => if eq_dec x x' then O else S (index_of x xs')
  end.

#[universes(polymorphic=yes)]
Definition lookup@{u} {A : Type@{u}} (default : A) (n : nat) (xs : list A) : A :=
  nth n xs default.

#[universes(polymorphic=yes)]
Lemma lookup_index_of@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (x : A) (xs : list A) (default : A)
  (IN : x ∈ xs)
  : lookup default (index_of x xs) xs = x.
Proof.
  induction xs as [ | x' xs IH]; simpl in IN |- *; [contradiction | ].
  destruct (eq_dec x x') as [EQ | NE].
  - symmetry. exact EQ.
  - destruct IN as [EQ | IN]; [contradiction NE; symmetry; exact EQ | ].
    simpl. eapply IH. exact IN.
Qed.

#[universes(polymorphic=yes)]
Lemma index_of_lt@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (x : A) (xs : list A)
  (IN : x ∈ xs)
  : index_of x xs < length xs.
Proof.
  induction xs as [ | x' xs IH]; simpl in IN |- *; [contradiction | ].
  destruct (eq_dec x x') as [EQ | NE]; [lia | ].
  destruct IN as [EQ | IN]; [contradiction NE; symmetry; exact EQ | ].
  pose proof (IH IN). lia.
Qed.

#[universes(polymorphic=yes)]
Lemma index_of_in_seq@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (x : A) (xs : list A)
  (IN : x ∈ xs)
  : index_of x xs ∈ seq 0 (length xs).
Proof.
  rewrite in_seq. pose proof (index_of_lt x xs IN). lia.
Qed.

#[universes(polymorphic=yes)]
Lemma index_of_inj@{u} {A : Type@{u}} `{EQ_DEC : hasEqDec@{u} A} (x : A) (y : A) (xs : list A) (default : A)
  (IN_X : x ∈ xs)
  (IN_Y : y ∈ xs)
  (EQ : index_of x xs = index_of y xs)
  : x = y.
Proof.
  pose proof (lookup_index_of x xs default IN_X) as Hx.
  pose proof (lookup_index_of y xs default IN_Y) as Hy.
  rewrite EQ in Hx. congruence.
Qed.

#[universes(polymorphic=yes)]
Lemma lookup_in@{u} {A : Type@{u}} (default : A) (n : nat) (xs : list A)
  (LT : n < length xs)
  : lookup default n xs ∈ xs.
Proof.
  unfold lookup. eapply nth_In. exact LT.
Qed.

#[universes(polymorphic=yes)]
Definition product@{u v} {A : Type@{u}} {B : Type@{v}} (xs : list A) (ys : list B) : list (A * B) :=
  xs >>= fun x => ys >>= fun y => pure (x, y).

#[universes(polymorphic=yes)]
Lemma product_sound@{u v} {A : Type@{u}} {B : Type@{v}} (xs : list A) (ys : list B) x y
  (IN : (x, y) ∈ product xs ys)
  : x ∈ xs /\ y ∈ ys.
Proof.
  unfold product in IN. cbn in IN. rewrite in_concat in IN.
  destruct IN as (z & IN & IN_PAIR). rewrite L.in_map_iff in IN.
  destruct IN as (? & EQ & IN); subst z. rewrite in_concat in IN_PAIR.
  destruct IN_PAIR as (z & IN_PAIR & IN'). rewrite L.in_map_iff in IN_PAIR.
  destruct IN_PAIR as (? & EQ & IN''); subst z. destruct IN' as [EQ | []].
  inv EQ. split; [exact IN | exact IN''].
Qed.

#[universes(polymorphic=yes)]
Lemma product_complete@{u v} {A : Type@{u}} {B : Type@{v}} (xs : list A) (ys : list B) x y
  (IN_X : x ∈ xs)
  (IN_Y : y ∈ ys)
  : (x, y) ∈ product xs ys.
Proof.
  unfold product. cbn. rewrite in_concat. exists (concat (map (fun y0 : B => [(x, y0)]) ys)). split.
  - rewrite L.in_map_iff. exists x. split; [reflexivity | exact IN_X].
  - rewrite in_concat. exists [(x, y)]. split.
    + rewrite L.in_map_iff. exists y. split; [reflexivity | exact IN_Y].
    + left. reflexivity.
Qed.

Lemma NoDup_map_injective_on {A : Type} {B : Type} (f : A -> B) (xs : list A)
  (INJ : forall x, forall y, x ∈ xs -> y ∈ xs -> f x = f y -> x = y)
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

Lemma forallb_false_exists {A : Type} (p : A -> bool) (xs : list A)
  (FORALL : forallb p xs = false)
  : exists x, x ∈ xs /\ p x = false.
Proof.
  induction xs as [ | x xs IH]; simpl in FORALL; [inv FORALL | ].
  rewrite andb_false_iff in FORALL. destruct FORALL as [PX | FORALL].
  - exists x. split; [left; reflexivity | exact PX].
  - pose proof (IH FORALL) as (y & IN & PY). exists y. split; [right; exact IN | exact PY].
Qed.

Lemma find_some_exists {A : Type} (p : A -> bool) (xs : list A) (x : A)
  (IN : x ∈ xs)
  (PX : p x = true)
  : exists y, find p xs = Some y.
Proof.
  induction xs as [ | x0 xs IH]; simpl in IN |- *; [contradiction | ].
  destruct IN as [EQ | IN].
  - subst x0. rewrite PX. exists x. reflexivity.
  - destruct (p x0) eqn: PX0; [exists x0; reflexivity | ].
    eapply IH; eauto.
Qed.

Lemma NoDup_exists_injective_length {A : Type} {B : Type} `{B_hasEqDec : hasEqDec B} (xs : list A) (ys : list B) (R : A -> B -> Prop)
  (NO_DUP : NoDup xs)
  (TOTAL : forall x, x ∈ xs -> exists y, y ∈ ys /\ R x y)
  (INJ : forall x1, forall x2, forall y, x1 ∈ xs -> x2 ∈ xs -> R x1 y -> R x2 y -> x1 = x2)
  : length xs <= length ys.
Proof.
  revert ys TOTAL INJ.
  induction NO_DUP as [ | x xs NOT_IN NO_DUP IH]; intros ys TOTAL INJ; simpl; [lia | ].
  pose proof (TOTAL x (or_introl eq_refl)) as (y & IN_Y & R_XY).
  enough (LE : length xs <= length (remove eq_dec y ys)).
  { pose proof (remove_length_lt y ys IN_Y). lia. }
  eapply IH.
  - intros x' IN_XS.
    pose proof (TOTAL x' (or_intror IN_XS)) as (y' & IN_Y' & R_XY').
    exists y'. split; [ | exact R_XY'].
    rewrite L.in_remove_iff. split; [exact IN_Y' | ].
    intros EQ. subst y'.
    assert (x' = x) as EQ.
    { eapply INJ; [right; exact IN_XS | left; reflexivity | exact R_XY' | exact R_XY]. }
    subst x'. contradiction.
  - intros x1 x2 y0 IN1 IN2 R1 R2.
    eapply INJ; [right; exact IN1 | right; exact IN2 | exact R1 | exact R2].
Qed.

Inductive relation_star {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
  | relation_star_refl x
    : relation_star R x x
  | relation_star_step x y z
    (STEP : R x y)
    (REST : relation_star R y z)
    : relation_star R x z.

Lemma relation_star_monotone {A : Type} (R : A -> A -> Prop) (R' : A -> A -> Prop) (x : A) (y : A)
  (INCL : forall x, forall y, R x y -> R' x y)
  (STEPS : relation_star R x y)
  : relation_star R' x y.
Proof.
  induction STEPS as [x | x y z STEP REST IH].
  - constructor.
  - econstructor; [eapply INCL; exact STEP | exact IH].
Qed.
