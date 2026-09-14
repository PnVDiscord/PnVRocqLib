Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Prelude.X.
Require Export PnV.Math.ThN.
Require Export PnV.Math.OrderTheory.
Require Export PnV.Data.HsOrd.
Require Import PnV.Data.BalancedTree.

#[local] Infix "=~=" := is_similar_to : type_scope.
#[local] Infix "\in" := E.In.
#[local] Infix "∈" := L.In.

#[local] Hint Resolve S_lt_S_intro : core.

#[universes(polymorphic=yes)]
Definition fin_ensemble@{u | } (A : Type@{u}) : Type@{u} :=
  list A.

#[global] Typeclasses Opaque fin_ensemble.

#[global]
Instance fin_ensemble_isMonad : isMonad fin_ensemble :=
  { pure {A} (x : A) := [x]
  ; bind {A} {B} (xs : list A) (k : A -> list B) := flat_map k xs
  }.

#[global]
Instance fin_ensemble_is_similar_to_ensemble {A : Type} {A' : Type} (Sim_A_A' : Similarity A A') : Similarity (fin_ensemble A) (ensemble A') :=
  fun X => fun X' => forall x : A, forall x' : A', forall x_sim_x' : x =~= x', x ∈ X <-> x' \in X'.

#[global, refine]
Instance fin_ensemble_isSetoid {A : Type} (A_isSetoid : isSetoid A) : isSetoid (fin_ensemble A) :=
  { eqProp (lhs : list A) (rhs : list A) := ⟪ SUBSET : forall a : A, a ∈ lhs -> (exists a' : A, a == a' /\ a' ∈ rhs) ⟫ /\ ⟪ SUPSET : forall a : A, a ∈ rhs -> (exists a' : A, a == a' /\ a' ∈ lhs) ⟫ }.
Proof.
  split; ii; split; ii; des.
  - exists a; eauto with *.
  - exists a; eauto with *.
  - find* (a' & Ha' & H_in) by SUPSET. exists a'; eauto with *.
  - find* (a' & Ha' & H_in) by SUBSET. exists a'; eauto with *.
  - find* (a' & Ha' & H_in) by SUBSET0. find* (a'' & Ha'' & IN) by SUBSET. exists a''; split; auto. etransitivity; eauto.
  - find* (a' & Ha' & H_in) by SUPSET. find* (a'' & Ha'' & IN) by SUPSET0. exists a''; split; auto. etransitivity; eauto.
Defined.

#[global]
Instance fin_ensemble_isSetoid1 : isSetoid1 fin_ensemble :=
  @fin_ensemble_isSetoid.

#[global]
Instance fin_ensemble_MonadLaws@{u}
  : MonadLaws fin_ensemble@{u} (SETOID1 := fin_ensemble_isSetoid1) (MONAD := fin_ensemble_isMonad).
Proof.
  assert (SIMP : forall A : Type@{u}, forall X : fin_ensemble@{u} A, forall X' : fin_ensemble@{u} A, X == X' <-> (forall z : A, z ∈ X <-> z ∈ X')).
  { ii. split; intros H_EQ; simpl in *.
    - des; firstorder congruence.
    - unnw; split; firstorder congruence.
  }
  split; ii; rewrite SIMP.
  - intros z. simpl. do 2 rewrite in_flat_map. rewrite SIMP in m_EQ. firstorder.
  - intros z. simpl. do 2 rewrite in_flat_map.
    assert (H_EQ : forall x : A, forall y : B, y ∈ k1 x <-> y ∈ k2 x).
    { intros x. rewrite <- SIMP. eapply k_EQ. }
    firstorder.
  - intros z. simpl. do 2 rewrite in_flat_map. split.
    + intros (x & Hx & Hz). rewrite in_flat_map in Hz.
      destruct Hz as (y & Hy & Hz). exists y; split; auto.
      rewrite in_flat_map. exists x; auto.
    + intros (y & Hy & Hz). rewrite in_flat_map in Hy.
      destruct Hy as (x & Hx & Hy). exists x; split; auto.
      rewrite in_flat_map. exists y; auto.
  - intros z. simpl. now rewrite app_nil_r.
  - intros z. simpl. rewrite in_flat_map. firstorder congruence.
Qed.

Module FSet.

#[universes(template), projections(primitive)]
Record t {A : Type} {isSorted : list A -> bool} : Type :=
  { tree : BalancedTree.t A
  ; data_isSorted : isSorted (BalancedTree.data tree) = true
  } as X.

#[global] Arguments t : clear implicits.

Definition data {A : Type} {isSorted : list A -> bool} (X : t A isSorted) : list A :=
  BalancedTree.data X.(tree).

#[refine]
Definition mk {A : Type} {isSorted : list A -> bool} (xs : list A) (SORTED : isSorted xs = true) : FSet.t A isSorted :=
  {| tree := BalancedTree.of_list xs; data_isSorted := _ |}.
Proof.
  rewrite BalancedTree.data_of_list. exact SORTED.
Defined.

Lemma data_mk {A : Type} {isSorted : list A -> bool} (xs : list A)
  (SORTED : isSorted xs = true)
  : data (mk xs SORTED) = xs.
Proof.
  unfold data, mk. cbn. eapply BalancedTree.data_of_list.
Qed.

End FSet.

#[global] Abbreviation fset A := (FSet.t A (isSorted compare)).

Section ORDERED_FSET.

Context {A : Type} {PROSET : isProset A} {ORD : hsOrd A}.

#[global]
Instance fset_isSetoid : isSetoid (fset A) :=
  { eqProp (X : fset A) (X' : fset A) := @eqProp (list A) (L.list_isSetoid PROSET.(Proset_isSetoid)) (FSet.data X) (FSet.data X')
  ; eqProp_Equivalence := relation_on_image_liftsEquivalence (L.list_isSetoid PROSET.(Proset_isSetoid)).(eqProp_Equivalence) (@FSet.data A (isSorted compare))
  }.

Theorem fset_eq_spec (X : fset A) (X' : fset A)
  : X == X' <-> (forall x : A, InA eqProp x (FSet.data X) <-> InA eqProp x (FSet.data X')).
Proof.
  eapply sorted_eqProp_iff; eapply FSet.data_isSorted.
Qed.

#[global, refine]
Instance fset_isProset : isProset (fset A) :=
  { leProp (X : fset A) (X' : fset A) := lex_le (FSet.data X) (FSet.data X')
  ; Proset_isSetoid := fset_isSetoid
  }.
Proof.
  - split.
    + intros X. eapply lex_le_PreOrder.
    + intros X Y Z XY YZ. eapply lex_le_PreOrder; eauto.
  - intros X Y. change (@eqProp (list A) (L.list_isSetoid PROSET.(Proset_isSetoid)) (FSet.data X) (FSet.data Y) <-> (lex_le (FSet.data X) (FSet.data Y) /\ lex_le (FSet.data Y) (FSet.data X))).
    rewrite <- lex_eq_iff. eapply lex_le_PartialOrder.
Defined.

#[global, refine]
Instance fset_hsOrd : hsOrd (fset A) (PROSET := fset_isProset) :=
  { compare (X : fset A) (X' : fset A) := lex_compare (FSet.data X) (FSet.data X') }.
Proof.
  - intros X Y XY. exact (@compare_Lt (list A) (@list_lexicographical_order A PROSET ORD) (@list_hsOrd A PROSET ORD) (FSet.data X) (FSet.data Y) XY).
  - intros X Y XY. exact (@compare_Eq (list A) (@list_lexicographical_order A PROSET ORD) (@list_hsOrd A PROSET ORD) (FSet.data X) (FSet.data Y) XY).
  - intros X Y XY. exact (@compare_Gt (list A) (@list_lexicographical_order A PROSET ORD) (@list_hsOrd A PROSET ORD) (FSet.data X) (FSet.data Y) XY).
Defined.

End ORDERED_FSET.

Module FS.

Section BASICS.

Context {A : Type} {PROSET : isProset A} {ORD : hsOrd A}.

Section fold.

Context {B : Type} (f : B -> A -> B).

Definition fold (X : fset A) : B -> B :=
  BalancedTree.fold f X.(FSet.tree).

Lemma fold_spec (X : fset A) (acc : B)
  : fold X acc = L.fold_left f (FSet.data X) acc.
Proof.
  eapply BalancedTree.fold_spec.
Qed.

End fold.

Definition is_empty (X : fset A) : bool :=
  match BalancedTree.root X.(FSet.tree) with
  | BalancedTree.Leaf => true
  | BalancedTree.Node _ _ _ _ => false
  end.

Lemma is_empty_spec (X : fset A)
  : is_empty X = true <-> FSet.data X = [].
Proof.
  unfold is_empty, FSet.data. rewrite BalancedTree.data_elements.
  destruct (BalancedTree.root _); cbn [BalancedTree.elements].
  - tauto.
  - split; [ss | intros EQ].
    apply app_eq_nil in EQ. des; ss.
Qed.

Definition In (x : A) (X : fset A) : Prop :=
  InA eqProp x (FSet.data X).

Theorem eq_spec (X : fset A) (Y : fset A)
  : X == Y <-> (forall x, In x X <-> In x Y).
Proof.
  eapply fset_eq_spec.
Qed.

Definition isSubsetOf (X : fset A) (Y : fset A) : Prop :=
  forall x, In x X -> In x Y.

Definition empty : fset A :=
  FSet.mk [] eq_refl.

Theorem in_empty_iff (x : A)
  : In x empty <-> False.
Proof.
  unfold In, empty. rewrite FSet.data_mk. eapply InA_nil.
Qed.

Lemma sorted_data (X : fset A)
  : isSorted compare (map (fun x : A => x) (FSet.data X)) = true.
Proof.
  rewrite map_id. exact X.(FSet.data_isSorted).
Qed.

#[local] Hint Resolve sorted_data : core.

Definition mem (x : A) (X : fset A) : bool :=
  match BalancedTree.lookup (compare x) X.(FSet.tree) with
  | Some _ => true
  | None => false
  end.

Lemma lookup_data (x : A) (X : fset A)
  : BalancedTree.lookup (compare x) X.(FSet.tree) = OrderedList.lookup (fun y : A => y) x (FSet.data X).
Proof.
  eapply BalancedTree.lookup_data. eapply sorted_data.
Qed.

Theorem mem_spec (x : A) (X : fset A)
  : forall b : bool, mem x X = b <-> (if b then In x X else ~ In x X).
Proof.
  assert (SPEC : mem x X = true <-> In x X).
  { unfold mem. rewrite lookup_data. unfold In. rewrite InA_alt.
    destruct (OrderedList.lookup _ _ _) as [y | ] eqn: OBS.
    - rewrite OrderedList.lookup_spec in OBS by apply sorted_data. firstorder.
    - split; [ss | intros (y & EQ & IN)].
      assert (HIT : OrderedList.lookup (fun y : A => y) x (FSet.data X) = Some y).
      { rewrite OrderedList.lookup_spec by apply sorted_data. auto. }
      congruence.
  }
  intros [ | ]; [exact SPEC | split].
  - intros EQ IN. apply SPEC in IN. congruence.
  - intros NOT_IN. destruct (mem x X); auto.
    exfalso. apply NOT_IN. apply SPEC. reflexivity.
Qed.

Lemma in_insert_iff (x : A) (xs : list A) (y : A)
  : InA eqProp y (OrderedList.insert (fun z : A => z) x xs) <-> (y == x \/ InA eqProp y xs).
Proof.
  induction xs as [ | z xs IH]; cbn [OrderedList.insert].
  - rewrite InA_cons, InA_nil. tauto.
  - destruct (compare x z) eqn: OBS.
    + rewrite !InA_cons.
      enough (EQ : y == x <-> y == z) by tauto.
      rewrite compare_Eq_iff in OBS. split; intros EQ; etransitivity; eauto with *.
    + rewrite !InA_cons. tauto.
    + rewrite !InA_cons, IH. tauto.
Qed.

#[refine]
Definition add (x : A) (X : fset A) : fset A :=
  {| FSet.tree := BalancedTree.add compare x X.(FSet.tree); FSet.data_isSorted := _ |}.
Proof.
  rewrite BalancedTree.data_add with (key := fun y : A => y) by eapply sorted_data.
  find* SORTED by (OrderedList.insert_sorted (fun y : A => y) x (FSet.data X) (sorted_data X)).
  now rewrite map_id in SORTED.
Defined.

Lemma data_add (x : A) (X : fset A)
  : FSet.data (add x X) = OrderedList.insert (fun y : A => y) x (FSet.data X).
Proof.
  unfold add, FSet.data. cbn [FSet.tree].
  now rewrite BalancedTree.data_add with (key := fun y : A => y) by eapply sorted_data.
Qed.

Theorem in_add_iff (x : A) (X : fset A) (y : A)
  : In y (add x X) <-> y == x \/ In y X.
Proof.
  unfold In. rewrite data_add. eapply in_insert_iff.
Qed.

Theorem length_add (x : A) (X : fset A)
  (FRESH : ~ In x X)
  : length (FSet.data (add x X)) = S (length (FSet.data X)).
Proof.
  rewrite data_add. eapply OrderedList.length_insert.
  destruct (OrderedList.lookup _ _ _) as [y | ] eqn: OBS; auto.
  contradiction FRESH. unfold In. rewrite InA_alt.
  rewrite OrderedList.lookup_spec in OBS by eapply sorted_data. firstorder.
Qed.

Definition fromList (xs : list A) : fset A :=
  L.fold_left (fun X => fun x => add x X) (L.rev_append xs []) empty.

Lemma fromList_spec (xs : list A)
  : fromList xs = L.fold_right add empty xs.
Proof.
  unfold fromList. rewrite <- L.fold_left_rev_right, <- L.rev_alt, L.rev_involutive. reflexivity.
Qed.

Lemma fromList_cons (x : A) (xs : list A)
  : fromList (x :: xs) = add x (fromList xs).
Proof.
  rewrite !fromList_spec. reflexivity.
Qed.

Theorem in_fromList_iff (xs : list A) (x : A)
  : In x (fromList xs) <-> InA eqProp x xs.
Proof.
  rewrite fromList_spec. induction xs as [ | y ys IH]; cbn [fold_right].
  - rewrite in_empty_iff, InA_nil. reflexivity.
  - rewrite in_add_iff, IH, InA_cons. reflexivity.
Qed.

Definition union (X : fset A) : fset A -> fset A :=
  L.fold_left (fun Y => fun x => add x Y) (L.rev_append (FSet.data X) []).

Lemma union_spec (X : fset A) (Y : fset A)
  : union X Y = L.fold_right add Y (FSet.data X).
Proof.
  unfold union. now rewrite <- L.fold_left_rev_right, <- L.rev_alt, L.rev_involutive.
Qed.

Theorem in_union_iff (X : fset A) (Y : fset A) (x : A)
  : In x (union X Y) <-> In x X \/ In x Y.
Proof.
  rewrite union_spec. unfold In at 2. generalize (FSet.data X) as xs. clear X.
  induction xs as [ | y ys IH]; cbn [fold_right].
  - rewrite InA_nil. tauto.
  - rewrite in_add_iff, IH, InA_cons. tauto.
Qed.

#[refine]
Definition remove (x : A) (X : fset A) : fset A :=
  {| FSet.tree := BalancedTree.remove (compare x) X.(FSet.tree); FSet.data_isSorted := _ |}.
Proof.
  rewrite BalancedTree.data_remove with (key := fun y : A => y) by eapply sorted_data.
  find* SORTED by (OrderedList.remove_sorted (fun y : A => y) x (FSet.data X) (sorted_data X)).
  now rewrite map_id in SORTED.
Defined.

Lemma data_remove (x : A) (X : fset A)
  : FSet.data (remove x X) = OrderedList.remove (fun y : A => y) x (FSet.data X).
Proof.
  unfold remove, FSet.data. cbn [FSet.tree].
  now rewrite BalancedTree.data_remove with (key := fun y : A => y) by eapply sorted_data.
Qed.

Lemma In_compat (x : A) (y : A) (X : fset A) (Y : fset A)
  (EQ_x : x == y)
  (EQ_X : X == Y)
  : In x X <-> In y Y.
Proof.
  rewrite eq_spec in EQ_X. rewrite EQ_X. unfold In.
  eapply InA_compat; [eapply eqProp_Equivalence | exact EQ_x | reflexivity].
Qed.

#[global]
Instance In_eqPropCompatible2
  : eqPropCompatible2 In.
Proof.
  ii; eapply In_compat; eauto.
Qed.

#[global]
Instance add_eqPropCompatible2
  : eqPropCompatible2 add.
Proof.
  intros x y X Y EQ_x EQ_X. eapply eq_spec. intros z.
  rewrite eq_spec in EQ_X. rewrite !in_add_iff, EQ_X.
  assert (EQ : z == x <-> z == y).
  { split; ii; etransitivity; eauto with *. }
  tauto.
Qed.

#[global]
Instance union_eqPropCompatible2
  : eqPropCompatible2 union.
Proof.
  intros X X' Y Y' EQ_X EQ_Y. eapply eq_spec. intros z.
  rewrite eq_spec in EQ_X, EQ_Y. rewrite !in_union_iff, EQ_X, EQ_Y.
  reflexivity.
Qed.

Lemma mem_remove_same (x : A) (X : fset A)
  : mem x (remove x X) = false.
Proof.
  unfold mem. rewrite lookup_data, data_remove.
  now rewrite OrderedList.lookup_remove_eq by eapply sorted_data.
Qed.

Lemma mem_remove_other (x : A) (z : A) (X : fset A)
  (NE : ~ z == x)
  : mem z (remove x X) = mem z X.
Proof.
  unfold mem. rewrite !lookup_data, data_remove.
  rewrite OrderedList.lookup_remove_ne by (eauto; eapply sorted_data). reflexivity.
Qed.

#[global]
Instance mem_eqPropCompatible2
  : @eqPropCompatible2 A (fset A) bool PROSET.(Proset_isSetoid) fset_isSetoid mkSetoid_from_eq mem.
Proof.
  intros x y X Y EQ_x EQ_X. change (mem x X = mem y Y).
  destruct (mem y Y) eqn: OBS.
  - apply mem_spec. apply (proj2 (In_compat x y X Y EQ_x EQ_X)). now apply mem_spec in OBS.
  - apply mem_spec. intros IN. apply mem_spec in OBS. apply OBS.
    apply (proj1 (In_compat x y X Y EQ_x EQ_X)). exact IN.
Qed.

Theorem in_remove_iff (x : A) (X : fset A) (z : A)
  : In z (remove x X) <-> (In z X /\ ~ z == x).
Proof.
  destruct (compare z x) eqn: OBS.
  - apply compare_Eq_iff in OBS.
    rewrite In_compat with (y := x) (Y := remove x X) by (try exact OBS; reflexivity).
    assert (NOT_IN : ~ In x (remove x X)).
    { apply (proj1 (mem_spec x (remove x X) false)). apply mem_remove_same. }
    tauto.
  - assert (NE : ~ z == x).
    { intros EQ. rewrite <- compare_Eq_iff in EQ. congruence. }
    rewrite <- mem_spec with (x := z) (X := remove x X) (b := true).
    rewrite mem_remove_other by exact NE.
    rewrite mem_spec. tauto.
  - assert (NE : ~ z == x).
    { intros EQ. rewrite <- compare_Eq_iff in EQ. congruence. }
    rewrite <- mem_spec with (x := z) (X := remove x X) (b := true).
    rewrite mem_remove_other by exact NE.
    rewrite mem_spec. tauto.
Qed.

#[global]
Instance remove_eqPropCompatible2
  : eqPropCompatible2 remove.
Proof.
  intros x y X Y EQ_x EQ_X. apply eq_spec. intros z.
  rewrite eq_spec in EQ_X. rewrite !in_remove_iff, EQ_X.
  assert (EQ : z == x <-> z == y) by (split; ii; etransitivity; eauto with *).
  tauto.
Qed.

#[global]
Instance isSubsetOf_eqPropCompatible2
  : eqPropCompatible2 isSubsetOf.
Proof.
  intros X X' Y Y' EQ_X EQ_Y. unfold isSubsetOf.
  rewrite eq_spec in EQ_X, EQ_Y.
  setoid_rewrite EQ_X. setoid_rewrite EQ_Y. reflexivity.
Qed.

Lemma isSorted_filter (p : A -> bool) (xs : list A)
  (SORTED : isSorted compare xs = true)
  : isSorted compare (L.filter p xs) = true.
Proof.
  revert SORTED. induction xs as [ | x xs IH]; i; cbn; auto.
  rewrite isSorted_cons_iff in SORTED. des.
  destruct (p x); auto. rewrite isSorted_cons_iff. split; eauto.
  i. rewrite L.filter_In in H. des; eauto.
Qed.

Definition filter (p : A -> bool) (X : fset A) : fset A :=
  FSet.mk (L.filter p (FSet.data X)) (isSorted_filter p (FSet.data X) X.(FSet.data_isSorted)).

Theorem in_filter_iff (p : A -> bool) (X : fset A)
  (COMPAT : forall x, forall y, x == y -> p x = p y)
  (z : A)
  : In z (filter p X) <-> In z X /\ p z = true.
Proof.
  unfold In, filter. rewrite FSet.data_mk, !InA_alt.
  setoid_rewrite L.filter_In. split.
  - intros (y & EQ & IN & P). split; eauto.
  - intros [(y & EQ & IN) P]. exists y. split; auto.
    split; auto. rewrite <- COMPAT with (x := z) by exact EQ. exact P.
Qed.

#[global]
Instance filter_eqPropCompatible1 (p : A -> bool)
  (COMPAT : Proper (eqProp ==> eq) p)
  : eqPropCompatible1 (filter p).
Proof.
  intros X Y EQ. apply eq_spec. intros z.
  rewrite !in_filter_iff by exact COMPAT.
  rewrite eq_spec in EQ. rewrite EQ. reflexivity.
Qed.

Lemma in_fold_left_add {B : Type} (f : B -> A) (xs : list B) (X : fset A) (y : A)
  : In y (L.fold_left (fun Y => fun x => add (f x) Y) xs X) <-> In y X \/ (exists x, L.In x xs /\ y == f x).
Proof.
  revert X. induction xs as [ | x xs IH]; i; cbn [L.fold_left].
  - cbn. firstorder.
  - rewrite IH, in_add_iff. split.
    + intros [[EQ | IN] | (z & IN & EQ)]; eauto.
      * right. exists x. split; auto. now left.
      * right. exists z. split; auto. now right.
    + intros [IN | (z & [EQ | IN] & EQ')]; subst; eauto.
Qed.

End BASICS.

Section MAP_and_BIND.

Context {A : Type} {PROSET_A : isProset A} {ORD_A : hsOrd A}.
Context {B : Type} {PROSET_B : isProset B} {ORD_B : hsOrd B}.

Definition map (f : A -> B) (X : fset A) : fset B :=
  fold (fun Y => fun x => add (f x) Y) X empty.

Lemma in_map_raw_iff (f : A -> B) (X : fset A) (y : B)
  : In y (map f X) <-> (exists x, L.In x (FSet.data X) /\ y == f x).
Proof.
  unfold map. rewrite fold_spec, in_fold_left_add, in_empty_iff. tauto.
Qed.

Theorem in_map_iff (f : A -> B) (X : fset A)
  (COMPAT : forall x, forall y, x == y -> f x == f y)
  (z : B)
  : In z (map f X) <-> (exists x, In x X /\ z == f x).
Proof.
  rewrite in_map_raw_iff. split.
  - intros (x & IN & EQ). exists x. split; auto.
    apply In_InA; [apply eqProp_Equivalence | exact IN].
  - intros (x & IN & EQ). unfold In in IN. rewrite InA_alt in IN.
    find* (y & EQ' & IN') by IN. exists y. split; auto.
    transitivity (f x); auto.
Qed.

Definition bind (X : fset A) (k : A -> fset B) : fset B :=
  L.fold_left (fun Y => fun x => union (k x) Y) (L.rev_append (FSet.data X) []) empty.

Lemma bind_spec (X : fset A) (k : A -> fset B)
  : bind X k = L.fold_right (fun x => union (k x)) empty (FSet.data X).
Proof.
  unfold bind. rewrite <- L.fold_left_rev_right, <- L.rev_alt, L.rev_involutive. reflexivity.
Qed.

Lemma in_bind_raw_iff (X : fset A) (k : A -> fset B) (z : B)
  : In z (bind X k) <-> (exists x, L.In x (FSet.data X) /\ In z (k x)).
Proof.
  rewrite bind_spec. generalize (FSet.data X) as xs. clear X.
  induction xs as [ | x xs IH]; cbn [fold_right].
  - rewrite in_empty_iff. cbn. firstorder.
  - rewrite in_union_iff, IH. split.
    + intros [IN | (y & IN & IN')].
      * exists x. split; auto. now left.
      * exists y. split; auto. now right.
    + intros (y & [EQ | IN] & IN'); subst; eauto.
Qed.

Theorem in_bind_iff (X : fset A) (k : A -> fset B)
  (COMPAT : forall x, forall y, x == y -> k x == k y)
  (z : B)
  : In z (bind X k) <-> (exists x, In x X /\ In z (k x)).
Proof.
  rewrite in_bind_raw_iff. split.
  - intros (x & IN & IN'). exists x. split; auto. apply In_InA; [apply eqProp_Equivalence | exact IN].
  - intros (x & IN & IN'). unfold In in IN. rewrite InA_alt in IN.
    find* (y & EQ & IN_y) by IN. exists y. split; auto.
    apply (proj1 (eq_spec (k x) (k y)) (COMPAT x y EQ) z). exact IN'.
Qed.

#[global]
Instance map_eqPropCompatible1 (f : A -> B)
  (COMPAT : forall x, forall y, x == y -> f x == f y)
  : eqPropCompatible1 (map f).
Proof.
  intros X Y EQ. apply eq_spec. intros z. rewrite !in_map_iff by exact COMPAT.
  rewrite eq_spec in EQ. setoid_rewrite EQ. reflexivity.
Qed.

#[global]
Instance bind_eqPropCompatible1 (k : A -> fset B)
  (COMPAT : forall x, forall y, x == y -> k x == k y)
  : eqPropCompatible1 (fun X => bind X k).
Proof.
  intros X Y EQ. apply eq_spec. intros z. rewrite !in_bind_iff by exact COMPAT.
  rewrite eq_spec in EQ. setoid_rewrite EQ. reflexivity.
Qed.

#[global]
Instance map_compat
  : Proper ((eqProp ==> eqProp) ==> eqProp ==> eqProp) map.
Proof.
  intros f g EQ_fg X Y EQ_X. apply eq_spec. intros z.
  assert (COMPAT_f : forall x, forall y, x == y -> f x == f y).
  { intros x y EQ. transitivity (g y); [apply EQ_fg; exact EQ | symmetry; apply EQ_fg; reflexivity]. }
  assert (COMPAT_g : forall x, forall y, x == y -> g x == g y).
  { intros x y EQ. transitivity (f x); [symmetry; apply EQ_fg; reflexivity | apply EQ_fg; exact EQ]. }
  rewrite !in_map_iff by assumption. split.
  - intros (x & IN & EQ). exists x. split.
    + apply (proj1 (eq_spec X Y) EQ_X). exact IN.
    + transitivity (f x); [exact EQ | apply EQ_fg; reflexivity].
  - intros (x & IN & EQ). exists x. split.
    + apply (proj1 (eq_spec X Y) EQ_X). exact IN.
    + transitivity (g x); [exact EQ | symmetry; apply EQ_fg; reflexivity].
Qed.

#[global]
Instance bind_compat
  : Proper (eqProp ==> (eqProp ==> eqProp) ==> eqProp) bind.
Proof.
  intros X Y EQ_X k k' EQ_k. apply eq_spec. intros z.
  rewrite !in_bind_raw_iff. split.
  - intros (x & IN & IN_z).
    assert (IN_Y : In x Y).
    { apply (proj1 (eq_spec X Y) EQ_X). apply In_InA; [apply eqProp_Equivalence | exact IN]. }
    unfold In in IN_Y. rewrite InA_alt in IN_Y. find* (y & EQ & IN_y) by IN_Y.
    exists y. split; auto. apply (proj1 (eq_spec (k x) (k' y)) (EQ_k x y EQ) z). exact IN_z.
  - intros (y & IN & IN_z).
    assert (IN_X : In y X).
    { apply (proj1 (eq_spec X Y) EQ_X). apply In_InA; [apply eqProp_Equivalence | exact IN]. }
    unfold In in IN_X. rewrite InA_alt in IN_X. find* (x & EQ & IN_x) by IN_X.
    exists x. split; auto. apply (proj1 (eq_spec (k x) (k' y)) (EQ_k x y (symmetry EQ)) z). exact IN_z.
Qed.

End MAP_and_BIND.

Section PRODUCT.

Context {A : Type} {PROSET_A : isProset A} {ORD_A : hsOrd A}.
Context {B : Type} {PROSET_B : isProset B} {ORD_B : hsOrd B}.
#[local] Existing Instances pair_isProset pair_hsOrd.

Definition product (X : fset A) (Y : fset B) : fset (A * B) :=
  fromList (L.list_prod (FSet.data X) (FSet.data Y)).

Theorem product_iff (X : fset A) (Y : fset B) (x : A) (y : B)
  : In (x, y) (product X Y) <-> In x X /\ In y Y.
Proof.
  unfold product. rewrite in_fromList_iff. unfold In. rewrite !InA_alt.
  split.
  - intros ([x' y'] & [EQ_x EQ_y] & IN).
    rewrite L.in_prod_iff in IN. des. split; eauto.
  - intros [(x' & EQ_x & IN_x) (y' & EQ_y & IN_y)].
    exists (x', y'). split; [split; auto | apply L.in_prod_iff; auto].
Qed.

#[global]
Instance product_eqPropCompatible2
  : eqPropCompatible2 product.
Proof.
  intros X X' Y Y' EQ_X EQ_Y. apply eq_spec. intros [x y].
  rewrite eq_spec in EQ_X. rewrite eq_spec in EQ_Y. rewrite !product_iff, EQ_X, EQ_Y.
  reflexivity.
Qed.

End PRODUCT.

Section UNIONS.

Context {A : Type} {PROSET : isProset A} {ORD : hsOrd A}.

Definition unions (Xs : fset (fset A)) : fset A :=
  bind Xs (fun X => X).

Theorem in_unions_iff (Xs : fset (fset A)) (x : A)
  : In x (unions Xs) <-> (exists X, In X Xs /\ In x X).
Proof.
  unfold unions. apply in_bind_iff. auto.
Qed.

#[global]
Instance unions_eqPropCompatible1
  : eqPropCompatible1 unions.
Proof.
  apply bind_eqPropCompatible1. auto.
Qed.

Definition Similarity_fset_ensemble {B : Type} (Sim : Similarity A B) : Similarity (fset A) (ensemble B) :=
  fun X => fun Y => forall x, forall y, x =~= y -> (In x X <-> E.In y Y).

#[global]
Instance fset_corresponds_to_ensemble : Similarity (fset A) (ensemble A) :=
  Similarity_fset_ensemble eq.

Theorem fset_corresponds_to_ensemble_iff (X : fset A) (Y : ensemble A)
  : X =~= Y <-> (forall z, In z X <-> E.In z Y).
Proof.
  unfold is_similar_to, fset_corresponds_to_ensemble, Similarity_fset_ensemble. firstorder congruence.
Qed.

End UNIONS.

Section DISCRETE.

Context {A : Type} {POSET : isPoset A} {ORD : HsOrd A}.

Lemma In_eq_iff (x : A) (X : fset A)
  : In x X <-> L.In x (FSet.data X).
Proof.
  apply InA_eqProp_iff.
Qed.

Lemma in_empty_eq_iff (x : A)
  : L.In x (FSet.data empty) <-> False.
Proof.
  rewrite <- In_eq_iff. apply in_empty_iff.
Qed.

Lemma in_add_eq_iff (x : A) (X : fset A) (y : A)
  : L.In y (FSet.data (add x X)) <-> x = y \/ L.In y (FSet.data X).
Proof.
  rewrite <- !In_eq_iff, in_add_iff, Poset_eqProp_spec. intuition congruence.
Qed.

Lemma mem_eq_spec (x : A) (X : fset A) (b : bool)
  : mem x X = b <-> (if b then L.In x (FSet.data X) else ~ L.In x (FSet.data X)).
Proof.
  rewrite mem_spec. destruct b; now rewrite In_eq_iff.
Qed.

Lemma in_fromList_eq_iff (xs : list A) (x : A)
  : L.In x (FSet.data (fromList xs)) <-> L.In x xs.
Proof.
  rewrite <- In_eq_iff, in_fromList_iff. apply InA_eqProp_iff.
Qed.

Lemma in_union_eq_iff (X : fset A) (Y : fset A) (x : A)
  : L.In x (FSet.data (union X Y)) <-> L.In x (FSet.data X) \/ L.In x (FSet.data Y).
Proof.
  rewrite <- !In_eq_iff. apply in_union_iff.
Qed.

End DISCRETE.

Section DISCRETE_MAP.

Context {A : Type} {POSET_A : isPoset A} {ORD_A : HsOrd A}.
Context {B : Type} {POSET_B : isPoset B} {ORD_B : HsOrd B}.

Lemma in_map_eq_iff (f : A -> B) (X : fset A) (y : B)
  : L.In y (FSet.data (map f X)) <-> (exists x, f x = y /\ L.In x (FSet.data X)).
Proof.
  rewrite <- In_eq_iff, in_map_raw_iff. setoid_rewrite Poset_eqProp_spec. firstorder congruence.
Qed.

Lemma product_eq_iff (X : fset A) (Y : fset B) (x : A) (y : B)
  : L.In (x, y) (FSet.data (product X Y)) <-> L.In x (FSet.data X) /\ L.In y (FSet.data Y).
Proof.
  rewrite <- InA_eqProp_iff with (x := (x, y)) (xs := FSet.data (product X Y)).
  change (In (x, y) (product X Y) <-> L.In x (FSet.data X) /\ L.In y (FSet.data Y)).
  rewrite product_iff, !In_eq_iff. reflexivity.
Qed.

End DISCRETE_MAP.

Section CARDINALITY.

Context {A : Type} {PROSET : isProset A} {ORD : hsOrd A}.

Lemma length_fromList (xs : list A)
  (NO_DUP : NoDupA eqProp xs)
  : length (FSet.data (fromList xs)) = length xs.
Proof.
  induction NO_DUP as [ | x xs NOT_IN NO_DUP IH].
  - unfold fromList, empty. cbn [L.fold_left L.rev_append]. rewrite FSet.data_mk. reflexivity.
  - rewrite fromList_cons. cbn [length].
    rewrite length_add; auto. rewrite in_fromList_iff. exact NOT_IN.
Qed.

Lemma NoDupA_data (X : fset A)
  : NoDupA eqProp (FSet.data X).
Proof.
  apply sorted_NoDupA. apply FSet.data_isSorted.
Qed.

#[global]
Instance cardinality_eqPropCompatible1
  : @eqPropCompatible1 (fset A) nat fset_isSetoid mkSetoid_from_eq (fun X : fset A => length (FSet.data X)).
Proof.
  intros X Y EQ. eapply eqlistA_length. apply list_eqProp_eqlistA. exact EQ.
Qed.

#[global]
Instance fromList_compat
  : Proper (equivlistA eqProp ==> eqProp) fromList.
Proof.
  intros xs ys EQ. apply eq_spec. intros z. rewrite !in_fromList_iff. apply EQ.
Qed.

End CARDINALITY.

Section POWERSET.

Context {A : Type} {PROSET : isProset A} {ORD : hsOrd A}.

#[local]
Lemma InA_map_fset {B : Type} (f : B -> fset A) (Y : fset A) (xs : list B)
  : InA eqProp Y (L.map f xs) <-> (exists x, L.In x xs /\ Y == f x).
Proof.
  rewrite InA_alt. split.
  - intros (Z & EQ & IN). rewrite L.in_map_iff in IN.
    find* (x & <- & IN') by IN. eauto.
  - intros (x & IN & EQ). exists (f x). split; eauto using L.in_map.
Qed.

Fixpoint powerset' (xs : list A) {struct xs} : list (fset A) :=
  match xs with
  | [] => [empty]
  | x :: xs' => let ps := powerset' xs' in ps ++ L.map (add x) ps
  end.

Definition powerset (X : fset A) : fset (fset A) :=
  fromList (powerset' (FSet.data X)).

Lemma in_powerset'_iff (xs : list A)
  : forall Y : fset A, InA eqProp Y (powerset' xs) <-> (forall z : A, In z Y -> InA eqProp z xs).
Proof.
  induction xs as [ | x xs IH]; intros Y.
  - cbn [powerset']. rewrite InA_cons, InA_nil. split.
    + intros [EQ | []] z IN. rewrite eq_spec in EQ.
      apply EQ in IN. rewrite in_empty_iff in IN. contradiction.
    + intros SUBSET. left. apply eq_spec. intros z.
      rewrite in_empty_iff. split; [intros IN | tauto].
      specialize (SUBSET z IN). now rewrite InA_nil in SUBSET.
  - cbn [powerset']. rewrite InA_app_iff, InA_map_fset. split.
    + intros [IN | (Z & IN & EQ)] z IN_z.
      * rewrite IH in IN. apply InA_cons_tl. eauto.
      * rewrite eq_spec in EQ. apply EQ in IN_z.
        rewrite in_add_iff in IN_z. rewrite InA_cons.
        find* [EQ_z | IN_z'] by IN_z; auto. right.
        eapply (proj1 (IH Z)); eauto. eapply In_InA; [apply eqProp_Equivalence | eauto].
    + intros SUBSET. destruct (mem x Y) eqn: OBS.
      * rewrite mem_spec in OBS.
        set (Z := remove x Y).
        assert (SUBSET_Z : forall z, In z Z -> InA eqProp z xs).
        { intros z IN. unfold Z in IN. rewrite in_remove_iff in IN.
          find* [IN' NE] by IN. specialize (SUBSET z IN'). rewrite InA_cons in SUBSET. tauto.
        }
        assert (IN_Z : InA eqProp Z (powerset' xs)) by (apply IH; exact SUBSET_Z).
        rewrite InA_alt in IN_Z. find* (Z' & EQ_Z & IN_Z') by IN_Z. right.
        exists Z'. split; auto. apply eq_spec. intros z.
        rewrite eq_spec in EQ_Z. rewrite in_add_iff, <- EQ_Z.
        unfold Z. rewrite in_remove_iff. split.
        { intros IN. destruct (compare z x) eqn: EQ.
          - left. now apply compare_Eq_iff.
          - right. split; auto. intros E. apply compare_Eq_iff in E. congruence.
          - right. split; auto. intros E. apply compare_Eq_iff in E. congruence.
        }
        { intros [EQ | [IN _]]; auto.
          eapply (proj2 (In_compat z x Y Y EQ (reflexivity _))). exact OBS.
        }
      * rewrite mem_spec in OBS. left. apply IH.
        intros z IN. specialize (SUBSET z IN). rewrite InA_cons in SUBSET.
        find* [EQ | IN_xs] by SUBSET; auto. exfalso. apply OBS.
        eapply (proj1 (In_compat z x Y Y EQ (reflexivity _))). exact IN.
Qed.

Theorem in_powerset_iff (X : fset A) (Y : fset A)
  : In Y (powerset X) <-> isSubsetOf Y X.
Proof.
  unfold powerset. rewrite in_fromList_iff, in_powerset'_iff.
  unfold isSubsetOf, In. reflexivity.
Qed.

Theorem filter_in_powerset (p : A -> bool) (X : fset A)
  (COMPAT : forall x, forall y, x == y -> p x = p y)
  : In (filter p X) (powerset X).
Proof.
  rewrite in_powerset_iff. intros z IN.
  rewrite in_filter_iff in IN by exact COMPAT. tauto.
Qed.

#[local]
Lemma add_fresh_injective (x : A) (Y : fset A) (Z : fset A)
  (FRESH_Y : ~ In x Y)
  (FRESH_Z : ~ In x Z)
  (EQ : add x Y == add x Z)
  : Y == Z.
Proof.
  apply eq_spec. intros z. rewrite eq_spec in EQ.
  specialize (EQ z). rewrite !in_add_iff in EQ.
  destruct (compare z x) eqn: OBS.
  - apply compare_Eq_iff in OBS.
    rewrite In_compat with (y := x) (Y := Y) by (try exact OBS; reflexivity).
    rewrite In_compat with (x := z) (y := x) (X := Z) (Y := Z) by (try exact OBS; reflexivity). tauto.
  - assert (NE : ~ z == x) by (intros E; apply compare_Eq_iff in E; congruence). tauto.
  - assert (NE : ~ z == x) by (intros E; apply compare_Eq_iff in E; congruence). tauto.
Qed.

#[local]
Lemma NoDupA_add_map (x : A) (ps : list (fset A))
  (NO_DUP : NoDupA eqProp ps)
  (FRESH : forall Y, L.In Y ps -> ~ In x Y)
  : NoDupA eqProp (L.map (add x) ps).
Proof.
  revert FRESH. induction NO_DUP as [ | Y ps NOT_IN NO_DUP IH]; intros FRESH; cbn [L.map]; econs.
  - rewrite InA_map_fset. intros (Z & IN & EQ). apply NOT_IN.
    rewrite InA_alt. exists Z. split; auto.
    eapply add_fresh_injective; [eapply FRESH; now left | eapply FRESH; now right | exact EQ].
  - eapply IH. i. eapply FRESH. now right.
Qed.

Lemma NoDup_powerset' (xs : list A)
  (NO_DUP : NoDupA eqProp xs)
  : NoDupA eqProp (powerset' xs).
Proof.
  induction NO_DUP as [ | x xs NOT_IN NO_DUP IH].
  - cbn [powerset']. apply NoDupA_singleton.
  - assert (FRESH : forall Y, InA eqProp Y (powerset' xs) -> ~ In x Y).
    { intros Y IN H_x. apply NOT_IN. eapply (proj1 (in_powerset'_iff xs Y)); eauto. }
    cbn [powerset']. eapply NoDupA_app; [apply eqProp_Equivalence | exact IH | | ].
    + eapply NoDupA_add_map; auto. intros Y IN. eapply FRESH. eapply In_InA; [apply eqProp_Equivalence | eauto].
    + intros Y IN IN'. rewrite InA_map_fset in IN'.
      find* (Z & IN_Z & EQ) by IN'. eapply FRESH; [exact IN | ].
      rewrite eq_spec in EQ. apply EQ. rewrite in_add_iff. left. reflexivity.
Qed.

Lemma length_powerset' (xs : list A)
  : length (powerset' xs) = pow2 (length xs).
Proof.
  induction xs as [ | x xs IH]; [reflexivity | ].
  cbn [powerset' length pow2]. rewrite length_app, length_map, IH. lia.
Qed.

Theorem powerset_length (X : fset A)
  : length (FSet.data (powerset X)) = pow2 (length (FSet.data X)).
Proof.
  unfold powerset. rewrite length_fromList.
  - apply length_powerset'.
  - apply NoDup_powerset'. apply NoDupA_data.
Qed.

#[global]
Instance powerset_eqPropCompatible1
  : eqPropCompatible1 powerset.
Proof.
  intros X Y EQ. apply eq_spec. intros Z. rewrite !in_powerset_iff.
  apply isSubsetOf_eqPropCompatible2; [reflexivity | exact EQ].
Qed.

End POWERSET.

#[global] Hint Rewrite @in_empty_iff @in_add_iff @in_fromList_iff @in_union_iff @in_unions_iff @in_remove_iff @product_iff @in_powerset_iff @mem_spec : simplication_hints.

End FS.

Lemma fset_NoDup {A : Type} {PROSET : isProset A} {ORD : hsOrd A} (X : fset A)
  : NoDup (FSet.data X).
Proof.
  assert (SORTED : isSorted compare (FSet.data X) = true) by apply FSet.data_isSorted.
  remember (FSet.data X) as xs eqn: DEF.
  clear DEF X. induction xs as [ | x xs IH]; [econs | ].
  rewrite isSorted_cons_iff in SORTED. des. econs; eauto.
  ii. find ? by SORTED. rewrite compare_refl in *. congruence.
Qed.
