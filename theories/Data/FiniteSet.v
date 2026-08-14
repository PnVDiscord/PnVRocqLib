Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.X.
Require Export PnV.Math.ThN.

#[local] Infix "=~=" := is_similar_to : type_scope.
#[local] Infix "\in" := E.In.
#[local] Infix "∈" := L.In.

#[local] Hint Resolve S_lt_S_intro : core.

Universe U_fs.

Constraint U_fs <= U_discourse.

Module FS.

#[universes(polymorphic=yes)]
Definition fin_ensemble@{u | } (Elem : Type@{u}) : Type@{u} :=
  list Elem.

Definition Similarity_list_finite_ensemble {ELEM : Type} {ELEM' : Type} (ELEM_sim : Similarity ELEM ELEM') : Similarity (fin_ensemble ELEM) (ensemble ELEM') :=
  fun xs : fin_ensemble ELEM => fun X' : ensemble ELEM' => forall x : ELEM, forall x' : ELEM', x =~= x' -> ⟪ IFF : x ∈ xs <-> x' \in X' ⟫.

#[global]
Instance list_corresponds_to_finite_ensemble {ELEM : Type} : Similarity (fin_ensemble ELEM) (ensemble ELEM) :=
  Similarity_list_finite_ensemble eq.

Theorem list_corresponds_to_finite_ensemble_iff (A : Type) (xs : fin_ensemble A) (X : ensemble A)
  : xs =~= X <-> (forall x, x ∈ xs <-> x \in X).
Proof.
  done!.
Qed.

#[global] Hint Rewrite list_corresponds_to_finite_ensemble_iff : simplication_hints.

Theorem list_corresponds_to_finite_ensemble_flat_map {A : Type} {B : Type} (xs : fin_ensemble A) (X : ensemble A) (f : A -> fin_ensemble B) (F : A -> ensemble B)
  (xs_sim : xs =~= X)
  (f_sim : forall x, x ∈ xs -> f x =~= F x)
  : L.flat_map f xs =~= (X >>= F).
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff.
  intros b. rewrite L.in_flat_map. split.
  - intros (x & x_in & b_in). exists x. split.
    + rewrite list_corresponds_to_finite_ensemble_iff in xs_sim.
      now rewrite <- xs_sim.
    + find fx_sim by f_sim.
      rewrite list_corresponds_to_finite_ensemble_iff in fx_sim.
      now rewrite <- fx_sim.
  - intros (x & x_in & b_in). exists x. split.
    + rewrite list_corresponds_to_finite_ensemble_iff in xs_sim.
      now rewrite -> xs_sim.
    + rewrite list_corresponds_to_finite_ensemble_iff in xs_sim.
      rewrite <- xs_sim in x_in. find fx_sim by f_sim.
      rewrite list_corresponds_to_finite_ensemble_iff in fx_sim.
      now rewrite -> fx_sim.
Qed.

#[global] Typeclasses Opaque fin_ensemble.

#[global] Hint Rewrite L.in_concat : simplication_hints.
#[global] Hint Rewrite L.in_map_iff : simplication_hints.
#[global] Hint Rewrite L.in_flat_map : simplication_hints.
#[global] Hint Rewrite length_app : simplication_hints.
#[global] Hint Rewrite length_map : simplication_hints.

#[global, program]
Instance fin_ensemble_isSetoid (Elem : Type@{U_fs}) (Elem_isSetoid : isSetoid Elem) : isSetoid (fin_ensemble@{U_fs} Elem) :=
  { eqProp (lhs : list Elem) (rhs : list Elem) := (forall e : Elem, forall IN : e ∈ lhs, exists e', e' ∈ rhs /\ e == e') /\ (forall e : Elem, forall IN : e ∈ rhs, exists e', e' ∈ lhs /\ e' == e) }.
Next Obligation.
  split; [intros xs | intros xs ys [xs_ys ys_xs] | intros xs ys zs [xs_ys ys_xs] [ys_zs zs_ys]]; split; i.
  - exists e. split; auto with *.
  - exists e. split; auto with *.
  - find (e1 & H_in & H_eq) by ys_xs. exists e1. split; auto with *.
  - find (e1 & H_in & H_eq) by xs_ys. exists e1. split; auto with *.
  - find (e1 & H_in & H_eq) by xs_ys. find (e1' & H_in' & H_eq') by ys_zs. exists e1'. split; auto. transitivity e1; auto with *.
  - find (e1 & H_in & H_eq) by zs_ys. find (e1' & H_in' & H_eq') by ys_xs. exists e1'. split; auto. transitivity e1; auto with *.
Qed.

#[global]
Instance fin_ensemble_isSetoid1 : isSetoid1 fin_ensemble@{U_fs} :=
  fin_ensemble_isSetoid.

Lemma fin_ensemble_isSetoid1_eq_iff (A : Type@{U_fs}) (xs : fin_ensemble@{U_fs} A) (xs' : fin_ensemble@{U_fs} A)
  : eqProp (isSetoid := fromSetoid1 fin_ensemble_isSetoid) xs xs' <-> (forall e : A, e ∈ xs <-> e ∈ xs').
Proof.
  ii; ss!.
Qed.

#[global, universes(polymorphic=yes)]
Instance fin_ensemble_isMonad@{u} : isMonad@{u u} fin_ensemble@{u} :=
  { pure {A : Type@{u}} (x : A) := (@L.cons A x (@L.nil A))
  ; bind {A : Type@{u}} {B : Type@{u}} (xs : list A) (k : A -> list B) := (@flat_map A B k xs)
  }.

#[global]
Instance fin_ensemble_MonadLaws
  : MonadLaws fin_ensemble (SETOID1 := fin_ensemble_isSetoid1) (MONAD := fin_ensemble_isMonad@{U_fs}).
Proof.
  split; i; rewrite fin_ensemble_isSetoid1_eq_iff in *; i; ss!; ss!; exists x0; ss!.
Qed.

Lemma in_fin_ensemble_bind_intro {A : Type} {B : Type} (xs : fin_ensemble A) (k : A -> fin_ensemble B) (x : A) (y : B)
  (x_in : L.In x xs)
  (y_in : L.In y (k x))
  : L.In y (xs >>= k).
Proof.
  cbn [bind fin_ensemble_isMonad]. rewrite L.in_flat_map. eauto.
Qed.

Lemma in_fin_ensemble_bind_elim {A : Type} {B : Type} (xs : fin_ensemble A) (k : A -> fin_ensemble B) (y : B)
  (IN : L.In y (xs >>= k))
  : exists x, L.In x xs /\ L.In y (k x).
Proof.
  cbn [bind fin_ensemble_isMonad] in IN. rewrite L.in_flat_map in IN. exact IN.
Qed.

Definition mem {A : Type@{U_fs}} `{EQ_DEC : hasEqDec A} (x : A) (xs : fin_ensemble A) : bool :=
  if in_dec EQ_DEC x xs then true else false.

Theorem mem_spec (A : Type) `(EQ_DEC : hasEqDec A) (x : A) (xs : fin_ensemble A)
  : forall b, mem x xs = b <-> (if b then x ∈ xs else ~ x ∈ xs).
Proof.
  unfold mem; intros [ | ]; revert x; induction xs; intros; simpl; des_ifs; done.
Qed.

#[global] Hint Rewrite mem_spec : simplication_hints.

Definition add {A : Type@{U_fs}} `{EQ_DEC : hasEqDec A} (x : A) (xs : fin_ensemble A) : fin_ensemble A :=
  if mem x xs then xs else x :: xs.

Theorem in_add_iff (A : Type) `(EQ_DEC : hasEqDec A) (x : A) (xs : fin_ensemble A)
  : forall y, y ∈ add x xs <-> (x = y \/ y ∈ xs).
Proof.
  i; unfold add, mem; des_ifs; done.
Qed.

#[global] Hint Rewrite in_add_iff : simplication_hints.

Fixpoint union {A : Type@{U_fs}} `{EQ_DEC : hasEqDec A} (xs : fin_ensemble A) (ys : fin_ensemble A) {struct xs} : fin_ensemble A :=
  match xs with
  | [] => ys
  | x :: xs' => union xs' (add x ys)
  end.

Theorem in_union_iff (A : Type) `(EQ_DEC : hasEqDec A) (xs : fin_ensemble A) (ys : fin_ensemble A)
  : forall z, z ∈ union xs ys <-> (z ∈ xs \/ z ∈ ys).
Proof.
  revert ys; induction xs as [ | x xs IH]; ii; simpl; s!.
  - tauto.
  - rewrite IH; s!; tauto.
Qed.

#[global] Hint Rewrite in_union_iff : simplication_hints.

Fixpoint normalize {A : Type@{U_fs}} `{EQ_DEC : hasEqDec A} (xs : fin_ensemble A) {struct xs} : fin_ensemble A :=
  match xs with
  | [] => []
  | x :: xs' => add x (normalize xs')
  end.

Theorem in_normalize_iff (A : Type) `(EQ_DEC : hasEqDec A) (xs : fin_ensemble A)
  : forall z, z ∈ normalize xs <-> z ∈ xs.
Proof.
  induction xs as [ | x xs IH]; simpl; ii; done.
Qed.

#[global] Hint Rewrite in_normalize_iff : simplication_hints.

Fixpoint unions {A : Type@{U_fs}} `{EQ_DEC : hasEqDec A} (xss : fin_ensemble (fin_ensemble A)) {struct xss} : fin_ensemble A :=
  match xss with
  | [] => []
  | xs :: xss' => union xs (unions xss')
  end.

Lemma in_unions_iff (A : Type) `(EQ_DEC : hasEqDec A) (xss : fin_ensemble (fin_ensemble A))
  : forall z, z ∈ unions xss <-> (exists xs, xs ∈ xss /\ z ∈ xs).
Proof.
  induction xss as [ | xs xss IH]; simpl; i; ss!.
Qed.

#[global] Hint Rewrite in_unions_iff : simplication_hints.

Lemma remove_length_lt {A : Type} `{EQ_DEC : hasEqDec A} (x : A) (xs : list A)
  (IN : x ∈ xs)
  : length (remove EQ_DEC x xs) < length xs.
Proof.
  revert x IN; induction xs as [ | y ys IH]; simpl; ii.
  - ss!.
  - des_ifs.
    + find ? by remove_length_le; ss!.
    + des; ss!.
Qed.

Fixpoint powerset {A : Type@{U_fs}} (xs : fin_ensemble A) : fin_ensemble (fin_ensemble A) :=
  match xs with
  | [] => [[]]
  | x :: xs' =>
    let ps := powerset xs' in
    ps ++ map (fun ys => x :: ys) ps
  end.

Lemma filter_in_powerset {A : Type} (p : A -> bool) (xs : fin_ensemble A)
  : filter p xs ∈ powerset xs.
Proof.
  induction xs as [ | x xs IH]; simpl; des_ifs; ss!.
Qed.

Lemma powerset_length@{u} {A : Type@{u}} (xs : fin_ensemble A)
  : length (powerset xs) = pow2 (length xs).
Proof.
  induction xs as [ | x xs IH]; simpl.
  - reflexivity.
  - rewrite length_app, length_map, IH. f_equal.
    transitivity (pow2 (length xs)); [exact IH | symmetry; apply Nat.add_0_r].
Qed.

#[universes(polymorphic=yes)]
Definition product@{u v} {A : Type@{u}} {B : Type@{v}} (xs : list A) (ys : list B) : list (A * B) :=
  xs >>= fun x => ys >>= fun y => pure (x, y).

Theorem product_iff (A : Type) (B : Type) (xs : fin_ensemble A) (ys : fin_ensemble B)
  : forall x, forall y, (x, y) ∈ product xs ys <-> (x ∈ xs /\ y ∈ ys).
Proof.
  ii; unfold product; split; intros H_in.
  - done.
  - s!. exists (concat (map (fun y => pure (x, y)) ys)). s!. split.
    + exists x. ss!.
    + exists [(x, y)]. ss!.
Qed.

#[global] Hint Rewrite product_iff : simplication_hints.

Lemma in_list_bind_intro {A : Type} {B : Type} (xs : list A) (k : A -> list B) (x : A) (y : B)
  (x_in : x ∈ xs)
  (y_in : y ∈ k x)
  : y ∈ (xs >>= k).
Proof.
  rewrite L.list_bind_flat_map. rewrite in_flat_map; eauto.
Qed.

Lemma in_list_bind_elim {A : Type} {B : Type} (xs : list A) (k : A -> list B) (y : B)
  (IN : y ∈ (xs >>= k))
  : exists x, x ∈ xs /\ y ∈ k x.
Proof.
  induction xs as [ | x xs IH]; ss!.
Qed.

Lemma in_list_pure_intro {A : Type} (x : A)
  : x ∈ pure x.
Proof.
  now simpl; left.
Qed.

Lemma forallb_false_exists {A : Type} (p : A -> bool) (xs : list A)
  (FORALL : forallb p xs = false)
  : exists x, x ∈ xs /\ p x = false.
Proof.
  induction xs as [ | x xs IH]; s!; [congruence | des; ss!].
Qed.

Lemma find_some_exists {A : Type} (p : A -> bool) (xs : list A) (x : A)
  (IN : x ∈ xs)
  (YES : p x = true)
  : exists y, find p xs = Some y.
Proof.
  revert x IN YES; induction xs as [ | x0 xs IH]; ss!; des_ifs; eauto.
Qed.

Theorem NoDup_exists_injective_length {A : Type} {B : Type} `{B_hasEqDec : hasEqDec B} (xs : list A) (ys : list B) (R : A -> B -> Prop)
  (xs_NoDup : NoDup xs)
  (R_total : forall x, x ∈ xs -> (exists y, y ∈ ys /\ R x y))
  (R_functional : forall x1, forall x2, forall y, x1 ∈ xs -> x2 ∈ xs -> R x1 y -> R x2 y -> x1 = x2)
  : length xs <= length ys.
Proof.
  revert ys R_total R_functional; induction xs_NoDup as [ | x xs NOT_IN NO_DUP IH]; intros ys TOTAL INJ; simpl; [lia | ].
  pose proof (TOTAL x (or_introl eq_refl)) as (y & IN_Y & R_XY).
  enough (LE : length xs <= length (remove B_hasEqDec y ys)).
  { pose proof (remove_length_lt y ys IN_Y). lia. }
  eapply IH.
  - intros x' IN_XS.
    pose proof (TOTAL x' (or_intror IN_XS)) as (y' & IN_Y' & R_XY').
    exists y'. split; eauto. rewrite L.in_remove_iff. split; eauto; ii.
    enough (x' = x) by done!.
    eapply INJ; ss!.
  - ii; eapply INJ; ss!.
Qed.

Lemma subset_lemma (A : Type@{U_fs}) (xs : fin_ensemble A) (X : ensemble A)
  : (exists X' : ensemble@{U_fs} A, xs =~= E.union X X') <-> (forall x : A, E.In x X -> L.In x xs).
Proof.
  ss!. exists (E.fromList xs). ss!.
Qed.

Lemma superset_lemma (A : Type@{U_fs}) (xs : fin_ensemble A) (X : ensemble A)
  : (exists X' : ensemble@{U_fs} A, xs =~= E.intersection X X') <-> (forall x : A, L.In x xs -> E.In x X).
Proof.
  ss!. exists (E.fromList xs). ss!.
Qed.

End FS.
