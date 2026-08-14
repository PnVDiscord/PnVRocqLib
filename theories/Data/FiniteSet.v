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

End FS.
