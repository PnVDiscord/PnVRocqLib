Require Import PnV.Prelude.Prelude.

Notation "lhs ≠ rhs" := (~ (lhs = rhs)) : type_scope.

Ltac done :=
  des; subst; done!.

#[projections(primitive)]
Class isFinite@{u} (A : Type@{u}) : Type@{u} :=
  { finite_hasEqDec : hasEqDec@{u} A
  ; finite_enumeration : list A
  ; finite_enumeration_complete
    : forall x : A, L.In x finite_enumeration
  ; finite_enumeration_NoDup
    : NoDup finite_enumeration
  }.

#[global] Existing Instance finite_hasEqDec.

Lemma inject_pair_eq (A : Type) (B : Type) (x : A) (x' : A) (y : B) (y' : B)
  : (x, y) = (x', y') <-> (x = x' /\ y = y').
Proof.
  split; [intros EQ; split | intros [EQ1 EQ2]]; congruence.
Qed.

#[global] Hint Rewrite inject_pair_eq : simplication_hints.

#[universes(polymorphic=yes)]
Fixpoint iter@{u | } {A : Type@{u}} (fuel : nat) (step : A -> A) (x : A) {struct fuel} : A :=
  match fuel with
  | O => x
  | S fuel' => iter fuel' step (step x)
  end.

#[universes(polymorphic=yes)]
Lemma iter_succ@{u | } {A : Type@{u}} (fuel : nat) (step : A -> A) (x : A)
  : iter (S fuel) step x = step (iter fuel step x).
Proof.
  revert x; induction fuel as [ | fuel IH]; intros x; simpl.
  - reflexivity.
  - eapply IH.
Qed.
