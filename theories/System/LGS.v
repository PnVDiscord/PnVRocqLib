Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Strings.String.
Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Monad.
Require Import PnV.Data.FiniteMap.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Data.Graph.
Require Import PnV.System.Regex.
Require Import PnV.Prelude.X.

Import DoNotations.

#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "=~=" := (is_similar_to (Similarity := Re.in_regex eq)) : type_scope.
#[local] Infix "∈" := L.In.
#[local] Infix "⊑" := is_similar_to.

#[local] Existing Instance Similarity_bool_Prop.

#[global]
Instance ascii_hasEqDec
  : hasEqDec@{Set} ascii.
Proof.
  exact Ascii.ascii_dec.
Defined.

#[global]
Instance regex_hasEqDec {A : Set}
  (A_hasEqDec : hasEqDec@{Set} A)
  : hasEqDec@{Set} (regex A).
Proof.
  red in A_hasEqDec |- *. decide equality.
Defined.

Notation all_bools := Bool_FinEnum.all.

Notation all_bools_complete := Bool_FinEnum.all_complete.

Module Ascii_FinEnum <: FINITE_ENUM.

Definition t : Set :=
  ascii.

Definition t_hasEqDec : hasEqDec@{Set} Ascii_FinEnum.t :=
  ascii_hasEqDec.

Definition all : list ascii :=
  do
    'b0 <- all_bools;
    'b1 <- all_bools;
    'b2 <- all_bools;
    'b3 <- all_bools;
    'b4 <- all_bools;
    'b5 <- all_bools;
    'b6 <- all_bools;
    'b7 <- all_bools;
    ret (Ascii b0 b1 b2 b3 b4 b5 b6 b7)
  end.

Lemma all_complete
  : forall x : Ascii_FinEnum.t, L.In x Ascii_FinEnum.all.
Proof.
  unfold all; intros [b0 b1 b2 b3 b4 b5 b6 b7].
  eapply list_bind_complete with (x := b0); [eapply all_bools_complete | ].
  eapply list_bind_complete with (x := b1); [eapply all_bools_complete | ].
  eapply list_bind_complete with (x := b2); [eapply all_bools_complete | ].
  eapply list_bind_complete with (x := b3); [eapply all_bools_complete | ].
  eapply list_bind_complete with (x := b4); [eapply all_bools_complete | ].
  eapply list_bind_complete with (x := b5); [eapply all_bools_complete | ].
  eapply list_bind_complete with (x := b6); [eapply all_bools_complete | ].
  eapply list_bind_complete with (x := b7); [eapply all_bools_complete | ].
  eapply list_pure_complete.
Qed.

Lemma all_no_dup
  : NoDup Ascii_FinEnum.all.
Proof.
  assert (EQ : L.nodup (@eq_dec@{Set} ascii ascii_hasEqDec) all = all) by reflexivity.
  rewrite <- EQ. eapply L.NoDup_nodup.
Qed.

End Ascii_FinEnum.

Notation all_asciis := Ascii_FinEnum.all.

Notation all_asciis_complete := Ascii_FinEnum.all_complete.

Module Type TOKEN_SPEC.

Parameter t : Set.

Parameter t_hasEqDec : hasEqDec@{Set} TOKEN_SPEC.t.

Parameter rules : list (TOKEN_SPEC.t * regex ascii).

End TOKEN_SPEC.

Module LGS (Token : TOKEN_SPEC).

#[global] Existing Instance Token.t_hasEqDec.

Module BuildError.

Inductive t : Set :=
  | NullableTokenRule (idx : nat).

End BuildError.

#[universes(polymorphic=yes)]
Definition BuildErrorM@{u} (A : Type@{u}) : Type@{u} :=
  BuildError.t + A.

#[universes(polymorphic=yes)]
Instance BuildErrorM_isMonad@{u} : isMonad@{u u} BuildErrorM@{u} :=
  { pure {A : Type@{u}} (x : A) := inr x
  ; bind {A : Type@{u}} {B : Type@{u}} (m : BuildErrorM A) (k : A -> BuildErrorM B) := B.either (@inl _ _) k m
  }.

Fact mem_spec (A : Set) `(A_hasEqDec : hasEqDec@{Set} A) (x : A) (xs : list A) (b : bool)
  : mem@{Set} x xs = b <-> (if b then x ∈ xs else ~ x ∈ xs).
Proof.
  destruct b; [eapply mem_true_iff | eapply mem_false_iff].
Qed.

Fact eqb_iff (A : Set) `(A_hasEqDec : hasEqDec@{Set} A) (x : A) (y : A) (b : bool)
  : eqb@{Set} x y = b <-> (if b then x = y else ~ x = y).
Proof.
  eapply eqb_spec.
Qed.

Fact existsb_iff (A : Set) (p : A -> bool) (xs : list A)
  : existsb p xs = true <-> (exists x, x ∈ xs /\ p x = true).
Proof.
  eapply L.existsb_exists.
Qed.

Fact forallb_iff (A : Set) (p : A -> bool) (xs : list A)
  : forallb p xs = true <-> (forall x, x ∈ xs -> p x = true).
Proof.
  eapply L.forallb_forall.
Qed.

#[local] Hint Rewrite mem_spec eqb_iff existsb_iff forallb_iff : simplication_hints.

#[local] Existing Instance list_corresponds_to_finite_ensemble.
#[local] Existing Instance alist_corresponds_to_finite_partial_map.

End LGS.
