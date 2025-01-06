Require Import PnV.Prelude.Prelude.

Module Re.

Inductive t {A : Type} : Type :=
  | Null : t
  | Empty : t
  | Char (c : A) : t
  | Union (e1 : t) (e2 : t) : t
  | Append (e1 : t) (e2 : t) : t
  | Star (e1 : t).

#[global] Arguments t : clear implicits.

Inductive regex_semantics {A : Type} : Re.t A -> list A -> Prop :=
  | rs_Empty
    : regex_semantics (Empty) []
  | rs_Char c
    : regex_semantics (Char c) [c]
  | rs_Union_l s e1 e2
    (H_inl : regex_semantics e1 s)
    : regex_semantics (Union e1 e2) s
  | rs_Union_r s e1 e2
    (H_inr : regex_semantics e2 s)
    : regex_semantics (Union e1 e2) s
  | rs_Append s1 s2 e1 e2
    (H_in1 : regex_semantics e1 s1)
    (H_in2 : regex_semantics e2 s2)
    : regex_semantics (Append e1 e2) (s1 ++ s2)
  | rs_Star_nil e1
    : regex_semantics (Star e1) []
  | rs_Star_app e1 s1 s2
    (H_in1 : regex_semantics e1 s1)
    (H_in2 : regex_semantics (Star e1) s2)
    : regex_semantics (Star e1) (s1 ++ s2).

#[global] Hint Constructors regex_semantics : simplication_hints.

End Re.

Notation regex := Re.t.

Section LANGUAGE.

#[local] Notation In := L.In.
#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "\subseteq" := E.isSubsetOf : type_scope.

#[local] Hint Rewrite @E.liftM2_spec : simplication_hints.
#[local] Opaque liftM2.

Import Re.
Import ListNotations.

Context {A : Type}.

Let lang : Type :=
  ensemble (list A).

Inductive star (L : lang) : lang :=
  | star_nil
    : [] \in star L
  | Star_app s1 s2
    (H_IN1 : s1 \in L)
    (H_IN2 : s2 \in star L)
    : s1 ++ s2 \in star L.

#[local] Hint Constructors star : core.

Fixpoint eval_regex (e : regex A) {struct e} : lang :=
  match e with
  | Null => E.empty
  | Empty => E.singleton []
  | Char c => E.singleton [c]
  | Union e1 e2 => E.union (eval_regex e1) (eval_regex e2)
  | Append e1 e2 => liftM2 (@L.app A) (eval_regex e1) (eval_regex e2)
  | Star e1 => star (eval_regex e1) 
  end.

Theorem eval_regex_good e s
  : s \in eval_regex e <-> regex_semantics e s.
Proof with eauto with *.
  split.
  - revert s; induction e; simpl; intros s H_IN; rewrite!; subst...
    + destruct H_IN...
    + des; subst...
    + induction H_IN...
  - intros H_in; induction H_in; simpl; rewrite!...
Qed.

End LANGUAGE.

#[global] Hint Constructors star : simplication_hints.
