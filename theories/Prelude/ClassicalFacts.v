Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Export Stdlib.Logic.Classical_Prop.

Include EqdepTheory.

Lemma projT2_eq {A : Type} {B : A -> Type} (x : A) (y1 : B x) (y2 : B x)
  (EQ : @existT A B x y1 = @existT A B x y2)
  : y1 = y2.
Proof.
  erewrite eq_sigT_iff_eq_dep in EQ. eapply eq_rect_eq__eq_dep1_eq.
  - ii. eapply eq_rect_eq.
  - eapply eq_dep_dep1. exact EQ.
Qed.

Lemma exist_eq_iff {A : Type} {P : A -> Prop} (x : A) (x' : A) (H_P : P x) (H_P' : P x')
  : @exist A P x H_P = @exist A P x' H_P' <-> x = x'.
Proof.
  split.
  - intros EQ. apply f_equal with (f := @proj1_sig A P) in EQ. exact EQ.
  - intros EQ. subst x'. rewrite proof_irrelevance with (P := P x) (p1 := H_P) (p2 := H_P'). reflexivity.
Qed.

Theorem minimisation_lemma (P : nat -> Prop)
  (EXISTENCE : exists n, P n)
  : exists n, P n /\ ⟪ MIN : forall m, P m -> m >= n ⟫.
Proof.
  eapply NNPP. intros CONTRA. destruct EXISTENCE as [n P_n].
  eapply infinite_descent with (P := P) (n := n); [intros i P_i | exact P_n].
  eapply NNPP. intros CONTRA'. eapply CONTRA. exists i. split; trivial.
  intros m P_m. enough (WTS : ~ m < i) by lia. intros H_lt.
  contradiction CONTRA'. exists m. split; trivial.
Qed.

#[projections(primitive)]
Class ClassicalAxioms `{b_AC : bool} `{b_fun_ext : bool} `{b_prop_ext : bool} : Prop :=
  { Axiom_of_Choice (A : Type) (B : A -> Type) (R : forall x : A, B x -> Prop)
    (CHOICE : forall x : A, exists y : B x, R x y)
    : if b_AC then exists f : forall x : A, B x, forall x : A, R x (f x) else True
  ; Functional_Extensionality (A : Type) (B : A -> Type) (f : forall x : A, B x) (f' : forall x : A, B x)
    (EQUAL : forall x : A, f x = f' x)
    : if b_fun_ext then f = f' else True
  ; Propositional_Extensionality (P : Prop) (P' : Prop)
    (EQUAL : P <-> P')
    : if b_prop_ext then P = P' else True
  } as ClassicalAxioms.

#[global] Abbreviation flagsOfClassicalAxioms := @ClassicalAxioms.

Lemma AC_implies_DC `{Axms : ClassicalAxioms (b_AC := true)} {X : Type} (step : X -> X -> Prop) (x0 : X)
  (Hstep : forall x : X, exists x' : X, step x x')
  : exists seq : nat -> X, seq O = x0 /\ ⟪ STEP : forall n : nat, step (seq n) (seq (S n)) ⟫.
Proof.
  pose proof (Axiom_of_Choice X (fun _ => X) step Hstep) as Hsucc.
  exact (FUN_FACTS.AC_implies_DC step x0 Hstep Hsucc).
Qed.

Lemma AC_implies_inhabited_informative_excluded_middle `{Axms : ClassicalAxioms (b_AC := true)}
  : forall P : Prop, inhabited ({P} + {~ P}).
Proof.
  exploit (Axiom_of_Choice Prop (fun _ => bool) (fun P : Prop => fun b : bool => if b then P else ~ P)).
  - intros P. now pose proof (classic P) as [YES | NO]; [exists true | exists false].
  - intros [oracle H_oracle] P. pose proof (H_oracle P). now destruct (oracle P) as [ | ]; econs; [left | right].
Qed.

Theorem AC_implies_inhabited_choice `{Axms : ClassicalAxioms (b_AC := true)} (I : Type) (X : I -> Type)
  (NONEMPTY : forall i : I, inhabited (X i))
  : inhabited (forall i : I, X i).
Proof.
  exploit (Axiom_of_Choice I X (fun i : I => fun _ : X i => True)).
  - intros i. pose proof (NONEMPTY i) as [x]. exists x. econs.
  - intros [WTS _]. econs. exact WTS.
Qed.

Corollary AC_implies_inhabited_hasEqDec `{Axms : ClassicalAxioms (b_AC := true)} (A : Type)
  : inhabited (hasEqDec A).
Proof.
  exploit (AC_implies_inhabited_choice (A * A) (fun '(lhs, rhs) => {lhs = rhs} + {lhs <> rhs})).
  - intros [x y]. eapply AC_implies_inhabited_informative_excluded_middle.
  - intros [H_dec]. econs. intros x y. now pose proof (H_dec (x, y)) as [YES | NO]; [left | right].
Qed.
