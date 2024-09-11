Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import Coq.Logic.EqdepFacts.
Require Export Coq.Logic.Classical_Prop.

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
