Require Import PnV.Prelude.Prelude.
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
