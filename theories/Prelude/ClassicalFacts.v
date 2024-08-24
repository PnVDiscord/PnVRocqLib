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
