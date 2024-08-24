Require Import PnV.Prelude.Prelude.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.EqdepFacts.

Lemma eq_pirrel_fromEqDec {A : Type} {hasEqDec: hasEqDec A} (lhs : A) (rhs : A)
  (EQ1 : lhs = rhs)
  (EQ2 : lhs = rhs)
  : EQ1 = EQ2.
Proof.
  eapply UIP_dec. exact hasEqDec.
Defined.

Lemma projT2_eq_fromEqDec {A : Type} {B : A -> Type} {hasEqDec : hasEqDec A} (x : A) (y1 : B x) (y2 : B x)
  (EQ : @existT A B x y1 = @existT A B x y2)
  : y1 = y2.
Proof.
  erewrite eq_sigT_iff_eq_dep in EQ. eapply eq_rect_eq__eq_dep1_eq.
  - ii. eapply eq_rect_eq_dec. exact hasEqDec.
  - eapply eq_dep_dep1. exact EQ.
Defined.
