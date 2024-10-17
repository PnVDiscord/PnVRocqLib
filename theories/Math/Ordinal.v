Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Prelude.AC.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Data.Aczel.

#[local] Infix "\in" := member : type_scope.

#[local] Infix "\subseteq" := isSubsetOf : type_scope.

Module Ord.

Variant trichotomy (x : Tree) (y : Tree) : Prop :=
  | Trichotomy_lt
    (LT : x \in y)
    : trichotomy x y
  | Trichotomy_eq
    (EQ : x == y)
    : trichotomy x y
  | Trichotomy_gt
    (GT : y \in x)
    : trichotomy x y.

Variant isOrdinal (alpha : Tree) : Prop :=
  | isOrdinal_intro
    (TRANS : isTransitiveSet alpha)
    (TOTAL : forall x, forall y, x \in alpha -> y \in alpha -> trichotomy x y)
    : isOrdinal alpha.

Record t : Type :=
  Mk { asSet : Tree; isOrd : isOrdinal asSet }.

End Ord.

Notation isOrdinal := Ord.isOrdinal.

Notation asSet := Ord.asSet.

Notation isOrd := Ord.isOrd.

Notation MkOrd o o_ord := (Ord.Mk o o_ord).
