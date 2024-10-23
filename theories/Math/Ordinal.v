Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Prelude.AC.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Data.Aczel.

#[local] Infix "\in" := member : type_scope.

#[local] Infix "\subseteq" := isSubsetOf : type_scope.

Module Ord.

Variant trichotomy (x : Tree) (y : Tree) : Prop :=
  | Mk_trichotomy_lt
    (LT : x \in y)
    : trichotomy x y
  | Mk_trichotomy_eq
    (EQ : x == y)
    : trichotomy x y
  | Mk_trichotomy_gt
    (GT : y \in x)
    : trichotomy x y.

#[global] Arguments Mk_trichotomy_lt {x} {y}.
#[global] Arguments Mk_trichotomy_eq {x} {y}.
#[global] Arguments Mk_trichotomy_gt {x} {y}.

Definition ltIn (alpha : Tree) (lhs : { x : Tree | x \in alpha }) (rhs : { x : Tree | x \in alpha }) : Prop :=
  proj1_sig lhs \in proj1_sig rhs.

#[global]
Instance ltIn_isWellPoset' (alpha : Tree) (TRANS : Transitive (ltIn alpha)) : isWellPoset { x : Tree | x \in alpha } :=
  { wltProp := ltIn alpha
  ; wltProp_Transitive := TRANS
  ; wltProp_well_founded := relation_on_image_liftsWellFounded member (@proj1_sig Tree (fun x => x \in alpha)) member_wf
  }.

Variant isOrdinal (alpha : Tree) : Prop :=
  | isOrdinal_intro
    (TRANS : isTransitiveSet alpha)
    (POSET : Transitive (ltIn alpha))
    (TOTAL : forall x, forall y, x \in alpha -> y \in alpha -> trichotomy x y)
    : isOrdinal alpha.

#[global] Arguments isOrdinal_intro {alpha}.

Definition ltIn_isWellPoset {alpha : Tree} (ORDINAL : isOrdinal alpha) : isWellPoset { x : Tree | x \in alpha } :=
  match ORDINAL with
  | isOrdinal_intro _ TRANS _ => ltIn_isWellPoset' alpha TRANS
  end.

Record t : Type :=
  Mk { asSet : Tree; isOrd : isOrdinal asSet }.

End Ord.

Notation isOrdinal := Ord.isOrdinal.

Notation asSet := Ord.asSet.

Notation isOrd := Ord.isOrd.
