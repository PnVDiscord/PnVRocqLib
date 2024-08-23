Require Import PnV.Prelude.Prelude.

Class isWellPreOrderedSet (A : Type) (leProp : A -> A -> Prop) {PREORDER : PreOrder leProp} : Type :=
  wellorder (x : nat -> A) : { '(i, j) : nat * nat | i < j /\ leProp (x i) (x j) }.

Class isToset (A : Type) : Type :=
  { leToset (lhs : A) (rhs : A) : Prop
  ; leToset_PreOrder :: PreOrder leToset
  ; leToset_PartialOrder :: PartialOrder eq leToset
  ; leToset_total x y
    : leToset x y \/ leToset y x
  }.

Infix "≦" := leToset : type_scope.

Class isWoset (A : Type) : Type :=
  { Woset_isToset :: isToset A
  ; Woset_wellfounded :: isWellPreOrderedSet A leToset
  }.
