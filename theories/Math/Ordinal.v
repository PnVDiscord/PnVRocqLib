Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Prelude.AC.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Data.Aczel.

Module Ord.

Record t : Type :=
  Mk
  { asSet : Tree
  ; isOrd : isOrdinal asSet
  }.

Definition empty : Ord.t :=
  Mk empty empty_isOrdinal.

Definition succ (x : Ord.t) : Ord.t :=
  Mk (succ (asSet x)) (succ_isOrdinal (asSet x) (isOrd x)).

Definition limit {A : Type@{Set_u}} (x : A -> Ord.t) : Ord.t :=
  Mk (indexed_union A (fun i => asSet (x i))) (indexed_union_isOrdinal (fun i => asSet (x i)) (fun i => isOrd (x i))).

End Ord.

Notation asSet := Ord.asSet.
Notation isOrd := Ord.isOrd.
Notation MkOrd o o_ord := (Ord.Mk o o_ord).

#[global]
Instance Ord_isSetoid : isSetoid Ord.t :=
  { eqProp lhs rhs := lhs.(asSet) =ᵣ rhs.(asSet)
  ; eqProp_Equivalence := relation_on_image_liftsEquivalence rEq_asSetoid.(eqProp_Equivalence) asSet
  }.

#[global]
Instance Ord_isProset : isProset Ord.t :=
  { leProp lhs rhs := lhs.(asSet) ≦ᵣ rhs.(asSet)
  ; Proset_isSetoid := Ord_isSetoid
  ; leProp_PreOrder := relation_on_image_liftsPreOrder rLe_PreOrder asSet
  ; leProp_PartialOrder := relation_on_image_liftsPartialOrder rLe_PartialOrder asSet
  }.

#[local] Infix "\in" := member : type_scope.
#[local] Infix "\subseteq" := isSubsetOf : type_scope.
