Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.subset.
#[local] Obligation Tactic := i.

#[local] Hint Resolve Equivalence_Reflexive Equivalence_Symmetric Equivalence_Transitive : poset_hints.
#[local] Hint Resolve eqProp_refl eqProp_sym eqProp_trans leProp_refl leProp_trans leProp_antisymmetry eqProp_implies_leProp : poset_hints.
#[local] Hint Resolve supremum_monotonic supremum_unique supremum_congruence is_supremum_of_compatWith_eqProp : poset_hints.

Class isBA (B : Type) : Type :=
  { andB : B -> B -> B
  ; orB : B -> B -> B
  ; notB : B -> B
  ; trueB : B
  ; falseB : B
  }.

Definition andsB {B : Type} {BA : isBA B} : list B -> B :=
  fold_right andB trueB.

Class BooleanAlgebraLaws {B : Type} {SETOID : isSetoid B} (BA : isBA B) : Prop :=
  { andB_compathWith_eqProp :: eqPropCompatible2 andB
  ; orB_compatWith_eqProp :: eqPropCompatible2 orB
  ; notB_compatWith_eqProp :: eqPropCompatible1 notB
  ; andB_assoc :: isAssociative andB
  ; orB_assoc :: isAssociative orB
  ; andB_comm :: isCommutative andB
  ; orB_comm :: isCommutative orB
  ; andB_distr_orB :: distributesOver andB orB
  ; orB_distr_andB :: distributesOver orB andB
  ; trueB_id_andB :: isIdentityElementOf trueB andB
  ; falseB_id_orB :: isIdentityElementOf falseB orB
  ; falseB_ann_andB :: isAnnihilatorFor falseB andB
  ; trueB_ann_orB :: isAnnihilatorFor trueB orB
  ; andB_idem :: isIdempotent andB
  ; orBA_idem :: isIdempotent orB
  ; Absorption_andBA_orBA :: AbsorptionLaw andB orB
  ; andB_notB_falseB
    : forall x, andB x (notB x) == falseB
  ; orB_notB_trueB
    : forall x, orB x (notB x) == trueB
  }.
