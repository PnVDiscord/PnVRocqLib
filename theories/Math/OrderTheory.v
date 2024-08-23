Require Import PnV.Prelude.Prelude.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.subset.
#[local] Obligation Tactic := i.

Lemma well_founded_implies_Irreflexive {A : Type} (R : A -> A -> Prop)
  (WF : well_founded R)
  : Irreflexive R.
Proof.
  intros x H_R. induction (WF x) as [x _ IH]. eapply IH with (y := x); exact H_R.
Qed.

#[program]
Definition mkPosetFrom_ltProp {A : Type} (ltProp : A -> A -> Prop) (ltProp_StrictOrder : StrictOrder ltProp) : isPoset A :=
  {| leProp x y := ltProp x y \/ x = y; Poset_isSetoid := mkSetoid_from_eq; |}.
Next Obligation.
  split; ii; firstorder try congruence.
Qed.
Next Obligation.
  intros x y. cbn. unfold flip. split; firstorder try congruence. contradiction (StrictOrder_Irreflexive x). firstorder.
Qed.

Class isWellOrderedSet (A : Type) : Type :=
  { wltProp (lhs : A) (rhs : A) : Prop
  ; wltProp_Transitive :: Transitive wltProp
  ; wltProp_well_founded : well_founded wltProp
  }.

Infix "⪵" := wltProp : type_scope.

#[global]
Instance wltProp_StrictOrder {A : Type} `{WOSET : isWellOrderedSet A} : StrictOrder wltProp :=
  { StrictOrder_Irreflexive := well_founded_implies_Irreflexive wltProp wltProp_well_founded
  ; StrictOrder_Transitive := wltProp_Transitive
  }.
