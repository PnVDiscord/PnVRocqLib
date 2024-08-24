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

Class has_ltProp (A : Type) : Type :=
  ltProp (lhs : A) (rhs : A) : Prop.

Infix "≨" := ltProp : type_scope.

Class hasStrictOrder (A : Type) : Type :=
  { lt :: has_ltProp A
  ; lt_StrictOrder :: StrictOrder lt
  }.

Infix "≦" := ((mkPosetFrom_ltProp lt lt_StrictOrder).(leProp)) : type_scope.

Class isWellOrderedSet (A : Type) : Type :=
  { wltProp : has_ltProp A
  ; wltProp_Transitive :: Transitive wltProp
  ; wltProp_well_founded : well_founded wltProp
  }.

Infix "⪵" := wltProp : type_scope.

#[global]
Instance wltProp_StrictOrder {A : Type} `{WOSET : isWellOrderedSet A} : StrictOrder wltProp :=
  { StrictOrder_Irreflexive := well_founded_implies_Irreflexive wltProp wltProp_well_founded
  ; StrictOrder_Transitive := wltProp_Transitive
  }.

Class hsOrd (A : Type) {POSET : isPoset A} : Type :=
  { compare : A -> A -> comparison
  ; compare_Lt x y
    (OBS_Lt : compare x y = Lt)
    : x =< y /\ ~ x == y
  ; compare_Eq x y
    (OBS_Eq : compare x y = Eq)
    : x == y
  ; compare_Gt x y
    (OBS_Gt : compare x y = Gt)
    : y =< x /\ ~ x == y
  }.
