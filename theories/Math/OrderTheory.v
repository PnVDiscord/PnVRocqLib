Require Import PnV.Prelude.Prelude.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.subset.
#[local] Obligation Tactic := i.

Create HintDb poset_hints.

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

Infix "⪳" := ((mkPosetFrom_ltProp wltProp wltProp_StrictOrder).(leProp)) : type_scope.

Class hsOrd (A : Type) `{POSET : isPoset A} : Type :=
  { compare (x : A) (y : A) : comparison
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

#[local] Hint Resolve Equivalence_Reflexive Equivalence_Symmetric Equivalence_Transitive : poset_hints.

#[local] Hint Resolve eqProp_refl eqProp_sym eqProp_trans leProp_refl leProp_trans leProp_antisymmetry eqProp_implies_leProp : poset_hints.

Section BASIC1.

Lemma leProp_unfold {A : Type} `{POSET : isPoset A} (x : A) (y : A)
  : x =< y <-> (forall z, z =< x -> z =< y).
Proof.
  exact (proj1 (PreOrder_iff leProp) leProp_PreOrder x y).
Qed.

#[local] Close Scope nat_scope.

#[local] Notation "x >= y" := (y =< x) (only parsing) : type_scope.

Context {D : Type}.

Definition fixedpointsOf `{SETOID : isSetoid D} (f : D -> D) : ensemble D :=
  fun x => x == f x.

Definition prefixedpointsOf `{POSET : isPoset D} (f : D -> D) : ensemble D :=
  fun x => x >= f x.

Definition postfixedpointsOf `{POSET : isPoset D} (f : D -> D) : ensemble D :=
  fun x => x =< f x.

Definition upperboundsOf `{POSET : isPoset D} (X : ensemble D) : ensemble D :=
  fun u => forall x : D, forall IN : x \in X, x =< u.

Definition lowerboundsOf `{POSET : isPoset D} (X: ensemble D) : ensemble D :=
  fun l => forall x : D, forall IN : x \in X, x >= l.

Definition is_supremum_of `{POSET : isPoset D} (sup_X : D) (X : ensemble D) : Prop :=
  forall u : D, sup_X =< u <-> u \in upperboundsOf X.

Definition is_infimum_of `{POSET : isPoset D} (inf_X : D) (X : ensemble D) : Prop :=
  forall l : D, inf_X >= l <-> l \in lowerboundsOf X.

#[global]
Add Parametric Morphism `{SETOID : isSetoid D}
  : fixedpointsOf with signature (eqProp ==> eqProp)
  as fixedpointsOf_compatWith_eqProp.
Proof.
  intros f1 f2 f1_eq_f2. unfold fixedpointsOf. cbn. unfold "\in". intros x. split; intros EQ.
  - transitivity (f1 x); [exact EQ | exact (f1_eq_f2 x)].
  - transitivity (f2 x); [exact EQ | symmetry; exact (f1_eq_f2 x)].
Qed.

#[local] Hint Unfold fixedpointsOf prefixedpointsOf postfixedpointsOf upperboundsOf lowerboundsOf is_supremum_of is_infimum_of : simplication_hints.

Context `{POSET : isPoset D}.

Lemma supremum_is_infimum_of_its_upperbounds X sup_X
  (SUPREMUM : is_supremum_of sup_X X)
  : is_infimum_of sup_X (E.singleton sup_X).
Proof.
  ii. split.
  - ii. now inv IN.
  - ii. red in H. done!.
Qed.

Lemma supremum_monotonic sup_X1 sup_X2 X1 X2
  (SUPREMUM1 : is_supremum_of sup_X1 X1)
  (SUPREMUM2 : is_supremum_of sup_X2 X2)
  (SUBSET : X1 \subseteq X2)
  : sup_X1 =< sup_X2.
Proof.
  eapply SUPREMUM1. ii. eapply SUPREMUM2; done!.
Qed.

#[local] Hint Resolve supremum_monotonic : poset_hints.

Lemma supremum_unique sup_X1 sup_X2 X1 X2
  (SUPREMUM1 : is_supremum_of sup_X1 X1)
  (SUPREMUM2 : is_supremum_of sup_X2 X2)
  (EQ : X1 == X2)
  : sup_X1 == sup_X2.
Proof.
  eapply leProp_antisymmetry; eapply supremum_monotonic; done!.
Qed.

#[local] Hint Resolve supremum_unique : poset_hints.

End BASIC1.

Module Cola.

Notation "`[ A -> B ]" := { f : A -> B | isMonotonic1 f }.

Class isCola (D : Type) {POSET : isPoset D} : Type :=
  supremum_cola (X : ensemble D) : { sup_X : D | is_supremum_of sup_X X }.

End Cola.

Module Cpo.

Import ListNotations.

Notation "`[ A -> B ]" := { f : A -> B | isContinuous f }.

Variant isDirected {D : Type} `{POSET : isPoset D} (X : ensemble D) : Prop :=
  | isDirected_intro 
    (NONEMPTY : exists x0, x0 \in X)
    (DIRECTED' : forall x1, forall x2, forall x1_IN : x1 \in X, forall x2_IN : x2 \in X, exists x3, x3 \in X /\ (x1 =< x3 /\ x2 =< x3))
    : isDirected X.

#[local] Hint Constructors isDirected : poset_hints.

Lemma isDirected_iff {D : Type} `{POSET : isPoset D} (X : ensemble D)
  : isDirected X <-> (forall xs, L.is_finsubset_of xs X -> exists y, y \in X /\ (forall x, In x xs -> x =< y)).
Proof.
  split.
  - intros [? ?]. induction xs as [ | x' xs' IH]; simpl.
    + done!.
    + intros FINSUBSET. exploit IH. done!.
      intros [y' [IN' BOUNDED']]. exploit (DIRECTED' x' y'); eauto.
      intros (y & ? & ? & ?). exists y. split; trivial. intros x [<- | IN]; done!.
  - intros DIRECTED. split.
    + exploit (DIRECTED []); simpl.
      * done!.
      * intros [y [IN ?]]. exists y. done!.
    + ii. exploit (DIRECTED [x1; x2]); simpl. 
      * now intros ? [<- | [<- | []]].
      * intros [y [IN ?]]. exists y. done!.
Qed.

Lemma preservesDirectedness_if_isMonotonic {A : Type} {B : Type} {A_isPoset : isPoset A} {B_isPoset : isPoset B} (f : A -> B)
  (MONOTONIC : isMonotonic1 f)
  : forall X, isDirected X -> isDirected (E.image f X).
Proof.
  intros X [? ?]. split.
  - destruct NONEMPTY as [x0 IN]. exists (f x0). done!.
  - intros y1 y2 ? ?. s!. destruct x1_IN as [x1 [-> x1_in]]; destruct x2_IN as [x2 [-> x2_in]].
    pose proof (DIRECTED' x1 x2 x1_in x2_in) as [x3 [x3_in [x1_le_x3 x2_le_x3]]]. exists (f x3). done!.
Qed.

Class isCpo (D : Type) `{POSET : isPoset D} : Type :=
  { bottom_cpo : D
  ; supremum_cpo (X : ensemble D) (DIRECTED : isDirected X) : D
  ; bottom_cpo_spec : forall x : D, bottom_cpo =< x
  ; supremum_cpo_spec (X : ensemble D) (DIRECTED : isDirected X) : is_supremum_of (supremum_cpo X DIRECTED) X
  }.

End Cpo.
