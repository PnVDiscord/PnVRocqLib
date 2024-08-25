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

Infix "≦" := (leProp (isPoset := mkPosetFrom_ltProp lt lt_StrictOrder)) : type_scope.

Class isWellPoset (A : Type) : Type :=
  { wltProp :: has_ltProp A
  ; wltProp_Transitive :: Transitive wltProp
  ; wltProp_well_founded : well_founded wltProp
  }.

Infix "⪵" := wltProp : type_scope.

#[global]
Instance wltProp_StrictOrder {A : Type} `{WPOSET : isWellPoset A} : StrictOrder wltProp :=
  { StrictOrder_Irreflexive := well_founded_implies_Irreflexive wltProp wltProp_well_founded
  ; StrictOrder_Transitive := wltProp_Transitive
  }.

Infix "⪳" := (leProp (isPoset := mkPosetFrom_ltProp wltProp wltProp_StrictOrder)) : type_scope.

Class isWellToset (A : Type) : Type :=
  { WellToset_isWellPoset :: isWellPoset A
  ; WellToset_total_order (x : A) (y : A)
    : x ⪳ y \/ y ⪳ x
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

Definition fixedpointsOf {D : Type} `{SETOID : isSetoid D} (f : D -> D) : ensemble D :=
  fun x => x == f x.

#[global]
Instance fixedpointsOf_eqPropCompatible1 {D : Type} `{SETOID : isSetoid D}
  : eqPropCompatible1 (@fixedpointsOf D SETOID).
Proof.
  intros f1 f2 f1_eq_f2 x. unfold fixedpointsOf. unfold "\in".
  change (forall x, f1 x == f2 x) in f1_eq_f2. now rewrite f1_eq_f2.
Qed.

Definition prefixedpointsOf {D : Type} `{POSET : isPoset D} (f : D -> D) : ensemble D :=
  fun x => x >= f x.

Definition postfixedpointsOf {D : Type} `{POSET : isPoset D} (f : D -> D) : ensemble D :=
  fun x => x =< f x.

Definition upperboundsOf {D : Type} `{POSET : isPoset D} (X : ensemble D) : ensemble D :=
  fun u => forall x : D, forall IN : x \in X, x =< u.

Definition lowerboundsOf {D : Type} `{POSET : isPoset D} (X: ensemble D) : ensemble D :=
  fun l => forall x : D, forall IN : x \in X, x >= l.

Definition is_supremum_of {D : Type} `{POSET : isPoset D} (sup_X : D) (X : ensemble D) : Prop :=
  forall u : D, sup_X =< u <-> u \in upperboundsOf X.

Definition is_infimum_of {D : Type} `{POSET : isPoset D} (inf_X : D) (X : ensemble D) : Prop :=
  forall l : D, inf_X >= l <-> l \in lowerboundsOf X.

#[global]
Add Parametric Morphism {D : Type} `{SETOID : isSetoid D}
  : fixedpointsOf with signature (eqProp ==> eqProp)
  as fixedpointsOf_compatWith_eqProp.
Proof.
  intros f1 f2 f1_eq_f2. unfold fixedpointsOf. cbn. unfold "\in". intros x. split; intros EQ.
  - transitivity (f1 x); [exact EQ | exact (f1_eq_f2 x)].
  - transitivity (f2 x); [exact EQ | symmetry; exact (f1_eq_f2 x)].
Qed.

#[local] Hint Unfold fixedpointsOf prefixedpointsOf postfixedpointsOf upperboundsOf lowerboundsOf is_supremum_of is_infimum_of : simplication_hints.

Context {D : Type} `{POSET : isPoset D}.

#[local] Existing Instance pi_isPoset.

#[global]
Instance prefixecpointsOf_eqPropCompatible1
  : eqPropCompatible1 (@prefixedpointsOf D POSET).
Proof.
  intros f1 f2 f1_eq_f2 x. unfold prefixedpointsOf. unfold "\in".
  change (forall x, f1 x == f2 x) in f1_eq_f2. now rewrite f1_eq_f2.
Qed.

#[global]
Instance postfixedpointsOf_eqPropCompatible1
  : eqPropCompatible1 (@postfixedpointsOf D POSET).
Proof.
  intros f1 f2 f1_eq_f2 x. unfold postfixedpointsOf. unfold "\in".
  change (forall x, f1 x == f2 x) in f1_eq_f2. now rewrite f1_eq_f2.
Qed.

Lemma prefixedpointsOf_decreasing (f1 : D -> D) (f2 : D -> D)
  (LE : f1 =< f2)
  : prefixedpointsOf f2 =< prefixedpointsOf f1.
Proof.
  intros x. unfold prefixedpointsOf, "\in". i.
  change (forall x, f1 x =< f2 x) in LE. now rewrite -> LE.
Qed.

Lemma postfixedpointsOf_increasing (f1 : D -> D) (f2 : D -> D)
  (LE : f1 =< f2)
  : postfixedpointsOf f1 =< postfixedpointsOf f2.
Proof.
  intros x. unfold postfixedpointsOf, "\in". i.
  change (forall x, f1 x =< f2 x) in LE. now rewrite <- LE.
Qed.

#[global]
Add Parametric Morphism
  : (@upperboundsOf D POSET) with signature (eqProp ==> eqProp)
  as upperboundsOf_compatWith_eqProp.
Proof.
  intros X1 X2 X_EQ. done!.
Qed.

#[global]
Add Parametric Morphism
  : (@lowerboundsOf D POSET) with signature (eqProp ==> eqProp)
  as lowerboundsOf_compatWith_eqProp.
Proof.
  intros X1 X2 X_EQ. done!.
Qed.

#[global]
Add Parametric Morphism
  : (@is_supremum_of D POSET) with signature (eqProp ==> eqProp ==> iff)
  as is_supremum_of_compatWith_eqProp.
Proof.
  intros sup_X1 sup_X2 sup_EQ X1 X2 X_EQ; unfold is_supremum_of. split; intros UPPERBOUND ?.
  - rewrite <- X_EQ, <- sup_EQ. eauto.
  - rewrite -> X_EQ, -> sup_EQ. eauto.
Qed.

#[global]
Add Parametric Morphism
  : (@is_infimum_of D POSET) with signature (eqProp ==> eqProp ==> iff)
  as is_infimum_of_compatWith_eqProp.
Proof.
  intros inf_X1 inf_X2 inf_EQ X1 X2 X_EQ; unfold is_infimum_of. split; intros UPPERBOUND ?.
  - rewrite <- X_EQ, <- inf_EQ. eauto.
  - rewrite -> X_EQ, -> inf_EQ. eauto.
Qed.

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

Lemma is_supremum_of_congruence sup_X1 sup_X2 X1 X2
  (SUPREMUM : is_supremum_of sup_X1 X1)
  (sup_EQ : sup_X1 == sup_X2)
  (X_EQ : X1 == X2)
  : is_supremum_of sup_X2 X2.
Proof.
  now rewrite sup_EQ, X_EQ in SUPREMUM.
Qed.

#[local] Hint Resolve is_supremum_of_congruence : poset_hints.

Definition map_suprema (Xs : ensemble (ensemble D)) : ensemble D :=
  Xs >>= fun X_i => fun sup_X_i => is_supremum_of sup_X_i X_i.

Lemma in_map_suprema_iff Xs sup
  : sup \in map_suprema Xs <-> (exists X_i, X_i \in Xs /\ is_supremum_of sup X_i).
Proof.
  reflexivity.
Qed.

Lemma supremum_of_map_suprema_ge_suprema (sup : D) (Xs : ensemble (ensemble D)) (sup_X : D) (X : ensemble D)
  (SUPREMUM : is_supremum_of sup (map_suprema Xs))
  (IN : X \in Xs)
  (SUPREMUM' : is_supremum_of sup_X X)
  : sup_X =< sup.
Proof with eauto with *.
  eapply SUPREMUM... rewrite in_map_suprema_iff...
Qed.

#[local] Hint Resolve supremum_of_map_suprema_ge_suprema : poset_hints.

Theorem supremum_of_map_suprema_is_supremum_of_unions (Xs : ensemble (ensemble D)) (sup : D)
  (SUPS_EXIST : forall X, X \in Xs -> exists sup_X, is_supremum_of sup_X X)
  : is_supremum_of sup (map_suprema Xs) <-> is_supremum_of sup (E.unions Xs).
Proof with eauto with *.
  split; intros H_supremum z; split; ii.
  - rewrite E.in_unions_iff in IN. destruct IN as [X_i [x_in_X_i X_i_in_Xs]].
    pose proof (SUPS_EXIST X_i X_i_in_Xs) as [sup_X_i sup_X_i_isSupremumOf_X_i].
    transitivity sup_X_i.
    + eapply sup_X_i_isSupremumOf_X_i...
    + transitivity sup...
  - eapply H_supremum. intros sup_X_i sup_X_i_in_MapSuprema.
    rewrite in_map_suprema_iff in sup_X_i_in_MapSuprema.
    destruct sup_X_i_in_MapSuprema as [X_i [X_i_in_Xs sup_X_i_isSupremumOf_X_i]].
    eapply sup_X_i_isSupremumOf_X_i. ii. eapply H. rewrite E.in_unions_iff...
  - rewrite in_map_suprema_iff in IN. destruct IN as [X [X_in_Xs sup_X_isSupremumOf_X]].
    rename x into sup_X. enough (to_show : sup_X =< sup) by now transitivity sup.
    eapply sup_X_isSupremumOf_X. ii. eapply H_supremum... rewrite E.in_unions_iff...
  - eapply H_supremum. ii. rewrite E.in_unions_iff in IN.
    destruct IN as [X [x_in_X X_in_Xs]]. pose proof (SUPS_EXIST X X_in_Xs) as [sup_X sup_X_isSupremumOf_X].
    transitivity sup_X.
    + eapply sup_X_isSupremumOf_X...
    + eapply H; rewrite in_map_suprema_iff...
Qed.

Theorem infimum_of_upperbounds_is_supremum (sup_X : D) (X : ensemble D)
  : is_supremum_of sup_X X <-> is_infimum_of sup_X (upperboundsOf X).
Proof with eauto with *.
  split.
  - intros sup_X_isSupremumOf_X z. split; ii.
    + rewrite H. eapply sup_X_isSupremumOf_X...
    + eapply H, sup_X_isSupremumOf_X...
  - intros H_supremum z. split; ii.
    + rewrite <- H. eapply H_supremum.
      intros upper_bound upper_bound_in.
      exact (upper_bound_in x IN).
    + eapply H_supremum...
Qed.

Theorem supremum_of_lowerbounds_is_infimum (inf_X : D) (X : ensemble D)
  : is_infimum_of inf_X X <-> is_supremum_of inf_X (lowerboundsOf X).
Proof with eauto with *.
  split.
  - intros inf_X_isInfimumOf_X z. split; ii.
    + rewrite <- H. eapply inf_X_isInfimumOf_X...
    + eapply H, inf_X_isInfimumOf_X...
  - intros H_infimum z. split; ii.
    + rewrite H. eapply H_infimum .
      intros lower_bound lower_bound_in. unnw.
      exact (lower_bound_in x IN).
    + unnw. eapply H_infimum...
Qed.

Lemma infimum_monotonic (X1 : ensemble D) (X2 : ensemble D) (inf_X1 : D) (inf_X2 : D)
  (INFIMUM1 : is_infimum_of inf_X1 X1)
  (INFIMUM2 : is_infimum_of inf_X2 X2)
  (SUBSETEQ : X1 \subseteq X2)
  : inf_X2 =< inf_X1.
Proof.
  eapply INFIMUM1; ii.
  eapply INFIMUM2; eauto with *.
Qed.

#[local] Hint Resolve infimum_monotonic : poset_hints.

Lemma infimum_unique (X1 : ensemble D) (X2 : ensemble D) (inf_X1 : D) (inf_X2 : D)
  (INFIMUM1 : is_infimum_of inf_X1 X1)
  (INFIMUM2 : is_infimum_of inf_X2 X2)
  (EQ : X1 == X2)
  : inf_X1 == inf_X2.
Proof.
  pose proof (eqProp_implies_leProp X1 X2 EQ) as claim1. symmetry in EQ.
  pose proof (eqProp_implies_leProp X2 X1 EQ) as claim2. eapply leProp_antisymmetry; eauto with *.
Qed.

Lemma infimum_congruence (inf_X : D) (inf_Y : D) (X : ensemble D) (Y : ensemble D)
  (inf_EQ : inf_X == inf_Y)
  (EQ : X == Y)
  (INFIMUM : is_infimum_of inf_X X)
  : is_infimum_of inf_Y Y.
Proof with eauto with *.
  intros z. unnw. rewrite <- inf_EQ. split.
  - intros z_le_inf_X. rewrite <- EQ. eapply INFIMUM...
  - intros z_isLowerBoundOf_Y. eapply INFIMUM. rewrite -> EQ...
Qed.

#[local] Hint Resolve infimum_unique infimum_congruence : core.

Definition is_lfpOf (lfp : D) (f : D -> D) : Prop :=
  lfp \in fixedpointsOf f /\ lfp \in lowerboundsOf (fixedpointsOf f).

Definition is_gfpOf (gfp : D) (f : D -> D) : Prop :=
  gfp \in fixedpointsOf f /\ gfp \in upperboundsOf (fixedpointsOf f).

#[local] Hint Unfold is_lfpOf is_gfpOf : poset_hints.

Theorem lfpOf_Monotnoic (f : D -> D) (lfp : D)
  (MONOTONIC : isMonotonic1 f)
  (INFIMUM : is_infimum_of lfp (prefixedpointsOf f))
  : is_lfpOf lfp f.
Proof with eauto with *.
  assert (claim1 : forall x, x \in fixedpointsOf f -> lfp =< x).
  { intros x H_IN. transitivity (f x).
    - eapply INFIMUM... eapply MONOTONIC...
    - eapply eqProp_implies_leProp...
  }
  assert (claim2 : f lfp =< lfp).
  { eapply INFIMUM. ii. transitivity (f x); trivial.
    eapply MONOTONIC, INFIMUM...
  }
  assert (claim3 : lfp =< f lfp).
  { eapply INFIMUM... eapply MONOTONIC... }
  split... eapply leProp_antisymmetry...
Qed.

Lemma gfpOf_Monotnoic (f : D -> D) (gfp : D)
  (MONOTONIC : isMonotonic1 f)
  (SUPREMUM : is_supremum_of gfp (postfixedpointsOf f))
  : is_gfpOf gfp f.
Proof with eauto with *.
  assert (claim1 : gfp =< f gfp).
  { eapply SUPREMUM... ii. transitivity (f x); trivial.
    eapply MONOTONIC, SUPREMUM...
  }
  assert (claim2 : f gfp =< gfp).
  { eapply SUPREMUM... eapply MONOTONIC... }
  split.
  - eapply leProp_antisymmetry...
  - intros fix_f H_in.
    eapply SUPREMUM...
    eapply eqProp_implies_leProp...
Qed.

Definition isSupremumIn (sup : D) (X : ensemble D) (phi : D -> Prop) : Prop :=
  phi sup /\ (forall upper_bound : { d : D | phi d }, sup =< (proj1_sig upper_bound) <-> proj1_sig upper_bound \in upperboundsOf X).

Theorem isSupremumIn_iff (phi : D -> Prop) (sup_X : @sig D phi) (X : ensemble (@sig D phi))
  : isSupremumIn (proj1_sig sup_X) (E.image (@proj1_sig D phi) X) phi <-> is_supremum_of sup_X X.
Proof with eauto with *. 
  split.
  { intros [? ?] z; split.
    - ii. eapply H0... rewrite E.in_image_iff...
    - ii. eapply H0.
      intros x H_in_image. rewrite E.in_image_iff in H_in_image.
      destruct H_in_image as [[x' phi_x] [x_eq x_in]]. simpl in x_eq; subst x'.
      change (@exist D phi x phi_x =< z)...
  }
  { intros sup_X_isSupremumOf_X. split.
    - property sup_X.
    - split; ii.
      + rewrite E.in_image_iff in IN. destruct IN as [[x' phi_x] [x_eq x_in]].
        simpl in x_eq; subst x'. rewrite <- H.
        change (@exist D phi x phi_x =< sup_X). eapply sup_X_isSupremumOf_X...
      + change (sup_X =< upper_bound). eapply sup_X_isSupremumOf_X.
        intros x x_in. change (proj1_sig x =< proj1_sig upper_bound).
        eapply H; rewrite E.in_image_iff...
  }
Qed.

End BASIC1.

#[local, program]
Instance direct_product_of_Poset {A : Type} {B : Type} (A_isPoset : isPoset A) (B_isPoset : isPoset B) : isPoset (A * B) :=
  { leProp lhs rhs := fst lhs =< fst rhs /\ snd lhs =< snd rhs
  ; Poset_isSetoid := directProduct_of_two_Setoids A_isPoset.(Poset_isSetoid) B_isPoset.(Poset_isSetoid)
  }.
Next Obligation.
  split.
  - intros p1. split; reflexivity.
  - intros p1 p2 p3 LE LE'. split; eapply leProp_trans. 
    + exact (proj1 LE).
    + exact (proj1 LE').
    + exact (proj2 LE).
    + exact (proj2 LE').
Defined.
Next Obligation.
  intros p1 p2. unfold flip. cbn. split.
  - intros EQ. split; split.
    + eapply eqProp_implies_leProp. exact (proj1 EQ).
    + eapply eqProp_implies_leProp. exact (proj2 EQ).
    + eapply eqProp_implies_leProp. eapply eqProp_sym. exact (proj1 EQ).
    + eapply eqProp_implies_leProp. eapply eqProp_sym. exact (proj2 EQ).
  - intros EQ. split; eapply leProp_antisymmetry.
    + exact (proj1 (proj1 EQ)).
    + exact (proj1 (proj2 EQ)).
    + exact (proj2 (proj1 EQ)).
    + exact (proj2 (proj2 EQ)).
Defined.

Module Cola.

#[local] Existing Instance pi_isPoset.

Notation "`[ A -> B ]" := { f : A -> B | isMonotonic1 f }.

Class isCola (D : Type) {POSET : isPoset D} : Type :=
  supremum_cola (X : ensemble D) : { sup_X : D | is_supremum_of sup_X X }.

End Cola.

Module Cpo.

Import ListNotations.

#[local] Existing Instance pi_isPoset.

Notation "`[ A -> B ]" := { f : A -> B | isContinuous f }.

Variant isDirected {D : Type} `{POSET : isPoset D} (X : ensemble D) : Prop :=
  | isDirected_intro 
    (NONEMPTY : exists x0, x0 \in X)
    (DIRECTED' : forall x1, forall x2, forall x1_IN : x1 \in X, forall x2_IN : x2 \in X, exists x3, x3 \in X /\ (x1 =< x3 /\ x2 =< x3))
    : isDirected X.

#[local] Hint Constructors isDirected : poset_hints.

Lemma isDirected_iff {D : Type} `{POSET : isPoset D} (X : ensemble D)
  : isDirected X <-> (forall xs, L.is_finsubset_of xs X -> exists y, y \in X /\ (forall x, L.In x xs -> x =< y)).
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
  - intros y1 y2 y1_IN y2_IN. s!. destruct y1_IN as [x1 [-> x1_in]], y2_IN as [x2 [-> x2_in]].
    pose proof (DIRECTED' x1 x2 x1_in x2_in) as [x3 [x3_in [x1_le_x3 x2_le_x3]]]. exists (f x3). done!.
Qed.

Class isCpo (D : Type) {POSET : isPoset D} : Type :=
  { bottom_cpo : D
  ; supremum_cpo (X : ensemble D) (DIRECTED : isDirected X) : D
  ; bottom_cpo_spec : forall x : D, bottom_cpo =< x
  ; supremum_cpo_spec (X : ensemble D) (DIRECTED : isDirected X) : is_supremum_of (supremum_cpo X DIRECTED) X
  }.

End Cpo.

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

#[global] Hint Resolve compare_Lt compare_Eq compare_Gt : poset_hints.

Lemma compare_spec {A : Type} {POSET : isPoset A} {ORD : hsOrd A (POSET := POSET)} (lhs : A) (rhs : A) :
  match compare lhs rhs with
  | Lt => lhs =< rhs /\ ~ lhs == rhs
  | Eq => lhs == rhs
  | Gt => rhs =< lhs /\ ~ lhs == rhs
  end.
Proof.
  destruct (compare lhs rhs) eqn: H_compare_result; eauto with *.
Qed.

Section list_hsOrd.

Context {A : Type} {POSET : isPoset A} {ORD : hsOrd A (POSET := POSET)}.

Fixpoint lex_compare (xs : list A) (ys : list A) {struct xs} : comparison :=
  match xs, ys with
  | [], [] => Eq
  | [], y :: ys => Lt
  | x :: xs, [] => Gt
  | x :: xs, y :: ys =>
    match compare x y with
    | Lt => Lt
    | Eq => lex_compare xs ys
    | Gt => Gt
    end
  end.

Definition lex_eq lhs rhs : Prop :=
  lex_compare lhs rhs = Eq.

Definition lex_le lhs rhs : Prop :=
  lex_compare lhs rhs = Lt \/ lex_compare lhs rhs = Eq.

#[global]
Instance lex_eq_Equivalence
  : Equivalence lex_eq.
Proof with discriminate || eauto with *.
  unfold lex_eq. split.
  - intros xs1; induction xs1 as [ | x1 xs1 IH]; simpl...
    pose proof (claim1 := compare_spec x1 x1).
    destruct (compare x1 x1) eqn: H_compare_result1...
    all: contradiction (proj2 claim1)...
  - intros xs1 xs2; revert xs1 xs2; induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl...
    pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x1).
    destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x1) eqn: H_compare_result2...
    all: contradiction (proj2 claim2)...
  - intros xs1 xs2 xs3; revert xs1 xs3; induction xs2 as [ | x2 xs2 IH]; destruct xs1 as [ | x1 xs1]; destruct xs3 as [ | x3 xs3]; simpl...
    pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x3); pose proof (claim3 := compare_spec x1 x3).
    destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x3) eqn: H_compare_result2; destruct (compare x1 x3) eqn: H_compare_result3...
    all: contradiction (proj2 claim3)...
Qed.

#[local]
Instance list_isSetoid_of_elementwise_comparison : isSetoid (list A) :=
  { eqProp := lex_eq
  ; eqProp_Equivalence := lex_eq_Equivalence
  }.

#[local]
Instance lex_le_PreOrder
  : PreOrder lex_le.
Proof with discriminate || eauto with *.
  assert (lemma1 : forall x1 : A, forall x2 : A, x1 =< x2 -> x2 =< x1 -> x1 == x2). { ii... }
  assert (lemma2 : forall x1 : A, forall x2 : A, x1 == x2 -> x1 =< x2). { ii... }
  assert (lemma3 : forall x1 : A, forall x2 : A, x1 == x2 -> x2 =< x1). { ii... }
  unfold lex_le. split.
  - intros xs1; right. eapply lex_eq_Equivalence.
  - intros xs1 xs2 xs3; revert xs1 xs3; induction xs2 as [ | x2 xs2 IH]; destruct xs1 as [ | x1 xs1]; destruct xs3 as [ | x3 xs3]; simpl...
    intros [H_false | H_false]...
    pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x3); pose proof (claim3 := compare_spec x1 x3); pose proof (claim4 := IH xs1 xs3).
    destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x3) eqn: H_compare_result2; destruct (compare x1 x3) eqn: H_compare_result3...
    + contradiction (proj2 claim3)...
    + contradiction (proj2 claim2)...
    + contradiction (proj2 claim3); eapply lemma1; [transitivity x2 | exact (proj1 claim3)]. eapply lemma2... exact (proj1 claim2).
    + contradiction (proj2 claim2)...
    + contradiction (proj2 claim1)...
    + contradiction (proj2 claim3); eapply lemma1; [transitivity x2 | exact (proj1 claim3)]. exact (proj1 claim1). eapply lemma2...
    + contradiction (proj2 claim1); eapply lemma1; [exact (proj1 claim1) | transitivity x3]. exact (proj1 claim2). eapply lemma2...
    + contradiction (proj2 claim1); eapply lemma1; [exact (proj1 claim1) | transitivity x3]. exact (proj1 claim2). exact (proj1 claim3).
    + intros ? [? | ?]...
    + intros [? | ?]...
    + intros [? | ?]...
    + intros [? | ?]...
Qed.

Lemma lex_le_flip_spec lhs rhs :
  match lex_compare lhs rhs with
  | Lt => lex_compare rhs lhs = Gt
  | Eq => lex_compare rhs lhs = Eq
  | Gt => lex_compare rhs lhs = Lt
  end.
Proof with discriminate || eauto with *.
  revert lhs rhs.
  assert (lemma1 : forall x1 : A, forall x2 : A, x1 =< x2 -> x2 =< x1 -> x1 == x2). { ii... }
  assert (lemma2 : forall x1 : A, forall x2 : A, x1 == x2 -> x1 =< x2). { ii... }
  assert (lemma3 : forall x1 : A, forall x2 : A, x1 == x2 -> x2 =< x1). { ii... }
  assert (lemma4 : forall xs1 : list A, forall xs2 : list A, lex_compare xs1 xs2 = Lt <-> lex_compare xs2 xs1 = Gt).
  { induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl... split...
    pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x1); pose proof (claim3 := IH xs2).
    destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x1) eqn: H_compare_result2...
    - contradiction (proj2 claim2)...
    - contradiction (proj2 claim2)...
    - contradiction (proj2 claim1)...
    - contradiction (proj2 claim1). eapply lemma1; [exact (proj1 claim1) | exact (proj1 claim2)].
    - contradiction (proj2 claim1)...
    - contradiction (proj2 claim1). eapply lemma1; [exact (proj1 claim2) | exact (proj1 claim1)].
  }
  assert (lemma5 : forall xs1 : list A, forall xs2 : list A, lex_compare xs1 xs2 = Eq <-> lex_compare xs2 xs1 = Eq).
  { induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl... split... split...
    pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x1); pose proof (claim3 := IH xs2).
    destruct (compare x1 x2) eqn: H_compare_result1; destruct (compare x2 x1) eqn: H_compare_result2...
    - contradiction (proj2 claim2)...
    - contradiction (proj2 claim2)...
    - contradiction (proj2 claim1)...
    - split...
    - contradiction (proj2 claim1)...
    - split...
  }
  assert (lemma6 : forall xs1 : list A, forall xs2 : list A, lex_compare xs1 xs2 = Gt <-> lex_compare xs2 xs1 = Lt) by firstorder.
  intros lhs rhs; destruct (lex_compare lhs rhs) eqn: H_compare_result; now firstorder.
Qed.

Corollary lex_le_flip_iff lhs rhs OBS :
  lex_compare lhs rhs = OBS <->
  match OBS with
  | Lt => lex_compare rhs lhs = Gt
  | Eq => lex_compare rhs lhs = Eq
  | Gt => lex_compare rhs lhs = Lt
  end.
Proof.
  split.
  - ii; subst OBS. exact (lex_le_flip_spec lhs rhs).
  - pose proof (lex_le_flip_spec rhs lhs) as claim1. intros H_eq.
    destruct OBS eqn: H_compare_result; now rewrite H_eq in claim1.
Qed.

#[local]
Instance lex_le_PartialOrder
  : PartialOrder lex_eq lex_le.
Proof with discriminate || eauto with *.
  intros xs1 xs2; cbn. unfold flip, lex_eq, lex_le.
  pose proof (claim1 := lex_le_flip_spec xs1 xs2).
  destruct (lex_compare xs1 xs2) eqn: H_compare_result.
  - split...
  - split... intros [? [H_false | H_false]].
    all: rewrite H_false in claim1...
  - split... intros [[? | ?] ?]...
Qed.

#[local]
Instance list_lexicographical_order : isPoset (list A) :=
  { leProp := lex_le
  ; Poset_isSetoid := list_isSetoid_of_elementwise_comparison
  ; leProp_PreOrder := lex_le_PreOrder
  ; leProp_PartialOrder := lex_le_PartialOrder
  }.

#[local] Obligation Tactic := cbn; unfold lex_le, lex_eq; ii.

#[global, program]
Instance list_hsOrd : hsOrd (list A) (POSET := list_lexicographical_order) :=
  { compare := lex_compare }.
Next Obligation.
  rewrite OBS_Lt. split; [now left | congruence].
Qed.
Next Obligation.
  exact OBS_Eq.
Qed.
Next Obligation.
  pose proof (lex_le_flip_spec x y) as H; revert H; rewrite OBS_Gt; intros H_lt. rewrite H_lt. split; [now left | congruence].
Qed.

End list_hsOrd.
