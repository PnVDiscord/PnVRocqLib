Require Import PnV.Prelude.Prelude.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.
#[local] Obligation Tactic := i.

Create HintDb poset_hints.

Lemma well_founded_implies_Irreflexive {A : Type} (R : A -> A -> Prop)
  (WF : well_founded R)
  : Irreflexive R.
Proof.
  intros x H_R. induction (WF x) as [x _ IH]. eapply IH with (y := x); exact H_R.
Qed.

#[program]
Definition mkProsetFrom_ltProp {A : Type} (ltProp : A -> A -> Prop) (ltProp_StrictOrder : StrictOrder ltProp) : isProset A :=
  {| leProp x y := ltProp x y \/ x = y; Proset_isSetoid := mkSetoid_from_eq; |}.
Next Obligation.
  split; ii; firstorder try congruence.
Qed.
Next Obligation.
  intros x y. cbn. unfold flip. split; firstorder try congruence. contradiction (StrictOrder_Irreflexive x). firstorder.
Qed.

#[universes(template)]
Class isPoset (A : Type) : Type :=
  { Poset_isProset :: isProset A
  ; Poset_eqProp_spec (x : A) (y : A)
    : x == y <-> x = y
  }.

Infix "≦" := (leProp (isProset := Poset_isProset)) : type_scope.

Lemma eqPropCompatible_dom_isPoset {A : Type} {B : Type} `{A_isPoset : isPoset A} `{B_isSetoid : isSetoid B}
  : forall f : A -> B, eqPropCompatible1 f.
Proof.
  ii. rewrite Poset_eqProp_spec in x_EQ. now rewrite x_EQ.
Qed.

#[global]
Instance mkProsetFrom_ltProp_isPoset {A : Type} {ltProp : A -> A -> Prop} (ltProp_StrictOrder : StrictOrder ltProp) : isPoset A :=
  { Poset_isProset := mkProsetFrom_ltProp ltProp ltProp_StrictOrder
  ; Poset_eqProp_spec x y := conj (fun H : x = y => H) (fun H : x = y => H)
  }.

#[universes(polymorphic=yes)]
Class has_ltProp@{u} (A : Type@{u}) : Type@{u} :=
  ltProp (lhs : A) (rhs : A) : Prop.

Infix "≨" := ltProp : type_scope.

#[universes(template)]
Class hasStrictOrder (A : Type) : Type :=
  { lt :: has_ltProp A
  ; lt_StrictOrder :: StrictOrder lt
  }.

#[global]
Instance mkPoset_fromStrictOrder {A : Type} `{STRICT_ORDER : hasStrictOrder A} : isPoset A :=
  @mkProsetFrom_ltProp_isPoset A lt lt_StrictOrder.

Lemma lt_iff_le_ne {A : Type} `{STRICT_ORDER : hasStrictOrder A} (x : A) (y : A)
  : x ≨ y <-> (x ≦ y /\ x <> y).
Proof.
  split.
  - intros H_LT. split.
    + left. exact H_LT.
    + intros ->. revert H_LT. eapply StrictOrder_Irreflexive.
  - intros [[H_LT | H_EQ] H_NE].
    + exact H_LT.
    + contradiction (H_NE H_EQ).
Qed.

Lemma le_iff_lt_eq {A : Type} `{STRICT_ORDER : hasStrictOrder A} (x : A) (y : A)
  : x ≦ y <-> (x ≨ y \/ x = y).
Proof.
  reflexivity.
Qed.

#[projections(primitive)]
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

#[global, program]
Instance subWwellPoset {A : Type} {P : A -> Prop} (WPOSET : isWellPoset A) : isWellPoset { x : A | P x } :=
  { wltProp := binary_relation_on_image wltProp (@proj1_sig A P) }.
Next Obligation.
  intros x1 x2 x3 H_1LE2 H_2LE3. exact (wltProp_Transitive (proj1_sig x1) (proj1_sig x2) (proj1_sig x3) H_1LE2 H_2LE3).
Defined.
Next Obligation.
  eapply relation_on_image_liftsWellFounded. exact wltProp_well_founded.
Defined.

Definition wleProp {A : Type} `{WPOSET : isWellPoset A} : forall lhs : A, forall rhs : A, Prop :=
  leProp (isProset := Poset_isProset (isPoset := mkProsetFrom_ltProp_isPoset (ltProp := wltProp) wltProp_StrictOrder)).

Infix "⪳" := wleProp : type_scope.

#[local] Hint Resolve Equivalence_Reflexive Equivalence_Symmetric Equivalence_Transitive : poset_hints.
#[local] Hint Resolve eqProp_refl eqProp_sym eqProp_trans leProp_refl leProp_trans leProp_antisymmetry eqProp_implies_leProp : poset_hints.

Section BASIC1.

Lemma leProp_unfold {A : Type} `{PROSET : isProset A} (x : A) (y : A)
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

Definition isChain {D : Type} `{PROSET : isProset D} (X : ensemble D) : Prop :=
  forall x1, forall x2, x1 \in X -> x2 \in X -> (x1 =< x2 \/ x1 >= x2).

Definition prefixedpointsOf {D : Type} `{PROSET : isProset D} (f : D -> D) : ensemble D :=
  fun x => x >= f x.

Definition postfixedpointsOf {D : Type} `{PROSET : isProset D} (f : D -> D) : ensemble D :=
  fun x => x =< f x.

Definition upperboundsOf {D : Type} `{PROSET : isProset D} (X : ensemble D) : ensemble D :=
  fun u => forall x : D, forall IN : x \in X, x =< u.

Definition lowerboundsOf {D : Type} `{PROSET : isProset D} (X : ensemble D) : ensemble D :=
  fun l => forall x : D, forall IN : x \in X, x >= l.

Definition is_supremum_of {D : Type} `{PROSET : isProset D} (sup_X : D) (X : ensemble D) : Prop :=
  forall u : D, sup_X =< u <-> u \in upperboundsOf X.

Definition is_infimum_of {D : Type} `{PROSET : isProset D} (inf_X : D) (X : ensemble D) : Prop :=
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

Context {D : Type} `{PROSET : isProset D}.

#[local] Existing Instance pi_isProset.

#[global]
Instance prefixecpointsOf_eqPropCompatible1
  : eqPropCompatible1 (@prefixedpointsOf D PROSET).
Proof.
  done!.
Qed.

#[global]
Instance postfixedpointsOf_eqPropCompatible1
  : eqPropCompatible1 (@postfixedpointsOf D PROSET).
Proof.
  done!.
Qed.

Lemma prefixedpointsOf_decreasing (f1 : D -> D) (f2 : D -> D)
  (LE : f1 =< f2)
  : prefixedpointsOf f1 >= prefixedpointsOf f2.
Proof.
  done!.
Qed.

Lemma postfixedpointsOf_increasing (f1 : D -> D) (f2 : D -> D)
  (LE : f1 =< f2)
  : postfixedpointsOf f1 =< postfixedpointsOf f2.
Proof.
  done!.
Qed.

#[global]
Add Parametric Morphism
  : (@upperboundsOf D PROSET) with signature (eqProp ==> eqProp)
  as upperboundsOf_compatWith_eqProp.
Proof.
  done!.
Qed.

#[global]
Add Parametric Morphism
  : (@lowerboundsOf D PROSET) with signature (eqProp ==> eqProp)
  as lowerboundsOf_compatWith_eqProp.
Proof.
  done!.
Qed.

#[global]
Add Parametric Morphism
  : (@is_supremum_of D PROSET) with signature (eqProp ==> eqProp ==> iff)
  as is_supremum_of_compatWith_eqProp.
Proof.
  intros sup_X1 sup_X2 sup_EQ X1 X2 X_EQ; unfold is_supremum_of. split; intros UPPERBOUND ?.
  - rewrite <- X_EQ, <- sup_EQ; eauto.
  - rewrite -> X_EQ, -> sup_EQ; eauto.
Qed.

#[global]
Add Parametric Morphism
  : (@is_infimum_of D PROSET) with signature (eqProp ==> eqProp ==> iff)
  as is_infimum_of_compatWith_eqProp.
Proof.
  intros inf_X1 inf_X2 inf_EQ X1 X2 X_EQ; unfold is_infimum_of. split; intros UPPERBOUND ?.
  - rewrite <- X_EQ, <- inf_EQ; eauto.
  - rewrite -> X_EQ, -> inf_EQ; eauto.
Qed.

Lemma supremum_is_infimum_of_its_upperbounds X sup_X
  (SUPREMUM : is_supremum_of sup_X X)
  : is_infimum_of sup_X (E.singleton sup_X).
Proof.
  ii; split; done!.
Qed.

Lemma supremum_monotonic sup_X1 sup_X2 X1 X2
  (SUPREMUM1 : is_supremum_of sup_X1 X1)
  (SUPREMUM2 : is_supremum_of sup_X2 X2)
  (SUBSET : X1 \subseteq X2)
  : sup_X1 =< sup_X2.
Proof.
  eapply SUPREMUM1; ii; eapply SUPREMUM2; done!.
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

Lemma supremum_congruence sup_X1 sup_X2 X1 X2
  (SUPREMUM : is_supremum_of sup_X1 X1)
  (sup_EQ : sup_X1 == sup_X2)
  (X_EQ : X1 == X2)
  : is_supremum_of sup_X2 X2.
Proof.
  now rewrite sup_EQ, X_EQ in SUPREMUM.
Qed.

#[local] Hint Resolve supremum_congruence : poset_hints.

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
    + eapply H_infimum...
Qed.

Lemma infimum_monotonic (X1 : ensemble D) (X2 : ensemble D) (inf_X1 : D) (inf_X2 : D)
  (INFIMUM1 : is_infimum_of inf_X1 X1)
  (INFIMUM2 : is_infimum_of inf_X2 X2)
  (SUBSETEQ : X1 \subseteq X2)
  : inf_X2 =< inf_X1.
Proof.
  eapply INFIMUM1; ii; eapply INFIMUM2; eauto with *.
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

Theorem prefixedpoint_is_lfpOf (f : D -> D) (lfp : D)
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

Lemma postfixedpoint_is_gfpOf (f : D -> D) (gfp : D)
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

Definition is_supremum_in (sup : D) (X : ensemble D) (phi : D -> Prop) : Prop :=
  phi sup /\ (forall upper_bound : { d : D | phi d }, sup =< (proj1_sig upper_bound) <-> proj1_sig upper_bound \in upperboundsOf X).

Theorem is_supremum_in_iff (phi : D -> Prop) (sup_X : @sig D phi) (X : ensemble (@sig D phi))
  : is_supremum_in (proj1_sig sup_X) (E.image (@proj1_sig D phi) X) phi <-> is_supremum_of sup_X X.
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

#[projections(primitive), universes(template)]
Class isWoset (A : Type) {SETOID : isSetoid A} : Type :=
  { Woset_isWellPoset :: isWellPoset A
  ; Woset_eqPropCompatible2 :: eqPropCompatible2 wltProp
  ; Woset_ext_eq (x : A) (y : A)
    (EXT_EQ : forall z : A, wltProp z x <-> wltProp z y)
    : x == y
  }.

Definition wlt {A : Type} {SETOID : isSetoid A} {WOSET : isWoset A} (x : A) (y : A) : Prop :=
  wltProp (isWellPoset := @Woset_isWellPoset A SETOID WOSET) x y.

#[global] Infix "≺" := wlt.

Lemma Woset_extensional {A : Type} {SETOID : isSetoid A} {WOSET : isWoset A} (x : A) (y : A)
  : x == y <-> (forall z, wlt z x <-> wlt z y).
Proof.
  split; intros EQ.
  - intros z. split; intros H_LT.
    + eapply Woset_eqPropCompatible2; cycle -1; eauto with *.
    + eapply Woset_eqPropCompatible2; cycle -1; eauto with *.
  - eapply Woset_ext_eq. exact EQ.
Qed.

#[global]
Add Parametric Morphism {A : Type} {SETOID : isSetoid A} {WOSET : @isWoset A SETOID}
  : (@wlt A SETOID WOSET) with signature (eqProp ==> eqProp ==> iff)
  as Woset_wlt_eqProp.
Proof.
  intros a1 b1 EQ1 a2 b2 EQ2. split; intros H_lt.
  - eapply Woset_eqPropCompatible2; eauto; symmetry; eauto.
  - eapply Woset_eqPropCompatible2; eauto.
Qed.

Module O.

#[projections(primitive)]
Record Ord : Type :=
  { carrier :> Type
  ; carrier_isSetoid : isSetoid carrier
  ; carrier_isWoset : isWoset carrier
  }.

#[global] Existing Instance carrier_isSetoid.

#[global] Existing Instance carrier_isWoset.

Lemma infinite_descent {A : Type} {WPOSET : isWellPoset A} (P : A -> Prop)
  (DESCENT : forall n, P n -> exists m, m ⪵ n /\ P m)
  : forall n, ~ P n.
Proof.
  intros n. induction (wltProp_well_founded n) as [n _ IH]. intros P_n.
  pose proof (DESCENT n P_n) as [m [LT P_m]].
  contradiction (IH m LT P_m).
Qed.

#[local]
Instance wlt_StrictOrder {A : Type} {SETOID : isSetoid A} {WOSET : isWoset A} : StrictOrder wlt :=
  wltProp_StrictOrder (WPOSET := @Woset_isWellPoset A SETOID WOSET).

Section CLASSICAL_WELLORDERING.

Context {classic : forall P : Prop, P \/ ~ P}.

Theorem wlt_trichotomous {A : Type} {SETOID : isSetoid A} {WOSET : isWoset A} (a : A) (b : A)
  : (a == b) \/ (a ≺ b \/ b ≺ a).
Proof.
  revert b. pose proof (wltProp_well_founded a) as H_Acc_a. induction H_Acc_a as [a _ IH_a].
  intros b. pose proof (wltProp_well_founded b) as H_Acc_b. induction H_Acc_b as [b _ IH_b].
  pose proof (classic ((exists b', wlt b' b /\ wlt a b') \/ (exists b', wlt b' b /\ a == b'))) as [[H_LT | H_EQ] | H_GT].
  { des. right. left. transitivity b'; eauto. }
  { destruct H_EQ as [a' [H_LT H_EQ]]. right. left. rewrite -> H_EQ. exact H_LT. }
  assert (claim1 : forall b', wlt b' b -> wlt b' a).
  { intros b' H_lt_b. pose proof (IH_b b' H_lt_b) as [H_eq | [H_lt | H_gt]].
    - contradiction H_GT. right. exists b'. eauto.
    - contradiction H_GT. left. exists b'. eauto.
    - eauto.
  }
  pose proof (classic ((exists a', wlt a' a /\ wlt b a') \/ (exists a', wlt a' a /\ a' == b))) as [[H_LT' | H_EQ'] | H_GT'].
  { des. right. right. transitivity a'; eauto. }
  { destruct H_EQ' as [a' [H_LT H_EQ']]. right. right. rewrite <- H_EQ'. exact H_LT. }
  assert (claim2 : forall a', wlt a' a -> wlt a' b).
  { intros a' H_lt_a. pose proof (IH_a a' H_lt_a b) as [H_eq | [H_lt | H_gt]].
    - contradiction H_GT'. right. exists a'. eauto.
    - eauto.
    - contradiction H_GT'. left. exists a'. eauto.
  }
  left. rewrite Woset_extensional. done!.
Qed.

Theorem minimisation_lemma {A : Type} {SETOID : isSetoid A} {WOSET : isWoset A} (P : A -> Prop)
  (EXISTENCE : exists n, P n)
  : exists n, P n /\ ⟪ MIN : forall m, P m -> (n ≺ m \/ n == m) ⟫.
Proof.
  assert (NNPP : forall phi : Prop, ⟪ NNP : ~ (~ phi) ⟫ -> phi).
  { intros phi NNP; unnw. pose proof (classic phi) as [YES | NO]; tauto. }
  unnw. eapply NNPP. intros CONTRA. destruct EXISTENCE as [n P_n].
  eapply infinite_descent with (P := P) (n := n); [intros i P_i | exact P_n].
  eapply NNPP. intros CONTRA'. eapply CONTRA. exists i. split; trivial. intros m P_m.
  assert (WTS : ~ wlt m i).
  { intros H_lt. contradiction CONTRA'. exists m. split; trivial. }
  pose proof (@wlt_trichotomous A SETOID WOSET i m). tauto.
Qed.

#[local, program]
Instance WellfoundedToset_isWoset {A : Type} {SETOID : isSetoid A} {WPOSET : isWellPoset A} {wltProp_eqPropCompatible2 : eqPropCompatible2 wltProp} (wltProp_trichotomous : forall a : A, forall b : A, (a == b) \/ (a ⪵ b \/ b ⪵ a)) : isWoset A (SETOID := SETOID) :=
  { Woset_isWellPoset := WPOSET
  ; Woset_eqPropCompatible2 := wltProp_eqPropCompatible2
  }.
Next Obligation.
  revert x y EXT_EQ.
  assert (NNPP : forall phi : Prop, ⟪ NNP : ~ (~ phi) ⟫ -> phi).
  { intros phi NNP; unnw. pose proof (classic phi) as [YES | NO]; tauto. }
  unnw.
  intros a. pose proof (wltProp_well_founded a) as H_Acc_a. induction H_Acc_a as [a _ IH_a].
  intros b. pose proof (wltProp_well_founded b) as H_Acc_b. induction H_Acc_b as [b _ IH_b].
  intros EXT_EQ. eapply NNPP. intros CONTRA.
  enough (not_balanced : exists c : A, (wltProp c a /\ ~ wltProp c b) \/ (wltProp c b /\ ~ wltProp c a)).
  { destruct not_balanced as [c [[? ?] | [? ?]]]; ss!. }
  eapply NNPP. intros CONTRA'.
  pose proof (classic (wltProp a b)) as [LT1 | NLT1].
  { contradiction CONTRA'. exists a. right. split; eauto. }
  pose proof (classic (wltProp b a)) as [LT2 | NLT2].
  { contradiction CONTRA'. exists b. left. split; eauto. }
  pose proof (wltProp_trichotomous a b). tauto.
Qed.

#[global]
Instance subWoset {A : Type} {SETOID : isSetoid A} (WOSET : isWoset A (SETOID := SETOID)) (P : A -> Prop)
  : isWoset (@sig A P) (SETOID := subSetoid (SETOID := SETOID) P).
Proof.
  pose (@WellfoundedToset_isWoset (@sig A P) (@subSetoid A SETOID P) (subWwellPoset WOSET.(Woset_isWellPoset))) as THIS; eapply THIS; clear THIS.
  - red. intros [x1 H_x1] [x2 H_x2] [y1 H_y1] [y2 H_y2]; simpl. unfold binary_relation_on_image. simpl. eapply Woset_eqPropCompatible2.
  - intros [a H_a] [b H_b]; simpl. unfold binary_relation_on_image. simpl. eapply wlt_trichotomous.
Defined.

Lemma subWoset_wlt_unfold {A : Type} {SETOID : isSetoid A} (WOSET : @isWoset A SETOID) (P : A -> Prop) (a : @sig A P) (b : @sig A P)
  : @wlt (@sig A P) (@subSetoid A SETOID P) (@subWoset A SETOID WOSET P) a b = @wlt A SETOID WOSET (@proj1_sig A P a) (@proj1_sig A P b).
Proof.
  exact eq_refl.
Defined.

End CLASSICAL_WELLORDERING.

Section AUX1.

Context {A : Type} {SETOID : isSetoid A} {WOSET : isWoset A}.

Definition wle (x : A) (y : A) : Prop :=
  x ≺ y \/ x == y.

#[global]
Instance wlt_Transitive
  : Transitive wlt.
Proof.
  eapply wltProp_Transitive.
Defined.

#[global]
Instance wlt_Irreflexive
  : Irreflexive wlt.
Proof.
  eapply StrictOrder_Irreflexive.
Defined.

#[global]
Instance wle_Reflexive
  : Reflexive wle.
Proof.
  ii. right. reflexivity.
Qed.

#[global]
Instance wle_Transitive
  : Transitive wle.
Proof.
  intros ? ? ? [? | ?] [? | ?].
  - left. etransitivity; eauto.
  - left. now rewrite <- H0.
  - left. now rewrite -> H.
  - right. etransitivity; eauto.
Qed.

#[global]
Instance wle_Antisymmetric
  : @Antisymmetric A eqProp eqProp_Equivalence wle.
Proof.
  intros x y [? | ?] [? | ?].
  - contradiction (wlt_Irreflexive x). now transitivity y.
  - contradiction (wlt_Irreflexive x). now rewrite <- H0 at 2.
  - contradiction (wlt_Irreflexive x). now rewrite -> H at 1.
  - exact H.
Qed.

#[global]
Add Parametric Morphism
  : wle with signature (eqProp ==> eqProp ==> iff)
  as wle_eqProp_eqProp_iff.
Proof.
  unfold wle. ii. now rewrite H, H0.
Qed.

Lemma wle_wlt_wlt x y z
  (H_wle : wle x y)
  (H_wlt : wlt y z)
  : wlt x z.
Proof.
  destruct H_wle as [H_LT | H_EQ].
  - now transitivity y.
  - now rewrite -> H_EQ.
Qed.

Lemma wlt_wle_wlt x y z
  (H_wlt : wlt x y)
  (H_wle : wle y z)
  : wlt x z.
Proof.
  destruct H_wle as [H_LT | H_EQ].
  - now transitivity y.
  - now rewrite <- H_EQ.
Qed.

End AUX1.

Section pair_lex.

Context {A : Type} {B : Type} {A_isSetoid : isSetoid A} {B_isSetoid : isSetoid B} {A_isWoset : isWoset A} {B_isWoset : isWoset B}.

Inductive prod_wlt (p1 : A * B) (p2 : A * B) : Prop :=
  | prod_wlt_fst_lt
    (fst_lt : fst p1 ≺ fst p2)
  | prod_wlt_fst_eq_snd_eq
    (fst_eq : fst p1 == fst p2)
    (snd_lt : snd p1 ≺ snd p2).

#[global]
Instance prod_wlt_Transitive
  : Transitive prod_wlt.
Proof.
  intros x y z [? | ? ?] [? | ? ?].
  - econs 1. now transitivity (fst y).
  - econs 1. now rewrite <- fst_eq.
  - econs 1. now rewrite -> fst_eq.
  - econs 2; [now transitivity (fst y) | now transitivity (snd y)].
Qed.

Lemma prod_wlt_well_founded (p : A * B)
  : Acc prod_wlt p.
Proof.
  destruct p as [x y]. revert y.
  enough (forall x0 : A, x == x0 -> forall y : B, Acc prod_wlt (x0, y)) as ETS by now eapply ETS.
  pose proof (wltProp_well_founded x) as H_Acc_x. induction H_Acc_x as [x _ IHx].
  intros x0 x_eq_x0 y.
  pose proof (wltProp_well_founded y) as H_Acc_y. revert x0 x_eq_x0. induction H_Acc_y as [y _ IHy].
  change (forall x' : A, x' ≺ x -> forall x0 : A, x' == x0 -> forall y' : B, Acc prod_wlt (x0, y')) in IHx.
  change (forall y' : B, y' ≺ y -> forall x0 : A, x == x0 -> Acc prod_wlt (x0, y')) in IHy.
  econs. intros [x' y'] [fst_lt | fst_eq snd_lt]; simpl in *.
  - eapply IHx with (x' := x'); eauto with *. now rewrite -> x_eq_x0.
  - eapply IHy; eauto with *.
Qed.

#[global]
Instance pair_isWellPoset : isWellPoset (A * B) :=
  { wltProp := prod_wlt
  ; wltProp_Transitive := prod_wlt_Transitive
  ; wltProp_well_founded := prod_wlt_well_founded
  }.

Let pair_isSetoid : isSetoid (A * B) :=
  @prod_isSetoid A B A_isSetoid B_isSetoid.

#[local] Existing Instance pair_isSetoid.

#[global]
Instance prod_wlt_eqPropCompatible2
  : eqPropCompatible2 prod_wlt.
Proof.
  ii. simpl in *. destruct x_EQ as [x_fst_EQ x_snd_EQ], y_EQ as [y_fst_EQ y_snd_EQ]; simpl in *.
  change (fst x1 == fst x2) in x_fst_EQ. change (snd x1 == snd x2) in x_snd_EQ.
  change (fst y1 == fst y2) in y_fst_EQ. change (snd y1 == snd y2) in y_snd_EQ.
  split; (intros [? | ? ?]; [econs 1 | econs 2]); eauto with *.
  - now rewrite <- x_fst_EQ, <- y_fst_EQ.
  - now rewrite <- x_snd_EQ, <- y_snd_EQ.
  - now rewrite -> x_fst_EQ, -> y_fst_EQ.
  - now rewrite -> x_snd_EQ, -> y_snd_EQ.
Qed.

Lemma prod_wlt_extensionality (p1 : A * B) (p2 : A * B)
  (EXT : forall p : A * B, prod_wlt p p1 <-> prod_wlt p p2)
  : p1 == p2.
Proof.
  assert (fst p1 == fst p2) as FST_EQ.
  { eapply Woset_ext_eq. intros x; split; intros fst_lt.
    - assert (claim : prod_wlt (x, snd p2) (fst p1, snd p1)).
      { econs 1. exact fst_lt. }
      replace (fst p1, snd p1) with p1 in claim by now destruct p1.
      rewrite -> EXT in claim. destruct claim; simpl in *; eauto.
      contradiction (O.wlt_Irreflexive (snd p2)).
    - assert (claim : prod_wlt (x, snd p1) (fst p2, snd p2)).
      { econs 1. exact fst_lt. }
      replace (fst p2, snd p2) with p2 in claim by now destruct p2.
      rewrite <- EXT in claim. destruct claim; simpl in *; eauto.
      contradiction (O.wlt_Irreflexive (snd p1)).
  }
  assert (snd p1 == snd p2) as SND_EQ.
  { eapply Woset_ext_eq. intros x; split; intros fst_lt.
    - assert (claim : prod_wlt (fst p1, x) (fst p1, snd p1)).
      { econs 2; simpl; eauto with *. }
      replace (fst p1, snd p1) with p1 in claim by now destruct p1.
      rewrite -> EXT in claim. destruct claim; simpl in *; eauto.
      contradiction (O.wlt_Irreflexive (fst p2)). now rewrite <- FST_EQ at 1.
    - assert (claim : prod_wlt (fst p2, x) (fst p2, snd p2)).
      { econs 2; simpl; eauto with *. }
      replace (fst p2, snd p2) with p2 in claim by now destruct p2.
      rewrite <- EXT in claim. destruct claim; simpl in *; eauto.
      contradiction (O.wlt_Irreflexive (fst p1)). now rewrite -> FST_EQ at 1.
  }
  split; [exact FST_EQ | exact SND_EQ].
Qed.

#[global]
Instance pair_isWoset : isWoset (A * B) :=
  { Woset_isWellPoset := pair_isWellPoset
  ; Woset_eqPropCompatible2 := prod_wlt_eqPropCompatible2
  ; Woset_ext_eq := prod_wlt_extensionality
  }.

End pair_lex.

End O.

Infix "≼" := O.wle : type_scope.

#[universes(template)]
Class isUpperSemilattice (D : Type) {PROSET : isProset D} : Type :=
  { join_lattice (x : D) (y : D) : D
  ; bot_lattice : D
  ; join_lattice_spec (x : D) (y : D)
    : is_supremum_of (join_lattice x y) (E.fromList [x; y])
  ; bot_lattice_spec
    : is_supremum_of bot_lattice E.empty
  }.

Section UPPER_SEMILATTICE.

Context {D : Type} {PROSET : isProset D} {UPPER_SEMILATTICE : isUpperSemilattice D (PROSET := PROSET)}.

Lemma le_join_lattice_introl (x1 : D) (x2 : D)
  : forall x : D, x =< x1 -> x =< join_lattice x1 x2.
Proof.
  intros x x_le; rewrite x_le. eapply join_lattice_spec; done!.
Qed.

Lemma le_join_lattice_intror (x1 : D) (x2 : D)
  : forall x : D, x =< x2 -> x =< join_lattice x1 x2.
Proof.
  intros x x_le; rewrite x_le. eapply join_lattice_spec; done!.
Qed.

Lemma join_lattice_le_elim_l (x1 : D) (x2 : D)
  : forall x : D, join_lattice x1 x2 =< x -> x1 =< x.
Proof.
  intros x le_x. apply join_lattice_spec in le_x; done!.
Qed.

Lemma join_lattice_le_elim_r (x1 : D) (x2 : D)
  : forall x : D, join_lattice x1 x2 =< x -> x2 =< x.
Proof.
  intros x le_x. apply join_lattice_spec in le_x; done!.
Qed.

Lemma join_lattice_le_intro (x1 : D) (x2 : D)
  : forall x : D, x1 =< x -> x2 =< x -> join_lattice x1 x2 =< x.
Proof.
  ii; eapply join_lattice_spec; done!.
Qed.

Lemma bot_lattice_le_intro
  : forall x : D, bot_lattice =< x.
Proof.
  ii; eapply bot_lattice_spec; done!.
Qed.

End UPPER_SEMILATTICE.

#[universes(template)]
Class isLowerSemilattice (D : Type) {PROSET : isProset D} : Type :=
  { meet_lattice (x : D) (y : D) : D
  ; top_lattice : D
  ; meet_lattice_spec (x1 : D) (x2 : D)
    : forall x : D, x =< meet_lattice x1 x2 <-> (x =< x1 /\ x =< x2)
  ; top_lattice_spec
    : forall x : D, x =< top_lattice
  }.

Section LOWER_SEMILATTICE.

Import ListNotations.

Context {D : Type} {PROSET : isProset D} {LOWER_SEMILATTICE : isLowerSemilattice D (PROSET := PROSET)}.

Lemma meet_lattice_is_infimum (x1 : D) (x2 : D)
  : is_infimum_of (meet_lattice x1 x2) (E.fromList [x1; x2]).
Proof.
  ii. rewrite meet_lattice_spec. split; done!.
Qed.

End LOWER_SEMILATTICE.

#[universes(template)]
Class isLattice (D : Type) {PROSET : isProset D} : Type :=
  { Lattice_asUpperSemilattice :: isUpperSemilattice D (PROSET := PROSET)
  ; Lattice_asLowerSemilattice :: isLowerSemilattice D (PROSET := PROSET)
  }.

#[local, program]
Instance direct_product_of_two_Prosets {A : Type} {B : Type} (A_isProset : isProset A) (B_isProset : isProset B) : isProset (A * B) :=
  { leProp lhs rhs := fst lhs =< fst rhs /\ snd lhs =< snd rhs
  ; Proset_isSetoid := directProduct_of_two_Setoids A_isProset.(Proset_isSetoid) B_isProset.(Proset_isSetoid)
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

#[program]
Definition dual_Proset {D : Type} `(PROSET : isProset D) : isProset D :=
  {| leProp lhs rhs := rhs =< lhs; Proset_isSetoid := PROSET.(Proset_isSetoid) |}.
Next Obligation.
  split.
  - intros x. reflexivity.
  - intros x y z LE LE'. transitivity y; [exact LE' | exact LE].
Defined.
Next Obligation.
  intros x y. unfold flip; cbn. split.
  - intros EQ. eapply leProp_PartialOrder. symmetry. exact EQ.
  - intros EQ. symmetry. eapply leProp_PartialOrder. exact EQ.
Defined.

Module ColaDef.

#[local] Existing Instance pi_isProset.

Import ListNotations.

Notation "`[ A -> B ]" := { f : A -> B | isMonotonic1 f }.

Class isCola (D : Type) {PROSET : isProset D} : Type :=
  supremum_cola (X : ensemble D) : { sup_X : D | is_supremum_of sup_X X }.

#[program]
Definition Cola_isUpperSemilattice {D : Type} {PROSET : isProset D} {COLA : isCola D (PROSET := PROSET)} : isUpperSemilattice D (PROSET := PROSET) :=
  {| join_lattice x y := supremum_cola (E.fromList [x; y]); bot_lattice := supremum_cola E.empty; |}.
Next Obligation.
  i. exact (proj2_sig (supremum_cola (E.fromList [x; y]))).
Qed.
Next Obligation.
  ii. destruct (supremum_cola E.empty) as [bot bot_spec]; simpl. done!.
Qed.

End ColaDef.

Module CpoDef.

Import ListNotations.

#[local] Existing Instance pi_isProset.

Notation "`[ A -> B ]" := { f : A -> B | isContinuous f }.

Variant isDirected {D : Type} `{PROSET : isProset D} (X : ensemble D) : Prop :=
  | isDirected_intro 
    (NONEMPTY : exists x0, x0 \in X)
    (DIRECTED' : forall x1, forall x2, forall x1_IN : x1 \in X, forall x2_IN : x2 \in X, exists x3, x3 \in X /\ (x1 =< x3 /\ x2 =< x3))
    : isDirected X.

#[local] Hint Constructors isDirected : poset_hints.

Lemma isDirected_iff {D : Type} `{PROSET : isProset D} (X : ensemble D)
  : isDirected X <-> (forall xs, L.is_finsubset_of xs X -> (exists u, u \in X /\ (forall x, L.In x xs -> x =< u))).
Proof.
  split.
  - intros [? ?]. induction xs as [ | x' xs' IH]; simpl.
    + done!.
    + intros FINSUBSET. exploit IH. done!.
      intros [u' [IN' BOUNDED']]. exploit (DIRECTED' x' u'); eauto.
      intros (u & ? & ? & ?). exists u; done!.
  - intros DIRECTED. split.
    + exploit (DIRECTED []); simpl.
      * done!.
      * intros [u [IN ?]]. exists u; done!.
    + ii. exploit (DIRECTED [x1; x2]); simpl. 
      * now intros ? [<- | [<- | []]].
      * intros [u [IN ?]]. exists u; done!.
Qed.

Lemma theSetOfNeighborhoods_isDirected {A : Type} {TOPOLOGY : topology A} (x : A) (X : ensemble (ensemble A))
  (NEIGHBORHOOD : forall N, N \in X <-> (exists O, isOpen O /\ x \in O /\ O \subseteq N))
  : isDirected (PROSET := dual_Proset E.ensemble_isProset) X.
Proof.
  split; simpl in *.
  - exists E.full. rewrite NEIGHBORHOOD. exists E.full. split.
    + eapply full_isOpen.
    + done!.
  - ii. exists (E.intersection x1 x2). split.
    + rewrite NEIGHBORHOOD in *. destruct x1_IN as (O1&O1_open&IN1&SUBSET1), x2_IN as (O2&O2_open&IN2&SUBSET2).
      exists (E.intersection O1 O2). split.
      * eapply intersection_isOpen; eauto with *.
      * done!.
    + done!.
Qed.

Lemma preservesDirectedness_if_isMonotonic {A : Type} {B : Type} {A_isProset : isProset A} {B_isProset : isProset B} (f : A -> B)
  (MONOTONIC : isMonotonic1 f)
  : forall X, isDirected X -> isDirected (E.image f X).
Proof.
  intros X [? ?]. split.
  - destruct NONEMPTY as [x0 IN]. exists (f x0); done!.
  - intros y1 y2 y1_IN y2_IN. s!. destruct y1_IN as [x1 [-> x1_in]], y2_IN as [x2 [-> x2_in]].
    pose proof (DIRECTED' x1 x2 x1_in x2_in) as [x3 [x3_in [x1_le_x3 x2_le_x3]]]. exists (f x3); done!.
Qed.

Class isCpo (D : Type) {PROSET : isProset D} : Type :=
  { bottom_cpo : D
  ; supremum_cpo (X : ensemble D) (DIRECTED : isDirected X) : D
  ; bottom_cpo_spec : forall x : D, bottom_cpo =< x
  ; supremum_cpo_spec (X : ensemble D) (DIRECTED : isDirected X) : is_supremum_of (supremum_cpo X DIRECTED) X
  }.

Section SCOTT_TOPOLOGY.

#[local] Opaque "\in".

Context {D : Type} `{PROSET : isProset D}.

Variant isOpen_Scott (O : ensemble D) : Prop :=
  | isOpen_Scott_intro
    (UPWARD_CLOSED : forall x, forall y, x \in O -> x =< y -> y \in O)
    (LIMIT : forall X, forall sup_X, isDirected X -> is_supremum_of sup_X X -> sup_X \in O -> exists x, x \in X /\ x \in O)
    : isOpen_Scott O.

#[local] Hint Constructors isDirected : core.
#[local] Hint Constructors isOpen_Scott : core.

#[global]
Instance isOpen_Scott_lawful
  : AxiomsForOpenSets D isOpen_Scott.
Proof.
  split; ii.
  - split; try done!; ss!. exists x; ss!.
  - split.
    + intros x y x_IN LE. rewrite E.in_unions_iff in x_IN. destruct x_IN as [O [x_IN H_IN]]. ss!. exists O; done!.
    + intros X sup_X DIRECTED SUPREMUM sup_IN. rewrite E.in_unions_iff in sup_IN. destruct sup_IN as [O [sup_IN H_IN]]. ss!.
      pose proof (OPENs O H_IN) as [? ?]. exploit (LIMIT X sup_X); eauto with *. intros [y [y_IN y_IN']]. exists y; done!.
  - split.
    + done!.
    + intros X sup_X DIRECTED SUPREMUM sup_IN. s!. destruct sup_IN as [sup_IN1 sup_IN2]. destruct OPEN1 as [UPWARD_CLOSED1 LIMIT1], OPEN2 as [UPWARD_CLOSED2 LIMIT2].
      exploit (LIMIT1 X sup_X); eauto with *. intros [x1 [x1_IN x1_IN']]. exploit (LIMIT2 X sup_X); eauto with *. intros [x2 [x2_IN x2_IN']]. destruct DIRECTED.
      pose proof (DIRECTED' x1 x2 x1_IN x2_IN) as [x3 [? [? ?]]]; exists x3; done!.
  - split.
    + intros x y x_IN LE. rewrite <- EXT_EQ in *. destruct OPEN as [? ?]. done!.
    + intros X sup_X DIRECTED SUPREMUM sup_IN. destruct OPEN as [? ?]. rewrite <- EXT_EQ in sup_IN.
      pose proof (LIMIT X sup_X DIRECTED SUPREMUM sup_IN) as [x [? ?]]; exists x; done!.
Qed.

#[local]
Instance Scott_topology : topology D :=
  { isOpen := isOpen_Scott
  ; AxiomsForTopology := isOpen_Scott_lawful
  }.

End SCOTT_TOPOLOGY.

Section MAKE_CPO_FROM_COLA.

Context {D : Type} {PROSET : isProset D} {COLA : ColaDef.isCola D (PROSET := PROSET)}.

#[global, program]
Instance cola_isCpo : isCpo D :=
  { bottom_cpo := proj1_sig (ColaDef.supremum_cola E.empty)
  ; supremum_cpo X _ := proj1_sig (ColaDef.supremum_cola X)
  ; bottom_cpo_spec := _
  ; supremum_cpo_spec X _ := proj2_sig (ColaDef.supremum_cola X)
  }.
Next Obligation.
  destruct (ColaDef.supremum_cola E.empty) as [bot bot_spec]; simpl in *.
  eapply bot_spec. ii. inv IN.
Qed.

End MAKE_CPO_FROM_COLA.

End CpoDef.

#[universes(template)]
Class hsOrd (A : Type) `{PROSET : isProset A} : Type :=
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

Lemma compare_spec {A : Type} {PROSET : isProset A} {ORD : hsOrd A (PROSET := PROSET)} (lhs : A) (rhs : A) :
  match compare lhs rhs with
  | Lt => lhs =< rhs /\ ~ lhs == rhs
  | Eq => lhs == rhs
  | Gt => rhs =< lhs /\ ~ lhs == rhs
  end.
Proof.
  destruct (compare lhs rhs) eqn: H_OBS; eauto with *.
Qed.

Section list_hsOrd.

Context {A : Type} {PROSET : isProset A} {ORD : hsOrd A (PROSET := PROSET)}.

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
    destruct (compare x1 x1) eqn: H_OBS1...
    all: contradiction (proj2 claim1)...
  - intros xs1 xs2; revert xs1 xs2; induction xs1 as [ | x1 xs1 IH]; destruct xs2 as [ | x2 xs2]; simpl...
    pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x1).
    destruct (compare x1 x2) eqn: H_OBS1; destruct (compare x2 x1) eqn: H_OBS2...
    all: contradiction (proj2 claim2)...
  - intros xs1 xs2 xs3; revert xs1 xs3; induction xs2 as [ | x2 xs2 IH]; destruct xs1 as [ | x1 xs1]; destruct xs3 as [ | x3 xs3]; simpl...
    pose proof (claim1 := compare_spec x1 x2); pose proof (claim2 := compare_spec x2 x3); pose proof (claim3 := compare_spec x1 x3).
    destruct (compare x1 x2) eqn: H_OBS1; destruct (compare x2 x3) eqn: H_OBS2; destruct (compare x1 x3) eqn: H_OBS3...
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
    destruct (compare x1 x2) eqn: H_OBS1; destruct (compare x2 x3) eqn: H_OBS2; destruct (compare x1 x3) eqn: H_OBS3...
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
    destruct (compare x1 x2) eqn: H_OBS1; destruct (compare x2 x1) eqn: H_OBS2...
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
    destruct (compare x1 x2) eqn: H_OBS1; destruct (compare x2 x1) eqn: H_OBS2...
    - contradiction (proj2 claim2)...
    - contradiction (proj2 claim2)...
    - contradiction (proj2 claim1)...
    - split...
    - contradiction (proj2 claim1)...
    - split...
  }
  assert (lemma6 : forall xs1 : list A, forall xs2 : list A, lex_compare xs1 xs2 = Gt <-> lex_compare xs2 xs1 = Lt) by firstorder.
  intros lhs rhs; destruct (lex_compare lhs rhs) eqn: H_OBS; now firstorder.
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
    destruct OBS eqn: H_OBS; now rewrite H_eq in claim1.
Qed.

#[local]
Instance lex_le_PartialOrder
  : PartialOrder lex_eq lex_le.
Proof with discriminate || eauto with *.
  intros xs1 xs2; cbn. unfold flip, lex_eq, lex_le.
  pose proof (claim1 := lex_le_flip_spec xs1 xs2).
  destruct (lex_compare xs1 xs2) eqn: H_OBS.
  - split...
  - split... intros [? [H_false | H_false]].
    all: rewrite H_false in claim1...
  - split... intros [[? | ?] ?]...
Qed.

#[local]
Instance list_lexicographical_order : isProset (list A) :=
  { leProp := lex_le
  ; Proset_isSetoid := list_isSetoid_of_elementwise_comparison
  ; leProp_PreOrder := lex_le_PreOrder
  ; leProp_PartialOrder := lex_le_PartialOrder
  }.

#[local] Obligation Tactic := cbn; unfold lex_le, lex_eq; ii.

#[global, program]
Instance list_hsOrd : hsOrd (list A) (PROSET := list_lexicographical_order) :=
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

Section nat_hsOrd.

#[local]
Instance nat_isProset : isProset nat :=
  { leProp := Nat.le
  ; Proset_isSetoid := mkSetoid_from_eq
  ; leProp_PreOrder := Nat.le_preorder
  ; leProp_PartialOrder := Nat.le_partialorder
  }.

Fixpoint nat_compare (x : nat) (y : nat) {struct x} : comparison :=
  match x, y with
  | O, O => Eq
  | O, S y' => Lt
  | S x', O => Gt
  | S x', S y' => nat_compare x' y'
  end.

Lemma nat_compare_lt (x : nat) (y : nat)
  (hyp_lt : nat_compare x y = Lt)
  : x <= y /\ x <> y.
Proof with eauto with *.
  revert x y hyp_lt. induction x as [ | x IH], y as [ | y]; simpl; ii.
  - inversion hyp_lt.
  - split; lia.
  - inversion hyp_lt.
  - pose proof (IH y hyp_lt) as [x_le_y x_ne_y]. split; lia.
Qed.

Lemma nat_compare_eq (x : nat) (y : nat)
  (hyp_eq : nat_compare x y = Eq)
  : x = y.
Proof with eauto with *.
  revert x y hyp_eq. induction x as [ | x IH], y as [ | y]; simpl; ii.
  - reflexivity.
  - inversion hyp_eq.
  - inversion hyp_eq.
  - pose proof (IH y hyp_eq) as x_eq_y. f_equal. exact x_eq_y.
Qed.

Lemma nat_compare_gt (x : nat) (y : nat)
  (hyp_gt : nat_compare x y = Gt)
  : y <= x /\ x <> y.
Proof with eauto with *.
  cbn. revert x y hyp_gt. induction x as [ | x IH], y as [ | y]; simpl; ii.
  - inversion hyp_gt.
  - inversion hyp_gt.
  - split; lia.
  - pose proof (IH y hyp_gt) as [y_le_x x_ne_y]. split; lia.
Qed.

#[local]
Instance nat_hsOrd : hsOrd nat (PROSET := nat_isProset) :=
  { compare := nat_compare
  ; compare_Lt := nat_compare_lt
  ; compare_Eq := nat_compare_eq
  ; compare_Gt := nat_compare_gt
  }.

End nat_hsOrd.
