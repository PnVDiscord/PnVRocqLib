Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Math.DomainTheory.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.
#[local] Obligation Tactic := i.

#[local] Hint Resolve Equivalence_Reflexive Equivalence_Symmetric Equivalence_Transitive : poset_hints.
#[local] Hint Resolve eqProp_refl eqProp_sym eqProp_trans leProp_refl leProp_trans leProp_antisymmetry eqProp_implies_leProp : poset_hints.
#[global] Hint Resolve supremum_monotonic supremum_unique supremum_congruence is_supremum_of_compatWith_eqProp : poset_hints.

#[local] Hint Unfold fixedpointsOf prefixedpointsOf postfixedpointsOf upperboundsOf lowerboundsOf is_supremum_of is_infimum_of : simplication_hints.

Section CPO_THEORY.

Import CpoDef.

#[local] Existing Instance direct_product_of_two_Prosets.
#[local] Existing Instance subProset.
#[local] Existing Instance pi_isProset.
#[local] Existing Instance Scott_topology.

Definition U {D : Type} {PROSET : isProset D} (x : D) : ensemble D :=
  fun z : D => ~ z =< x.

Lemma U_x_isOpen {D : Type} {PROSET : isProset D} (x : D)
  : isOpen (U x).
Proof.
  split.
  - intros y z y_in_U_x y_le_z z_le_x. contradiction y_in_U_x. now transitivity z.
  - intros X sup_X [X_nonempty DIRECTED_OR_EMPTY] sup_X_is_supremum_of_X sup_X_in_U_x.
    assert (NOT_UPPER_BOUND : ~ x \in upperboundsOf X).
    { ii. contradiction sup_X_in_U_x. now eapply sup_X_is_supremum_of_X. }
    eapply NNPP. intros H_false. contradiction NOT_UPPER_BOUND. intros y y_in_X.
    eapply NNPP. intros y_in_U_x. contradiction H_false. now exists (y).
Qed.

Lemma Scott_topology_T0_aux {D : Type} {PROSET : isProset D} (a : D) (b : D)
  (NE : ~ a == b)
  : exists O : ensemble D, isOpen O /\ ((a \in O /\ ~ b \in O) \/ (b \in O /\ ~ a \in O)).
Proof.
  pose proof (classic (a =< b)) as [YES | NO].
  - assert (IN : b \in U a).
    { intros LE. contradiction NE. eapply leProp_antisymmetry; trivial. }
    exists (U a). split. eapply U_x_isOpen.
    right. split; trivial. intros LE. contradiction LE. reflexivity.
  - exists (U b). split. eapply U_x_isOpen.
    left. split; trivial. intros LE. contradiction LE. reflexivity.
Qed.

Lemma Scott_topology_T0 {D : Type} {POSET : isPoset D} (a : D) (b : D)
  (NE : a <> b)
  : exists O : ensemble D, isOpen O /\ ((a \in O /\ ~ b \in O) \/ (b \in O /\ ~ a \in O)).
Proof.
  eapply Scott_topology_T0_aux. now rewrite Poset_eqProp_spec.
Qed.

Lemma ScottContinuousMap_isMonotonic {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} (f : D -> D')
  (CONTINUIOUS : isContinuous f)
  : isMonotonic1 f.
Proof.
  intros x1 x2 x1_le_x2. eapply NNPP. intros f_x1_in_U_f_x2.
  assert (x1_in_preimage_f_U_f_x2 : x1 \in E.preimage f (U (f x2))) by now econstructor.
  assert (preimage_f_U_f_x2_isOpen : isOpen (E.preimage f (U (f x2)))) by eapply CONTINUIOUS, U_x_isOpen.
  assert (x2_in_preimage_f_U_f_x2 : x2 \in E.preimage f (U (f x2))).
  { inversion preimage_f_U_f_x2_isOpen. eapply UPWARD_CLOSED with (x := x1); eauto. }
  assert (f_x2_in_U_f_x2 : f x2 \in U (f x2)) by now inversion x2_in_preimage_f_U_f_x2; subst.
  now contradiction f_x2_in_U_f_x2.
Qed.

#[local] Hint Resolve ScottContinuousMap_isMonotonic : poset_hints.

Lemma f_sup_X_eq_sup_image_f_X {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (f : D -> D') (X : ensemble D) (sup_X : D)
  (CONTINUIOUS : isContinuous f)
  (DIRECTED : isDirected X)
  (SUPREMUM : is_supremum_of sup_X X)
  (DIRECTED' : isDirected (E.image f X))
  : f sup_X == supremum_cpo (E.image f X) DIRECTED'.
Proof with eauto with *.
  assert (MONOTONIC : isMonotonic1 f) by now eapply ScottContinuousMap_isMonotonic.
  set (E.image f X) as Y in *. set (sup_Y := supremum_cpo Y DIRECTED').
  pose proof (SUPREMUM' := supremum_cpo_spec Y DIRECTED').
  assert (claim1 : sup_Y =< f sup_X).
  { eapply SUPREMUM'. intros y y_in_Y. unfold Y in *. s!.
    des. subst y. eapply MONOTONIC, SUPREMUM...
  }
  assert (claim2 : f sup_X =< sup_Y).
  { eapply NNPP. intros f_sup_X_in_U_sup_Y.
    assert (sup_X_in_preimage_f_U_sup_Y : sup_X \in E.preimage f (U sup_Y)) by now done!.
    assert (f_U_sup_Y_isOpen : isOpen (E.preimage f (U sup_Y))) by now eapply CONTINUIOUS, U_x_isOpen.
    inv f_U_sup_Y_isOpen. pose proof (LIMIT X sup_X DIRECTED SUPREMUM sup_X_in_preimage_f_U_sup_Y) as [x1 [x1_in_X x1_in_preimage_f_U_sup_Y]].
    assert (f_x1_in_image_f_X : f x1 \in E.image f X).
    { econstructor... }
    assert (f_x1_in_U_sup_Y : f x1 \in U sup_Y).
    { s!. des. done!. }
    contradiction f_x1_in_U_sup_Y. eapply SUPREMUM'...
  }
  eapply @leProp_antisymmetry with (A_isProset := PROSET')...
Qed.

Lemma sup_Y_is_supremum_of_image_f_X_iff_f_sup_X_eq_sup_Y {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (f : D -> D') (X : ensemble D) (sup_X : D) (sup_Y : D')
  (CONTINUIOUS : isContinuous f)
  (DIRECTED : isDirected X)
  (SUPREMUM : is_supremum_of sup_X X)
  : is_supremum_of sup_Y (E.image f X) <-> f sup_X == sup_Y.
Proof.
  assert (image_f_X_isDirected : isDirected (E.image f X)).
  { eapply preservesDirectedness_if_isMonotonic; eauto with *. }
  split.
  - intros sup_Y_is_supremum_of_image_f_X.
    rewrite f_sup_X_eq_sup_image_f_X with (f := f) (CONTINUIOUS := CONTINUIOUS) (DIRECTED := DIRECTED) (SUPREMUM := SUPREMUM) (DIRECTED' := image_f_X_isDirected).
    eapply supremum_unique.
    + exact (supremum_cpo_spec (E.image f X) image_f_X_isDirected).
    + exact sup_Y_is_supremum_of_image_f_X.
    + reflexivity.
  - intros f_sup_X_eq_sup_Y. rewrite <- f_sup_X_eq_sup_Y.
    rewrite f_sup_X_eq_sup_image_f_X with (f := f) (CONTINUIOUS := CONTINUIOUS) (DIRECTED := DIRECTED) (SUPREMUM := SUPREMUM) (DIRECTED' := image_f_X_isDirected).
    exact (supremum_cpo_spec (E.image f X) image_f_X_isDirected).
Qed.

Corollary ScottContinuousMap_preserves_supremum {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (f : D -> D') (X : ensemble D) (sup_X : D)
  (CONTINUIOUS : isContinuous f)
  (DIRECTED : isDirected X)
  (SUPREMUM : is_supremum_of sup_X X)
  : is_supremum_of (f sup_X) (E.image f X).
Proof.
  eapply sup_Y_is_supremum_of_image_f_X_iff_f_sup_X_eq_sup_Y; eauto with *.
Qed.

Definition preserves_supremum {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (f : D -> D') : Prop :=
  forall X, isDirected X -> exists sup_X, exists sup_Y, is_supremum_of sup_X X /\ is_supremum_of sup_Y (E.image f X) /\ f sup_X == sup_Y.

Lemma isMonotonic_if_preserves_supremum {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (f : D -> D')
  (COMPAT_WITH_eqProp : eqPropCompatible1 f)
  (PRESERVES_SUPREMUM : preserves_supremum f)
  : isMonotonic1 f.
Proof with eauto with *.
  intros x1 x2 x1_le_x2. pose (E.fromList [x1; x2]) as X. set (E.image f X) as Y.
  assert (claim1 : is_supremum_of x2 X).
  { intros z. split.
    - intros x2_le_z x x_in_X. unfold X in *. s!. destruct x_in_X as [x_eq_x1 | [x_eq_x2 | []]]; subst x; rewrite <- x2_le_z...
    - intros z_isUpperBoundOf_X. eapply z_isUpperBoundOf_X. done!.
  }
  assert (X_isDirected : isDirected X).
  { split.
    - exists x1. done!.
    - intros z1 z2 ? ?. unfold X in *. s!. destruct x1_IN as [<- | [<- | []]], x2_IN as [<- | [<- | []]]; exists x2; done!.
  }
  pose proof (PRESERVES_SUPREMUM X X_isDirected) as [sup_X [sup_Y [sup_X_is_supremum_of_X [sup_Y_is_supremum_of_Y f_sup_X_eq_sup_Y]]]].
  assert (it_is_sufficient_to_show : f sup_X == f x2).
  { eapply COMPAT_WITH_eqProp. eapply supremum_unique... }
  unfold X, Y in *. transitivity (f sup_X).
  - eapply sup_Y_is_supremum_of_Y; done!.
  - eapply eqProp_implies_leProp; done!.
Qed.

Lemma preservesDirectedness_if_preservesSupremum {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (f : D -> D')
  (COMPAT_WITH_eqProp : eqPropCompatible1 f)
  (PRESERVES_SUPREMUM : preserves_supremum f)
  : forall X, isDirected X -> isDirected (E.image f X).
Proof with eauto with *.
  pose proof (isMonotonic_if_preserves_supremum f COMPAT_WITH_eqProp PRESERVES_SUPREMUM) as claim1.
  ii; s!. inversion H. des. split.
  - exists (f x0); done!.
  - intros y1 y2 ? ?; des. s!. destruct x1_IN as [x1 [-> x1_in_X]], x2_IN as [x2 [-> x2_in_X]].
    pose proof (DIRECTED' x1 x2 x1_in_X x2_in_X) as [x3 [x3_in_X [? ?]]]; unnw.
    exists (f x3); done!.
Qed.

Theorem the_main_reason_for_introducing_ScottTopology {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (f : D -> D')
  (COMPAT_WITH_eqProp : eqPropCompatible1 f)
  : isContinuous f <-> preserves_supremum f.
Proof with eauto with *.
  split; [intros f_isContinuous | intros f_preservesSupremum].
  - intros X X_isDirected. set (Y := E.image f X).
    assert (Y_isDirected : isDirected Y).
    { eapply preservesDirectedness_if_isMonotonic... }
    set (sup_X := supremum_cpo X X_isDirected).
    pose proof (sup_X_is_supremum_of_X := supremum_cpo_spec X X_isDirected).
    exists sup_X, (f sup_X). pose proof (proj2 (sup_Y_is_supremum_of_image_f_X_iff_f_sup_X_eq_sup_Y f X sup_X (f sup_X) f_isContinuous X_isDirected sup_X_is_supremum_of_X) (eqProp_refl (f sup_X))) as claim1...
  - ii. s!. inversion H.
    pose proof (isMonotonic_if_preserves_supremum f COMPAT_WITH_eqProp f_preservesSupremum) as f_isMonotonic.
    split; ii.
    + s!. des. subst. done!.
    + pose proof (f_preservesSupremum X H0) as [sup [sup_Y [? [? ?]]]].
      assert (sup_X_eq_sup : sup_X == sup).
      { eapply supremum_unique... }
      assert (f_sup_X_in_Y : f sup_X \in Y).
      { s!. des. now subst. }
      pose proof (preservesDirectedness_if_preservesSupremum f COMPAT_WITH_eqProp f_preservesSupremum X H0) as image_f_X_isDirected.
      assert (sup_Y_eq_f_sup_X : sup_Y == f sup_X).
      { rewrite sup_X_eq_sup... }
      assert (claim1 : exists y, y \in E.image f X /\ y \in Y).
      { eapply LIMIT... }
      destruct claim1 as [y [y_in_image_f_X y_in_Y]].
      inversion y_in_image_f_X; subst y.
      exists x. done!.
Qed.

Corollary isContinuous_iff_preserves_supremum {D : Type} {D' : Type} {POSET : isPoset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (f : D -> D')
  : isContinuous f <-> preserves_supremum f.
Proof.
  eapply the_main_reason_for_introducing_ScottTopology.
  ii. rewrite Poset_eqProp_spec in x_EQ. now subst x2.
Qed.

Lemma supOfScottContinuousMaps_isWellDefined {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (F : ensemble `[D -> D'])
  (F_isDirected : isDirected F)
  : forall x, isDirected (E.image (fun f_i : `[D -> D'] => proj1_sig f_i x) F).
Proof.
  inversion F_isDirected. s!. ii. destruct NONEMPTY as [f0 f0_in_F]. split.
  - exists (proj1_sig f0 x); done!.
  - intros y1 y2 ? ?. s!. destruct x1_IN as [f1 [-> f1_in]], x2_IN as [f2 [-> f2_in]].
    pose proof (DIRECTED' f1 f2 f1_in f2_in) as [f3 [f3_in_F [f1_le_f3 f2_le_f3]]].
    exists (proj1_sig f3 x); done!.
Qed.

Definition supOfScottContinuousMaps {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (F : ensemble `[D -> D']) (F_isDirected : isDirected F) : D -> D' :=
  fun x => supremum_cpo (E.image (fun f_i => proj1_sig f_i x) F) (supOfScottContinuousMaps_isWellDefined F F_isDirected x).

Lemma supOfScottContinuousMaps_isSupremum {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (F : ensemble `[D -> D']) (F_isDirected : isDirected F) (x : D)
  : is_supremum_of (supOfScottContinuousMaps F F_isDirected x) (E.image (fun f_i => proj1_sig f_i x) F).
Proof.
  exact (supremum_cpo_spec (E.image (fun f_i => proj1_sig f_i x) F) (supOfScottContinuousMaps_isWellDefined F F_isDirected x)).
Defined.

Lemma supOfScottContinuousMaps_isMonotonic {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (F : ensemble `[D -> D'])
  (F_isDirected : isDirected F)
  : isMonotonic1 (supOfScottContinuousMaps F F_isDirected).
Proof with eauto with *.
  intros x1 x2 x1_le_x2. eapply supOfScottContinuousMaps_isSupremum with (x := x1).
  ii; s!. destruct IN as [f [-> IN]]. transitivity (proj1_sig f x2).
  - eapply ScottContinuousMap_isMonotonic... exact (proj2_sig f).
  - eapply supOfScottContinuousMaps_isSupremum with (x := x2); done!.
Qed.

Lemma supOfScottContinuousMaps_F_sup_X_is_supremum_of_unions_i_image_f_i_X_F {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (F : ensemble `[D -> D']) (X : ensemble D) (sup_X : D)
  (F_isDirected : isDirected F)
  (X_isDirected : isDirected X)
  (sup_X_is_supremum_of_X : is_supremum_of sup_X X)
  : is_supremum_of (supOfScottContinuousMaps F F_isDirected sup_X) (E.unions (E.image (fun f_i => E.image (fun x => proj1_sig f_i x) X) F)).
Proof with eauto with *.
  assert (claim1 : forall f_i, f_i \in F -> is_supremum_of (proj1_sig f_i sup_X) (E.image (fun x => proj1_sig f_i x) X)).
  { intros f_i f_i_in. eapply sup_Y_is_supremum_of_image_f_X_iff_f_sup_X_eq_sup_Y... exact (proj2_sig f_i). }
  pose proof (claim2 := supOfScottContinuousMaps_isSupremum F F_isDirected sup_X).
  eapply supremum_of_map_suprema_is_supremum_of_unions.
  - intros Y ?; s!. destruct H as [f0 [? f0_in_F]]; subst Y...
  - intros y. split.
    + intros f_sup_X_le_y sup_Y. unfold map_suprema. i. simpl in IN. red in IN. destruct IN as [Y [IN SUPREMUM]]. red in SUPREMUM. s!. destruct IN as [f_i [-> f_i_in]].
      pose proof (f_i_sup_X_isSupremum := claim1 f_i f_i_in).
      assert (sup_Y_eq : sup_Y == proj1_sig f_i sup_X).
      { eapply supremum_unique... }
      assert (f_i_sup_X_in : proj1_sig f_i sup_X \in E.image (fun f => proj1_sig f sup_X) F).
      { done!. }
      rewrite sup_Y_eq. rewrite <- f_sup_X_le_y. eapply claim2...
    + intros ?. eapply claim2. intros y' ?. s!. destruct IN as [f_i [-> f_i_in]].
      eapply H. exists (E.image (fun x => proj1_sig f_i x) X); done!.
Qed.

Theorem supOfScottContinuousMaps_preserves_supremum {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (F : ensemble `[D -> D']) (X : ensemble D) (sup_X : D)
  (F_isDirected : isDirected F)
  (X_isDirected : isDirected X)
  (sup_X_is_supremum_of_X : is_supremum_of sup_X X)
  : is_supremum_of (supOfScottContinuousMaps F F_isDirected sup_X) (E.image (supOfScottContinuousMaps F F_isDirected) X).
Proof with eauto with *.
  assert (unions_image_image_comm : E.unions (E.image (fun f_i => E.image (fun x_i => proj1_sig f_i x_i) X) F) == E.unions (E.image (fun x_i => E.image (fun f_i => proj1_sig f_i x_i) F) X)).
  { intros z. split; i; s!.
    - destruct H as [Y [H_in H_IN]]. s!. destruct H_IN as [f [-> H_IN]]. s!. destruct H_in as [x [-> H_in]]. exists (E.image (fun f => proj1_sig f x) F); done!.
    - destruct H as [Y [H_in H_IN]]. s!. destruct H_IN as [x [-> H_IN]]. s!. destruct H_in as [f [-> H_in]]. exists (E.image (fun x => proj1_sig f x) X); done!.
  }
  assert (lemma1 : forall sup_Y, is_supremum_of sup_Y (E.unions (E.image (fun f_i => E.image (fun x => proj1_sig f_i x) X) F)) <-> is_supremum_of sup_Y (E.unions (E.image (fun x => E.image (fun f_i => proj1_sig f_i x) F) X))).
  { i; now rewrite unions_image_image_comm. }
  assert (lemma2 : forall sup_Y, is_supremum_of sup_Y (E.unions (E.image (fun x => E.image (fun f_i => proj1_sig f_i x) F) X)) <-> is_supremum_of sup_Y (map_suprema (E.image (fun x => E.image (fun f_i => proj1_sig f_i x) F) X))).
  { ii. symmetry. eapply supremum_of_map_suprema_is_supremum_of_unions.
    intros Y ?. rewrite E.in_image_iff in H. destruct H as [x [-> x_in]].
    exists (supOfScottContinuousMaps F F_isDirected x). eapply supOfScottContinuousMaps_isSupremum.
  }
  pose proof (lemma3 := supOfScottContinuousMaps_isMonotonic F F_isDirected).
  assert (claim1 : forall f_i, f_i \in F -> is_supremum_of (proj1_sig f_i sup_X) (E.image (fun x => proj1_sig f_i x) X)).
  { intros f_i f_i_in. eapply sup_Y_is_supremum_of_image_f_X_iff_f_sup_X_eq_sup_Y... exact (proj2_sig f_i). }
  assert (claim2 : is_supremum_of (supOfScottContinuousMaps F F_isDirected sup_X) (E.image (fun f_i => proj1_sig f_i sup_X) F)).
  { eapply supOfScottContinuousMaps_isSupremum. }
  assert (claim3 : is_supremum_of (supOfScottContinuousMaps F F_isDirected sup_X) (E.unions (E.image (fun f_i => E.image (fun x => proj1_sig f_i x) X) F))).
  { eapply supOfScottContinuousMaps_F_sup_X_is_supremum_of_unions_i_image_f_i_X_F... }
  rewrite lemma1, lemma2 in claim3.
  intros y. split.
  - intros ? y' ?. rewrite E.in_image_iff in IN. destruct IN as [x [-> x_in]].
    eapply claim3... exists (E.image (fun f_i => proj1_sig f_i x) F). split.
    + econstructor...
    + red. eapply supOfScottContinuousMaps_isSupremum.
  - ii. do 2 red in H. eapply claim3. intros upper_bound ?.
    repeat red in IN. destruct IN as [Y [Y_in upper_bound_in]]. s!. destruct Y_in as [x [-> ?]].
    red in upper_bound_in. transitivity (supOfScottContinuousMaps F F_isDirected x).
    + eapply eqProp_implies_leProp, supremum_unique.
      { exact upper_bound_in. }
      { eapply supOfScottContinuousMaps_isSupremum. }
      { reflexivity. }
    + eapply H; done!.
Qed.

Corollary supOfScottContinuousMaps_isContinuous {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (F : ensemble `[D -> D'])
  (F_isDirected : isDirected F)
  : isContinuous (supOfScottContinuousMaps F F_isDirected).
Proof with eauto with *.
  eapply the_main_reason_for_introducing_ScottTopology.
  - ii. eapply leProp_antisymmetry; eapply supOfScottContinuousMaps_isMonotonic...
  - intros X X_isDirected.
    pose proof (supremum_cpo_spec X X_isDirected) as sup_X_is_supremum_of_X.
    exists (supremum_cpo X X_isDirected), (supOfScottContinuousMaps F F_isDirected (supremum_cpo X X_isDirected)).
    pose proof (supOfScottContinuousMaps_preserves_supremum F X (supremum_cpo X X_isDirected) F_isDirected X_isDirected sup_X_is_supremum_of_X) as claim1...
Qed.

Definition supremum_of_ScottContinuousMaps {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (F : ensemble `[D -> D']) (F_isDirected : isDirected F) : `[D -> D'] :=
  @exist (D -> D') isContinuous (supOfScottContinuousMaps F F_isDirected) (supOfScottContinuousMaps_isContinuous F F_isDirected).

Lemma supremum_of_ScottContinuousMaps_is_supremum {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (F : ensemble `[D -> D']) (F_isDirected : isDirected F)
  : is_supremum_of (supremum_of_ScottContinuousMaps F F_isDirected) F.
Proof with eauto with *.
  intros f. split.
  - intros ? f_i ?. rewrite <- H. intros x. simpl.
    eapply supOfScottContinuousMaps_isSupremum with (F := F) (F_isDirected := F_isDirected); done!.
  - intros ?. intros x; simpl. unfold supOfScottContinuousMaps.
    set (sup_F_x := supremum_cpo (E.image (fun f_i => proj1_sig f_i x) F) (supOfScottContinuousMaps_isWellDefined F F_isDirected x)).
    pose proof (sup_F_x_isSupremum := supremum_cpo_spec (E.image (fun f_i => proj1_sig f_i x) F) (supOfScottContinuousMaps_isWellDefined F F_isDirected x)).
    eapply sup_F_x_isSupremum. intros y ?. s!. destruct IN as [f_i [-> f_i_in]]. eapply H...
Qed.

Definition botOfScottContinuousMaps {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} : D -> D' :=
  fun x => bottom_cpo.

Lemma botOfScottContinuousMaps_isContinuous {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'}
  : isContinuous (botOfScottContinuousMaps (D := D) (D' := D')).
Proof with eauto with *.
  intros O O_isOpen. unfold botOfScottContinuousMaps. inversion O_isOpen. split.
  - ii. s!. des. done!.
  - ii. s!. des. subst y. inv H. des. exists x0. done!.
Qed.

Definition BotOfScottContinuousMaps {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} : `[D -> D'] :=
  @exist (D -> D') isContinuous botOfScottContinuousMaps botOfScottContinuousMaps_isContinuous.

Lemma BottomOfScottContinuousMaps_isBottom {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'}
  : forall f : `[D -> D'], BotOfScottContinuousMaps =< f.
Proof.
  intros f. exact (fun x => bottom_cpo_spec (proj1_sig f x)).
Qed.

#[global]
Instance ScottContinuousMaps_isCpo {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} : isCpo `[D -> D'] :=
  { bottom_cpo := BotOfScottContinuousMaps
  ; supremum_cpo := supremum_of_ScottContinuousMaps
  ; bottom_cpo_spec := BottomOfScottContinuousMaps_isBottom
  ; supremum_cpo_spec := supremum_of_ScottContinuousMaps_is_supremum
  }.

Lemma bottom_of_pair_isBottom {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'}
  : forall x : D * D', (bottom_cpo, bottom_cpo) =< x.
Proof.
  intros [x1 x2]. split; [exact (bottom_cpo_spec x1) | exact (bottom_cpo_spec x2)].
Qed.

Lemma image_fst_preservesDirectedness {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (X : ensemble (D * D'))
  (X_isDirected : isDirected X)
  : isDirected (E.image fst X).
Proof with eauto with *.
  inversion X_isDirected. destruct NONEMPTY as [x0 IN]. destruct x0 as [x1_0 x2_0]. split.
  - exists (x1_0); done!.
  - intros x1_1 x2_1 ? ?. s!. destruct x1_IN as [[x1 x1_2] [-> H_IN1]], x2_IN as [[x2 x2_2] [-> H_IN2]]; simpl in *.
    pose proof (DIRECTED' _ _ H_IN1 H_IN2) as [[x3_1 x3_2] [? [[? ?] [? ?]]]]; simpl in *.
    exists (x3_1); done!.
Qed.

Lemma image_snd_preservesDirectedness {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (X : ensemble (D * D'))
  (X_isDirected : isDirected X)
  : isDirected (E.image snd X).
Proof with eauto with *.
  inversion X_isDirected. destruct NONEMPTY as [x0 IN]. destruct x0 as [x1_0 x2_0]. split; unnw.
  - exists (x2_0); done!.
  - intros x1_2 x2_2 ? ?. s!. destruct x1_IN as [[x1_1 x1] [-> H_IN1]], x2_IN as [[x2_1 x2] [-> H_IN2]]; simpl in *.
    pose proof (DIRECTED' _ _ H_IN1 H_IN2) as [[x3_1 x3_2] [? [[? ?] [? ?]]]]; simpl in *.
    exists (x3_2); done!.
Qed.

Lemma supremum_of_pair_is_supremum {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} (X : ensemble (D * D'))
  (X_isDirected : isDirected X)
  : is_supremum_of (supremum_cpo (E.image fst X) (image_fst_preservesDirectedness X X_isDirected), supremum_cpo (E.image snd X) (image_snd_preservesDirectedness X X_isDirected)) X.
Proof with eauto with *.
  intros [z1 z2]. split; intros ?; s!.
  - destruct H as [SUPREMUM_LE_UPPER_BOUND1 SUPREMUM_LE_UPPER_BOUND2]; simpl in *. intros [x1 x2] ?; s!. split; simpl.
    + rewrite <- SUPREMUM_LE_UPPER_BOUND1. eapply supremum_cpo_spec... done!.
    + rewrite <- SUPREMUM_LE_UPPER_BOUND2. eapply supremum_cpo_spec... done!.
  - inversion X_isDirected. s!. des. destruct x0 as [x1_0 x2_0]. split; simpl.
    + eapply supremum_cpo_spec. intros x1 ?. s!. destruct IN as [[x1_1 x2_1] [-> H_IN]]. exploit (H (x1_1, x2_1))... simpl; i. done!.
    + eapply supremum_cpo_spec. intros x1 ?. s!. destruct IN as [[x1_1 x2_1] [-> H_IN]]. exploit (H (x1_1, x2_1))... simpl; i. done!.
Qed.

#[global]
Instance direct_product_of_two_Cpos {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'} : isCpo (D * D') :=
  { bottom_cpo := (bottom_cpo, bottom_cpo)
  ; supremum_cpo (X : ensemble (D * D')) (X_isDirected : isDirected X) := (supremum_cpo (E.image fst X) (image_fst_preservesDirectedness X X_isDirected), supremum_cpo (E.image snd X) (image_snd_preservesDirectedness X X_isDirected))
  ; bottom_cpo_spec := bottom_of_pair_isBottom
  ; supremum_cpo_spec := supremum_of_pair_is_supremum
  }.

Definition seperately_monotonic {D : Type} {D' : Type} {D'' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {PROSET'' : isProset D''} {CPO : isCpo D} {CPO' : isCpo D'} {CPO'' : isCpo D''} (f : D * D' -> D'') : Prop :=
  (forall x2 : D', isMonotonic1 (fun x1 : D => f (x1, x2))) /\ (forall x1 : D, isMonotonic1 (fun x2 : D' => f (x1, x2))).

Lemma seperately_monotonic_iff_monotonic {D : Type} {D' : Type} {D'' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {PROSET'' : isProset D''} {CPO : isCpo D} {CPO' : isCpo D'} {CPO'' : isCpo D''} (f : D * D' -> D'')
  : seperately_monotonic f <-> isMonotonic1 f.
Proof.
  split; [intros [? ?]; s! | intros f_monotonic].
  - ii. destruct x1 as [x1_1 x1_2]. destruct x2 as [x2_1 x2_2]. simpl in x_LE.
    transitivity (f (x2_1, x1_2)); [eapply H | eapply H0]; done!.
  - split; ii; eapply f_monotonic; split; done!.
Qed.

Lemma f_x1_sup_X2_eq_sup_f_x1_X2 {D : Type} {D' : Type} {D'' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {PROSET'' : isProset D''} {CPO : isCpo D} {CPO' : isCpo D'} {CPO'' : isCpo D''} (f : D * D' -> D'') (x1 : D) (X2 : ensemble D') (sup_X2 : D')
  (f_isContinuous : isContinuous f)
  (X2_isDirected : isDirected X2)
  (sup_X2_is_supremum_of_X2 : is_supremum_of sup_X2 X2)
  : is_supremum_of (f (x1, sup_X2)) (E.image (fun x2 => f (x1, x2)) X2).
Proof with eauto with *.
  revert x1 X2 X2_isDirected sup_X2 sup_X2_is_supremum_of_X2.
  assert (f_isMonotonic : isMonotonic1 f).
  { eapply ScottContinuousMap_isMonotonic... }
  assert (f_isMonotonic_at2 : forall x1, isMonotonic1 (fun x2 => f (x1, x2))).
  { eapply seperately_monotonic_iff_monotonic... }
  assert (COMPAT_WITH_eqProp : eqPropCompatible1 f).
  { intros [x1 x2] [x1' x2'] [H_eq1 H_eq2]; simpl in *. eapply leProp_antisymmetry; eapply f_isMonotonic; split... }
  intros x1.
  assert (COMPAT_WITH_eqProp' : eqPropCompatible1 (fun x2 => f (x1, x2))).
  { ii. eapply COMPAT_WITH_eqProp. simpl. now rewrite x_EQ. }
  intros X2 X2_isDirected.
  set (X := E.image (fun x2 => (x1, x2)) X2).
  set (Y := E.image (fun x2 => f (x1, x2)) X2).
  assert (X_isDirected : isDirected X).
  { inversion X2_isDirected. des. rename x0 into x2_0. split.
    - unfold X. exists (x1, x2_0); done!.
    - intros ? ? x1_in_X x2_in_X. unfold X in *. s!.
      destruct x1_in_X as [? [H_eq x2_1_in]]. inv H_eq.
      destruct x2_in_X as [? [H_eq x2_2_in]]. inv H_eq.
      pose proof (DIRECTED' x x0 x2_1_in x2_2_in) as [x2_3 [? [x2_1_le_x2_3 x2_2_le_x2_3]]].
      exists (x1, x2_3). simpl. repeat split; done!.
  }
  intros sup_X2 sup_X2_is_supremum_of_X2.
  set (sup_X := supremum_cpo X X_isDirected). pose proof (supremum_cpo_spec X X_isDirected) as sup_X_is_supremum_of_X. fold sup_X in sup_X_is_supremum_of_X.
  assert (claim1 : (x1, sup_X2) == sup_X).
  { eapply supremum_unique with (X2 := X); [intros [x_1 x_2] | trivial | reflexivity]. split.
    - intros [x1_le_x_1 sup_X2_le_x2] [x_1' x_2'] H_IN'. unfold X in *. s!. destruct H_IN' as [x [H_EQ H_IN']].
      apply pair_equal_spec in H_EQ. destruct H_EQ; subst x_1' x_2'. split; simpl in *.
      + trivial.
      + eapply sup_X2_is_supremum_of_X2...
    - intros ?. s!. split; simpl.
      + inversion X2_isDirected. des. enough (to_show : (x1, x0) =< (x_1, x_2)) by exact (proj1 to_show). unfold X in *. eapply H; econs...
      + eapply sup_X2_is_supremum_of_X2. intros x2 ?; des. eapply H with (x := (x1, x2))... unfold X. econs...
  }
  assert (claim2 : f (x1, sup_X2) == f sup_X).
  { eapply COMPAT_WITH_eqProp... }
  assert (PRESERVES_SUPREMUM : exists sup_X', exists sup_Y', is_supremum_of sup_X' X /\ is_supremum_of sup_Y' (E.image f X) /\ f sup_X' == sup_Y').
  { eapply the_main_reason_for_introducing_ScottTopology with (f := f)... }
  destruct PRESERVES_SUPREMUM as [sup_X' [sup_Y' [sup_X'_isSupremum [sup_Y'_isSupremum f_x1_sup_X'_eq_sup_Y']]]].
  assert (claim3 : is_supremum_of (f sup_X) (E.image f X)).
  { eapply supremum_congruence with (sup_X1 := f sup_X') (X1 := E.image f X).
    - rewrite f_x1_sup_X'_eq_sup_Y'...
    - eapply COMPAT_WITH_eqProp. symmetry. eapply supremum_unique...
    - reflexivity.
  }
  eapply supremum_congruence with (sup_X1 := f sup_X) (X1 := E.image f X); trivial.
  - symmetry...
  - intros y. split; intros H_IN; unfold X, Y in *; s!; des; subst y.
    + destruct x as [x_1 x_2]; done!.
    + exists (x1, x). done!.
Qed.

Corollary f2_cont_if_f_cont {D : Type} {D' : Type} {D'' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {PROSET'' : isProset D''} {CPO : isCpo D} {CPO' : isCpo D'} {CPO'' : isCpo D''} (f : D * D' -> D'') (x1 : D)
  (f_isContinuous : isContinuous f)
  : isContinuous (fun x2 => f (x1, x2)).
Proof with eauto with *.
  revert x1.
  assert (f_monotonic : isMonotonic1 f).
  { eapply ScottContinuousMap_isMonotonic... }
  assert (f2_isMonotonic : forall x1, isMonotonic1 (fun x2 => f (x1, x2))).
  { ii. eapply ScottContinuousMap_isMonotonic; trivial. split... }
  assert (f_preserves_eqProp : eqPropCompatible1 f).
  { intros [x1 x2] [x1' x2'] [? ?]; simpl in *. eapply leProp_antisymmetry; eapply f_monotonic; split... }
  intros x1. eapply the_main_reason_for_introducing_ScottTopology.
  - ii. eapply f_preserves_eqProp. split...
  - intros X2 X2_isDirected. set (sup_X2 := supremum_cpo X2 X2_isDirected). exists (sup_X2), (f (x1, sup_X2)).
    pose proof (supremum_cpo_spec X2 X2_isDirected) as claim1. split; trivial. split.
    + eapply f_x1_sup_X2_eq_sup_f_x1_X2...
    + reflexivity.
Qed.

Lemma f_sup_X1_x2_eq_sup_f_X1_x2 {D : Type} {D' : Type} {D'' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {PROSET'' : isProset D''} {CPO : isCpo D} {CPO' : isCpo D'} {CPO'' : isCpo D''} (f : D * D' -> D'') (x2 : D') (X1 : ensemble D) (sup_X1 : D)
  (f_isContinuous : isContinuous f)
  (X1_isDirected : isDirected X1)
  (sup_X1_is_supremum_of_X1 : is_supremum_of sup_X1 X1)
  : is_supremum_of (f (sup_X1, x2)) (E.image (fun x1 => f (x1, x2)) X1).
Proof with eauto with *.
  revert x2 X1 X1_isDirected sup_X1 sup_X1_is_supremum_of_X1.
  assert (f_isMonotonic : isMonotonic1 f).
  { eapply ScottContinuousMap_isMonotonic... }
  assert (f_isMonotonic_at2 : forall x2, isMonotonic1 (fun x1 => f (x1, x2))).
  { eapply seperately_monotonic_iff_monotonic... }
  assert (f_preserves_eqProp : eqPropCompatible1 f).
  { intros [x1 x2] [x1' x2'] [H_eq1 H_eq2]; simpl in *. eapply leProp_antisymmetry; eapply f_isMonotonic; split... }
  intros x2.
  assert (f_preserves_eqProp_at2 : eqPropCompatible1 (fun x1 => f (x1, x2))).
  { ii. eapply leProp_antisymmetry; eapply f_isMonotonic_at2... }
  intros X1 X1_isDirected.
  set (X := E.image (fun x1 => (x1, x2)) X1).
  set (Y := E.image (fun x1 => f (x1, x2)) X1).
  assert (X_isDirected : isDirected X).
  { inversion X1_isDirected. des. rename x0 into x1_0. unfold X, Y in *. split.
    - exists (x1_0, x2); done!.
    - intros [x1_1 x2_1] [x1_2 x2_2] x1_in_X x2_in_X. s!.
      destruct x1_in_X as [x1 [H_eq x1_1_in]]. inversion H_eq; subst x2_1 x1. clear H_eq.
      destruct x2_in_X as [x1 [H_eq x1_2_in]]. inversion H_eq; subst x2_2 x1. clear H_eq.
      pose proof (DIRECTED' x1_1 x1_2 x1_1_in x1_2_in) as [x1_3 [? [x1_1_le_x1_3 x1_2_le_x1_3]]]; s!.
      exists (x1_3, x2). repeat split... unfold X, Y in *. done!.
  }
  intros sup_X1 sup_X1_is_supremum_of_X1.
  set (sup_X := supremum_cpo X X_isDirected). pose proof (supremum_cpo_spec X X_isDirected) as sup_X_is_supremum_of_X. fold sup_X in sup_X_is_supremum_of_X.
  assert (claim1 : (sup_X1, x2) == sup_X).
  { eapply supremum_unique with (X2 := X); [intros [x_1 x_2] | trivial | reflexivity]. split.
    - intros [sup_X1_le_x1 x2_le_x_2] [x_1' x_2'] H_IN'. simpl in *. unfold X, Y in *. s!. destruct H_IN' as [x1 [H_EQ x1_in]].
      apply pair_equal_spec in H_EQ. destruct H_EQ; subst x_1' x_2'. split; simpl in *; trivial. eapply sup_X1_is_supremum_of_X1...
    - intros ?. split; simpl.
      + eapply sup_X1_is_supremum_of_X1. unfold X, Y in *. intros x1 ?. eapply H with (x := (x1, x2)); done!.
      + inversion X1_isDirected. des. enough (to_show : (x0, x2) =< (x_1, x_2)) by exact (proj2 to_show). eapply H. unfold X, Y in *. done!.
  }
  assert (claim2 : f (sup_X1, x2) == f sup_X).
  { eapply f_preserves_eqProp... }
  assert (PRESERVES_SUPREMUM : exists sup_X', exists sup_Y', is_supremum_of sup_X' X /\ is_supremum_of sup_Y' (E.image f X) /\ f sup_X' == sup_Y').
  { eapply the_main_reason_for_introducing_ScottTopology with (f := f)... }
  destruct PRESERVES_SUPREMUM as [sup_X' [sup_Y' [sup_X'_isSupremum [sup_Y'_isSupremum f_x1_sup_X'_eq_sup_Y']]]].
  assert (claim3 : is_supremum_of (f sup_X) (E.image f X)).
  { eapply supremum_congruence with (sup_X1 := f sup_X') (X1 := E.image f X).
    - rewrite f_x1_sup_X'_eq_sup_Y'...
    - eapply f_preserves_eqProp. symmetry. eapply supremum_unique...
    - reflexivity.
  }
  eapply supremum_congruence with (sup_X1 := f sup_X) (X1 := E.image f X); trivial.
  - symmetry...
  - intros y. split; intros H_IN; unfold X, Y in *; s!; des; subst y.
    + destruct x as [x_1 x_2]; done!.
    + exists (x, x2). done!.
Qed.

Corollary f1_cont_if_f_cont {D : Type} {D' : Type} {D'' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {PROSET'' : isProset D''} {CPO : isCpo D} {CPO' : isCpo D'} {CPO'' : isCpo D''} (f : D * D' -> D'') (x2 : D')
  (f_isContinuous : isContinuous f)
  : isContinuous (fun x1 => f (x1, x2)).
Proof with eauto with *.
  revert x2.
  assert (f_monotonic : isMonotonic1 f).
  { eapply ScottContinuousMap_isMonotonic... }
  assert (f1_isMonotonic : forall x2, isMonotonic1 (fun x1 => f (x1, x2))).
  { ii. eapply ScottContinuousMap_isMonotonic; trivial. split... }
  assert (f_preserves_eqProp : eqPropCompatible1 f).
  { intros [x1 x2] [x1' x2'] [? ?]; simpl in *. eapply leProp_antisymmetry; eapply f_monotonic; split... }
  intros x2. eapply the_main_reason_for_introducing_ScottTopology.
  - ii. eapply f_preserves_eqProp. split...
  - intros X1 X1_isDirected. set (sup_X1 := supremum_cpo X1 X1_isDirected). exists (sup_X1), (f (sup_X1, x2)).
    pose proof (supremum_cpo_spec X1 X1_isDirected) as claim1. split; trivial. split.
    + eapply f_sup_X1_x2_eq_sup_f_X1_x2...
    + reflexivity.
Qed.

Lemma f_sup_X1_sup_X2_eq_sup_f_X1_X2 {D : Type} {D' : Type} {D'' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {PROSET'' : isProset D''} {CPO : isCpo D} {CPO' : isCpo D'} {CPO'' : isCpo D''} (f : D * D' -> D'') (X : ensemble (D * D')) (sup_X1 : D) (sup_X2 : D')
  (f1_isContinuous : forall x2, isContinuous (fun x1 => f (x1, x2)))
  (f2_isContinuous : forall x1, isContinuous (fun x2 => f (x1, x2)))
  (X_isDirected : isDirected X)
  (sup_X1_is_supremum_of_X1 : is_supremum_of sup_X1 (E.image fst X))
  (sup_X2_is_supremum_of_X2 : is_supremum_of sup_X2 (E.image snd X))
  : is_supremum_of (f (sup_X1, sup_X2)) (E.image f X).
Proof with eauto with *.
  revert X X_isDirected sup_X1 sup_X2 sup_X1_is_supremum_of_X1 sup_X2_is_supremum_of_X2.
  assert (f1_isMonotonic : forall x2, isMonotonic1 (fun x1 => f (x1, x2))).
  { intros x2. eapply ScottContinuousMap_isMonotonic... }
  assert (f2_isMonotonic : forall x1, isMonotonic1 (fun x2 => f (x1, x2))).
  { intros x1. eapply ScottContinuousMap_isMonotonic... }
  assert (f1_preserves_eqProp : forall x2, eqPropCompatible1 (fun x1 => f (x1, x2))).
  { ii. eapply leProp_antisymmetry; eapply @compatibleWith_leProp_1 with (f := fun x1 => f (x1, x2))... }
  assert (f2_preserves_eqProp : forall x1, eqPropCompatible1 (fun x2 => f (x1, x2))).
  { ii. eapply leProp_antisymmetry; eapply @compatibleWith_leProp_1 with (f := fun x2 => f (x1, x2))... }
  assert (f_preserves_eqProp : eqPropCompatible1 f).
  { intros [x1 x2] [x1' x2'] [? ?]; simpl in *. transitivity (f (x1', x2)); [eapply f1_preserves_eqProp | eapply f2_preserves_eqProp]... }
  intros X X_isDirected. set (X1 := E.image fst X). set (X2 := E.image snd X).
  set (image_fst_preservesDirectedness X X_isDirected) as X1_isDirected. fold X1 in X1_isDirected.
  set (image_snd_preservesDirectedness X X_isDirected) as X2_isDirected. fold X2 in X2_isDirected.
  assert (mayday : is_supremum_of (supremum_cpo X1 X1_isDirected, supremum_cpo X2 X2_isDirected) X) by exact (supremum_cpo_spec X X_isDirected).
  assert (claim1 : forall x1, exists sup_X2_x1, exists sup_f_X2_x1, is_supremum_of sup_X2_x1 X2 /\ is_supremum_of sup_f_X2_x1 (E.image (fun x2 => f (x1, x2)) X2) /\ f (x1, sup_X2_x1) == sup_f_X2_x1).
  { intros x1. eapply the_main_reason_for_introducing_ScottTopology with (f := fun x2 => f (x1, x2))... }
  assert (claim2 : forall x2, exists sup_X1_x2, exists sup_f_X1_x2, is_supremum_of sup_X1_x2 X1 /\ is_supremum_of sup_f_X1_x2 (E.image (fun x1  => f (x1, x2)) X1) /\ f (sup_X1_x2, x2) == sup_f_X1_x2).
  { intros x2. eapply the_main_reason_for_introducing_ScottTopology with (f := fun x1 => f (x1, x2))... }
  set (sup_X1 := supremum_cpo X1 X1_isDirected). fold sup_X1 in mayday.
  set (sup_X2 := supremum_cpo X2 X2_isDirected). fold sup_X2 in mayday.
  pose proof (sup_X1_is_supremum_of_X1 := supremum_cpo_spec X1 X1_isDirected). fold sup_X1 in sup_X1_is_supremum_of_X1.
  pose proof (sup_X2_is_supremum_of_X2 := supremum_cpo_spec X2 X2_isDirected). fold sup_X2 in sup_X2_is_supremum_of_X2.
  assert (claim3 : is_supremum_of (f (sup_X1, sup_X2)) (E.image (fun x2 => f (sup_X1, x2)) X2)).
  { pose proof (claim1 sup_X1) as [sup_X2_x1 [sup_f_X2_x1 [sup_X2_x1_isSupremum [sup_f_X1_x2_isSupremum H_EQ]]]].
    eapply supremum_congruence with (sup_X1 := sup_f_X2_x1).
    - exact (sup_f_X1_x2_isSupremum).
    - rewrite <- H_EQ. eapply f_preserves_eqProp. split; simpl.
      + reflexivity.
      + eapply supremum_unique...
    - reflexivity.
  }
  assert (claim4 : forall x2, x2 \in X2 -> is_supremum_of (f (sup_X1, x2)) (E.image (fun x1 => f (x1, x2)) X1)).
  { intros x2 x2_in. pose proof (claim2 x2) as [sup_X1' [sup_f_X1_x2' [sup_X1'_isSupremum [sup_f_X1_x2'_isSupremum H_EQ]]]].
    eapply supremum_congruence with (sup_X1 := sup_f_X1_x2').
    - exact (sup_f_X1_x2'_isSupremum).
    - rewrite <- H_EQ. eapply f_preserves_eqProp. split; simpl.
      + eapply supremum_unique...
      + reflexivity.
    - reflexivity.
  }
  assert (claim5 : is_supremum_of (f (sup_X1, sup_X2)) (map_suprema (E.image (fun x2 => E.image (fun x1 => f (x1, x2)) X1) X2))).
  { intros upper_bound. split.
    - intros ? sup_Y [Y [Y_in sup_Y_isSupremum]]. s!. destruct Y_in as [x2 [? x2_in]]; subst Y.
      eapply sup_Y_isSupremum. intros y ?. change (y \in E.image (fun x1 => f (x1, x2)) X1) in IN. s!. destruct IN as [x1 [? x1_in]]; subst y.
      rewrite <- H. transitivity (f (sup_X1, x2)).
      + eapply f1_isMonotonic. eapply sup_X1_is_supremum_of_X1...
      + eapply f2_isMonotonic. eapply sup_X2_is_supremum_of_X2...
    - intros ?. s!. eapply claim3. intros y ?. change (y \in E.image (fun x2 => f (sup_X1, x2)) X2) in IN. s!. destruct IN as [x2 [? x2_in]]; subst y.
      eapply H. exists (E.image (fun x1 => f (x1, x2)) X1). split. econs... red. done!.
  }
  assert (claim6 : is_supremum_of (f (sup_X1, sup_X2)) (E.unions (E.image (fun x2 => E.image (fun x1 => f (x1, x2)) X1) X2))).
  { eapply supremum_of_map_suprema_is_supremum_of_unions...
    intros Y ?. s!. destruct H as [x2 [? x2_in]]; subst Y. exists (f (sup_X1, x2))...
  }
  assert (claim7 : is_supremum_of (f (sup_X1, sup_X2)) (E.image f X)).
  { intros upper_bound. split.
    - intros ? y ?. s!. destruct IN as [[x1 x2] [? H_IN]]; subst y.
      eapply claim6... exists (E.image (fun x1' => f (x1', x2)) X1). unfold X1 in *. econs... econs... reflexivity. econs... econs... reflexivity.
    - ii. eapply claim6. intros y y_in. s!. destruct y_in as [Y [y_in_Y Y_in]]. s!.
      destruct Y_in as [x2 [? x2_in_X2]]; subst Y. s!. destruct y_in_Y as [x1 [? x1_in_X1]]; subst y.
      unfold X1, X2 in *. s!. destruct x1_in_X1 as [[x1_1 x2_1] [? x1_in_X]]; subst x1. destruct x2_in_X2 as [[x1_2 x2_2] [? x2_in_X]]; subst x2. inversion X_isDirected.
      pose proof (DIRECTED' (x1_1, x2_1) (x1_2, x2_2) x1_in_X x2_in_X) as [[x1_3 x2_3] [x3_in [[x1_1_le_x1_3 x2_1_le_x2_3] [x1_2_le_x1_3 x2_2_le_x2_3]]]]; simpl in *.
      transitivity (f (x1_3, x2_3)).
      + transitivity (f (x1_1, x2_3)); [eapply f2_isMonotonic | eapply f1_isMonotonic]...
      + eapply H... econs...
  }
  intros sup_X1' sup_X2' sup_X1'_isSupremum sup_X2'_isSupremum.
  assert (to_show : f (sup_X1, sup_X2) == f (sup_X1', sup_X2')).
  { eapply f_preserves_eqProp. split; simpl; eapply supremum_unique... }
  rewrite <- to_show...
Qed.

Corollary f_cont_if_f1_and_f2_cont {D : Type} {D' : Type} {D'' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {PROSET'' : isProset D''} {CPO : isCpo D} {CPO' : isCpo D'} {CPO'' : isCpo D''} (f : D * D' -> D'')
  (f1_isContinuous : forall x2, isContinuous (fun x1 => f (x1, x2)))
  (f2_isContinuous : forall x1, isContinuous (fun x2 => f (x1, x2)))
  : isContinuous f.
Proof with eauto with *.
  assert (f1_isMonotonic : forall x2, isMonotonic1 (fun x1 => f (x1, x2))).
  { intros x2. eapply ScottContinuousMap_isMonotonic... }
  assert (f2_isMonotonic : forall x1, isMonotonic1 (fun x2 => f (x1, x2))).
  { intros x1. eapply ScottContinuousMap_isMonotonic... }
  assert (f1_preserves_eqProp : forall x2, eqPropCompatible1 (fun x1 => f (x1, x2))).
  { ii. eapply leProp_antisymmetry; eapply @compatibleWith_leProp_1 with (f := fun x1 => f (x1, x2))... }
  assert (f2_preserves_eqProp : forall x1, eqPropCompatible1 (fun x2 => f (x1, x2))).
  { ii. eapply leProp_antisymmetry; eapply @compatibleWith_leProp_1 with (f := fun x2 => f (x1, x2))... }
  assert (f_preserves_eqProp : eqPropCompatible1 f).
  { intros [x1 x2] [x1' x2'] [? ?]; simpl in *. transitivity (f (x1', x2)); [eapply f1_preserves_eqProp | eapply f2_preserves_eqProp]... }
  eapply the_main_reason_for_introducing_ScottTopology...
  intros X X_isDirected; unnw. set (X1 := E.image fst X). set (X2 := E.image snd X).
  set (image_fst_preservesDirectedness X X_isDirected) as X1_isDirected. fold X1 in X1_isDirected.
  set (image_snd_preservesDirectedness X X_isDirected) as X2_isDirected. fold X2 in X2_isDirected.
  assert (mayday : is_supremum_of (supremum_cpo X1 X1_isDirected, supremum_cpo X2 X2_isDirected) X) by exact (supremum_cpo_spec X X_isDirected).
  set (sup_X1 := supremum_cpo X1 X1_isDirected). fold sup_X1 in mayday.
  set (sup_X2 := supremum_cpo X2 X2_isDirected). fold sup_X2 in mayday.
  assert (sup_X1_is_supremum_of_X1 : is_supremum_of sup_X1 X1) by exact (supremum_cpo_spec X1 X1_isDirected).
  assert (sup_X2_is_supremum_of_X2 : is_supremum_of sup_X2 X2) by exact (supremum_cpo_spec X2 X2_isDirected).
  exists (sup_X1, sup_X2), (f (sup_X1, sup_X2)). split; trivial. split; [eapply f_sup_X1_sup_X2_eq_sup_f_X1_X2 | reflexivity]...
Qed.

Theorem seperately_continuous_iff {D : Type} {D' : Type} {D'' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {PROSET'' : isProset D''} {CPO : isCpo D} {CPO' : isCpo D'} {CPO'' : isCpo D''} (f : D * D' -> D'')
  : ((forall x2, isContinuous (fun x1 => f (x1, x2))) /\ (forall x1, isContinuous (fun x2 => f (x1, x2)))) <-> isContinuous f.
Proof with eauto.
  split.
  - intros [? ?]. eapply f_cont_if_f1_and_f2_cont...
  - intros ?; split; [intros x1; eapply f1_cont_if_f_cont | intros x2; eapply f2_cont_if_f_cont]...
Qed.

Section SCOTT_APP.

Context {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {CPO : isCpo D} {CPO' : isCpo D'}.

Let scottApp1 : (`[D -> D'] * D) -> D' :=
  fun '(f, x) => proj1_sig f x.

Lemma scottApp1_isMonotonic
  : isMonotonic1 scottApp1.
Proof with eauto with *.
  intros [f1 x1] [f2 x2] [f1_le_f2 x1_le_x2]; simpl in *. transitivity (proj1_sig f1 x2).
  - eapply ScottContinuousMap_isMonotonic... exact (proj2_sig f1).
  - clear x1 x1_le_x2. revert x2. change (f1 =< f2)...
Qed.

Lemma scottApp1_preserves_eqProp (f1 : `[D -> D']) (f2 : `[D -> D']) (x1 : D) (x2 : D)
  (f1_eq_f2 : f1 == f2)
  (x1_eq_x2 : x1 == x2)
  : scottApp1 (f1, x1) == scottApp1 (f2, x2).
Proof.
  eapply leProp_antisymmetry; eapply scottApp1_isMonotonic.
  - split; simpl fst; simpl snd. now rewrite -> f1_eq_f2. now rewrite -> x1_eq_x2.
  - split; simpl fst; simpl snd. now rewrite <- f1_eq_f2. now rewrite <- x1_eq_x2.
Qed.

Lemma scottApp1_isContinuous
  : isContinuous scottApp1.
Proof with eauto with *.
  eapply f_cont_if_f1_and_f2_cont.
  - intros x. eapply the_main_reason_for_introducing_ScottTopology.
    + ii; eapply scottApp1_preserves_eqProp...
    + intros F F_isDirected. set (Y := E.image (fun f_i => scottApp1 (f_i, x)) F). simpl in Y. set (sup_F := supremum_cpo F F_isDirected).
      assert (sup_F_is_supremum_of_F : is_supremum_of sup_F F) by exact (supremum_cpo_spec F F_isDirected).
      exists (sup_F), (scottApp1 (sup_F, x)). split; trivial. split; [simpl | reflexivity].
      eapply supOfScottContinuousMaps_isSupremum.
  - exact (fun f => proj2_sig f).
Qed.

Definition ScottApp : `[(`[D -> D'] * D) -> D'] :=
  @exist ((`[D -> D'] * D) -> D') isContinuous scottApp1 scottApp1_isContinuous.

End SCOTT_APP.

Section SCOTT_LAM.

Context {D : Type} {D' : Type} {D'' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {PROSET'' : isProset D''} {CPO : isCpo D} {CPO' : isCpo D'} {CPO'' : isCpo D''}.

Let scottLam1 (f : `[(D * D') -> D'']) (x1 : D) (x2 : D') : D'' :=
  proj1_sig f (x1, x2).

Let scottLam2 (f : `[(D * D') -> D'']) (x1 : D) : `[D' -> D''] :=
  @exist (D' -> D'') isContinuous (scottLam1 f x1) (f2_cont_if_f_cont (proj1_sig f) x1 (proj2_sig f)).

Lemma scottLam2_isContinuous (f : `[(D * D') -> D''])
  : isContinuous (scottLam2 f).
Proof with eauto with *.
  assert (f_isMonotonic : isMonotonic1 (proj1_sig f)).
  { eapply ScottContinuousMap_isMonotonic. exact (proj2_sig f). }
  pose proof (proj2 (seperately_monotonic_iff_monotonic (proj1_sig f)) f_isMonotonic) as [? ?].
  assert (scottLam2_f_isMonotonic : isMonotonic1 (scottLam2 f)).
  { intros x1 x1' x1_le_x1' x2. simpl. unfold scottLam1. eapply H... }
  assert (scottLam2_f_preserves_eqProp : eqPropCompatible1 (scottLam2 f)).
  { ii. eapply leProp_antisymmetry; eapply scottLam2_f_isMonotonic... }
  eapply the_main_reason_for_introducing_ScottTopology; trivial.
  intros X1 X1_isDirected; unnw. set (sup_X1 := supremum_cpo X1 X1_isDirected).
  assert (Y_isDirected : isDirected (E.image (scottLam2 f) X1)).
  { eapply preservesDirectedness_if_isMonotonic... }
  set (Y := E.image (scottLam2 f) X1). fold Y in Y_isDirected. set (sup_Y := supremum_cpo Y Y_isDirected).
  assert (sup_X1_is_supremum_of_X1 : is_supremum_of sup_X1 X1) by exact (supremum_cpo_spec X1 X1_isDirected).
  assert (sup_Y_is_supremum_of_Y : is_supremum_of sup_Y Y) by exact (supremum_cpo_spec Y Y_isDirected).
  exists (sup_X1), (sup_Y). split; trivial. split; trivial.
  assert (claim1 : forall x1, x1 \in X1 -> forall x2, proj1_sig f (x1, x2) =< proj1_sig f (sup_X1, x2)).
  { intros x1 x1_in_X1 x2. eapply f_isMonotonic. split; [eapply sup_X1_is_supremum_of_X1 | reflexivity]... }
  intros x2. simpl. unfold scottLam1. pose proof (f_sup_X1_x2_eq_sup_f_X1_x2 (proj1_sig f) x2 X1 sup_X1 (proj2_sig f) X1_isDirected sup_X1_is_supremum_of_X1) as claim2. eapply supremum_unique.
  - exact (claim2).
  - eapply supOfScottContinuousMaps_isSupremum.
  - intros z. split.
    + intros z_in. s!. destruct z_in as [x1 [? x1_in_X1]]; subst z. exists (scottLam2 f x1). split. reflexivity. unfold scottLam2. econs... reflexivity.
    + intros z_in. rewrite E.in_image_iff in z_in. destruct z_in as [f1 [? f1_in_Y]]; subst z. unfold Y in f1_in_Y. rewrite E.in_image_iff in f1_in_Y. destruct f1_in_Y as [x1 [? x1_in_X1]]; subst f1... econs... reflexivity.
Qed.

Let scottLam3 (f : `[(D * D') -> D'']) : `[D -> `[D' -> D'']] :=
  @exist (D -> `[D' -> D'']) isContinuous (scottLam2 f) (scottLam2_isContinuous f).

Lemma scottLam3_isContinuous
  : isContinuous scottLam3.
Proof with eauto with *.
  assert (scottLam3_isMonotonic : isMonotonic1 scottLam3).
  { ii. eapply x_LE. }
  assert (scottLam3_preserves_eqProp : eqPropCompatible1 scottLam3).
  { ii. eapply x_EQ. }
  eapply the_main_reason_for_introducing_ScottTopology; trivial.
  intros F F_isDirected. set (Y := E.image scottLam3 F). set (sup_F := supremum_cpo F F_isDirected).
  assert (sup_F_is_supremum_of_F : is_supremum_of sup_F F) by exact (supremum_cpo_spec F F_isDirected).
  assert (Y_isDirected : isDirected Y).
  { eapply preservesDirectedness_if_isMonotonic... }
  set (sup_Y := supremum_cpo Y Y_isDirected).
  assert (sup_Y_is_supremum_of_Y : is_supremum_of sup_Y Y) by exact (supremum_cpo_spec Y Y_isDirected).
  exists (sup_F), (sup_Y). split; trivial. split; trivial.
  eapply supremum_unique with (X1 := E.image scottLam3 F).
  - intros z. split.
    + intros ? f ?. s!. destruct IN as [f1 [? H_IN]]; subst f. intros x1 x2. rewrite <- H. simpl. unfold scottLam1.
      generalize (x1, x2). clear x1 x2. change (f1 =< supremum_cpo F F_isDirected). eapply supremum_cpo_spec...
    + intros ?. intros x1 x2. simpl.
      eapply supOfScottContinuousMaps_isSupremum with (F := F) (F_isDirected := F_isDirected) (x := (x1, x2)).
      intros y ?. s!. destruct IN as [f_i [? H_IN]]; subst y.
      change (proj1_sig (proj1_sig (scottLam3 f_i) x1) x2 =< proj1_sig (proj1_sig z x1) x2). eapply H. econs...
  - exact (sup_Y_is_supremum_of_Y).
  - intros z. split; unfold Y in *.
    + intros H_IN. rewrite E.in_image_iff in H_IN. destruct H_IN as [f_i [? H_IN]]; subst z; done!.
    + intros H_IN. rewrite E.in_image_iff in H_IN. destruct H_IN as [f_i [? H_IN]]; subst z; done!.
Qed.

Definition ScottLam : `[`[(D * D') -> D''] -> `[D -> `[D' -> D'']]] :=
  @exist (`[(D * D') -> D''] -> `[D -> `[D' -> D'']]) isContinuous scottLam3 scottLam3_isContinuous.

End SCOTT_LAM.

Section SCOTT_FIX.

Context {D : Type}.

Fixpoint iterS (n : nat) (f : D -> D) (x : D) {struct n} : D :=
  match n with
  | O => x
  | S n' => f (iterS n' f x)
  end.

Variant IterS (f : D -> D) (x : D) : ensemble D :=
  | In_IterS (n : nat) : iterS n f x \in IterS f x.

#[local] Hint Constructors IterS : core.

Context {PROSET : isProset D} {CPO : isCpo D}.

Lemma iterS_monotonic (f : D -> D)
  (f_isMonotonic : isMonotonic1 f)
  : forall n1 : nat, forall n2 : nat, n1 <= n2 -> iterS n1 f bottom_cpo =< iterS n2 f bottom_cpo.
Proof with eauto with *.
  assert (claim1 : forall n : nat, iterS n f bottom_cpo =< iterS (S n) f bottom_cpo).
  { induction n as [ | n IH]; [eapply bottom_cpo_spec | simpl]... }
  intros n1 n2 n1_le_n2. induction n1_le_n2 as [ | n2 n1_le_n2 IH].
  - reflexivity.
  - rewrite IH...
Qed.

Lemma IterS_f_bottom_isDirected_if_f_isMonotonic (f : D -> D)
  (f_isMonotonic : isMonotonic1 f)
  : isDirected (IterS f bottom_cpo).
Proof with eauto with *.
  assert (claim1 : forall n1 : nat, forall n2 : nat, n1 <= max n1 n2) by lia.
  assert (claim2 : forall n1 : nat, forall n2 : nat, n2 <= max n1 n2) by lia.
  pose proof (claim3 := iterS_monotonic).
  split.
  - exists (iterS 0 f bottom_cpo)...
  - ii. inversion x1_IN; subst. rename n into n1. inversion x2_IN; subst. rename n into n2.
    exists (iterS (max n1 n2) f bottom_cpo). split...
Qed.

Definition lfp_cpo (f : `[D -> D]) : D :=
  supremum_cpo (IterS (proj1_sig f) bottom_cpo) (IterS_f_bottom_isDirected_if_f_isMonotonic (proj1_sig f) (ScottContinuousMap_isMonotonic (proj1_sig f) (proj2_sig f))).

Lemma every_ScottContinuousMap_has_a_fixed_point (f : `[D -> D])
  : lfp_cpo f \in fixedpointsOf (proj1_sig f).
Proof with eauto with *.
  pose proof (lfp_f_is_supremum_of_F := supremum_cpo_spec (IterS (proj1_sig f) bottom_cpo) (IterS_f_bottom_isDirected_if_f_isMonotonic (proj1_sig f) (ScottContinuousMap_isMonotonic (proj1_sig f) (proj2_sig f)))). fold (lfp_cpo f) in lfp_f_is_supremum_of_F.
  pose proof (sup_Y_is_supremum_of_image_f_X_iff_f_sup_X_eq_sup_Y (proj1_sig f) (IterS (proj1_sig f) bottom_cpo)) as claim1.
  enough (to_show : proj1_sig f (lfp_cpo f) == lfp_cpo f) by now do 2 red.
  eapply claim1.
  - exact (proj2_sig f).
  - eapply IterS_f_bottom_isDirected_if_f_isMonotonic. eapply ScottContinuousMap_isMonotonic. exact (proj2_sig f).
  - exact (lfp_f_is_supremum_of_F).
  - ii; split.
    + intros ? y ?. s!. destruct IN as [x [? H_IN]]; subst y. inversion H_IN; subst.
      rewrite <- H. eapply lfp_f_is_supremum_of_F...
      change (iterS (S n) (proj1_sig f) bottom_cpo \in IterS (proj1_sig f) bottom_cpo)...
    + ii. s!. eapply lfp_f_is_supremum_of_F. ii. inversion IN; subst.
      destruct n as [ | n']; simpl.
      { eapply bottom_cpo_spec. }
      { eapply H... econs... }
Qed.

Theorem lfp_returns_the_least_fixed_point (f : `[D -> D])
  : is_lfpOf (lfp_cpo f) (proj1_sig f).
Proof with eauto with *.
  pose proof (every_ScottContinuousMap_has_a_fixed_point f) as claim1.
  split; trivial. intros y ?. s!. rename IN into y_eq_f_y.
  eapply supremum_cpo_spec. ii. inversion IN; subst. induction n as [ | n IH].
  - eapply bottom_cpo_spec.
  - transitivity (proj1_sig f y).
    + simpl. eapply ScottContinuousMap_isMonotonic; [exact (proj2_sig f) | eapply IH]...
    + now rewrite <- y_eq_f_y.
Qed.

Lemma iterS_isMonotonic (n : nat)
  : isMonotonic1 (fun '(f, x) => iterS n (@proj1_sig (D -> D) isContinuous f) x).
Proof with eauto with *.
  induction n as [ | n IH]; intros [f1 x1] [f2 x2] [f1_le_f2 x1_le_x2]; simpl in *; trivial.
  transitivity (proj1_sig f2 (iterS n (proj1_sig f1) x1)).
  - eapply f1_le_f2.
  - eapply ScottContinuousMap_isMonotonic.
    + exact (proj2_sig f2).
    + eapply IH with (x1 := (f1, x1)) (x2 := (f2, x2)). split...
Qed.

Lemma f_mapsto_iterS_n_f_bottom_isMonotonic_for_any_n
  : forall n : nat, isMonotonic1 (fun f : `[D -> D] => iterS n (proj1_sig f) bottom_cpo).
Proof.
  ii. eapply iterS_isMonotonic with (n := n) (x1 := (x1, bottom_cpo)) (x2 := (x2, bottom_cpo)). split; eauto with *.
Qed.

#[local] Hint Resolve iterS_isMonotonic f_mapsto_iterS_n_f_bottom_isMonotonic_for_any_n : core.

Lemma f_mapsto_iterS_n_f_bottom_isContinuous_for_any_n
  : forall n : nat, isContinuous (fun f : `[D -> D] => iterS n (proj1_sig f) bottom_cpo).
Proof with eauto with *.
  induction n as [ | n IH].
  - eapply botOfScottContinuousMaps_isContinuous.
  - eapply the_main_reason_for_introducing_ScottTopology.
    + ii. eapply leProp_antisymmetry; eapply f_mapsto_iterS_n_f_bottom_isMonotonic_for_any_n...
    + intros F F_isDirected.
      set (sup_F := supremum_cpo F F_isDirected).
      assert (sup_F_is_supremum_of_F : is_supremum_of sup_F F) by exact (supremum_cpo_spec F F_isDirected).
      set (Y := E.image (fun f : `[D -> D] => iterS (S n) (proj1_sig f) bottom_cpo) F).
      assert (Y_isDirected : isDirected Y).
      { eapply preservesDirectedness_if_isMonotonic... }
      set (X := E.image (fun f : `[D -> D] => iterS n (proj1_sig f) bottom_cpo) F).
      assert (X_isDirected : isDirected X).
      { eapply preservesDirectedness_if_isMonotonic... }
      set (sup_X := iterS n (proj1_sig sup_F) bottom_cpo).
      assert (sup_X_is_supremum_of_X : is_supremum_of sup_X X).
      { eapply ScottContinuousMap_preserves_supremum with (f := fun f : `[D -> D] => iterS n (proj1_sig f) bottom_cpo)... }
      set (sup_Y := proj1_sig sup_F (iterS n (proj1_sig sup_F) bottom_cpo)).
      assert (claim1 : proj1_sig sup_F sup_X == sup_Y).
      { eapply leProp_antisymmetry... }
      assert (claim2 : iterS n (proj1_sig sup_F) bottom_cpo == sup_X).
      { eapply sup_Y_is_supremum_of_image_f_X_iff_f_sup_X_eq_sup_Y with (f := fun f : `[D -> D] => iterS n (proj1_sig f) bottom_cpo).
        - exact (IH).
        - exact (F_isDirected).
        - exact (sup_F_is_supremum_of_F).
        - exact (sup_X_is_supremum_of_X).
      }
      assert (claim3 : is_supremum_of (proj1_sig sup_F sup_X) (E.unions (E.image (fun f_i : `[D -> D] => E.image (fun x : D => proj1_sig f_i x) X) F))).
      { eapply supOfScottContinuousMaps_F_sup_X_is_supremum_of_unions_i_image_f_i_X_F... }
      exists (sup_F), (sup_Y). split; trivial. split; trivial. ii; split.
      { intros ? y ?. unfold X, Y in *. rewrite E.in_image_iff in IN. destruct IN as [f_i [? H_IN]]; subst y. transitivity (proj1_sig f_i sup_X).
        - simpl. eapply ScottContinuousMap_isMonotonic; [exact (proj2_sig f_i) | eapply sup_X_is_supremum_of_X]... done!.
        - rewrite <- H, <- claim1. eapply sup_F_is_supremum_of_F...
      }
      { ii. rewrite <- claim1. eapply claim3. intros y ?. s!. destruct IN as [Z [Z_in H_IN]]. s!.
        destruct H_IN as [f1 [? H_IN1]]; subst Z. s!. destruct Z_in as [x [? x_in_X]]; subst y. unfold X, Y in *. s!.
        destruct x_in_X as [f2 [? H_IN2]]; subst x. inversion F_isDirected. pose proof (DIRECTED' f1 f2 H_IN1 H_IN2) as [f3 [? [f1_le_f3 f2_le_f3]]].
        transitivity (proj1_sig f3 (iterS n (proj1_sig f3) bottom_cpo)).
        - etransitivity; [eapply f1_le_f3 | eapply ScottContinuousMap_isMonotonic].
          + exact (proj2_sig f3).
          + eapply f_mapsto_iterS_n_f_bottom_isMonotonic_for_any_n...
        - eapply H... econs...
      }
Qed.

Lemma lfp_cpo_isContinuous
  : isContinuous lfp_cpo.
Proof with eauto with *.
  intros O O_isOpen; unnw.
  assert (claim1 : forall n : nat, isOpen (E.preimage (fun f : `[D -> D] => iterS n (proj1_sig f) bottom_cpo) O)).
  { ii. eapply f_mapsto_iterS_n_f_bottom_isContinuous_for_any_n... }
  assert (claim2 : isOpen (E.unions (fun F : ensemble `[D -> D] => exists n : nat, F == E.preimage (fun f : `[D -> D] => iterS n (proj1_sig f) bottom_cpo) O))).
  { eapply unions_in_T. intros F [n H_EQ]. rewrite H_EQ... }
  eapply isOpen_compatWith_eqProp. 2: exact (claim2).
  inversion O_isOpen. intros f. split.
  - intros f_in. rewrite E.in_preimage_iff in f_in. destruct f_in as [y [? H_IN]]; subst y.
    pose proof (LIMIT (IterS (proj1_sig f) bottom_cpo) (lfp_cpo f) (IterS_f_bottom_isDirected_if_f_isMonotonic (proj1_sig f) (ScottContinuousMap_isMonotonic (proj1_sig f) (proj2_sig f))) (supremum_cpo_spec _ _) H_IN) as [x [x_in x_in']].
    inversion x_in; subst. exists (E.preimage (fun f_i : `[D -> D] => iterS n (proj1_sig f_i) bottom_cpo) O)... econstructor... econs...
  - intros f_in. rewrite E.in_unions_iff in f_in. destruct f_in as [F [f_in H_IN]].
    red in H_IN. destruct H_IN as [n H_EQ]. rewrite H_EQ in f_in.
    rewrite E.in_preimage_iff in f_in. destruct f_in as [y [? H_IN]]; subst y.
    rewrite E.in_preimage_iff. exists (lfp_cpo f). split...
    eapply UPWARD_CLOSED... eapply supremum_cpo_spec...
Qed.

Definition ScottFix : `[`[D -> D] -> D] :=
  @exist (`[D -> D] -> D) isContinuous lfp_cpo lfp_cpo_isContinuous.

End SCOTT_FIX.

End CPO_THEORY.
