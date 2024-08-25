Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.subset.
#[local] Obligation Tactic := i.

#[local] Hint Resolve Equivalence_Reflexive Equivalence_Symmetric Equivalence_Transitive : poset_hints.
#[local] Hint Resolve eqProp_refl eqProp_sym eqProp_trans leProp_refl leProp_trans leProp_antisymmetry eqProp_implies_leProp : poset_hints.
#[local] Hint Resolve supremum_monotonic supremum_unique supremum_congruence is_supremum_of_compatWith_eqProp : poset_hints.

#[local] Hint Unfold fixedpointsOf prefixedpointsOf postfixedpointsOf upperboundsOf lowerboundsOf is_supremum_of is_infimum_of : simplication_hints.

Section COLA_THEORY.

Import ColaDef.

#[local] Existing Instance direct_product_of_two_Prosets.
#[local] Existing Instance subProset.
#[local] Existing Instance pi_isProset.

Definition infimum_cola {D : Type} {PROSET : isProset D} {COLA : isCola D} (X : ensemble D) : { inf_X : D | is_infimum_of inf_X X } :=
  let inf_X : D := proj1_sig (supremum_cola (lowerboundsOf X)) in
  @exist D (fun inf_X : D => is_infimum_of inf_X X) inf_X (proj2 (supremum_of_lowerbounds_is_infimum inf_X X) (proj2_sig (supremum_cola (lowerboundsOf X)))).

Definition supremum_of_monotonic_maps {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {COLA : isCola D} {COLA' : isCola D'} (F : ensemble `[D -> D']) :=
  reify (fun x => supremum_cola (E.image (fun f : `[D -> D'] => proj1_sig f x) F)).

Lemma supremum_of_monotonic_maps_isMonotonic {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {COLA : isCola D} {COLA' : isCola D'} (F : ensemble `[D -> D'])
  : isMonotonic1 (proj1_sig (supremum_of_monotonic_maps F)).
Proof.
  ii. property (supremum_of_monotonic_maps F). ii. rewrite E.in_image_iff in IN. destruct IN as [f [-> IN]].
  etransitivity. property f; exact x_LE. property (supremum_of_monotonic_maps F); done!.
Qed.

Definition supOfMonotonicMaps {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {COLA : isCola D} {COLA' : isCola D'} (F : ensemble `[D -> D']) : `[D -> D'] :=
  @exist (D -> D') isMonotonic1 (proj1_sig (supremum_of_monotonic_maps F)) (supremum_of_monotonic_maps_isMonotonic F).

Lemma supOfMonotonicMaps_is_supremum {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {COLA : isCola D} {COLA' : isCola D'}
  : forall F : ensemble `[D -> D'], is_supremum_of (supOfMonotonicMaps F) F.
Proof.
  unfold supOfMonotonicMaps. intros F f. split.
  - intros H_LE f_i f_i_in. rewrite <- H_LE.
    intros x. simpl. property (supremum_of_monotonic_maps F); done!.
  - intros UPPERBOUND x. simpl. property (supremum_of_monotonic_maps F); done!.
Qed.

#[local]
Instance MonotonicMaps_asCola {D : Type} {D' : Type} {PROSET : isProset D} {PROSET' : isProset D'} {COLA : isCola D} {COLA' : isCola D'} : isCola `[D -> D'] :=
  fun F : ensemble `[D -> D'] => @exist `[D -> D'] (fun sup_F => is_supremum_of sup_F F) (supOfMonotonicMaps F) (supOfMonotonicMaps_is_supremum F).

Section KNASTER_TARSKI. (* Reference: "https://www.cs.utexas.edu/users/misra/Notes.dir/KnasterTarski.pdf" written by Jayadev Misra *)

Context {D : Type} {PROSET : isProset D} {COLA : isCola D (PROSET := PROSET)}.

Theorem KnasterTarski_1st (f : D -> D)
  (f_isMonotonic : isMonotonic1 f)
  : { lfp_f : D | is_infimum_of lfp_f (prefixedpointsOf f) /\ is_lfpOf lfp_f f }.
Proof.
  assert (IS_INFIMUM : is_infimum_of (proj1_sig (infimum_cola (prefixedpointsOf f))) (prefixedpointsOf f)).
  { exact (proj2_sig (infimum_cola (prefixedpointsOf f))). }
  exists (proj1_sig (infimum_cola (prefixedpointsOf f))). split.
  - done!.
  - eapply prefixedpoint_is_lfpOf; done!.
Qed.

Theorem KnasterTarski_2nd (f : D -> D)
  (f_isMonotonic : isMonotonic1 f)
  : { gfp_f : D | is_supremum_of gfp_f (postfixedpointsOf f) /\ is_gfpOf gfp_f f }.
Proof.
  assert (IS_SUPREMUM : is_supremum_of (proj1_sig (supremum_cola (postfixedpointsOf f))) (postfixedpointsOf f)).
  { exact (proj2_sig (supremum_cola (postfixedpointsOf f))). }
  exists (proj1_sig (supremum_cola (postfixedpointsOf f))). split.
  - done!.
  - eapply postfixedpoint_is_gfpOf; done!.
Qed.

Theorem KnasterTarski_3rd (f : D -> D) (W : ensemble D)
  (f_isMonotonic : isMonotonic1 f)
  (W_is_a_set_of_fixed_points_of_f : W \subseteq fixedpointsOf f)
  : {fix_f : D | is_supremum_in fix_f W (fixedpointsOf f)}.
Proof with eauto with *.
  pose proof (supremum_cola W) as [q q_is_lub_of_W].
  pose (fun w : D => q =< w) as W_hat.
  assert (q_is_glb_of_W_hat : is_infimum_of q W_hat).
  { unfold W_hat.  done!. }
  assert (q_in_W_hat : q \in W_hat) by exact (leProp_refl q).
  assert (W_hat_closed_under_f : forall x : D, x \in W_hat -> f x \in W_hat).
  { intros x q_le_x. eapply q_is_lub_of_W.
    intros w w_in_W. transitivity (f w).
    - eapply eqProp_implies_leProp, W_is_a_set_of_fixed_points_of_f...
    - eapply f_isMonotonic. transitivity q; trivial. eapply q_is_lub_of_W...
  }
  assert (q_le_f_q : q =< f q) by exact (W_hat_closed_under_f q q_in_W_hat).
  pose proof (infimum_cola (E.intersection (prefixedpointsOf f) W_hat)) as [fix_f fix_f_isInfimum].
  enough (claim1 : f fix_f =< fix_f).
  enough (claim2 : q =< fix_f).
  enough (claim3 : fix_f == f fix_f).
  - exists fix_f. split; unnw; trivial.
    intros [x x_in]. simpl. split.
    { intros fix_f_le_x d d_in. transitivity (q).
      - eapply q_is_lub_of_W...
      - transitivity fix_f...
    }
    { intros x_is_upper_bound_of_W. eapply fix_f_isInfimum... split.
      - eapply eqProp_implies_leProp. now symmetry.
      - eapply q_is_lub_of_W...
    }
  - eapply leProp_antisymmetry; trivial.
    eapply fix_f_isInfimum... done!.
  - eapply fix_f_isInfimum. ii; s!. destruct IN as [f_x_le_x q_le_x]...
  - eapply fix_f_isInfimum. intros x x_in. s!. destruct x_in as [f_x_le_x q_le_x].
    rewrite <- f_x_le_x. eapply f_isMonotonic.
    eapply fix_f_isInfimum... split; eauto.
Qed.

Corollary fixedpointsOf_asCoLa (f : `[ D -> D ])
  : isCola (@sig D (fixedpointsOf (proj1_sig f))) (PROSET := @subProset D PROSET (fixedpointsOf (proj1_sig f))).
Proof.
  intros X.
  assert (claim1 : E.image (@proj1_sig D (fixedpointsOf (proj1_sig f))) X \subseteq fixedpointsOf (proj1_sig f)).
  { intros z z_in. rewrite E.in_image_iff in z_in. destruct z_in as [[x x_eq_f_x] [z_eq x_in]]. now subst z. }
  pose proof (KnasterTarski_3rd (proj1_sig f) (E.image (@proj1_sig D (fixedpointsOf (proj1_sig f))) X) (proj2_sig f) claim1) as [sup_X IS_SUPREMUM].
  exists (@exist D (fixedpointsOf (proj1_sig f)) sup_X (proj1 IS_SUPREMUM)). now rewrite <- is_supremum_in_iff.
Qed.

End KNASTER_TARSKI.

End COLA_THEORY.
