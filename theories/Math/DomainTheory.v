Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.subset.
#[local] Obligation Tactic := i.

#[local] Hint Resolve Equivalence_Reflexive Equivalence_Symmetric Equivalence_Transitive : poset_hints.
#[local] Hint Resolve eqProp_refl eqProp_sym eqProp_trans leProp_refl leProp_trans leProp_antisymmetry eqProp_implies_leProp : poset_hints.
#[global] Hint Resolve supremum_monotonic supremum_unique supremum_congruence is_supremum_of_compatWith_eqProp : poset_hints.

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

End COLA_THEORY.
