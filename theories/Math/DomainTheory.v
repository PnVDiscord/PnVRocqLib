Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.
#[local] Obligation Tactic := i.

#[local] Hint Resolve Equivalence_Reflexive Equivalence_Symmetric Equivalence_Transitive : poset_hints.
#[local] Hint Resolve eqProp_refl eqProp_sym eqProp_trans leProp_refl leProp_trans leProp_antisymmetry eqProp_implies_leProp : poset_hints.
#[local] Hint Resolve supremum_monotonic supremum_unique supremum_congruence is_supremum_of_compatWith_eqProp : poset_hints.

#[local] Hint Unfold fixedpointsOf prefixedpointsOf postfixedpointsOf upperboundsOf lowerboundsOf is_supremum_of is_infimum_of : simplication_hints.

Section COLA_THEORY.

Import ListNotations.
Import ColaDef.

#[local] Existing Instance direct_product_of_two_Prosets.
#[local] Existing Instance subProset.
#[local] Existing Instance pi_isProset.

Definition infimum_cola {D : Type} {PROSET : isProset D} {COLA : isCola D} (X : ensemble D) : { inf_X : D | is_infimum_of inf_X X } :=
  let inf_X : D := proj1_sig (supremum_cola (lowerboundsOf X)) in
  @exist D (fun inf_X : D => is_infimum_of inf_X X) inf_X (proj2 (supremum_of_lowerbounds_is_infimum inf_X X) (proj2_sig (supremum_cola (lowerboundsOf X)))).

#[program]
Definition Cola_isLowerSemilattice {D : Type} {PROSET : isProset D} {COLA : isCola D (PROSET := PROSET)} : isLowerSemilattice D (PROSET := PROSET) :=
  {| meet_lattice x y := infimum_cola (E.fromList [x; y]); top_lattice := infimum_cola E.empty; |}.
Next Obligation.
  cbn beta. destruct (infimum_cola (E.fromList [x1; x2])) as [meet meet_spec]; simpl. s!. rewrite meet_spec. split.
  - i; split; done!.
  - now i; des; subst.
Qed.
Next Obligation.
  destruct (infimum_cola E.empty) as [top top_spec]; simpl. done!.
Qed.

Definition Cola_isLattice {D : Type} {PROSET : isProset D} (COLA : isCola D (PROSET := PROSET)) : isLattice D (PROSET := PROSET) :=
  {| Lattice_asUpperSemilattice := Cola_isUpperSemilattice; Lattice_asLowerSemilattice := Cola_isLowerSemilattice; |}.

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
  : { fix_f : D | is_supremum_in fix_f W (fixedpointsOf f) }.
Proof with eauto with *.
  pose proof (supremum_cola W) as [q q_is_lub_of_W].
  pose (fun w : D => q =< w) as W_hat.
  assert (q_is_glb_of_W_hat : is_infimum_of q W_hat).
  { unfold W_hat. done!. }
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
  - exists fix_f. split; trivial.
    intros [x x_in]. simpl. split.
    + intros fix_f_le_x d d_in. transitivity q.
      * eapply q_is_lub_of_W...
      * transitivity fix_f...
    + intros x_is_upper_bound_of_W. eapply fix_f_isInfimum... split.
      * eapply eqProp_implies_leProp. now symmetry.
      * eapply q_is_lub_of_W...
  - eapply leProp_antisymmetry; trivial.
    eapply fix_f_isInfimum... done!.
  - eapply fix_f_isInfimum. ii; s!. destruct IN as [f_x_le_x q_le_x]...
  - eapply fix_f_isInfimum. intros x x_in. s!. destruct x_in as [f_x_le_x q_le_x].
    rewrite <- f_x_le_x. eapply f_isMonotonic.
    eapply fix_f_isInfimum... split; eauto.
Qed.

Corollary fixedpointsOf_asCoLa (f : `[D -> D])
  : isCola (@sig D (fixedpointsOf (proj1_sig f))) (PROSET := @subProset D PROSET (fixedpointsOf (proj1_sig f))).
Proof.
  intros X.
  assert (claim1 : E.image (@proj1_sig D (fixedpointsOf (proj1_sig f))) X \subseteq fixedpointsOf (proj1_sig f)).
  { intros z z_in. rewrite E.in_image_iff in z_in. destruct z_in as [[x x_eq_f_x] [z_eq x_in]]. now subst z. }
  pose proof (KnasterTarski_3rd (proj1_sig f) (E.image (@proj1_sig D (fixedpointsOf (proj1_sig f))) X) (proj2_sig f) claim1) as [sup_X IS_SUPREMUM].
  exists (@exist D (fixedpointsOf (proj1_sig f)) sup_X (proj1 IS_SUPREMUM)). now rewrite <- is_supremum_in_iff.
Qed.

End KNASTER_TARSKI.

Section NU.

Context {D : Type} {PROSET : isProset D} {COLA : isCola D (PROSET := PROSET)}.

Definition nu (f : `[D -> D]) : { gfp_f : D | is_gfpOf gfp_f (proj1_sig f) } :=
  let nu_f_proj1_sig : D := proj1_sig (supremum_cola (postfixedpointsOf (proj1_sig f))) in
  let IS_SUPREMUM : is_supremum_of nu_f_proj1_sig (postfixedpointsOf (proj1_sig f)) := proj2_sig (supremum_cola (postfixedpointsOf (proj1_sig f))) in
  @exist D (fun gfp_f : D => is_gfpOf gfp_f (proj1_sig f)) nu_f_proj1_sig (postfixedpoint_is_gfpOf (proj1_sig f) nu_f_proj1_sig (proj2_sig f) IS_SUPREMUM).

Corollary nu_is_supremum_of_postfixedpointsOf (f : `[D -> D])
  : is_supremum_of (proj1_sig (nu f)) (postfixedpointsOf (proj1_sig f)).
Proof.
  exact (proj2_sig (supremum_cola (postfixedpointsOf (proj1_sig f)))).
Qed.

Corollary nu_f_is_gfpOf_f (f : `[D -> D])
  : is_gfpOf (proj1_sig (nu f)) (proj1_sig f).
Proof.
  eapply postfixedpoint_is_gfpOf; [exact (proj2_sig f) | exact (nu_is_supremum_of_postfixedpointsOf f)].
Qed.

Lemma coinduction_principle (b : `[D -> D])
  : forall x, x =< proj1_sig (nu b) <-> (exists y : D, x =< y /\ y =< proj1_sig b y).
Proof.
  pose proof (nu_f_is_gfpOf_f b) as [claim1 claim2].
  pose proof (nu_is_supremum_of_postfixedpointsOf b) as claim3.
  ii; split.
  - ii; exists (proj1_sig (nu b)). split; trivial.
    eapply eqProp_implies_leProp, claim1.
  - intros [y [x_le_y y_le_b_y]]. rewrite x_le_y.
    eapply claim3; eauto with *.
Qed.

Lemma postfixedpoint_le_gfpOf (f : `[D -> D]) (x : D)
  (POSTFIXEDPOINT : x =< proj1_sig f x)
  : x =< proj1_sig (nu f).
Proof.
  eapply nu_is_supremum_of_postfixedpointsOf; eauto with *.
Qed.

End NU.

Section PACO_METATHEORY.

Context {D : Type} {PROSET : isProset D}.

#[local] Hint Resolve le_join_lattice_introl le_join_lattice_intror join_lattice_le_intro bot_lattice_le_intro : core.

Lemma strong_coinduction {COLA : isCola D} {UPPER_LATTICE : isUpperSemilattice D} (f : `[D -> D]) (x : D)
  : x =< proj1_sig (nu f) <-> x =< proj1_sig f (join_lattice x (proj1_sig (nu f))).
Proof with eauto with *.
  assert (claim1 : proj1_sig f (proj1_sig (nu f)) =< proj1_sig f (join_lattice x (proj1_sig (nu f)))).
  { eapply (proj2_sig f). eapply join_lattice_spec; done!. }
  pose proof (proj2_sig (nu f)) as [claim2 claim3]. split.
  - intros x_le. rewrite x_le at 1. transitivity (proj1_sig f (proj1_sig (nu f)))...
  - intros x_le. unnw. exploit (join_lattice_le_intro x (proj1_sig (nu f)) _ x_le).
    + do 2 red in claim2. rewrite claim2 at 1. eapply (proj2_sig f). eapply le_join_lattice_intror...
    + intros H. rewrite x_le. eapply postfixedpoint_le_gfpOf. eapply (proj2_sig f)...
Qed.

Definition G_aux0 {UPPER_LATTICE : isUpperSemilattice D} (f : `[D -> D]) (x : D) : D -> D :=
  fun y : D => proj1_sig f (join_lattice x y).

Lemma G_aux0_isMonotionicMap {UPPER_LATTICE : isUpperSemilattice D} (f : `[D -> D]) (x : D)
  : isMonotonic1 (G_aux0 f x).
Proof.
  intros x1 x2 x1_le_x2. eapply (proj2_sig f).
  eapply join_lattice_le_intro; [eapply le_join_lattice_introl | rewrite x1_le_x2; eapply le_join_lattice_intror]; eauto with *.
Qed.

Definition G_aux {UPPER_LATTICE : isUpperSemilattice D} (f : `[D -> D]) (x : D) : `[D -> D] :=
  @exist (D -> D) isMonotonic1 (G_aux0 f x) (G_aux0_isMonotionicMap f x).

Context {COLA : isCola D} {UPPER_LATTICE : isUpperSemilattice D}.

Definition G0 (f : `[D -> D]) (x : D) : D :=
  proj1_sig (nu (G_aux f x)).

Lemma G0_isMonotonic1 (f : `[D -> D])
  : isMonotonic1 (G0 f).
Proof with eauto with *.
  intros x1 x2 x1_le_x2. eapply strong_coinduction. simpl in *.
  assert (claim1 : G0 f x1 == proj1_sig f (join_lattice x1 (G0 f x1))) by eapply (proj2_sig (nu (G_aux f x1))).
  rewrite claim1 at 1. eapply (proj2_sig f). transitivity (join_lattice x2 (G0 f x1)).
  - eapply join_lattice_le_intro.
    + rewrite x1_le_x2 at 1. eapply le_join_lattice_introl...
    + eapply le_join_lattice_intror...
  - eapply join_lattice_le_intro...
Qed.

Definition G1 (f : `[D -> D]) : `[D -> D] :=
  @exist (D -> D) isMonotonic1 (G0 f) (G0_isMonotonic1 f).

Lemma G1_isMonotonic1
  : isMonotonic1 G1.
Proof.
  intros f1 f2 f1_le_f2 x0. simpl. unfold G0.
  pose proof (nu_is_supremum_of_postfixedpointsOf (G_aux f1 x0)) as claim1.
  pose proof (nu_is_supremum_of_postfixedpointsOf (G_aux f2 x0)) as claim2.
  eapply claim1. ii. do 2 red in IN. eapply claim2; eauto with *.
  do 3 red. revert IN. unfold G_aux, G_aux0. simpl. intros x_le.
  rewrite x_le at 1. eapply f1_le_f2.
Qed.

Definition G : `[`[D -> D] -> `[D -> D]] :=
  @exist (`[D -> D] -> `[D -> D]) isMonotonic1 G1 G1_isMonotonic1.

Variant paco_spec (f : `[D -> D]) (G_f : `[D -> D]) : Prop :=
  | paco_spec_intro
    (INIT_COFIXPOINT : proj1_sig (nu f) == proj1_sig G_f bot_lattice)
    (UNFOLD_COFIXPOINT : forall x : D, proj1_sig G_f x == proj1_sig f (join_lattice x (proj1_sig G_f x)))
    (ACCUM_COFIXPOINT : forall x : D, forall y : D, y =< proj1_sig G_f x <-> y =< proj1_sig G_f (join_lattice x y))
    : paco_spec f G_f.

Theorem G_specification (f : `[D -> D])
  : paco_spec f (proj1_sig G f).
Proof with eauto with *.
  pose proof (nu_is_supremum_of_postfixedpointsOf (G_aux f bot_lattice)) as claim1.
  pose proof (nu_is_supremum_of_postfixedpointsOf f) as claim2.
  pose proof (fun x : D => proj1 (nu_f_is_gfpOf_f (G_aux f x))) as claim3.
  split.
  - eapply leProp_antisymmetry.
    + eapply claim2. ii. eapply claim1... s!. rewrite IN at 1. eapply (proj2_sig f)...
    + eapply claim1. ii. eapply claim2... s!. rewrite IN at 1. eapply (proj2_sig f)...
  - exact (claim3).
  - ii; split; intros y_le.
    + rewrite y_le at 1. eapply G0_isMonotonic1...
    + rewrite y_le at 1. eapply postfixedpoint_le_gfpOf.
      transitivity (proj1_sig f (join_lattice (join_lattice x y) (proj1_sig (proj1_sig G f) (join_lattice x y)))).
      { eapply eqProp_implies_leProp. exact (claim3 (join_lattice x y)). }
      { eapply (proj2_sig f). eapply join_lattice_le_intro... }
Qed.

Theorem G_compositionality (f : `[D -> D]) (r : D) (r1 : D) (r2 : D) (g1 : D) (g2 : D)
  (g1_le_G_f_r1 : g1 =< proj1_sig (proj1_sig G f) r1)
  (g2_le_G_f_r2 : g2 =< proj1_sig (proj1_sig G f) r2)
  (r1_le : r1 =< join_lattice r g2)
  (r2_le : r2 =< join_lattice r g1)
  : join_lattice g1 g2 =< proj1_sig (proj1_sig G f) r.
Proof with eauto with *.
  assert (claim1 : g1 =< proj1_sig (proj1_sig G f) (join_lattice r (join_lattice g1 g2))).
  { rewrite g1_le_G_f_r1 at 1. eapply G0_isMonotonic1. rewrite r1_le. eapply join_lattice_le_intro... }
  assert (claim2 : g2 =< proj1_sig (proj1_sig G f) (join_lattice r (join_lattice g1 g2))).
  { rewrite g2_le_G_f_r2 at 1. eapply G0_isMonotonic1. rewrite r2_le. eapply join_lattice_le_intro... }
  pose proof (G_specification f) as [? ? ?]. eapply ACCUM_COFIXPOINT...
Qed.

Theorem G_characterization (f : `[D -> D]) (G_f : `[D -> D])
  (G_f_spec : paco_spec f G_f)
  : G_f == proj1_sig G f.
Proof with eauto with *.
  destruct G_f_spec as [INIT_COFIXPOINT' UNFOLD_COFIXPOINT' ACCUM_COFIXPOINT'].
  assert (claim1 : forall x : D, proj1_sig G_f x =< proj1_sig (proj1_sig G f) x).
  { ii. eapply postfixedpoint_le_gfpOf... }
  pose proof (G_specification f) as [? ? ?].
  assert (claim2 : forall x : D, proj1_sig (proj1_sig G f) x =< proj1_sig G_f (join_lattice x (proj1_sig (proj1_sig G f) x))).
  { ii. rewrite UNFOLD_COFIXPOINT with (x := x) at 1. rewrite UNFOLD_COFIXPOINT'. eapply (proj2_sig f). eapply join_lattice_le_intro... }
  ii. eapply leProp_antisymmetry.
  - eapply claim1.
  - eapply ACCUM_COFIXPOINT'...
Qed.

End PACO_METATHEORY.

Section PACO.

#[local] Hint Resolve le_join_lattice_introl le_join_lattice_intror join_lattice_le_intro bot_lattice_le_intro : core.

Context {A : Type}.

Lemma union_join_lattice_spec (X1 : ensemble A) (X2 : ensemble A)
  : is_supremum_of (@E.union A X1 X2) (E.fromList [X1; X2]).
Proof.
  ii; split.
  - intros H_SUBSET X X_in. s!. destruct X_in as [<- | [<- | []]].
    + intros x x_in; eapply H_SUBSET. left; trivial.
    + intros x x_in; eapply H_SUBSET. right; trivial.
  - intros H_IN x x_in. rewrite E.in_union_iff in x_in. destruct x_in as [x_in | x_in].
    + eapply H_IN with (x := X1); trivial. done!.
    + eapply H_IN with (x := X2); trivial. done!.
Qed.

Lemma empty_bot_lattice_spec
  : is_supremum_of (@E.empty A) E.empty.
Proof.
  ii; split.
  - intros H_SUBSET X X_in. inversion X_in.
  - intros H_IN x x_in. inversion x_in.
Qed.

Let D : Type := ensemble A.

#[local]
Instance ensemble_isUpperSemilattice : isUpperSemilattice D :=
  { join_lattice := @E.union A
  ; bot_lattice := @E.empty A
  ; join_lattice_spec := union_join_lattice_spec
  ; bot_lattice_spec := empty_bot_lattice_spec
  }.

Variant paco' {paco_F : D -> D} (F : D -> D) (X : D) : D :=
  | mk_paco' (WITNESS : D)
    (INCL : WITNESS \subseteq join_lattice X (paco_F X))
    : F WITNESS \subseteq paco' F X.

Lemma inv_paco' {paco_F : D -> D} {F : D -> D} {Y : D} {z : A}
  (H_paco' : z \in paco' (paco_F := paco_F) F Y)
  : exists X, X \subseteq join_lattice Y (paco_F Y) /\ z \in F X.
Proof.
  inversion H_paco'; subst. now exists WITNESS.
Qed.

Lemma unions_is_supremum (Xs : ensemble D)
  : is_supremum_of (E.unions Xs) Xs.
Proof.
  intros X; unnw; split.
  - intros unions_Xs_le_X Z Z_in x x_in. eapply unions_Xs_le_X. now exists Z.
  - intros X_is_upper_bound_of_Xs x x_in. s!. destruct x_in as [Z [x_in IN]].
    revert x x_in. change (Z =< X). eapply X_is_upper_bound_of_Xs. exact IN.
Qed.

#[global]
Instance ensemble_isCoLa : isCola D :=
  fun Xs : ensemble D => @exist D (fun sup_Xs : D => is_supremum_of sup_Xs Xs) (E.unions Xs) (unions_is_supremum Xs).

#[projections(primitive)]
CoInductive paco (F : D -> D) (X : D) (z : A) : Prop :=
  Fold_paco { unfold_paco : z \in paco' (paco_F := paco F) F X }.

Theorem paco_fold (F : D -> D) (Y : D)
  : F (join_lattice Y (paco F Y)) \subseteq paco F Y.
Proof.
  intros z z_in. econstructor. revert z z_in. eapply mk_paco'.
  now change (join_lattice Y (paco F Y) =< join_lattice Y (paco F Y)).
Qed.

Theorem paco_unfold (F : D -> D) (Y : D)
  (F_monotonic : isMonotonic1 F)
  : paco F Y \subseteq F (join_lattice Y (paco F Y)).
Proof.
  intros z z_in. apply unfold_paco in z_in. apply inv_paco' in z_in. s!. destruct z_in as [X [SUBSET IN]].
  revert z IN. change (F X =< F (join_lattice Y (paco F Y))). now eapply F_monotonic.
Qed.

Lemma paco_preserves_monotonicity (F : D -> D)
  (F_monotonic : isMonotonic1 F)
  : isMonotonic1 (paco F).
Proof.
  intros X1 X2 X1_le_X2. pose proof (paco_unfold F X1 F_monotonic) as claim1.
  cofix CIH. intros z z_in. econstructor. apply claim1 in z_in. revert z z_in. eapply mk_paco'.
  intros z [z_in_X1 | z_in_paco_f_X1]; [left; eapply X1_le_X2 | right; eapply CIH]; assumption.
Qed.

Definition Paco (f : `[D -> D]) : `[D -> D] :=
  @exist (D -> D) isMonotonic1 (paco (proj1_sig f)) (paco_preserves_monotonicity (proj1_sig f) (proj2_sig f)).

Lemma initPaco (f : `[D -> D])
  : proj1_sig (nu f) == proj1_sig (Paco f) bot_lattice.
Proof with eauto with *.
  pose (proj1_sig f) as F.
  assert (claim1 : F (join_lattice bot_lattice (paco F bot_lattice)) =< paco F bot_lattice) by exact (paco_fold F bot_lattice).
  assert (claim2 : paco F bot_lattice =< F (join_lattice bot_lattice (paco F bot_lattice))) by exact (paco_unfold F bot_lattice (proj2_sig f)).
  assert (FIXEDPOINT : paco F bot_lattice == F (paco F bot_lattice)).
  { eapply @leProp_antisymmetry with (A_isProset := E.ensemble_isProset).
    - rewrite claim2 at 1. eapply (proj2_sig f). eapply join_lattice_le_intro...
    - rewrite <- claim1 at 2. eapply (proj2_sig f). eapply le_join_lattice_intror...
  }
  assert (IS_SUPREMUM : is_supremum_of (proj1_sig (nu f)) (postfixedpointsOf F)) by eapply nu_is_supremum_of_postfixedpointsOf.
  pose proof (nu_f_is_gfpOf_f f) as [claim3 claim4]; unnw.
  do 2 red in claim3. fold F in claim3.
  assert (to_show : F (proj1_sig (nu f)) =< paco F bot_lattice).
  { cofix CIH. intros z z_in. econstructor. revert z z_in. apply mk_paco'.
    intros z z_in. right. eapply CIH. rewrite <- claim3. exact (z_in).
  }
  rewrite <- claim3 in to_show. eapply @leProp_antisymmetry with (A_isProset := E.ensemble_isProset)...
Qed.

Theorem paco_init (F : D -> D)
  (F_monotonic : isMonotonic1 F)
  : paco F bot_lattice == proj1_sig (nu (@exist (D -> D) isMonotonic1 F F_monotonic)).
Proof.
  symmetry. eapply initPaco with (f := @exist (D -> D) isMonotonic1 F F_monotonic).
Qed.

Lemma unfoldPaco (f : `[D -> D])
  : forall X : D, proj1_sig (Paco f) X == proj1_sig f (join_lattice X (proj1_sig (Paco f) X)).
Proof.
  intros X. eapply @leProp_antisymmetry with (A_isProset := E.ensemble_isProset).
  - eapply paco_unfold. exact (proj2_sig f).
  - eapply paco_fold.
Qed.

Lemma accumPaco (f : `[D -> D])
  : forall X : D, forall Y : D, Y =< proj1_sig (Paco f) X <-> Y =< proj1_sig (Paco f) (join_lattice X Y).
Proof with eauto with *.
  intros X Y. pose (proj1_sig f) as F. split.
  - intros Y_le_paco_f_X z z_in. apply Y_le_paco_f_X in z_in.
    revert z z_in. change (proj1_sig (Paco f) X =< proj1_sig (Paco f) (join_lattice X Y)).
    eapply paco_preserves_monotonicity; [exact (proj2_sig f) | eapply le_join_lattice_introl]...
  - intros COIND. rewrite COIND at 1. change (paco F (join_lattice X Y) =< paco F X). pose (G_aux0 f X) as F'.
    assert (claim1 : paco F (join_lattice X Y) =< F (join_lattice (join_lattice X Y) (paco F (join_lattice X Y)))).
    { exact (paco_unfold (proj1_sig f) (join_lattice X Y) (proj2_sig f)). }
    assert (claim2 : F (join_lattice (join_lattice X Y) (paco F (join_lattice X Y))) =< F (join_lattice X (paco F (join_lattice X Y)))).
    { eapply (proj2_sig f). eapply join_lattice_le_intro.
      - intros z [z_in_X | z_in_Y]; [left | right]...
      - eapply le_join_lattice_intror...
    }
    assert (claim3 : paco F (join_lattice X Y) \in postfixedpointsOf F').
    { intros z z_in. eapply (proj2_sig f); [reflexivity | eapply claim2]... }
    assert (claim4 : isMonotonic1 F').
    { eapply G_aux0_isMonotionicMap. }
    set (G_f_X := proj1_sig (nu (@exist (D -> D) isMonotonic1 F' claim4))).
    assert (claim5 : paco F (join_lattice X Y) =< F' (paco F (join_lattice X Y))).
    { intros z z_in. eapply (proj2_sig f); [reflexivity | eapply claim2]... }
    assert (claim6 : paco F (join_lattice X Y) =< G_f_X).
    { eapply postfixedpoint_le_gfpOf... }
    assert (claim7 : is_supremum_of G_f_X (postfixedpointsOf F')).
    { eapply nu_is_supremum_of_postfixedpointsOf. }
    pose proof (postfixedpoint_is_gfpOf (PROSET := E.ensemble_isProset) F' G_f_X claim4 claim7) as [? ?]; s!.
    assert (claim8 : G_f_X =< F (join_lattice X G_f_X)).
    { eapply eqProp_implies_leProp... }
    assert (claim9 : F (join_lattice X G_f_X) =< paco F X).
    { simpl. cofix CIH. intros z z_in. econstructor. revert z z_in. eapply mk_paco'.
      intros z z_in. destruct z_in as [? | ?]; simpl.
      - left. exact H_inl.
      - right. eapply CIH. exact (claim8 z H_inr).
    }
    change (paco F (E.union X Y) =< paco F X). now rewrite <- claim9, claim6.
Qed.

Theorem paco_accum (F : D -> D) (X : D) (Y : D)
  (F_monotonic : isMonotonic1 F)
  : Y =< paco F X <-> Y =< paco F (join_lattice X Y).
Proof.
  eapply accumPaco with (f := @exist (D -> D) isMonotonic1 F F_monotonic).
Qed.

Corollary Paco_spec (f : `[D -> D])
  : paco_spec f (Paco f).
Proof.
  split; [exact (initPaco f) | exact (unfoldPaco f) | exact (accumPaco f)].
Qed.

Corollary Paco_eq_G (f : `[D -> D])
  : Paco f == proj1_sig G f.
Proof.
  eapply @G_characterization with (PROSET := E.ensemble_isProset); exact (Paco_spec f).
Qed.

Corollary paco_eq_G (F : D -> D)
  (F_monotonic : isMonotonic1 F)
  : forall X : D, paco F X == proj1_sig (proj1_sig G (@exist (D -> D) isMonotonic1 F F_monotonic)) X.
Proof.
  eapply Paco_eq_G with (f := @exist (D -> D) isMonotonic1 F F_monotonic).
Qed.

Corollary Paco_isMonotonic1
  : isMonotonic1 Paco.
Proof.
  intros f1 f2 f1_le_f2. do 2 rewrite Paco_eq_G. now eapply G1_isMonotonic1.
Qed.

Corollary paco_compositionality (F : D -> D) (r : D) (r1 : D) (r2 : D) (g1 : D) (g2 : D)
  (F_monotonic : isMonotonic1 F)
  (g1_le_G_f_r1 : g1 =< paco F r1)
  (g2_le_G_f_r2 : g2 =< paco F r2)
  (r1_le : r1 =< join_lattice r g2)
  (r2_le : r2 =< join_lattice r g1)
  : join_lattice g1 g2 =< paco F r.
Proof with eauto.
  rewrite paco_eq_G with (F := F) (F_monotonic := F_monotonic).
  eapply G_compositionality... all: rewrite <- paco_eq_G...
Qed.

End PACO.

End COLA_THEORY.
