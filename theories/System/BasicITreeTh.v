Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Control.Monad.
Require Import PnV.Control.Category.
Require Import PnV.Data.ITree.
Require Import PnV.Math.DomainTheory.
Require Import PnV.Math.OrderTheory.

Section ITREE_BISIMULATION.

#[local] Notation In := L.In.
#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "\subseteq" := E.isSubsetOf : type_scope.

#[local] Existing Instance ensemble_isUpperSemilattice.

#[local] Hint Resolve bot_lattice_spec : poset_hints.
#[local] Hint Resolve join_lattice_spec : poset_hints.
#[local] Hint Resolve Equivalence_Reflexive Equivalence_Symmetric Equivalence_Transitive : poset_hints.
#[local] Hint Resolve eqProp_refl eqProp_sym eqProp_trans leProp_refl leProp_trans leProp_antisymmetry eqProp_implies_leProp : poset_hints.
#[local] Hint Unfold upperboundsOf : poset_hints.

Context {E : Type -> Type}.

Lemma itree_bind_unfold_observed {R1 : Type} {R2 : Type} (t0 : itree E R1) (k0 : R1 -> itree E R2)
  : observe (itree_bind' k0 t0) = observe (itree_guard k0 (observe t0) (itree_bind' k0)).
Proof.
  exact (@eq_refl _ (observe (itree_guard k0 (observe t0) (fun t : itree E R1 => bind t k0)))).
Defined.

Section SETOID.

Context {R : Type} {SETOID : isSetoid R}.

Variant itreeBisimF {bisim : itree E R -> itree E R -> Prop} : forall lhs : itreeF (itree E R) E R, forall rhs : itreeF (itree E R) E R, Prop :=
  | EqRetF (r1 : R) (r2 : R)
    (REL : r1 == r2)
    : itreeBisimF (RetF r1) (RetF r2)
  | EqTauF (t1 : itree E R) (t2 : itree E R)
    (REL : bisim t1 t2)
    : itreeBisimF (TauF t1) (TauF t2)
  | EqVisF (X : Type) (e : E X) (k1 : X -> itree E R) (k2 : X -> itree E R)
    (REL : forall x : X, bisim (k1 x) (k2 x))
    : itreeBisimF (VisF X e k1) (VisF X e k2).

Definition eqITreeF (BISIM : ensemble (itree E R * itree E R)) : ensemble (itree E R * itree E R) :=
  fun '(lhs, rhs) => itreeBisimF (bisim := curry BISIM) (observe lhs) (observe rhs).

Definition eqITreeF_monotonic (BISIM : ensemble (itree E R * itree E R)) (BISIM' : ensemble (itree E R * itree E R)) (INCL : BISIM \subseteq BISIM') : eqITreeF BISIM \subseteq eqITreeF BISIM' :=
  fun '(lhs, rhs) => fun lhs_REL_rhs : itreeBisimF (observe lhs) (observe rhs) =>
  match lhs_REL_rhs in itreeBisimF lhs rhs return itreeBisimF lhs rhs with
  | EqRetF r1 r2 REL => EqRetF r1 r2 REL
  | EqTauF t1 t2 REL => EqTauF t1 t2 (INCL (t1, t2) REL)
  | EqVisF X e k1 k2 REL => EqVisF X e k1 k2 (fun x : X => INCL (k1 x, k2 x) (REL x))
  end.

#[global]
Instance eqITreeF_isMonotonic1 : isMonotonic1 eqITreeF :=
  eqITreeF_monotonic.

#[local] Hint Resolve eqITreeF_isMonotonic1 : core.

Definition eqITreeF' : ensemble (itree E R * itree E R) -> ensemble (itree E R * itree E R) :=
  paco eqITreeF.

Definition eqITree (lhs : itree E R) (rhs : itree E R) : Prop :=
  (lhs, rhs) \in eqITreeF' bot_lattice.

#[projections(primitive)]
CoInductive itreeBisim (lhs : itree E R) (rhs : itree E R) : Prop :=
  Fold_itreeBisim { unfold_itreeBisim : itreeBisimF (bisim := itreeBisim) (observe lhs) (observe rhs) }.

Theorem eqITree_iff_itreeBisim (lhs : itree E R) (rhs : itree E R)
  : eqITree lhs rhs <-> itreeBisim lhs rhs.
Proof.
  revert lhs rhs. set (itreeBisim' := uncurry itreeBisim). set (f := @exist (ensemble (itree E R * itree E R) -> ensemble (itree E R * itree E R)) isMonotonic1 eqITreeF eqITreeF_isMonotonic1).
  enough (claim1 : itreeBisim' \subseteq proj1_sig f itreeBisim').
  enough (claim2 : is_supremum_of itreeBisim' (postfixedpointsOf (proj1_sig f))).
  enough (claim3 : eqITreeF' ensemble_isUpperSemilattice.(bot_lattice) == itreeBisim').
  - ii. exact (claim3 (lhs, rhs)).
  - eapply @supremum_unique with (PROSET := E.ensemble_isProset) (X1 := postfixedpointsOf (proj1_sig f)) (X2 := postfixedpointsOf (proj1_sig f)).
    + rewrite paco_init with (F_monotonic := eqITreeF_isMonotonic1). eapply nu_is_supremum_of_postfixedpointsOf.
    + exact claim2.
    + reflexivity.
  - intros Y. split.
    + intros le_Y X X_in. unnw. do 2 red in X_in. rewrite <- le_Y. intros [lhs rhs] H_in. revert lhs rhs H_in.
      exact (
        cofix CIH (lhs : itree E R) (rhs : itree E R) (H_in : (lhs, rhs) \in X) : itreeBisim lhs rhs :=
        Fold_itreeBisim lhs rhs (eqITreeF_isMonotonic1 X (uncurry itreeBisim) (fun '(LHS, RHS) => CIH LHS RHS) (lhs, rhs) (X_in (lhs, rhs) H_in))
      ).
    + intros UPPER_BOUND. eapply UPPER_BOUND. exact claim1.
  - intros [lhs rhs] H_in. eapply unfold_itreeBisim. exact H_in.
Qed.

Lemma eqITree_reflexivity
  : B.Rel_id \subseteq eqITreeF' bot_lattice.
Proof with eauto with *.
  eapply paco_accum... set (Rel_focus := join_lattice bot_lattice B.Rel_id).
  rewrite <- paco_fold. intros [lhs rhs] lhs_eq_rhs. repeat red. do 2 red in lhs_eq_rhs.
  destruct (observe lhs) as [r1 | t1 | X1 e1 k1] eqn: H_lhs_obs; destruct (observe rhs) as [r2 | t2 | X2 e2 k2] eqn: H_rhs_obs; try congruence.
  - econstructor 1. replace r2 with r1 by congruence. reflexivity.
  - econstructor 2. left. right. do 2 red. congruence.
  - assert (obs_eq : @eq (itreeF (itree E R) E R) (VisF X1 e1 k1) (VisF X2 e2 k2)) by congruence.
    rewrite obs_eq. econstructor 3. ii. left. right. reflexivity.
Qed.

Lemma eqITree_symmetry
  : B.Rel_flip (eqITreeF' bot_lattice) \subseteq eqITreeF' bot_lattice.
Proof with eauto with *.
  eapply paco_accum... set (Rel_focus := join_lattice bot_lattice (B.Rel_flip (eqITreeF' bot_lattice))).
  rewrite <- paco_fold. intros [lhs rhs] lhs_eq_rhs. apply paco_unfold in lhs_eq_rhs... repeat red in lhs_eq_rhs. repeat red.
  destruct lhs_eq_rhs as [r1 r2 REL | t1 t2 REL | X e k1 k2 REL].
  - econstructor 1. symmetry...
  - econstructor 2. apply E.in_union_iff in REL. destruct REL as [REL | REL]; [inversion REL | left; right]...
  - econstructor 3. intros x. specialize REL with (x := x).
    apply E.in_union_iff in REL. destruct REL as [REL | REL]; [inversion REL | left; right]...
Qed.

Lemma eqITree_transitivity
  : B.Rel_compose (eqITreeF' bot_lattice) (eqITreeF' bot_lattice) \subseteq eqITreeF' bot_lattice.
Proof with eauto with *.
  eapply paco_accum... set (Rel_focus := join_lattice bot_lattice (B.Rel_compose (eqITreeF' bot_lattice) (eqITreeF' bot_lattice))).
  assert (INIT : eqITreeF (join_lattice bot_lattice (eqITreeF' bot_lattice)) =< eqITreeF (join_lattice Rel_focus (eqITreeF' Rel_focus))).
  { eapply eqITreeF_isMonotonic1. intros [lhs rhs] [lhs_eq_rhs | lhs_eq_rhs]; [inversion lhs_eq_rhs | right]. eapply paco_preserves_monotonicity with (x1 := bot_lattice)... eapply bot_lattice_spec. now ii. }
  rewrite <- paco_fold. intros [lhs rhs] [t [lhs_eq_t t_eq_rhs]]. apply paco_unfold in lhs_eq_t... apply paco_unfold in t_eq_rhs... repeat red in lhs_eq_t, t_eq_rhs |- *.
  destruct (observe t) as [r3 | t3 | X3 e3 k3] eqn: H_t_obs.
  - inversion lhs_eq_t; subst. rename REL into REL1, H0 into H_lhs_obs. 
    inversion t_eq_rhs; subst. rename REL into REL2, H into H_rhs_obs.
    econstructor 1. transitivity r3...
  - inversion lhs_eq_t; subst. rename REL into REL1, H0 into H_lhs_obs. 
    inversion t_eq_rhs; subst. rename REL into REL2, H into H_rhs_obs.
    apply E.in_union_iff in REL1, REL2. destruct REL1 as [REL1 | REL1]; [inversion REL1 | ]. destruct REL2 as [REL2 | REL2]; [inversion REL2 | ].
    econstructor 2. left. right. exists t3...
  - rewrite <- H_t_obs in lhs_eq_t, t_eq_rhs. revert H_t_obs. destruct t_eq_rhs as [r2' r2 REL2 | t2' t2 REL | X2 e2 k2' k2 REL2]; try congruence.
    ii. rewrite H_t_obs in lhs_eq_t. destruct lhs_eq_t as [r1 r1' REL1 | t1 t1' REL1 | X1 e1 k1 k1' REL1]; try congruence.
    assert (X2_eq_X1 : X2 = X1).
    { exact (@f_equal _ _ (fun ot : itreeF (itree E R) E R => match ot with VisF X e k => X | _ => X1 end) (VisF X2 e2 k2') (VisF X1 e1 k1') H_t_obs). }
    subst X2. rename X1 into X.
    assert (e1_eq_e2 : e1 = e2).
    { inversion H_t_obs. eapply @ClassicalFacts.projT2_eq with (B := fun X' : Type => E X')... }
    assert (k1_eq_k2 : k1' = k2').
    { inversion H_t_obs. eapply @ClassicalFacts.projT2_eq with (B := fun X' : Type => X' -> itree E R)... }
    subst e2 k2'. rename e1 into e, k1' into k.
    econstructor 3. intros x. specialize REL1 with (x := x). specialize REL2 with (x := x).
    apply E.in_union_iff in REL1, REL2. destruct REL1 as [REL1 | REL1]; [inversion REL1 | ]. destruct REL2 as [REL2 | REL2]; [inversion REL2 | ].
    left. right. exists (k x)...
Qed.

#[global]
Instance eqITree_Reflexive
  : Reflexive eqITree.
Proof.
  intros t1. exact (eqITree_reflexivity (t1, t1) eq_refl).
Qed.

#[global]
Instance eqITree_Symmetric
  : Symmetric eqITree.
Proof.
  intros t1 t2 t1_eq_t2. exact (eqITree_symmetry (t2, t1) t1_eq_t2).
Qed.

#[global]
Instance eqITree_Transitive
  : Transitive eqITree.
Proof.
  intros t1 t2 t3 t1_eq_t2 t2_eq_t3.
  exact (eqITree_transitivity (t1, t3) (@ex_intro _ _ t2 (@conj _ _ t1_eq_t2 t2_eq_t3))).
Qed.

#[global]
Instance eqITree_Equivalence : Equivalence eqITree :=
  { Equivalence_Reflexive := eqITree_Reflexive
  ; Equivalence_Symmetric := eqITree_Symmetric
  ; Equivalence_Transitive := eqITree_Transitive
  }.

#[local]
Instance itree_isSetoid : isSetoid (itree E R) :=
  { eqProp := eqITree
  ; eqProp_Equivalence := eqITree_Equivalence
  }.

Lemma Ret_eq_Ret_iff (x1 : R) (x2 : R)
  : Ret x1 == Ret x2 <-> x1 == x2.
Proof.
  repeat rewrite eqITree_iff_itreeBisim. split; intros H_EQ.
  - apply unfold_itreeBisim in H_EQ. now inversion H_EQ; subst.
  - econstructor. now econstructor 1. 
Qed.

Lemma Tau_eq_Tau_iff (t1 : itree E R) (t2 : itree E R)
  : Tau t1 == Tau t2 <-> t1 == t2.
Proof.
  repeat rewrite eqITree_iff_itreeBisim. split; intros H_EQ.
  - apply unfold_itreeBisim in H_EQ. now inversion H_EQ.
  - econstructor. now econstructor 2. 
Qed.

Lemma Vis_eq_Vis_iff (X : Type) (e : E X) (k1 : X -> itree E R) (k2 : X -> itree E R)
  : Vis X e k1 == Vis X e k2 <-> k1 == k2.
Proof.
  change (eqITree (Vis X e k1) (Vis X e k2) <-> (forall x : X, eqITree (k1 x) (k2 x))). split; intros H_EQ.
  - rewrite eqITree_iff_itreeBisim in H_EQ. apply unfold_itreeBisim in H_EQ.
    inversion H_EQ as [ | | X' e' k1' k2' REL]; subst X'.
    assert (e_eq_e' : e = e').
    { now eapply @ClassicalFacts.projT2_eq with (B := fun X' : Type => E X'). }
    assert (k1_eq_k1' : k1 = k1').
    { now eapply @ClassicalFacts.projT2_eq with (B := fun X' : Type => X' -> itree E R). }
    assert (k2_eq_k2' : k2 = k2').
    { now eapply @ClassicalFacts.projT2_eq with (B := fun X' : Type => X' -> itree E R). }
    subst e' k1' k2'. intros x; rewrite eqITree_iff_itreeBisim; exact (REL x).
  - rewrite eqITree_iff_itreeBisim. econstructor. econstructor 3.
    intros x; rewrite <- eqITree_iff_itreeBisim; exact (H_EQ x).
Qed.

End SETOID.

#[local]
Instance itree_isSetoid1 : isSetoid1 (itree E) :=
  @itree_isSetoid.

Theorem obs_eq_obs_implies_eqITree {R : Type} (lhs : itree E R) (rhs : itree E R)
  (obs_eq_obs : observe lhs = observe rhs)
  : lhs == rhs.
Proof.
  eapply eqITree_iff_itreeBisim; constructor.
  replace (observe rhs) with (observe lhs) by exact (obs_eq_obs).
  eapply eqITree_iff_itreeBisim; reflexivity.
Qed.

Corollary itree_eta {R : Type} (t : itree E R)
  : go (observe t) == t.
Proof.
  now eapply obs_eq_obs_implies_eqITree.
Qed.

Lemma itree_bind_unfold {R1 : Type} {R2 : Type} (t0 : itree E R1) (k0 : R1 -> itree E R2) :
  bind t0 k0 ==
  match observe t0 with
  | RetF r => k0 r
  | TauF t => Tau (bind t k0)
  | VisF X e k => Vis X e (fun x : X => bind (k x) k0)
  end.
Proof.
  now eapply obs_eq_obs_implies_eqITree.
Qed.

Lemma itree_iter_unfold {I : Type} {R : Type} (step : I -> itree E (I + R)) (arg : I) :
  monad_iter step arg ==
  bind (step arg) (fun res : I + R =>
    match res with
    | inl arg' => Tau (monad_iter step arg')
    | inr res' => Ret res'
    end
  ).
Proof.
  now eapply obs_eq_obs_implies_eqITree.
Qed.

Section ITREE_BIND_CASES.

Context {R1 : Type} {R2 : Type} (k0 : R1 -> itree E R2).

Corollary itree_bind_Ret (r : R1)
  : bind (Ret r) k0 == k0 r.
Proof.
  now rewrite itree_bind_unfold.
Qed.

Corollary itree_bind_Tau (t : itree E R1)
  : bind (Tau t) k0 == Tau (bind t k0).
Proof.
  now rewrite itree_bind_unfold.
Qed.

Corollary itree_bind_Vis (X : Type) (e : E X) (k : X -> itree E R1)
  : bind (Vis X e k) k0 == Vis X e (fun x : X => bind (k x) k0).
Proof.
  now rewrite itree_bind_unfold.
Qed.

End ITREE_BIND_CASES.

#[local] Notation eqITreeF1 := (eqITreeF' (SETOID := mkSetoid_from_eq)).

Lemma itree_bind_assoc {R1 : Type} {R2 : Type} {R3 : Type} (t_0 : itree E R1) (k_1 : R1 -> itree E R2) (k_2 : R2 -> itree E R3)
  : (t_0 >>= fun x_1 => k_1 x_1 >>= k_2) == (t_0 >>= k_1 >>= k_2).
Proof with eauto with *.
  symmetry. revert t_0. set (Rel_image := E.image (fun '(lhs, rhs) => (lhs >>= k_1 >>= k_2, rhs >>= fun x_1 => k_1 x_1 >>= k_2))).
  enough (to_show : Rel_image (eqITreeF1 bot_lattice) \subseteq eqITreeF1 bot_lattice).
  { intros t0. eapply to_show. exists (t0, t0)... change (t0 == t0)... }
  eapply paco_accum... set (Rel_focus := join_lattice bot_lattice (Rel_image (eqITreeF1 bot_lattice))).
  assert (INIT : join_lattice bot_lattice (eqITreeF1 bot_lattice) =< join_lattice Rel_focus (eqITreeF1 Rel_focus)).
  { intros z [z_in | z_in]; [inversion z_in | right]. revert z z_in. change (eqITreeF1 bot_lattice =< eqITreeF1 Rel_focus). eapply paco_preserves_monotonicity... eapply bot_lattice_spec. now ii. }
  rewrite <- paco_fold. intros [k0_lhs k0_rhs] k0_lhs_eq_k0_rhs. apply E.in_image_iff in k0_lhs_eq_k0_rhs.
  destruct k0_lhs_eq_k0_rhs as [[lhs rhs] [H_EQ H_IN]].
  pose proof (@f_equal _ _ fst _ _ H_EQ) as k0_lhs_is.
  pose proof (@f_equal _ _ snd _ _ H_EQ) as k0_rhs_is.
  simpl in k0_lhs_is, k0_rhs_is. subst k0_lhs k0_rhs. clear H_EQ.
  apply paco_unfold in H_IN... do 2 red in H_IN |- *.
  repeat rewrite itree_bind_unfold_observed. destruct H_IN as [r1 r2 REL | t1 t2 REL | X e k1 k2 REL]; simpl in REL; simpl.
  - subst r2. rewrite <- itree_bind_unfold_observed. pose proof (eqITree_reflexivity (SETOID := mkSetoid_from_eq) (itree_bind' k_2 (k_1 r1), (itree_bind' k_2 (k_1 r1))) eq_refl) as claim1.
    apply paco_unfold in claim1... pose proof (eqITreeF_isMonotonic1 _ _ INIT _ claim1) as claim2. simpl in claim2. exact claim2.
  - destruct REL as [REL | REL]; [inversion REL | ].
    econstructor 2. left. right. exists (t1, t2)...
  - econstructor 3. intros x. specialize REL with (x := x).
    apply E.in_union_iff in REL. destruct REL as [REL | REL]; [inversion REL | ].
    left. right. exists (k1 x, k2 x)...
Qed.

Lemma itree_pure_left_id_bind {R1 : Type} {R2 : Type} (k : R1 -> itree E R2) (x : R1)
  : (pure x >>= k) == k x.
Proof.
  exact (itree_bind_Ret k x).
Qed.

Lemma itree_pure_right_id_bind {R1 : Type} (t : itree E R1)
  : (t >>= pure) == t.
Proof with eauto with *.
  revert t. set (Rel_image := E.image (B := itree E R1 * itree E R1) (fun '(lhs, rhs) => (lhs >>= pure, rhs))).
  enough (to_show : Rel_image (eqITreeF1 bot_lattice) \subseteq eqITreeF1 bot_lattice).
  { intros t0. eapply to_show. exists (t0, t0)... change (t0 == t0)... }
  eapply paco_accum... set (Rel_focus := join_lattice bot_lattice (Rel_image (eqITreeF1 bot_lattice))).
  assert (INIT : join_lattice bot_lattice (eqITreeF1 bot_lattice) =< join_lattice Rel_focus (eqITreeF1 Rel_focus)).
  { intros z [z_in | z_in]; [inversion z_in | right]. revert z z_in. change (eqITreeF1 bot_lattice =< eqITreeF1 Rel_focus). eapply paco_preserves_monotonicity... eapply bot_lattice_spec. now ii. }
  rewrite <- paco_fold. intros [k0_lhs k0_rhs] k0_lhs_eq_k0_rhs. apply E.in_image_iff in k0_lhs_eq_k0_rhs.
  destruct k0_lhs_eq_k0_rhs as [[lhs rhs] [H_EQ H_IN]].
  pose proof (@f_equal _ _ fst _ _ H_EQ) as k0_lhs_is.
  pose proof (@f_equal _ _ snd _ _ H_EQ) as k0_rhs_is.
  simpl in k0_lhs_is, k0_rhs_is. subst k0_lhs k0_rhs. clear H_EQ.
  apply paco_unfold in H_IN... do 2 red in H_IN |- *.
  repeat rewrite itree_bind_unfold_observed. destruct H_IN as [r1 r2 REL | t1 t2 REL | X e k1 k2 REL]; simpl in REL; simpl.
  - econstructor 1...
  - destruct REL as [REL | REL]; [inversion REL | ].
    econstructor 2. left. right. exists (t1, t2)...
  - econstructor 3. intros x. specialize REL with (x := x).
    apply E.in_union_iff in REL. destruct REL as [REL | REL]; [inversion REL | ].
    left. right. exists (k1 x, k2 x)...
Qed.

Lemma itree_bind_compatWith_eqProp_on_1st_arg {R1 : Type} {R2 : Type} (t_1 : itree E R1) (t_2 : itree E R1) (k_0 : R1 -> itree E R2)
  (HYP_FST_ARG_EQ : t_1 == t_2)
  : (t_1 >>= k_0) == (t_2 >>= k_0).
Proof with eauto with *.
  revert t_1 t_2 HYP_FST_ARG_EQ. rename k_0 into k0. set (Rel_image := E.image (fun '(lhs, rhs) => (lhs >>= k0, rhs >>= k0))).
  enough (to_show : Rel_image (eqITreeF1 bot_lattice) \subseteq eqITreeF1 bot_lattice).
  { ii. eapply to_show. exists (t_1, t_2)... }
  eapply paco_accum... set (Rel_focus := join_lattice bot_lattice (Rel_image (eqITreeF1 bot_lattice))).
  assert (INIT : join_lattice bot_lattice (eqITreeF1 bot_lattice) =< join_lattice Rel_focus (eqITreeF1 Rel_focus)).
  { intros z [z_in | z_in]; [inversion z_in | right]. revert z z_in. change (eqITreeF1 bot_lattice =< eqITreeF1 Rel_focus). eapply paco_preserves_monotonicity... eapply bot_lattice_spec. now ii. }
  rewrite <- paco_fold. intros [k0_lhs k0_rhs] k0_lhs_eq_k0_rhs. apply E.in_image_iff in k0_lhs_eq_k0_rhs.
  destruct k0_lhs_eq_k0_rhs as [[lhs rhs] [H_EQ H_IN]].
  assert (k0_lhs_is : k0_lhs = (lhs >>= k0)) by exact (@f_equal _ _ fst _ _ H_EQ).
  assert (k0_rhs_is : k0_rhs = (rhs >>= k0)) by exact (@f_equal _ _ snd _ _ H_EQ).
  clear H_EQ. subst k0_lhs k0_rhs. apply paco_unfold in H_IN...
  do 2 red in H_IN |- *. simpl (itree_isMonad.(bind)). cbn beta. do 2 rewrite itree_bind_unfold_observed.
  destruct H_IN as [r1 r2 REL | t1 t2 REL | X e k1 k2 REL]; simpl in *.
  - assert (claim1 : (k0 r1, k0 r2) \in B.Rel_id) by congruence.
    pose proof (eqITree_reflexivity (SETOID := mkSetoid_from_eq) (k0 r1, k0 r2) claim1) as claim2.
    apply paco_unfold in claim2... do 2 red in claim2.
    exact (eqITreeF_isMonotonic1 _ _ INIT (k0 r1, k0 r2) claim2).
  - destruct REL as [REL | REL]; [inversion REL | ].
    econstructor 2. left. right... unfold Rel_image. econstructor... reflexivity.
  - econstructor 3. intros x. specialize REL with (x := x).
    destruct REL as [REL | REL]; [inversion REL | ]. left. right. unfold Rel_image. econstructor... reflexivity.
Qed.

Lemma itree_bind_compatWith_eqProp_on_2nd_arg {R1 : Type} {R2 : Type} (t_0 : itree E R1) (k_1 : R1 -> itree E R2) (k_2 : R1 -> itree E R2)
  (HYP_SND_ARG_EQ : forall x : R1, k_1 x == k_2 x)
  : (t_0 >>= k_1) == (t_0 >>= k_2).
Proof with eauto with *.
  set (Rel_image := E.image (B := itree E R2 * itree E R2) (fun '(lhs, rhs) => (lhs >>= k_1, rhs >>= k_2))).
  enough (to_show : Rel_image (eqITreeF1 bot_lattice) \subseteq eqITreeF1 bot_lattice).
  { rename t_0 into t0. eapply to_show. exists (t0, t0)... change (t0 == t0)... }
  eapply paco_accum... set (Rel_focus := join_lattice bot_lattice (Rel_image (eqITreeF1 bot_lattice))).
  assert (INIT : join_lattice bot_lattice (eqITreeF1 bot_lattice) =< join_lattice Rel_focus (eqITreeF1 Rel_focus)).
  { intros z [z_in | z_in]; [inversion z_in | right]. revert z z_in. change (eqITreeF1 bot_lattice =< eqITreeF1 Rel_focus). eapply paco_preserves_monotonicity... eapply bot_lattice_spec. now ii. }
  rewrite <- paco_fold. intros [k0_lhs k0_rhs] k0_lhs_eq_k0_rhs. apply E.in_image_iff in k0_lhs_eq_k0_rhs.
  destruct k0_lhs_eq_k0_rhs as [[lhs rhs] [H_EQ H_IN]].
  pose proof (@f_equal _ _ fst _ _ H_EQ) as k0_lhs_is.
  pose proof (@f_equal _ _ snd _ _ H_EQ) as k0_rhs_is.
  simpl in k0_lhs_is, k0_rhs_is. subst k0_lhs k0_rhs. clear H_EQ.
  apply paco_unfold in H_IN... do 2 red in H_IN |- *.
  repeat rewrite itree_bind_unfold_observed. destruct H_IN as [r1 r2 REL | t1 t2 REL | X e k1 k2 REL]; simpl in REL; simpl.
  - subst r2. rename r1 into x. specialize HYP_SND_ARG_EQ with (x := x).
    apply paco_unfold in HYP_SND_ARG_EQ... exact (eqITreeF_isMonotonic1 _ _ INIT _ HYP_SND_ARG_EQ).
  - apply E.in_union_iff in REL. destruct REL as [REL | REL]; [inversion REL | ].
    econstructor 2. left. right. exists (t1, t2)...
  - econstructor 3. intros x. specialize REL with (x := x).
    destruct REL as [REL | REL]; [inversion REL | ].
    left. right. exists (k1 x, k2 x)...
Qed.

#[local]
Instance itree_MonadLaws : MonadLaws (itree E) :=
  { bind_assoc {R1 : Type} {R2 : Type} {R3 : Type} := itree_bind_assoc (R1 := R1) (R2 := R2) (R3 := R3)
  ; bind_pure_l {R1 : Type} {R2 : Type} := itree_pure_left_id_bind (R1 := R1) (R2 := R2)
  ; bind_pure_r {R1 : Type} := itree_pure_right_id_bind (R1 := R1)
  ; bind_compatWith_eqProp_l {R1 : Type} {R2 : Type} := itree_bind_compatWith_eqProp_on_1st_arg (R1 := R1) (R2 := R2)
  ; bind_compatWith_eqProp_r {R1 : Type} {R2 : Type} := itree_bind_compatWith_eqProp_on_2nd_arg (R1 := R1) (R2 := R2)
  }.

End ITREE_BISIMULATION.
