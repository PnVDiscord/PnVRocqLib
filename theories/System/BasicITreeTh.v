Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Control.Monad.
Require Import PnV.Control.Category.
Require Import PnV.Data.ITree.
Require Import PnV.Math.DomainTheory.
Require Import PnV.Math.OrderTheory.

Lemma VisF_eq_VisF_elim {E : Type -> Type} {R : Type} (X1 : Type) (X2 : Type) (e1 : E X1) (e2 : E X2) (k1 : X1 -> itree E R) (k2 : X2 -> itree E R)
  (VisF_eq_VisF : @VisF (itree E R) E R X1 e1 k1 = @VisF (itree E R) E R X2 e2 k2)
  : { X_EQ : X1 = X2 | @eq_rect Type X1 (fun X => E X * (X -> itree E R))%type (e1, k1) X2 X_EQ = (e2, k2) }.
Proof.
  set (view := fun default : { X : Type & (E X * (X -> itree E R))%type } => fun ot : @itreeF (itree E R) E R =>
    match ot return { X : Type & (E X * (X -> itree E R))%type } with
    | RetF _ => default
    | TauF _ => default
    | VisF X e k => @existT Type (fun X : Type => (E X * (X -> itree E R)))%type X (e, k)
    end
  ).
  pose proof (f_equal (view (@existT Type (fun X : Type => (E X * (X -> itree E R)))%type X1 (e1, k1))) VisF_eq_VisF) as H.
  exact (FUN_FACTS.existT_eq_existT_elim (B := fun X : Type => (E X * (X -> itree E R))%type) X1 X2 (e1, k1) (e2, k2) H).
Qed.

#[local] Notation "x ≠ y" := (~ eq x y) : type_scope.

Module ItreeBisimulation.

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
  : (itree_bind' k0 t0).(observe) = (itree_guard k0 t0.(observe) (itree_bind' k0)).(observe).
Proof.
  reflexivity.
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
  fun '(lhs, rhs) => itreeBisimF (bisim := curry BISIM) lhs.(observe) rhs.(observe).

Definition eqITreeF_monotonic (BISIM : ensemble (itree E R * itree E R)) (BISIM' : ensemble (itree E R * itree E R)) (INCL : BISIM \subseteq BISIM') : eqITreeF BISIM \subseteq eqITreeF BISIM' :=
  fun '(lhs, rhs) => fun lhs_REL_rhs : itreeBisimF lhs.(observe) rhs.(observe) =>
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
  Fold_itreeBisim { unfold_itreeBisim : itreeBisimF (bisim := itreeBisim) lhs.(observe) rhs.(observe) }.

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
  destruct lhs.(observe) as [r1 | t1 | X1 e1 k1] eqn: H_lhs_obs; destruct rhs.(observe) as [r2 | t2 | X2 e2 k2] eqn: H_rhs_obs; try congruence.
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
  destruct t.(observe) as [r3 | t3 | X3 e3 k3] eqn: H_t_obs.
  - inversion lhs_eq_t; subst. rename REL into REL1, H0 into H_lhs_obs. 
    inversion t_eq_rhs; subst. rename REL into REL2, H into H_rhs_obs.
    econstructor 1. transitivity r3...
  - inversion lhs_eq_t; subst. rename REL into REL1, H0 into H_lhs_obs. 
    inversion t_eq_rhs; subst. rename REL into REL2, H into H_rhs_obs.
    apply E.in_union_iff in REL1, REL2. destruct REL1 as [REL1 | REL1]; [inversion REL1 | ]. destruct REL2 as [REL2 | REL2]; [inversion REL2 | ].
    econstructor 2. left. right. exists t3...
  - rewrite <- H_t_obs in lhs_eq_t, t_eq_rhs. revert H_t_obs. destruct t_eq_rhs as [r2' r2 REL2 | t2' t2 REL | X2 e2 k2' k2 REL2]; try congruence.
    ii. rewrite H_t_obs in lhs_eq_t. destruct lhs_eq_t as [r1 r1' REL1 | t1 t1' REL1 | X1 e1 k1 k1' REL1]; try congruence. 
    apply VisF_eq_VisF_elim in H_t_obs. destruct H_t_obs as [<- H_EQ]. simpl in H_EQ. inv H_EQ. rename e1 into e, k1' into k.
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

Definition eqITree_code (lhs : itree E R) (rhs : itree E R) : Prop :=
  match lhs.(observe), rhs.(observe) with
  | RetF r1, RetF r2 => r1 == r2
  | TauF t1, TauF t2 => t1 == t2
  | VisF X1 e1 k1, VisF X2 e2 k2 => { X_EQ : X1 = X2 | @eq_rect Type X1 (fun X : Type => E X) e1 X2 X_EQ = e2 /\ @eq_rect Type X1 (fun X : Type => X -> itree E R) k1 X2 X_EQ == k2 }
  | _, _ => False
  end.

Theorem eqITree_code_iff (lhs : itree E R) (rhs : itree E R)
  : eqITree_code lhs rhs <-> lhs == rhs.
Proof.
  split; intros H_EQ.
  - rewrite -> eqITree_iff_itreeBisim. unfold eqITree_code in H_EQ. econstructor. destruct lhs.(observe), rhs.(observe); simpl; try tauto.
    + econstructor; eauto.
    + econstructor; rewrite <- eqITree_iff_itreeBisim; eauto.
    + destruct H_EQ as [<- [? ?]]. simpl in *. subst. econstructor. i. rewrite <- eqITree_iff_itreeBisim; eauto.
  - rewrite -> eqITree_iff_itreeBisim in H_EQ. inv H_EQ. unfold eqITree_code. destruct unfold_itreeBisim0.
    + eauto.
    + rewrite -> eqITree_iff_itreeBisim; eauto.
    + exists eq_refl. simpl; split; eauto. i. rewrite -> eqITree_iff_itreeBisim; eauto.
Qed.

End SETOID.

#[local]
Instance itree_isSetoid1 : isSetoid1 (itree E) :=
  @itree_isSetoid.

Theorem obs_eq_obs_implies_eqITree {R : Type} (lhs : itree E R) (rhs : itree E R)
  (obs_eq_obs : lhs.(observe) = rhs.(observe))
  : lhs == rhs.
Proof.
  eapply eqITree_iff_itreeBisim; constructor.
  replace rhs.(observe) with lhs.(observe) by exact (obs_eq_obs).
  eapply eqITree_iff_itreeBisim; reflexivity.
Qed.

Corollary itree_eta {R : Type} (t : itree E R)
  : go t.(observe) == t.
Proof.
  now eapply obs_eq_obs_implies_eqITree.
Qed.

Lemma itree_bind_unfold {R1 : Type} {R2 : Type} (t0 : itree E R1) (k0 : R1 -> itree E R2) :
  bind t0 k0 ==
  match t0.(observe) with
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

End ItreeBisimulation.

Module EQIT.

Section eqit_defn.

#[local] Notation In := L.In.
#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "\subseteq" := E.isSubsetOf : type_scope.

#[local] Existing Instance ensemble_isUpperSemilattice.

#[universes(polymorphic=yes)]
Definition subseteq1@{u1} {A : Type@{u1}} (REL : A -> Prop) (REL' : A -> Prop) : Prop :=
  forall x : A, REL x -> REL' x.

#[universes(polymorphic=yes)]
Definition subseteq2@{u1 u2} {A : Type@{u1}} {B : Type@{u2}} (REL : A -> B -> Prop) (REL' : A -> B -> Prop) : Prop :=
  forall x : A, forall y : B, REL x y -> REL' x y.

#[universes(polymorphic=yes)]
Definition subseteq3@{u1 u2 u3} {A : Type@{u1}} {B : Type@{u2}} {C : Type@{u3}} (REL : A -> B -> C -> Prop) (REL' : A -> B -> C -> Prop) : Prop :=
  forall x : A, forall y : B, forall z, REL x y z -> REL' x y z.

#[local] Hint Unfold subseteq1 subseteq2 subseteq3 : core.

#[local] Infix "=~=" := is_similar_to.

Context {E : Type -> Type} {R : Type} {R' : Type} {R_sim : Similarity R R'}.

Inductive eqitF {skip_l : bool} {skip_r : bool} (vclo : (itree E R -> itree E R' -> Prop) -> itree E R -> itree E R' -> Prop) (sim : itree E R -> itree E R' -> Prop) : Similarity (itreeF (itree E R) E R) (itreeF (itree E R') E R') :=
  | EqRet (r1 : R) (r2 : R')
    (REL : r1 =~= r2)
    : RetF r1 =~= RetF r2
  | EqTau (t1 : itree E R) (t2 : itree E R')
    (REL : sim t1 t2)
    : TauF t1 =~= TauF t2
  | EqVis (X : Type) (e : E X) (k1 : X -> itree E R) (k2 : X -> itree E R')
    (REL : forall x : X, vclo sim (k1 x) (k2 x))
    : VisF X e k1 =~= VisF X e k2
  | EqTauL (t1 : itree E R) (ot2 : itreeF (itree E R') E R')
    (skip_l_is_true : skip_l = true)
    (REL : @eqitF skip_l skip_r vclo sim t1.(observe) ot2)
    : TauF t1 =~= ot2
  | EqTauR (ot1 : itreeF (itree E R) E R) (t2 : itree E R')
    (skip_r_is_true : skip_r = true)
    (REL : @eqitF skip_l skip_r vclo sim ot1 t2.(observe))
    : ot1 =~= TauF t2.

#[local] Hint Unfold is_similar_to : core.
#[local] Hint Constructors eqitF : core.

Context (skip_l : bool) (skip_r : bool).

Lemma eqitF_monotonic (lhs : @itreeF (itree E R) E R) (rhs : @itreeF (itree E R') E R') (vclo : (itree E R -> itree E R' -> Prop) -> itree E R -> itree E R' -> Prop) (vclo' : (itree E R -> itree E R' -> Prop) -> itree E R -> itree E R' -> Prop) (sim : Similarity (itree E R) (itree E R')) (sim' : Similarity (itree E R) (itree E R'))
  (IN : @eqitF skip_l skip_r vclo sim lhs rhs)
  (MON_vclo : forall sim : itree E R -> itree E R' -> Prop, forall sim' : itree E R -> itree E R' -> Prop, subseteq2 sim sim' -> subseteq2 (vclo sim) (vclo sim'))
  (LE_vclo : subseteq3 vclo vclo')
  (LE_sim : subseteq2 sim sim')
  : @eqitF skip_l skip_r vclo' sim' lhs rhs.
Proof.
  change (is_similar_to (Similarity := @eqitF skip_l skip_r vclo' sim') lhs rhs).
  induction IN; simpl; eauto. econstructor; i. eapply LE_vclo; eapply MON_vclo; eauto.
Qed.

Definition eqitF' (vclo : Similarity (itree E R) (itree E R') -> Similarity (itree E R) (itree E R')) (sim : Similarity (itree E R) (itree E R')) : ensemble (itree E R * itree E R') :=
  fun '(lhs, rhs) => is_similar_to (Similarity := @eqitF skip_l skip_r vclo sim) lhs.(observe) rhs.(observe).

#[local]
Instance eqit : Similarity (itree E R) (itree E R') :=
  curry (paco (fun REL : ensemble (itree E R * itree E R') => eqitF' id (curry REL)) E.empty).

#[local] Hint Unfold is_similar_to : core.

Section eqitF_elim.

#[local] Notation R1 := R.
#[local] Notation R2 := R'.
#[local] Notation RR := R_sim.
#[local] Notation b1 := skip_l.
#[local] Notation b2 := skip_r.
#[local] Notation SIM := (Similarity (itree E R1) (itree E R2)).

Let __LocalInstance_eqitF : forall vclo : SIM -> SIM, forall sim : SIM, Similarity (@itreeF (itree E R1) E R1) (@itreeF (itree E R2) E R2) :=
  @eqitF b1 b2.

#[local] Existing Instance __LocalInstance_eqitF.

Lemma eqitF_t1_VisF_X2_e2_k2_elim {vclo : SIM -> SIM} {sim : SIM} (t1 : @itreeF (itree E R1) E R1) (X2 : Type) (e2 : E X2) (k2 : X2 -> itree E R2)
  (H_eqitF : is_similar_to (Similarity := __LocalInstance_eqitF vclo sim) t1 (VisF X2 e2 k2))
  : ⟪ is_VisF : exists k1, t1 = VisF X2 e2 k1 /\ forall x, is_similar_to (Similarity := vclo sim) (k1 x) (k2 x) ⟫ \/ ⟪ is_TauF : b1 = true /\ exists t1', t1 = TauF t1' /\ is_similar_to (Similarity := __LocalInstance_eqitF vclo sim) t1'.(observe) (VisF X2 e2 k2) ⟫.
Proof with eauto.
  refine (
    match H_eqitF in @eqitF _ _ _ _ t1 t2 return
      match t2 return Prop with
      | VisF X2 e2 k2 => (exists k1, t1 = VisF X2 e2 k1 /\ forall x, k1 x =~= k2 x) \/ (b1 = true /\ exists t1', t1 = TauF t1' /\ t1'.(observe) =~= VisF X2 e2 k2)
      | _ => True
      end
    with
    | EqVis _ _ _ _ _ _ _ => _
    | EqTauL _ _ _ _ _ _ => _
    | _ => I
    end
  )...
  match goal with [ t : @itreeF (itree E R2) E R2 |- _ ] => destruct t end...
Qed.

Lemma eqitF_VisF_X1_e1_k1_t2_elim {vclo : SIM -> SIM} {sim : SIM} (X1 : Type) (e1 : E X1) (k1 : X1 -> itree E R1) (t2 : @itreeF (itree E R2) E R2)
  (H_eqitF : is_similar_to (Similarity := __LocalInstance_eqitF vclo sim) (VisF X1 e1 k1) t2)
  : ⟪ is_VisF : exists k2, t2 = VisF X1 e1 k2 /\ forall x, is_similar_to (Similarity := vclo sim) (k1 x) (k2 x) ⟫ \/ ⟪ is_TauF : b2 = true /\ exists t2', t2 = TauF t2' /\ is_similar_to (Similarity := __LocalInstance_eqitF vclo sim) (VisF X1 e1 k1) t2'.(observe) ⟫.
Proof with eauto.
  refine (
    match H_eqitF in @eqitF _ _ _ _ t1 t2 return
      match t1 return Prop with
      | VisF X1 e1 k1 => (exists k2, t2 = VisF X1 e1 k2 /\ forall x, k1 x =~= k2 x) \/ (b2 = true /\ exists t2', t2 = TauF t2' /\ VisF X1 e1 k1 =~= t2'.(observe))
      | _ => True
      end
    with
    | EqVis _ _ _ _ _ _ _ => _
    | EqTauR _ _ _ _ _ _ => _
    | _ => I
    end
  )...
  match goal with [ t : @itreeF (itree E R1) E R1 |- _ ] => destruct t end...
Qed.

Lemma eqitF_t1_RetF_r2_elim {vclo : SIM -> SIM} {sim : SIM} (t1 : @itreeF (itree E R1) E R1) (r2 : R2)
  (H_eqitF : is_similar_to (Similarity := __LocalInstance_eqitF vclo sim) t1 (RetF r2))
  : ⟪ is_RetF : exists r1, t1 = RetF r1 /\ r1 =~= r2 ⟫ \/ ⟪ is_TauF : b1 = true /\ exists t1', t1 = TauF t1' /\ is_similar_to (Similarity := __LocalInstance_eqitF vclo sim) t1'.(observe) (RetF r2) ⟫.
Proof with eauto.
  refine (
    match H_eqitF in @eqitF _ _ _ _ t1 t2 return
      match t2 return Prop with
      | RetF r2 => (exists r1, t1 = RetF r1 /\ r1 =~= r2) \/ (b1 = true /\ exists t1', t1 = TauF t1' /\ t1'.(observe) =~= RetF r2)
      | _ => True
      end
    with
    | EqRet _ _ _ _ _ => _
    | EqTauL _ _ _ _ _ _ => _
    | _ => I
    end
  )...
  match goal with [ t : @itreeF (itree E R2) E R2 |- _ ] => destruct t end...
Qed.

Lemma eqitF_RetF_r1_t2_elim {vclo : SIM -> SIM} {sim : SIM} (r1 : R1) (t2 : @itreeF (itree E R2) E R2)
  (H_eqitF : is_similar_to (Similarity := __LocalInstance_eqitF vclo sim) (RetF r1) t2)
  : ⟪ is_RetF : exists r2, t2 = RetF r2 /\ r1 =~= r2 ⟫ \/ ⟪ is_TauF : b2 = true /\ exists t2', t2 = TauF t2' /\ is_similar_to (Similarity := __LocalInstance_eqitF vclo sim) (RetF r1) t2'.(observe) ⟫.
Proof with eauto.
  refine (
    match H_eqitF in @eqitF _ _ _ _ t1 t2 return
      match t1 return Prop with
      | RetF r1 => (exists r2, t2 = RetF r2 /\ r1 =~= r2) \/ (b2 = true /\ exists t2', t2 = TauF t2' /\ RetF r1 =~= t2'.(observe))
      | _ => True
      end
    with
    | EqRet _ _ _ _ _ => _
    | EqTauR _ _ _ _ _ _ => _
    | _ => I
    end
  )...
  match goal with [ t : @itreeF (itree E R1) E R1 |- _ ] => destruct t end...
Qed.

Lemma eqitF_t1_TauF_u2_elim {vclo : SIM -> SIM} {sim : SIM} (t1 : @itreeF (itree E R1) E R1) (u2 : itree E R2)
  (H_eqitF : is_similar_to (Similarity := __LocalInstance_eqitF vclo sim) t1 (TauF u2))
  : ⟪ is_TauF : exists t1', t1 = TauF t1' /\ is_similar_to (Similarity := sim) t1' u2 ⟫ \/ ⟪ is_TauL : b1 = true /\ exists t1', t1 = TauF t1' /\ is_similar_to (Similarity := __LocalInstance_eqitF vclo sim) t1'.(observe) (TauF u2) ⟫ \/ ⟪ is_TauR : b2 = true /\ is_similar_to (Similarity := __LocalInstance_eqitF vclo sim) t1 u2.(observe) ⟫.
Proof with eauto.
  refine (
    match H_eqitF in @eqitF _ _ _ _ t1 t2 return
      match t2 return Prop with
      | TauF u2 => (exists t1', t1 = TauF t1' /\ t1' =~= u2) \/ (b1 = true /\ exists t1', t1 = TauF t1' /\ t1'.(observe) =~= TauF u2) \/ (b2 = true /\ t1 =~= u2.(observe))
      | _ => True
      end
    with
    | EqTau _ _ _ _ _ => _
    | EqTauL _ _ _ _ _ _ => _
    | EqTauR _ _ _ _ _ _ => _
    | _ => I
    end
  ); clear H_eqitF...
  destruct i0; eauto; cbv in *. right; left...
Qed.

Lemma eqitF_TauF_u1_t2_elim {vclo : SIM -> SIM} {sim : SIM} (u1 : itree E R1) (t2 : @itreeF (itree E R2) E R2)
  (H_eqitF : is_similar_to (Similarity := __LocalInstance_eqitF vclo sim) (TauF u1) t2)
  : ⟪ is_TauF : exists t2', t2 = TauF t2' /\ is_similar_to (Similarity := sim) u1 t2' ⟫ \/ ⟪ is_TauL : b1 = true /\ is_similar_to (Similarity := __LocalInstance_eqitF vclo sim) u1.(observe) t2 ⟫ \/ ⟪ is_TauR : b2 = true /\ exists t2', t2 = TauF t2' /\ is_similar_to (Similarity := __LocalInstance_eqitF vclo sim) (TauF u1) t2'.(observe) ⟫.
Proof with eauto.
  refine (
    match H_eqitF in @eqitF _ _ _ _ t1 t2 return
      match t1 return Prop with
      | TauF u1 => (exists t2', t2 = TauF t2' /\ u1 =~= t2') \/ (b1 = true /\ u1.(observe) =~= t2) \/ (b2 = true /\ exists t2', t2 = TauF t2' /\ TauF u1 =~= t2'.(observe))
      | _ => True
      end
    with
    | EqTau _ _ _ _ _ => _
    | EqTauL _ _ _ _ _ _ => _
    | EqTauR _ _ _ _ _ _ => _
    | _ => I
    end
  ); clear H_eqitF...
  destruct i; eauto; cbv in *. right; right...
Qed.

Theorem VisF_eqitF_VisF_iff {vclo : SIM -> SIM} {sim : SIM} (X1 : Type) (X2 : Type) (e1 : E X1) (e2 : E X2) (k1 : X1 -> itree E R1) (k2 : X2 -> itree E R2)
  : is_similar_to (Similarity := __LocalInstance_eqitF vclo sim) (VisF X1 e1 k1) (VisF X2 e2 k2) <-> { X_EQ : X1 = X2 | @eq_rect Type X1 (fun X => E X) e1 X2 X_EQ = e2 /\ is_similar_to (Similarity := fun lhs => fun rhs => forall x : X2, vclo sim (lhs x) (rhs x)) (@eq_rect Type X1 (fun X => X -> itree E R1) k1 X2 X_EQ) k2 }.
Proof with eauto.
  split.
  - refine (fun H_eqitF =>
      match H_eqitF in @eqitF _ _ _ _ t1 t2 return
        match t1, t2 return Prop with
        | VisF X1 e1 k1, VisF X2 e2 k2 => _
        | _, _ => True
        end
      with
      | EqVis _ _ _ _ _ _ _ => _
      | _ => _
      end
    )...
    + exists eq_refl; cbn...
    + match goal with [ t : @itreeF (itree E R1) E R1 |- _ ] => destruct t end...
  - intros (X_EQ & ? & ?); destruct X_EQ; cbn in *; subst. econs...
Qed.

End eqitF_elim.

End eqit_defn.

Section eqit_prop.

#[local] Hint Unfold is_similar_to : core.

#[local] Notation In := L.In.
#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "\subseteq" := E.isSubsetOf : type_scope.

#[local] Existing Instance ensemble_isUpperSemilattice.

#[local] Infix "=~=" := is_similar_to.

#[local] Infix "≈ₜ" := (eqit true true).
#[local] Infix "≳ₜ" := (eqit true false).
#[local] Infix "≲ₜ" := (eqit false true).
#[local] Infix "≃ₜ" := (eqit false false).

#[local] Hint Resolve bot_lattice_spec : poset_hints.
#[local] Hint Resolve join_lattice_spec : poset_hints.
#[local] Hint Resolve Equivalence_Reflexive Equivalence_Symmetric Equivalence_Transitive : poset_hints.
#[local] Hint Resolve eqProp_refl eqProp_sym eqProp_trans leProp_refl leProp_trans leProp_antisymmetry eqProp_implies_leProp : poset_hints.
#[local] Hint Unfold upperboundsOf : poset_hints.

Context {E : Type -> Type}.

Section GENERAL.

Context {R : Type} {R' : Type} {R_sim : Similarity R R'}.

Definition eqit_op (skip_l : bool) (skip_r : bool) : ensemble (itree E R * itree E R') -> ensemble (itree E R * itree E R') :=
  fun REL : ensemble (itree E R * itree E R') => @eqitF' E R R' R_sim skip_l skip_r id (curry REL).

Lemma eqitF_id_monotonic (skip_l : bool) (skip_r : bool) (sim sim' : itree E R -> itree E R' -> Prop) (ot1 : itreeF (itree E R) E R) (ot2 : itreeF (itree E R') E R')
  (LE_sim : subseteq2 sim sim')
  (H_IN : @eqitF E R R' R_sim skip_l skip_r id sim ot1 ot2)
  : @eqitF E R R' R_sim skip_l skip_r id sim' ot1 ot2.
Proof.
  induction H_IN as [r1 r2 H_REL | u1 u2 H_REL | X e k1 k2 H_REL | u1 ou2 SK H_REL IH | ou1 u2 SK H_REL IH].
  - econstructor; eauto.
  - econstructor. exact (LE_sim u1 u2 H_REL).
  - econstructor. intros x. exact (LE_sim (k1 x) (k2 x) (H_REL x)).
  - eapply EqTauL; eauto.
  - eapply EqTauR; eauto.
Qed.

Lemma eqit_op_isMonotonic1 (skip_l : bool) (skip_r : bool)
  : isMonotonic1 (eqit_op skip_l skip_r).
Proof.
  intros REL REL' LE_REL [t1 t2] H_IN. red. red in H_IN.
  eapply eqitF_id_monotonic; eauto. ii; cbv in *; eauto.
Qed.

#[local] Hint Resolve eqit_op_isMonotonic1 : core.

Lemma eqit_iff_paco_eqit_op (skip_l : bool) (skip_r : bool) (t1 : itree E R) (t2 : itree E R')
  : is_similar_to (Similarity := @eqit E R R' R_sim skip_l skip_r) t1 t2 <-> (t1, t2) \in paco (eqit_op skip_l skip_r) bot_lattice.
Proof.
  reflexivity.
Qed.

Lemma eqit_unfold (skip_l : bool) (skip_r : bool) (t1 : itree E R) (t2 : itree E R')
  (H_eqit : is_similar_to (Similarity := @eqit E R R' R_sim skip_l skip_r) t1 t2)
  : @eqitF E R R' R_sim skip_l skip_r id (is_similar_to (Similarity := @eqit E R R' R_sim skip_l skip_r)) t1.(observe) t2.(observe).
Proof.
  pose proof (paco_unfold (eqit_op skip_l skip_r) bot_lattice (eqit_op_isMonotonic1 skip_l skip_r)) as H.
  apply H in H_eqit. red in H_eqit. eapply eqitF_id_monotonic; eauto.
  intros u1 u2 [u_in | u_in]; [inversion u_in | exact u_in].
Qed.

Lemma eqit_fold (skip_l : bool) (skip_r : bool) (t1 : itree E R) (t2 : itree E R')
  (H_step : @eqitF E R R' R_sim skip_l skip_r id (is_similar_to (Similarity := @eqit E R R' R_sim skip_l skip_r)) t1.(observe) t2.(observe))
  : is_similar_to (Similarity := @eqit E R R' R_sim skip_l skip_r) t1 t2.
Proof.
  pose proof (paco_fold (eqit_op skip_l skip_r) bot_lattice) as H.
  eapply H. red. eapply eqitF_id_monotonic; eauto.
  intros u1 u2 SIM. right. exact SIM.
Qed.

Lemma eqit_obs_eq_obs skip_l skip_r t1 t1' t2 t2'
  (OBS_EQ_l : t1.(observe) = t1'.(observe))
  (OBS_EQ_r : t2.(observe) = t2'.(observe))
  (H_eqit : is_similar_to (Similarity := @eqit E R R' R_sim skip_l skip_r) t1 t2)
  : is_similar_to (Similarity := @eqit E R R' R_sim skip_l skip_r) t1' t2'.
Proof.
  apply eqit_unfold in H_eqit. eapply eqit_fold.
  now rewrite <- OBS_EQ_l, <- OBS_EQ_r.
Qed.

Lemma eqitF_skip_mon b1 b1' b2 b2' sim sim' (ot1 : itreeF (itree E R) E R) (ot2 : itreeF (itree E R') E R')
  (LE1 : b1 = true -> b1' = true)
  (LE2 : b2 = true -> b2' = true)
  (LE_sim : subseteq2 sim sim')
  (H_IN : @eqitF E R R' R_sim b1 b2 id sim ot1 ot2)
  : @eqitF E R R' R_sim b1' b2' id sim' ot1 ot2.
Proof.
  induction H_IN as [r1 r2 H_REL | u1 u2 H_REL | X e k1 k2 H_REL | u1 ou2 SK H_REL IH | ou1 u2 SK H_REL IH].
  - econstructor; eauto.
  - econstructor. exact (LE_sim _ _ H_REL).
  - econstructor. intros x. exact (LE_sim _ _ (H_REL x)).
  - eapply EqTauL; auto.
  - eapply EqTauR; auto.
Qed.

Lemma eqit_skip_mon b1 b1' b2 b2' t1 t2
  (LE1 : b1 = true -> b1' = true)
  (LE2 : b2 = true -> b2' = true)
  (H_eqit : is_similar_to (Similarity := @eqit E R R' R_sim b1 b2) t1 t2)
  : is_similar_to (Similarity := @eqit E R R' R_sim b1' b2') t1 t2.
Proof with eauto with *.
  revert t1 t2 H_eqit.
  set (Y := fun p : itree E R * itree E R' => is_similar_to (Similarity := @eqit E R R' R_sim b1 b2) (fst p) (snd p)).
  enough (CLAIM : Y \subseteq paco (eqit_op b1' b2') bot_lattice).
  { intros u1 u2 H. exact (CLAIM (u1, u2) H). }
  eapply paco_accum... set (Rel_focus := join_lattice bot_lattice Y).
  rewrite <- paco_fold. intros [u1 u2] H_IN.
  apply eqit_unfold in H_IN. red.
  eapply eqitF_skip_mon with (b1 := b1) (b2 := b2) (sim := fun v1 v2 => is_similar_to (Similarity := @eqit E R R' R_sim b1 b2) v1 v2)...
  intros v1 v2 SIM. left. right. exact SIM.
Qed.

Corollary eq_sub_eqit b1 b2 (t1 : itree E R) (t2 : itree E R')
  (H_eqit : is_similar_to (Similarity := @eqit E R R' R_sim false false) t1 t2)
  : is_similar_to (Similarity := @eqit E R R' R_sim b1 b2) t1 t2.
Proof.
  eapply eqit_skip_mon; cycle -1; eauto.
Qed.

Lemma eqit_Tau_inv_l b1 (t1 : itree E R) (t2 : itree E R')
  (H_eqit : is_similar_to (Similarity := @eqit E R R' R_sim b1 true) (Tau t1) t2)
  : is_similar_to (Similarity := @eqit E R R' R_sim b1 true) t1 t2.
Proof with eauto.
  apply eqit_unfold in H_eqit; simpl in H_eqit. apply eqit_fold. revert H_eqit.
  remember (TauF t1) as ot eqn: H_ot. intros H. revert t1 H_ot. induction H; ii; inv H_ot...
  - econs 5... eapply eqit_unfold...
  - econs 5...
Qed.

Lemma eqit_Tau_inv_r b2 (t1 : itree E R) (t2 : itree E R')
  (H_eqit : is_similar_to (Similarity := @eqit E R R' R_sim true b2) t1 (Tau t2))
  : is_similar_to (Similarity := @eqit E R R' R_sim true b2) t1 t2.
Proof with eauto.
  apply eqit_unfold in H_eqit; simpl in H_eqit. apply eqit_fold. revert H_eqit.
  remember (TauF t2) as ot eqn: H_ot. intros H. revert t2 H_ot. induction H; ii; inv H_ot...
  - econs 4... eapply eqit_unfold...
  - econs 4...
Qed.

Theorem TauF_eqit_TauF_iff b1 b2 (t1 : itree E R) (t2 : itree E R')
  : is_similar_to (Similarity := @eqit E R R' R_sim b1 b2) (Tau t1) (Tau t2) <-> is_similar_to (Similarity := @eqit E R R' R_sim b1 b2) t1 t2.
Proof with eauto.
  split.
  - intros H_eqit. apply eqit_unfold in H_eqit; simpl in H_eqit. apply eqit_fold. revert H_eqit.
    remember (TauF t1) as ot1 eqn: H_ot1. remember (TauF t2) as ot2 eqn: H_ot2.
    intros H. revert t1 t2 H_ot1 H_ot2. induction H; ii; try congruence.
    + inv H_ot1. inv H_ot2. eapply eqit_unfold...
    + inv H_ot1. inv H...
      * econs...
      * econs... 
    + inv H_ot2. inv H...
      * econs...
      * econs...
  - intros H_eqit. eapply eqit_fold. econs 2...
Qed.

End GENERAL.

#[local] Hint Resolve eqit_op_isMonotonic1 : core.

Section reflexivity.

Context {R : Type} {R_sim : Similarity R R}.

Hypothesis R_sim_refl : forall r : R, r =~= r.

Lemma eqit_reflexivity (b1 : bool) (b2 : bool)
  : Reflexive (is_similar_to (Similarity := @eqit E R R R_sim b1 b2)).
Proof with eauto with *.
  enough (CLAIM : @B.Rel_id (itree E R) \subseteq paco (eqit_op (R' := R) (R_sim := R_sim) b1 b2) bot_lattice).
  { intros t. exact (CLAIM (t, t) eq_refl). }
  eapply paco_accum... set (Rel_focus := join_lattice bot_lattice (@B.Rel_id (itree E R))).
  rewrite <- paco_fold. intros [t1 t2] H_EQ. repeat red. do 2 red in H_EQ.
  destruct t1.(observe) as [r1 | u1 | X1 e1 k1] eqn: H_obs1; destruct t2.(observe) as [r2 | u2 | X2 e2 k2] eqn: H_obs2; try congruence.
  - econstructor. assert (r1 = r2) by congruence. subst r2...
  - econstructor. left. right. red. congruence.
  - assert (obs_eq : @eq (itreeF (itree E R) E R) (VisF X1 e1 k1) (VisF X2 e2 k2)) by congruence.
    rewrite obs_eq. econstructor. intros x. left. right. red. reflexivity.
Qed.

End reflexivity.

Section symmetry.

Context {R : Type} {R' : Type} {R_sim : Similarity R R'} {R_sim_flip : Similarity R' R}.

Hypothesis R_sim_swap : forall r1 : R, forall r2 : R', r1 =~= r2 -> r2 =~= r1.

Lemma eqitF_symmetry b1 b2 sim sim' (ot1 : itreeF (itree E R) E R) (ot2 : itreeF (itree E R') E R')
  (sim_swap : forall t1, forall t2, sim t1 t2 -> sim' t2 t1)
  (H_eqitF : @eqitF E R R' R_sim b1 b2 id sim ot1 ot2)
  : @eqitF E R' R R_sim_flip b2 b1 id sim' ot2 ot1.
Proof.
  induction H_eqitF as [r1 r2 H_REL | u1 u2 H_REL | X e k1 k2 H_REL | u1 ou2 SK H_REL IH | ou1 u2 SK H_REL IH].
  - econstructor. exact (R_sim_swap _ _ H_REL).
  - econstructor. exact (sim_swap _ _ H_REL).
  - econstructor. intros x. exact (sim_swap _ _ (H_REL x)).
  - eapply EqTauR; auto.
  - eapply EqTauL; auto.
Qed.

Theorem eqit_symmetry (b1 : bool) (b2 : bool) (t1 : itree E R) (t2 : itree E R')
  (H_eqit : is_similar_to (Similarity := @eqit E R R' R_sim b1 b2) t1 t2)
  : is_similar_to (Similarity := @eqit E R' R R_sim_flip b2 b1) t2 t1.
Proof with eauto with *.
  revert t1 t2 H_eqit.
  set (Y := fun p : itree E R' * itree E R => is_similar_to (Similarity := @eqit E R R' R_sim b1 b2) (snd p) (fst p)).
  enough (CLAIM : Y \subseteq paco (eqit_op (R := R') (R' := R) (R_sim := R_sim_flip) b2 b1) bot_lattice).
  { intros t1 t2 H. exact (CLAIM (t2, t1) H). }
  eapply paco_accum... set (Rel_focus := join_lattice bot_lattice Y).
  rewrite <- paco_fold. intros [u2 u1] H_IN.
  apply eqit_unfold in H_IN. red.
  eapply eqitF_symmetry...
  intros v1 v2 SIM. left. right. exact SIM.
Qed.

End symmetry.

Section transitivity.

Context {R1 : Type} {R2 : Type} {R3 : Type} {R12 : Similarity R1 R2} {R23 : Similarity R2 R3} {R13 : Similarity R1 R3}.

Hypothesis R_sim_compose : forall r1 : R1, forall r2 : R2, forall r3 : R3, r1 =~= r2 -> r2 =~= r3 -> r1 =~= r3.

Theorem eqit_transitivity (b1 : bool) (b2 : bool) (t1 : itree E R1) (t2 : itree E R2) (t3 : itree E R3)
  (H_12 : is_similar_to (Similarity := @eqit E R1 R2 R12 b1 b2) t1 t2)
  (H_23 : is_similar_to (Similarity := @eqit E R2 R3 R23 b1 b2) t2 t3)
  : is_similar_to (Similarity := @eqit E R1 R3 R13 b1 b2) t1 t3.
Proof with eauto.
  revert t1 t2 t3 H_12 H_23. set (Y := fun p : itree E R1 * itree E R3 => exists s2 : itree E R2, is_similar_to (Similarity := @eqit E R1 R2 R12 b1 b2) (fst p) s2 /\ is_similar_to (Similarity := @eqit E R2 R3 R23 b1 b2) s2 (snd p)).
  enough (CLAIM : Y \subseteq paco (eqit_op (R_sim := R13) b1 b2) bot_lattice).
  { intros t1 t2 t3 H_12 H_23. eapply CLAIM. exists t2... }
  change (Y =< paco (eqit_op b1 b2) bot_lattice). eapply pcofix1.
  intros K _ CIH [t1 t3] (t2 & H_12 & H_23); simpl in H_12, H_23. eapply paco_fold. do 4 red.
  apply eqit_unfold in H_12, H_23. revert H_12 H_23. generalize t3.(observe) as ot3. generalize t2.(observe) as ot2. generalize t1.(observe) as ot1.
  clear t1 t2 t3. intros ot1 ot2 ot3 H H_23. revert ot3 H_23. induction H.
  - remember (RetF r2) as ot2 eqn: H_ot2. ii. revert r2 H_ot2 REL. induction H_23; ii; try inv H_ot2.
    + econs 1...
    + econs 5...
  - ii.
    assert (DEC : ⟪ EQ : exists t3, ot3 = TauF t3 ⟫ \/ ⟪ NE : forall t3, ot3 ≠ TauF t3 ⟫).
    { destruct ot3 as [ | | ]; [right | left | right]; eauto; intros; congruence. }
    des.
    + subst ot3. econs 2. red. left. eapply CIH. exists t2; simpl. split...
      rewrite <- TauF_eqit_TauF_iff. eapply eqit_fold...
    + inv H_23; try contradiction (NE _ eq_refl). econs 4... apply eqit_unfold in REL.
      revert REL REL0. generalize t2.(observe) as ot2. generalize t1.(observe) as ot1. clear t1 t2.
      intros ot1 ot2 H_12 H. revert ot1 H_12. induction H; ii; try contradiction (NE _ eq_refl).
      { clear NE. remember (RetF r1) as ot eqn: H_ot. revert r1 r2 REL H_ot. rename H_12 into H. induction H; ii; inv H_ot.
        - econs 1...
        - econs 4...
      }
      { clear NE. remember (VisF X e k1) as ot eqn: H_ot. revert X e k1 k2 REL H_ot. rename H_12 into H. induction H; ii; try congruence.
        apply VisF_eq_VisF_elim in H_ot. destruct H_ot as [X_EQ EQ]. destruct X_EQ; simpl in *. inv EQ.
        - econs 3. intros x. left. eapply CIH. exists (k0 x); simpl. unfold id in *. split...
        - econs 4...
      }
      { eapply IHeqitF... apply eqitF_t1_TauF_u2_elim in H_12. set (t := {| observe := ot1 |}). change ot1 with t.(observe). eapply eqit_unfold. subst t. des; subst.
        - eapply eqit_fold. econs 4... eapply eqit_unfold...
        - eapply eqit_fold. econs 4... eapply eqit_unfold... eapply eqit_Tau_inv_r. eapply eqit_fold...
        - eapply eqit_fold...
      }
  - remember (VisF X e k2) as ot2 eqn: H_ot2. ii. revert k2 H_ot2 REL. induction H_23; ii; try congruence.
    + apply VisF_eq_VisF_elim in H_ot2. destruct H_ot2 as [X_EQ EQ]. destruct X_EQ; simpl in *. inv EQ.
      econs 3. intros x. left. eapply CIH. exists (k3 x); simpl. unfold id in *. split...
    + econs 5...
  - ii. econs 4...
  - remember (TauF t2) as ot2 eqn: H_ot2. ii. revert t2 H_ot2 H IHeqitF. induction H_23; ii; inv H_ot2.
    + eapply IHeqitF. apply eqit_unfold in REL. econs 5...
    + eapply IHeqitF...
    + econs 5...
Qed.

End transitivity.

#[local, program]
Instance equality_upto_tau (R : Type) (R_isSetoid : isSetoid R) : isSetoid (itree E R) :=
  { eqProp := eqit (R_sim := eqProp (isSetoid := R_isSetoid)) true true }.
Next Obligation.
  split; ii.
  - eapply eqit_reflexivity; eauto. ii; reflexivity; eauto.
  - eapply eqit_symmetry; eauto. ii; symmetry; eauto.
  - eapply eqit_transitivity; eauto. ii; etransitivity; eauto.
Qed.

#[global]
Instance eutt : isSetoid1 (itree E) :=
  equality_upto_tau.

Lemma observe_eq_observe_implies_eqit {R} (b1 : bool) (b2 : bool) (t1 : itree E R) (t2 : itree E R)
  (OBS_EQ : t1.(observe) = t2.(observe))
  : is_similar_to (Similarity := @eqit E R R eq b1 b2) t1 t2.
Proof.
  eapply eqit_obs_eq_obs with (t1 := t2) (t2 := t2); auto.
  eapply eqit_reflexivity; eauto.
Qed.

Lemma itree_bind_obs_eq {R1} {R2} (k0 : R1 -> itree E R2) (t0 : itree E R1) :
  (itree_bind' k0 t0).(observe) =
  match t0.(observe) with
  | RetF r => (k0 r).(observe)
  | TauF t => TauF (itree_bind' k0 t)
  | VisF X e k => VisF X e (fun x : X => itree_bind' k0 (k x))
  end.
Proof.
  rewrite ItreeBisimulation.itree_bind_unfold_observed.
  destruct t0.(observe); reflexivity.
Defined.

Lemma Tau_eutt_aux {R : Type} (t : itree E R)
  : is_similar_to (Similarity := @eqit E R R eq true true) (Tau t) t.
Proof.
  eapply eqit_fold. simpl. eapply EqTauL with (t1 := t) (ot2 := observe t); auto. eapply eqit_unfold.
  exact (eqit_reflexivity (R := R) (R_sim := @eq R) (fun r : R => @eq_refl R r) true true t).
Qed.

Lemma bind_pure_l_eutt {R1} {R2} (k : R1 -> itree E R2) (x : R1)
  : is_similar_to (Similarity := @eqit E R2 R2 eq true true) (pure x >>= k) (k x).
Proof.
  eapply observe_eq_observe_implies_eqit. reflexivity.
Qed.

Lemma bind_pure_r_eutt {R : Type} (t : itree E R)
  : is_similar_to (Similarity := @eqit E R R eq true true) (t >>= pure) t.
Proof with eauto with *.
  revert t.
  set (Y := fun p : itree E R * itree E R => exists t : itree E R, p = (t >>= pure, t)).
  enough (CLAIM : Y \subseteq paco (eqit_op (R_sim := @eq R) true true) bot_lattice).
  { intros t. eapply CLAIM. exists t... }
  change (Y =< paco (eqit_op (R_sim := @eq R) true true) bot_lattice). eapply pcofix1.
  intros K _ CIH p H_in. destruct H_in as (t & ?); subst p. eapply paco_fold. cbv [eqit_op eqitF' E.In].
  cbn beta iota. simpl bind. rewrite itree_bind_obs_eq. destruct t.(observe); simpl.
  - econs 1...
  - econs 2. left. eapply CIH. exists t0...
  - econstructor 3. intros x. left. eapply CIH. exists (k x)...
Qed.

Lemma bind_assoc_eutt {R1} {R2} {R3} (m : itree E R1) (k1 : R1 -> itree E R2) (k2 : R2 -> itree E R3)
  : is_similar_to (Similarity := @eqit E R3 R3 eq true true) (m >>= (fun x : R1 => k1 x >>= k2)) ((m >>= k1) >>= k2).
Proof with eauto with *.
  revert m.
  set (Y := fun p : itree E R3 * itree E R3 => exists m : itree E R1, p = (m >>= (fun x : R1 => k1 x >>= k2), (m >>= k1) >>= k2)).
  enough (CLAIM : Y \subseteq paco (eqit_op (R_sim := @eq R3) true true) bot_lattice).
  { intros m. eapply CLAIM. exists m... }
  change (Y =< paco (eqit_op (R_sim := @eq R3) true true) bot_lattice). eapply pcofix1.
  intros K _ CIH p H_in. destruct H_in as (m & ?); subst p. eapply paco_fold. cbv [eqit_op eqitF' E.In].
  cbn beta iota. simpl bind. rewrite !itree_bind_obs_eq. destruct m.(observe) as [r | u | X e k0]; simpl.
  - destruct (k1 r).(observe) as [r' | u' | X' e' k']; simpl.
    + eapply eqitF_id_monotonic; cycle -1.
      * eapply eqit_unfold. eapply eqit_reflexivity. eauto.
      * intros t1 t2 SIM. right. red. revert SIM. eapply paco_preserves_monotonicity; s!.
        { eapply eqit_op_isMonotonic1. }
        { done!. }
    + econs 2. right. red. eapply paco_preserves_monotonicity with (F := eqit_op (R_sim := @eq R3) true true).
      { eapply eqit_op_isMonotonic1. }
      { eapply bot_lattice_le_intro. }
      { exact (eqit_reflexivity (fun r : R3 => @eq_refl R3 r) true true (itree_bind' k2 u')). }
    + econs 3. intros x. right. eapply paco_preserves_monotonicity with (F := eqit_op (R_sim := @eq R3) true true).
      { eapply eqit_op_isMonotonic1. }
      { eapply bot_lattice_le_intro. }
      { exact (eqit_reflexivity (fun r : R3 => @eq_refl R3 r) true true (itree_bind' k2 (k' x))). }
  - econs 2. left. eapply CIH. exists u...
  - econs 3. intros x. left. eapply CIH. exists (k0 x)...
Qed.

Lemma bind_compatWith_eqProp_l_eutt {R1} {R2} (k0 : R1 -> itree E R2) (t1 : itree E R1) (t2 : itree E R1)
  (HYP : is_similar_to (Similarity := @eqit E R1 R1 eq true true) t1 t2)
  : is_similar_to (Similarity := @eqit E R2 R2 eq true true) (t1 >>= k0) (t2 >>= k0).
Proof with eauto with *.
  revert t1 t2 HYP.
  set (Y := fun p : itree E R2 * itree E R2 => exists s1 s2 : itree E R1, p = (s1 >>= k0, s2 >>= k0) /\ is_similar_to (Similarity := @eqit E R1 R1 eq true true) s1 s2).
  enough (CLAIM : Y \subseteq paco (eqit_op (R_sim := @eq R2) true true) bot_lattice).
  { intros t1 t2 H. eapply CLAIM. exists t1, t2... }
  change (Y =< paco (eqit_op (R_sim := @eq R2) true true) bot_lattice). eapply pcofix1.
  intros K _ CIH p H_in. destruct H_in as (s1 & s2 & ? & H_eutt); subst p. eapply paco_fold. cbv [eqit_op eqitF' E.In].
  cbn beta iota. apply eqit_unfold in H_eutt. simpl bind. rewrite !itree_bind_obs_eq.
  induction H_eutt as [r1 r2 REL | u1 u2 REL | X e k1 k2 REL | u1 ot2_inner SK_l REL IH | ot1_inner u2 SK_r REL IH]; simpl.
  - change (r1 = r2) in REL. subst r2. eapply eqitF_id_monotonic; cycle -1.
    + eapply eqit_unfold. exact (eqit_reflexivity (fun r : R2 => @eq_refl R2 r) true true (k0 r1)).
    + intros t1 t2 SIM. right. red. revert SIM. eapply paco_preserves_monotonicity; s!.
      { eapply eqit_op_isMonotonic1. }
      { done!. }
  - econs 2. left. eapply CIH. exists u1, u2. split...
  - econs 3. intros x. left. eapply CIH. unfold id in *. exists (k1 x), (k2 x). split...
  - econs 4; auto. rewrite itree_bind_obs_eq...
  - econs 5; auto. rewrite itree_bind_obs_eq...
Qed.

Lemma bind_compatWith_eqProp_r_eutt {R1} {R2} (m : itree E R1) (k1 : R1 -> itree E R2) (k2 : R1 -> itree E R2)
  (HYP : forall x : R1, is_similar_to (Similarity := @eqit E R2 R2 eq true true) (k1 x) (k2 x))
  : is_similar_to (Similarity := @eqit E R2 R2 eq true true) (m >>= k1) (m >>= k2).
Proof with eauto with *.
  revert m.
  set (Y := fun p : itree E R2 * itree E R2 => exists m : itree E R1, p = (m >>= k1, m >>= k2)).
  enough (CLAIM : Y \subseteq paco (eqit_op (R_sim := @eq R2) true true) bot_lattice).
  { intros m. eapply CLAIM. exists m... }
  change (Y =< paco (eqit_op (R_sim := @eq R2) true true) bot_lattice).
  eapply pcofix1. intros K _ CIH p H_in. destruct H_in as (m & ?); subst p. eapply paco_fold. cbv [eqit_op eqitF' E.In].
  cbn beta iota. simpl bind. rewrite !itree_bind_obs_eq. destruct m.(observe) as [r | u | X e k0]; simpl.
  - eapply eqitF_id_monotonic; cycle -1.
    + eapply eqit_unfold...
    + intros t1 t2 SIM. right. red. revert SIM. eapply paco_preserves_monotonicity; s!.
      { eapply eqit_op_isMonotonic1. }
      { done!. }
  - econs 2. left. eapply CIH. exists u...
  - econs 3. intros x. left. eapply CIH. exists (k0 x)...
Qed.

#[global]
Instance itree_eutt_MonadLaws : @MonadLaws (itree E) eutt itree_isMonad :=
  { bind_compatWith_eqProp_l {A : Type} {B : Type} (m1 m2 : itree E A) (k : A -> itree E B) := bind_compatWith_eqProp_l_eutt k m1 m2
  ; bind_compatWith_eqProp_r {A : Type} {B : Type} (m : itree E A) (k1 k2 : A -> itree E B) := bind_compatWith_eqProp_r_eutt m k1 k2
  ; bind_assoc {A : Type} {B : Type} {C : Type} := bind_assoc_eutt (R1 := A) (R2 := B) (R3 := C)
  ; bind_pure_l {A : Type} {B : Type} := bind_pure_l_eutt (R1 := A) (R2 := B)
  ; bind_pure_r {A : Type} := bind_pure_r_eutt (R := A)
  }.

Lemma monad_iter_unfold_pointwise {I : Type} {R : Type} (step : I -> itree E (I + R)%type) (i : I)
  : is_similar_to (Similarity := @eqit E R R eq true true) (monad_iter step i) (step i >>= B.either (monad_iter step) pure).
Proof with eauto with *.
  assert (STEP1 : is_similar_to (Similarity := @eqit E R R eq true true) (monad_iter step i) (step i >>= (fun res : I + R => match res with inl arg' => Tau (monad_iter step arg') | inr res' => Ret res' end))).
  { eapply observe_eq_observe_implies_eqit... }
  assert (STEP2 : is_similar_to (Similarity := @eqit E R R eq true true) (step i >>= (fun res : I + R => match res with inl arg' => Tau (monad_iter step arg') | inr res' => Ret res' end)) (step i >>= B.either (monad_iter step) pure)).
  { eapply bind_compatWith_eqProp_r_eutt. intros [arg' | r].
    - eapply Tau_eutt_aux.
    - eapply observe_eq_observe_implies_eqit. reflexivity.
  }
  eapply eqit_transitivity; cycle -2...
  intros r1 r2 r3 H1 H2. change (r1 = r2) in H1. change (r2 = r3) in H2. congruence.
Qed.

#[global]
Instance itree_eutt_MonadIterSpec : MonadIterSpec (itree E) (MONAD := itree_isMonad) (MONADITER := itree_isMonadIter) (SETOID1 := eutt) :=
  @monad_iter_unfold_pointwise.

End eqit_prop.

End EQIT.

Infix "≈ₜ" := (EQIT.eqit (R_sim := eqProp) true true).
Infix "≳ₜ" := (EQIT.eqit (R_sim := eqProp) true false).
Infix "≲ₜ" := (EQIT.eqit (R_sim := eqProp) false true).
Infix "≃ₜ" := (EQIT.eqit (R_sim := eqProp) false false).
