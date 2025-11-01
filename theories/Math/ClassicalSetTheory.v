Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Data.Aczel.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Math.SetTheory.

Import TypeTheoreticImplementation.

Definition toSet_wlt (t : Tree) (lhs : toSet t) (rhs : toSet t) : Prop :=
  fromWf (projT2 (toWoSet t)) (toWoSet_well_founded t) lhs <ᵣ fromWf (projT2 (toWoSet t)) (toWoSet_well_founded t) rhs.

#[global] Arguments toSet_wlt t / lhs rhs.

Section ClassicalWoset.

#[local] Infix "\in" := member : type_scope.

Lemma toSet_wlt_Transitive t
  : Transitive (toSet_wlt t).
Proof.
  red. i. eapply (rLt_StrictOrder).(StrictOrder_Transitive); eauto.
Qed.

Lemma toSet_wlt_well_founded t
  : well_founded (toSet_wlt t).
Proof.
  eapply relation_on_image_liftsWellFounded. eapply rLt_wf.
Qed.

#[global]
Instance toSet_isWellPoset (t : Tree) : isWellPoset (toSet t) :=
  { wltProp := toSet_wlt t
  ; wltProp_Transitive := toSet_wlt_Transitive t
  ; wltProp_well_founded := toSet_wlt_well_founded t
  }.

#[global]
Instance toSet_wlt_eqPropCompatible2 t
  : eqPropCompatible2 (toSet_wlt t).
Proof.
  red. ii; simpl in *. unfold toSet_wlt. rewrite x_EQ. rewrite y_EQ. reflexivity.
Qed.

Lemma toSet_wlt_extensional {t : Tree} (x : toSet t) (y : toSet t)
  (EXT_EQ : forall z : toSet t, wltProp z x <-> wltProp z y)
  : x == y.
Proof.
  simpl in *. eapply rEq_ext. intros z. split; intros H_rLt.
  - rewrite <- @fromWf_toWoset_rEq with (t := z) in H_rLt; cycle 1.
    { ii; eapply projT2_eq; eauto. }
    rewrite <- @fromWf_toWoset_rEq with (t := z); cycle 1.
    { ii; eapply projT2_eq; eauto. }
    unfold fromWfSet in *. eapply rLt_rLe_rLt; eauto. clear z H_rLt.
    unfold fromWf in *. destruct (toWoSet_well_founded t x) as [H_ACC_inv], (toWoSet_well_founded t y) as [H_ACC_inv']. unfold toSet in *.
    econs. intros [cz z]. simpl in *. rewrite fromAcc_pirrel with (ACC' := toWoSet_well_founded t cz). rewrite <- EXT_EQ with (z := cz).
    econs. simpl. exists (@exist _ _ cz z). simpl. rewrite fromAcc_pirrel. reflexivity.
  - rewrite <- @fromWf_toWoset_rEq with (t := z) in H_rLt; cycle 1.
    { ii; eapply projT2_eq; eauto. }
    rewrite <- @fromWf_toWoset_rEq with (t := z); cycle 1.
    { ii; eapply projT2_eq; eauto. }
    unfold fromWfSet in *. eapply rLt_rLe_rLt; eauto. clear z H_rLt.
    unfold fromWf in *. destruct (toWoSet_well_founded t x) as [H_ACC_inv], (toWoSet_well_founded t y) as [H_ACC_inv']. unfold toSet in *.
    econs. intros [cz z]. simpl in *. rewrite fromAcc_pirrel with (ACC' := toWoSet_well_founded t cz). rewrite -> EXT_EQ with (z := cz).
    econs. simpl. exists (@exist _ _ cz z). simpl. rewrite fromAcc_pirrel. reflexivity.
Qed.

#[global]
Instance toSet_isWoset (t : Tree) : isWoset (toSet t) :=
  { Woset_isWellPoset := toSet_isWellPoset t
  ; Woset_eqPropCompatible2 := toSet_wlt_eqPropCompatible2 t
  ; Woset_ext_eq := toSet_wlt_extensional
  }.

Corollary toSet_wlt_trichotomous (t : Tree)
  : forall x : toSet t, forall y : toSet t, x == y \/ (x ≺ y \/ y ≺ x).
Proof.
  eapply @O.wlt_trichotomous. exact classic.
Qed.

End ClassicalWoset.

Module __fixedpointtheorem1.

End __fixedpointtheorem1.

Module __wellorderingtheorem1.

Section WELL_ORDERING_THEOREM.

Context {X : Type}.

#[projections(primitive)]
Record pair : Type :=
  { P : X -> Prop
  ; R : X -> X -> Prop
  }.

Variant pair_le (s : pair) (s' : pair) : Prop :=
  | pair_le_intro
    (P_incl : forall a, s.(P) a -> s'.(P) a)
    (R_incl : forall a, forall b, s.(R) a b -> s'.(R) a b)
    (NO_INSERTION : forall a, forall b, forall IN : s.(P) b, s'.(R) a b <-> s.(R) a b).

#[global]
Instance pair_le_Reflexive 
  : Reflexive pair_le.
Proof.
  intros s0. econs; eauto.
Qed.

#[global]
Instance pair_le_Transitive
  : Transitive pair_le.
Proof.
  intros s0 s1 s2 s0_le_s1 s1_le_s2. destruct s0_le_s1, s1_le_s2; simpl in *; destruct s0, s1, s2; simpl in *.
  econs; simpl in *; eauto; i. rewrite <- NO_INSERTION; eauto.
Qed.

#[global]
Instance pair_le_PreOrder : PreOrder pair_le :=
  { PreOrder_Reflexive := pair_le_Reflexive
  ; PreOrder_Transitive := pair_le_Transitive
  }.

Let pair_isSetoid : isSetoid pair :=
  mkSetoidFromPreOrder pair_le_PreOrder.

#[local] Existing Instance pair_isSetoid.

#[local]
Instance pair_isProset : isProset pair :=
  { leProp := pair_le
  ; Proset_isSetoid := pair_isSetoid
  ; leProp_PreOrder := pair_le_PreOrder
  ; leProp_PartialOrder s1 s2 := conj (fun H : pair_le s1 s2 /\ pair_le s2 s1 => H) (fun H : pair_le s1 s2 /\ pair_le s2 s1 => H)
  }.

Definition pair_sup (I : Type) (chain : I -> pair) : pair :=
  {| P x := exists i, P (chain i) x; R x y := exists i, R (chain i) x y; |}.

Lemma pair_sup_isSupremum (I : Type) (chain : I -> pair)
  (H_chain : forall i1 : I, forall i2 : I, pair_le (chain i1) (chain i2) \/ pair_le (chain i2) (chain i1))
  : is_supremum_of (pair_sup I chain) (fun s => exists i : I, s = chain i).
Proof.
  intros u; split.
  - intros [? ? ?]. intros x x_in. destruct x_in as [i ->]. econs; i.
    + eapply P_incl. simpl. exists i; eauto.
    + eapply R_incl. simpl. exists i; eauto.
    + rewrite -> NO_INSERTION; simpl; eauto. split.
      * intros [i' H_R]. pose proof (H_chain i i') as [[? ? ?] | [? ? ?]]; eauto. rewrite <- NO_INSERTION0; eauto.
      * intros H_R. exists i. eauto.
  - intros u_in. do 2 red in u_in. econs; simpl; i; des.
    + hexploit (u_in (chain i)).
      { exists i. reflexivity. }
      intros [? ? ?]; eauto.
    + hexploit (u_in (chain i)).
      { exists i. reflexivity. }
      intros [? ? ?]; eauto.
    + hexploit (u_in (chain i)).
      { exists i. reflexivity. }
      intros [? ? ?]. rewrite -> NO_INSERTION; eauto. split.
      * intros H_R. exists i. eauto.
      * intros [i' H_R]. pose proof (H_chain i i') as [[? ? ?] | [? ? ?]]; eauto. rewrite <- NO_INSERTION0; eauto.
Qed.

Context {SETOID : isSetoid X}.

Variant good (P : X -> Prop) (R : X -> X -> Prop) : Prop :=
  | good_intro
    (SOUND : forall a, forall b, forall LT : R a b, P a /\ P b)
    (COMPLETE : forall a, forall b, forall IN : P a, forall IN' : P b, a == b \/ (R a b \/ R b a))
    (WELL_FOUNDED : well_founded R).

Definition pair_good (s : pair) : Prop :=
  good s.(P) s.(R).

Lemma pair_sup_good (I : Type) (chain : I -> pair)
  (chain_good : forall i, pair_good (chain i))
  (H_chain : forall i1, forall i2, pair_le (chain i1) (chain i2) \/ pair_le (chain i2) (chain i1))
  : pair_good (pair_sup I chain).
Proof.
  split.
  - intros a b [i H_R]. pose proof (chain_good i) as [? ? ?]. pose proof (SOUND a b H_R). split; exists i; tauto.
  - intros a b [i1 H_P1] [i2 H_P2]. pose proof (H_chain i1 i2) as [[? ? ?] | [? ? ?]].
    + pose proof (chain_good i2) as [? ? ?]. hexploit (COMPLETE _ _ (P_incl _ H_P1) H_P2); eauto.
      intros [? | [? | ?]]; [left; tauto | right | right]; [left | right]; exists i2; tauto.
    + pose proof (chain_good i1) as [? ? ?]. hexploit (COMPLETE _ _ H_P1 (P_incl _ H_P2)); eauto.
      intros [? | [? | ?]]; [left; tauto | right | right]; [left | right]; exists i1; tauto.
  - intros x1. econs. intros x0 [i H_R]. pose proof (chain_good i) as [? ? ?].
    assert (H_Acc : Acc (chain i).(R) x0) by eauto.
    pose proof (SOUND _ _ H_R) as [H_P _]. revert H_P. clear H_R. induction H_Acc as [x0 _ IH]; intros; econs; intros y [i' H_R'].
    assert (LT : (chain i).(R) y x0).
    { pose proof (H_chain i i') as [[? ? ?] | [? ? ?]]; eauto. rewrite <- NO_INSERTION; eauto. }
    eapply IH; eauto. pose proof (SOUND _ _ LT) as [? ?]; tauto.
Qed.

Section NEXT.

Variable next : pair -> pair.

Hypothesis next_extensive : forall s : pair, s =< next s.

Hypothesis next_good : forall s : pair, pair_good s -> pair_good (next s).

Hypothesis next_exhausted : forall s : pair, (forall x : X, s.(P) x) \/ (exists x : X, (next s).(P) x /\ ~ s.(P) x).

End NEXT.

End WELL_ORDERING_THEOREM.

End __wellorderingtheorem1. 
