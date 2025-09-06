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
  (EXT_EQ : forall z, wltProp z x <-> wltProp z y)
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

End ClassicalWoset.
