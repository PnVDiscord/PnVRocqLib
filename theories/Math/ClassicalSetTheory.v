Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Data.Aczel.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Math.SetTheory.

Import TypeTheoreticImplementation.

Section ClassicalWoset.

#[local] Infix "\in" := member : type_scope.
#[local] Infix "\subseteq" := isSubsetOf : type_scope.

Lemma fromWf_rLt_fromWf_iff {A : Type} {SETOID : isSetoid A} {WOSET : isWoset A} (x : A) (x' : A) 
  : @fromWf A wltProp wltProp_well_founded x <ᵣ @fromWf A wltProp wltProp_well_founded x' <-> @fromWf A wltProp wltProp_well_founded x \in @fromWf A wltProp wltProp_well_founded x'.
Proof.
  split.
  - intros H_rLt. eapply fromAcc_member_fromAcc_intro. change (x ≺ x').
    pose proof (O.wlt_trichotomous (classic := classic) x x') as [H_eq | [H_lt | H_gt]].
    + destruct H_rLt as [[c H_rLe]]. unfold fromWf in *. destruct (wltProp_well_founded x) as [Acc_inv], (wltProp_well_founded x') as [Acc_inv']; simpl in *.
      destruct c as [y H_LT]; simpl in *. change (y ≺ x') in H_LT. pose proof (COPY := H_LT). rewrite <- H_eq in COPY.
      destruct H_rLe; simpl in *. contradiction (rLt_StrictOrder.(StrictOrder_Irreflexive) (fromAcc y (wltProp_well_founded y))).
      pose proof (H_rLt (@exist _ _ y COPY)) as claim1. simpl in claim1.
      erewrite -> fromAcc_pirrel with (ACC := Acc_inv y COPY) (ACC' := wltProp_well_founded y) in claim1.
      erewrite -> fromAcc_pirrel with (ACC := Acc_inv' y H_LT) (ACC' := wltProp_well_founded y) in claim1.
      exact claim1.
    + exact H_lt.
    + destruct H_rLt as [[c H_rLe]]. unfold fromWf in *. destruct (wltProp_well_founded x) as [Acc_inv], (wltProp_well_founded x') as [Acc_inv']; simpl in *.
      destruct c as [y H_LT]; simpl in *. change (y ≺ x') in H_LT. pose proof (COPY := StrictOrder_Transitive (R := wltProp) y x' x H_LT H_gt). change (y ≺ x) in COPY.
      destruct H_rLe; simpl in *. contradiction (rLt_StrictOrder.(StrictOrder_Irreflexive) (fromAcc y (wltProp_well_founded y))).
      pose proof (H_rLt (@exist _ _ y COPY)) as claim1. simpl in claim1.
      erewrite -> fromAcc_pirrel with (ACC := Acc_inv y COPY) (ACC' := wltProp_well_founded y) in claim1.
      erewrite -> fromAcc_pirrel with (ACC := Acc_inv' y H_LT) (ACC' := wltProp_well_founded y) in claim1.
      exact claim1.
  - intros H_in. eapply member_implies_rLt. exact H_in.
Qed.

Lemma fromWf_in_fromWf_iff {A : Type} {SETOID : isSetoid A} {WOSET : isWoset A} (x : A) (x' : A)
  : @fromWf A wltProp wltProp_well_founded x \in @fromWf A wltProp wltProp_well_founded x' <-> x ≺ x'.
Proof.
  split.
  - unfold fromWf. rewrite fromAcc_unfold. intros [[y H_LT] H_eqTree]; simpl in H_eqTree. change (y ≺ x') in H_LT.
    pose proof (O.wlt_trichotomous (classic := classic) x x') as [H_eq | [H_lt | H_gt]].
    + pose proof (COPY := H_LT). rewrite <- H_eq in COPY.
      assert (H_IN : @fromWf A wltProp wltProp_well_founded y \in @fromWf A wltProp wltProp_well_founded x).
      { unfold fromWf. rewrite fromAcc_unfold. exists (@exist _ _ y COPY). simpl. eapply fromAcc_pirrel. }
      change ((fromAcc x (wltProp_well_founded x)) == (fromAcc y (Acc_inv (wltProp_well_founded x') H_LT))) in H_eqTree.
      rewrite H_eqTree in H_IN. contradiction (rLt_StrictOrder.(StrictOrder_Irreflexive) (fromWf wltProp wltProp_well_founded y)).
      eapply member_implies_rLt. rewrite fromAcc_pirrel in H_IN. exact H_IN.
    + exact H_lt.
    + pose proof (COPY := StrictOrder_Transitive (R := wltProp) y x' x H_LT H_gt).
      assert (H_IN : @fromWf A wltProp wltProp_well_founded y \in @fromWf A wltProp wltProp_well_founded x).
      { unfold fromWf. rewrite fromAcc_unfold. exists (@exist _ _ y COPY). simpl. eapply fromAcc_pirrel. }
      change ((fromAcc x (wltProp_well_founded x)) == (fromAcc y (Acc_inv (wltProp_well_founded x') H_LT))) in H_eqTree.
      rewrite H_eqTree in H_IN. contradiction (rLt_StrictOrder.(StrictOrder_Irreflexive) (fromWf wltProp wltProp_well_founded y)).
      eapply member_implies_rLt. rewrite fromAcc_pirrel in H_IN. exact H_IN.
  - intros H_LT. unfold fromWf. rewrite fromAcc_unfold. exists (@exist _ _ x H_LT). simpl. eapply fromAcc_pirrel.
Qed.

Lemma fromWf_wlt_rLt_fromWf_wlt_iff {X : Type} {SETOID : isSetoid X} {WOSET : isWoset X} (x : X) (x' : X)
  : @fromWf X wltProp wltProp_well_founded x <ᵣ @fromWf X wltProp wltProp_well_founded x' <-> x ≺ x'.
Proof.
  simpl. rewrite fromWf_rLt_fromWf_iff. rewrite fromWf_in_fromWf_iff. reflexivity.
Qed.

Lemma fromWf_wlt_rEq_fromWf_wlt_iff {X : Type} {SETOID : isSetoid X} {WOSET : isWoset X} (x : X) (x' : X)
  : @fromWf X wltProp wltProp_well_founded x =ᵣ @fromWf X wltProp wltProp_well_founded x' <-> x == x'.
Proof.
  simpl in x, x' |- *. split; intros H_EQ.
  - pose proof (O.wlt_trichotomous (classic := classic) x x') as [H_eq | [H_lt | H_gt]].
    + exact H_eq.
    + rewrite <- fromWf_wlt_rLt_fromWf_wlt_iff with (x := x) (x' := x') in H_lt. simpl in H_lt.
      rewrite H_EQ in H_lt. contradiction (rLt_StrictOrder.(StrictOrder_Irreflexive) (fromWf wltProp wltProp_well_founded x')).
    + rewrite <- fromWf_wlt_rLt_fromWf_wlt_iff with (x := x') (x' := x) in H_gt. simpl in H_gt.
      rewrite H_EQ in H_gt. contradiction (rLt_StrictOrder.(StrictOrder_Irreflexive) (fromWf wltProp wltProp_well_founded x')).
  - pose proof (O.wlt_trichotomous (classic := classic) (WOSET := rLt_isWellOrdering) (fromWf wltProp wltProp_well_founded x) (fromWf wltProp wltProp_well_founded x')) as [H_eq | [H_lt | H_gt]].
    + exact H_eq.
    + rewrite -> fromWf_wlt_rLt_fromWf_wlt_iff with (x := x) (x' := x') in H_lt. simpl in H_lt. rewrite H_EQ in H_lt. contradiction (StrictOrder_Irreflexive x').
    + rewrite -> fromWf_wlt_rLt_fromWf_wlt_iff with (x := x') (x' := x) in H_gt. simpl in H_gt. rewrite H_EQ in H_gt. contradiction (StrictOrder_Irreflexive x').
Qed.

Lemma fromWf_wlt_rLe_fromWf_wlt_iff {X : Type} {SETOID : isSetoid X} {WOSET : isWoset X} (x : X) (x' : X)
  : @fromWf X wltProp wltProp_well_founded x ≦ᵣ @fromWf X wltProp wltProp_well_founded x' <-> (x ≺ x' \/ x == x').
Proof.
  simpl in x, x' |- *. split; intros H_LE.
  - pose proof (O.wlt_trichotomous (classic := classic) x x') as [H_eq | [H_lt | H_gt]].
    + right. exact H_eq.
    + left. exact H_lt.
    + rewrite <- fromWf_wlt_rLt_fromWf_wlt_iff with (x := x') (x' := x) in H_gt. simpl in H_gt.
      contradiction (rLt_StrictOrder.(StrictOrder_Irreflexive) (fromWf wltProp wltProp_well_founded x')). eapply rLt_rLe_rLt; eauto.
  - pose proof (O.wlt_trichotomous (classic := classic) (WOSET := rLt_isWellOrdering) (fromWf wltProp wltProp_well_founded x) (fromWf wltProp wltProp_well_founded x')) as [H | [H | H]].
    + do 3 red in H. exact (proj1 H).
    + do 2 red in H. eapply rLt_implies_rLe. exact H.
    + do 2 red in H. destruct H_LE as [H_LT | H_EQ].
      * contradiction (rLt_StrictOrder.(StrictOrder_Irreflexive) (fromWf wltProp wltProp_well_founded x')). transitivity (fromWf wltProp wltProp_well_founded x); eauto.
        rewrite <- fromWf_wlt_rLt_fromWf_wlt_iff with (x := x) (x' := x') in H_LT. exact H_LT.
      * contradiction (rLt_StrictOrder.(StrictOrder_Irreflexive) (fromWf wltProp wltProp_well_founded x')).
        rewrite <- fromWf_wlt_rEq_fromWf_wlt_iff with (x := x) (x' := x') in H_EQ. rewrite -> H_EQ in H. exact H.
Qed.

Lemma fromWf_subseteq_fromWf_iff {A : Type} {SETOID : isSetoid A} {WOSET : isWoset A} (x : A) (x' : A)
  : @fromWf A wltProp wltProp_well_founded x \subseteq @fromWf A wltProp wltProp_well_founded x' <-> (~ @fromWf A wltProp wltProp_well_founded x' \in @fromWf A wltProp wltProp_well_founded x).
Proof.
  split.
  - intros H_subseteq H_in. apply subseteq_implies_rLe in H_subseteq. rewrite <- fromWf_rLt_fromWf_iff in H_in.
    contradiction (rLt_StrictOrder.(StrictOrder_Irreflexive) (fromWf wltProp wltProp_well_founded x')). eapply rLt_rLe_rLt; eauto.
  - intros H_notin z z_in. eapply NNPP. intros H_contra. contradiction H_notin. unfold fromWf in z_in. rewrite fromAcc_unfold in z_in. destruct z_in as [[y R_y_x] z_eq]. simpl proj1_sig in z_eq.
    rewrite z_eq in H_contra. clear z z_eq. rewrite fromAcc_pirrel with (ACC := Acc_inv (wltProp_well_founded x) (proj2_sig (exist (fun y : A => y ⪵ x) y R_y_x))) (ACC' := wltProp_well_founded y) in H_contra.
    change (~ fromWf wltProp wltProp_well_founded y \in fromWf wltProp wltProp_well_founded x') in H_contra. rewrite fromWf_in_fromWf_iff in H_contra.
    change (y ≺ x) in R_y_x. pose proof (O.wlt_trichotomous (classic := classic) x x') as [H | [H | H]].
    + rewrite H in R_y_x. contradiction.
    + contradiction H_contra. red. transitivity x; [exact R_y_x | exact H].
    + eapply fromAcc_member_fromAcc_intro. exact H.
Qed.

Lemma fromWf_rLe_fromWf_iff {A : Type} {SETOID : isSetoid A} {WOSET : isWoset A} (x : A) (x' : A)
  : @fromWf A wltProp wltProp_well_founded x ≦ᵣ @fromWf A wltProp wltProp_well_founded x' <-> @fromWf A wltProp wltProp_well_founded x \subseteq @fromWf A wltProp wltProp_well_founded x'.
Proof.
  rewrite -> fromWf_subseteq_fromWf_iff. rewrite <- fromWf_rLt_fromWf_iff. split.
  - intros H_rLe H_rLt. contradiction (rLt_StrictOrder.(StrictOrder_Irreflexive) (fromWf wltProp wltProp_well_founded x')). eapply rLt_rLe_rLt; eauto.
  - intros H_not_rLt. pose proof (O.wlt_trichotomous (classic := classic) (WOSET := rLt_isWellOrdering) (fromWf wltProp wltProp_well_founded x) (fromWf wltProp wltProp_well_founded x')) as [H | [H | H]].
    + do 3 red in H. tauto.
    + do 2 red in H. eapply rLt_implies_rLe. tauto.
    + tauto.
Qed.

Lemma fromWf_rEq_fromWf_iff {A : Type} {SETOID : isSetoid A} {WOSET : isWoset A} (x : A) (x' : A)
  : @fromWf A wltProp wltProp_well_founded x =ᵣ @fromWf A wltProp wltProp_well_founded x' <-> @fromWf A wltProp wltProp_well_founded x == @fromWf A wltProp wltProp_well_founded x'.
Proof.
  split.
  - intros [H_rLe1 H_rLe2]. eapply extensionality. intros z; split; revert z.
    + change (fromWf wltProp wltProp_well_founded x \subseteq fromWf wltProp wltProp_well_founded x'). now rewrite <- fromWf_rLe_fromWf_iff.
    + change (fromWf wltProp wltProp_well_founded x' \subseteq fromWf wltProp wltProp_well_founded x). now rewrite <- fromWf_rLe_fromWf_iff.
  - intros H_EQ. rewrite H_EQ. reflexivity. 
Qed.

Theorem fromWfSet_isOrdinal {A : Type@{Set_u}} {SETOID : isSetoid A} {WOSET : isWoset A}
  : isOrdinal (@fromWfSet A wltProp wltProp_well_founded).
Proof.
  econs.
  - intros y [cy y_eq] z. simpl in cy. rewrite y_eq. clear y y_eq. simpl. intros z_in.
    rewrite fromWf_unfold in z_in. destruct z_in as (c & H_LT & z_eq). rewrite z_eq.
    clear z z_eq. change (c ≺ cy) in H_LT. exists c. simpl. reflexivity.
  - intros beta [c beta_eq] y. simpl in c. intros y_in z z_in. rewrite -> beta_eq in y_in |- *. simpl in y_in |- *.
    clear beta beta_eq. rewrite fromWf_unfold in y_in. destruct y_in as (cy & H_LT1 & y_eq). rewrite y_eq in z_in.
    rewrite fromWf_unfold in z_in. destruct z_in as (cz & H_LT2 & z_eq). rewrite z_eq.
    rewrite -> fromWf_in_fromWf_iff. red; transitivity cy; eauto.
Qed.

Definition fromOrderType (A : Type@{Set_u}) {SETOID : isSetoid A} {WOSET : isWoset A} : A -> Tree :=
  @fromWf A wlt wltProp_well_founded.

Lemma fromOrderType_in_fromOrderType_iff {A : Type@{Set_u}} {SETOID : isSetoid A} {WOSET : isWoset A} (x : A) (y : A)
  : fromOrderType A x \in fromOrderType A y <-> x ≺ y.
Proof.
  now rewrite <- fromWf_in_fromWf_iff.
Qed.

Lemma fromOrderType_subseteq_fromOrderType_iff {A : Type@{Set_u}} {SETOID : isSetoid A} {WOSET : isWoset A} (x : A) (y : A)
  : fromOrderType A x \subseteq fromOrderType A y <-> x ≼ y.
Proof.
  unfold O.wle. rewrite <- fromWf_wlt_rLe_fromWf_wlt_iff. now rewrite -> fromWf_rLe_fromWf_iff.
Qed.

Lemma fromOrderType_eq_fromOrderType_iff {A : Type@{Set_u}} {SETOID : isSetoid A} {WOSET : isWoset A} (x : A) (y : A)
  : fromOrderType A x == fromOrderType A y <-> x == y.
Proof.
  rewrite <- fromWf_wlt_rEq_fromWf_wlt_iff. now rewrite -> fromWf_rEq_fromWf_iff.
Qed.

Definition FromOrderType (A : Type@{Set_u}) {SETOID : isSetoid A} {WOSET : isWoset A} : Tree :=
  @fromWfSet A wlt wltProp_well_founded.

Lemma FromOrderType_isOrdinal {A : Type@{Set_u}} {SETOID : isSetoid A} {WOSET : isWoset A}
  : isOrdinal (FromOrderType A).
Proof.
  exact (@fromWfSet_isOrdinal A SETOID WOSET).
Qed.

Theorem FromOrderType_spec {A : Type@{Set_u}} {SETOID : isSetoid A} {WOSET : isWoset A}
  : forall z : Tree, z \in FromOrderType A <-> (exists x : A, z == fromOrderType A x).
Proof.
  now i.
Qed.

End ClassicalWoset.

Module InducedOrdinal.

Section THEORY_ON_RANK.

#[local] Infix "\in" := member : type_scope.

#[local] Existing Instance rEq_asSetoid.

#[local]
Instance Tree_rLt_isWellPoset : isWellPoset Tree :=
  { wltProp := rLt
  ; wltProp_Transitive := rLt_StrictOrder.(StrictOrder_Transitive)
  ; wltProp_well_founded := rLt_wf
  }.

#[local]
Instance Tree_rLt_isWoset : isWoset Tree (SETOID := rEq_asSetoid) :=
  { Woset_isWellPoset := Tree_rLt_isWellPoset
  ; Woset_eqPropCompatible2 := rLt_eqPropCompatible2
  ; Woset_ext_eq := rEq_ext
  }.

Lemma rank_trichotomy (lhs : Tree) (rhs : Tree)
  : lhs =ᵣ rhs \/ (lhs <ᵣ rhs \/ rhs <ᵣ lhs).
Proof.
  change (lhs == rhs \/ lhs ≺ rhs \/ rhs ≺ lhs).
  eapply @O.wlt_trichotomous. exact classic.
Qed.

Lemma rLe_or_rGt (lhs : Tree) (rhs : Tree)
  : lhs ≦ᵣ rhs \/ rhs <ᵣ lhs.
Proof.
  pose proof (rank_trichotomy lhs rhs) as [H | [H | H]]; try tauto; left.
  - now rewrite H.
  - now eapply rLt_implies_rLe.
Qed.

Lemma rLt_iff_not_rGe (lhs : Tree) (rhs : Tree)
  : lhs <ᵣ rhs <-> ~ rhs ≦ᵣ lhs.
Proof.
  split.
  - intros H_rLt H_rLe. contradiction (rLt_StrictOrder.(StrictOrder_Irreflexive) lhs).
    eapply rLt_rLe_rLt; eauto.
  - pose proof (rLe_or_rGt rhs lhs); tauto.
Qed.

Lemma rLe_total (lhs : Tree) (rhs : Tree)
  : lhs ≦ᵣ rhs \/ rhs ≦ᵣ lhs.
Proof.
  pose proof (rLe_or_rGt lhs rhs) as [H | H]; try tauto; right.
  now eapply rLt_implies_rLe.
Qed.

Lemma rLe_iff_rLt_or_rEq (lhs : Tree) (rhs : Tree)
  : lhs ≦ᵣ rhs <-> (lhs <ᵣ rhs \/ lhs =ᵣ rhs).
Proof.
  split.
  - intros H_rLe. pose proof (rank_trichotomy lhs rhs) as [H | [H | H]]; try tauto.
    contradiction (rLt_StrictOrder.(StrictOrder_Irreflexive) rhs). eapply rLt_rLe_rLt; eauto.
  - intros [H | H].
    + eapply rLt_implies_rLe; eauto.
    + exact (proj1 H).
Qed.

Fixpoint fromAcc_complete (A : Type) (R : A -> A -> Prop) (x : A) (H_Acc : Acc R x) (o : Tree) (LT : o <ᵣ @fromAcc A R x H_Acc) {struct H_Acc} : exists x' : A, exists H_Acc' : Acc R x', o =ᵣ @fromAcc A R x' H_Acc'.
Proof.
  destruct H_Acc as [H_ACC_inv]; simpl in *. destruct LT as [[[c R_c_x] LE]]; simpl in *.
  rewrite rLe_iff_rLt_or_rEq in LE. destruct LE as [LT | EQ].
  - eapply fromAcc_complete. exact LT.
  - exists c. exists (H_ACC_inv c R_c_x). exact EQ.
Qed.

Fixpoint fromAcc_complete1 (A : Type) (R : A -> A -> Prop) (R_trans : Transitive R) (x : A) (H_Acc : Acc R x) (o : Tree) (LT : o <ᵣ @fromAcc A R x H_Acc) {struct H_Acc} : exists x' : A, exists H_Acc' : Acc R x', o =ᵣ @fromAcc A R x' H_Acc' /\ R x' x.
Proof.
  destruct H_Acc as [H_ACC_inv]; simpl in *. destruct LT as [[[c R_c_x] LE]]; simpl in *.
  rewrite rLe_iff_rLt_or_rEq in LE. destruct LE as [LT | EQ].
  - pose proof (fromAcc_complete1 A R R_trans _ (H_ACC_inv c R_c_x) o LT) as (x' & H_Acc' & H_EQ & R_c_x').
    exists x'. exists H_Acc'. split; [exact H_EQ | now transitivity c].
  - exists c. exists (H_ACC_inv c R_c_x). split; [exact EQ | exact R_c_x].
Qed.

Lemma fromWf_complete {A : Type} (R : A -> A -> Prop) (R_wf : well_founded R) (x : A) (o : Tree)
  (LT : o <ᵣ @fromWf A R R_wf x)
  : exists x' : A, o =ᵣ @fromWf A R R_wf x'.
Proof.
  unfold fromWf in *. apply fromAcc_complete in LT. des.
  exists x'. rewrite fromAcc_pirrel. exact LT.
Qed.

Lemma fromWf_complete1 (A : Type) (R : A -> A -> Prop) (R_wf : well_founded R) (R_trans : Transitive R) (x : A) (o : Tree)
  (LT : o <ᵣ @fromWf A R R_wf x)
  : exists x' : A, o =ᵣ @fromWf A R R_wf x' /\ R x' x.
Proof.
  unfold fromWf in *. apply fromAcc_complete1 in LT; trivial. des.
  exists x'. split; trivial. rewrite fromAcc_pirrel. exact LT.
Qed.

Lemma fromWfSet_complete {A : Type} (R : A -> A -> Prop) (R_wf : well_founded R) (o : Tree)
  (LT : o <ᵣ @fromWfSet A R R_wf)
  : exists x' : A, o =ᵣ @fromWf A R R_wf x'.
Proof.
  unfold fromWfSet in LT. destruct LT as [[c LE]]; simpl in *.
  rewrite rLe_iff_rLt_or_rEq in LE. destruct LE as [LT | EQ].
  - eapply fromWf_complete. exact LT.
  - exists c. eauto.
Qed.

Lemma fromWfSet_lt {A : Type} {R : A -> A -> Prop} {R' : A -> A -> Prop}
  (INCL : forall x : A, forall x' : A, forall LE : R x x', R' x x')
  (WF : well_founded R)
  (WF' : well_founded R')
  (TOP : exists top : A, (exists x, R' x top) /\ (forall x, forall x', R x x' -> R' x' top))
  : @fromWfSet A R WF <ᵣ @fromWfSet A R' WF'.
Proof.
  des. econs. exists top. simpl. unfold fromWf. destruct (WF' top) as [H_ACC_inv]; simpl. econs. intros x'.
  pose proof (classic (exists x0, R x0 x')) as [YES | NO].
  - des. econs. exists (@exist _ _ x' (TOP0 _ _ YES)). simpl in *. unfold fromWf. eapply fromAcc_isMonotonic; eauto.
  - econs. simpl. exists (@exist _ _ x TOP). simpl. unfold fromWfSet in x'. simpl in x'. unfold fromWf.
    destruct (WF x'), (H_ACC_inv x TOP); econs; simpl. intros [c R_c_x']. contradiction NO. now exists c.
Qed.

Variant is_minimum_of (P : Tree -> Prop) (o : Tree) : Prop :=
  | is_minimum_of_intro
    (IN : P o)
    (MIN : forall o' : Tree, forall IN : P o', o ≦ᵣ o').

Lemma minimum_exists (P : Tree -> Prop)
  (INHABITED : exists o, P o)
  : exists o', is_minimum_of P o'.
Proof.
  pose proof (O.minimisation_lemma (classic := classic) P INHABITED) as (o' & IN & MIN); unnw.
  exists o'. econs; eauto. intros o1 o1_in. rewrite rLe_iff_rLt_or_rEq. now eapply MIN.
Qed.

Definition is_open (alpha : Tree) : Prop :=
  forall c1 : children alpha, exists c2 : children alpha, childnodes alpha c1 <ᵣ childnodes alpha c2.

Lemma limit_or_succ (alpha : Tree)
  : ⟪ LIMIT : (alpha =ᵣ unions alpha) /\ (is_open alpha) ⟫ \/ ⟪ SUCC : (exists beta : Tree, alpha =ᵣ succ beta) /\ (~ is_open alpha) ⟫.
Proof.
  unnw. unfold is_open. destruct alpha as [cs ts]; simpl. pose proof (classic (forall c, exists c', ts c <ᵣ ts c')) as [YES | NO].
  - left. split; eauto. split.
    + econs. simpl; i. econs. simpl. pose proof (YES c) as [c' [[t H_rLe]]].
      exists (@existT cs (fun i => children (ts i)) c' t). exact H_rLe.
    + econs. simpl; i. econs. simpl. exists (projT1 c). eapply rLt_implies_rLe. econs. now exists (projT2 c).
  - right. split; eauto.
    assert (exists c : cs, forall c' : cs, ~ ts c <ᵣ ts c') as [c H_c].
    { eapply NNPP. intros H_contra. contradiction NO. intros c.
      eapply NNPP. intros H. contradiction H_contra. exists c. intros c' YES. contradiction H. eauto.
    }
    exists (ts c). rewrite rEq_succ_iff. intros z. split.
    + intros [[c' H_rLe]]. simpl in *. pose proof (classic (ts c' ≦ᵣ ts c)) as [H | H].
      * transitivity (ts c'); eauto.
      * pose proof (H_c c') as H'. pose proof (rLe_or_rGt (ts c') (ts c)); tauto.
    + intros H_rLe. econs. simpl. now exists c.
Qed.

Theorem transfinite_induction (P : Tree -> Prop)
  (P_zero : forall o, forall ZERO : o =ᵣ empty, P o)
  (P_succ : forall o, forall alpha : Tree, ⟪ IH : P alpha ⟫ -> forall SUCC : o =ᵣ succ alpha, P o)
  (P_lim' : forall o, forall I : Type, ⟪ INHABITED : inhabited I ⟫ -> forall alpha : I -> Tree, ⟪ IH : forall i, P (alpha i) ⟫ -> forall LIMIT : o =ᵣ @indexed_union I alpha, ⟪ OPEN : forall i1 : I, exists i2 : I, alpha i1 <ᵣ alpha i2 ⟫ -> P o)
  : forall o : Tree, P o.
Proof.
  intros o. pose proof (rLt_wf o) as H_Acc. induction H_Acc as [o _ IH]. pose proof (limit_or_succ o) as [[LIMIT OPEN] | [SUCC _]]; unnw.
  - pose proof (classic (inhabited (children o))) as [YES | NO].
    + eapply P_lim' with (I := children o); eauto. intros i. eapply IH. econs. now exists i.
    + eapply P_zero. split.
      * econs. intros i. contradiction NO. econs. exact i.
      * econs. simpl. intros [].
  - destruct SUCC as [beta SUCC]. eapply P_succ; eauto. eapply IH. rewrite rEq_succ_iff in SUCC. now rewrite -> SUCC.
Qed.

Section BOURBAKI_WITT_FIXEDPOINT_THEOREM.

Context {D : Type}.

Variable good : D -> Prop.
Variable dle : D -> D -> Prop.

#[local] Infix "⊑" := dle.

Hypothesis dle_refl : forall d1 : D, forall GOOD1 : good d1, d1 ⊑ d1.
Hypothesis dle_trans : forall d1 : D, forall d2 : D, forall d3 : D, forall GOOD1 : good d1, forall GOOD2 : good d2, forall GOOD3 : good d3, forall LE : d1 ⊑ d2, forall LE' : d2 ⊑ d3, d1 ⊑ d3.

Lemma dle_unfold (d1 : D) (d2 : D)
  (GOOD1 : good d1)
  (GOOD2 : good d2)
  : d1 ⊑ d2 <-> (forall d : D, forall GOOD : good d, d ⊑ d1 -> d ⊑ d2).
Proof.
  split; ii; eauto.
Qed.

Let deq (lhs : D) (rhs : D) : Prop :=
  lhs ⊑ rhs /\ rhs ⊑ lhs.
#[local] Infix "≡" := deq.
#[local] Hint Unfold deq : core.

Lemma deq_refl d1
  (GOOD1 : good d1)
  : d1 ≡ d1.
Proof.
  split; eauto.
Qed.

Lemma deq_sym d1 d2
  (EQ : d1 ≡ d2)
  : d2 ≡ d1.
Proof.
  unfold deq in *; tauto.
Qed.

Lemma deq_trans d1 d2 d3
  (GOOD1 : good d1)
  (GOOD2 : good d2)
  (GOOD3 : good d3)
  (EQ : d1 ≡ d2)
  (EQ' : d2 ≡ d3)
  : d1 ≡ d3.
Proof.
  red in EQ, EQ'; split; eapply dle_trans with (d2 := d2); eauto; tauto.
Qed.

Variable djoin : forall I : Type, (I -> D) -> D.
Hypothesis djoin_good : forall I : Type, forall ds : I -> D, forall CHAIN : forall i1, forall i2, ds i1 ⊑ ds i2 \/ ds i2 ⊑ ds i1, forall GOODs : forall i, good (ds i), good (djoin I ds).
Hypothesis djoin_supremum : forall I : Type, forall ds : I -> D, forall CHAIN : forall i1, forall i2, ds i1 ⊑ ds i2 \/ ds i2 ⊑ ds i1, forall GOODs : forall i, good (ds i), forall d : D, forall GOOD : good d, djoin I ds ⊑ d <-> (forall i, ds i ⊑ d).

Lemma djoin_upperbound (I : Type) (ds : I -> D)
  (CHAIN : forall i1, forall i2, ds i1 ⊑ ds i2 \/ ds i2 ⊑ ds i1)
  (GOODs : forall i, good (ds i))
  : forall i : I, ds i ⊑ djoin I ds.
Proof.
  i. eapply djoin_supremum; eauto.
Qed.

Variable dbase : D.
Hypothesis dbase_good : good dbase.

Variable next : D -> D.
Hypothesis next_good : forall d : D, forall GOOD : good d, good (next d).
Hypothesis next_extensive : forall d : D, forall GOOD : good d, d ⊑ next d.
Hypothesis next_congruence : forall d : D, forall d' : D, forall GOOD : good d, forall GOOD' : good d', forall EQ : d ≡ d', next d ≡ next d'.

Let rec : Tree -> D :=
  Ord.rec dbase next djoin.

Let rLe_Reflexive (o : Tree) : o ≦ᵣ o :=
  PreOrder_Reflexive o.

Let trivial_rLt (cs : Type) (ts : cs -> Tree) (c : cs) : ts c <ᵣ mkNode cs ts :=
  rLt_intro (ts c) (mkNode cs ts) (@ex_intro _ _ c (rLe_Reflexive (ts c))).

#[local] Hint Resolve rLe_Reflexive trivial_rLt : core.

Theorem rec_spec (o : Tree)
  : ⟪ mono_rec : forall o', o' ≦ᵣ o -> rec o' ⊑ rec o ⟫ /\ ⟪ base_rec : dbase ⊑ rec o ⟫ /\ ⟪ next_rec : forall o', o' <ᵣ o -> next (rec o') ⊑ rec o ⟫ /\ ⟪ good_rec : good (rec o) ⟫.
Proof.
  rename o into t. pose proof (rLt_wf t) as H_Acc. induction H_Acc as [t _ IH]. destruct t as [cs ts]; simpl.
  assert (H_chain : forall cs' : Type, forall ts' : cs' -> Tree, forall LE : forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c, forall c1 : cs', forall c2 : cs', next (rec (ts' c1)) ⊑ next (rec (ts' c2)) \/ next (rec (ts' c2)) ⊑ next (rec (ts' c1))).
  { ii.
    assert (ts' c1 <ᵣ mkNode cs ts /\ ts' c2 <ᵣ mkNode cs ts) as [helper1 helper2].
    { split; econs; eapply LE. }
    pose proof (rank_trichotomy (ts' c1) (ts' c2)) as [EQ | [LT | GT]].
    - hexploit (next_congruence (rec (ts' c1)) (rec (ts' c2))).
      + eapply IH; eauto.
      + eapply IH; eauto.
      + destruct EQ as [LE1 LE2]. split; eapply IH; eauto.
      + intros H_deq. left. exact (proj1 H_deq).
    - left. eapply dle_trans with (d2 := rec (ts' c2)); eauto.
      + eapply next_good. eapply IH; eauto.
      + eapply IH; eauto.
      + eapply next_good. eapply IH; eauto.
      + eapply IH; eauto.
      + eapply next_extensive. eapply IH; eauto.
    - right. eapply dle_trans with (d2 := rec (ts' c1)); eauto.
      + eapply next_good. eapply IH; eauto.
      + eapply IH; eauto.
      + eapply next_good. eapply IH; eauto.
      + eapply IH; eauto.
      + eapply next_extensive. eapply IH; eauto.
  }
  assert (H_next_good : forall cs' : Type, forall ts' : cs' -> Tree, forall LE : forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c, forall c' : cs', good (next (rec (ts' c')))).
  { ii. eapply next_good. eapply IH; eauto. econs. eapply LE. }
  set (fun cs' : Type => fun ts' : cs' -> Tree => fun b : bool => if b then dbase else djoin cs' (fun c' => next (rec (ts' c')))) as f.
  assert (claim1 : forall b1 : bool, forall b2 : bool, forall cs' : Type, forall ts' : cs' -> Tree, forall LE : forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c, f cs' ts' b1 ⊑ f cs' ts' b2 \/ f cs' ts' b2 ⊑ f cs' ts' b1).
  { ii.
    assert (helper1 : forall c' : cs', ts' c' <ᵣ mkNode cs ts).
    { i; econs; eapply LE. }
    assert (helper2 : dbase ⊑ djoin cs' (fun c' : cs' => next (rec (ts' c'))) \/ djoin cs' (fun c' : cs' => next (rec (ts' c'))) ⊑ dbase).
    { pose proof (classic (inhabited cs')) as [YES | NO].
      - destruct YES as [c']. left. eapply dle_trans with (d2 := next (rec (ts' c'))); eauto.
        + eapply dle_trans with (d2 := rec (ts' c')); eauto.
          * eapply IH; eauto.
          * eapply IH; eauto.
          * eapply next_extensive. eapply IH; eauto.
        + eapply djoin_upperbound with (ds := fun c' : cs' => next (rec (ts' c'))); eauto.
      - right. eapply djoin_supremum; eauto. intros c'. contradiction NO. econs. exact c'.
    }
    destruct b1, b2; simpl in *; eauto; [tauto | left; eapply dle_refl]. eapply djoin_good; eauto.
  }
  assert (claim2 : forall b : bool, forall cs' : Type, forall ts' : cs' -> Tree, forall LE : forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c, good (f cs' ts' b)).
  { ii. destruct b; eauto. }
  set (djoin bool (f cs ts)) as x.
  assert (claim3 : good x).
  { eapply djoin_good; eauto. }
  assert (claim4 : dbase ⊑ x).
  { eapply djoin_upperbound with (ds := f cs ts) (i := true); eauto. }
  assert (claim5 : forall cs' : Type, forall ts' : cs' -> Tree, forall H_rLt : forall c, ts' c <ᵣ mkNode cs ts, forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c).
  { ii. pose proof (H_rLt c') as [[c H_rLe]]; simpl in *. exists c. exact H_rLe. }
  assert (claim6 : forall o : Tree, forall LE : o ≦ᵣ mkNode cs ts, rec o ⊑ x).
  { intros [cs' ts'] [H_rLt]. simpl in *. unfold Ord.join.
    change (fun b : bool => if b then dbase else djoin cs' (fun c : cs' => next (rec (ts' c)))) with (f cs' ts').
    rewrite -> djoin_supremum; eauto. destruct i; eauto. simpl. eapply djoin_supremum; i; eauto.
    unfold x. eapply dle_trans with (d2 := djoin cs' (fun c' => next (rec (ts' c')))); eauto.
    - eapply djoin_good; eauto.
    - eapply djoin_upperbound with (ds := fun c' : cs' => next (rec (ts' c'))); eauto.
    - eapply djoin_supremum; eauto. intros c'. pose proof (H_rLt c') as [[c H_rLe]]; simpl in *.
      rewrite rLe_iff_rLt_or_rEq in H_rLe. destruct H_rLe as [H_LT | H_EQ].
      + eapply dle_trans with (d2 := next (rec (ts c))); eauto.
        { eapply dle_trans with (d2 := rec (ts c)); eauto.
          - eapply IH; eauto.
          - eapply IH; eauto.
          - eapply next_extensive; eauto. eapply IH; eauto.
        }
        { unfold f. eapply dle_trans with (d2 := djoin cs (fun i : cs => next (rec (ts i)))); eauto.
          - eapply djoin_good; eauto.
          - eapply djoin_upperbound with (ds := fun c : cs => next (rec (ts c))); eauto.
          - eapply djoin_upperbound with (ds := f cs ts) (i := false); eauto.
        }
      + eapply dle_trans with (d2 := next (rec (ts c))); eauto.
        { eapply next_congruence.
          - eapply IH; eauto.
          - eapply IH; eauto.
          - destruct H_EQ as [H_LE1 H_LE2]. split; eapply IH; eauto.
        }
        { unfold f. eapply dle_trans with (d2 := djoin cs (fun i : cs => next (rec (ts i)))); eauto.
          - eapply djoin_good; eauto.
          - eapply djoin_upperbound with (ds := fun c : cs => next (rec (ts c))); eauto.
          - eapply djoin_upperbound with (ds := f cs ts) (i := false); eauto.
        }
  }
  split; eauto. split; eauto. split; eauto. intros o H_rLt.
  pose proof (classic (exists o' : Tree, o <ᵣ o' /\ o' <ᵣ mkNode cs ts)) as [YES | NO].
  - unfold Ord.join. des. hexploit (IH o'); eauto. i; des. eapply dle_trans with (d2 := rec o'); eauto.
    + eapply next_good. eapply IH; eauto.
    + unfold x, f in claim6. eapply claim6. eapply rLt_implies_rLe; eauto.
  - assert (exists c, ts c =ᵣ o) as [c H_rEq].
    { eapply NNPP. intros H_contra. rewrite rLt_iff_not_rGe in H_rLt. contradiction H_rLt.
      econs. simpl. intros c. pose proof (rank_trichotomy (ts c) o) as [H_EQ | [H_LT | H_GT]]; eauto.
      - contradiction H_contra; eauto.
      - contradiction NO; eauto.
    }
    assert (rec o ≡ rec (ts c)) as claim7.
    { destruct H_rEq; split; eapply IH; eauto. }
    unfold Ord.join. eapply dle_trans with (d2 := next (rec (ts c))); eauto.
    { eapply next_good. eapply IH; eauto. }
    { eapply next_congruence.
      - eapply IH; eauto.
      - eapply IH; eauto.
      - eapply deq_sym; eauto.
    }
    { eapply dle_trans with (d2 := djoin cs (fun i : cs => next (rec (ts i)))); eauto.
      - eapply djoin_good; eauto.
      - eapply djoin_upperbound with (ds := fun c : cs => next (rec (ts c))); eauto.
      - eapply djoin_upperbound with (ds := f cs ts) (i := false); eauto.
    }
Qed.

Lemma le_rec (t : Tree) (t' : Tree)
  (H_rLe : t ≦ᵣ t')
  : rec t ⊑ rec t'.
Proof.
  eapply rec_spec; eauto.
Qed.

Lemma eq_rec (t : Tree) (t' : Tree)
  (H_rLe : t =ᵣ t')
  : rec t ≡ rec t'.
Proof.
  destruct H_rLe; split; eapply rec_spec; eauto.
Qed.

Lemma lt_rec (t : Tree) (t' : Tree)
  (H_rLt : t <ᵣ t')
  : next (rec t) ⊑ rec t'.
Proof.
  eapply rec_spec; eauto.
Qed.

Lemma rec_le_base (t : Tree)
  : dbase ⊑ rec t.
Proof.
  eapply rec_spec; eauto.
Qed.

Lemma good_rec (t : Tree)
  : good (rec t).
Proof.
  eapply rec_spec; eauto.
Qed.

#[local] Hint Resolve le_rec lt_rec eq_rec rec_le_base good_rec deq_sym : core.

Lemma rec_next_dle (t : Tree) (t' : Tree)
  (H_rLe : t ≦ᵣ t')
  : next (rec t) ⊑ next (rec t').
Proof.
  rewrite rLe_iff_rLt_or_rEq in H_rLe. destruct H_rLe as [H_rLt | H_rEq].
  - eapply dle_trans with (d2 := rec t'); eauto.
  - eapply next_congruence; eauto.
Qed.

Lemma rec_chain (t : Tree) (t' : Tree)
  : rec t ⊑ rec t' \/ rec t' ⊑ rec t.
Proof.
  pose proof (rLe_total t t') as [H | H]; [left | right]; eauto.
Qed.

Lemma rec_next_chain (t : Tree) (t' : Tree)
  : next (rec t) ⊑ next (rec t') \/ next (rec t') ⊑ next (rec t).
Proof.
  pose proof (rLe_total t t') as [H | H]; [left | right]; eapply rec_next_dle; eauto.
Qed.

Lemma good_next_rec (cs : Type) (ts : cs -> Tree)
  : forall c : cs, good (next (rec (ts c))).
Proof.
  eauto.
Qed.

#[local] Hint Resolve rec_next_dle rec_chain rec_next_chain good_next_rec : core.

Let j (cs : Type) (ts : cs -> Tree) (b : bool) : D :=
  if b then dbase else djoin cs (fun c => next (rec (ts c))).

Lemma j_chain (cs : Type) (ts : cs -> Tree) (b : bool) (b' : bool)
  : j cs ts b ⊑ j cs ts b' \/ j cs ts b' ⊑ j cs ts b.
Proof.
  assert (dbase ⊑ djoin cs (fun c => next (rec (ts c))) \/ djoin cs (fun c => next (rec (ts c))) ⊑ dbase) as claim1.
  { pose proof (classic (inhabited cs)) as [YES | NO]; [left | right].
    - destruct YES as [c]. eapply dle_trans with (d2 := next (rec (ts c))); eauto. eapply djoin_upperbound with (ds := fun c : cs => next (rec (ts c))); eauto.
    - eapply djoin_supremum; eauto. intros c. contradiction NO. econs. exact c.
  }
  destruct b, b'; simpl; eauto; try tauto.
Qed.

Lemma good_j (cs : Type) (ts : cs -> Tree)
  : forall b, good (j cs ts b).
Proof.
  intros [ | ]; simpl; eauto.
Qed.

#[local] Hint Resolve j_chain good_j : core.

Lemma rec_zero (o : Tree)
  (ZERO : o =ᵣ empty)
  : rec o ≡ dbase.
Proof.
  eapply deq_trans with (d2 := rec empty); eauto. simpl.
  change (djoin bool (j Empty_set (Empty_set_rect _)) ≡ dbase). split.
  - eapply djoin_supremum; eauto. intros [ | ]; eauto. eapply djoin_supremum; eauto. intros [].
  - eapply djoin_upperbound with (ds := j Empty_set (Empty_set_rect _)) (i := true); eauto.
Qed.

Lemma rec_succ (o : Tree) (alpha : Tree)
  (SUCC : o =ᵣ succ alpha)
  : rec o ≡ next (rec alpha).
Proof.
  eapply deq_trans with (d2 := rec (succ alpha)); eauto. simpl.
  change (djoin bool (j { b : bool & children (if b then alpha else singleton alpha) } (fun c => childnodes (if projT1 c then alpha else singleton alpha) (projT2 c))) ≡ next (rec alpha)). split.
  - eapply djoin_supremum; eauto. intros [ | ]; eauto. eapply djoin_supremum; eauto. intros [[ | ] c]; simpl; eapply rec_next_dle.
    + eapply rLt_implies_rLe. econs. exists c. reflexivity.
    + simpl in c. destruct c as [ | ]; reflexivity.
  - refine (let c : { b : bool & children (if b then alpha else singleton alpha) } := @existT _ _ false true in _).
    eapply dle_trans with (d2 := djoin { b : bool & children (if b then alpha else singleton alpha) } (fun c => next (rec (childnodes (if projT1 c then alpha else singleton alpha) (projT2 c))))); eauto.
    + eapply djoin_upperbound with (ds := fun c : {b : bool & children (if b then alpha else singleton alpha)} => next (rec (childnodes (if projT1 c then alpha else singleton alpha) (projT2 c)))) (i := c); eauto.
    + eapply djoin_upperbound with (ds := j { b : bool & children (if b then alpha else singleton alpha) } (fun c => childnodes (if projT1 c then alpha else singleton alpha) (projT2 c))) (i := false); eauto.
Qed.

Lemma rec_lim' (o : Tree) (cs : Type) (ts : cs -> Tree)
  (OPEN : forall c1 : cs, exists c2 : cs, ts c1 <ᵣ ts c2)
  (INHABITED : inhabited cs)
  (LIM' : o =ᵣ indexed_union cs ts)
  : rec o ≡ djoin cs (fun c : cs => rec (ts c)).
Proof.
  destruct INHABITED as [c]. destruct o as [cs' ts']; simpl.
  change (djoin bool (j cs' ts') ≡ djoin cs (fun i : cs => rec (ts i))); split.
  - eapply djoin_supremum; eauto. intros [ | ]; simpl.
    + eapply dle_trans with (d2 := rec (ts c)); eauto. eapply djoin_upperbound with (ds := fun i : cs => rec (ts i)) (i := c); eauto.
    + eapply djoin_supremum; eauto. clear c. intros c'. destruct LIM' as [LE1 LE2]; simpl in *. destruct LE1 as [H_rLt]; simpl in *.
      pose proof (H_rLt c') as [[c H_rLe]]; simpl in *. eapply dle_trans with (d2 := rec (ts (projT1 c))); eauto.
      * eapply lt_rec. econs. exists (projT2 c). exact H_rLe.
      * eapply djoin_upperbound with (ds := fun i : cs => rec (ts i)) (i := projT1 c); eauto.
  - eapply djoin_supremum; eauto. clear c. intros c. eapply dle_trans with (d2 := djoin cs (fun c => rec (ts c))); eauto.
    + eapply djoin_upperbound with (ds := fun i : cs => rec (ts i)) (i := c); eauto.
    + clear c. eapply djoin_supremum; eauto. intros c1. simpl in *. pose proof (OPEN c1) as [c2 H_rLt].
      destruct H_rLt as [[c H_rLe]]. destruct LIM' as [LE1 LE2]. destruct LE2 as [LE2]; simpl in *.
      pose proof (LE2 (@existT cs (fun i : cs => children (ts i)) c2 c)) as claim1. simpl in *. destruct claim1 as [[c' H_rLe']]. simpl in *.
      eapply dle_trans with (d2 := rec (ts' c')); eauto. eapply dle_trans with (d2 := djoin cs' (fun i : cs' => next (rec (ts' i)))); eauto.
      * eapply dle_trans with (d2 := next (rec (ts' c'))); eauto. eapply djoin_upperbound with (ds := fun i : cs' => next (rec (ts' i))) (i := c'); eauto.
      * eapply djoin_upperbound with (ds := j cs' ts') (i := false); eauto.
Qed.

#[local] Notation dunion := (Ord.join djoin).

Lemma dunion_good (d1 : D) (d2 : D)
  (GOOD1 : good d1)
  (GOOD2 : good d2)
  (CHAIN : d1 ⊑ d2 \/ d2 ⊑ d1)
  : good (dunion d1 d2).
Proof.
  eapply djoin_good; eauto.
  - intros [ | ] [ | ]; eauto. des; eauto.
  - intros [ | ]; eauto.
Qed.

#[local] Hint Resolve dunion_good : core.

Lemma dunion_supremum (d1 : D) (d2 : D)
  (GOOD1 : good d1)
  (GOOD2 : good d2)
  (CHAIN : d1 ⊑ d2 \/ d2 ⊑ d1)
  : forall d : D, good d -> d1 ⊑ d -> d2 ⊑ d -> dunion d1 d2 ⊑ d.
Proof.
  ii. eapply djoin_supremum; eauto.
  - intros [ | ] [ | ]; eauto. des; eauto.
  - intros [ | ]; eauto.
  - intros [ | ]; eauto.
Qed.

Lemma dunion_l (d1 : D) (d2 : D)
  (GOOD1 : good d1)
  (GOOD2 : good d2)
  (CHAIN : d1 ⊑ d2 \/ d2 ⊑ d1)
  : d1 ⊑ dunion d1 d2.
Proof.
  eapply djoin_upperbound with (ds := fun b : bool => if b then d1 else d2) (i := true).
  - intros [ | ] [ | ]; eauto. des; auto.
  - intros [ | ]; eauto.
Qed.

Lemma dunion_r (d1 : D) (d2 : D)
  (GOOD1 : good d1)
  (GOOD2 : good d2)
  (CHAIN : d1 ⊑ d2 \/ d2 ⊑ d1)
  : d2 ⊑ dunion d1 d2.
Proof.
  eapply djoin_upperbound with (ds := fun b : bool => if b then d1 else d2) (i := false).
  - intros [ | ] [ | ]; eauto. des; auto.
  - intros [ | ]; eauto.
Qed.

#[local] Hint Resolve dunion_supremum dunion_l dunion_r : core.

Let BASEJOIN (cs : Type) (ts : cs -> Tree)
  : dbase ⊑ djoin cs (fun c : cs => rec (ts c)) \/ djoin cs (fun c : cs => rec (ts c)) ⊑ dbase.
Proof.
  destruct (classic (inhabited cs)) as [YES | NO].
  - destruct YES as [c]. left. eapply dle_trans with (d2 := rec (ts c)); eauto.
    eapply djoin_upperbound with (ds := fun a => rec (ts a)) (i := c); eauto.
  - right. eapply djoin_supremum; eauto. intros c. contradiction NO. econs. exact c.
Qed.

Let BASENEXTJOIN (cs : Type) (ts : cs -> Tree)
  : dbase ⊑ djoin cs (fun c : cs => next (rec (ts c))) \/ djoin cs (fun c : cs => next (rec (ts c))) ⊑ dbase.
Proof.
  destruct (classic (inhabited cs)) as [YES | NO].
  - destruct YES as [c]. left.
    eapply dle_trans with (d2 := rec (ts c)); eauto.
    eapply dle_trans with (d2 := next (rec (ts c))); eauto.
    eapply djoin_upperbound with (ds := fun c => next (rec (ts c))); eauto.
  - right. eapply djoin_supremum; eauto. intros c. contradiction NO. econs; exact c.
Qed.

#[local] Hint Resolve BASEJOIN BASENEXTJOIN : core.

Lemma rec_join (cs : Type) (ts : cs -> Tree)
  : rec (indexed_union cs ts) ≡ dunion dbase (djoin cs (fun i : cs => rec (ts i))).
Proof.
  simpl.
  change (djoin bool (j { i : cs & children (ts i) } (fun c => childnodes (ts (projT1 c)) (projT2 c))) ≡ dunion dbase (djoin cs (fun i : cs => rec (ts i)))); split.
  - eapply djoin_supremum; eauto.
    intros [ | ]; simpl; eauto. eapply djoin_supremum; eauto. intros [c i]; simpl.
    eapply dle_trans with (d2 := rec (ts c)); eauto.
    + eapply lt_rec. econs. exists i; eauto.
    + eapply dle_trans with (d2 := djoin _ (fun c => rec (ts c))); eauto.
      eapply djoin_upperbound with (ds := fun c => rec (ts c)); eauto.
  - change (dunion dbase (djoin cs (fun i : cs => rec (ts i))) ⊑ rec (indexed_union cs ts)). eapply dunion_supremum; eauto.
    eapply djoin_supremum; eauto. intros c. eapply le_rec. econs. intros i. econs. simpl. exists (@existT _ _ c i); eauto.
Qed.

Lemma rec_is_join (o : Tree) (cs : Type) (ts : cs -> Tree)
  (JOIN : o =ᵣ indexed_union cs ts)
  : rec o ≡ dunion dbase (djoin cs (fun c : cs => rec (ts c))).
Proof.
  eapply deq_trans with (d2 := rec (indexed_union cs ts)); eauto.
  eapply rec_join.
Qed.

Lemma rec_join_inhabited (cs : Type) (ts : cs -> Tree)
  (INHABITED : inhabited cs)
  : rec (indexed_union cs ts) ≡ djoin cs (fun c : cs => rec (ts c)).
Proof.
  eapply deq_trans with (d2 := dunion dbase (djoin cs (fun i : cs => rec (ts i)))); eauto.
  - eapply rec_join with (cs := cs) (ts := ts).
  - split.
    + destruct INHABITED as [c]. eapply dunion_supremum; eauto.
      eapply dle_trans with (d2 := rec (ts c)); eauto.
      eapply djoin_supremum with (ds := fun c : cs => rec (ts c)); eauto.
    + eapply dunion_r; eauto.
Qed.

Lemma rec_is_join_inhabited (o : Tree) (cs : Type) (ts : cs -> Tree)
  (INHABITED : inhabited cs)
  (JOIN : o =ᵣ indexed_union cs ts)
  : rec o ≡ djoin cs (fun c : cs => rec (ts c)).
Proof.
  eapply deq_trans with (d2 := rec (indexed_union cs ts)); eauto.
  eapply rec_join_inhabited; eauto.
Qed.

#[local] Hint Resolve rec_is_join_inhabited : core.

Lemma rec_union (o : Tree) (o' : Tree)
  : rec (union o o') ≡ dunion (rec o) (rec o').
Proof.
  assert (INHABITED : inhabited bool).
  { constructor. exact true. }
  split.
  { eapply dle_trans with (d2 := djoin bool (fun b : bool => rec (if b then o else o'))); eauto.
    - eapply rec_join_inhabited; eauto.
    - eapply djoin_supremum; eauto. intros [ | ]; eauto.
  }
  { eapply dle_trans with (d2 := djoin bool (fun b : bool => rec (if b then o else o'))); eauto.
    - eapply djoin_supremum; eauto.
      + intros [ | ] [ | ]; simpl; eauto.
      + intros [ | ]; simpl; eauto.
      + intros [ | ].
        * eapply djoin_upperbound with (ds := fun b : bool => rec (if b then o else o')) (i := true); eauto.
        * eapply djoin_upperbound with (ds := fun b : bool => rec (if b then o else o')) (i := false); eauto.
    - eapply rec_join_inhabited; eauto.
  }
Qed.

Lemma rec_unique (f : Tree -> D)
  (ZERO : forall o : Tree, o =ᵣ empty -> f o ≡ dbase)
  (SUCC : forall o : Tree, forall alpha : Tree, o =ᵣ succ alpha -> f o ≡ next (f alpha))
  (LIM' : forall o : Tree, forall I : Type, forall alpha : I -> Tree, o =ᵣ indexed_union I alpha -> inhabited I -> (forall i1, exists i2, alpha i1 <ᵣ alpha i2) -> f o ≡ djoin I (fun i : I => f (alpha i)))
  (GOOD : forall o, good (f o))
  : forall o, f o ≡ rec o.
Proof.
  eapply transfinite_induction.
  - ii. eapply deq_trans with (d2 := dbase); eauto. eapply deq_sym. eapply rec_zero; eauto.
  - ii. eapply deq_trans with (d2 := next (f alpha)); eauto. eapply deq_sym. eapply deq_trans with (d2 := next (rec alpha)); eauto. eapply rec_succ; eauto.
  - ii. des.
    assert (CHAIN : forall i1, forall i2, dle (f (alpha i1)) (f (alpha i2)) \/ dle (f (alpha i2)) (f (alpha i1))).
    { ii. pose proof (rec_chain (alpha i1) (alpha i2)) as [LE | LE].
      - left. eapply dle_trans with (d2 := rec (alpha i1)). 1,2,3: eauto. eapply H0. eapply dle_trans with (d2 := rec (alpha i2)). 1,2,3: eauto. exact LE. eapply H0.
      - right. eapply dle_trans with (d2 := rec (alpha i2)). 1,2,3: eauto. eapply H0. eapply dle_trans with (d2 := rec (alpha i1)). 1,2,3: eauto. exact LE. eapply H0.
    }
    eapply deq_sym. eapply deq_trans with (d2 := djoin I (fun i => f (alpha i))); eauto.
    + eapply deq_trans with (d2 := djoin I (fun i => rec (alpha i))); eauto. split; eapply djoin_supremum. 1,2,3,5,6,7: eauto.
      * i. eapply dle_trans with (d2 := f (alpha i)). 1,2,3: eauto. eapply H0. eapply djoin_upperbound with (ds := fun i => f (alpha i)); eauto.
      * i. eapply dle_trans with (d2 := rec (alpha i)). 1,2,3: eauto. eapply H0. eapply djoin_upperbound with (ds := fun i => rec (alpha i)); eauto.
Qed.

Lemma rec_characterisation (rec' : Tree -> D)
  (REC : forall cs : Type, forall ts : cs -> Tree, rec' (mkNode cs ts) ≡ dunion dbase (djoin cs (fun c : cs => next (rec' (ts c)))))
  (GOOD : forall o : Tree, good (rec' o))
  : forall o : Ord.t, rec' o ≡ rec o.
Proof.
  rename rec' into f. intros t; red in t. induction t as [cs ts IH]; simpl.
  assert (NEXTLE : forall c1 : cs, forall c2 : cs, ts c1 ≦ᵣ ts c2 -> next (f (ts c1)) ⊑ next (f (ts c2))).
  { ii. eapply dle_trans with (d2 := next (rec (ts c1))); eauto.
    - eapply next_congruence; eauto.
    - eapply dle_trans with (d2 := next (rec (ts c2))); eauto. eapply next_congruence; eauto.
  }
  assert (NEXTCHAIN : forall c1 : cs, forall c2 : cs, next (f (ts c1)) ⊑ next (f (ts c2)) \/ next (f (ts c2)) ⊑ next (f (ts c1))).
  { ii. pose proof (rLe_total (ts c1) (ts c2)) as [? | ?]; eauto. }
  assert (BASE : dbase ⊑ djoin cs (fun c => next (f (ts c))) \/ djoin cs (fun c => next (f (ts c))) ⊑ dbase).
  { ii. destruct (classic (inhabited cs)) as [YES | NO]; [left | right].
    - destruct YES as [c]. eapply dle_trans with (d2 := f (ts c)); eauto.
      + eapply dle_trans with (d2 := rec (ts c)); eauto. eapply IH.
      + eapply dle_trans with (d2 := next (f (ts c))); eauto. eapply djoin_upperbound with (ds := fun c => next (f (ts c))); eauto.
    - eapply djoin_supremum; eauto. intros c. contradiction NO. econs. exact c.
  }
  assert (H1_good : good (dunion dbase (djoin cs (fun c => next (f (ts c)))))).
  { eapply dunion_good; eauto. }
  assert (H2_good : good (dunion dbase (djoin cs (fun c => next (rec (ts c)))))).
  { eapply djoin_good; [eapply j_chain | eapply good_j]. }
  split.
  - eapply dle_trans with (d2 := dunion dbase (djoin cs (fun c => next (f (ts c))))). 1,2,3: eauto.
    + eapply REC.
    + eapply djoin_supremum; eauto.
      * intros [ | ] [ | ]; simpl; eauto. destruct BASE; eauto.
      * intros [ | ]; eauto.
      * intros [ | ]; eauto. eapply dle_trans with (d2 := djoin cs (fun c => next (rec (ts c)))); eauto.
        eapply djoin_supremum; eauto. intros i. eapply dle_trans with (d2 := next (rec (ts i))). 1,2,3: eauto.
        { eapply next_congruence; eauto. }
        { eapply djoin_upperbound with (ds := fun c => next (rec (ts c))); eauto. }
  - eapply dle_trans with (d2 := dunion dbase (djoin cs (fun c => next (f (ts c))))). 1,2,3: eauto.
    + eapply dunion_supremum; eauto. eapply dle_trans with (d2 := djoin cs (fun c => next (f (ts c)))). 1,2,3: eauto.
      * eapply djoin_supremum; eauto. intros i. eapply dle_trans with (d2 := next (f (ts i))). 1,2,3: eauto.
        { eapply next_congruence; eauto. }
        { eapply djoin_upperbound with (ds := fun c => next (f (ts c))); eauto. }
      * eapply dunion_r; eauto.
    + eapply REC.
Qed.

Lemma rec_good (o : Tree)
  : good (rec o).
Proof.
  eapply good_rec; eauto.
Qed.

Lemma rec_next_good (o : Tree)
  : good (next (rec o)).
Proof.
  eapply next_good. eapply rec_good; eauto.
Qed.

Inductive strictly_increasing : D -> D -> Prop :=
  | strictly_increasing_intro (alpha : Tree) (beta : Tree)
    (LT : alpha <ᵣ beta)
    (INCR : ~ rec beta ⊑ rec alpha)
    : strictly_increasing (rec alpha) (rec beta).

Lemma strictly_increasing_well_founded
  : well_founded strictly_increasing.
Proof.
  enough (claim1 : forall o : Tree, Acc strictly_increasing (rec o)).
  { intros d. econs. intros d' H. inv H. eapply claim1. }
  intros o. pose proof (rLt_wf o) as H_Acc. induction H_Acc as [o _ IH].
  econs. intros o' H. inv H. eapply IH.
  pose proof (rLe_or_rGt o alpha) as [LE | GT].
  - contradiction INCR. rewrite H2. eapply le_rec. exact LE.
  - exact GT.
Qed.

Definition not_fixed (beta : Tree) : Prop :=
  forall alpha : Tree, forall LT : alpha <ᵣ beta, ~ rec beta ⊑ rec alpha.

Lemma fixed_point_after (alpha : Tree) (beta : Tree)
  (FIX : next (rec alpha) ⊑ rec alpha)
  (LE : alpha ≦ᵣ beta)
  : rec beta ⊑ rec alpha.
Proof.
  revert alpha FIX LE. induction beta using @transfinite_induction; ii.
  - eapply le_rec; eauto. rewrite ZERO. econs. intros [].
  - assert (next (rec alpha) ≡ rec alpha) as claim1.
    { split; eauto. }
    eapply rLe_iff_rLt_or_rEq in LE. destruct LE as [LT | EQ].
    + unnw. eapply dle_trans with (d2 := next (rec beta2)). 1,2,3: eauto.
      * eapply rec_succ; eauto.
      * eapply dle_trans with (d2 := next (rec alpha)); eauto. eapply next_congruence; eauto. rewrite rEq_succ_iff in SUCC. rewrite -> SUCC in LT. split; eauto.
    + eapply le_rec; eauto. eapply EQ.
  - hexploit rec_is_join_inhabited; try eassumption. i; des. rename I into cs, alpha into ts, alpha0 into alpha.
    assert (claim1 : forall c1 : cs, forall c2 : cs, rec (ts c1) ⊑ rec (ts c2) \/ rec (ts c2) ⊑ rec (ts c1)).
    { ii. pose proof (rLe_total (ts c1) (ts c2)) as [H_LE | H_LE]; [left | right]; eapply le_rec; eauto. }
    eapply dle_trans with (d2 := djoin cs (fun c => rec (ts c))). 1,2,3: eauto.
    + eapply H2.
    + eapply djoin_supremum; eauto. intros i. pose proof (rLe_or_rGt (ts i) alpha) as [H_LE | H_GT]; eauto. eapply H0; eauto. eapply rLt_implies_rLe; eauto.
Qed.

Lemma end_le_end (o : Tree) (o' : Tree)
  (LE : o ≦ᵣ o')
  (NOT_END : not_fixed o')
  : not_fixed o.
Proof.
  ii. eapply NOT_END with (alpha := alpha).
  - eapply rLt_rLe_rLt; eauto.
  - assert (claim1 : succ alpha ≦ᵣ o).
    { econs. simpl. intros [[ | ] c]; simpl.
      - transitivity alpha; eauto. destruct alpha; eauto.
      - destruct c; eauto.
    }
    eapply fixed_point_after with (alpha := alpha).
    + eapply dle_trans with (d2 := rec (succ alpha)); eauto.
      eapply rec_succ. reflexivity.
    + transitivity o; eauto. eapply rLt_implies_rLe; eauto.
Qed.

Lemma least_lt_incr_acc (o : Tree)
  (INCR : not_fixed o)
  : o ≦ᵣ @fromWf D strictly_increasing strictly_increasing_well_founded (rec o).
Proof.
  pose proof (rLt_wf o) as H_Acc. induction H_Acc as [o _ IH].
  pose proof (rLe_or_rGt o (@fromWf D strictly_increasing strictly_increasing_well_founded (rec o))) as [H_LE | H_GT]; eauto.
  destruct o; simpl. econs. simpl. intros c.
  assert (claim1 : not_fixed (ts c)).
  { eapply end_le_end with (o' := mkNode cs ts); eauto. eapply rLt_implies_rLe; eauto. }
  pose proof (IH (ts c) (trivial_rLt cs ts c) claim1) as claim2. eapply rLe_rLt_rLt; eauto.
  assert (strictly_increasing (rec (ts c)) (rec (mkNode cs ts))) as claim3.
  { econs; eauto. }
  econs. eapply member_implies_rLt. unfold fromWf. eapply fromAcc_member_fromAcc_intro. exact claim3.
Qed.

Lemma Hartogs_fixed
  : ~ not_fixed (Hartogs D).
Proof.
  intros H_contra. apply least_lt_incr_acc in H_contra; eauto.
  eapply rLt_iff_not_rGe. 2: exact H_contra. eapply rLe_rLt_rLt with (y := @fromWfSet D strictly_increasing strictly_increasing_well_founded).
  - eapply rLt_implies_rLe. econs. unfold fromWfSet. exists (rec (Hartogs D)). reflexivity.
  - econs. simpl. exists (B.exist strictly_increasing strictly_increasing_well_founded). reflexivity.
Qed.

Theorem BourbakiWittFixedpointTheorem
  : next (rec (Hartogs D)) ≡ rec (Hartogs D).
Proof.
  split.
  - eapply NNPP. intros H_contra. eapply Hartogs_fixed. eapply end_le_end with (o' := succ (Hartogs D)).
    { eapply rLt_implies_rLe. econs. simpl. exists (@existT _ _ false true). simpl. reflexivity. }
    intros o H_rLt H_dle. eapply H_contra. eapply dle_trans with (d2 := rec (succ (Hartogs D))). 1,2,3: eauto.
    + eapply rec_succ. reflexivity.
    + pose proof (rLe_or_rGt o (Hartogs D)) as [H_rLe | H_rGt].
      * eapply dle_trans with (d2 := rec o); eauto.
      * exfalso. eapply rLt_iff_not_rGe; [exact H_rLt | ].
        assert (claim1 : succ (Hartogs D) =ᵣ succ (Hartogs D)) by reflexivity.
        rewrite rEq_succ_iff in claim1. eapply succ_rLe_intro; eauto.
  - eapply next_extensive; eauto.
Qed.

End BOURBAKI_WITT_FIXEDPOINT_THEOREM.

Section GENERALISED_KLEENE_FIXEDPOINT_THEOREM.

#[local] Hint Unfold E.In : simplication_hints.

Context {D : Type} {PROSET : isProset D}.

#[local] Notation range ds := (fun d : D => exists i, d = ds i).

Variable ipo_sup : forall I : Type, forall ds : I -> D, D.

Hypothesis ipo_sup_is_supremum : forall I : Type, forall ds : I -> D, forall CHAIN : forall i1, forall i2, ds i1 =< ds i2 \/ ds i2 =< ds i1, is_supremum_of (ipo_sup I ds) (range ds).

Theorem generalised_Kleene_fixedpoint_theorem (f : D -> D)
  (f_isMonotonic : isMonotonic1 f)
  (mu_f := Ord.rec (D := D) (ipo_sup Empty_set (Empty_set_rect (fun _ : Empty_set => D))) f ipo_sup (Hartogs D))
  : is_lfpOf mu_f f.
Proof.
  split.
  - red. red. symmetry.
    enough (f mu_f =< mu_f /\ mu_f =< f mu_f) as [H1 H2] by now eapply leProp_antisymmetry.
    eapply BourbakiWittFixedpointTheorem with (good := fun x : D => x =< f x) (dbase := ipo_sup Empty_set (Empty_set_rect _)) (djoin := ipo_sup) (next := f).
    + ii; reflexivity.
    + ii; now transitivity d2.
    + ii. eapply ipo_sup_is_supremum; eauto. ii. red in IN. destruct IN as (i & ->). transitivity (f (ds i)); eauto.
      eapply f_isMonotonic. eapply ipo_sup_is_supremum; done!.
    + ii. split.
      * intros H_LE i. eapply ipo_sup_is_supremum; eauto with *.
      * intros H_upperbound. eapply ipo_sup_is_supremum; done!.
    + eapply ipo_sup_is_supremum; done!.
    + ii; done!.
    + ii; done!.
    + ii; des; split; done!.
  - red. red. intros fix_f H_fix_f. do 2 red in H_fix_f.
    enough (mu_f =< f mu_f /\ mu_f =< fix_f) as [H1 H2] by now exact H2.
    eapply @rec_good with (D := D) (dle := leProp) (good := fun x : D => x =< f x /\ x =< fix_f) (dbase := ipo_sup Empty_set (Empty_set_rect _)) (djoin := ipo_sup) (next := f).
    + ii; reflexivity.
    + ii; now transitivity d2.
    + ii. split; eapply ipo_sup_is_supremum; eauto; try done!. do 2 red. ii. destruct IN as [i ->].
      transitivity (f (ds i)); eauto; try done!. eapply f_isMonotonic. eapply ipo_sup_is_supremum; eauto; done!.
    + ii. split.
      * intros H_LE i. eapply ipo_sup_is_supremum; eauto with *.
      * intros H_upperbound. eapply ipo_sup_is_supremum; done!.
    + split; eapply ipo_sup_is_supremum; ii; try done!.
    + ii; split.
      * eapply f_isMonotonic; done!.
      * des. rewrite H_fix_f. eapply f_isMonotonic. done!.
    + ii; des; done!.
    + done!.
Qed.

End GENERALISED_KLEENE_FIXEDPOINT_THEOREM.

End THEORY_ON_RANK.

End InducedOrdinal.

Module Ordinal1.

Section ORDINAL_section1.

#[local] Infix "\in" := member.
#[local] Infix "\subseteq" := isSubsetOf.

#[local] Hint Resolve isOrdinal_member_isOrdinal : core.
#[local] Hint Unfold rEq : simplication_hints.

Lemma Ordinal_comparison__aux1 (x : Tree) (alpha : Tree) (beta : Tree)
  (x_rGe1 : alpha ≦ᵣ x)
  (x_rGe2 : beta ≦ᵣ x)
  (H_isOrdinal1 : isOrdinal alpha)
  (H_isOrdinal2 : isOrdinal beta)
  : (alpha <ᵣ beta -> alpha \in beta) /\ (alpha =ᵣ beta -> alpha == beta).
Proof with eauto with *.
  revert alpha beta x_rGe1 x_rGe2 H_isOrdinal1 H_isOrdinal2. pose proof (rLt_wf x) as H_Acc. induction H_Acc as [x _ IH].
  destruct alpha as [cs1 ts1], beta as [cs2 ts2]; ii. split; intros H.
  - destruct H as [[c2 H_rLe]]. simpl in *. exploit (IH (ts2 c2) _ (mkNode cs1 ts1) (ts2 c2))...
    { eapply rLt_rLe_rLt... }
    intros (H1 & H2). rewrite InducedOrdinal.rLe_iff_rLt_or_rEq in H_rLe. destruct H_rLe as [H_LT | H_EQ].
    + specialize (H1 H_LT). inversion H_isOrdinal2. eapply TRANS with (y := ts2 c2)...
    + specialize (H2 H_EQ). rewrite -> H2...
  - eapply extensionality. intros z; split; intros [c z_eq].
    + simpl in *. change (z == ts1 c) in z_eq. destruct H as [H_rLe1 H_rLe2]. destruct H_rLe1. simpl in H_rLt. pose proof (H_rLt c) as [[c' H_rLe]].
      simpl in c', H_rLe. rewrite InducedOrdinal.rLe_iff_rLt_or_rEq in H_rLe. rewrite z_eq. clear z z_eq. destruct H_rLe as [H_LT | H_EQ].
      * exploit (IH (ts2 c') _ (ts1 c) (ts2 c'))...
        { eapply rLt_rLe_rLt... }
        intros (H1 & H2). specialize (H1 H_LT). inversion H_isOrdinal2. eapply TRANS with (y := ts2 c')...
      * exploit (IH (ts2 c') _ (ts1 c) (ts2 c'))...
        { eapply rLt_rLe_rLt... }
        { rewrite -> H_EQ... }
        intros (H1 & H2). specialize (H2 H_EQ). rewrite -> H2...
    + simpl in *. change (z == ts2 c) in z_eq. destruct H as [H_rLe1 H_rLe2]. destruct H_rLe2. simpl in H_rLt. pose proof (H_rLt c) as [[c' H_rLe]].
      simpl in c', H_rLe. rewrite InducedOrdinal.rLe_iff_rLt_or_rEq in H_rLe. rewrite z_eq. clear z z_eq. destruct H_rLe as [H_LT | H_EQ].
      * exploit (IH (ts1 c') _ (ts2 c) (ts1 c'))...
        { eapply rLt_rLe_rLt... }
        intros (H1 & H2). specialize (H1 H_LT). inversion H_isOrdinal1. eapply TRANS with (y := ts1 c')...
      * exploit (IH (ts1 c') _ (ts2 c) (ts1 c'))...
        { eapply rLt_rLe_rLt... }
        { rewrite -> H_EQ... }
        intros (H1 & H2). specialize (H2 H_EQ). rewrite -> H2...
Qed.

Lemma Ordinal_rLt_Ordinal_elim (alpha : Tree) (beta : Tree)
  (H_isOrdinal1 : isOrdinal alpha)
  (H_isOrdinal2 : isOrdinal beta)
  (H_rLt : alpha <ᵣ beta)
  : alpha \in beta.
Proof.
  eapply Ordinal_comparison__aux1 with (x := beta); eauto with *.
Qed.

Lemma Ordinal_rEq_Ordinal_elim (alpha : Tree) (beta : Tree)
  (H_isOrdinal1 : isOrdinal alpha)
  (H_isOrdinal2 : isOrdinal beta)
  (H_rEq : alpha =ᵣ beta)
  : alpha == beta.
Proof.
  eapply Ordinal_comparison__aux1 with (x := beta); done!.
Qed.

Lemma Ordinal_rLe_Ordinal_elim (alpha : Tree) (beta : Tree)
  (H_isOrdinal1 : isOrdinal alpha)
  (H_isOrdinal2 : isOrdinal beta)
  (H_rLe : alpha ≦ᵣ beta)
  : alpha \subseteq beta.
Proof.
  intros z z_in. eapply Ordinal_rLt_Ordinal_elim; eauto with *.
  eapply rLt_rLe_rLt; eauto with *.
Qed.

End ORDINAL_section1.

Section RANK.

#[local] Infix "\in" := member.
#[local] Infix "\subseteq" := isSubsetOf.

Lemma toSet_wlt_Transitive (t : Tree)
  : Transitive (toSet_wlt t).
Proof.
  red. i. eapply @toWellPoset_Transitive; eauto. now ii; eapply projT2_eq.
Qed.

#[local]
Instance toSet_isWellPoset (t : Tree) : isWellPoset (toSet t) :=
  { wltProp := toSet_wlt t
  ; wltProp_well_founded := toSet_wlt_well_founded t
  ; wltProp_Transitive := toSet_wlt_Transitive t
  }.

Lemma rank_isOrdinal (t : Tree)
  : isOrdinal (rank t).
Proof.
  econs.
  - intros y [cy y_eq] z. simpl in cy. rewrite y_eq. clear y y_eq. simpl. intros z_in.
    rewrite fromWf_unfold in z_in. destruct z_in as (c & H_LT & z_eq). rewrite z_eq.
    clear z z_eq. exists c. simpl. reflexivity.
  - intros beta [c beta_eq] y. simpl in c. intros y_in z z_in. rewrite -> beta_eq in y_in |- *. simpl in y_in |- *.
    clear beta beta_eq. rewrite fromWf_unfold in y_in. destruct y_in as (cy & H_LT1 & y_eq). rewrite y_eq in z_in.
    rewrite fromWf_unfold in z_in. destruct z_in as (cz & H_LT2 & z_eq). rewrite z_eq. clear y y_eq z z_eq.
    eapply fromAcc_member_fromAcc_intro. exact (toSet_wlt_Transitive t cz cy c H_LT2 H_LT1).
Qed.

Lemma rank_rEq (t : Tree)
  : rank t =ᵣ t.
Proof.
  unfold rank. unfold toWellPoset, toSet_wlt_well_founded. rewrite -> @fromWfSet_toWellPoset_rEq with (t := t); [reflexivity | now ii; eapply projT2_eq].
Qed.

End RANK.

Section ToOrderType.

#[local] Infix "\in" := member.
#[local] Infix "\subseteq" := isSubsetOf.

Lemma FromOrderType_ToOrderType_rEq (alpha : Tree)
  : FromOrderType (ToOrderType alpha) =ᵣ alpha.
Proof.
  symmetry. etransitivity.
  - symmetry. eapply rank_rEq.
  - eapply Totalify.fromWfSet_rEq.
Qed.

Lemma ToOrderType_wlt_iff (alpha : Tree) (x : ToOrderType alpha) (y : ToOrderType alpha)
  : x ≺ y <-> (exists z : ToOrderType alpha, x == z /\ toSet_wlt alpha z y).
Proof.
  transitivity (@fromWf (toSet alpha) (toSet_wlt alpha) (toSet_wlt_well_founded alpha) x <ᵣ @fromWf (toSet alpha) (toSet_wlt alpha) (toSet_wlt_well_founded alpha) y).
  { reflexivity. }
  transitivity (@fromWf (toSet alpha) (toSet_wlt alpha) (toSet_wlt_well_founded alpha) x \in @fromWf (toSet alpha) (toSet_wlt alpha) (toSet_wlt_well_founded alpha) y).
  { split.
    - intros H_rLt. eapply Ordinal_rLt_Ordinal_elim; try eassumption; eapply fromWf_isOrdinal; eapply toSet_wlt_Transitive.
    - intros H_in. eapply member_implies_rLt. exact H_in.
  }
  transitivity (fromWf (projT2 (toWellPoset alpha)) (toWellPoset_well_founded alpha) x \in fromWf (projT2 (toWellPoset alpha)) (toWellPoset_well_founded alpha) y).
  { reflexivity. }
  rewrite @fromWf_toWellPoset_in_fromWf_toWellPoset_iff; cycle 1.
  { now ii; eapply projT2_eq. }
  split; intros (z & H_R & H_EQ); exists z; split; try eassumption.
  - do 3 red. now rewrite H_EQ.
  - do 3 red in H_EQ. eapply Ordinal_rEq_Ordinal_elim; try eassumption; eapply fromWf_isOrdinal; eapply toSet_wlt_Transitive.
Qed.

Lemma FromOrderType_ToOrderType_id (alpha : Tree)
  (ORDINAL : isOrdinal alpha)
  : FromOrderType (ToOrderType alpha) == alpha.
Proof.
  eapply Ordinal_rEq_Ordinal_elim.
  - eapply FromOrderType_isOrdinal.
  - exact ORDINAL.
  - eapply FromOrderType_ToOrderType_rEq.
Qed.

End ToOrderType.

End Ordinal1.

Lemma fromWfSet_embed `{Axms : ClassicalAxioms (b_AC := true)} (A : Type@{Set_u}) (B : Type@{Set_u}) (A_isSetoid : isSetoid A) (B_isSetoid : isSetoid B) (RA : A -> A -> Prop) (RB : B -> B -> Prop)
  (RA_wf : well_founded RA)
  (RB_wf : well_founded RB)
  (RB_eqPropCompatible2 : eqPropCompatible2 RB)
  (RB_Transitive : Transitive RB)
  (H_rLe : @fromWfSet A RA RA_wf ≦ᵣ @fromWfSet B RB RB_wf)
  (RB_total : forall y1, forall y2, y1 == y2 \/ RB y1 y2 \/ RB y2 y1)
  : exists f : A -> B, forall x1 : A, forall x2 : A, RA x1 x2 -> RB (f x1) (f x2).
Proof.
  hexploit (Axiom_of_Choice A (fun _ => B) (fun a : A => fun b : B => rEq (fromWf RA RA_wf a) (fromWf RB RB_wf b))).
  { intros a. eapply InducedOrdinal.fromWfSet_complete. eapply rLt_rLe_rLt; eauto. econs. exists a. reflexivity. }
  intros EQ. des. exists f. intros a1 a2 a1_RA_a2.
  assert (LT : fromWf RA RA_wf a1 <ᵣ fromWf RA RA_wf a2).
  { eapply member_implies_rLt. rewrite fromWf_unfold. exists a1. now split; trivial. }
  assert (claim1 : fromWf RB RB_wf (f a1) <ᵣ fromWf RB RB_wf (f a2)).
  { eapply rLe_rLt_rLt with (y := fromWf RA RA_wf a1); eauto.
    - eapply EQ.
    - eapply rLt_rLe_rLt with (y := fromWf RA RA_wf a2); eauto. eapply EQ.
  }
  pose proof (RB_total (f a1) (f a2)) as [H_EQ | [H_LT | H_GT]].
  - exfalso. revert claim1. change (~ fromWf RB RB_wf (f a1) <ᵣ fromWf RB RB_wf (f a2)).
    eapply @well_founded_implies_Irreflexive' with (SETOID := rEq_asSetoid) (R := rLt).
    + exact rLt_wf.
    + intros x1 x2 x1_rEq_x2. do 3 red in x1_rEq_x2.
      destruct x1_rEq_x2 as [H1_rLe H2_rLe]. intros x H_rLt. eapply rLe_rLt_rLt; eauto.
    + set (WPOSET := {| wltProp := RB; wltProp_well_founded := RB_wf; wltProp_Transitive := RB_Transitive |}).
      set (WOSET := @O.WellfoundedToset_isWoset classic B B_isSetoid WPOSET RB_eqPropCompatible2 RB_total).
      change (@fromOrderType B B_isSetoid WOSET (f a1) =ᵣ @fromOrderType B B_isSetoid WOSET (f a2)).
      enough (fromOrderType B (f a1) == fromOrderType B (f a2)) as H by now rewrite H.
      now rewrite fromOrderType_eq_fromOrderType_iff.
  - trivial.
  - assert (claim2 : fromWf RB RB_wf (f a2) <ᵣ fromWf RB RB_wf (f a1)).
    { eapply member_implies_rLt. rewrite fromWf_unfold. exists (f a2). now split. }
    contradiction (StrictOrder_Irreflexive (fromWf RB RB_wf (f a1))); now transitivity (fromWf RB RB_wf (f a2)).
Qed.

Lemma fromWfSet_embed' `{Axms : ClassicalAxioms (b_AC := true)} (A : Type@{Set_u}) (B : Type@{Set_u}) (A_isSetoid : isSetoid A) (B_isSetoid : isSetoid B) (RA : A -> A -> Prop) (RB : B -> B -> Prop)
  (RA_wf : well_founded RA)
  (RB_wf : well_founded RB)
  (RA_eqPropCompatible2 : eqPropCompatible2 RA)
  (RB_eqPropCompatible2 : eqPropCompatible2 RB)
  (RA_Transitive : Transitive RA)
  (RB_Transitive : Transitive RB)
  (H_rLe : @fromWfSet A RA RA_wf ≦ᵣ @fromWfSet B RB RB_wf)
  (RA_total : forall x1, forall x2, x1 == x2 \/ RA x1 x2 \/ RA x2 x1)
  (RB_total : forall y1, forall y2, y1 == y2 \/ RB y1 y2 \/ RB y2 y1)
  : exists f : A -> B, forall x1 : A, forall x2 : A, RA x1 x2 <-> RB (f x1) (f x2).
Proof.
  hexploit (Axiom_of_Choice A (fun _ => B) (fun a : A => fun b : B => rEq (fromWf RA RA_wf a) (fromWf RB RB_wf b))).
  { intros a. eapply InducedOrdinal.fromWfSet_complete. eapply rLt_rLe_rLt; eauto. econs. exists a. reflexivity. }
  intros EQ. des. exists f. intros a1 a2; split; [intros a1_RA_a2 | intros f_a1_RB_f_a2].
  - assert (LT : fromWf RA RA_wf a1 <ᵣ fromWf RA RA_wf a2).
    { eapply member_implies_rLt. rewrite fromWf_unfold. exists a1. now split; trivial. }
    assert (claim1 : fromWf RB RB_wf (f a1) <ᵣ fromWf RB RB_wf (f a2)).
    { eapply rLe_rLt_rLt with (y := fromWf RA RA_wf a1); eauto.
      - eapply EQ.
      - eapply rLt_rLe_rLt with (y := fromWf RA RA_wf a2); eauto. eapply EQ.
    }
    pose proof (RB_total (f a1) (f a2)) as [H_EQ | [H_LT | H_GT]].
    + exfalso. revert claim1. change (~ fromWf RB RB_wf (f a1) <ᵣ fromWf RB RB_wf (f a2)).
      eapply @well_founded_implies_Irreflexive' with (SETOID := rEq_asSetoid) (R := rLt).
      * exact rLt_wf.
      * intros x1 x2 x1_rEq_x2. do 3 red in x1_rEq_x2.
        destruct x1_rEq_x2 as [H1_rLe H2_rLe]. intros x H_rLt. eapply rLe_rLt_rLt; eauto.
      * set (WPOSET := {| wltProp := RB; wltProp_well_founded := RB_wf; wltProp_Transitive := RB_Transitive |}).
        set (WOSET := @O.WellfoundedToset_isWoset classic B B_isSetoid WPOSET RB_eqPropCompatible2 RB_total).
        change (@fromOrderType B B_isSetoid WOSET (f a1) =ᵣ @fromOrderType B B_isSetoid WOSET (f a2)).
        enough (fromOrderType B (f a1) == fromOrderType B (f a2)) as H by now rewrite H.
        now rewrite fromOrderType_eq_fromOrderType_iff.
    + trivial.
    + assert (claim2 : fromWf RB RB_wf (f a2) <ᵣ fromWf RB RB_wf (f a1)).
      { eapply member_implies_rLt. rewrite fromWf_unfold. exists (f a2). now split. }
      contradiction (StrictOrder_Irreflexive (fromWf RB RB_wf (f a1))); now transitivity (fromWf RB RB_wf (f a2)).
  - assert (LT : fromWf RB RB_wf (f a1) <ᵣ fromWf RB RB_wf (f a2)).
    { eapply member_implies_rLt. rewrite fromWf_unfold. exists (f a1). now split; trivial. }
    assert (claim1 : fromWf RA RA_wf a1 <ᵣ fromWf RA RA_wf a2).
    { now do 2 rewrite EQ. }
    pose proof (RA_total a1 a2) as [H_EQ | [H_LT | H_GT]].
    + exfalso. revert claim1. change (~ fromWf RA RA_wf a1 <ᵣ fromWf RA RA_wf a2).
      eapply @well_founded_implies_Irreflexive' with (SETOID := rEq_asSetoid) (R := rLt).
      * exact rLt_wf.
      * intros x1 x2 x1_rEq_x2. do 3 red in x1_rEq_x2.
        destruct x1_rEq_x2 as [H1_rLe H2_rLe]. intros x H_rLt. eapply rLe_rLt_rLt; eauto.
      * set (WPOSET := {| wltProp := RA; wltProp_well_founded := RA_wf; wltProp_Transitive := RA_Transitive |}).
        set (WOSET := @O.WellfoundedToset_isWoset classic A A_isSetoid WPOSET RA_eqPropCompatible2 RA_total).
        change (@fromOrderType A A_isSetoid WOSET a1 =ᵣ @fromOrderType A A_isSetoid WOSET a2).
        enough (fromOrderType A a1 == fromOrderType A a2) as H by now rewrite H.
        now rewrite fromOrderType_eq_fromOrderType_iff.
    + trivial.
    + assert (claim2 : fromWf RA RA_wf a2 <ᵣ fromWf RA RA_wf a1).
      { eapply member_implies_rLt. rewrite fromWf_unfold. exists a2. now split. }
      contradiction (StrictOrder_Irreflexive (fromWf RA RA_wf a1)); now transitivity (fromWf RA RA_wf a2).
Qed.

Variant good {X : Type} {SETOID : isSetoid X} (P : X -> Prop) (R : X -> X -> Prop) : Prop :=
  | good_intro
    (SOUND : forall a : X, forall b : X, forall LT : R a b, P a /\ P b)
    (COMPLETE : forall a : X, forall b : X, forall IN : P a, forall IN' : P b, a == b \/ (R a b \/ R b a))
    (WELL_FOUNDED : well_founded R)
    (R_eqPropCompatible2 : eqPropCompatible2 R)
    (P_eqCompatible1 : eqPropCompatible1 P)
    : good P R.

Section WELL_ORDERING_THEOREM.

Context {X : Type}.

#[projections(primitive)]
Record pair : Type :=
  { P (x : X) : Prop
  ; R (x : X) (y : X) : Prop
  } as s.

Variant pair_le (s : pair) (s' : pair) : Prop :=
  | pair_le_intro
    (P_incl : forall a : X, forall IN : s.(P) a, s'.(P) a)
    (R_incl : forall a : X, forall b : X, forall LT : s.(R) a b, s'.(R) a b)
    (NO_INSERTION : forall a : X, forall b : X, forall IN' : s.(P) b, s'.(R) a b <-> s.(R) a b)
    : pair_le s s'.

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
  intros s0 s1 s2 [? ? ?] [? ? ?]. simpl in *.
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
  ; leProp_PartialOrder := mkSetoidFromPreOrder_good pair_le_PreOrder
  }.

Definition pair_sup (I : Type) (chain : I -> pair) : pair :=
  {| P (x : X) := exists i : I, (chain i).(P) x; R (x : X) (y : X) := exists i : I, (chain i).(R) x y; |}.

Lemma pair_sup_isSupremum (I : Type) (chain : I -> pair)
  (H_chain : forall i1 : I, forall i2 : I, chain i1 =< chain i2 \/ chain i2 =< chain i1)
  : is_supremum_of (pair_sup I chain) (fun s : pair => exists i : I, s = chain i).
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

Variable X_bot : X.

Definition base : pair :=
  {| P := eqProp X_bot; R _ _ := False |}.

#[local] Notation good s := (good (X := X) (SETOID := SETOID) s.(P) s.(R)).

Lemma pair_sup_good (I : Type) (chain : I -> pair)
  (H_chain : forall i1 : I, forall i2 : I, chain i1 =< chain i2 \/ chain i2 =< chain i1)
  (chain_good : forall i : I, good (chain i))
  : good (pair_sup I chain).
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
    pose proof (SOUND _ _ H_R) as [H_P _]. clear H_R. induction H_Acc as [x0 _ IH]; intros; econs; intros y [i' H_R'].
    assert (LT : (chain i).(R) y x0).
    { pose proof (H_chain i i') as [[? ? ?] | [? ? ?]]; eauto. rewrite <- NO_INSERTION; eauto. }
    eapply IH; eauto. pose proof (SOUND _ _ LT) as [? ?]; tauto.
  - ii. do 2 red. unfold pair_sup. simpl. split; intros [i H]; pose proof (chain_good i) as [? ? ? ?]; exists i.
    + rewrite <- x_EQ, <- y_EQ; eauto.
    + rewrite -> x_EQ, -> y_EQ; eauto.
  - ii. do 2 red. unfold pair_sup. simpl. split; intros [i H]; pose proof (chain_good i) as [? ? ? ?]; exists i.
    + rewrite <- x_EQ; eauto.
    + rewrite -> x_EQ; eauto.
Qed.

Lemma base_good
  : good base.
Proof.
  econs; ss.
  i. subst.
  - left. now rewrite <- IN.
  - do 3 red. ii. now rewrite <- x_EQ.
Qed.

Lemma pair_sup_isSupremum' (I : Type) (ds : I -> pair) (d : pair)
  (H_chain : forall i1 : I, forall i2 : I, ds i1 =< ds i2 \/ ds i2 =< ds i1)
  (GOOD : good d)
  : pair_le (pair_sup I ds) d <-> (forall i : I, pair_le (ds i) d).
Proof.
  pose proof (pair_sup_isSupremum I ds H_chain) as claim1. split.
  - intros H_le i. eapply claim1; eauto. red. now exists i.
  - intros H_le. eapply claim1. red. red. intros x H_x. red in H_x.
    destruct H_x as [i ->]. eapply H_le.
Qed.

Section NEXT.

Variable next : pair -> pair.

Hypothesis next_extensive : forall s : pair, good s -> s =< next s.

Hypothesis next_eq : forall s1 : pair, forall s2 : pair, good s1 -> good s2 -> s1 == s2 -> next s1 == next s2.

Hypothesis next_good : forall s : pair, good s -> good (next s).

Hypothesis next_exhausted : forall s : pair, good s-> (forall x : X, s.(P) x) \/ (exists x : X, (next s).(P) x /\ ~ s.(P) x).

Lemma eventually_exhausted'
  : forall x : X, (Ord.rec base next pair_sup (Hartogs pair)).(P) x.
Proof.
  exploit (InducedOrdinal.BourbakiWittFixedpointTheorem (fun s : pair => good s) pair_le _ _ pair_sup _ _ base _ next); i.
  { ii; reflexivity. }
  { ii; transitivity d2; eauto. }
  { ii; eapply pair_sup_good; eauto. }
  { ii; eapply pair_sup_isSupremum'; eauto. }
  { ii; eapply base_good. }
  { ii; eapply next_good; eauto. }
  { ii; eapply next_extensive; eauto. }
  { ii; eapply next_eq; eauto. }
  hexploit (next_exhausted (Ord.rec base next pair_sup (Hartogs pair))); i.
  - eapply (InducedOrdinal.rec_good); eauto.
    { ii; reflexivity. }
    { ii; transitivity d2; eauto. }
    { ii; eapply pair_sup_good; eauto. }
    { ii; eapply pair_sup_isSupremum'; eauto. }
    { ii; eapply base_good. }
  - des; eauto. exfalso. eapply H0. eapply x0. eauto.
Qed.

Lemma eventually_exhausted
  : exists o : Ord.t, forall x : X, (Ord.rec base next pair_sup o).(P) x.
Proof.
  exists (Hartogs pair). eapply eventually_exhausted'.
Qed.

Lemma well_ordering_aux
  : exists R : X -> X -> Prop, well_founded R /\ (forall x1, forall x2, x1 == x2 \/ R x1 x2 \/ R x2 x1) /\ Transitive R /\ eqPropCompatible2 R.
Proof.
  hexploit eventually_exhausted. intros H_P. des.
  assert (GOOD : good (Ord.rec base next pair_sup o)).
  { exploit (InducedOrdinal.rec_good (fun s : pair => good s) pair_le _ _ pair_sup _ _ base _ next).
    { ii; reflexivity. }
    { ii; transitivity d2; eauto. }
    { ii; eapply pair_sup_good; eauto. }
    { ii; eapply pair_sup_isSupremum'; eauto. }
    { ii; eapply base_good. }
    { ii; eapply next_good; eauto. }
    { ii; eapply next_extensive; eauto. }
    { ii; eapply next_eq; eauto. }
    { intros HH; exact HH. }
  }
  exists (B.transitiveClosure (Ord.rec base next pair_sup o).(R)). destruct GOOD. splits.
  - eapply B.transitiveClosure_lifts_well_founded; eauto.
  - intros x1 x2. unshelve epose proof (COMPLETE x1 x2 _ _) as [H_EQ | [H_LT | H_GT]]; eauto; right; [left | right]; econs 1; eauto.
  - ii; econs 2; eauto.
  - ii. do 2 red. split; intros TC.
    + revert x2 y2 x_EQ y_EQ. induction TC; ii.
      * econs 1. now rewrite <- x_EQ, <- y_EQ.
      * econs 2; [eapply IHTC1 | eapply IHTC2]; eauto; reflexivity.
    + revert x1 y1 x_EQ y_EQ. induction TC; ii.
      * econs 1. now rewrite -> x_EQ, -> y_EQ.
      * econs 2; [eapply IHTC1 | eapply IHTC2]; eauto; reflexivity.
Qed.

End NEXT.

Lemma choice_and_pred_exts_imply_well_ordering `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}
  : exists R : X -> X -> Prop, well_founded R /\ (forall x1, forall x2, x1 == x2 \/ R x1 x2 \/ R x2 x1) /\ Transitive R /\ eqPropCompatible2 R.
Proof.
  assert (exists next : pair -> pair, (forall s : pair, good s -> s =< next s) /\ (forall s : pair, good s -> good (next s)) /\ (forall s : pair, good s -> (forall x : X, s.(P) x) \/ (exists x : X, (next s).(P) x /\ ~ s.(P) x))) as [next H_next].
  { hexploit (Axiom_of_Choice pair (fun _ => pair) (fun x => fun y => forall GOOD : good x, good y /\ x =< y /\ ((forall a, x.(P) a) \/ (exists a, y.(P) a /\ ~ x.(P) a)))).
    - intros d1. pose proof (classic (forall x, P d1 x)) as [YES | NO].
      { exists d1. i. now splits; eauto. }
      { assert (exists x : X, ~ d1.(P) x) as [x0 H].
        { eapply NNPP. intros H_contra. contradiction NO. intros x. eapply NNPP. ii. contradiction H_contra. now exists x. }
        exists {| P x := d1.(P) x \/ x == x0; R x1 x2 := d1.(R) x1 x2 \/ (d1.(P) x1 /\ x2 == x0) |}; simpl.
        i. destruct GOOD. splits.
        - split; ss.
          + i. des; clarify; splits; eauto.
            * left. apply SOUND in LT. des; eauto.
            * left. apply SOUND in LT. des; eauto.
          + i. des; clarify; eauto.
            * pose proof (COMPLETE a b) as [H_EQ | [H_LT | H_GT]]; eauto.
            * left. now rewrite -> IN.
          + assert (forall x, Acc d1.(R) x -> d1.(P) x -> Acc (fun x1 => fun x2 => R d1 x1 x2 \/ P d1 x1 /\ x2 == x0) x).
            { i. revert H1. induction H0. econs. i. des. 
              - eapply H1; eauto. apply SOUND in H3. des; eauto.
              - econs. now rewrite <- H4 in H.
            }
            econs. i. des; clarify.
            * eapply H0.
              { eapply WELL_FOUNDED. }
              { eapply SOUND in H1. des; eauto. }
            * eapply H0; eauto.
          + ii. do 2 red. now rewrite <- x_EQ, <- y_EQ.
          + ii. do 2 red. now rewrite <- x_EQ.
        - econs; ss; eauto. i. split; i; eauto. des; clarify. now rewrite <- H1 in H.
        - i. right. ss. exists x0. split; eauto. now right.
      }
    - i. des. exists f. splits; i; try apply H; eauto.
  }
  des. eapply well_ordering_aux; eauto. intros s1 s2 GOOD1 GOOD2 H_EQ.
  enough (s1 = s2) by now subst s2.
  destruct s1, s2; simpl in *. f_equal.
  - eapply @Functional_Extensionality with (b_fun_ext := true) (f := P0) (f' := P1); eauto. i.
    eapply @Propositional_Extensionality with (b_prop_ext := true) (P := P0 x) (P' := P1 x); eauto.
    firstorder.
  - eapply @Functional_Extensionality with (b_fun_ext := true) (f := R0) (f' := R1); eauto. i.
    eapply @Functional_Extensionality with (b_fun_ext := true) (f := R0 x) (f' := R1 x); eauto. i.
    eapply @Propositional_Extensionality with (b_prop_ext := true) (P := R0 x x0) (P' := R1 x x0); eauto.
    firstorder.
Qed.

End WELL_ORDERING_THEOREM.

Theorem well_ordering_thm `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (X : Type) (SETOID : isSetoid X)
  : exists R : X -> X -> Prop, well_founded R /\ (forall x1, forall x2, x1 == x2 \/ R x1 x2 \/ R x2 x1) /\ Transitive R /\ eqPropCompatible2 R.
Proof.
  pose proof (classic (inhabited X)) as [[x] | NO].
  - eapply choice_and_pred_exts_imply_well_ordering; eauto.
  - exists (fun _ => fun _ => False). splits; ii; contradiction NO; eauto.
Qed.

Section EXTEND_ORDER.

Context {A : Type} {SETOID : isSetoid A} (RT : A -> A -> Prop) (R : A -> A -> Prop).

Hypothesis R_wf : well_founded R.

Definition extendedOrder (x1 : A) (x2 : A) : Prop :=
  fromWf R R_wf x1 <ᵣ fromWf R R_wf x2 \/ (fromWf R R_wf x1 =ᵣ fromWf R R_wf x2 /\ RT x1 x2).

Hypothesis RT_wf : well_founded RT.

Hypothesis TOTAL : forall x1 : A, forall x2 : A, x1 == x2 \/ RT x1 x2 \/ RT x2 x1.

Lemma extendedOrder_total x1 x2
  : x1 == x2 \/ extendedOrder x1 x2 \/ extendedOrder x2 x1.
Proof.
  pose proof (O.wlt_trichotomous (classic := classic) (WOSET := rLt_isWellOrdering) (fromWf R R_wf x1) (fromWf R R_wf x2)) as [H_EQ | [H_LT | H_GT]].
  - pose proof (@TOTAL x1 x2) as [H_EQ' | [H_LT' | H_GT']]; eauto.
    + right. left. right. split; eauto with *.
    + right. right. right. split; eauto with *.
  - right. left. left. eauto.
  - right. right. left. eauto.
Qed.

Lemma extendedOrder_well_founded
  : well_founded extendedOrder.
Proof.
  ii.
  enough (forall o : Tree, forall LE : fromWf R R_wf a ≦ᵣ o, Acc extendedOrder a) as WTS.
  { eapply WTS with (o := fromWfSet R R_wf). eapply rLt_implies_rLe. econs. exists a. reflexivity. }
  intros o. revert a. induction (rLt_wf o) as [o _ IH].
  assert (LTS : forall a : A, forall LT : fromWf R R_wf a <ᵣ o, Acc extendedOrder a).
  { i. econs. i.
    hexploit (IH _ LT).
    - reflexivity.
    - i. inv H0. eauto.
  }
  ii. rewrite InducedOrdinal.rLe_iff_rLt_or_rEq in LE. des; eauto.
  induction (RT_wf a) as [a _ IH']. econs. i. inv H.
  - eapply IH with (y := fromWf R R_wf y).
    + now rewrite <- LE.
    + reflexivity.
  - des. eapply IH'; eauto. transitivity (fromWf R R_wf a); eauto.
Qed.

Lemma extendedOrder_incl x1 x2
  (LT : R x1 x2)
  : extendedOrder x1 x2.
Proof.
  left. eapply member_implies_rLt. rewrite fromWf_unfold. now exists x1; split.
Qed.

#[local]
Instance extendedOrder_Transitive
  (RT_Transitive : Transitive RT)
  : Transitive extendedOrder.
Proof.
  intros x y z. unfold extendedOrder; ii; des.
  - left. now rewrite H.
  - left. now rewrite H.
  - left. now rewrite <- H0.
  - right. split; [rewrite <- H0 | transitivity y]; eauto.
Qed.

End EXTEND_ORDER.

Lemma extendedOrder_exists `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (A : Type) (SETOID : isSetoid A) (R : A -> A -> Prop)
  (R_wf : well_founded R)
  : exists R' : A -> A -> Prop, ⟪ WF : well_founded R' ⟫ /\ ⟪ INCL : forall x : A, forall x' : A, forall LT : R x x', R' x x' ⟫ /\ ⟪ TOTAL : forall x : A, forall x' : A, x == x' \/ R' x x' \/ R' x' x ⟫ /\ ⟪ TRANSITIVE : Transitive R' ⟫.
Proof.
  hexploit (well_ordering_thm A SETOID); eauto.
  intros (R1 & R1_wf & R1_total & R1_Transitive & R1_eqPropCompatible2).
  exists (extendedOrder R1 R R_wf); splits; ii.
  - eapply @extendedOrder_well_founded; eauto.
  - eapply @extendedOrder_incl; eauto.
  - eapply @extendedOrder_total with (SETOID := SETOID); eauto.
  - eapply @extendedOrder_Transitive; eauto.
Qed.

Lemma fromWfSet_comparable `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (A : Type) (B : Type) (A_isSetoid : isSetoid A) (B_isSetoid : isSetoid B) (RA : A -> A -> Prop) (RB : B -> B -> Prop)
  (WFA : well_founded RA)
  (WFB : well_founded RB)
  (RA_eqPropCompatible2 : eqPropCompatible2 RA)
  (RB_eqPropCompatible2 : eqPropCompatible2 RB)
  (RA_Transitive : Transitive RA)
  (RB_Transitive : Transitive RB)
  (TOTALA : forall x1 : A, forall x2 : A, x1 == x2 \/ (RA x1 x2 \/ RA x2 x1))
  (TOTALB : forall y1 : B, forall y2 : B, y1 == y2 \/ (RB y1 y2 \/ RB y2 y1))
  : ⟪ LE : exists f : A -> B, forall x1 : A, forall x2 : A, RA x1 x2 <-> RB (f x1) (f x2) ⟫ \/ ⟪ GE : exists g : B -> A, forall y1 : B, forall y2 : B, RB y1 y2 <-> RA (g y1) (g y2) ⟫.
Proof.
  pose proof (InducedOrdinal.rLe_total (fromWfSet RA WFA) (fromWfSet RB WFB)) as [H_LE | H_GE].
  - left. eapply fromWfSet_embed'; eauto.
  - right. eapply fromWfSet_embed'; eauto.
Qed.

Theorem compareSetoids `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (A : Type@{Set_u}) (B : Type@{Set_u}) (A_isSetoid : isSetoid A) (B_isSetoid : isSetoid B)
  : ⟪ card_LE : exists f : A -> B, forall x1 : A, forall x2 : A, x1 == x2 <-> f x1 == f x2 ⟫ \/ ⟪ card_GE : exists g : B -> A, forall y1 : B, forall y2 : B, y1 == y2 <-> g y1 == g y2 ⟫.
Proof.
  hexploit (@well_ordering_thm Axms A A_isSetoid); eauto; i; des.
  hexploit (@well_ordering_thm Axms B B_isSetoid); eauto; i; des.
  hexploit (fromWfSet_comparable A B A_isSetoid B_isSetoid); eauto; i; des.
  - left. exists f; i; split; i.
    + pose proof (H4 (f x1) (f x2)); des; eauto.
      * rewrite <- LE in H8. rewrite H7 in H8. exfalso.
        eapply well_founded_implies_Irreflexive with (R := R0); eauto.
      * rewrite <- LE in H8. rewrite H7 in H8. exfalso.
        eapply well_founded_implies_Irreflexive with (R := R0); eauto.
    + pose proof (H0 x1 x2); des; eauto.
      * rewrite -> LE in H8. rewrite H7 in H8. exfalso.
        eapply well_founded_implies_Irreflexive with (R := R1); eauto.
      * rewrite -> LE in H8. rewrite H7 in H8. exfalso.
        eapply well_founded_implies_Irreflexive with (R := R1); eauto.
  - right. exists g; i; split; i.
    + pose proof (H0 (g y1) (g y2)); des; eauto.
      * rewrite <- GE in H8. rewrite H7 in H8. exfalso.
        eapply well_founded_implies_Irreflexive with (R := R1); eauto.
      * rewrite <- GE in H8. rewrite H7 in H8. exfalso.
        eapply well_founded_implies_Irreflexive with (R := R1); eauto.
    + pose proof (H4 y1 y2); des; eauto.
      * rewrite -> GE in H8. rewrite H7 in H8. exfalso.
        eapply well_founded_implies_Irreflexive with (R := R0); eauto.
      * rewrite -> GE in H8. rewrite H7 in H8. exfalso.
        eapply well_founded_implies_Irreflexive with (R := R0); eauto.
Qed.

Reserved Infix "`hasCardinality`" (no associativity, at level 70).

Definition hasCardinality (kappa : Cardinality.t) (c : Tree) : Prop :=
  let P (alpha : Tree) : Prop := exists R : kappa.(Cardinality.carrier) -> kappa.(Cardinality.carrier) -> Prop, exists R_wf : well_founded R, (forall x, forall x', x == x' \/ R x x' \/ R x' x) /\ Transitive R /\ eqPropCompatible2 R /\ fromWfSet R R_wf == alpha in
  P c /\ (forall alpha : Tree, P alpha -> c ≦ᵣ alpha).

Infix "`hasCardinality`" := hasCardinality.

Section CARDINALITY.

#[local] Infix "\in" := member.
#[local] Infix "\subseteq" := isSubsetOf.

Section CARDINAL.

Context `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t).

Theorem hasCardinality_intro
  : kappa `hasCardinality` Cardinality.toTree kappa.
Proof using Axms kappa.
  hexploit (well_ordering_thm kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid)); eauto.
  intros (R0 & R0_wf & R0_total & R0_Transitive & R0_eqPropCompatible2).
  set (WPOSET := {| wltProp := R0; wltProp_Transitive := R0_Transitive; wltProp_well_founded := R0_wf; |}).
  set (WOSET := @O.WellfoundedToset_isWoset classic kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) WPOSET R0_eqPropCompatible2 R0_total).
  red. set (P := fun alpha : Tree => exists R : kappa.(Cardinality.carrier) -> kappa.(Cardinality.carrier) -> Prop, exists R_wf : well_founded R, (forall x, forall x', x == x' \/ R x x' \/ R x' x) /\ Transitive R /\ eqPropCompatible2 R /\ fromWfSet R R_wf == alpha).
  exploit (@O.minimisation_lemma classic _ _ rLt_isWellOrdering P).
  { exists (@FromOrderType _ _ WOSET). red. exists R0, R0_wf. splits; eauto. unfold FromOrderType. reflexivity. }
  intros (c & H_c & MIN); unnw. red in H_c. destruct H_c as (R & R_wf & R_total & R_Transitive & R_eqPropCompatible2 & H_c). split.
  { exists R, R_wf. splits; eauto. eapply extensionality. intros z; split; intros z_in.
    - unfold Cardinality.toTree. rewrite unions_spec. exists (fromWfSet R R_wf). split; eauto.
      rewrite filter_spec. simpl children. exists (B.exist R (conj R_wf (conj R_total (conj R_Transitive R_eqPropCompatible2)))). split.
      + intros WOSET'. simpl. rewrite proof_irrelevance with (p1 := proj1 _) (p2 := R_wf). rewrite InducedOrdinal.rLe_iff_rLt_or_rEq.
        rewrite -> H_c. eapply MIN. red. exists WOSET'.(Woset_isWellPoset).(wltProp), WOSET'.(Woset_isWellPoset).(wltProp_well_founded).
        split. { unshelve eapply O.wlt_trichotomous. exact classic. }
        split. { exact WOSET'.(Woset_isWellPoset).(wltProp_Transitive). }
        split. { exact WOSET'.(Woset_eqPropCompatible2). }
        reflexivity.
      + simpl childnodes. rewrite proof_irrelevance with (p1 := proj1 _) (p2 := R_wf). reflexivity.
    - unfold Cardinality.toTree in z_in. rewrite unions_spec in z_in. destruct z_in as (y & z_in & y_in).
      rewrite filter_spec in y_in. simpl children in y_in. destruct y_in as (i & H_i & y_eq). simpl childnodes in H_i, y_eq.
      rewrite y_eq in z_in. clear y y_eq.
      enough (fromWfSet R R_wf == fromWfSet (B.proj1_sig i) (proj1 (B.proj2_sig i))) as WTS by now rewrite WTS.
      set (WPOSET' := {| wltProp := R; wltProp_Transitive := R_Transitive; wltProp_well_founded := R_wf; |}).
      set (WOSET' := @O.WellfoundedToset_isWoset classic kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) WPOSET' R_eqPropCompatible2 R_total).
      set (WPOSET'' := {| wltProp := i.(B.proj1_sig); wltProp_Transitive := proj1 (proj2 (proj2 (i.(B.proj2_sig)))); wltProp_well_founded := proj1 (i.(B.proj2_sig)); |}).
      set (WOSET'' := @O.WellfoundedToset_isWoset classic kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) WPOSET'' (proj2 (proj2 (proj2 (i.(B.proj2_sig))))) (proj1 (proj2 (i.(B.proj2_sig))))).
      eapply Ordinal1.Ordinal_rEq_Ordinal_elim.
      { change (isOrdinal (@FromOrderType _ _ WOSET')). eapply FromOrderType_isOrdinal. }
      { change (isOrdinal (@FromOrderType _ _ WOSET'')). eapply FromOrderType_isOrdinal. }
      split.
      + rewrite -> H_c. rewrite InducedOrdinal.rLe_iff_rLt_or_rEq. eapply MIN. red. exists (B.proj1_sig i), (proj1 (B.proj2_sig i)).
        split. { exact (proj1 (proj2 (i.(B.proj2_sig)))). }
        split. { exact (proj1 (proj2 (proj2 i.(B.proj2_sig)))). }
        split. { exact (proj2 (proj2 (proj2 i.(B.proj2_sig)))). }
        reflexivity.
      + exact (H_i WOSET').
  }
  { intros alpha (R1 & R1_wf & R1_total & R1_Transitive & R1_eqPropCompatible2 & H_alpha).
    rewrite <- H_alpha. unfold Cardinality.toTree. eapply unions_rLe_intro. intros x x_in.
    rewrite filter_spec in x_in. simpl children in x_in; simpl childnodes in x_in.
    destruct x_in as (i & H_i & H_x). rewrite H_x. clear x H_x.
    set (WPOSET' := {| wltProp := R1; wltProp_Transitive := R1_Transitive; wltProp_well_founded := R1_wf; |}).
    set (WOSET' := @O.WellfoundedToset_isWoset classic kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) WPOSET' R1_eqPropCompatible2 R1_total).
    exact (H_i WOSET').
  }
Qed.

Lemma hasCardinality_isOrdinal c
  (CARDINAL : kappa `hasCardinality` c)
  : isOrdinal c.
Proof using kappa.
  destruct CARDINAL as [(R & R_wf & R_total & R_Transitive & R_eqPropCompatible2 & H_c) MIN]. rewrite <- H_c.
  set (WPOSET' := {| wltProp := R; wltProp_Transitive := R_Transitive; wltProp_well_founded := R_wf; |}).
  set (WOSET' := @O.WellfoundedToset_isWoset classic kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) WPOSET' R_eqPropCompatible2 R_total).
  change (isOrdinal (@FromOrderType _ _ WOSET')). eapply FromOrderType_isOrdinal.
Qed.

Lemma hasCardinality_unique c c'
  (CARDINAL : kappa `hasCardinality` c)
  (CARDINAL' : kappa `hasCardinality` c')
  : c == c'.
Proof using kappa.
  eapply Ordinal1.Ordinal_rEq_Ordinal_elim.
  - eapply hasCardinality_isOrdinal; eauto.
  - eapply hasCardinality_isOrdinal; eauto.
  - destruct CARDINAL as [R MIN]. destruct CARDINAL' as [R' MIN']. split.
    + eapply MIN; eauto.
    + eapply MIN'; eauto.
Qed.

Lemma hasCardinality_rewrite_r (c : Tree) (c' : Tree)
  (EQ : c == c')
  (CARDINAL : kappa `hasCardinality` c)
  : kappa `hasCardinality` c'.
Proof.
  destruct CARDINAL as [(R & R_wf & R_total & R_Transitive & R_eqPropCompatible2 & H_R) MIN]. split.
  - exists R, R_wf. splits; eauto. now rewrite <- EQ.
  - intros alpha (R1 & R1_wf & R1_total & R1_Transitive & R1_eqPropCompatible2 & H_R1).
    rewrite <- EQ. eapply MIN. exists R1, R1_wf. splits; eauto.
Qed.

End CARDINAL.

#[local] Hint Resolve hasCardinality_intro hasCardinality_isOrdinal : core.

Lemma Cardinality_le_total `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} kappa kappa'
  : kappa =< kappa' \/ kappa' =< kappa.
Proof.
  hexploit (compareSetoids kappa.(Cardinality.carrier) kappa'.(Cardinality.carrier)); i. des; [left | right]; [exists f | exists g]; firstorder.
Qed.

Lemma Cardinality_lowerbound `{Axms : ClassicalAxioms (b_AC := true)} kappa R
  (R_wf : well_founded R)
  (R_total : forall x : kappa.(Cardinality.carrier), forall x' : kappa.(Cardinality.carrier), x == x' \/ R x x' \/ R x' x)
  (R_Transitive : Transitive R)
  (R_eqPropCompatible2 : eqPropCompatible2 R)
  : Cardinality.toTree kappa ≦ᵣ fromWfSet R R_wf.
Proof.
  unfold Cardinality.toTree. eapply unions_rLe_intro. intros x x_in.
  rewrite filter_spec in x_in. destruct x_in as [i [H_i H_x]]; simpl in *.
  set (WPOSET := {| wltProp := R; wltProp_Transitive := R_Transitive; wltProp_well_founded := R_wf; |}).
  set (WOSET := @O.WellfoundedToset_isWoset classic kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) WPOSET R_eqPropCompatible2 R_total).
  rewrite H_x. exact (H_i WOSET).
Qed.

Lemma Cardinality_le_elim `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t) (kappa' : Cardinality.t)
  (H_cLe : kappa =< kappa')
  : Cardinality.toTree kappa ≦ᵣ Cardinality.toTree kappa'.
Proof.
  hexploit (hasCardinality_intro kappa'); intros [(R & R_wf & R_total & R_Transitive & R_eqPropCompatible2 & H_kappa') MIN].
  rewrite <- H_kappa'. inversion H_cLe. 
  pose proof (R1_wf := WfHelper.ProjectedRelRev_wf _ _ R f R_wf).
  set (R1 := WfHelper.ProjectedRelRev R f) in *.
  transitivity (fromWfSet R1 R1_wf).
  - eapply hasCardinality_intro. exists R1, R1_wf.
    set (WPOSET' := {| wltProp := R; wltProp_Transitive := R_Transitive; wltProp_well_founded := R_wf; |}).
    set (WOSET' := @O.WellfoundedToset_isWoset classic kappa'.(Cardinality.carrier) kappa'.(Cardinality.carrier_isSetoid) WPOSET' R_eqPropCompatible2 R_total).
    unfold R1. splits; eauto with *.
    + intros x x'. pose proof (@O.wlt_trichotomous classic kappa'.(Cardinality.carrier) kappa'.(Cardinality.carrier_isSetoid) WOSET' (f x) (f x')) as [H_EQ | [H_LT | H_GT]].
      * left. now eapply f_inj.
      * right. left. eauto.
      * right. right. eauto.
    + intros x x' x'' H_LT H_LT'. eapply R_Transitive with (y := f x'); eauto.
    + ii. change (R (f x1) (f y1) <-> R (f x2) (f y2)).
      pose proof (f_cong _ _ x_EQ) as f_x_EQ.
      pose proof (f_cong _ _ y_EQ) as f_y_EQ.
      now rewrite f_x_EQ, f_y_EQ.
  - eapply fromWfSet_cong with (f := f). eauto.
Qed.

Lemma Cardinality_upperbound `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t) (kappa' : Cardinality.t) (R : kappa'.(Cardinality.carrier) -> kappa'.(Cardinality.carrier) -> Prop)
  (H_cLt : kappa' ≨ kappa)
  (R_wf : well_founded R)
  (R_total : forall x, forall x', x == x' \/ R x x' \/ R x' x)
  (R_Transitive : Transitive R)
  (R_eqPropCompatible2 : eqPropCompatible2 R)
  : fromWfSet R R_wf <ᵣ Cardinality.toTree kappa.
Proof.
  assert (H_cLt' : ~ kappa =< kappa').
  { intros [f ? ?]. destruct H_cLt as [[g ? ?] NE]. contradiction NE. exists g f; eauto. }
  hexploit (well_ordering_thm kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid)); eauto.
  intros (R0 & R0_wf & R0_total & R0_Transitive & R0_eqPropCompatible2).
  set (WPOSET := {| wltProp := R0; wltProp_Transitive := R0_Transitive; wltProp_well_founded := R0_wf; |}).
  set (WOSET := @O.WellfoundedToset_isWoset classic kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) WPOSET R0_eqPropCompatible2 R0_total).
  set (P := fun alpha : Tree => exists R : kappa.(Cardinality.carrier) -> kappa.(Cardinality.carrier) -> Prop, exists R_wf : well_founded R, (forall x, forall x', x == x' \/ R x x' \/ R x' x) /\ Transitive R /\ eqPropCompatible2 R /\ fromWfSet R R_wf == alpha).
  exploit (@O.minimisation_lemma classic _ _ rLt_isWellOrdering P).
  { exists (@FromOrderType _ _ WOSET). red. exists R0, R0_wf. splits; eauto. unfold FromOrderType. reflexivity. }
  intros (c & H_c & MIN); unnw. red in H_c. destruct H_c as (R1 & R1_wf & R1_total & R1_Transitive & R1_eqPropCompatible2 & H_c).
  unfold Cardinality.toTree. rewrite rLt_unions_iff. exists (fromWfSet R1 R1_wf). rewrite filter_spec. split.
  { unshelve eexists (B.exist R1 _).
    - splits; eauto.
    - split.
      + intros WOSET'. simpl. rewrite proof_irrelevance with (p1 := proj1 _) (p2 := R1_wf). rewrite -> H_c. rewrite InducedOrdinal.rLe_iff_rLt_or_rEq.
        eapply MIN. exists WOSET'.(Woset_isWellPoset).(wltProp), WOSET'.(Woset_isWellPoset).(wltProp_well_founded).
        split. { unshelve eapply O.wlt_trichotomous. exact classic. }
        split. { exact WOSET'.(Woset_isWellPoset).(wltProp_Transitive). }
        split. { exact WOSET'.(Woset_eqPropCompatible2). }
        reflexivity.
      + simpl childnodes. now rewrite proof_irrelevance with (p1 := proj1 _) (p2 := R1_wf).
  }
  eapply NNPP. intros H_contra.
  assert (SUBSET : fromWfSet R1 R1_wf \subseteq fromWfSet R R_wf).
  { eapply Ordinal1.Ordinal_rLe_Ordinal_elim.
    - set (WPOSET' := {| wltProp := R1; wltProp_Transitive := R1_Transitive; wltProp_well_founded := R1_wf; |}).
      set (WOSET' := @O.WellfoundedToset_isWoset classic kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) WPOSET' R1_eqPropCompatible2 R1_total).
      change (isOrdinal (@FromOrderType _ _ WOSET')). eapply FromOrderType_isOrdinal.
    - set (WPOSET' := {| wltProp := R; wltProp_Transitive := R_Transitive; wltProp_well_founded := R_wf; |}).
      set (WOSET' := @O.WellfoundedToset_isWoset classic kappa'.(Cardinality.carrier) kappa'.(Cardinality.carrier_isSetoid) WPOSET' R_eqPropCompatible2 R_total).
      change (isOrdinal (@FromOrderType _ _ WOSET')). eapply FromOrderType_isOrdinal.
    - pose proof (InducedOrdinal.rLe_or_rGt (fromWfSet R1 R1_wf) (fromWfSet R R_wf)) as [H | H]; [exact H | contradiction H].
  }
  hexploit (fromWfSet_comparable _ _ _ _ R1 R); eauto. i; des.
  - contradiction H_cLt'. exists f.
    + intros x1 x2 x_EQ. pose proof (R_total (f x1) (f x2)) as [H_EQ | [H_LT | H_GT]]; eauto.
      * rewrite <- LE in H_LT. exploit (well_founded_implies_Irreflexive' R1 R1_wf _ x1 x2); eauto.
        { intros a a' EQ b. now rewrite <- EQ. }
        intros H_not. contradiction H_not.
      * rewrite <- LE in H_GT. symmetry in x_EQ. exploit (well_founded_implies_Irreflexive' R1 R1_wf _ x2 x1); eauto.
        { intros a a' EQ b. now rewrite <- EQ. }
        intros H_not. contradiction H_not.
    + intros x1 x2 x_EQ. pose proof (R1_total x1 x2) as [H_EQ | [H_LT | H_GT]]; eauto.
      * rewrite -> LE in H_LT. exploit (well_founded_implies_Irreflexive' R R_wf _ (f x1) (f x2)); eauto.
        { intros a a' EQ b. now rewrite <- EQ. }
        intros H_not. contradiction H_not.
      * rewrite -> LE in H_GT. symmetry in x_EQ. exploit (well_founded_implies_Irreflexive' R R_wf _ (f x2) (f x1)); eauto.
        { intros a a' EQ b. now rewrite <- EQ. }
        intros H_not. contradiction H_not.
  - assert (fromWfSet R R_wf ≦ᵣ fromWfSet R1 R1_wf) as claim1.
    { eapply fromWfSet_cong with (f := g); firstorder. }
    assert (fromWfSet R1 R1_wf ≦ᵣ fromWfSet R R_wf) as claim2.
    { eapply subseteq_implies_rLe; eauto. }
    assert (fromWfSet R R_wf =ᵣ fromWfSet R1 R1_wf) as claim3.
    { split; eauto. }
    assert (claim4 : forall h : kappa.(Cardinality.carrier) -> kappa'.(Cardinality.carrier), eqPropCompatible1 h -> (exists x1, exists x2, h x1 == h x2 /\ ~ x1 == x2)).
    { ii. eapply NNPP. intros H_not. contradiction H_cLt'.
      assert (HH : exists h : Cardinality.carrier kappa -> Cardinality.carrier kappa', eqPropCompatible1 h /\ (forall x1, forall x2, h x1 == h x2 -> x1 == x2)).
      { eapply NNPP. intros H_not1. contradiction H_not. eapply NNPP. intros H_not'.
        contradiction H_not1. exists h. split; trivial. ii. eapply NNPP. ii. contradiction H_not'. exists x1, x2. split; eauto.
      }
      clear h H H_not. destruct HH as [h [h_cong h_inj]]. exists h; eauto.
    }
    set (WPOSET0 := {| wltProp := R; wltProp_Transitive := R_Transitive; wltProp_well_founded := R_wf; |}).
    set (WOSET0 := @O.WellfoundedToset_isWoset classic kappa'.(Cardinality.carrier) kappa'.(Cardinality.carrier_isSetoid) WPOSET0 R_eqPropCompatible2 R_total).
    set (WPOSET1 := {| wltProp := R1; wltProp_Transitive := R1_Transitive; wltProp_well_founded := R1_wf; |}).
    set (WOSET1 := @O.WellfoundedToset_isWoset classic kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) WPOSET1 R1_eqPropCompatible2 R1_total).
    assert (claim5 : fromWfSet R R_wf == fromWfSet R1 R1_wf).
    { eapply Ordinal1.Ordinal_rEq_Ordinal_elim.
      - change (isOrdinal (@FromOrderType _ _ WOSET0)). eapply FromOrderType_isOrdinal.
      - change (isOrdinal (@FromOrderType _ _ WOSET1)). eapply FromOrderType_isOrdinal.
      - exact claim3.
    }
    assert (exists f, forall x, fromWf R R_wf (f x) == fromWf R1 R1_wf x) as [h claim6].
    { destruct claim5 as [_ H]. exploit (Axiom_of_Choice (Cardinality.carrier kappa) (fun _ => Cardinality.carrier kappa')).
      - intros x. pose proof (H x) as [y H_y]. exists y. exact H_y.
      - eauto.
    }
    assert (claim7 : forall x, forall x', x == x' <-> h x == h x').
    { clear WPOSET WOSET. intros x x'; split; intros H_EQ.
      - pose proof (COPY := H_EQ). rewrite <- fromOrderType_eq_fromOrderType_iff in H_EQ.
        change (fromWf R1 R1_wf x == fromWf R1 R1_wf x') in H_EQ. do 2 rewrite <- claim6 in H_EQ.
        rewrite <- fromOrderType_eq_fromOrderType_iff. exact H_EQ.
      - pose proof (COPY := H_EQ). rewrite <- fromOrderType_eq_fromOrderType_iff in H_EQ.
        change (fromWf R R_wf (h x) == fromWf R R_wf (h x')) in H_EQ. do 2 rewrite -> claim6 in H_EQ.
        rewrite <- fromOrderType_eq_fromOrderType_iff. exact H_EQ.
    }
    exploit (claim4 h).
    { ii. now rewrite <- claim7. }
    intros (x1 & x2 & H_EQ & H_NE). now rewrite <- claim7 in H_EQ.
Qed.

Theorem Cardinality_le_iff `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} kappa kappa'
  : kappa =< kappa' <-> Cardinality.toTree kappa ≦ᵣ Cardinality.toTree kappa'.
Proof.
  split.
  - eapply Cardinality_le_elim. 
  - hexploit (hasCardinality_intro kappa'). intros [(R & R_wf & R_total & R_Transitive & R_eqPropCompatible2 & H_kappa') MIN] H_rLe.
    eapply NNPP. intros H_contra. pose proof (Cardinality_le_total kappa kappa') as [H_cLe | H_cGe]; eauto.
    pose proof (Cardinality_le_elim kappa' kappa H_cGe) as H_rGe.
    assert (theSameCardinality : Cardinality.toTree kappa == Cardinality.toTree kappa').
    { eapply Ordinal1.Ordinal_rEq_Ordinal_elim; eauto. split; eauto. }
    assert (kappa_hasCardinality : kappa `hasCardinality` Cardinality.toTree kappa').
    { eapply hasCardinality_rewrite_r; eauto with *. }
    unshelve hexploit (Cardinality_upperbound kappa kappa' R); eauto.
    + split; eauto. intros [? ? ? ? ? ?]. contradiction H_contra. exists g; eauto.
    + intros H_rLt. rewrite H_kappa' in H_rLt. rewrite <- theSameCardinality in H_rLt.
      contradiction (well_founded_implies_Irreflexive rLt rLt_wf (Cardinality.toTree kappa) H_rLt).
Qed.

Theorem Cardinality_eq_iff `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} kappa kappa'
  : kappa == kappa' <-> Cardinality.toTree kappa =ᵣ Cardinality.toTree kappa'.
Proof.
  split; i.
  - destruct H. split; eapply Cardinality_le_iff.
    + exists f; eauto.
    + exists g; eauto.
  - enough (kappa =< kappa' /\ kappa' =< kappa) as [[f ? ?] [g ? ?]].
    { exists f g; eauto. }
    split; rewrite Cardinality_le_iff; eapply H. 
Qed.

Theorem Cardinality_lt_iff `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} kappa kappa'
  : kappa ≨ kappa' <-> Cardinality.toTree kappa <ᵣ Cardinality.toTree kappa'.
Proof.
  split.
  - intros [LE NE]. rewrite Cardinality_le_iff in LE.
    change (~ kappa == kappa') in NE. rewrite Cardinality_eq_iff in NE.
    rewrite InducedOrdinal.rLe_iff_rLt_or_rEq in LE.
    destruct LE; eauto. contradiction.
  - intros H_rLe. split.
    + rewrite Cardinality_le_iff. now eapply rLt_implies_rLe.
    + rewrite Cardinality_eq_iff. intros H_EQ. rewrite H_EQ in H_rLe.
      contradiction (well_founded_implies_Irreflexive rLt rLt_wf (Cardinality.toTree kappa')).
Qed.

End CARDINALITY.
