Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Data.Aczel.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Math.SetTheory.
Require Import PnV.Data.Vector.
Require Import PnV.Math.ThN.

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

Section CHILDREN_ORDERTYPE.

#[local] Infix "\in" := member.

#[local] Existing Instance children_isSetoid.

#[local] Existing Instance children_isWellPoset.

#[local] Existing Instance children_isWoset.

Lemma fromOrderType_children_eq (alpha : Tree) (c : children alpha)
  (ORDINAL : isOrdinal alpha)
  : @fromOrderType (children alpha) (children_isSetoid alpha) (children_isWoset alpha ORDINAL) c == childnodes alpha c.
Proof.
  pose proof (proj1 (isOrdinal_iff1 alpha) ORDINAL) as Hord.
  pose proof (proj1 Hord) as TRANSITIVE.
  pose proof (proj1 (proj2 Hord)) as H_wf.
  induction (H_wf c) as [c _ IH]. eapply extensionality; intros z; split; intros H_in.
  - unfold fromOrderType in H_in. rewrite fromWf_unfold in H_in. destruct H_in as (d & Hdc & z_eq).
    rewrite z_eq. eapply eqProp_member_member; eauto.
  - assert (H_in_alpha : z \in alpha).
    { eapply TRANSITIVE with (y := childnodes alpha c); eauto with *. }
    destruct H_in_alpha as [d z_eq].
    assert (Hdc : isElemOf alpha d c).
    { unfold isElemOf. rewrite <- z_eq; eauto with *. }
    rewrite -> z_eq. rewrite <- IH; auto.
    now rewrite fromOrderType_in_fromOrderType_iff.
Qed.

Lemma FromOrderType_children_id (alpha : Tree)
  (ORDINAL : isOrdinal alpha)
  : @FromOrderType (children alpha) (children_isSetoid alpha) (children_isWoset alpha ORDINAL) == alpha.
Proof.
  eapply extensionality; intros z; split; intros H_in.
  - rewrite FromOrderType_spec in H_in. destruct H_in as [c z_eq].
    rewrite z_eq. rewrite fromOrderType_children_eq. eauto with *.
  - destruct H_in as [c z_eq]. rewrite FromOrderType_spec. exists c.
    rewrite z_eq. symmetry. eapply fromOrderType_children_eq.
Qed.

End CHILDREN_ORDERTYPE.

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

Fixpoint fromAcc_complete (A : Type) (R : A -> A -> Prop) (x : A) (H_ACC : Acc R x) (o : Tree) (LT : o <ᵣ @fromAcc A R x H_ACC) {struct H_ACC} : exists x' : A, exists H_ACC' : Acc R x', o =ᵣ @fromAcc A R x' H_ACC'.
Proof.
  destruct H_ACC as [H_ACC_inv]; simpl in *. destruct LT as [[[c R_c_x] LE]]; simpl in *.
  rewrite rLe_iff_rLt_or_rEq in LE. destruct LE as [LT | EQ].
  - eapply fromAcc_complete. exact LT.
  - exists c. exists (H_ACC_inv c R_c_x). exact EQ.
Qed.

Fixpoint fromAcc_complete1 (A : Type) (R : A -> A -> Prop) (R_trans : Transitive R) (x : A) (H_ACC : Acc R x) (o : Tree) (LT : o <ᵣ @fromAcc A R x H_ACC) {struct H_ACC} : exists x' : A, exists H_ACC' : Acc R x', o =ᵣ @fromAcc A R x' H_ACC' /\ R x' x.
Proof.
  destruct H_ACC as [H_ACC_inv]; simpl in *. destruct LT as [[[c R_c_x] LE]]; simpl in *.
  rewrite rLe_iff_rLt_or_rEq in LE. destruct LE as [LT | EQ].
  - pose proof (fromAcc_complete1 A R R_trans _ (H_ACC_inv c R_c_x) o LT) as (x' & H_ACC' & H_EQ & R_c_x').
    exists x'. exists H_ACC'. split; [exact H_EQ | now transitivity c].
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
  exists o'. econs; eauto. intros beta H_in. rewrite rLe_iff_rLt_or_rEq. now eapply MIN.
Qed.

Definition approx (alpha : Tree) : Prop :=
  forall c1 : children alpha, exists c2 : children alpha, childnodes alpha c1 <ᵣ childnodes alpha c2.

Lemma limit_or_succ (alpha : Tree)
  : ⟪ LIMIT : (alpha =ᵣ unions alpha) /\ (approx alpha) ⟫ \/ ⟪ SUCC : (exists beta : Tree, alpha =ᵣ succ beta) /\ (~ approx alpha) ⟫.
Proof.
  unnw. unfold approx. destruct alpha as [cs ts]; simpl. pose proof (classic (forall c, exists c', ts c <ᵣ ts c')) as [YES | NO].
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
  (P_lim' : forall o, forall I : Type, ⟪ INHABITED : inhabited I ⟫ -> forall alpha : I -> Tree, ⟪ IH : forall i, P (alpha i) ⟫ -> forall LIMIT : o =ᵣ @indexed_union I alpha, ⟪ APPROX : forall i1 : I, exists i2 : I, alpha i1 <ᵣ alpha i2 ⟫ -> P o)
  : forall o : Tree, P o.
Proof.
  intros o. pose proof (rLt_wf o) as H_ACC. induction H_ACC as [o _ IH]. pose proof (limit_or_succ o) as [[LIMIT APPROX] | [SUCC _]]; unnw.
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
  rename o into t. pose proof (rLt_wf t) as H_ACC. induction H_ACC as [t _ IH]. destruct t as [cs ts]; simpl.
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
      - destruct YES as [c']. left. eapply dle_trans with (d2 := next (rec (ts' c'))); auto.
        + eapply dle_trans with (d2 := rec (ts' c')); auto.
          * eapply IH; eauto.
          * eapply IH; eauto.
          * eapply next_extensive. eapply IH; eauto.
        + eapply djoin_upperbound with (ds := fun c' : cs' => next (rec (ts' c'))); eauto.
      - right. eapply djoin_supremum; auto. intros c'. contradiction NO. econs. exact c'.
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
    rewrite -> djoin_supremum; auto. destruct i; auto. simpl. eapply djoin_supremum; i; auto.
    unfold x. eapply dle_trans with (d2 := djoin cs' (fun c' => next (rec (ts' c')))); auto.
    - eapply djoin_upperbound with (ds := fun c' : cs' => next (rec (ts' c'))); eauto.
    - eapply djoin_supremum; auto. intros c'. pose proof (H_rLt c') as [[c H_rLe]]; simpl in *.
      rewrite rLe_iff_rLt_or_rEq in H_rLe. destruct H_rLe as [H_LT | H_EQ].
      + eapply dle_trans with (d2 := next (rec (ts c))); auto.
        { eapply dle_trans with (d2 := rec (ts c)); auto.
          - eapply IH; eauto.
          - eapply IH; eauto.
          - eapply next_extensive; auto. eapply IH; eauto.
        }
        { unfold f. eapply dle_trans with (d2 := djoin cs (fun i : cs => next (rec (ts i)))); auto.
          - eapply djoin_upperbound with (ds := fun c : cs => next (rec (ts c))); eauto.
          - eapply djoin_upperbound with (ds := f cs ts) (i := false); eauto.
        }
      + eapply dle_trans with (d2 := next (rec (ts c))); eauto.
        { eapply next_congruence.
          - eapply IH; eauto.
          - eapply IH; eauto.
          - destruct H_EQ as [H_LE1 H_LE2]. split; eapply IH; eauto.
        }
        { unfold f. eapply dle_trans with (d2 := djoin cs (fun i : cs => next (rec (ts i)))); auto.
          - eapply djoin_upperbound with (ds := fun c : cs => next (rec (ts c))); eauto.
          - eapply djoin_upperbound with (ds := f cs ts) (i := false); eauto.
        }
  }
  splits; auto. intros o H_rLt.
  pose proof (classic (exists o' : Tree, o <ᵣ o' /\ o' <ᵣ mkNode cs ts)) as [YES | NO].
  - unfold Ord.join. des. hexploit (IH o'); eauto. i; des. eapply dle_trans with (d2 := rec o'); auto.
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
    unfold Ord.join. eapply dle_trans with (d2 := next (rec (ts c))); auto.
    { eapply next_good. eapply IH; eauto. }
    { eapply next_congruence; auto.
      - eapply IH; eauto.
      - eapply IH; eauto.
      - eapply deq_sym; eauto.
    }
    { eapply dle_trans with (d2 := djoin cs (fun i : cs => next (rec (ts i)))); auto.
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
    - destruct YES as [c]. eapply dle_trans with (d2 := next (rec (ts c))); eauto. eapply djoin_upperbound with (ds := fun c : cs => next (rec (ts c))); auto.
    - eapply djoin_supremum; auto. intros c. contradiction NO. econs. exact c.
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
  eapply deq_trans with (d2 := rec empty); auto. simpl.
  change (djoin bool (j Empty_set (Empty_set_rect _)) ≡ dbase). split.
  - eapply djoin_supremum; auto. intros [ | ]; auto. eapply djoin_supremum; auto. intros [].
  - eapply djoin_upperbound with (ds := j Empty_set (Empty_set_rect _)) (i := true); eauto.
Qed.

Lemma rec_succ (o : Tree) (alpha : Tree)
  (SUCC : o =ᵣ succ alpha)
  : rec o ≡ next (rec alpha).
Proof with auto.
  eapply deq_trans with (d2 := rec (succ alpha))... simpl.
  change (djoin bool (j { b : bool & children (if b then alpha else singleton alpha) } (fun c => childnodes (if projT1 c then alpha else singleton alpha) (projT2 c))) ≡ next (rec alpha)). split.
  - eapply djoin_supremum... intros [ | ]; eauto. eapply djoin_supremum... intros [[ | ] c]; simpl; eapply rec_next_dle.
    + eapply rLt_implies_rLe. econs. exists c...
    + simpl in c. destruct c as [ | ]...
  - refine (let c : { b : bool & children (if b then alpha else singleton alpha) } := @existT _ _ false true in _).
    eapply dle_trans with (d2 := djoin { b : bool & children (if b then alpha else singleton alpha) } (fun c => next (rec (childnodes (if projT1 c then alpha else singleton alpha) (projT2 c))))); auto.
    + eapply djoin_upperbound with (ds := fun c : {b : bool & children (if b then alpha else singleton alpha)} => next (rec (childnodes (if projT1 c then alpha else singleton alpha) (projT2 c)))) (i := c); eauto.
    + eapply djoin_upperbound with (ds := j { b : bool & children (if b then alpha else singleton alpha) } (fun c => childnodes (if projT1 c then alpha else singleton alpha) (projT2 c))) (i := false); eauto.
Qed.

Lemma rec_lim' (o : Tree) (cs : Type) (ts : cs -> Tree)
  (APPROX : forall c1 : cs, exists c2 : cs, ts c1 <ᵣ ts c2)
  (INHABITED : inhabited cs)
  (LIM' : o =ᵣ indexed_union cs ts)
  : rec o ≡ djoin cs (fun c : cs => rec (ts c)).
Proof with auto.
  destruct INHABITED as [c]. destruct o as [cs' ts']; simpl. change (djoin bool (j cs' ts') ≡ djoin cs (fun i : cs => rec (ts i))); split.
  - eapply djoin_supremum; eauto. intros [ | ]; simpl.
    + eapply dle_trans with (d2 := rec (ts c))... eapply djoin_upperbound with (ds := fun i : cs => rec (ts i)) (i := c); eauto.
    + eapply djoin_supremum... clear c. intros c'. destruct LIM' as [LE1 LE2]; simpl in *. destruct LE1 as [H_rLt]; simpl in *.
      pose proof (H_rLt c') as [[c H_rLe]]; simpl in *. eapply dle_trans with (d2 := rec (ts (projT1 c)))...
      * eapply lt_rec. econs. exists (projT2 c). exact H_rLe.
      * eapply djoin_upperbound with (ds := fun i : cs => rec (ts i)) (i := projT1 c); eauto.
  - eapply djoin_supremum... clear c. intros c. eapply dle_trans with (d2 := djoin cs (fun c => rec (ts c)))...
    + eapply djoin_upperbound with (ds := fun i : cs => rec (ts i)) (i := c); eauto.
    + clear c. eapply djoin_supremum; eauto. intros c1. simpl in *. pose proof (APPROX c1) as [c2 H_rLt].
      destruct H_rLt as [[c H_rLe]]. destruct LIM' as [LE1 LE2]. destruct LE2 as [LE2]; simpl in *.
      pose proof (LE2 (@existT cs (fun i : cs => children (ts i)) c2 c)) as claim1. simpl in *. destruct claim1 as [[c' H_rLe']]. simpl in *.
      eapply dle_trans with (d2 := rec (ts' c')); eauto. eapply dle_trans with (d2 := djoin cs' (fun i : cs' => next (rec (ts' i))))...
      * eapply dle_trans with (d2 := next (rec (ts' c')))... eapply djoin_upperbound with (ds := fun i : cs' => next (rec (ts' i))) (i := c'); eauto.
      * eapply djoin_upperbound with (ds := j cs' ts') (i := false); eauto.
Qed.

#[local] Notation dunion := (Ord.join djoin).

Lemma dunion_good (d1 : D) (d2 : D)
  (GOOD1 : good d1)
  (GOOD2 : good d2)
  (CHAIN : d1 ⊑ d2 \/ d2 ⊑ d1)
  : good (dunion d1 d2).
Proof.
  eapply djoin_good; auto.
  - intros [ | ] [ | ]; auto. des; eauto.
  - intros [ | ]; eauto.
Qed.

#[local] Hint Resolve dunion_good : core.

Lemma dunion_supremum (d1 : D) (d2 : D)
  (GOOD1 : good d1)
  (GOOD2 : good d2)
  (CHAIN : d1 ⊑ d2 \/ d2 ⊑ d1)
  : forall d : D, good d -> d1 ⊑ d -> d2 ⊑ d -> dunion d1 d2 ⊑ d.
Proof.
  ii. eapply djoin_supremum; auto.
  - intros [ | ] [ | ]; auto. des; eauto.
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
  - intros [ | ] [ | ]; auto. des; auto.
  - intros [ | ]; auto.
Qed.

Lemma dunion_r (d1 : D) (d2 : D)
  (GOOD1 : good d1)
  (GOOD2 : good d2)
  (CHAIN : d1 ⊑ d2 \/ d2 ⊑ d1)
  : d2 ⊑ dunion d1 d2.
Proof.
  eapply djoin_upperbound with (ds := fun b : bool => if b then d1 else d2) (i := false).
  - intros [ | ] [ | ]; auto. des; auto.
  - intros [ | ]; auto.
Qed.

#[local] Hint Resolve dunion_supremum dunion_l dunion_r : core.

Let BASEJOIN (cs : Type) (ts : cs -> Tree)
  : dbase ⊑ djoin cs (fun c : cs => rec (ts c)) \/ djoin cs (fun c : cs => rec (ts c)) ⊑ dbase.
Proof.
  destruct (classic (inhabited cs)) as [YES | NO].
  - destruct YES as [c]. left. eapply dle_trans with (d2 := rec (ts c)); auto.
    eapply djoin_upperbound with (ds := fun a => rec (ts a)) (i := c); eauto.
  - right. eapply djoin_supremum; auto. intros c. contradiction NO. econs. exact c.
Qed.

Let BASENEXTJOIN (cs : Type) (ts : cs -> Tree)
  : dbase ⊑ djoin cs (fun c : cs => next (rec (ts c))) \/ djoin cs (fun c : cs => next (rec (ts c))) ⊑ dbase.
Proof.
  destruct (classic (inhabited cs)) as [YES | NO].
  - destruct YES as [c]. left.
    eapply dle_trans with (d2 := rec (ts c)); auto.
    eapply dle_trans with (d2 := next (rec (ts c))); auto.
    eapply djoin_upperbound with (ds := fun c => next (rec (ts c))); eauto.
  - right. eapply djoin_supremum; auto. intros c. contradiction NO. econs; exact c.
Qed.

#[local] Hint Resolve BASEJOIN BASENEXTJOIN : core.

Lemma rec_join (cs : Type) (ts : cs -> Tree)
  : rec (indexed_union cs ts) ≡ dunion dbase (djoin cs (fun i : cs => rec (ts i))).
Proof.
  simpl.
  change (djoin bool (j { i : cs & children (ts i) } (fun c => childnodes (ts (projT1 c)) (projT2 c))) ≡ dunion dbase (djoin cs (fun i : cs => rec (ts i)))); split.
  - eapply djoin_supremum; auto.
    intros [ | ]; simpl; eauto. eapply djoin_supremum; auto. intros [c i]; simpl.
    eapply dle_trans with (d2 := rec (ts c)); auto.
    + eapply lt_rec. econs. exists i; eauto.
    + eapply dle_trans with (d2 := djoin _ (fun c => rec (ts c))); auto.
      eapply djoin_upperbound with (ds := fun c => rec (ts c)); eauto.
  - change (dunion dbase (djoin cs (fun i : cs => rec (ts i))) ⊑ rec (indexed_union cs ts)). eapply dunion_supremum; auto.
    eapply djoin_supremum; auto. intros c. eapply le_rec. econs. intros i. econs. simpl. exists (@existT _ _ c i); eauto.
Qed.

Lemma rec_is_join (o : Tree) (cs : Type) (ts : cs -> Tree)
  (JOIN : o =ᵣ indexed_union cs ts)
  : rec o ≡ dunion dbase (djoin cs (fun c : cs => rec (ts c))).
Proof.
  eapply deq_trans with (d2 := rec (indexed_union cs ts)); auto. eapply rec_join.
Qed.

Lemma rec_join_inhabited (cs : Type) (ts : cs -> Tree)
  (INHABITED : inhabited cs)
  : rec (indexed_union cs ts) ≡ djoin cs (fun c : cs => rec (ts c)).
Proof.
  eapply deq_trans with (d2 := dunion dbase (djoin cs (fun i : cs => rec (ts i)))); auto.
  - eapply rec_join with (cs := cs) (ts := ts).
  - split.
    + destruct INHABITED as [c]. eapply dunion_supremum; auto.
      eapply dle_trans with (d2 := rec (ts c)); auto.
      eapply djoin_supremum with (ds := fun c : cs => rec (ts c)); eauto.
    + eapply dunion_r; eauto.
Qed.

Lemma rec_is_join_inhabited (o : Tree) (cs : Type) (ts : cs -> Tree)
  (INHABITED : inhabited cs)
  (JOIN : o =ᵣ indexed_union cs ts)
  : rec o ≡ djoin cs (fun c : cs => rec (ts c)).
Proof.
  eapply deq_trans with (d2 := rec (indexed_union cs ts)); auto.
  eapply rec_join_inhabited; eauto.
Qed.

#[local] Hint Resolve rec_is_join_inhabited : core.

Lemma rec_union (o : Tree) (o' : Tree)
  : rec (union o o') ≡ dunion (rec o) (rec o').
Proof.
  assert (INHABITED : inhabited bool).
  { constructor. exact true. }
  split.
  { eapply dle_trans with (d2 := djoin bool (fun b : bool => rec (if b then o else o'))); auto.
    - eapply rec_join_inhabited; eauto.
    - eapply djoin_supremum; auto. intros [ | ]; eauto.
  }
  { eapply dle_trans with (d2 := djoin bool (fun b : bool => rec (if b then o else o'))); auto.
    - eapply djoin_supremum; auto.
      + intros [ | ] [ | ]; simpl; eauto.
      + intros [ | ]; simpl; eauto.
      + intros [ | ].
        * eapply djoin_upperbound with (ds := fun b : bool => rec (if b then o else o')) (i := true); eauto.
        * eapply djoin_upperbound with (ds := fun b : bool => rec (if b then o else o')) (i := false); eauto.
    - eapply rec_join_inhabited; eauto.
  }
Qed.

Let __helper1 (I : Type@{Set_u}) (alpha : I -> Tree) (f : Tree -> D)
  (EQ : forall i : I, f (alpha i) ≡ rec (alpha i))
  : forall i : I, rec (alpha i) ⊑ f (alpha i).
Proof.
  i; exact (proj2 (EQ i)).
Qed.

Let __helper2 (I : Type@{Set_u}) (alpha : I -> Tree) (f : Tree -> D)
  (EQ : forall i : I, f (alpha i) ≡ rec (alpha i))
  : forall i : I, f (alpha i) ⊑ rec (alpha i).
Proof.
  i; exact (proj1 (EQ i)).
Qed.

#[local] Hint Unfold deq : core.

Lemma rec_unique (f : Tree -> D)
  (ZERO : forall o : Tree, o =ᵣ empty -> f o ≡ dbase)
  (SUCC : forall o : Tree, forall alpha : Tree, o =ᵣ succ alpha -> f o ≡ next (f alpha))
  (LIM' : forall o : Tree, forall I : Type, forall alpha : I -> Tree, o =ᵣ indexed_union I alpha -> inhabited I -> (forall i1, exists i2, alpha i1 <ᵣ alpha i2) -> f o ≡ djoin I (fun i : I => f (alpha i)))
  (GOOD : forall o, good (f o))
  : forall o, f o ≡ rec o.
Proof.
  eapply transfinite_induction.
  - ii. eapply deq_trans with (d2 := dbase); auto. eapply deq_sym. eapply rec_zero; eauto.
  - ii. eapply deq_trans with (d2 := next (f alpha)); auto. eapply deq_sym. eapply deq_trans with (d2 := next (rec alpha)); auto. eapply rec_succ; eauto.
  - ii. des.
    assert (CHAIN : forall i1, forall i2, dle (f (alpha i1)) (f (alpha i2)) \/ dle (f (alpha i2)) (f (alpha i1))).
    { ii. pose proof (rec_chain (alpha i1) (alpha i2)) as [LE | LE]; [left | right].
      - eapply dle_trans with (d2 := rec (alpha i1)); auto.
        eapply dle_trans with (d2 := rec (alpha i2)); auto.
      - eapply dle_trans with (d2 := rec (alpha i1)); auto.
        eapply dle_trans with (d2 := rec (alpha i2)); auto.
    }
    eapply deq_sym. eapply deq_trans with (d2 := djoin I (fun i => f (alpha i))); auto.
    eapply deq_trans with (d2 := djoin I (fun i => rec (alpha i))); auto. split; eapply djoin_supremum; auto; i.
    + eapply dle_trans with (d2 := f (alpha i)); auto. eapply djoin_upperbound with (ds := fun i => f (alpha i)); eauto.
    + eapply dle_trans with (d2 := rec (alpha i)); auto. eapply djoin_upperbound with (ds := fun i => rec (alpha i)); eauto.
Qed.

Lemma rec_characterisation (rec' : Tree -> D)
  (REC : forall cs : Type, forall ts : cs -> Tree, rec' (mkNode cs ts) ≡ dunion dbase (djoin cs (fun c : cs => next (rec' (ts c)))))
  (GOOD : forall o : Tree, good (rec' o))
  : forall alpha : Ord.t, rec' alpha ≡ rec alpha.
Proof.
  rename rec' into f. intros t; red in t. induction t as [cs ts IH]; simpl.
  assert (NEXTLE : forall c1 : cs, forall c2 : cs, ts c1 ≦ᵣ ts c2 -> next (f (ts c1)) ⊑ next (f (ts c2))).
  { ii. eapply dle_trans with (d2 := next (rec (ts c1))); auto.
    - eapply next_congruence; eauto.
    - eapply dle_trans with (d2 := next (rec (ts c2))); auto. eapply next_congruence; eauto.
  }
  assert (NEXTCHAIN : forall c1 : cs, forall c2 : cs, next (f (ts c1)) ⊑ next (f (ts c2)) \/ next (f (ts c2)) ⊑ next (f (ts c1))).
  { ii. pose proof (rLe_total (ts c1) (ts c2)) as [? | ?]; eauto. }
  assert (BASE : dbase ⊑ djoin cs (fun c => next (f (ts c))) \/ djoin cs (fun c => next (f (ts c))) ⊑ dbase).
  { ii. pose proof (classic (inhabited cs)) as [YES | NO]; [left | right].
    - destruct YES as [c]. eapply dle_trans with (d2 := f (ts c)); auto.
      + eapply dle_trans with (d2 := rec (ts c)); eauto.
      + eapply dle_trans with (d2 := next (f (ts c))); auto. eapply djoin_upperbound with (ds := fun c => next (f (ts c))); eauto.
    - eapply djoin_supremum; auto. intros c. contradiction NO. econs. exact c.
  }
  assert (H1_good : good (dunion dbase (djoin cs (fun c => next (f (ts c)))))).
  { eapply dunion_good; eauto. }
  assert (H2_good : good (dunion dbase (djoin cs (fun c => next (rec (ts c)))))).
  { eapply djoin_good; [eapply j_chain | eapply good_j]. }
  split.
  - eapply dle_trans with (d2 := dunion dbase (djoin cs (fun c => next (f (ts c))))); auto.
    + eapply REC.
    + eapply djoin_supremum; auto.
      * intros [ | ] [ | ]; simpl; auto. destruct BASE; eauto.
      * intros [ | ]; eauto.
      * intros [ | ]; auto. eapply dle_trans with (d2 := djoin cs (fun c => next (rec (ts c)))); auto.
        eapply djoin_supremum; auto. intros i. eapply dle_trans with (d2 := next (rec (ts i))); auto.
        { eapply next_congruence; eauto. }
        { eapply djoin_upperbound with (ds := fun c => next (rec (ts c))); eauto. }
  - eapply dle_trans with (d2 := dunion dbase (djoin cs (fun c => next (f (ts c))))); auto.
    + eapply dunion_supremum; auto. eapply dle_trans with (d2 := djoin cs (fun c => next (f (ts c)))); auto.
      eapply djoin_supremum; auto. intros i. eapply dle_trans with (d2 := next (f (ts i))); auto.
      * eapply next_congruence; eauto.
      * eapply djoin_upperbound with (ds := fun c => next (f (ts c))); eauto.
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
  intros o. pose proof (rLt_wf o) as H_ACC. induction H_ACC as [o _ IH].
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
    + unnw. eapply dle_trans with (d2 := next (rec beta2)); auto.
      * eapply rec_succ; eauto.
      * eapply dle_trans with (d2 := next (rec alpha)); auto. eapply next_congruence; auto. rewrite rEq_succ_iff in SUCC. rewrite -> SUCC in LT. split; eauto.
    + eapply le_rec; auto. eapply EQ.
  - hexploit rec_is_join_inhabited; try eassumption. i; des. rename I into cs, alpha into ts, alpha0 into alpha.
    assert (claim1 : forall c1 : cs, forall c2 : cs, rec (ts c1) ⊑ rec (ts c2) \/ rec (ts c2) ⊑ rec (ts c1)).
    { ii. pose proof (rLe_total (ts c1) (ts c2)) as [H_LE | H_LE]; [left | right]; eapply le_rec; eauto. }
    eapply dle_trans with (d2 := djoin cs (fun c => rec (ts c))); auto.
    + exact (proj1 H2).
    + eapply djoin_supremum; auto. intros i. pose proof (rLe_or_rGt (ts i) alpha) as [H_LE | H_GT]; auto with *.
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
      - transitivity alpha; auto. destruct alpha; eauto.
      - destruct c; eauto.
    }
    eapply fixed_point_after with (alpha := alpha).
    + eapply dle_trans with (d2 := rec (succ alpha)); eauto.
      eapply rec_succ. reflexivity.
    + transitivity o; eauto with *.
Qed.

Lemma least_lt_incr_acc (o : Tree)
  (INCR : not_fixed o)
  : o ≦ᵣ @fromWf D strictly_increasing strictly_increasing_well_founded (rec o).
Proof.
  pose proof (rLt_wf o) as H_ACC. induction H_ACC as [o _ IH].
  pose proof (rLe_or_rGt o (@fromWf D strictly_increasing strictly_increasing_well_founded (rec o))) as [H_LE | H_GT]; eauto.
  destruct o; simpl. econs. simpl. intros c.
  assert (claim1 : not_fixed (ts c)).
  { eapply end_le_end with (o' := mkNode cs ts); eauto. eapply rLt_implies_rLe; eauto. }
  pose proof (IH (ts c) (trivial_rLt cs ts c) claim1) as claim2. eapply rLe_rLt_rLt; eauto.
  assert (strictly_increasing (rec (ts c)) (rec (mkNode cs ts))) as claim3.
  { econs; eauto. }
  econs. eapply member_implies_rLt. unfold fromWf. eapply fromAcc_member_fromAcc_intro. exact claim3.
Qed.

Lemma hartogs_fixed
  : ~ not_fixed (hartogs D).
Proof.
  intros H_contra. apply least_lt_incr_acc in H_contra; eauto.
  eapply rLt_iff_not_rGe. 2: exact H_contra. eapply rLe_rLt_rLt with (y := @fromWfSet D strictly_increasing strictly_increasing_well_founded).
  - eapply rLt_implies_rLe. econs. unfold fromWfSet. exists (rec (hartogs D)). reflexivity.
  - econs. simpl. exists (B.exist strictly_increasing strictly_increasing_well_founded). reflexivity.
Qed.

Theorem BourbakiWittFixedpointTheorem
  : next (rec (hartogs D)) ≡ rec (hartogs D).
Proof.
  split.
  - eapply NNPP. intros H_contra. eapply hartogs_fixed. eapply end_le_end with (o' := succ (hartogs D)).
    { eapply rLt_implies_rLe. econs. simpl. exists (@existT _ _ false true). simpl. reflexivity. }
    intros o H_rLt H_dle. eapply H_contra. eapply dle_trans with (d2 := rec (succ (hartogs D))). 1,2,3: eauto.
    + eapply rec_succ. reflexivity.
    + pose proof (rLe_or_rGt o (hartogs D)) as [H_rLe | H_rGt].
      * eapply dle_trans with (d2 := rec o); eauto.
      * exfalso. eapply rLt_iff_not_rGe; [exact H_rLt | ].
        assert (claim1 : succ (hartogs D) =ᵣ succ (hartogs D)) by reflexivity.
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
  (mu_f := Ord.rec (D := D) (ipo_sup Empty_set (Empty_set_rect (fun _ : Empty_set => D))) f ipo_sup (hartogs D))
  : is_lfpOf mu_f f.
Proof.
  split.
  - red. red. symmetry.
    enough (f mu_f =< mu_f /\ mu_f =< f mu_f) as [H1 H2] by now eapply leProp_antisymmetry.
    eapply BourbakiWittFixedpointTheorem with (good := fun x : D => x =< f x) (dbase := ipo_sup Empty_set (Empty_set_rect _)) (djoin := ipo_sup) (next := f).
    + ii; reflexivity.
    + ii; now transitivity d2.
    + ii. eapply ipo_sup_is_supremum; auto. ii. red in IN. destruct IN as (i & ->). transitivity (f (ds i)); auto.
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
    + split; eapply ipo_sup_is_supremum; ii; done!.
    + ii; split.
      * eapply f_isMonotonic; done!.
      * des. rewrite H_fix_f. eapply f_isMonotonic. done!.
    + ii; des; done!.
    + done!.
Qed.

End GENERALISED_KLEENE_FIXEDPOINT_THEOREM.

End THEORY_ON_RANK.

End InducedOrdinal.

Module Hessenberg.

#[local] Typeclasses Opaque Ord.t.

#[local] Existing Instance rEq_asSetoid.

#[local] Existing Instance Ord_isProset.

Variant double_rel {A : Type} {B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) : A * B -> A * B -> Prop :=
  | double_rel_left (a0 : A) (a1 : A) (b : B)
    (LT : RA a0 a1)
    : double_rel RA RB (a0, b) (a1, b)
  | double_rel_right (a : A) (b0 : B) (b1 : B)
    (LT : RB b0 b1)
    : double_rel RA RB (a, b0) (a, b1).

Lemma double_rel_well_founded {A : Type} {B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop)
  (WFA : well_founded RA)
  (WFB : well_founded RB)
  : well_founded (double_rel RA RB).
Proof.
  cut (forall a : A, forall b : B, Acc (double_rel RA RB) (a, b)).
  { intros H [a b]. eapply H. }
  intros a0. pattern a0. revert a0. eapply well_founded_induction with (R := RA); [exact WFA |].
  intros a0 IHL b0. pattern b0. revert b0. eapply well_founded_induction with (R := RB); [exact WFB |].
  intros b0 IHR. econs. intros [a1 b1] LT. inv LT.
  - eapply IHL; eauto.
  - eapply IHR; eauto.
Qed.

Lemma double_well_founded_induction {A : Type} {B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop)
  (WFA : well_founded RA)
  (WFB : well_founded RB)
  (P : A -> B -> Prop)
  (IND : forall a1 : A, forall b1 : B, (forall a0 : A, RA a0 a1 -> P a0 b1) -> (forall b0 : B, RB b0 b1 -> P a1 b0) -> P a1 b1)
  : forall a : A, forall b : B, P a b.
Proof.
  cut (forall ab : A * B, match ab with (a, b) => P a b end).
  { intros H a b. eapply H with (ab := (a, b)). }
  intros ab. pattern ab. revert ab. eapply well_founded_induction with (R := double_rel RA RB); [eapply double_rel_well_founded with (RA := RA) (RB := RB); assumption |].
  intros [a b] IH. simpl. eapply IND.
  - intros a0 LT. eapply IH with (y := (a0, b)). eapply double_rel_left. exact LT.
  - intros b0 LT. eapply IH with (y := (a, b0)). eapply double_rel_right. exact LT.
Qed.

Fixpoint add (alpha : Ord.t) : Ord.t -> Ord.t :=
  match alpha with
  | mkNode cs0 ts0 =>
    fix add_right (beta : Ord.t) : Ord.t :=
    match beta with
    | mkNode cs1 ts1 => Ord_join (Ord.sup cs1 (fun c1 : cs1 => Ord.suc (add_right (ts1 c1)))) (Ord.sup cs0 (fun c0 : cs0 => Ord.suc (add (ts0 c0) (mkNode cs1 ts1))))
    end
  end.

Lemma add_red_eq (cs0 : Type@{Set_u}) (ts0 : cs0 -> Ord.t) (cs1 : Type@{Set_u}) (ts1 : cs1 -> Ord.t)
  : add (mkNode cs0 ts0) (mkNode cs1 ts1) = Ord_join (Ord.sup cs1 (fun c1 : cs1 => Ord.suc (add (mkNode cs0 ts0) (ts1 c1)))) (Ord.sup cs0 (fun c0 : cs0 => Ord.suc (add (ts0 c0) (mkNode cs1 ts1)))).
Proof.
  reflexivity.
Qed.

Lemma add_red (cs0 : Type@{Set_u}) (ts0 : cs0 -> Ord.t) (cs1 : Type@{Set_u}) (ts1 : cs1 -> Ord.t)
  : add (mkNode cs0 ts0) (mkNode cs1 ts1) =ᵣ Ord_join (Ord.sup cs1 (fun c1 : cs1 => Ord.suc (add (mkNode cs0 ts0) (ts1 c1)))) (Ord.sup cs0 (fun c0 : cs0 => Ord.suc (add (ts0 c0) (mkNode cs1 ts1)))).
Proof.
  rewrite add_red_eq. reflexivity.
Qed.

Lemma add_supremum (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LE0 : forall alpha2 : Ord.t, alpha2 <ᵣ alpha -> add alpha2 beta <ᵣ alpha1)
  (LE1 : forall alpha2 : Ord.t, alpha2 <ᵣ beta -> add alpha alpha2 <ᵣ alpha1)
  : add alpha beta ≦ᵣ alpha1.
Proof.
  destruct alpha as [cs0 ts0], beta as [cs1 ts1]. rewrite add_red_eq. eapply Ord_join_spec.
  - eapply Ord_sup_rLe_intro. intros c1. eapply succ_rLe_intro. eapply LE1. eapply member_implies_rLt. eapply member_intro.
  - eapply Ord_sup_rLe_intro. intros c0. eapply succ_rLe_intro. eapply LE0. eapply member_implies_rLt. eapply member_intro.
Qed.

Lemma add_rLe_l (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LE : alpha ≦ᵣ beta)
  : add alpha alpha1 ≦ᵣ add beta alpha1.
Proof.
  revert alpha LE. pattern beta, alpha1. revert beta alpha1.
  eapply double_well_founded_induction with (RA := rLt) (RB := rLt); [exact rLt_wf | exact rLt_wf |].
  intros beta alpha1 IHL IHR alpha LE. destruct alpha as [cs0 ts0], beta as [cs1 ts1], alpha1 as [cs2 ts2].
  rewrite 2 add_red_eq. eapply Ord_join_spec.
  - eapply Ord_sup_rLe_intro. intros c2. transitivity (Ord.suc (add (mkNode cs1 ts1) (ts2 c2))).
    + eapply Ord_suc_rLe. eapply IHR.
      * eapply member_implies_rLt. eapply member_intro.
      * exact LE.
    + transitivity (Ord.sup cs2 (fun c : cs2 => Ord.suc (add (mkNode cs1 ts1) (ts2 c)))).
      * change ((fun c : cs2 => Ord.suc (add (mkNode cs1 ts1) (ts2 c))) c2 ≦ᵣ Ord.sup cs2 (fun c : cs2 => Ord.suc (add (mkNode cs1 ts1) (ts2 c)))). eapply Ord_rLe_sup_intro.
      * eapply Ord_join_l.
  - eapply Ord_sup_rLe_intro. intros c0.
    pose proof (rLt_rLe_rLt (ts0 c0) (mkNode cs0 ts0) (mkNode cs1 ts1) (member_implies_rLt (ts0 c0) (mkNode cs0 ts0) (member_intro cs0 ts0 c0)) LE) as [[c1 LE_c1]].
    transitivity (Ord.suc (add (ts1 c1) (mkNode cs2 ts2))).
    + eapply Ord_suc_rLe. eapply IHL.
      * eapply member_implies_rLt. eapply member_intro.
      * exact LE_c1.
    + transitivity (Ord.sup cs1 (fun c : cs1 => Ord.suc (add (ts1 c) (mkNode cs2 ts2)))).
      * change ((fun c : cs1 => Ord.suc (add (ts1 c) (mkNode cs2 ts2))) c1 ≦ᵣ Ord.sup cs1 (fun c : cs1 => Ord.suc (add (ts1 c) (mkNode cs2 ts2)))). eapply Ord_rLe_sup_intro.
      * eapply Ord_join_r.
Qed.

Lemma add_rLe_r (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LE : beta ≦ᵣ alpha1)
  : add alpha beta ≦ᵣ add alpha alpha1.
Proof.
  revert beta LE. pattern alpha, alpha1. revert alpha alpha1.
  eapply double_well_founded_induction with (RA := rLt) (RB := rLt); [exact rLt_wf | exact rLt_wf |].
  intros alpha alpha1 IHL IHR beta LE. destruct alpha as [cs0 ts0], beta as [cs1 ts1], alpha1 as [cs2 ts2].
  rewrite 2 add_red_eq. eapply Ord_join_spec.
  - eapply Ord_sup_rLe_intro. intros c1.
    pose proof (rLt_rLe_rLt (ts1 c1) (mkNode cs1 ts1) (mkNode cs2 ts2) (member_implies_rLt (ts1 c1) (mkNode cs1 ts1) (member_intro cs1 ts1 c1)) LE) as [[c2 LE_c2]].
    transitivity (Ord.suc (add (mkNode cs0 ts0) (ts2 c2))).
    + eapply Ord_suc_rLe. eapply IHR.
      * eapply member_implies_rLt. eapply member_intro.
      * exact LE_c2.
    + transitivity (Ord.sup cs2 (fun c : cs2 => Ord.suc (add (mkNode cs0 ts0) (ts2 c)))).
      * change ((fun c : cs2 => Ord.suc (add (mkNode cs0 ts0) (ts2 c))) c2 ≦ᵣ Ord.sup cs2 (fun c : cs2 => Ord.suc (add (mkNode cs0 ts0) (ts2 c)))). eapply Ord_rLe_sup_intro.
      * eapply Ord_join_l.
  - eapply Ord_sup_rLe_intro. intros c0. transitivity (Ord.suc (add (ts0 c0) (mkNode cs2 ts2))).
    + eapply Ord_suc_rLe. eapply IHL.
      * eapply member_implies_rLt. eapply member_intro.
      * exact LE.
    + transitivity (Ord.sup cs0 (fun c : cs0 => Ord.suc (add (ts0 c) (mkNode cs2 ts2)))).
      * change ((fun c : cs0 => Ord.suc (add (ts0 c) (mkNode cs2 ts2))) c0 ≦ᵣ Ord.sup cs0 (fun c : cs0 => Ord.suc (add (ts0 c) (mkNode cs2 ts2)))). eapply Ord_rLe_sup_intro.
      * eapply Ord_join_r.
Qed.

Lemma add_rEq_l (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (EQ : alpha =ᵣ beta)
  : add alpha alpha1 =ᵣ add beta alpha1.
Proof.
  rewrite rEq_iff in *. destruct EQ as [LE GE]. split; now eapply add_rLe_l.
Qed.

Lemma add_rEq_r (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (EQ : beta =ᵣ alpha1)
  : add alpha beta =ᵣ add alpha alpha1.
Proof.
  rewrite rEq_iff in *. destruct EQ as [LE GE]. split; now eapply add_rLe_r.
Qed.

#[global]
Instance add_isMonotonic2 : isMonotonic2 add.
Proof.
  intros alpha beta alpha1 beta1 LE0 LE1. transitivity (add beta alpha1).
  - eapply add_rLe_l. exact LE0.
  - eapply add_rLe_r. exact LE1.
Qed.

Lemma add_rLt_l (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LT : alpha <ᵣ beta)
  : add alpha alpha1 <ᵣ add beta alpha1.
Proof.
  destruct beta as [cs1 ts1]. destruct LT as [[c LE]]. destruct alpha1 as [cs2 ts2]. rewrite add_red_eq.
  eapply rLt_rLe_rLt with (y := Ord.suc (add (ts1 c) (mkNode cs2 ts2))).
  - unfold Ord.suc. rewrite rLt_succ_iff. eapply add_rLe_l. exact LE.
  - transitivity (Ord.sup cs1 (fun c0 : cs1 => Ord.suc (add (ts1 c0) (mkNode cs2 ts2)))).
    + change ((fun c0 : cs1 => Ord.suc (add (ts1 c0) (mkNode cs2 ts2))) c ≦ᵣ Ord.sup cs1 (fun c0 : cs1 => Ord.suc (add (ts1 c0) (mkNode cs2 ts2)))). eapply Ord_rLe_sup_intro.
    + eapply Ord_join_r.
Qed.

Lemma add_rLt_r (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LT : beta <ᵣ alpha1)
  : add alpha beta <ᵣ add alpha alpha1.
Proof.
  destruct alpha1 as [cs2 ts2]. destruct LT as [[c LE]]. destruct alpha as [cs0 ts0]. rewrite add_red_eq.
  eapply rLt_rLe_rLt with (y := Ord.suc (add (mkNode cs0 ts0) (ts2 c))).
  - unfold Ord.suc. rewrite rLt_succ_iff. eapply add_rLe_r. exact LE.
  - transitivity (Ord.sup cs2 (fun c0 : cs2 => Ord.suc (add (mkNode cs0 ts0) (ts2 c0)))).
    + change ((fun c0 : cs2 => Ord.suc (add (mkNode cs0 ts0) (ts2 c0))) c ≦ᵣ Ord.sup cs2 (fun c0 : cs2 => Ord.suc (add (mkNode cs0 ts0) (ts2 c0)))). eapply Ord_rLe_sup_intro.
    + eapply Ord_join_l.
Qed.

Lemma add_spec (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (SUP0 : forall alpha2 : Ord.t, alpha2 <ᵣ alpha -> add alpha2 beta <ᵣ alpha1)
  (SUP1 : forall alpha2 : Ord.t, alpha2 <ᵣ beta -> add alpha alpha2 <ᵣ alpha1)
  : add alpha beta ≦ᵣ alpha1.
Proof.
  eapply add_supremum; eauto.
Qed.

Lemma Ord_sup_rLt_elim {I : Type@{Set_u}} (os : I -> Ord.t) (x : Ord.t)
  (LT : x <ᵣ Ord.sup I os)
  : exists i : I, x <ᵣ os i.
Proof.
  destruct LT as [[[i c] LE]]. exists i. eapply rLe_rLt_rLt with (y := childnodes (os i) c).
  - exact LE.
  - eapply member_implies_rLt. eapply member_intro.
Qed.

Lemma Ord_sup_suc_rLt_elim {I : Type@{Set_u}} (os : I -> Ord.t) (x : Ord.t)
  (LT : x <ᵣ Ord.sup I (fun i : I => Ord.suc (os i)))
  : exists i : I, x ≦ᵣ os i.
Proof.
  pose proof (Ord_sup_rLt_elim (fun i : I => Ord.suc (os i)) x LT) as [i LT_i]. exists i.
  unfold Ord.suc in LT_i. now rewrite rLt_succ_iff in LT_i.
Qed.

Lemma add_rLt_elim (x : Ord.t) (alpha : Ord.t) (beta : Ord.t)
  (LT : x <ᵣ add alpha beta)
  : (exists alpha' : Ord.t, alpha' <ᵣ alpha /\ x ≦ᵣ add alpha' beta) \/ (exists beta' : Ord.t, beta' <ᵣ beta /\ x ≦ᵣ add alpha beta').
Proof.
  destruct alpha as [cs0 ts0], beta as [cs1 ts1]. rewrite add_red_eq in LT. unfold Ord_join in LT.
  pose proof (Ord_sup_rLt_elim (fun b : bool => if b then Ord.sup cs1 (fun c1 : cs1 => Ord.suc (add (mkNode cs0 ts0) (ts1 c1))) else Ord.sup cs0 (fun c0 : cs0 => Ord.suc (add (ts0 c0) (mkNode cs1 ts1)))) x LT) as [[ | ] LT_branch].
  - pose proof (Ord_sup_suc_rLt_elim (fun c1 : cs1 => add (mkNode cs0 ts0) (ts1 c1)) x LT_branch) as [c1 LE]. right. exists (ts1 c1). split.
    + eapply member_implies_rLt. eapply member_intro.
    + exact LE.
  - pose proof (Ord_sup_suc_rLt_elim (fun c0 : cs0 => add (ts0 c0) (mkNode cs1 ts1)) x LT_branch) as [c0 LE]. left. exists (ts0 c0). split.
    + eapply member_implies_rLt. eapply member_intro.
    + exact LE.
Qed.

Lemma add_comm (alpha : Ord.t) (beta : Ord.t)
  : add alpha beta =ᵣ add beta alpha.
Proof.
  revert alpha beta. cut (forall alpha : Ord.t, forall beta : Ord.t, add alpha beta ≦ᵣ add beta alpha).
  { intros LE alpha beta. split; eapply LE. }
  eapply double_well_founded_induction with (RA := rLt) (RB := rLt); [exact rLt_wf | exact rLt_wf |]. intros alpha beta IHL IHR.
  destruct alpha as [cs0 ts0], beta as [cs1 ts1]. rewrite 2 add_red_eq. eapply Ord_join_spec.
  - eapply Ord_sup_rLe_intro. intros c1. transitivity (Ord.suc (add (ts1 c1) (mkNode cs0 ts0))).
    + eapply Ord_suc_rLe. eapply IHR. eapply member_implies_rLt. eapply member_intro.
    + transitivity (Ord.sup cs1 (fun c : cs1 => Ord.suc (add (ts1 c) (mkNode cs0 ts0)))).
      * change ((fun c : cs1 => Ord.suc (add (ts1 c) (mkNode cs0 ts0))) c1 ≦ᵣ Ord.sup cs1 (fun c : cs1 => Ord.suc (add (ts1 c) (mkNode cs0 ts0)))). eapply Ord_rLe_sup_intro.
      * eapply Ord_join_r.
  - eapply Ord_sup_rLe_intro. intros c0. transitivity (Ord.suc (add (mkNode cs1 ts1) (ts0 c0))).
    + eapply Ord_suc_rLe. eapply IHL. eapply member_implies_rLt. eapply member_intro.
    + transitivity (Ord.sup cs0 (fun c : cs0 => Ord.suc (add (mkNode cs1 ts1) (ts0 c)))).
      * change ((fun c : cs0 => Ord.suc (add (mkNode cs1 ts1) (ts0 c))) c0 ≦ᵣ Ord.sup cs0 (fun c : cs0 => Ord.suc (add (mkNode cs1 ts1) (ts0 c)))). eapply Ord_rLe_sup_intro.
      * eapply Ord_join_l.
Qed.

Lemma add_assoc (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  : add (add alpha beta) alpha1 =ᵣ add alpha (add beta alpha1).
Proof.
  enough (LE : forall alpha : Ord.t, forall beta : Ord.t, forall alpha1 : Ord.t, add (add alpha beta) alpha1 ≦ᵣ add alpha (add beta alpha1)).
  { split.
    - eapply LE.
    - transitivity (add (add beta alpha1) alpha).
      + pose proof (add_comm alpha (add beta alpha1)) as [LE1 _]. exact LE1.
      + transitivity (add (add alpha1 beta) alpha).
        * eapply add_rLe_l. pose proof (add_comm beta alpha1) as [LE1 _]. exact LE1.
        * transitivity (add alpha1 (add beta alpha)).
          { eapply LE. }
          { transitivity (add alpha1 (add alpha beta)).
            - eapply add_rLe_r. pose proof (add_comm beta alpha) as [LE1 _]. exact LE1.
            - pose proof (add_comm alpha1 (add alpha beta)) as [LE1 _]. exact LE1.
          }
  }
  cut (forall alpha : Ord.t, forall beta_alpha1 : Ord.t * Ord.t, match beta_alpha1 with (beta, alpha1) => add (add alpha beta) alpha1 ≦ᵣ add alpha (add beta alpha1) end).
  { intros H a b c. exact (H a (b, c)). }
  eapply double_well_founded_induction with (RA := rLt) (RB := double_rel rLt rLt); [exact rLt_wf | eapply double_rel_well_founded with (RA := rLt) (RB := rLt); exact rLt_wf |].
  intros a [b c] IH0 IH12. simpl. eapply add_spec.
  - intros x LT. pose proof (add_rLt_elim x a b LT) as [[a' [LT0 LE0]] | [b' [LT1 LE1]]].
    + eapply rLe_rLt_rLt with (y := add (add a' b) c).
      * eapply add_rLe_l. exact LE0.
      * eapply rLe_rLt_rLt with (y := add a' (add b c)).
        { eapply IH0. exact LT0. }
        { eapply add_rLt_l. exact LT0. }
    + eapply rLe_rLt_rLt with (y := add (add a b') c).
      * eapply add_rLe_l. exact LE1.
      * eapply rLe_rLt_rLt with (y := add a (add b' c)).
        { eapply IH12 with (b0 := (b', c)). eapply double_rel_left. exact LT1. }
        { eapply add_rLt_r. eapply add_rLt_l. exact LT1. }
  - intros c' LT2. eapply rLe_rLt_rLt with (y := add a (add b c')).
    + eapply IH12 with (b0 := (b, c')). eapply double_rel_right. exact LT2.
    + eapply add_rLt_r. eapply add_rLt_r. exact LT2.
Qed.

Lemma add_base_l (alpha : Ord.t) (beta : Ord.t)
  : alpha ≦ᵣ add alpha beta.
Proof.
  revert beta. induction (rLt_wf alpha) as [alpha _ IH]. intros beta. destruct alpha as [cs ts]. eapply rLe_ext. intros z LT.
  destruct LT as [[c LE]]. eapply rLe_rLt_rLt with (y := add (ts c) beta).
  - transitivity (ts c); [exact LE | eapply IH; eapply member_implies_rLt; eapply member_intro].
  - eapply add_rLt_l. eapply member_implies_rLt. eapply member_intro.
Qed.

Lemma add_base_r (alpha : Ord.t) (beta : Ord.t)
  : beta ≦ᵣ add alpha beta.
Proof.
  transitivity (add beta alpha).
  - eapply add_base_l.
  - pose proof (add_comm beta alpha) as [LE _]. exact LE.
Qed.

Lemma arith_add_larger (alpha : Ord.t) (beta : Ord.t)
  : Ord.add alpha beta ≦ᵣ add alpha beta.
Proof.
  revert alpha. induction (rLt_wf beta) as [beta _ IH]. intros alpha. destruct beta as [cs ts]. destruct alpha as [cs0 ts0].
  transitivity (Ord_join (mkNode cs0 ts0) (Ord.sup cs (fun c : cs => Ord.suc (Ord.add (mkNode cs0 ts0) (ts c))))).
  - pose proof (Ord_add_mkNode (mkNode cs0 ts0) cs ts) as [LE _]. exact LE.
  - rewrite add_red_eq. eapply Ord_join_spec.
    + change (mkNode cs0 ts0 ≦ᵣ add (mkNode cs0 ts0) (mkNode cs ts)). eapply add_base_l.
    + eapply Ord_sup_rLe_intro. intros c. transitivity (Ord.suc (add (mkNode cs0 ts0) (ts c))).
      * eapply Ord_suc_rLe. eapply IH. eapply member_implies_rLt. eapply member_intro.
      * transitivity (Ord.sup cs (fun c0 : cs => Ord.suc (add (mkNode cs0 ts0) (ts c0)))).
        { change ((fun c0 : cs => Ord.suc (add (mkNode cs0 ts0) (ts c0))) c ≦ᵣ Ord.sup cs (fun c0 : cs => Ord.suc (add (mkNode cs0 ts0) (ts c0)))). eapply Ord_rLe_sup_intro. }
        { eapply Ord_join_l. }
Qed.

Lemma add_zer_r (alpha : Ord.t)
  : add alpha Ord.zer =ᵣ alpha.
Proof.
  induction (rLt_wf alpha) as [alpha _ IH]. rewrite rEq_iff. split.
  - eapply add_spec.
    + intros alpha1 LT. pose proof (IH alpha1 LT) as [LE _]. eapply rLe_rLt_rLt with (y := alpha1); eauto.
    + intros alpha1 LT. destruct LT as [[c _]]. destruct c.
  - eapply add_base_l.
Qed.

Lemma add_zer_l (alpha : Ord.t)
  : add Ord.zer alpha =ᵣ alpha.
Proof.
  etransitivity.
  - eapply add_comm.
  - eapply add_zer_r.
Qed.

Lemma add_suc_r (alpha : Ord.t) (beta : Ord.t)
  : add alpha (Ord.suc beta) =ᵣ Ord.suc (add alpha beta).
Proof.
  revert beta. induction (rLt_wf alpha) as [alpha _ IH]. intros beta. rewrite rEq_iff. split.
  - eapply add_spec.
    + intros alpha1 LT. unfold Ord.suc. rewrite rLt_succ_iff. transitivity (Ord.suc (add alpha1 beta)).
      * pose proof (IH alpha1 LT beta) as [LE _]. exact LE.
      * unfold Ord.suc. rewrite succ_rLe_iff. eapply add_rLt_l. exact LT.
    + intros alpha1 LT. unfold Ord.suc in LT. rewrite rLt_succ_iff in LT. unfold Ord.suc. rewrite rLt_succ_iff. eapply add_rLe_r. exact LT.
  - eapply succ_rLe_intro. eapply add_rLt_r. unfold Ord.suc. eapply rLt_succ_intro.
Qed.

Lemma add_suc_l (alpha : Ord.t) (beta : Ord.t)
  : add (Ord.suc alpha) beta =ᵣ Ord.suc (add alpha beta).
Proof.
  etransitivity.
  - eapply add_comm.
  - etransitivity.
    + eapply add_suc_r.
    + eapply Ord_suc_rEq. eapply add_comm.
Qed.

Lemma arith_add_of_nat_r (alpha : Ord.t) (n : nat)
  : add alpha (Ord_of_nat n) =ᵣ Ord.add alpha (Ord_of_nat n).
Proof.
  induction n as [ | n IH].
  - rewrite Ord_of_nat_zer. etransitivity.
    + eapply add_zer_r.
    + symmetry. eapply Ord_add_zer_r.
  - rewrite Ord_of_nat_suc. etransitivity.
    + eapply add_suc_r.
    + etransitivity.
      * eapply Ord_suc_rEq. exact IH.
      * symmetry. eapply Ord_add_suc.
Qed.

Lemma add_of_nat (n0 : nat) (n1 : nat)
  : add (Ord_of_nat n0) (Ord_of_nat n1) =ᵣ Ord_of_nat (n0 + n1).
Proof.
  etransitivity.
  - eapply arith_add_of_nat_r.
  - eapply Ord_add_of_nat.
Qed.

Lemma add_rLt_larger_l (alpha : Ord.t) (beta : Ord.t)
  (LT : Ord.zer <ᵣ beta)
  : alpha <ᵣ add alpha beta.
Proof.
  eapply rLt_rLe_rLt.
  - eapply Ord_add_rLt_larger. exact LT.
  - eapply arith_add_larger.
Qed.

Lemma add_rLt_larger_r (alpha : Ord.t) (beta : Ord.t)
  (LT : Ord.zer <ᵣ alpha)
  : beta <ᵣ add alpha beta.
Proof.
  eapply rLt_rLe_rLt with (y := add beta alpha).
  - eapply add_rLt_larger_l. exact LT.
  - pose proof (add_comm beta alpha) as [LE _]. exact LE.
Qed.

Lemma add_isOrdinal (alpha : Ord.t) (beta : Ord.t)
  (ORD0 : isOrdinal alpha)
  (ORD1 : isOrdinal beta)
  : isOrdinal (add alpha beta).
Proof.
  revert beta ORD1. induction alpha as [cs0 ts0 IH0]. intros beta ORD1. induction beta as [cs1 ts1 IH1].
  rewrite add_red_eq. eapply Ord_join_isOrdinal.
  - eapply sup_isOrdinal. intros c1. eapply suc_isOrdinal. eapply IH1. eapply isOrdinal_member_isOrdinal.
    + exact ORD1.
    + eapply member_intro.
  - eapply sup_isOrdinal. intros c0. eapply suc_isOrdinal. eapply IH0.
    + eapply isOrdinal_member_isOrdinal.
      * exact ORD0.
      * eapply member_intro.
    + exact ORD1.
Qed.

End Hessenberg.

Global Opaque Hessenberg.add.

#[local] Infix "⊕" := Hessenberg.add (at level 80, right associativity).

Module Jacobsthal.

#[local] Typeclasses Opaque Ord.t.

#[local] Existing Instance rEq_asSetoid.

#[local] Existing Instance Ord_isProset.

Definition mult (alpha : Ord.t) : Ord.t -> Ord.t :=
  Ord.orec Ord.zer (Hessenberg.add alpha).

Lemma arith_mult_larger (alpha : Ord.t) (beta : Ord.t)
  : Ord.mul alpha beta ≦ᵣ mult alpha beta.
Proof.
  revert alpha. induction (rLt_wf beta) as [beta _ IH]. intros alpha. destruct beta as [cs ts].
  transitivity (Ord.sup cs (fun c : cs => Ord.add (Ord.mul alpha (ts c)) alpha)).
  - pose proof (Ord_mul_mkNode alpha cs ts) as [LE _]. exact LE.
  - etransitivity.
    + eapply Ord_sup_rLe. intros c. transitivity (Hessenberg.add (Ord.mul alpha (ts c)) alpha).
      * eapply Hessenberg.arith_add_larger.
      * transitivity (Hessenberg.add (mult alpha (ts c)) alpha).
        { eapply Hessenberg.add_rLe_l. eapply IH. eapply member_implies_rLt. eapply member_intro. }
        { pose proof (Hessenberg.add_comm (mult alpha (ts c)) alpha) as [LE _]. exact LE. }
    + change (Ord.sup cs (fun c : cs => Hessenberg.add alpha (mult alpha (ts c))) ≦ᵣ Ord.orec Ord.zer (Hessenberg.add alpha) (mkNode cs ts)). rewrite Ord_orec_unfold. eapply Ord_join_r.
Qed.

Lemma mult_zer_r (alpha : Ord.t)
  : mult alpha Ord.zer =ᵣ Ord.zer.
Proof.
  unfold mult. eapply Ord_orec_zer.
Qed.

Lemma mult_suc (alpha : Ord.t) (beta : Ord.t)
  : mult alpha (Ord.suc beta) =ᵣ Hessenberg.add alpha (mult alpha beta).
Proof.
  unfold mult. eapply Ord_orec_suc.
  - intros alpha1. eapply Hessenberg.add_base_r.
  - intros alpha1 beta1 LE. eapply Hessenberg.add_rLe_r. exact LE.
Qed.

Lemma mult_sup (alpha : Ord.t) (I : Type@{Set_u}) (os : I -> Ord.t)
  : mult alpha (Ord.sup I os) =ᵣ Ord.sup I (fun i : I => mult alpha (os i)).
Proof.
  unfold mult. etransitivity.
  - eapply Ord_orec_sup.
    + intros beta. eapply Hessenberg.add_base_r.
    + intros beta alpha1 LE. eapply Hessenberg.add_rLe_r. exact LE.
  - eapply Ord_join_max_r. eapply Ord_zer_rLe.
Qed.

Lemma mult_join (alpha : Ord.t) (beta : Ord.t) (beta1 : Ord.t)
  : mult alpha (Ord_join beta beta1) =ᵣ Ord_join (mult alpha beta) (mult alpha beta1).
Proof.
  unfold Ord_join at 1. etransitivity.
  - eapply mult_sup.
  - unfold Ord_join. eapply Ord_sup_rEq. intros [ | ]; reflexivity.
Qed.

Lemma mult_mkNode (alpha : Ord.t) (cs : Type@{Set_u}) (os : cs -> Ord.t)
  : mult alpha (mkNode cs os) =ᵣ Ord.sup cs (fun c : cs => Hessenberg.add alpha (mult alpha (os c))).
Proof.
  unfold mult. rewrite Ord_orec_unfold. eapply Ord_join_max_r. eapply Ord_zer_rLe.
Qed.

Lemma mult_rLe_r (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LE : beta ≦ᵣ alpha1)
  : mult alpha beta ≦ᵣ mult alpha alpha1.
Proof.
  unfold mult. eapply Ord_orec_rLe; eauto.
  - intros alpha2. eapply Hessenberg.add_base_r.
  - intros alpha2 beta2 LE'. eapply Hessenberg.add_rLe_r. exact LE'.
Qed.

Lemma mult_rEq_r (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (EQ : beta =ᵣ alpha1)
  : mult alpha beta =ᵣ mult alpha alpha1.
Proof.
  rewrite rEq_iff in *. destruct EQ as [LE GE]. split; now eapply mult_rLe_r.
Qed.

Lemma mult_rLe_l (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LE : alpha ≦ᵣ beta)
  : mult alpha alpha1 ≦ᵣ mult beta alpha1.
Proof.
  revert alpha beta LE. induction (rLt_wf alpha1) as [alpha1 _ IH]. intros alpha beta LE. destruct alpha1 as [cs ts].
  unfold mult. rewrite 2 Ord_orec_unfold. eapply Ord_join_spec.
  - eapply Ord_zer_rLe.
  - eapply Ord_sup_rLe_intro. intros c. transitivity (Hessenberg.add beta (Ord.orec Ord.zer (Hessenberg.add beta) (ts c))).
    + eapply Hessenberg.add_isMonotonic2.
      * exact LE.
      * eapply IH. eapply member_implies_rLt. eapply member_intro. exact LE.
    + transitivity (Ord.sup cs (fun c0 : cs => Hessenberg.add beta (Ord.orec Ord.zer (Hessenberg.add beta) (ts c0)))).
      * change ((fun c0 : cs => Hessenberg.add beta (Ord.orec Ord.zer (Hessenberg.add beta) (ts c0))) c ≦ᵣ Ord.sup cs (fun c0 : cs => Hessenberg.add beta (Ord.orec Ord.zer (Hessenberg.add beta) (ts c0)))). eapply Ord_rLe_sup_intro.
      * eapply Ord_join_r.
Qed.

Lemma mult_rEq_l (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (EQ : alpha =ᵣ beta)
  : mult alpha alpha1 =ᵣ mult beta alpha1.
Proof.
  rewrite rEq_iff in *. destruct EQ as [LE GE]. split; now eapply mult_rLe_l.
Qed.

Lemma mult_rLt_r (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LT : beta <ᵣ alpha1)
  (POS : Ord.zer <ᵣ alpha)
  : mult alpha beta <ᵣ mult alpha alpha1.
Proof.
  eapply rLt_rLe_rLt with (y := mult alpha (Ord.suc beta)).
  - eapply rLt_rLe_rLt with (y := Hessenberg.add alpha (mult alpha beta)).
    + eapply Hessenberg.add_rLt_larger_r. exact POS.
    + pose proof (mult_suc alpha beta) as [_ LE]. exact LE.
  - eapply mult_rLe_r. unfold Ord.suc. eapply succ_rLe_intro. exact LT.
Qed.

Lemma mult_zer_l (alpha : Ord.t)
  : mult Ord.zer alpha =ᵣ Ord.zer.
Proof.
  induction alpha as [cs ts IH]. etransitivity.
  - eapply mult_mkNode.
  - rewrite rEq_iff. split.
    + eapply Ord_sup_rLe_intro. intros c. transitivity (Hessenberg.add Ord.zer Ord.zer).
      * eapply Hessenberg.add_isMonotonic2.
        { reflexivity. }
        { pose proof (IH c) as [LE _]. exact LE. }
      * pose proof (Hessenberg.add_zer_l Ord.zer) as [LE _]. exact LE.
    + eapply Ord_zer_rLe.
Qed.

Lemma mult_one_r (alpha : Ord.t)
  : mult alpha Ord_one =ᵣ alpha.
Proof.
  unfold Ord_one. etransitivity.
  - eapply mult_suc.
  - etransitivity.
    + eapply Hessenberg.add_rEq_r. eapply mult_zer_r.
    + eapply Hessenberg.add_zer_r.
Qed.

Lemma mult_one_l (alpha : Ord.t)
  : mult Ord_one alpha =ᵣ alpha.
Proof.
  induction alpha as [cs ts IH]. etransitivity.
  - eapply mult_mkNode.
  - etransitivity.
    + eapply Ord_sup_rEq. intros c. unfold Ord_one. etransitivity.
      * eapply Hessenberg.add_suc_l.
      * eapply Ord_suc_rEq. etransitivity.
        { eapply Hessenberg.add_zer_l. }
        { eapply IH. }
    + symmetry. eapply Ord_mkNode_suc_sup_rEq.
Qed.

#[global]
Instance mult_isMonotonic2 : isMonotonic2 mult.
Proof.
  intros alpha beta alpha1 beta1 LE0 LE1. transitivity (mult beta alpha1).
  - eapply mult_rLe_l. exact LE0.
  - eapply mult_rLe_r. exact LE1.
Qed.

Lemma mult_of_nat (n0 : nat) (n1 : nat)
  : mult (Ord_of_nat n0) (Ord_of_nat n1) =ᵣ Ord_of_nat (n0 * n1).
Proof.
  induction n1 as [ | n1 IH].
  - rewrite Ord_of_nat_zer. rewrite Nat.mul_0_r. eapply mult_zer_r.
  - rewrite Ord_of_nat_suc. rewrite Nat.mul_succ_r. etransitivity.
    + eapply mult_suc.
    + etransitivity.
      * eapply Hessenberg.add_rEq_r. exact IH.
      * etransitivity.
        { eapply Hessenberg.add_comm. }
        { eapply Hessenberg.add_of_nat. }
Qed.

Lemma mult_isOrdinal (alpha : Ord.t) (beta : Ord.t)
  (ORD0 : isOrdinal alpha)
  : isOrdinal (mult alpha beta).
Proof.
  unfold mult. eapply Ord_orec_isOrdinal.
  - eapply zer_isOrdinal.
  - intros alpha1 ORD. eapply Hessenberg.add_isOrdinal; eauto.
Qed.

Definition flip {A : Type} {B : Type} {C : Type} (f : A -> B -> C) : B -> A -> C :=
  fun b : B => fun a : A => f a b.

Definition expn (alpha : Ord.t) : Ord.t -> Ord.t :=
  Ord.orec Ord_one (flip mult alpha).

Lemma arith_expn_larger (alpha : Ord.t) (beta : Ord.t)
  : Ord_exp alpha beta ≦ᵣ expn alpha beta.
Proof.
  revert alpha. induction (rLt_wf beta) as [beta _ IH]. intros alpha. destruct beta as [cs ts].
  transitivity (Ord_join Ord_one (Ord.sup cs (fun c : cs => Ord.mul (Ord_exp alpha (ts c)) alpha))).
  - pose proof (Ord_exp_mkNode alpha cs ts) as [LE _]. exact LE.
  - unfold expn. rewrite Ord_orec_unfold. eapply Ord_join_spec.
    + eapply Ord_join_l.
    + eapply Ord_sup_rLe_intro. intros c. transitivity (mult (Ord_exp alpha (ts c)) alpha).
      * eapply arith_mult_larger.
      * transitivity (mult (Ord.orec Ord_one (flip mult alpha) (ts c)) alpha).
        { eapply mult_rLe_l. eapply IH. eapply member_implies_rLt. eapply member_intro. }
        { transitivity (Ord.sup cs (fun c0 : cs => mult (Ord.orec Ord_one (flip mult alpha) (ts c0)) alpha)).
          - change ((fun c0 : cs => mult (Ord.orec Ord_one (flip mult alpha) (ts c0)) alpha) c ≦ᵣ Ord.sup cs (fun c0 : cs => mult (Ord.orec Ord_one (flip mult alpha) (ts c0)) alpha)). eapply Ord_rLe_sup_intro.
          - eapply Ord_join_r.
        }
Qed.

Lemma expn_zer (base : Ord.t)
  : expn base Ord.zer =ᵣ Ord_one.
Proof.
  unfold expn. eapply Ord_orec_zer.
Qed.

Lemma expn_pos (base : Ord.t) (alpha : Ord.t)
  : Ord.zer <ᵣ expn base alpha.
Proof.
  eapply rLt_rLe_rLt with (y := Ord_one).
  - unfold Ord_one, Ord.suc. eapply rLt_succ_intro.
  - unfold expn. eapply Ord_orec_base_rLe.
Qed.

Lemma expn_base (base : Ord.t) (alpha : Ord.t)
  : Ord_one ≦ᵣ expn base alpha.
Proof.
  unfold expn. eapply Ord_orec_base_rLe.
Qed.

Lemma expn_suc (base : Ord.t) (alpha : Ord.t)
  (POS : Ord.zer <ᵣ base)
  : expn base (Ord.suc alpha) =ᵣ mult (expn base alpha) base.
Proof.
  unfold expn. eapply Ord_orec_suc.
  - intros alpha1. unfold flip. transitivity (mult alpha1 Ord_one).
    + pose proof (mult_one_r alpha1) as [_ LE]. exact LE.
    + eapply mult_rLe_r. unfold Ord_one, Ord.suc. eapply succ_rLe_intro. exact POS.
  - intros alpha1 beta1 LE. unfold flip. eapply mult_rLe_l. exact LE.
Qed.

Lemma expn_rLe_r (base : Ord.t) (alpha : Ord.t) (beta : Ord.t)
  (POS : Ord.zer <ᵣ base)
  (LE : alpha ≦ᵣ beta)
  : expn base alpha ≦ᵣ expn base beta.
Proof.
  unfold expn. eapply Ord_orec_rLe; eauto.
  - intros alpha1. unfold flip. transitivity (mult alpha1 Ord_one).
    + pose proof (mult_one_r alpha1) as [_ LE']. exact LE'.
    + eapply mult_rLe_r. unfold Ord_one, Ord.suc. eapply succ_rLe_intro. exact POS.
  - intros alpha1 beta1 LE'. unfold flip. eapply mult_rLe_l. exact LE'.
Qed.

Lemma expn_rEq_r (base : Ord.t) (alpha : Ord.t) (beta : Ord.t)
  (POS : Ord.zer <ᵣ base)
  (EQ : alpha =ᵣ beta)
  : expn base alpha =ᵣ expn base beta.
Proof.
  rewrite rEq_iff in *. destruct EQ as [LE GE]. split; now eapply expn_rLe_r.
Qed.

Lemma expn_sup (base : Ord.t) (I : Type@{Set_u}) (os : I -> Ord.t)
  (POS : Ord.zer <ᵣ base)
  : expn base (Ord.sup I os) =ᵣ Ord_join Ord_one (Ord.sup I (fun i : I => expn base (os i))).
Proof.
  unfold expn. eapply Ord_orec_sup.
  - intros alpha1. unfold flip. transitivity (mult alpha1 Ord_one).
    + pose proof (mult_one_r alpha1) as [_ LE]. exact LE.
    + eapply mult_rLe_r. unfold Ord_one, Ord.suc. eapply succ_rLe_intro. exact POS.
  - intros alpha1 beta1 LE. unfold flip. eapply mult_rLe_l. exact LE.
Qed.

Lemma expn_sup_inhabited (base : Ord.t) (I : Type@{Set_u}) (os : I -> Ord.t)
  (POS : Ord.zer <ᵣ base)
  (INHABITED : inhabited I)
  : expn base (Ord.sup I os) =ᵣ Ord.sup I (fun i : I => expn base (os i)).
Proof.
  etransitivity.
  - eapply expn_sup. exact POS.
  - destruct INHABITED as [i]. eapply Ord_join_max_r. transitivity (expn base (os i)).
    + unfold expn. eapply Ord_orec_le_base.
      * intros alpha1. unfold flip. transitivity (mult alpha1 Ord_one).
        { pose proof (mult_one_r alpha1) as [_ LE]. exact LE. }
        { eapply mult_rLe_r. unfold Ord_one, Ord.suc. eapply succ_rLe_intro. exact POS. }
      * intros alpha1 beta1 LE. unfold flip. eapply mult_rLe_l. exact LE.
    + change ((fun i0 : I => expn base (os i0)) i ≦ᵣ Ord.sup I (fun i0 : I => expn base (os i0))). eapply Ord_rLe_sup_intro.
Qed.

Lemma expn_join (base : Ord.t) (alpha : Ord.t) (beta : Ord.t)
  (POS : Ord.zer <ᵣ base)
  : expn base (Ord_join alpha beta) =ᵣ Ord_join (expn base alpha) (expn base beta).
Proof.
  unfold Ord_join at 1. etransitivity.
  - eapply expn_sup_inhabited.
    + exact POS.
    + constructor. exact true.
  - unfold Ord_join. eapply Ord_sup_rEq. intros [ | ]; reflexivity.
Qed.

Lemma expn_mkNode (base : Ord.t) (cs : Type@{Set_u}) (os : cs -> Ord.t)
  : expn base (mkNode cs os) =ᵣ Ord_join Ord_one (Ord.sup cs (fun c : cs => mult (expn base (os c)) base)).
Proof.
  unfold expn. rewrite Ord_orec_unfold. reflexivity.
Qed.

Lemma expn_one_r (base : Ord.t)
  (POS : Ord.zer <ᵣ base)
  : expn base Ord_one =ᵣ base.
Proof.
  unfold Ord_one. etransitivity.
  - eapply expn_suc. exact POS.
  - etransitivity.
    + eapply mult_rEq_l. eapply expn_zer.
    + eapply mult_one_l.
Qed.

Lemma expn_rLt_r (base : Ord.t) (alpha : Ord.t) (beta : Ord.t)
  (TWO : Ord_one <ᵣ base)
  (LT : alpha <ᵣ beta)
  : expn base alpha <ᵣ expn base beta.
Proof.
  assert (POS : Ord.zer <ᵣ base).
  { eapply rLe_rLt_rLt with (y := Ord_one).
    - unfold Ord_one, Ord.suc. eapply rLt_implies_rLe. eapply rLt_succ_intro.
    - exact TWO.
  }
  eapply rLt_rLe_rLt with (y := expn base (Ord.suc alpha)).
  - eapply rLt_rLe_rLt with (y := mult (expn base alpha) base).
    + eapply rLe_rLt_rLt with (y := mult (expn base alpha) Ord_one).
      * pose proof (mult_one_r (expn base alpha)) as [_ LE]. exact LE.
      * eapply mult_rLt_r.
        { exact TWO. }
        { eapply expn_pos. }
    + pose proof (expn_suc base alpha POS) as [_ LE]. exact LE.
  - eapply expn_rLe_r.
    + exact POS.
    + unfold Ord.suc. eapply succ_rLe_intro. exact LT.
Qed.

Lemma expn_one_l (alpha : Ord.t)
  : expn Ord_one alpha =ᵣ Ord_one.
Proof.
  induction alpha as [cs ts IH]. etransitivity.
  - eapply expn_mkNode.
  - eapply Ord_join_max_l. eapply Ord_sup_rLe_intro. intros c. transitivity (mult Ord_one Ord_one).
    + eapply mult_rLe_l. pose proof (IH c) as [LE _]. exact LE.
    + pose proof (mult_one_r Ord_one) as [LE _]. exact LE.
Qed.

Lemma expn_rLe_l (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LE : alpha ≦ᵣ beta)
  : expn alpha alpha1 ≦ᵣ expn beta alpha1.
Proof.
  revert alpha beta LE. induction (rLt_wf alpha1) as [alpha1 _ IH]. intros alpha beta LE. destruct alpha1 as [cs ts].
  transitivity (Ord_join Ord_one (Ord.sup cs (fun c : cs => mult (expn alpha (ts c)) alpha))).
  - pose proof (expn_mkNode alpha cs ts) as [LE' _]. exact LE'.
  - transitivity (Ord_join Ord_one (Ord.sup cs (fun c : cs => mult (expn beta (ts c)) beta))).
    + eapply Ord_join_spec.
      * eapply Ord_join_l.
      * eapply Ord_sup_rLe_intro. intros c. transitivity (mult (expn beta (ts c)) beta).
        { eapply mult_isMonotonic2.
          - eapply IH. eapply member_implies_rLt. eapply member_intro. exact LE.
          - exact LE.
        }
        { transitivity (Ord.sup cs (fun c0 : cs => mult (expn beta (ts c0)) beta)).
          - change ((fun c0 : cs => mult (expn beta (ts c0)) beta) c ≦ᵣ Ord.sup cs (fun c0 : cs => mult (expn beta (ts c0)) beta)). eapply Ord_rLe_sup_intro.
          - eapply Ord_join_r.
        }
    + pose proof (expn_mkNode beta cs ts) as [_ GE]. exact GE.
Qed.

Lemma expn_rEq_l (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (EQ : alpha =ᵣ beta)
  : expn alpha alpha1 =ᵣ expn beta alpha1.
Proof.
  rewrite rEq_iff in *. destruct EQ as [LE GE]. split; now eapply expn_rLe_l.
Qed.

Lemma expn_rLe (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t) (beta1 : Ord.t)
  (POS : Ord.zer <ᵣ beta)
  (LE0 : alpha ≦ᵣ beta)
  (LE1 : alpha1 ≦ᵣ beta1)
  : expn alpha alpha1 ≦ᵣ expn beta beta1.
Proof.
  transitivity (expn beta alpha1).
  - eapply expn_rLe_l. exact LE0.
  - eapply expn_rLe_r; assumption.
Qed.

Lemma expn_of_nat (n0 : nat) (n1 : nat)
  (POS : 0 < n0)
  : expn (Ord_of_nat n0) (Ord_of_nat n1) =ᵣ Ord_of_nat (Nat.pow n0 n1).
Proof.
  induction n1 as [ | n1 IH].
  - rewrite Ord_of_nat_zer. change (Ord_of_nat (Nat.pow n0 0)) with Ord_one. eapply expn_zer.
  - rewrite Ord_of_nat_suc. simpl. etransitivity.
    + eapply expn_suc. change (Ord_of_nat O <ᵣ Ord_of_nat n0). eapply Ord_of_nat_rLt. exact POS.
    + etransitivity.
      * eapply mult_rEq_l. exact IH.
      * rewrite Nat.mul_comm. eapply mult_of_nat.
Qed.

Lemma expn_isOrdinal (alpha : Ord.t) (beta : Ord.t)
  (ORD0 : isOrdinal alpha)
  : isOrdinal (expn alpha beta).
Proof.
  unfold expn. eapply Ord_orec_isOrdinal.
  - eapply Ord_one_isOrdinal.
  - intros alpha1 ORD. eapply mult_isOrdinal. exact ORD.
Qed.

End Jacobsthal.

Global Opaque Jacobsthal.mult.
Global Opaque Jacobsthal.expn.

#[local] Infix "⊗" := Jacobsthal.mult (at level 80, right associativity).
#[local] Infix "↑" := Jacobsthal.expn (at level 80, right associativity).

Module ClassicJacobsthal.

#[local] Typeclasses Opaque Ord.t.

#[local] Existing Instance rEq_asSetoid.

#[local] Existing Instance Ord_isProset.

Lemma add_rotate_l (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  : Hessenberg.add alpha (Hessenberg.add beta alpha1) =ᵣ Hessenberg.add beta (Hessenberg.add alpha alpha1).
Proof.
  etransitivity.
  - symmetry. eapply Hessenberg.add_assoc.
  - etransitivity.
    + eapply Hessenberg.add_rEq_l. eapply Hessenberg.add_comm.
    + eapply Hessenberg.add_assoc.
Qed.

Lemma mult_next_rLe (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LT : beta <ᵣ alpha1)
  : Hessenberg.add alpha (Jacobsthal.mult alpha beta) ≦ᵣ Jacobsthal.mult alpha alpha1.
Proof.
  transitivity (Jacobsthal.mult alpha (Ord.suc beta)).
  - pose proof (Jacobsthal.mult_suc alpha beta) as [_ LE]. exact LE.
  - eapply Jacobsthal.mult_rLe_r. unfold Ord.suc. eapply succ_rLe_intro. exact LT.
Qed.

Lemma mult_supremum (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LE : forall alpha2 : Ord.t, alpha2 <ᵣ beta -> Hessenberg.add alpha (Jacobsthal.mult alpha alpha2) ≦ᵣ alpha1)
  : Jacobsthal.mult alpha beta ≦ᵣ alpha1.
Proof.
  destruct beta as [cs ts].
  pose proof (Jacobsthal.mult_mkNode alpha cs ts) as [LE_mult _].
  transitivity (Ord.sup cs (fun c : cs => Hessenberg.add alpha (Jacobsthal.mult alpha (ts c)))).
  - exact LE_mult.
  - eapply Ord_sup_rLe_intro. intros c. eapply LE. eapply member_implies_rLt. eapply member_intro.
Qed.

Lemma mult_rLt_elim (x : Ord.t) (alpha : Ord.t) (beta : Ord.t)
  (LT : x <ᵣ Jacobsthal.mult alpha beta)
  : exists alpha1 : Ord.t, alpha1 <ᵣ beta /\ x <ᵣ Hessenberg.add alpha (Jacobsthal.mult alpha alpha1).
Proof.
  destruct beta as [cs ts].
  pose proof (Jacobsthal.mult_mkNode alpha cs ts) as [LE_mult _].
  pose proof (Hessenberg.Ord_sup_rLt_elim (fun c : cs => Hessenberg.add alpha (Jacobsthal.mult alpha (ts c))) x (rLt_rLe_rLt x (Jacobsthal.mult alpha (mkNode cs ts)) (Ord.sup cs (fun c : cs => Hessenberg.add alpha (Jacobsthal.mult alpha (ts c)))) LT LE_mult)) as [c LT_c].
  exists (ts c). split.
  - eapply member_implies_rLt. eapply member_intro.
  - exact LT_c.
Qed.

Lemma mult_dist (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  : Jacobsthal.mult alpha (Hessenberg.add beta alpha1) =ᵣ Hessenberg.add (Jacobsthal.mult alpha beta) (Jacobsthal.mult alpha alpha1).
Proof.
  revert beta alpha1. eapply Hessenberg.double_well_founded_induction with (RA := rLt) (RB := rLt); [exact rLt_wf | exact rLt_wf |].
  intros beta alpha1 IHL IHR. rewrite rEq_iff. split.
  - eapply mult_supremum. intros beta2 LT.
    pose proof (Hessenberg.add_rLt_elim beta2 beta alpha1 LT) as [[beta1 [LT1 LE1]] | [alpha2 [LT2 LE2]]].
    + transitivity (Hessenberg.add alpha (Jacobsthal.mult alpha (Hessenberg.add beta1 alpha1))).
      * eapply Hessenberg.add_rLe_r. eapply Jacobsthal.mult_rLe_r. exact LE1.
      * transitivity (Hessenberg.add alpha (Hessenberg.add (Jacobsthal.mult alpha beta1) (Jacobsthal.mult alpha alpha1))).
        { eapply Hessenberg.add_rLe_r. pose proof (IHL beta1 LT1) as [LE_IH _]. exact LE_IH. }
        { transitivity (Hessenberg.add (Hessenberg.add alpha (Jacobsthal.mult alpha beta1)) (Jacobsthal.mult alpha alpha1)).
          - pose proof (Hessenberg.add_assoc alpha (Jacobsthal.mult alpha beta1) (Jacobsthal.mult alpha alpha1)) as [_ GE]. exact GE.
          - eapply Hessenberg.add_rLe_l. eapply mult_next_rLe. exact LT1.
        }
    + transitivity (Hessenberg.add alpha (Jacobsthal.mult alpha (Hessenberg.add beta alpha2))).
      * eapply Hessenberg.add_rLe_r. eapply Jacobsthal.mult_rLe_r. exact LE2.
      * transitivity (Hessenberg.add alpha (Hessenberg.add (Jacobsthal.mult alpha beta) (Jacobsthal.mult alpha alpha2))).
        { eapply Hessenberg.add_rLe_r. pose proof (IHR alpha2 LT2) as [LE_IH _]. exact LE_IH. }
        { transitivity (Hessenberg.add (Jacobsthal.mult alpha beta) (Hessenberg.add alpha (Jacobsthal.mult alpha alpha2))).
          - pose proof (add_rotate_l alpha (Jacobsthal.mult alpha beta) (Jacobsthal.mult alpha alpha2)) as [LE_rot _]. exact LE_rot.
          - eapply Hessenberg.add_rLe_r. eapply mult_next_rLe. exact LT2.
        }
  - eapply Hessenberg.add_spec.
    + intros x LT.
      pose proof (mult_rLt_elim x alpha beta LT) as [beta1 [LT1 LT_x]].
      eapply rLt_rLe_rLt with (y := Hessenberg.add (Hessenberg.add alpha (Jacobsthal.mult alpha beta1)) (Jacobsthal.mult alpha alpha1)).
      * eapply Hessenberg.add_rLt_l. exact LT_x.
      * transitivity (Hessenberg.add alpha (Hessenberg.add (Jacobsthal.mult alpha beta1) (Jacobsthal.mult alpha alpha1))).
        { pose proof (Hessenberg.add_assoc alpha (Jacobsthal.mult alpha beta1) (Jacobsthal.mult alpha alpha1)) as [LE_assoc _]. exact LE_assoc. }
        { transitivity (Hessenberg.add alpha (Jacobsthal.mult alpha (Hessenberg.add beta1 alpha1))).
          - eapply Hessenberg.add_rLe_r. pose proof (IHL beta1 LT1) as [_ GE_IH]. exact GE_IH.
          - transitivity (Jacobsthal.mult alpha (Ord.suc (Hessenberg.add beta1 alpha1))).
            + pose proof (Jacobsthal.mult_suc alpha (Hessenberg.add beta1 alpha1)) as [_ GE_mult]. exact GE_mult.
            + eapply Jacobsthal.mult_rLe_r. unfold Ord.suc. eapply succ_rLe_intro. eapply Hessenberg.add_rLt_l. exact LT1.
        }
    + intros y LT.
      pose proof (mult_rLt_elim y alpha alpha1 LT) as [alpha2 [LT2 LT_y]].
      eapply rLt_rLe_rLt with (y := Hessenberg.add (Jacobsthal.mult alpha beta) (Hessenberg.add alpha (Jacobsthal.mult alpha alpha2))).
      * eapply Hessenberg.add_rLt_r. exact LT_y.
      * transitivity (Hessenberg.add alpha (Hessenberg.add (Jacobsthal.mult alpha beta) (Jacobsthal.mult alpha alpha2))).
        { pose proof (add_rotate_l alpha (Jacobsthal.mult alpha beta) (Jacobsthal.mult alpha alpha2)) as [_ GE_rot]. exact GE_rot. }
        { transitivity (Hessenberg.add alpha (Jacobsthal.mult alpha (Hessenberg.add beta alpha2))).
          - eapply Hessenberg.add_rLe_r. pose proof (IHR alpha2 LT2) as [_ GE_IH]. exact GE_IH.
          - transitivity (Jacobsthal.mult alpha (Ord.suc (Hessenberg.add beta alpha2))).
            + pose proof (Jacobsthal.mult_suc alpha (Hessenberg.add beta alpha2)) as [_ GE_mult]. exact GE_mult.
            + eapply Jacobsthal.mult_rLe_r. unfold Ord.suc. eapply succ_rLe_intro. eapply Hessenberg.add_rLt_r. exact LT2.
        }
Qed.

Lemma mult_assoc (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  : Jacobsthal.mult (Jacobsthal.mult alpha beta) alpha1 =ᵣ Jacobsthal.mult alpha (Jacobsthal.mult beta alpha1).
Proof.
  induction alpha1 as [cs ts IH]. etransitivity.
  - eapply Jacobsthal.mult_mkNode.
  - etransitivity.
    + eapply Ord_sup_rEq. intros c. eapply Hessenberg.add_rEq_r. exact (IH c).
    + symmetry. etransitivity.
      * eapply Jacobsthal.mult_rEq_r. eapply Jacobsthal.mult_mkNode.
      * etransitivity.
        { eapply Jacobsthal.mult_sup. }
        { eapply Ord_sup_rEq. intros c. eapply mult_dist. }
Qed.

Lemma expn_add (base : Ord.t) (alpha : Ord.t) (beta : Ord.t)
  (POS : Ord.zer <ᵣ base)
  : Jacobsthal.expn base (Ord.add alpha beta) =ᵣ Jacobsthal.mult (Jacobsthal.expn base alpha) (Jacobsthal.expn base beta).
Proof.
  revert alpha. induction (rLt_wf beta) as [beta _ IH]. intros alpha. destruct beta as [cs ts].
  etransitivity.
  - eapply Jacobsthal.expn_rEq_r. exact POS. eapply Ord_add_mkNode.
  - etransitivity.
    + eapply Jacobsthal.expn_join. exact POS.
    + etransitivity.
      * eapply Ord_join_rEq_r. eapply Jacobsthal.expn_sup. exact POS.
      * etransitivity.
        { eapply Ord_join_rEq_r. eapply Ord_join_rEq_r. eapply Ord_sup_rEq. intros c. etransitivity.
          - eapply Jacobsthal.expn_suc. exact POS.
          - etransitivity.
            + eapply Jacobsthal.mult_rEq_l. eapply IH. eapply member_implies_rLt. eapply member_intro.
            + eapply mult_assoc.
        }
        { etransitivity.
          - eapply Ord_join_absorb_l. eapply Jacobsthal.expn_base.
          - symmetry. etransitivity.
            + eapply Jacobsthal.mult_rEq_r. eapply Jacobsthal.expn_mkNode.
            + etransitivity.
              * eapply Jacobsthal.mult_join.
              * etransitivity.
                { eapply Ord_join_rEq_l. eapply Jacobsthal.mult_one_r. }
                { eapply Ord_join_rEq_r. eapply Jacobsthal.mult_sup. }
        }
Qed.

Lemma expn_mult (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (POS : Ord.zer <ᵣ alpha)
  : Jacobsthal.expn alpha (Ord.mul beta alpha1) =ᵣ Jacobsthal.expn (Jacobsthal.expn alpha beta) alpha1.
Proof.
  induction alpha1 as [cs ts IH]. etransitivity.
  - eapply Jacobsthal.expn_rEq_r. exact POS. eapply Ord_mul_mkNode.
  - etransitivity.
    + eapply Jacobsthal.expn_sup. exact POS.
    + symmetry. etransitivity.
      * eapply Jacobsthal.expn_mkNode.
      * eapply Ord_join_rEq_r. eapply Ord_sup_rEq. intros c. symmetry. etransitivity.
        { eapply expn_add. exact POS. }
        { eapply Jacobsthal.mult_rEq_l. eapply IH. }
Qed.

End ClassicJacobsthal.

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
  revert alpha beta x_rGe1 x_rGe2 H_isOrdinal1 H_isOrdinal2. pose proof (rLt_wf x) as H_ACC. induction H_ACC as [x _ IH].
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

Section toSet.

#[local] Existing Instance toSet_isSetoid.

#[local] Existing Instance toSet_isWoset.

#[local] Infix "\in" := member.

#[local] Infix "\subseteq" := isSubsetOf.

Lemma FromOrderType_toSet_rEq (alpha : Tree)
  : FromOrderType (toSet alpha) =ᵣ alpha.
Proof.
  symmetry. etransitivity.
  - symmetry. eapply rank_rEq.
  - eapply Totalify.fromWfSet_rEq.
Qed.

Lemma toSet_wlt_iff (alpha : Tree) (x : toSet alpha) (y : toSet alpha)
  : x ≺ y <-> (exists z : toSet alpha, x == z /\ toSet_wlt alpha z y).
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

Lemma FromOrderType_toSet_id (alpha : Tree)
  (ORDINAL : isOrdinal alpha)
  : FromOrderType (toSet alpha) == alpha.
Proof.
  eapply Ordinal_rEq_Ordinal_elim.
  - eapply FromOrderType_isOrdinal.
  - exact ORDINAL.
  - eapply FromOrderType_toSet_rEq.
Qed.

End toSet.

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
    + pose proof (chain_good i2) as [? ? ?]. hexploit (COMPLETE _ _ (P_incl _ H_P1) H_P2); auto.
      intros [? | [? | ?]]; [left; tauto | right | right]; [left | right]; exists i2; tauto.
    + pose proof (chain_good i1) as [? ? ?]. hexploit (COMPLETE _ _ H_P1 (P_incl _ H_P2)); auto.
      intros [? | [? | ?]]; [left; tauto | right | right]; [left | right]; exists i1; tauto.
  - intros x1. econs. intros x0 [i H_R]. pose proof (chain_good i) as [? ? ?].
    assert (H_ACC : Acc (chain i).(R) x0) by eauto.
    pose proof (SOUND _ _ H_R) as [H_P _]. clear H_R. induction H_ACC as [x0 _ IH]; intros; econs; intros y [i' H_R'].
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
  : forall x : X, (Ord.rec base next pair_sup (hartogs pair)).(P) x.
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
  hexploit (next_exhausted (Ord.rec base next pair_sup (hartogs pair))); i.
  - eapply InducedOrdinal.rec_good; eauto.
    { ii; reflexivity. }
    { ii; transitivity d2; eauto. }
    { ii; eapply pair_sup_good; eauto. }
    { ii; eapply pair_sup_isSupremum'; eauto. }
    { ii; eapply base_good. }
  - des; eauto. exfalso. eapply H0. eapply x0. eauto.
Qed.

Lemma eventually_exhausted
  : exists alpha : Ord.t, forall x : X, (Ord.rec base next pair_sup alpha).(P) x.
Proof.
  exists (hartogs pair). eapply eventually_exhausted'.
Qed.

Lemma well_ordering_aux
  : exists R : X -> X -> Prop, well_founded R /\ (forall x1, forall x2, x1 == x2 \/ R x1 x2 \/ R x2 x1) /\ Transitive R /\ eqPropCompatible2 R.
Proof.
  hexploit eventually_exhausted. intros H_P. des.
  assert (GOOD : good (Ord.rec base next pair_sup alpha)).
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
  exists (B.transitiveClosure (Ord.rec base next pair_sup alpha).(R)). destruct GOOD. splits.
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
    done!.
  - eapply @Functional_Extensionality with (b_fun_ext := true) (f := R0) (f' := R1); eauto. i.
    eapply @Functional_Extensionality with (b_fun_ext := true) (f := R0 x) (f' := R1 x); eauto. i.
    eapply @Propositional_Extensionality with (b_prop_ext := true) (P := R0 x x0) (P' := R1 x x0); eauto.
    done!.
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
  - left. now rewrite -> H.
  - left. now rewrite -> H.
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

Module Cardinal1.

Section HARTOGS.

#[local] Infix "\in" := member.

#[local] Existing Instance toSet_isSetoid.

#[local] Existing Instance toSet_isWoset.

Definition Hartogs (D : Type@{Set_u}) {SETOID : isSetoid D} : Tree :=
  mkNode { P : D -> Prop & { R : @sig D P -> @sig D P -> Prop | well_founded R /\ (forall x, forall x', x == x' \/ R x x' \/ R x' x) /\ Transitive R /\ eqPropCompatible2 R } } (fun X => @fromWfSet (@sig D (projT1 X)) (proj1_sig (projT2 X)) (proj1 (proj2_sig (projT2 X)))).

Lemma Hartogs_isTransitiveSet {D : Type@{Set_u}} {SETOID : isSetoid D}
  : isTransitiveSet (Hartogs D).
Proof.
  intros y y_in z [cy z_eq]. rewrite z_eq. clear z z_eq. destruct y as [csy tsy]; simpl in *.
  destruct y_in as [(P & R & R_wf & R_total & R_Transitive & R_eqPropCompatible2) y_eq]; simpl in *.
  destruct y_eq as [H1_eq H2_eq]; unred_eqTree. pose proof (H1_eq cy) as [c EQ].
  rewrite EQ. rewrite fromWf_pirrel with (R_wf := _) (R_wf' := R_wf).
  rewrite fromWfSet_InitialSegment; eauto.
  refine (let P' (d : D) : Prop := { H_d : P d | R (@exist _ _ d H_d) c } in _).
  refine (let R' (x1 : @sig D P') (x2 : @sig D P') : Prop := R (@exist _ _ (proj1_sig x1) (proj1_sig (proj2_sig x1))) (@exist _ _ (proj1_sig x2) (proj1_sig (proj2_sig x2))) in _).
  assert (H1_R' : well_founded R').
  { exact (@relation_on_image_liftsWellFounded _ _ R (fun x : @sig D P' => @exist D P (proj1_sig x) (proj1_sig (proj2_sig x))) R_wf). }
  assert (H2_R' : forall x, forall x', x == x' \/ R' x x' \/ R' x' x).
  { intros x1 x2; simpl. exact (R_total (@exist _ _ (proj1_sig x1) (proj1_sig (proj2_sig x1))) (@exist _ _ (proj1_sig x2) (proj1_sig (proj2_sig x2)))). }
  assert (H3_R' : Transitive R').
  { intros x1 x2 x3; simpl. exact (R_Transitive (@exist _ _ (proj1_sig x1) (proj1_sig (proj2_sig x1))) (@exist _ _ (proj1_sig x2) (proj1_sig (proj2_sig x2))) (@exist _ _ (proj1_sig x3) (proj1_sig (proj2_sig x3)))). }
  assert (H4_R' : eqPropCompatible2 R').
  { intros x1 x2 y1 y2; simpl. exact (R_eqPropCompatible2 (@exist _ _ (proj1_sig x1) (proj1_sig (proj2_sig x1))) (@exist _ _ (proj1_sig x2) (proj1_sig (proj2_sig x2))) (@exist _ _ (proj1_sig y1) (proj1_sig (proj2_sig y1))) (@exist _ _ (proj1_sig y2) (proj1_sig (proj2_sig y2)))). }
  exists (@existT _ _ P' (@exist _ _ R' (conj H1_R' (conj H2_R' (conj H3_R' H4_R'))))). simpl childnodes. simpl. split; intros a.
  - set (f := fun a : @sig (@sig D P) (fun y => R y c) => let '(@exist _ _ (@exist _ _ x p) r) := a in @exist D P' x (@exist (P x) (fun H_d => R (@exist _ P x H_d) c) p r)).
    destruct a as [[x p] r]. exists (@exist _ _ x (@exist _ _ p r)). unred_eqTree. eapply fromWf_eq_fromWf_intro with (f := f). intros [[? ?] ?] [? [? ?]]; simpl. unfold binary_relation_on_image, f. split.
    + intros ([[? ?] ?] & H1 & H2); simpl in *. eexists; split; [red | reflexivity]. simpl. clarify. now rewrite proof_irrelevance with (p1 := x2) (p2 := p1).
    + intros ([? [? ?]] & H1 & H2); simpl in *. eexists (@exist _ _ (@exist _ _ _ _) _); simpl; split; [ | reflexivity]; clarify. cbv in H1. now rewrite proof_irrelevance with (p1 := p0) (p2 := x4).
  - set (f := fun a : @sig D P' => let '(@exist _ _ x (@exist _ _ p r)) := a in @exist (@sig D P) (fun y => R y c) (@exist _ _ x p) r).
    destruct a as [x [p r]]. exists (@exist _ _ (@exist _ _ x p) r). unred_eqTree. symmetry. eapply fromWf_eq_fromWf_intro with (f := f). intros [? [? ?]] [[? ?] ?]; simpl. unfold binary_relation_on_image, f. split.
    + intros ([? [? ?]] & H1 & H2); simpl in *. eexists (@exist _ _ (@exist _ _ _ _) _); simpl; split; [ | reflexivity]; clarify. cbv in H1. now rewrite proof_irrelevance with (p1 := p0) (p2 := x4).
    + intros ([[? ?] ?] & H1 & H2); simpl in *. eexists (@exist D _ _ (@exist _ _ _ _)); simpl; split; [ | reflexivity]; clarify. red. simpl. now rewrite proof_irrelevance with (p1 := x1) (p2 := p1).
Qed.

Lemma Hartogs_isOrdinal {D : Type@{Set_u}} {SETOID : isSetoid D}
  : isOrdinal (Hartogs D).
Proof.
  enough (claim : forall alpha, alpha \in Hartogs D -> isOrdinal alpha).
  { split.
    - eapply Hartogs_isTransitiveSet.
    - intros beta beta_in. now pose proof (claim beta beta_in) as [? ?].
  }
  intros alpha [(P & R & R_wf & R_total & R_Transitive & R_eqPropCompatible2) alpha_eq]; simpl in *.
  rewrite alpha_eq. rewrite fromWfSet_pirrel with (R_wf' := R_wf).
  pose (WOSET := @O.WellfoundedToset_isWoset classic (@sig D P) (@subSetoid D SETOID P) {| wltProp := R; wltProp_well_founded := R_wf; wltProp_Transitive := R_Transitive |} R_eqPropCompatible2 R_total).
  change (isOrdinal (@FromOrderType (@sig D P) (@subSetoid D SETOID P) WOSET)). eapply FromOrderType_isOrdinal.
Qed.

Theorem Hartogs_spec1 `{Axms : ClassicalAxioms (b_AC := true)} (D : Type@{Set_u}) (D_isSetoid : isSetoid D) (alpha : Ord.t)
  (H_isOrdinal : isOrdinal alpha)
  : alpha \in Hartogs D <-> Cardinality.mk (toSet alpha) (toSet_isSetoid alpha) =< Cardinality.mk D D_isSetoid.
Proof.
  pose (RA_wf := (toSet_isWoset alpha).(Woset_isWellPoset).(wltProp_well_founded)).
  set (RA := (toSet_isWoset alpha).(Woset_isWellPoset).(wltProp)) in *.
  assert (claim2 : forall x : toSet alpha, forall x' : toSet alpha, eqProp (isSetoid := toSet_isSetoid alpha) x x' \/ RA x x' \/ RA x' x).
  { eapply @O.wlt_trichotomous with (SETOID := toSet_isSetoid alpha) (WOSET := toSet_isWoset alpha). exact classic. }  
  split.
  - intros [(P & R & R_wf & R_total & R_Transitive & R_eqPropCompatible2) alpha_eq]; simpl in *.
    pose proof (fromWfSet_embed' (toSet alpha) (@sig D P) (toSet_isSetoid alpha) (@subSetoid D D_isSetoid P)) as HH.
    rewrite <- Ordinal1.FromOrderType_toSet_id in alpha_eq by eassumption.
    rewrite fromWfSet_pirrel with (R_wf' := R_wf) in alpha_eq.
    change (FromOrderType (toSet alpha)) with (fromWfSet RA RA_wf) in alpha_eq.
    assert (claim1 : fromWfSet RA RA_wf ≦ᵣ fromWfSet R R_wf) by now rewrite alpha_eq.
    specialize (HH RA R RA_wf R_wf (toSet_isWoset alpha).(Woset_eqPropCompatible2) R_eqPropCompatible2 (toSet_isWoset alpha).(Woset_isWellPoset).(wltProp_Transitive) R_Transitive claim1 claim2 R_total).
    assert (claim3 : forall x1 : toSet alpha, forall x2 : toSet alpha, eqProp (isSetoid := toSet_isSetoid alpha) x1 x2 -> forall x : toSet alpha, RA x1 x -> RA x2 x).
    { pose proof (toSet_isWoset alpha).(Woset_eqPropCompatible2) as X. ii; eapply X with (x2 := x1) (y2 := x); eauto with *. }
    assert (claim4 : forall x1, forall x2, x1 == x2 -> forall x : @sig D P, R x1 x -> R x2 x).
    { ii. now rewrite <- H. }
    destruct HH as [f H_f]. exists (fun x : toSet alpha => proj1_sig (f x)).
    + red; simpl Cardinality.carrier; ii. pose proof (R_total (f x1) (f x2)) as [H_EQ | [H_LT | H_GT]]; eauto.
      * rewrite <- H_f in H_LT. exfalso. contradiction (well_founded_implies_Irreflexive' (SETOID := toSet_isSetoid alpha) RA RA_wf claim3 x1 x2 x_EQ H_LT).
      * rewrite <- H_f in H_GT. exfalso. symmetry in x_EQ. contradiction (well_founded_implies_Irreflexive' (SETOID := toSet_isSetoid alpha) RA RA_wf claim3 x2 x1 x_EQ H_GT).
    + simpl Cardinality.carrier; ii. pose proof (claim2 x1 x2) as [H_EQ | [H_LT | H_GT]]; eauto.
      * rewrite -> H_f in H_LT. exfalso. contradiction (well_founded_implies_Irreflexive' R R_wf claim4 (f x1) (f x2) H H_LT).
      * rewrite -> H_f in H_GT. exfalso. symmetry in H. contradiction (well_founded_implies_Irreflexive' R R_wf claim4 (f x2) (f x1) H H_GT).
  - intros [f f_cong f_inj].
    set (A := toSet alpha).
    set (RA_Transitive := (toSet_isWoset alpha).(Woset_isWellPoset).(wltProp_Transitive)).
    set (RA_eqPropCompatible2 := (toSet_isWoset alpha).(Woset_eqPropCompatible2)).
    pose (Pimg := fun d : D => exists x, f x == d).
    exploit (Axiom_of_Choice (@sig D Pimg) (fun _ => toSet alpha) (fun y => fun x => f x == proj1_sig y)).
    { intros [d Hd]; exact Hd. }
    intros [g Hg]. change (forall y : { d : D | Pimg d }, f (g y) == proj1_sig y) in Hg.
    set (R := binary_relation_on_image RA g).
    assert (g_cong : eqPropCompatible1 (B_isSetoid := toSet_isSetoid alpha) g).
    { intros y1 y2 Hy. eapply f_inj. now do 2 rewrite Hg. }
    assert (R_wf : well_founded R) by exact (relation_on_image_liftsWellFounded RA g RA_wf).
    assert (R_total : forall x : { d : D | Pimg d }, forall x' : { d : D | Pimg d }, x == x' \/ R x x' \/ R x' x).
    { intros y1 y2.
      pose proof (O.wlt_trichotomous (classic := classic) (WOSET := toSet_isWoset alpha) (g y1) (g y2)) as [H_eq | [H_lt | H_gt]].
      - left. change (proj1_sig y1 == proj1_sig y2). do 2 rewrite <- Hg. now rewrite H_eq.
      - right; left; exact H_lt.
      - right; right; exact H_gt.
    }
    assert (R_Transitive : Transitive R).
    { ii; eapply RA_Transitive; eauto. }
    assert (R_eqPropCompatible2 : eqPropCompatible2 R).
    { ii; eapply RA_eqPropCompatible2; eapply g_cong; eauto. }
    exists (@existT _ _ Pimg (@exist _ _ R (conj R_wf (conj R_total (conj R_Transitive R_eqPropCompatible2))))).
    simpl. rewrite fromWfSet_pirrel with (R_wf' := R_wf). simpl Cardinality.carrier in *.
    rewrite <- Ordinal1.FromOrderType_toSet_id with (alpha := alpha); eauto.
    eapply Ordinal1.Ordinal_rEq_Ordinal_elim.
    { eapply FromOrderType_isOrdinal. }
    { pose (WOSET := @O.WellfoundedToset_isWoset classic (@sig D Pimg) (@subSetoid D D_isSetoid Pimg) {| wltProp := R; wltProp_well_founded := R_wf; wltProp_Transitive := R_Transitive |} R_eqPropCompatible2 R_total).
      change (isOrdinal (@FromOrderType _ _ WOSET)). eapply FromOrderType_isOrdinal.
    }
    set (h := fun x : toSet alpha => @exist D Pimg (f x) (@ex_intro _ _ x (eqProp_Equivalence.(Equivalence_Reflexive) (f x)))).
    assert (claim : forall x, g (h x) == x).
    { intros x. eapply f_inj. now rewrite Hg. }
    unfold FromOrderType. split.
    + eapply fromWfSet_cong with (f := h). intros x1 x2 H_lt. eapply Woset_eqPropCompatible2 with (x2 := x1) (y2 := x2); eauto.
    + eapply fromWfSet_cong with (f := g). intros y1 y2 H_lt; eauto.
Qed.

#[local] Existing Instance children_isSetoid.

#[local] Existing Instance children_isWoset.

Theorem Hartogs_spec2 `{Axms : ClassicalAxioms (b_AC := true)} (D : Type@{Set_u}) (D_isSetoid : isSetoid D) (alpha : Tree)
  (H_isOrdinal : isOrdinal alpha)
  : alpha \in Hartogs D <-> Cardinality.mk (children alpha) (children_isSetoid alpha) =< Cardinality.mk D D_isSetoid.
Proof.
  pose (RA := isElemOf alpha).
  pose (RA_wf := (children_isWoset alpha H_isOrdinal).(Woset_isWellPoset).(wltProp_well_founded)).
  pose (RA_Transitive := (children_isWoset alpha H_isOrdinal).(Woset_isWellPoset).(wltProp_Transitive)).
  pose (RA_eqPropCompatible2 := (children_isWoset alpha H_isOrdinal).(Woset_eqPropCompatible2)).
  assert (RA_total : forall x : children alpha, forall x' : children alpha, x == x' \/ RA x x' \/ RA x' x).
  { eapply @O.wlt_trichotomous with (SETOID := children_isSetoid alpha) (WOSET := children_isWoset alpha H_isOrdinal). exact classic. }
  split.
  - intros [(P & R & R_wf & R_total & R_Transitive & R_eqPropCompatible2) alpha_eq].
    pose proof (fromWfSet_embed' (children alpha) (@sig D P) (children_isSetoid alpha) (@subSetoid D D_isSetoid P)) as HH.
    unshelve rewrite <- FromOrderType_children_id in alpha_eq; eauto.
    simpl childnodes in alpha_eq. rewrite fromWfSet_pirrel with (R_wf' := R_wf) in alpha_eq.
    change (@FromOrderType (children alpha) (children_isSetoid alpha) (children_isWoset alpha H_isOrdinal)) with (@fromWfSet (children alpha) RA RA_wf) in alpha_eq.
    assert (claim1 : @fromWfSet (children alpha) RA RA_wf ≦ᵣ @fromWfSet (@sig D P) R R_wf).
    { rewrite <- alpha_eq. unfold FromOrderType. now eapply fromWfSet_cong with (f := fun x => x). }
    specialize (HH RA R RA_wf R_wf RA_eqPropCompatible2 R_eqPropCompatible2 RA_Transitive R_Transitive claim1 RA_total R_total).
    assert (claim3 : forall x1 : children alpha, forall x2 : children alpha, x1 == x2 -> forall x : children alpha, RA x1 x -> RA x2 x).
    { intros x1 x2 H x Hlt. eapply RA_eqPropCompatible2 with (x2 := x1) (y2 := x); eauto with *. }
    assert (claim4 : forall x1 : @sig D P, forall x2 : @sig D P, x1 == x2 -> forall x : @sig D P, R x1 x -> R x2 x).
    { intros x1 x2 H x Hlt. now rewrite <- H. }
    destruct HH as [g Hg]. exists (fun x : children alpha => proj1_sig (g x)).
    + red. simpl. intros x1 x2 x_EQ. pose proof (R_total (g x1) (g x2)) as [H_EQ | [H_LT | H_GT]]; eauto.
      * rewrite <- Hg in H_LT. exfalso. contradiction (well_founded_implies_Irreflexive' (SETOID := children_isSetoid alpha) RA RA_wf claim3 x1 x2 x_EQ H_LT).
      * rewrite <- Hg in H_GT. exfalso. symmetry in x_EQ. contradiction (well_founded_implies_Irreflexive' (SETOID := children_isSetoid alpha) RA RA_wf claim3 x2 x1 x_EQ H_GT).
    + intros x1 x2 H. pose proof (RA_total x1 x2) as [H_EQ | [H_LT | H_GT]]; eauto.
      * rewrite -> Hg in H_LT. exfalso. contradiction (well_founded_implies_Irreflexive' R R_wf claim4 (g x1) (g x2) H H_LT).
      * rewrite -> Hg in H_GT. exfalso. symmetry in H. contradiction (well_founded_implies_Irreflexive' R R_wf claim4 (g x2) (g x1) H H_GT).
  - intros [f f_cong f_inj]. pose (Pimg := fun d : D => exists x : children alpha, f x == d).
    exploit (Axiom_of_Choice (@sig D Pimg) (fun _ => children alpha) (fun y => fun x => f x == proj1_sig y)).
    { intros [d Hd]. exact Hd. }
    intros [g Hg]. change (forall y : { d : D | Pimg d }, f (g y) == proj1_sig y) in Hg.
    pose (R := binary_relation_on_image RA g).
    assert (g_cong : eqPropCompatible1 g).
    { intros y1 y2 Hy. eapply f_inj. now do 2 rewrite Hg. }
    assert (R_wf : well_founded R).
    { exact (relation_on_image_liftsWellFounded RA g RA_wf). }
    assert (R_total : forall y1 : { d : D | Pimg d }, forall y2 : { d : D | Pimg d }, y1 == y2 \/ R y1 y2 \/ R y2 y1).
    { intros y1 y2. pose proof (O.wlt_trichotomous (classic := classic) (SETOID := children_isSetoid alpha) (WOSET := children_isWoset alpha H_isOrdinal) (g y1) (g y2)) as [H_eq | [H_lt | H_gt]].
      - left. change (proj1_sig y1 == proj1_sig y2). do 2 rewrite <- Hg. now rewrite H_eq.
      - right; left; exact H_lt.
      - right; right; exact H_gt.
    }
    assert (R_Transitive : Transitive R).
    { intros y1 y2 y3 H12 H23. eapply RA_Transitive; eauto. }
    assert (R_eqPropCompatible2 : eqPropCompatible2 R).
    { intros y1 y1' y2 y2' Hy1 Hy2. eapply RA_eqPropCompatible2; eauto. }
    exists (@existT _ _ Pimg (@exist _ _ R (conj R_wf (conj R_total (conj R_Transitive R_eqPropCompatible2))))); simpl.
    rewrite fromWfSet_pirrel with (R_wf' := R_wf). unshelve rewrite <- FromOrderType_children_id with (alpha := alpha); eauto.
    eapply Ordinal1.Ordinal_rEq_Ordinal_elim.
    + eapply FromOrderType_isOrdinal.
    + pose (WOSET := @O.WellfoundedToset_isWoset classic (@sig D Pimg) (@subSetoid D D_isSetoid Pimg) {| wltProp := R; wltProp_well_founded := R_wf; wltProp_Transitive := R_Transitive |} R_eqPropCompatible2 R_total).
      change (isOrdinal (@FromOrderType _ _ WOSET)). eapply FromOrderType_isOrdinal.
    + set (h := fun x : children alpha => @exist D Pimg (f x) (@ex_intro _ _ x (eqProp_Equivalence.(Equivalence_Reflexive) (f x)))).
      assert (claim : forall x, g (h x) == x).
      { intros x. eapply f_inj. now rewrite Hg. }
      unfold FromOrderType. split.
      * eapply fromWfSet_cong with (f := h). intros x1 x2 Hlt. eapply RA_eqPropCompatible2 with (x2 := x1) (y2 := x2); eauto.
      * eapply fromWfSet_cong with (f := g); eauto.
Qed.

Corollary Hartogs_rLt_iff `{Axms : ClassicalAxioms (b_AC := true)} (D : Type@{Set_u}) (D_isSetoid : isSetoid D) (alpha : Tree)
  (H_isOrdinal : isOrdinal alpha)
  : alpha <ᵣ Hartogs D <-> Cardinality.mk (children alpha) (children_isSetoid alpha) =< Cardinality.mk D D_isSetoid.
Proof.
  split.
  - intros Hlt. rewrite <- Hartogs_spec2; eauto.
    eapply Ordinal1.Ordinal_rLt_Ordinal_elim; eauto using Hartogs_isOrdinal.
  - intros Hle. eapply member_implies_rLt. rewrite -> Hartogs_spec2; eauto.
Qed.

Corollary Hartogs_not_embed `{Axms : ClassicalAxioms (b_AC := true)} (D : Type@{Set_u}) (D_isSetoid : isSetoid D)
  : ~ Cardinality.mk (children (Hartogs D)) (children_isSetoid (Hartogs D)) =< Cardinality.mk D D_isSetoid.
Proof.
  intros Hle. pose proof (proj2 (Hartogs_spec2 D D_isSetoid (Hartogs D) (Hartogs_isOrdinal)) Hle) as H_in.
  contradiction (StrictOrder_Irreflexive (Hartogs D)). exact (member_implies_rLt (Hartogs D) (Hartogs D) H_in).
Qed.

Corollary Hartogs_minimal_nonembed `{Axms : ClassicalAxioms (b_AC := true)} (D : Type@{Set_u}) (D_isSetoid : isSetoid D)
  (beta : Tree)
  (H_isOrdinal : isOrdinal beta)
  (H_nLe : ~ Cardinality.mk (children beta) (children_isSetoid beta) =< Cardinality.mk D D_isSetoid)
  : Hartogs D ≦ᵣ beta.
Proof.
  eapply NNPP; intro H_contra.
  pose proof (proj2 (InducedOrdinal.rLt_iff_not_rGe beta (Hartogs D)) H_contra) as Hlt.
  pose proof (Ordinal1.Ordinal_rLt_Ordinal_elim beta (Hartogs D) H_isOrdinal (Hartogs_isOrdinal) Hlt) as Hin.
  contradiction H_nLe. exact (proj1 (Hartogs_spec2 D D_isSetoid beta H_isOrdinal) Hin).
Qed.

Lemma Hartogs_ordertype_iff `{Axms : ClassicalAxioms (b_AC := true)} (D : Type@{Set_u}) (D_isSetoid : isSetoid D) (A : Type@{Set_u}) (A_isSetoid : isSetoid A) (WOSET : @isWoset A A_isSetoid)
  : @FromOrderType A A_isSetoid WOSET \in Hartogs D <-> Cardinality.mk A A_isSetoid =< Cardinality.mk D D_isSetoid.
Proof.
  split.
  - intros H_in.
    pose proof (proj1 (Hartogs_spec2 D D_isSetoid (@FromOrderType A A_isSetoid WOSET) FromOrderType_isOrdinal) H_in) as [f f_cong f_inj]; simpl in *. exists f.
    + ii; eapply f_cong. now rewrite <- fromOrderType_eq_fromOrderType_iff in x_EQ.
    + ii; simpl in *.
      assert (HH : @fromOrderType A A_isSetoid WOSET x1 == @fromOrderType A A_isSetoid WOSET x2) by now eapply f_inj.
      now rewrite <- fromOrderType_eq_fromOrderType_iff.
  - intros [f f_cong f_inj].
    rewrite Hartogs_spec2; [simpl in * | eapply FromOrderType_isOrdinal]. exists f.
    + ii; eapply f_cong. now rewrite <- fromOrderType_eq_fromOrderType_iff.
    + ii. change (@fromOrderType A A_isSetoid WOSET x1 == @fromOrderType A A_isSetoid WOSET x2).
      rewrite -> fromOrderType_eq_fromOrderType_iff; eauto.
Qed.

End HARTOGS.

Definition hasCardinality (kappa : Cardinality.t) (c : Tree) : Prop :=
  let P (alpha : Tree) : Prop := exists R : kappa.(Cardinality.carrier) -> kappa.(Cardinality.carrier) -> Prop, exists R_wf : well_founded R, (forall x, forall x', x == x' \/ R x x' \/ R x' x) /\ Transitive R /\ eqPropCompatible2 R /\ fromWfSet R R_wf == alpha in
  P c /\ (forall alpha : Tree, P alpha -> c ≦ᵣ alpha).

Infix "`hasCardinality`" := hasCardinality.

Section CARDINALITY.

Lemma Cardinality_le_lt_lt (kappa : Cardinality.t) (kappa' : Cardinality.t) (kappa'' : Cardinality.t)
  (LE : kappa =< kappa')
  (LT : kappa' ≨ kappa'')
  : kappa ≨ kappa''.
Proof.
  destruct LT as [[f1 ? ?] NE]. econs.
  - transitivity kappa'; eauto. exists f1; eauto.
  - intros [f2 g2 ? ? ? ?]. destruct LE as [g1 ? ?]. contradiction NE.
    exists f1 (compose g1 g2); firstorder. 
Qed.

Lemma Cardinality_lt_le_lt (kappa : Cardinality.t) (kappa' : Cardinality.t) (kappa'' : Cardinality.t)
  (LT : kappa ≨ kappa')
  (LE : kappa' =< kappa'')
  : kappa ≨ kappa''.
Proof.
  destruct LT as [[f1 ? ?] NE]. econs.
  - transitivity kappa'; eauto. exists f1; eauto.
  - intros [f2 g2 ? ? ? ?]. destruct LE as [g1 ? ?]. contradiction NE.
    eexists f1 (compose g2 g1); firstorder. 
Qed.

#[local] Infix "\in" := member.

#[local] Infix "\subseteq" := isSubsetOf.

Section CARDINAL.

Theorem hasCardinality_intro `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t)
  : kappa `hasCardinality` Cardinality.toTree kappa.
Proof.
  hexploit (well_ordering_thm kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid)); eauto.
  intros (R0 & R0_wf & R0_total & R0_Transitive & R0_eqPropCompatible2).
  set (WPOSET := {| wltProp := R0; wltProp_Transitive := R0_Transitive; wltProp_well_founded := R0_wf; |}).
  set (WOSET := @O.WellfoundedToset_isWoset classic kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) WPOSET R0_eqPropCompatible2 R0_total).
  red. set (P := fun alpha : Tree => exists R : kappa.(Cardinality.carrier) -> kappa.(Cardinality.carrier) -> Prop, exists R_wf : well_founded R, (forall x, forall x', x == x' \/ R x x' \/ R x' x) /\ Transitive R /\ eqPropCompatible2 R /\ fromWfSet R R_wf == alpha).
  exploit (@O.minimisation_lemma classic _ _ rLt_isWellOrdering P).
  { exists (@FromOrderType _ _ WOSET). red. exists R0, R0_wf. splits; eauto. unfold FromOrderType. reflexivity. }
  intros (c & H_c & MIN); unnw. red in H_c. destruct H_c as (R & R_wf & R_total & R_Transitive & R_eqPropCompatible2 & H_c). split.
  - exists R, R_wf. splits; eauto. eapply extensionality. intros z; split; intros z_in.
    + unfold Cardinality.toTree. rewrite unions_spec. exists (fromWfSet R R_wf). split; eauto.
      rewrite filter_spec. simpl children. exists (B.exist R (conj R_wf (conj R_total (conj R_Transitive R_eqPropCompatible2)))). split.
      * intros WOSET'. simpl. rewrite fromWfSet_pirrel with (R_wf := proj1 _) (R_wf' := R_wf). rewrite InducedOrdinal.rLe_iff_rLt_or_rEq.
        rewrite -> H_c. eapply MIN. red. exists WOSET'.(Woset_isWellPoset).(wltProp), WOSET'.(Woset_isWellPoset).(wltProp_well_founded).
        split. { unshelve eapply O.wlt_trichotomous. exact classic. }
        split. { exact WOSET'.(Woset_isWellPoset).(wltProp_Transitive). }
        split. { exact WOSET'.(Woset_eqPropCompatible2). }
        reflexivity.
      * simpl childnodes. rewrite fromWfSet_pirrel with (R_wf := proj1 _) (R_wf' := R_wf). reflexivity.
    + unfold Cardinality.toTree in z_in. rewrite unions_spec in z_in. destruct z_in as (y & z_in & y_in).
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
      * rewrite -> H_c. rewrite InducedOrdinal.rLe_iff_rLt_or_rEq. eapply MIN. red. exists (B.proj1_sig i), (proj1 (B.proj2_sig i)).
        split. { exact (proj1 (proj2 (i.(B.proj2_sig)))). }
        split. { exact (proj1 (proj2 (proj2 i.(B.proj2_sig)))). }
        split. { exact (proj2 (proj2 (proj2 i.(B.proj2_sig)))). }
        reflexivity.
      * exact (H_i WOSET').
  - intros alpha (R1 & R1_wf & R1_total & R1_Transitive & R1_eqPropCompatible2 & H_alpha).
    rewrite <- H_alpha. unfold Cardinality.toTree. eapply unions_rLe_intro. intros x x_in.
    rewrite filter_spec in x_in. simpl children in x_in; simpl childnodes in x_in.
    destruct x_in as (i & H_i & H_x). rewrite H_x. clear x H_x.
    set (WPOSET' := {| wltProp := R1; wltProp_Transitive := R1_Transitive; wltProp_well_founded := R1_wf; |}).
    set (WOSET' := @O.WellfoundedToset_isWoset classic kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) WPOSET' R1_eqPropCompatible2 R1_total).
    exact (H_i WOSET').
Qed.

Lemma hasCardinality_isOrdinal kappa c
  (CARDINAL : kappa `hasCardinality` c)
  : isOrdinal c.
Proof.
  destruct CARDINAL as [(R & R_wf & R_total & R_Transitive & R_eqPropCompatible2 & H_c) MIN]. rewrite <- H_c.
  set (WPOSET' := {| wltProp := R; wltProp_Transitive := R_Transitive; wltProp_well_founded := R_wf; |}).
  set (WOSET' := @O.WellfoundedToset_isWoset classic kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) WPOSET' R_eqPropCompatible2 R_total).
  change (isOrdinal (@FromOrderType _ _ WOSET')). eapply FromOrderType_isOrdinal.
Qed.

Lemma hasCardinality_unique kappa c c'
  (CARDINAL : kappa `hasCardinality` c)
  (CARDINAL' : kappa `hasCardinality` c')
  : c == c'.
Proof.
  eapply Ordinal1.Ordinal_rEq_Ordinal_elim.
  - eapply hasCardinality_isOrdinal; eauto.
  - eapply hasCardinality_isOrdinal; eauto.
  - destruct CARDINAL as [R MIN]. destruct CARDINAL' as [R' MIN']. split.
    + eapply MIN; eauto.
    + eapply MIN'; eauto.
Qed.

Lemma hasCardinality_rewrite_r kappa (c : Tree) (c' : Tree)
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

Lemma Cardinality_le_total `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t) (kappa' : Cardinality.t)
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
  assert (R1_total : forall x, forall x', x == x' \/ binary_relation_on_image R f x x' \/ binary_relation_on_image R f x' x).
  { unfold binary_relation_on_image; intros x1 x2. pose proof (R_total (f x1) (f x2)) as [H_EQ | [H_LT | H_GT]]; eauto. }
  assert (R1_Transitive : Transitive (binary_relation_on_image R f)).
  { unfold binary_relation_on_image; ii; eauto. }
  assert (R1_eqPropCompatible2 : eqPropCompatible2 (binary_relation_on_image R f)).
  { unfold binary_relation_on_image; ii; eauto. }
  set (R1 := binary_relation_on_image R f) in *.
  set (R1_wf := relation_on_image_liftsWellFounded R f R_wf) in *.
  clearbody R1_wf. splits; eauto. transitivity (fromWfSet R1 R1_wf).
  - pose proof (hasCardinality_intro kappa) as [_ MIN']. eapply MIN'. exists R1, R1_wf. splits; eauto with *.
  - eapply fromWfSet_cong with (f := f); eauto with *.
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
      + intros WOSET'. simpl. rewrite fromWfSet_pirrel with (R_wf := proj1 _) (R_wf' := R1_wf). rewrite -> H_c. rewrite InducedOrdinal.rLe_iff_rLt_or_rEq.
        eapply MIN. exists WOSET'.(Woset_isWellPoset).(wltProp), WOSET'.(Woset_isWellPoset).(wltProp_well_founded).
        split. { unshelve eapply O.wlt_trichotomous. exact classic. }
        split. { exact WOSET'.(Woset_isWellPoset).(wltProp_Transitive). }
        split. { exact WOSET'.(Woset_eqPropCompatible2). }
        reflexivity.
      + simpl childnodes. now rewrite fromWfSet_pirrel with (R_wf := proj1 _) (R_wf' := R1_wf).
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
    assert (exists f : Cardinality.carrier kappa -> Cardinality.carrier kappa', forall x, fromWf R R_wf (f x) == fromWf R1 R1_wf x) as [h claim6].
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

#[global]
Add Parametric Morphism `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}
  : hasCardinality with signature (@eqProp Cardinality.t Cardinality.t_isSetoid ==> @eqProp Tree Tree_isSetoid ==> iff) as hasCardinality_eqPropCompatible.
Proof.
  intros kappa kappa' kappa_EQ c c' c_EQ. transitivity (kappa `hasCardinality` c').
  - split; now eapply hasCardinality_rewrite_r.
  - split; intros H.
    + pose proof (hasCardinality_intro kappa) as claim1.
      assert (claim2 : c' == Cardinality.toTree kappa).
      { eapply hasCardinality_unique; eauto. }
      assert (claim3 : Cardinality.toTree kappa == Cardinality.toTree kappa').
      { eapply Ordinal1.Ordinal_rEq_Ordinal_elim.
        - eapply hasCardinality_isOrdinal. eapply hasCardinality_intro.
        - eapply hasCardinality_isOrdinal. eapply hasCardinality_intro.
        - now rewrite <- Cardinality_eq_iff.
      }
      eapply hasCardinality_rewrite_r with (c := Cardinality.toTree kappa').
      { now rewrite -> claim2. }
      eapply hasCardinality_intro.
    + pose proof (hasCardinality_intro kappa') as claim1.
      assert (claim2 : c' == Cardinality.toTree kappa').
      { eapply hasCardinality_unique; eauto. }
      assert (claim3 : Cardinality.toTree kappa == Cardinality.toTree kappa').
      { eapply Ordinal1.Ordinal_rEq_Ordinal_elim.
        - eapply hasCardinality_isOrdinal. eapply hasCardinality_intro.
        - eapply hasCardinality_isOrdinal. eapply hasCardinality_intro.
        - now rewrite <- Cardinality_eq_iff.
      }
      eapply hasCardinality_rewrite_r with (c := Cardinality.toTree kappa).
      { now rewrite -> claim2. }
      eapply hasCardinality_intro.
Qed.

#[global]
Add Parametric Morphism `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}
  : Cardinality.toTree with signature (@eqProp Cardinality.t Cardinality.t_isSetoid ==> @eqProp Tree Tree_isSetoid) as toTree_eqPropCompatible.
Proof.
  intros kappa kappa' kappa_EQ. eapply Ordinal1.Ordinal_rEq_Ordinal_elim.
  - eapply hasCardinality_isOrdinal. eapply hasCardinality_intro.
  - eapply hasCardinality_isOrdinal. eapply hasCardinality_intro.
  - now rewrite <- Cardinality_eq_iff.
Qed.

#[local] Existing Instance Ord_isProset.

#[global]
Instance Cardinality_toTree_isMonotonic1 `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}
  : isMonotonic1 (A_isProset := Cardinality.t_isProset) (B_isProset := Ord_isProset) Cardinality.toTree.
Proof.
  intros kappa kappa' kappa_LE. do 2 red.
  now rewrite <- Cardinality_le_iff.
Qed.

Lemma Cardinality_supremum `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t) (c : Tree)
  (UPPER : forall kappa' : Cardinality.t, forall CLT : kappa' ≨ kappa, forall R : kappa'.(Cardinality.carrier) -> kappa'.(Cardinality.carrier) -> Prop, forall R_wf : well_founded R, forall R_total : forall x, forall x', x == x' \/ R x x' \/ R x' x, forall R_Transitive : Transitive R, forall R_eqPropCompatible2 : eqPropCompatible2 R, fromWfSet R R_wf <ᵣ c)
  : Cardinality.toTree kappa ≦ᵣ c.
Proof.
  unfold Cardinality.toTree. eapply rLe_intro_var1. intros x x_in.
  rewrite unions_spec in x_in. destruct x_in as (y & [z x_eq] & y_in).
  rewrite x_eq; clear x x_eq. rewrite filter_spec in y_in. destruct y_in as [x [H_x y_eq]]; simpl in *.
  unred_eqTree. destruct y as [csy tsy]. simpl in z. simpl in y_eq. pose proof (proj1 y_eq z) as [w H_w].
  unred_eqTree. simpl. rewrite H_w. rewrite fromWfSet_InitialSegment with (R_Transitive := proj1 (proj2 (proj2 (B.proj2_sig x)))).
  set (kappa' := {| Cardinality.carrier := { y : Cardinality.carrier kappa | B.proj1_sig x y w }; Cardinality.carrier_isSetoid := @subSetoid (Cardinality.carrier kappa) (Cardinality.carrier_isSetoid kappa) (fun y => B.proj1_sig x y w); |}).
  assert (claim1 : forall a : Cardinality.carrier kappa', forall b : Cardinality.carrier kappa', a == b \/ binary_relation_on_image (B.proj1_sig x) (@proj1_sig _ _) a b \/ binary_relation_on_image (B.proj1_sig x) (@proj1_sig _ _) b a) by now intros [x1 H_x1] [x2 H_x2]; exact (proj1 (proj2 x.(B.proj2_sig)) x1 x2).
  assert (claim2 : Transitive (binary_relation_on_image (B.proj1_sig x) (@proj1_sig _ (fun y : Cardinality.carrier kappa => B.proj1_sig x y w)))) by now intros [x1 H_x1] [x2 H_x2] [x3 H_x3]; exact (proj1 (proj2 (proj2 x.(B.proj2_sig))) x1 x2 x3).
  assert (claim3 : eqPropCompatible2 (binary_relation_on_image (B.proj1_sig x) (@proj1_sig _ (fun y : Cardinality.carrier kappa => B.proj1_sig x y w)))) by now intros [x1 H_x1] [x2 H_x2] [y1 H_y1] [y2 H_y2]; exact (proj2 (proj2 (proj2 x.(B.proj2_sig))) x1 x2 y1 y2).
  eapply UPPER with (kappa' := kappa'); eauto.
  rewrite Cardinality_lt_iff. eapply rLe_rLt_rLt.
  eapply Cardinality_lowerbound with (R := binary_relation_on_image x.(B.proj1_sig) (@proj1_sig _ _)) (R_wf := (relation_on_image_liftsWellFounded x.(B.proj1_sig) (@proj1_sig _ _) (proj1 x.(B.proj2_sig)))); eauto.
  pose proof (fromWfSet_InitialSegment kappa.(Cardinality.carrier) x.(B.proj1_sig) w (proj1 x.(B.proj2_sig)) (proj1 (proj2 (proj2 x.(B.proj2_sig))))) as claim5.
  eapply rLe_rLt_rLt with (y := fromWf x.(B.proj1_sig) (proj1 x.(B.proj2_sig)) w).
  { rewrite -> claim5. reflexivity. }
  eapply rLt_rLe_rLt with (y := fromWfSet x.(B.proj1_sig) (proj1 x.(B.proj2_sig))).
  { eapply member_implies_rLt. exists w. reflexivity. }
  pose proof (hasCardinality_intro kappa) as [R2 MIN2]. destruct R2 as (R2 & R2_wf & R2_total & R2_Transitive & R2_eqPropCompatible2 & H_R2).
  set (WPOSET2 := {| wltProp := R2; wltProp_Transitive := R2_Transitive; wltProp_well_founded := R2_wf; |}).
  set (WOSET2 := @O.WellfoundedToset_isWoset classic kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) WPOSET2 R2_eqPropCompatible2 R2_total).
  rewrite <- H_R2. change (fromWfSet (B.proj1_sig x) (proj1 (B.proj2_sig x)) ≦ᵣ fromWfSet WOSET2.(Woset_isWellPoset).(wltProp) WOSET2.(Woset_isWellPoset).(wltProp_well_founded)). exact (H_x WOSET2).
Qed.

Lemma Cardinality_toTree_eq_intro `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} kappa c
  (CARDINAL : kappa `hasCardinality` c)
  : Cardinality.toTree kappa == c.
Proof.
  eapply hasCardinality_unique.
  - eapply hasCardinality_intro.
  - exact CARDINAL.
Qed.

Corollary Cardinality_toTree_eq_iff `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} kappa c
  : Cardinality.toTree kappa == c <-> kappa `hasCardinality` c.
Proof.
  split.
  - intros EQ. rewrite <- EQ. eapply hasCardinality_intro.
  - eapply Cardinality_toTree_eq_intro.
Qed.

Lemma toSet_Card_le `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} kappa (alpha : Tree)
  (CARDINAL : kappa `hasCardinality` alpha)
  : Cardinality.mk (toSet alpha) (toSet_isSetoid alpha) =< kappa.
Proof.
  destruct alpha as [cs ts]. cbv [toSet]. simpl toWellPoset at 1.
  pose proof (Cardinality_toTree_eq_intro kappa (mkNode cs ts) CARDINAL) as HH.
  rewrite <- Ordinal1.FromOrderType_toSet_id with (alpha := mkNode cs ts) in HH by now eapply hasCardinality_isOrdinal; exact CARDINAL.
  rewrite -> Cardinality_le_iff. rewrite HH. clear HH kappa CARDINAL. set (kappa := {| Cardinality.carrier := _ |}).
  pose proof (hasCardinality_intro kappa) as [R MIN]. eapply MIN.
  exists (toSet_isWoset (mkNode cs ts)).(Woset_isWellPoset).(wltProp). exists (toSet_isWoset (mkNode cs ts)).(Woset_isWellPoset).(wltProp_well_founded). splits.
  - intros x x'. eapply @O.wlt_trichotomous with (SETOID := toSet_isSetoid (mkNode cs ts)) (WOSET := toSet_isWoset (mkNode cs ts)). exact classic.
  - intros x x' x''. exact ((toSet_isWoset (mkNode cs ts)).(Woset_isWellPoset).(wltProp_Transitive) x x' x'').
  - intros x x' y y'. exact ((toSet_isWoset (mkNode cs ts)).(Woset_eqPropCompatible2) x x' y y').
  - reflexivity.
Qed.

Definition isCardinal (alpha : Tree) : Prop :=
  exists kappa : Cardinality.t, kappa `hasCardinality` alpha.

Lemma isCardinal_isOrdinal (alpha : Tree)
  (CARDINAL : isCardinal alpha)
  : isOrdinal alpha.
Proof.
  destruct CARDINAL as [kappa CARDINAL]. eapply hasCardinality_isOrdinal; eauto.
Qed.

Lemma isCardinal_elim `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (alpha : Tree)
  (CARDINAL : isCardinal alpha)
  : card alpha `hasCardinality` alpha.
Proof.
  unfold card. destruct CARDINAL as [kappa CARDINAL]. pose proof (hasCardinality_isOrdinal kappa alpha CARDINAL) as ORDINAL.
  pose proof (COPY := CARDINAL). destruct CARDINAL as [(R & R_wf & R_total & R_Transitive & R_eqPropCompatible2 & H_alpha) MIN].
  set (WOSET := @O.WellfoundedToset_isWoset classic kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) {| wltProp := R; wltProp_well_founded := R_wf; wltProp_Transitive := R_Transitive |} R_eqPropCompatible2 R_total).
  change (@FromOrderType kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) WOSET == alpha) in H_alpha.
  assert (H_le1 : Cardinality.mk (children alpha) (children_isSetoid alpha) =< kappa).
  { rewrite <- Hartogs_spec2; eauto. rewrite <- H_alpha; eauto. rewrite Hartogs_ordertype_iff. reflexivity. }
  assert (H_le2 : kappa =< Cardinality.mk (children alpha) (children_isSetoid alpha)).
  { rewrite <- Hartogs_ordertype_iff. rewrite -> H_alpha. rewrite Hartogs_spec2; eauto. reflexivity. }
  assert (H_eq : Cardinality.mk (children alpha) (children_isSetoid alpha) == kappa).
  { destruct H_le1 as [f f_cong f_inj], H_le2 as [g g_cong g_inj]; exists f g; eauto. }
  now rewrite H_eq.
Qed.

Lemma card_children_lt_card_of_rLt `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}
  (alpha : Tree) (beta : Tree)
  (ALPHA : isOrdinal alpha)
  (BETA : isCardinal beta)
  (LT : alpha <ᵣ beta)
  : card alpha ≨ card beta.
Proof.
  rewrite Cardinality_lt_iff.
  pose proof (Cardinality_toTree_eq_intro (card beta) beta (isCardinal_elim beta BETA)) as BETA_EQ.
  rewrite BETA_EQ.
  eapply rLe_rLt_rLt; [pose (WOSET := children_isWoset alpha ALPHA) | exact LT].
  transitivity (@FromOrderType (children alpha) (children_isSetoid alpha) WOSET).
  - change (Cardinality.toTree (card alpha) ≦ᵣ @fromWfSet (children alpha) (isElemOf alpha) (WOSET.(Woset_isWellPoset).(wltProp_well_founded))).
    eapply Cardinality_lowerbound.
    + eapply @O.wlt_trichotomous with (SETOID := children_isSetoid alpha) (WOSET := WOSET). exact classic.
    + exact (WOSET.(Woset_isWellPoset).(wltProp_Transitive)).
    + exact (WOSET.(Woset_eqPropCompatible2)).
  - eapply rLe_eqTree_rLe.
    + reflexivity.
    + eapply FromOrderType_children_id.
Qed.

Lemma indexed_union_ofCardinals_hasCardinality `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (I : Type@{Set_u}) (alphas : I -> Tree)
  (HCARD : forall i, isCardinal (alphas i))
  : card (indexed_union I alphas) `hasCardinality` indexed_union I alphas.
Proof.
  unfold card.
  set (u := indexed_union I alphas).
  assert (Hord : forall i, isOrdinal (alphas i)).
  { intro i. eapply isCardinal_isOrdinal. exact (HCARD i). }
  assert (Hord_u : isOrdinal u).
  { unfold u. eapply sup_isOrdinal. exact Hord. }
  split.
  - exists (isElemOf u). exists ((children_isWoset u Hord_u).(Woset_isWellPoset).(wltProp_well_founded)). splits.
    + eapply @O.wlt_trichotomous with (SETOID := children_isSetoid u) (WOSET := children_isWoset u Hord_u). exact classic.
    + exact ((children_isWoset u Hord_u).(Woset_isWellPoset).(wltProp_Transitive)).
    + exact ((children_isWoset u Hord_u).(Woset_eqPropCompatible2)).
    + exact (FromOrderType_children_id u Hord_u).
  - intros beta (R & R_wf & R_total & R_Transitive & R_eqPropCompatible2 & H_beta).
    set (WOSET := @O.WellfoundedToset_isWoset classic (children u) (children_isSetoid u) {| wltProp := R; wltProp_well_founded := R_wf; wltProp_Transitive := R_Transitive |} R_eqPropCompatible2 R_total).
    change (@FromOrderType (children u) (children_isSetoid u) WOSET == beta) in H_beta.
    rewrite <- H_beta. unfold u. rewrite indexed_union_rLe_iff. intros i.
    pose proof (isCardinal_elim (alphas i) (HCARD i)) as [_ MIN_i].
    set (A := children (alphas i)).
    set (A_isSetoid := children_isSetoid (alphas i)).
    set (h := fun x : A => @existT I (fun j => children (alphas j)) i x).
    set (Ri := binary_relation_on_image R h).
    assert (h_cong : @eqPropCompatible1 A (children u) A_isSetoid (children_isSetoid u) h) by now ii; eauto.
    assert (Ri_wf : well_founded Ri) by exact (relation_on_image_liftsWellFounded R h R_wf).
    assert (Ri_total : forall x : A, forall y : A, x == y \/ Ri x y \/ Ri y x).
    { intros x y. unfold Ri, binary_relation_on_image. pose proof (R_total (h x) (h y)) as [Heq | [Hlt | Hgt]]; eauto. }
    assert (Ri_Transitive : Transitive Ri).
    { ii; eapply R_Transitive; eauto. }
    assert (Ri_eqPropCompatible2 : eqPropCompatible2 Ri).
    { ii; eapply R_eqPropCompatible2; eauto. }
    set (WOSET_i := @O.WellfoundedToset_isWoset classic A A_isSetoid {| wltProp := Ri; wltProp_well_founded := Ri_wf; wltProp_Transitive := Ri_Transitive |} Ri_eqPropCompatible2 Ri_total).
    assert (H_left : alphas i ≦ᵣ @FromOrderType A A_isSetoid WOSET_i).
    { eapply MIN_i. exists Ri, Ri_wf; splits; eauto. reflexivity. }
    assert (H_right : @FromOrderType A A_isSetoid WOSET_i ≦ᵣ @FromOrderType (children u) (children_isSetoid u) WOSET).
    { eapply fromWfSet_cong with (f := h); eauto. }
    eapply rLe_trans; [exact H_left | exact H_right].
Qed.

Lemma indexed_union_ofCardinals_isCardinal `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (I : Type@{Set_u}) (alphas : I -> Tree)
  (HCARD : forall i, isCardinal (alphas i))
  : isCardinal (indexed_union I alphas).
Proof.
  exists (Cardinality.mk (children (indexed_union I alphas)) (children_isSetoid (indexed_union I alphas))).
  eapply indexed_union_ofCardinals_hasCardinality; eauto.
Qed.

Lemma indexed_union_ofCardinals_isSupremum `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (I : Type@{Set_u}) (alphas : I -> Tree) (beta : Tree)
  (HCARD : forall i, isCardinal (alphas i))
  (HCARD_beta : isCardinal beta)
  : indexed_union I alphas ≦ᵣ beta <-> (forall i : I, alphas i ≦ᵣ beta).
Proof.
  rewrite indexed_union_rLe_iff; eauto using isCardinal_isOrdinal.
Qed.

Lemma Cardinality_toTree_isCardinal `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}
  (kappa : Cardinality.t)
  : isCardinal (Cardinality.toTree kappa).
Proof.
  exists kappa. eapply hasCardinality_intro.
Qed.

Definition Cardinality_sup (I : Type@{Set_u}) (ks : I -> Cardinality.t) : Cardinality.t :=
  card (indexed_union I (fun i => Cardinality.toTree (ks i))).

Lemma Cardinality_sup_hasCardinality `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (I : Type@{Set_u}) (ks : I -> Cardinality.t)
  : Cardinality_sup I ks `hasCardinality` indexed_union I (fun i => Cardinality.toTree (ks i)).
Proof.
  eapply indexed_union_ofCardinals_hasCardinality.
  intros i. exact (Cardinality_toTree_isCardinal (ks i)).
Qed.

Lemma Cardinality_sup_toTree_eq `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (I : Type@{Set_u}) (ks : I -> Cardinality.t)
  : Cardinality.toTree (Cardinality_sup I ks) == indexed_union I (fun i => Cardinality.toTree (ks i)).
Proof.
  eapply Cardinality_toTree_eq_intro. eapply Cardinality_sup_hasCardinality.
Qed.

#[local] Hint Resolve Cardinality_toTree_isCardinal : core.

Theorem Cardinality_sup_spec `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (I : Type@{Set_u}) (ks : I -> Cardinality.t) (lambda : Cardinality.t)
  : Cardinality_sup I ks =< lambda <-> (forall i, ks i =< lambda).
Proof.
  rewrite Cardinality_le_iff. rewrite Cardinality_sup_toTree_eq. rewrite indexed_union_ofCardinals_isSupremum with (I := I) (alphas := fun i => Cardinality.toTree (ks i)) (beta := Cardinality.toTree lambda); auto. split.
  - intros H i. rewrite -> Cardinality_le_iff. exact (H i).
  - intros H i. rewrite <- Cardinality_le_iff. exact (H i).
Qed.

Corollary Cardinality_sup_upperbound `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (I : Type@{Set_u}) (ks : I -> Cardinality.t) (i : I)
  : ks i =< Cardinality_sup I ks.
Proof.
  rewrite Cardinality_le_iff. rewrite Cardinality_sup_toTree_eq. eapply rLe_indexed_union_intro. exists i. reflexivity.
Qed.

Corollary Cardinality_sup_least `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (I : Type@{Set_u}) (ks : I -> Cardinality.t) (lambda : Cardinality.t)
  (H_upper : forall i, ks i =< lambda)
  : Cardinality_sup I ks =< lambda.
Proof.
  rewrite Cardinality_sup_spec. exact H_upper.
Qed.

Section CARDINAL_ARITHMETIC.

Lemma Cardinality_subtype_le (kappa : Cardinality.t) (P : kappa.(Cardinality.carrier) -> Prop)
  : Cardinality.mk { x : kappa.(Cardinality.carrier) | P x } (@subSetoid kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) P) =< kappa.
Proof.
  exists (@proj1_sig kappa.(Cardinality.carrier) P).
  - intros [x Hx] [y Hy] EQ. exact EQ.
  - intros [x Hx] [y Hy] EQ. simpl in EQ. exact EQ.
Qed.

Lemma Cardinality_ofType_subtype_le (A : Type@{Set_u}) (P : A -> Prop)
  : Cardinality.mk { x : A | P x } (@subSetoid A (@mkSetoid_from_eq A) P) =< Cardinality.ofType A.
Proof.
  change (Cardinality.mk { x : (Cardinality.ofType A).(Cardinality.carrier) | P x } (@subSetoid (Cardinality.ofType A).(Cardinality.carrier) (Cardinality.ofType A).(Cardinality.carrier_isSetoid) P) =< Cardinality.ofType A).
  eapply Cardinality_subtype_le.
Qed.

Lemma Cardinality_add_l (kappa : Cardinality.t) (lambda : Cardinality.t)
  : kappa =< Cardinality.add kappa lambda.
Proof.
  exists (@inl kappa.(Cardinality.carrier) lambda.(Cardinality.carrier)).
  - intros x y H. econs. exact H.
  - intros x y H. inv H. exact x_corres.
Qed.

Lemma Cardinality_add_r (kappa : Cardinality.t) (lambda : Cardinality.t)
  : lambda =< Cardinality.add kappa lambda.
Proof.
  exists (@inr kappa.(Cardinality.carrier) lambda.(Cardinality.carrier)).
  - intros x y H. econs. exact H.
  - intros x y H. inv H. exact y_corres.
Qed.

Lemma Cardinality_add_le (kappa : Cardinality.t) (lambda : Cardinality.t) (mu : Cardinality.t)
  (LE0 : kappa =< mu)
  (LE1 : lambda =< mu)
  : Cardinality.add kappa lambda =< Cardinality.mul (Cardinality.ofType bool) mu.
Proof.
  destruct LE0 as [f f_cong f_inj]. destruct LE1 as [g g_cong g_inj].
  exists (fun x : (Cardinality.add kappa lambda).(Cardinality.carrier) => match x with inl x => (true, f x) | inr y => (false, g y) end).
  - intros [x | x] [y | y] H; inv H; simpl in *.
    + split; [reflexivity | now eapply f_cong].
    + split; [reflexivity | now eapply g_cong].
  - intros [x | x] [y | y] H; simpl in *.
    + econs. eapply f_inj. exact (proj2 H).
    + destruct H as [H _]. discriminate H.
    + destruct H as [H _]. discriminate H.
    + econs. eapply g_inj. exact (proj2 H).
Qed.

Lemma Cardinality_mul_l (kappa : Cardinality.t) (lambda : Cardinality.t)
  (INHABITED : inhabited lambda.(Cardinality.carrier))
  : kappa =< Cardinality.mul kappa lambda.
Proof.
  destruct INHABITED as [y0].
  exists (fun x : kappa.(Cardinality.carrier) => (x, y0)).
  - intros x y H. split; [exact H | reflexivity].
  - intros x y H. exact (proj1 H).
Qed.

Lemma Cardinality_mul_r (kappa : Cardinality.t) (lambda : Cardinality.t)
  (INHABITED : inhabited kappa.(Cardinality.carrier))
  : lambda =< Cardinality.mul kappa lambda.
Proof.
  destruct INHABITED as [x0].
  exists (fun y : lambda.(Cardinality.carrier) => (x0, y)).
  - intros x y H. split; [reflexivity | exact H].
  - intros x y H. exact (proj2 H).
Qed.

Lemma Cardinality_mul_le (kappa : Cardinality.t) (lambda : Cardinality.t) (mu : Cardinality.t) (nu : Cardinality.t)
  (LE0 : kappa =< mu)
  (LE1 : lambda =< nu)
  : Cardinality.mul kappa lambda =< Cardinality.mul mu nu.
Proof.
  destruct LE0 as [f f_cong f_inj]. destruct LE1 as [g g_cong g_inj].
  exists (fun xy : (Cardinality.mul kappa lambda).(Cardinality.carrier) => (f (Datatypes.fst xy), g (Datatypes.snd xy))).
  - intros [x0 y0] [x1 y1] H. split; [now eapply f_cong; exact (proj1 H) | now eapply g_cong; exact (proj2 H)].
  - intros [x0 y0] [x1 y1] H. split; [now eapply f_inj; exact (proj1 H) | now eapply g_inj; exact (proj2 H)].
Qed.

End CARDINAL_ARITHMETIC.

Section NEXT.

Corollary Hartogs_ordertype_lowerbound `{Axms : ClassicalAxioms (b_AC := true)} (D : Type@{Set_u}) (D_isSetoid : isSetoid D) (A : Type@{Set_u}) (A_isSetoid : isSetoid A) (WOSET : @isWoset A A_isSetoid)
  (H_nLe : ~ Cardinality.mk A A_isSetoid =< Cardinality.mk D D_isSetoid)
  : Hartogs D ≦ᵣ @FromOrderType A A_isSetoid WOSET.
Proof.
  eapply NNPP; intro H_contra.
  contradiction H_nLe. rewrite <- Hartogs_ordertype_iff.
  eapply Ordinal1.Ordinal_rLt_Ordinal_elim.
  - eapply FromOrderType_isOrdinal.
  - eapply Hartogs_isOrdinal.
  - now rewrite -> InducedOrdinal.rLt_iff_not_rGe.
Qed.

Theorem Hartogs_hasCardinality `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (D : Type@{Set_u}) (D_isSetoid : isSetoid D)
  : card (Hartogs D) `hasCardinality` Hartogs D.
Proof.
  unfold card. split.
  - exists (isElemOf (Hartogs D)). exists ((children_isWoset (Hartogs D) Hartogs_isOrdinal).(Woset_isWellPoset).(wltProp_well_founded)). splits.
    + eapply @O.wlt_trichotomous with (SETOID := children_isSetoid (Hartogs D)) (WOSET := children_isWoset (Hartogs D) Hartogs_isOrdinal). exact classic.
    + exact ((children_isWoset (Hartogs D) Hartogs_isOrdinal).(Woset_isWellPoset).(wltProp_Transitive)).
    + exact ((children_isWoset (Hartogs D) Hartogs_isOrdinal).(Woset_eqPropCompatible2)).
    + exact (FromOrderType_children_id (Hartogs D) Hartogs_isOrdinal).
  - intros alpha (R & R_wf & R_total & R_Transitive & R_eqPropCompatible2 & H_alpha).
    set (WOSET := @O.WellfoundedToset_isWoset classic (children (Hartogs D)) (children_isSetoid (Hartogs D)) {| wltProp := R; wltProp_well_founded := R_wf; wltProp_Transitive := R_Transitive; |} R_eqPropCompatible2 R_total).
    change (@FromOrderType (children (Hartogs D)) (children_isSetoid (Hartogs D)) WOSET == alpha) in H_alpha.
    rewrite <- H_alpha. eapply Hartogs_ordertype_lowerbound with (A := children (Hartogs D)) (A_isSetoid := children_isSetoid (Hartogs D)) (WOSET := WOSET). exact (Hartogs_not_embed D D_isSetoid).
Qed.

Definition next (kappa : Cardinality.t) : Cardinality.t :=
  card (Hartogs kappa.(Cardinality.carrier)).

Corollary next_hasCardinality `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t)
  : next kappa `hasCardinality` @Hartogs kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid).
Proof.
  eapply Hartogs_hasCardinality.
Qed.

Corollary next_toTree_eq `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t)
  : Cardinality.toTree (next kappa) == @Hartogs kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid).
Proof.
  eapply Cardinality_toTree_eq_intro. exact (next_hasCardinality kappa).
Qed.

Corollary next_not_le `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t)
  : ~ next kappa =< kappa.
Proof.
  exact (Hartogs_not_embed kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid)).
Qed.

Theorem next_gt `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t)
  : kappa ≨ next kappa.
Proof.
  pose proof (hasCardinality_intro kappa) as H_card.
  pose proof (hasCardinality_isOrdinal kappa (Cardinality.toTree kappa) H_card) as H_ord.
  rewrite Cardinality_lt_iff. rewrite next_toTree_eq.
  eapply member_implies_rLt. rewrite Hartogs_spec1; eauto.
  exact (toSet_Card_le kappa (Cardinality.toTree kappa) H_card).
Qed.

Theorem next_le_iff_lt `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t) (lambda : Cardinality.t)
  : next kappa =< lambda <-> kappa ≨ lambda.
Proof.
  split.
  - intros H_le; eapply Cardinality_lt_le_lt; [exact (next_gt kappa) | exact H_le].
  - intros [H_le H_ne].
    pose proof (hasCardinality_intro lambda) as [(R & R_wf & R_total & R_Transitive & R_eqPropCompatible2 & H_lambda) MIN].
    set (WOSET := @O.WellfoundedToset_isWoset classic lambda.(Cardinality.carrier) lambda.(Cardinality.carrier_isSetoid) {| wltProp := R; wltProp_well_founded := R_wf; wltProp_Transitive := R_Transitive; |} R_eqPropCompatible2 R_total).
    assert (H_nLe : ~ Cardinality.mk lambda.(Cardinality.carrier) lambda.(Cardinality.carrier_isSetoid) =< Cardinality.mk kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid)).
    { intro H_ge. contradiction H_ne. destruct H_le as [f f_cong f_inj], H_ge as [g g_cong g_inj]. exists f g; eauto. }
    rewrite Cardinality_le_iff. rewrite next_toTree_eq.
    change (@FromOrderType lambda.(Cardinality.carrier) lambda.(Cardinality.carrier_isSetoid) WOSET == Cardinality.toTree lambda) in H_lambda.
    rewrite <- H_lambda. now eapply Hartogs_ordertype_lowerbound with (A := lambda.(Cardinality.carrier)) (A_isSetoid := lambda.(Cardinality.carrier_isSetoid)) (WOSET := WOSET).
Qed.

Corollary FromOrderType_lt_next `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t) (A : Type@{Set_u}) (A_isSetoid : isSetoid A) (WOSET : @isWoset A A_isSetoid)
  (H_le : Cardinality.mk A A_isSetoid =< kappa)
  : @FromOrderType A A_isSetoid WOSET <ᵣ Cardinality.toTree (next kappa).
Proof.
  rewrite next_toTree_eq. eapply member_implies_rLt. now rewrite -> Hartogs_ordertype_iff.
Qed.

Corollary next_supremum `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t) (c : Tree)
  (UPPER : forall A : Type@{Set_u}, forall A_isSetoid : isSetoid A, forall WOSET : @isWoset A A_isSetoid, Cardinality.mk A A_isSetoid =< kappa -> @FromOrderType A A_isSetoid WOSET <ᵣ c)
  : Cardinality.toTree (next kappa) ≦ᵣ c.
Proof.
  rewrite next_toTree_eq. eapply rLe_intro_var1.
  intros x [(P & R & R_wf & R_total & R_Transitive & R_eqPropCompatible2) x_eq].
  set (A := @sig kappa.(Cardinality.carrier) P).
  set (A_isSetoid := @subSetoid kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) P).
  set (WOSET := @O.WellfoundedToset_isWoset classic A A_isSetoid {| wltProp := R; wltProp_well_founded := R_wf; wltProp_Transitive := R_Transitive |} R_eqPropCompatible2 R_total).
  rewrite x_eq. simpl. erewrite fromWfSet_pirrel. eapply UPPER with (A := A) (A_isSetoid := A_isSetoid) (WOSET := WOSET).
  exists (@proj1_sig (Cardinality.carrier kappa) P); firstorder.
Qed.

#[global]
Instance next_isMonotonic1 `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}
  : isMonotonic1 next.
Proof.
  intros kappa lambda H_le. rewrite next_le_iff_lt. eapply Cardinality_le_lt_lt; eauto using next_gt.
Qed.

#[global]
Instance next_eqPropCompatible1 `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}
  : eqPropCompatible1 next.
Proof.
  intros kappa lambda H_eq. enough (next kappa =< next lambda /\ next lambda =< next kappa) as [[f f_cong f_inj] [g g_cong g_inj]] by now exists f g.
  destruct H_eq; split; eapply next_isMonotonic1; [exists f | exists g]; eauto.
Qed.

End NEXT.

#[local] Existing Instance children_isSetoid.

#[local] Existing Instance children_isWoset.

Theorem Woset_iso_Ord `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (A : Type@{Set_u}) (SETOID : isSetoid A) (WOSET : isWoset A) (alpha : Tree)
  (ORDINAL : isOrdinal alpha)
  : @FromOrderType A SETOID WOSET == alpha <-> (exists f : A -> children alpha, ⟪ f_inj : forall x1 : A, forall x2 : A, x1 == x2 <-> f x1 == f x2 ⟫ /\ ⟪ f_preserves : forall x1 : A, forall x2 : A, x1 ≺ x2 <-> isElemOf alpha (f x1) (f x2) ⟫ /\ ⟪ f_surj : forall y, exists x, y == f x ⟫).
Proof.
  pose (B := children alpha). pose (BWOSET := children_isWoset alpha ORDINAL). split.
  - intros H_eq.
    assert (Hex : forall x : A, exists y : B, @fromOrderType A SETOID WOSET x == @fromOrderType B (children_isSetoid alpha) BWOSET y).
    { intros x.
      assert (Hx : @fromOrderType A SETOID WOSET x \in @FromOrderType A SETOID WOSET).
      { rewrite FromOrderType_spec. exists x. reflexivity. }
      rewrite H_eq in Hx.
      rewrite <- (FromOrderType_children_id alpha ORDINAL) in Hx.
      now rewrite FromOrderType_spec in Hx.
    }
    pose proof (Axiom_of_Choice A (fun _ => B) (fun x => fun y => @fromOrderType A SETOID WOSET x == @fromOrderType B (children_isSetoid alpha) BWOSET y) Hex) as [f Hf].
    exists f. splits.
    + intros x1 x2; split; [intros Hxx | intros Hff].
      * erewrite <- fromOrderType_eq_fromOrderType_iff. unfold B in Hf. do 2 rewrite <- Hf. now rewrite -> fromOrderType_eq_fromOrderType_iff.
      * erewrite <- fromOrderType_eq_fromOrderType_iff. do 2 rewrite -> Hf. now rewrite -> fromOrderType_eq_fromOrderType_iff.
    + intros x1 x2; split; [intros Hxx | intros Hff].
      * change (wlt (WOSET := children_isWoset alpha ORDINAL) (f x1) (f x2)).
        rewrite <- fromOrderType_in_fromOrderType_iff in Hxx. do 2 rewrite Hf in Hxx.
        now rewrite <- fromOrderType_in_fromOrderType_iff.
      * rewrite <- fromOrderType_in_fromOrderType_iff. do 2 rewrite Hf.
        change (wlt (WOSET := children_isWoset alpha ORDINAL) (f x1) (f x2)) in Hff.
        now rewrite <- fromOrderType_in_fromOrderType_iff in Hff.
    + intros y.
      assert (Hy : @fromOrderType B (children_isSetoid alpha) BWOSET y \in @FromOrderType B (children_isSetoid alpha) BWOSET).
      { rewrite FromOrderType_spec. exists y. reflexivity. }
      pose proof (FromOrderType_children_id alpha ORDINAL) as claim1. change (@FromOrderType B _ BWOSET == alpha) in claim1.
      rewrite claim1 in Hy. rewrite <- H_eq in Hy at 2. rewrite FromOrderType_spec in Hy.
      destruct Hy as [x Hy]. exists x. rewrite Hf in Hy. now rewrite <- fromOrderType_eq_fromOrderType_iff.
  - i; des.
    pose proof (Axiom_of_Choice B (fun _ => A) (fun y => fun x => y == f x) f_surj) as [g Hg].
    assert (H_le1 : @FromOrderType A SETOID WOSET ≦ᵣ @FromOrderType B (children_isSetoid alpha) BWOSET).
    { unfold FromOrderType. eapply fromWfSet_cong with (f := f).
      intros x1 x2 Hlt. change (isElemOf alpha (f x1) (f x2)). now rewrite <- f_preserves.
    }
    assert (H_le2 : @FromOrderType B (children_isSetoid alpha) BWOSET ≦ᵣ @FromOrderType A SETOID WOSET).
    { unfold FromOrderType. eapply fromWfSet_cong with (f := g). intros y1 y2 Hlt.
      assert (Hlt' : isElemOf alpha (f (g y1)) (f (g y2))).
      { pose proof (children_isWoset alpha ORDINAL).(Woset_eqPropCompatible2) as H_compat.
        eapply H_compat.
        - symmetry. exact (Hg y1).
        - symmetry. exact (Hg y2).
        - exact Hlt.
      }
      now rewrite <- f_preserves in Hlt'.
    }
    assert (H_eq' : @FromOrderType A SETOID WOSET == @FromOrderType B (children_isSetoid alpha) BWOSET).
    { eapply Ordinal1.Ordinal_rEq_Ordinal_elim.
      - apply FromOrderType_isOrdinal.
      - apply FromOrderType_isOrdinal.
      - split; assumption.
    }
    rewrite H_eq'. exact (FromOrderType_children_id alpha ORDINAL).
Qed.

Section COUNTABLE.

Let Nat_lt_Transitive
  : Transitive Nat.lt.
Proof.
  clear; red; lia.
Qed.

#[local]
Instance nat_isWellPoset : isWellPoset nat :=
  { wltProp := Nat.lt
  ; wltProp_well_founded := lt_wf
  ; wltProp_Transitive := Nat_lt_Transitive
  }.

#[local, program]
Instance nat_isWoset : isWoset nat (SETOID := @mkSetoid_from_eq nat) :=
  { Woset_isWellPoset := nat_isWellPoset }.
Next Obligation.
  ii; simpl in *. lia.
Qed.
Next Obligation.
  enough ((~ Nat.lt x y) /\ (~ Nat.lt y x))%nat by lia.
  split; [rewrite <- EXT_EQ | rewrite -> EXT_EQ]; lia.
Qed.

#[local]
Instance Fin_isWellPoset {n : nat} : isWellPoset (Fin.t n) :=
  { wltProp := Fin.Fin_lt
  ; wltProp_well_founded := Fin.Fin_lt_wf n
  ; wltProp_Transitive := Fin.Fin_lt_Transitive n
  }.

#[local]
Instance Fin_isWoset (n : nat) : isWoset (Fin.t n) (SETOID := @Fin.t_isSetoid n) :=
  @O.WellfoundedToset_isWoset classic (Fin.t n) (@Fin.t_isSetoid n) Fin_isWellPoset (Fin.Fin_lt_eqPropCompatible2 n) (@Fin.Fin_lt_total n).

Lemma fromWf_vs_Ord_of_nat (n : nat)
  : @fromWf nat Nat.lt lt_wf n == Ord_of_nat n.
Proof.
  assert (claim1 : forall m : nat, isOrdinal (fromWf Nat.lt lt_wf m)).
  { eapply fromWf_isOrdinal; eauto. }
  eapply Ordinal1.Ordinal_rEq_Ordinal_elim; auto.
  { eapply Ord_of_nat_isOrdinal. }
  induction n as [ | n IH]; simpl.
  - split.
    + econs. intros [c Hc]; simpl in Hc. red in Hc. exfalso; lia.
    + econs. simpl. intros [].
  - assert (IH' : fromWf Nat.lt lt_wf n == Ord_of_nat n).
    { eapply Ordinal1.Ordinal_rEq_Ordinal_elim; auto. eapply Ord_of_nat_isOrdinal. }
    split.
    + econs. intros [c Hc]; simpl in Hc.
      assert (c = n \/ c < n) as [EQ | LT] by lia.
      * econs. exists (@existT _ _ false true).
        subst n. simpl childnodes at 2. rewrite <- IH.
        econs. intros [n Hn]. simpl proj1_sig in *. simpl childnodes.
        rewrite fromAcc_pirrel with (ACC' := lt_wf n). eapply member_implies_rLt.
        eapply fromAcc_member_fromAcc_intro. exact Hn.
      * rewrite <- IH'. econs. exists (@existT _ _ true (@exist _ _ c LT)).
        econs. intros [m Hm]. simpl in Hm |- *.
        rewrite fromAcc_pirrel with (x := c) (ACC' := lt_wf c).
        rewrite fromAcc_pirrel with (x := m) (ACC' := lt_wf m).
         eapply member_implies_rLt. eapply fromAcc_member_fromAcc_intro. exact Hm.
    + rewrite <- IH'. econs. intros [b c]; simpl in b, c |- *. destruct b as [ | ].
      * eapply member_implies_rLt. pose proof (claim1 (S n)) as [? ?].
        eapply TRANS with (y := fromWf Nat.lt lt_wf n); eauto with *.
        unfold fromWf. rewrite fromAcc_unfold.
        assert (n < S n) as Hn by lia.
        exists (@exist _ _ n Hn). eapply fromAcc_pirrel.
      * assert (n < S n) as Hn by lia.
        simpl in c. destruct c; simpl; eapply member_implies_rLt; unfold fromWf; rewrite fromAcc_unfold; exists (@exist _ _ n Hn); eapply fromAcc_pirrel.
Qed.

Lemma fromWf_Fin_lt_vs_fromWf_nat (n : nat) (x : Fin.t n)
  : @fromWf (Fin.t n) (@Fin.Fin_lt n) (Fin.Fin_lt_wf n) x == @fromWf nat Nat.lt lt_wf (Fin.evalFin x).
Proof.
  eapply fromWf_eq_fromWf_intro with (f := @Fin.evalFin n).
  intros x' y; split.
  - intros [x0 [Hlt Hy]]. exists (Fin.evalFin x'). split.
    + rewrite Hy. exact Hlt.
    + reflexivity.
  - intros [y' [Hy Hy']]. subst y'.
    assert (Hy_n : y < n).
    { pose proof (proj2_sig (Fin.runFin x')) as Hx'. unfold Fin.evalFin in Hy. lia. }
    exists (Fin.getFin y Hy_n). split.
    + unfold Fin.Fin_lt, Fin.evalFin. rewrite Fin.runFin_getFin_id. simpl. exact Hy.
    + unfold Fin.evalFin. rewrite Fin.runFin_getFin_id. reflexivity.
Qed.

Lemma fromWfSet_Fin_lt_vs_Ord_of_nat (n : nat)
  : @fromWfSet (Fin.t n) (@Fin.Fin_lt n) (Fin.Fin_lt_wf n) == Ord_of_nat n.
Proof.
  transitivity (@fromWf nat Nat.lt lt_wf n).
  - eapply extensionality. intros z; split; intros Hz.
    + destruct Hz as [x Hz]. rewrite Hz. rewrite fromWf_unfold.
      exists (Fin.evalFin x). split.
      * exact (proj2_sig (Fin.runFin x)).
      * exact (fromWf_Fin_lt_vs_fromWf_nat n x).
    + rewrite fromWf_unfold in Hz. destruct Hz as [m [Hm_lt Hz]].
      replace m with (Fin.evalFin (Fin.getFin m Hm_lt)) in Hz by now unfold Fin.evalFin; rewrite Fin.runFin_getFin_id.
      rewrite Hz. exists (Fin.getFin m Hm_lt). simpl childnodes. symmetry. eapply fromWf_Fin_lt_vs_fromWf_nat.
  - exact (fromWf_vs_Ord_of_nat n).
Qed.

Lemma Fin_choose_top_aux (n : nat) (m : nat) (R : Fin.t (S n) -> Fin.t (S n) -> Prop)
  (Hm : m < S n)
  (R_total : forall x : Fin.t (S n), forall x' : Fin.t (S n), x == x' \/ R x x' \/ R x' x)
  (R_Transitive : Transitive R)
  : exists top : Fin.t (S n), Fin.evalFin top <= m /\ ⟪ TOP : forall x : Fin.t (S n), Fin.evalFin x <= m -> x == top \/ R x top ⟫.
Proof.
  revert n Hm R R_total R_Transitive. induction m as [ | m IH]; intros ? ? R ? ?.
  - exists (Fin.getFin 0 Hm). split.
    + unfold Fin.evalFin. rewrite Fin.runFin_getFin_id. reflexivity.
    + intros x Hx. left. rewrite -> Fin.Fin_eqProp_iff. eapply Fin.evalFin_inj.
      unfold Fin.evalFin in *. rewrite Fin.runFin_getFin_id. simpl. lia.
  - assert (Hm' : m < S n) by lia.
    pose proof (IH n Hm' R R_total R_Transitive) as [top [Htop_le Htop]].
    set (y := Fin.getFin (S m) Hm).
    assert (Hy_eval : Fin.evalFin y = S m).
    { unfold y, Fin.evalFin. rewrite Fin.runFin_getFin_id. reflexivity. }
    pose proof (R_total top y) as [H_eq | [H_top_y | H_y_top]].
    + exists top. split.
      { lia. }
      intros x Hx. pose proof (Nat.eq_dec (Fin.evalFin x) (S m)) as [Heq | Hneq].
      * left. transitivity y; auto with *.
        rewrite -> Fin.Fin_eqProp_iff. eapply Fin.evalFin_inj. now rewrite Hy_eval.
      * assert (Hx_small : Fin.evalFin x <= m) by lia.
        exact (Htop x Hx_small).
    + exists y. split.
      { lia. }
      intros x Hx.
      pose proof (Nat.eq_dec (Fin.evalFin x) (S m)) as [Heq | Hneq].
      * left. rewrite -> Fin.Fin_eqProp_iff. eapply Fin.evalFin_inj.
        rewrite Hy_eval. exact Heq.
      * assert (Hx_small : Fin.evalFin x <= m) by lia.
        destruct (Htop x Hx_small) as [Hx_eq_top | Hx_lt_top].
        { right. rewrite -> Fin.Fin_eqProp_iff in Hx_eq_top. subst x. exact H_top_y. }
        { right. transitivity top; eauto. }
    + exists top. split.
      { lia. }
      intros x Hx.
      pose proof (Nat.eq_dec (Fin.evalFin x) (S m)) as [Heq | Hneq].
      * assert (Hx_eq_y : x == y).
        { rewrite -> Fin.Fin_eqProp_iff. eapply Fin.evalFin_inj. rewrite Hy_eval. exact Heq. }
        right. rewrite -> Fin.Fin_eqProp_iff in Hx_eq_y. subst x. exact H_y_top.
      * assert (Hx_small : Fin.evalFin x <= m) by lia.
        exact (Htop x Hx_small).
Qed.

Lemma Fin_choose_top (n : nat) (R : Fin.t (S n) -> Fin.t (S n) -> Prop)
  (R_total : forall x : Fin.t (S n), forall x' : Fin.t (S n), x == x' \/ R x x' \/ R x' x)
  (R_Transitive : Transitive R)
  : exists top : Fin.t (S n), forall x, x == top \/ R x top.
Proof.
  exploit (Fin_choose_top_aux n n R); eauto.
  intros [top ?]; des. exists top. i. eapply TOP.
  pose proof (Fin.Fin_evalFin_lt x). lia.
Qed.

#[refine]
Fixpoint Fin_omit {n : nat} (z : Fin.t (S n)) {struct z} : Fin.t n -> Fin.t (S n):=
  match z with
  | @FZ n' => _
  | @FS n' z' => _
  end.
Proof.
  - intros i. exact (@FS n' i).
  - intros i. destruct i as [m | m i'].
    + exact (@FZ (S m)).
    + exact (@FS (S m) (@Fin_omit m z' i')).
Defined.

Lemma Fin_omit_omit {n : nat} (z : Fin.t (S n)) (i : Fin.t n)
  : ~ Fin_omit z i == z.
Proof.
  revert i. pattern n, z. revert n z. eapply Fin.rectS.
  - simpl; eauto.
  - simpl; intros n. Fin.caseS z; simpl; intros IH; Fin.caseS i; eauto.
Qed.

#[refine]
Fixpoint Fin_restore {n : nat} (z : Fin.t (S n)) {struct z} : { i : Fin.t (S n) | ~ i == z } -> Fin.t n :=
  match z with
  | @FZ n' => _
  | @FS n' z' => _
  end.
Proof.
  - intros [x Hx]. revert x Hx. Fin.caseS x'; ii.
    + exfalso. contradiction Hx. econs.
    + exact x'.
  - intros [x Hx]. revert x Hx. Fin.caseS x'; ii.
    + revert Hx. pattern z'. revert z'. destruct n' as [ | m].
      * Fin.case0.
      * ii. exact FZ.
    + revert Hx. pattern z'. revert z'. destruct n' as [ | m].
      * Fin.case0.
      * ii. eapply FS. eapply Fin_restore with (z := z'). exists x'. exact Hx.
Defined.

Lemma Fin_restore_omit {n : nat} (z : Fin.t (S n)) (i : Fin.t n)
  : Fin_restore z (@exist _ _ (Fin_omit z i) (Fin_omit_omit z i)) == i.
Proof.
  revert z. induction i as [n | n i IH]; Fin.caseS z.
  - simpl; eauto.
  - simpl; eauto.
  - simpl. reflexivity.
  - simpl. change (Fin_restore z (@exist _ (fun x : Fin.t (S n) => ~ Fin.t_eqProp (S n) x z) (Fin_omit z i) (Fin_omit_omit (FS z) (FS i))) == i).
    transitivity (Fin_restore z (@exist _ (fun i : Fin.t (S n) => ~ i == z) (Fin_omit z i) (Fin_omit_omit z i))); eauto.
    simpl. rewrite proof_irrelevance with (p1 := Fin_omit_omit (FS z) (FS i)) (p2 := Fin_omit_omit z i); eauto with *.
Qed.

Lemma Fin_omit_restore {n : nat} (z : Fin.t (S n)) (y : { x : Fin.t (S n) | ~ x == z })
  : Fin_omit z (Fin_restore z y) == proj1_sig y.
Proof.
  destruct y as [y Hy]. simpl proj1_sig. revert y Hy. pattern n, z. revert n z. refine (Fin.rectS _ _ _).
  - intros n; Fin.caseS y; simpl; ii; eauto with *.
  - intros n; Fin.caseS x; intros IH; ii; revert y Hy; Fin.caseS y; ii; simpl in *; eauto.
Qed.

Lemma Fin_omit_inj {n : nat} (z : Fin.t (S n)) (i1 : Fin.t n) (i2 : Fin.t n)
  (EQ : Fin_omit z i1 == Fin_omit z i2)
  : i1 == i2.
Proof.
  revert i1 i2 EQ. pattern n, z. revert n z. refine (Fin.rectS _ _ _).
  - intros n i1. destruct i1 as [ | i1']; Fin.caseS i2'; intros EQ; simpl in *; eauto.
  - intros n i IH. Fin.caseS i1'; Fin.caseS i2'; intros EQ; simpl in *; eauto.
Qed.

Lemma Fin_woset_unique (n : nat) (R : Fin.t n -> Fin.t n -> Prop)
  (R_wf : well_founded R)
  (R_total : forall x, forall x', x == x' \/ R x x' \/ R x' x)
  (R_Transitive : Transitive R)
  (R_eqPropCompatible2 : eqPropCompatible2 R)
  : @fromWfSet (Fin.t n) R R_wf == Ord_of_nat n.
Proof.
  revert R R_wf R_total R_Transitive R_eqPropCompatible2. induction n as [ | n IH]; intros R; ii.
  - eapply extensionality. intros z; split; intros Hz.
    + destruct Hz as [x _]. simpl in *. exact (Fin.case0 x).
    + now rewrite empty_spec in Hz.
  - pose proof (Fin_choose_top n R R_total R_Transitive) as [top Htop].
    assert (Hpred : forall x : Fin.t (S n), R x top <-> ~ x == top).
    { intros x; split.
      - intros Hlt Heq. refine (well_founded_implies_Irreflexive' R R_wf _ x top Heq Hlt).
        ii. now rewrite <- H.
      - intros Hneq. pose proof (Htop x) as [Heq | Hlt]; ss!.
    }
    set (A := { x : Fin.t (S n) | R x top }).
    set (A_isSetoid := @subSetoid (Fin.t (S n)) (@Fin.t_isSetoid (S n)) (fun x => R x top)).
    set (RA := binary_relation_on_image R (@proj1_sig _ (fun x : Fin.t (S n) => R x top))).
    set (RA_wf := relation_on_image_liftsWellFounded R (@proj1_sig _ (fun x : Fin.t (S n) => R x top)) R_wf).
    assert (RA_total : forall x : A, forall x' : A, x == x' \/ RA x x' \/ RA x' x).
    { intros [x Hx] [x' Hx']; simpl. exact (R_total x x'). }
    assert (RA_Transitive : Transitive RA).
    { unfold RA, binary_relation_on_image. intros [x Hx] [y Hy] [z Hz] H1 H2; simpl in *. eapply R_Transitive; eauto. }
    assert (RA_eqPropCompatible2 : eqPropCompatible2 RA).
    { intros [x1 H1] [x2 H2] [y1 H3] [y2 H4] Hx Hy; simpl in *. eapply R_eqPropCompatible2; simpl; eauto. }
    set (embed := fun i : Fin.t n => let y := Fin_omit top i in @exist _ (fun x : Fin.t (S n) => R x top) y (proj2 (Hpred y) (Fin_omit_omit top i))).
    set (forget := fun y : A => Fin_restore top (@exist _ _ (proj1_sig y) (proj1 (Hpred (proj1_sig y)) (proj2_sig y)))).
    set (Rn := binary_relation_on_image R (fun i : Fin.t n => proj1_sig (embed i))).
    set (Rn_wf := relation_on_image_liftsWellFounded R (fun i : Fin.t n => proj1_sig (embed i)) R_wf).
    assert (embed_cong : eqPropCompatible1 (fun i : Fin.t n => proj1_sig (embed i))).
    { intros i i' H. rewrite Fin.Fin_eqProp_iff in H |- *. congruence. }
    assert (Rn_total : forall x : Fin.t n, forall x' : Fin.t n, x == x' \/ Rn x x' \/ Rn x' x).
    { intros x x'. pose proof (R_total (proj1_sig (embed x)) (proj1_sig (embed x'))) as [Heq | [Hlt | Hgt]].
      - left. exact (Fin_omit_inj top x x' Heq).
      - now right; left.
      - now right; right.
    }
    assert (Rn_Transitive : Transitive Rn).
    { intros x y z H1 H2; simpl in *. eapply R_Transitive; eauto. }
    assert (Rn_eqPropCompatible2 : eqPropCompatible2 Rn).
    { intros x1 x2 y1 y2 Hx Hy. eapply R_eqPropCompatible2; eauto. }
    pose proof (IH Rn Rn_wf Rn_total Rn_Transitive Rn_eqPropCompatible2) as IHn.
    set (WPOSETA := {| wltProp := RA; wltProp_well_founded := RA_wf; wltProp_Transitive := RA_Transitive; |}).
    set (WPOSETn := {| wltProp := Rn; wltProp_well_founded := Rn_wf; wltProp_Transitive := Rn_Transitive; |}).
    set (WOSETA := @O.WellfoundedToset_isWoset classic A A_isSetoid WPOSETA RA_eqPropCompatible2 RA_total).
    set (WOSETn := @O.WellfoundedToset_isWoset classic (Fin.t n) (@Fin.t_isSetoid n) WPOSETn Rn_eqPropCompatible2 Rn_total).
    assert (Hseg_eq : @fromWfSet A RA RA_wf == @fromWfSet (Fin.t n) Rn Rn_wf).
    { eapply Ordinal1.Ordinal_rEq_Ordinal_elim.
      - change (isOrdinal (@FromOrderType A A_isSetoid WOSETA)). exact FromOrderType_isOrdinal.
      - change (isOrdinal (@FromOrderType (Fin.t n) (@Fin.t_isSetoid n) WOSETn)). exact FromOrderType_isOrdinal.
      - split.
        + eapply fromWfSet_cong with (f := forget).
          intros y1 y2 Hlt. unfold Rn. eapply R_eqPropCompatible2.
          * exact (Fin_omit_restore top (@exist _ _ (proj1_sig y1) ((proj1 (Hpred (proj1_sig y1))) (proj2_sig y1)))).
          * exact (Fin_omit_restore top (@exist _ _ (proj1_sig y2) ((proj1 (Hpred (proj1_sig y2))) (proj2_sig y2)))).
          * exact Hlt.
        + eapply fromWfSet_cong with (f := embed); eauto.
    }
    assert (Htop_eq : @fromWfSet (Fin.t (S n)) R R_wf == succ (@fromWf (Fin.t (S n)) R R_wf top)).
    { eapply extensionality. intros z; split; intros Hz.
      - destruct Hz as [x Hz]. rewrite Hz. rewrite succ_spec. pose proof (Htop x) as [Hx | Hlt].
        + right. rewrite Fin.Fin_eqProp_iff in Hx. now subst.
        + left. rewrite fromWf_spec. exists x; eauto with *.
      - rewrite succ_spec in Hz. destruct Hz as [Hz | Hz].
        + rewrite fromWf_spec in Hz. destruct Hz as [x [Hz Hlt]]. rewrite Hz. now exists x.
        + rewrite Hz. now exists top.
    }
    rewrite Htop_eq; simpl Ord_of_nat. eapply succ_eqPropCompatible1.
    rewrite fromWfSet_InitialSegment with (R_Transitive := R_Transitive).
    fold RA. fold RA_wf. transitivity (fromWfSet Rn Rn_wf); eauto.
Qed.

Theorem Fin_hasCardinality (n : nat)
  : Cardinality.mk (Fin.t n) (@Fin.t_isSetoid n) `hasCardinality` Ord_of_nat n.
Proof.
  split.
  - exists (@Fin.Fin_lt n), (Fin.Fin_lt_wf n). splits.
    + exact (@Fin.Fin_lt_total n).
    + exact (Fin.Fin_lt_Transitive n).
    + exact (Fin.Fin_lt_eqPropCompatible2 n).
    + exact (fromWfSet_Fin_lt_vs_Ord_of_nat n).
  - intros alpha (R & R_wf & R_total & R_Transitive & R_eqPropCompatible2 & Halpha).
    rewrite <- Halpha. erewrite Fin_woset_unique with (R := R) (R_wf := R_wf); eauto with *.
Qed.

Corollary Fin_hasCardinality_var1 (n : nat)
  : Cardinality.ofType (Fin.t n) `hasCardinality` Ord_of_nat n.
Proof.
  pose proof (Fin_hasCardinality n) as [HH1 HH2]; simpl Cardinality.carrier in *. split.
  - destruct HH1 as (R & R_wf & R_total & R_Transitive & R_eqPropCompatible2 & HH1).
    exists R, R_wf. splits; eauto.
    + ii. change (x == x') with (x = x'). simpl in x, x'. erewrite <- Fin.Fin_eqProp_iff with (i := x) (i' := x'). eauto.
    + ii. change (x1 = x2) in x_EQ. change (y1 = y2) in y_EQ. do 2 red. subst x2 y2. reflexivity.
  - intros alpha Halpha. destruct Halpha as (R & R_wf & R_total & R_Transitive & R_eqPropCompatible2 & Halpha).
    eapply HH2. exists R, R_wf. splits; eauto.
    + ii. simpl in x, x'. erewrite -> Fin.Fin_eqProp_iff with (i := x) (i' := x'). eauto.
    + ii. erewrite -> Fin.Fin_eqProp_iff in x_EQ, y_EQ. do 2 red. rewrite x_EQ, y_EQ. reflexivity.
Qed.

Corollary Fin_toTree_eq `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (n : nat)
  : Cardinality.toTree (Cardinality.ofType (Fin.t n)) == Ord_of_nat n.
Proof.
  eapply Cardinality_toTree_eq_intro. eapply Fin_hasCardinality_var1.
Qed.

Corollary card_Ord_of_nat_toTree_eq `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (n : nat)
  : Cardinality.toTree (card (Ord_of_nat n)) == Ord_of_nat n.
Proof.
  eapply Cardinality_toTree_eq_intro. eapply isCardinal_elim. exists (Cardinality.ofType (Fin.t n)). eapply Fin_hasCardinality_var1.
Qed.

Corollary card_Ord_of_nat_le_Fin `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (n : nat)
  : card (Ord_of_nat n) =< Cardinality.ofType (Fin.t n).
Proof.
  rewrite Cardinality_le_iff. rewrite card_Ord_of_nat_toTree_eq. rewrite Fin_toTree_eq. reflexivity.
Qed.

Lemma card_Ord_suc_of_nat_not_le_Fin `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (n : nat)
  : ~ card (Ord.suc (Ord_of_nat n)) =< Cardinality.ofType (Fin.t n).
Proof.
  intros H_le. rewrite Cardinality_le_iff in H_le.
  change (Cardinality.toTree (card (Ord_of_nat (S n))) ≦ᵣ Cardinality.toTree (Cardinality.ofType (Fin.t n))) in H_le.
  rewrite card_Ord_of_nat_toTree_eq in H_le. rewrite Fin_toTree_eq in H_le.
  pose proof (rLt_StrictOrder.(StrictOrder_Irreflexive) (Ord_of_nat n)) as H_irrefl.
  eapply H_irrefl.
  eapply rLt_rLe_rLt.
  - unfold Ord.suc. eapply rLt_succ_intro.
  - exact H_le.
Qed.

Theorem Fin_next_toTree_eq `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (n : nat)
  : Cardinality.toTree (next (Cardinality.ofType (Fin.t n))) == Ord.suc (Ord_of_nat n).
Proof.
  eapply Ordinal1.Ordinal_rEq_Ordinal_elim.
  - eapply hasCardinality_isOrdinal. eapply hasCardinality_intro.
  - change (isOrdinal (Ord_of_nat (S n))). eapply Ord_of_nat_isOrdinal.
  - split.
    + rewrite next_toTree_eq. eapply Hartogs_minimal_nonembed.
      * change (isOrdinal (Ord_of_nat (S n))). eapply Ord_of_nat_isOrdinal.
      * change (~ card (Ord.suc (Ord_of_nat n)) =< Cardinality.ofType (Fin.t n)). eapply card_Ord_suc_of_nat_not_le_Fin.
    + rewrite next_toTree_eq. eapply succ_rLe_intro. rewrite Hartogs_rLt_iff.
      * eapply card_Ord_of_nat_le_Fin.
      * eapply Ord_of_nat_isOrdinal.
Qed.

Corollary Fin_next_hasCardinality `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (n : nat)
  : next (Cardinality.ofType (Fin.t n)) `hasCardinality` Ord.suc (Ord_of_nat n).
Proof.
  rewrite <- Cardinality_toTree_eq_iff. eapply Fin_next_toTree_eq.
Qed.

Lemma fromWfSet_vs_omega
  : @fromWfSet nat Nat.lt lt_wf == omega.
Proof.
  eapply Ordinal1.Ordinal_rEq_Ordinal_elim.
  { change (isOrdinal (@FromOrderType _ _ nat_isWoset)). eapply FromOrderType_isOrdinal. }
  { eapply omega_isOrdinal. }
  split.
  - econs. simpl. intros n. rewrite -> fromWf_vs_Ord_of_nat.
    eapply member_implies_rLt. unfold omega. rewrite indexed_union_spec.
    exists (S n). simpl. rewrite succ_spec. now right.
  - econs. simpl. intros [n c]; simpl in *.
    transitivity (Ord_of_nat n).
    { eapply member_implies_rLt. eauto with *. }
    rewrite <- fromWf_vs_Ord_of_nat.
    eapply member_implies_rLt. eauto with *.
Qed.

Theorem nat_hasCardinality
  : Cardinality.ofType nat `hasCardinality` omega.
Proof.
  split.
  - exists Nat.lt, lt_wf. splits.
    + intros x x'. change (x = x' \/ x < x' \/ x' < x)%nat. lia.
    + exact Nat_lt_Transitive.
    + ii; simpl in *; lia.
    + exact fromWfSet_vs_omega.
  - intros alpha (R & R_wf & R_total & R_Transitive & R_eqPropCompatible2 & Halpha).
    rewrite <- Halpha. unfold omega. rewrite indexed_union_rLe_iff. intros n.
    set (Rn := binary_relation_on_image R (@Fin.evalFin n)).
    set (Rn_wf := relation_on_image_liftsWellFounded R (@Fin.evalFin n) R_wf).
    assert (Rn_total : forall x : Fin.t n, forall x' : Fin.t n, x == x' \/ Rn x x' \/ Rn x' x).
    { intros x x'. unfold Rn, binary_relation_on_image.
      pose proof (R_total (Fin.evalFin x) (Fin.evalFin x')) as [H_eq | [H_lt | H_gt]].
      - left. rewrite Fin.Fin_eqProp_iff. now apply Fin.evalFin_inj.
      - now right; left.
      - now right; right.
    }
    assert (Rn_Transitive : Transitive Rn).
    { unfold Rn, binary_relation_on_image. intros x y z H1 H2. eapply R_Transitive; eauto. }
    assert (Rn_eqPropCompatible2 : eqPropCompatible2 Rn).
    { intros x1 x2 y1 y2 Hx Hy. unfold Rn, binary_relation_on_image in *. eapply R_eqPropCompatible2.
      - rewrite Fin.Fin_eqProp_iff in Hx. now subst.
      - rewrite Fin.Fin_eqProp_iff in Hy. now subst.
    }
    transitivity (@fromWfSet (Fin.t n) Rn Rn_wf).
    + refine (proj2 (Fin_hasCardinality n) _ _). exists Rn, Rn_wf. splits; eauto with *.
    + eapply fromWfSet_cong with (f := @Fin.evalFin n); eauto.
Qed.

End COUNTABLE.

Section ALEPH.

Definition aleph0 : Tree :=
  omega.

Lemma aleph0_isCardinal `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}
  : isCardinal aleph0.
Proof.
  exists (Cardinality.ofType nat). eapply nat_hasCardinality.
Qed.

Lemma aleph0_isOrdinal `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}
  : isOrdinal aleph0.
Proof.
  eapply isCardinal_isOrdinal. eapply aleph0_isCardinal.
Qed.

Definition alephS (kappa : Tree) : Tree :=
  Cardinality.toTree (next (card kappa)).

Lemma alephS_eq_Hartogs `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (o : Tree)
  : alephS o == Hartogs (children o).
Proof.
  eapply next_toTree_eq.
Qed.

Lemma alephS_isCardinal `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (o : Tree)
  : isCardinal (alephS o).
Proof.
  exists (next (Cardinality.mk (children o) (children_isSetoid o))). eapply hasCardinality_intro.
Qed.

Lemma alephS_isOrdinal `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (o : Tree)
  : isOrdinal (alephS o).
Proof.
  eapply isCardinal_isOrdinal. eapply alephS_isCardinal.
Qed.

Lemma alephS_gt `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}
  (o : Tree)
  (ORDINAL : isOrdinal o)
  : o <ᵣ alephS o.
Proof.
  rewrite alephS_eq_Hartogs. rewrite Hartogs_rLt_iff; eauto with *.
Qed.

Lemma alephS_ge `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (o : Tree)
  (ORDINAL : isOrdinal o)
  : o ≦ᵣ alephS o.
Proof.
  eapply rLt_implies_rLe. eapply alephS_gt; eauto.
Qed.

Lemma card_le_card_intro `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (o : Tree) (o' : Tree)
  (ORDINAL : isOrdinal o)
  (ORDINAL' : isOrdinal o')
  (LE : o ≦ᵣ o')
  : card o =< card o'.
Proof.
  unfold card. rewrite <- Hartogs_rLt_iff; eauto. eapply rLe_rLt_rLt; eauto. rewrite -> Hartogs_rLt_iff; eauto. reflexivity.
Qed.

Lemma alephS_le_alpheS_intro `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (o : Tree) (o' : Tree)
  (ORDINAL : isOrdinal o)
  (ORDINAL' : isOrdinal o')
  (LE : o ≦ᵣ o')
  : alephS o ≦ᵣ alephS o'.
Proof.
  eapply Cardinality_toTree_isMonotonic1. eapply next_isMonotonic1. eapply card_le_card_intro; eauto.
Qed.

Lemma aleph_base_good `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}
  : isCardinal aleph0.
Proof.
  eapply aleph0_isCardinal.
Qed.

Lemma aleph_next_good `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (d : Tree)
  (GOOD : isCardinal d)
  : isCardinal (alephS d).
Proof.
  eapply alephS_isCardinal.
Qed.

Lemma aleph_next_extensive `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (d : Tree)
  (GOOD : isCardinal d)
  : d ≦ᵣ alephS d.
Proof.
  eapply alephS_ge. eapply isCardinal_isOrdinal. exact GOOD.
Qed.

Lemma aleph_next_congruence `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} d d'
  (GOOD : isCardinal d)
  (GOOD' : isCardinal d')
  (EQ : d =ᵣ d')
  : alephS d =ᵣ alephS d'.
Proof.
  destruct EQ as [LE GE]. split; eapply alephS_le_alpheS_intro; eauto using isCardinal_isOrdinal.
Qed.

#[local] Hint Resolve aleph_base_good aleph_next_good aleph_next_extensive aleph_next_extensive aleph_next_congruence : core.

Definition aleph : Tree -> Tree :=
  Ord.orec aleph0 alephS.

Let aleph_dle_refl d1
  (GOOD : isCardinal d1)
  : d1 ≦ᵣ d1.
Proof.
  reflexivity.
Qed.

Let aleph_dle_trans d1 d2 d3
  (GOOD1 : isCardinal d1)
  (GOOD2 : isCardinal d2)
  (GOOD3 : isCardinal d3)
  (LE : d1 ≦ᵣ d2)
  (LE' : d2 ≦ᵣ d3)
  : d1 ≦ᵣ d3.
Proof.
  now transitivity d2.
Qed.

Context `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}.

Let aleph_djoin_good (I : Type@{Set_u}) (ds : I -> Tree)
  (CHAIN : forall i1, forall i2, ds i1 ≦ᵣ ds i2 \/ ds i2 ≦ᵣ ds i1)
  (GOODs : forall i, isCardinal (ds i))
  : isCardinal (indexed_union I ds).
Proof.
  eapply indexed_union_ofCardinals_isCardinal; eauto.
Qed.

Let aleph_djoin_isSupremum (I : Type@{Set_u}) (ds : I -> Tree) (d : Tree)
  (CHAIN : forall i1, forall i2, ds i1 ≦ᵣ ds i2 \/ ds i2 ≦ᵣ ds i1)
  (GOODs : forall i, isCardinal (ds i))
  (GOOD : isCardinal d)
  : indexed_union I ds ≦ᵣ d <-> (forall i, ds i ≦ᵣ d).
Proof.
  eapply indexed_union_ofCardinals_isSupremum; eauto.
Qed.

#[local] Notation rank_trichotomy := (O.wlt_trichotomous (classic := classic) (WOSET := rLt_isWellOrdering)).

#[local] Infix "⊑" := rLe.

#[local] Infix "≡" := rEq.

#[local] Notation good := isCardinal.

#[local] Notation rec := aleph.

#[local] Notation dbase := aleph0.

#[local] Notation next := alephS.

#[local] Notation djoin := indexed_union.

#[local] Notation dle_refl := aleph_dle_refl.

#[local] Notation dle_trans := aleph_dle_trans.

#[local] Notation djoin_good := aleph_djoin_good.

#[local] Notation djoin_supremum := aleph_djoin_isSupremum.

#[local] Notation next_good := aleph_next_good.

#[local] Notation next_extensive := aleph_next_extensive.

#[local] Notation next_congruence := aleph_next_congruence.

Let aleph_djoin_upperbound (I : Type@{Set_u}) (ds : I -> Tree)
  (CHAIN : forall i1, forall i2, ds i1 ⊑ ds i2 \/ ds i2 ⊑ ds i1)
  (GOODs : forall i, good (ds i))
  : forall i : I, ds i ⊑ djoin I ds.
Proof.
  i. eapply djoin_supremum; eauto.
Qed.

#[local] Hint Resolve alephS_isCardinal : core.

Theorem aleph_rec_spec (o : Tree)
  : ⟪ mono_rec : forall o', o' ≦ᵣ o -> rec o' ⊑ rec o ⟫ /\ ⟪ base_rec : dbase ⊑ rec o ⟫ /\ ⟪ next_rec : forall o', o' <ᵣ o -> next (rec o') ⊑ rec o ⟫ /\ ⟪ good_rec : good (rec o) ⟫.
Proof.
  rename o into t. pose proof (rLt_wf t) as H_ACC. induction H_ACC as [t _ IH]. destruct t as [cs ts]; simpl.
  assert (H_chain : forall cs' : Type@{Set_u}, forall ts' : cs' -> Tree, forall LE : forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c, forall c1 : cs', forall c2 : cs', next (rec (ts' c1)) ⊑ next (rec (ts' c2)) \/ next (rec (ts' c2)) ⊑ next (rec (ts' c1))).
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
      + eapply IH; eauto.
      + eapply IH; eauto.
      + eapply next_extensive. eapply IH; eauto.
    - right. eapply dle_trans with (d2 := rec (ts' c1)); eauto.
      + eapply IH; eauto.
      + eapply IH; eauto.
      + eapply next_extensive. eapply IH; eauto.
  }
  assert (H_next_good : forall cs' : Type@{Set_u}, forall ts' : cs' -> Tree, forall LE : forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c, forall c' : cs', good (next (rec (ts' c')))).
  { ii. eapply next_good. eapply IH; eauto. econs. eapply LE. }
  set (fun cs' : Type@{Set_u} => fun ts' : cs' -> Tree => fun b : bool => if b then dbase else djoin cs' (fun c' => next (rec (ts' c')))) as f.
  assert (claim1 : forall b1 : bool, forall b2 : bool, forall cs' : Type@{Set_u}, forall ts' : cs' -> Tree, forall LE : forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c, f cs' ts' b1 ⊑ f cs' ts' b2 \/ f cs' ts' b2 ⊑ f cs' ts' b1).
  { ii.
    assert (helper1 : forall c' : cs', ts' c' <ᵣ mkNode cs ts).
    { i; econs; eapply LE. }
    assert (GOOD1 : forall i : cs', isCardinal (next (rec (ts' i)))).
    { i; eapply next_good. exploit (IH (ts' i)); auto. i; des; eauto. }
    assert (helper2 : dbase ⊑ djoin cs' (fun c' : cs' => next (rec (ts' c'))) \/ djoin cs' (fun c' : cs' => next (rec (ts' c'))) ⊑ dbase).
    { pose proof (classic (inhabited cs')) as [YES | NO]; [left | right].
      - destruct YES as [c']. exploit (IH (ts' c')); auto. i; des.
        enough (next (rec (ts' c')) ⊑ djoin cs' (fun i : cs' => next (rec (ts' i)))) by now eapply dle_trans with (d2 := next (rec (ts' c'))); eauto.
        eapply aleph_djoin_upperbound with (ds := fun c' : cs' => next (rec (ts' c'))); eauto.
      - enough (forall i : cs', next (rec (ts' i)) ⊑ dbase) by now eapply djoin_supremum; eauto.
        intros c'. contradiction NO. econs. exact c'.
    }
    destruct b1, b2; simpl in *; auto; tauto.
  }
  assert (claim2 : forall b : bool, forall cs' : Type@{Set_u}, forall ts' : cs' -> Tree, forall LE : forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c, good (f cs' ts' b)).
  { ii. destruct b; simpl; eauto. }
  set (djoin bool (f cs ts)) as x.
  assert (claim3 : good x).
  { eapply djoin_good; auto.
    - ii; eapply claim1; eauto with *.
    - ii; eapply claim2; eauto with *.
  }
  assert (claim4 : dbase ⊑ x).
  { eapply aleph_djoin_upperbound with (ds := f cs ts) (i := true); auto.
    - ii; eapply claim1; eauto with *.
    - ii; eapply claim2; eauto with *.
  }
  assert (claim5 : forall cs' : Type@{Set_u}, forall ts' : cs' -> Tree, forall H_rLt : forall c, ts' c <ᵣ mkNode cs ts, forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c).
  { ii. pose proof (H_rLt c') as [[c H_rLe]]; simpl in *. exists c. exact H_rLe. }
  assert (claim6 : forall o : Tree, forall LE : o ≦ᵣ mkNode cs ts, rec o ⊑ x).
  { intros [cs' ts'] [H_rLt]. simpl in *. unfold Ord.join.
    change (fun b : bool => if b then dbase else djoin cs' (fun c : cs' => next (rec (ts' c)))) with (f cs' ts').
    rewrite -> djoin_supremum; eauto. destruct i; auto. simpl. eapply djoin_supremum; i; auto.
    { unfold x. eapply dle_trans with (d2 := djoin cs' (fun c' => next (rec (ts' c')))); eauto.
      - eapply aleph_djoin_upperbound with (ds := fun c' : cs' => next (rec (ts' c'))); eauto.
      - eapply djoin_supremum; eauto.
        intros c'. pose proof (H_rLt c') as [[c H_rLe]]; simpl in *.
        rewrite InducedOrdinal.rLe_iff_rLt_or_rEq in H_rLe. destruct H_rLe as [H_LT | H_EQ].
        + eapply dle_trans with (d2 := next (rec (ts c))); auto.
          { eapply dle_trans with (d2 := rec (ts c)); auto.
            - eapply IH; eauto with *.
            - eapply IH; eauto with *.
            - eapply next_extensive; eauto. eapply IH; eauto with *.
          }
          { unfold f. eapply dle_trans with (d2 := djoin cs (fun i : cs => next (rec (ts i)))); auto.
            - eapply djoin_good; eauto with *.
            - eapply aleph_djoin_upperbound with (ds := fun c : cs => next (rec (ts c))); eauto with *.
            - eapply aleph_djoin_upperbound with (ds := f cs ts) (i := false); eauto with *.
          }
        + eapply dle_trans with (d2 := next (rec (ts c))); eauto.
          { eapply next_congruence.
            - eapply IH; eauto with *.
            - eapply IH; eauto with *.
            - destruct H_EQ as [H_LE1 H_LE2]. split; eapply IH; auto with *.
          }
          { unfold f. eapply dle_trans with (d2 := djoin cs (fun i : cs => next (rec (ts i)))); auto.
            - eapply djoin_good; eauto with *.
            - eapply aleph_djoin_upperbound with (ds := fun c : cs => next (rec (ts c))); eauto with *.
            - eapply aleph_djoin_upperbound with (ds := f cs ts) (i := false); eauto with *.
          }
    }
  }
  splits; auto. intros o H_rLt.
  pose proof (classic (exists o' : Tree, o <ᵣ o' /\ o' <ᵣ mkNode cs ts)) as [YES | NO].
  - unfold Ord.join. des. hexploit (IH o'); auto. i; des. eapply dle_trans with (d2 := rec o'); auto.
    eapply claim6. eapply rLt_implies_rLe; eauto.
  - assert (exists c, ts c =ᵣ o) as [c H_rEq].
    { eapply NNPP. intros H_contra. rewrite InducedOrdinal.rLt_iff_not_rGe in H_rLt. contradiction H_rLt.
      econs. simpl. intros c. pose proof (rank_trichotomy (ts c) o) as [H_EQ | [H_LT | H_GT]]; eauto.
      - contradiction H_contra; eauto.
      - contradiction NO; eauto with *.
    }
    assert (rec o ≡ rec (ts c)) as claim7.
    { destruct H_rEq; split; eapply IH; eauto with *. }
    unfold Ord.join. eapply dle_trans with (d2 := next (rec (ts c))); auto.
    { eapply next_congruence.
      - eapply IH; eauto with *.
      - eapply IH; eauto with *.
      - now symmetry.
    }
    { eapply dle_trans with (d2 := djoin cs (fun i : cs => next (rec (ts i)))); auto.
      - eapply djoin_good; eauto with *.
      - eapply aleph_djoin_upperbound with (ds := fun c : cs => next (rec (ts c))); eauto with *.
      - eapply aleph_djoin_upperbound with (ds := f cs ts) (i := false); eauto with *.
    }
Qed.

Lemma aleph_le_rec (t : Tree) (t' : Tree)
  (H_rLe : t ≦ᵣ t')
  : rec t ⊑ rec t'.
Proof.
  eapply aleph_rec_spec; eauto.
Qed.

Lemma aleph_eq_rec (t : Tree) (t' : Tree)
  (H_rLe : t =ᵣ t')
  : rec t ≡ rec t'.
Proof.
  destruct H_rLe; split; eapply aleph_rec_spec; eauto.
Qed.

Lemma aleph_lt_rec (t : Tree) (t' : Tree)
  (H_rLt : t <ᵣ t')
  : next (rec t) ⊑ rec t'.
Proof.
  eapply aleph_rec_spec; eauto.
Qed.

Lemma aleph_rec_le_base (t : Tree)
  : dbase ⊑ rec t.
Proof.
  eapply aleph_rec_spec; eauto.
Qed.

Lemma aleph_good_rec (t : Tree)
  : good (rec t).
Proof.
  eapply aleph_rec_spec; eauto.
Qed.

#[local] Hint Resolve aleph_le_rec aleph_eq_rec aleph_lt_rec : simplication_hints.

#[local] Hint Resolve aleph_rec_le_base aleph_good_rec : simplication_hints.

Lemma aleph_rec_next_dle (t : Tree) (t' : Tree)
  (H_rLe : t ≦ᵣ t')
  : next (rec t) ⊑ next (rec t').
Proof.
  rewrite InducedOrdinal.rLe_iff_rLt_or_rEq in H_rLe. destruct H_rLe as [H_rLt | H_rEq].
  - eapply dle_trans with (d2 := rec t'); eauto with *.
  - eapply next_congruence; eauto with *.
Qed.

Lemma aleph_rec_chain (t : Tree) (t' : Tree)
  : rec t ⊑ rec t' \/ rec t' ⊑ rec t.
Proof.
  pose proof (InducedOrdinal.rLe_total t t') as [H | H]; [left | right]; eauto with *.
Qed.

Lemma aleph_rec_next_chain (t : Tree) (t' : Tree)
  : next (rec t) ⊑ next (rec t') \/ next (rec t') ⊑ next (rec t).
Proof.
  pose proof (InducedOrdinal.rLe_total t t') as [H | H]; [left | right]; eapply aleph_rec_next_dle; eauto.
Qed.

Lemma aleph_good_next_rec (cs : Type@{Set_u}) (ts : cs -> Tree)
  : forall c : cs, good (next (rec (ts c))).
Proof.
  eauto.
Qed.

#[local] Hint Resolve aleph_rec_next_dle aleph_rec_chain : simplication_hints.

#[local] Hint Resolve aleph_rec_next_chain aleph_good_next_rec : core.

Let dbase_next_rec alpha
  : dbase ⊑ next (rec alpha).
Proof.
  eauto with *.
Qed.

Let j (cs : Type@{Set_u}) (ts : cs -> Tree) (b : bool) : Tree :=
  if b then dbase else djoin cs (fun c => next (rec (ts c))).

Lemma aleph_j_chain (cs : Type@{Set_u}) (ts : cs -> Tree) (b : bool) (b' : bool)
  : j cs ts b ⊑ j cs ts b' \/ j cs ts b' ⊑ j cs ts b.
Proof.
  assert (dbase ⊑ djoin cs (fun c => next (rec (ts c))) \/ djoin cs (fun c => next (rec (ts c))) ⊑ dbase) as claim1.
  { pose proof (classic (inhabited cs)) as [YES | NO]; [left | right].
    - destruct YES as [c]. eapply dle_trans with (d2 := next (rec (ts c))); auto.
      eapply aleph_djoin_upperbound with (ds := fun c : cs => next (rec (ts c))); eauto with *.
    - eapply djoin_supremum; auto. intros c. contradiction NO. econs. exact c.
  }
  destruct b, b'; simpl; auto with *; try tauto.
Qed.

Lemma aleph_good_j (cs : Type@{Set_u}) (ts : cs -> Tree)
  : forall b, good (j cs ts b).
Proof.
  intros [ | ]; simpl; eauto with *.
Qed.

#[local] Hint Resolve aleph_j_chain aleph_good_j : core.

Lemma aleph_rec_zero (o : Tree)
  (ZERO : o ≡ empty)
  : rec o ≡ dbase.
Proof.
  transitivity (rec empty); eauto with *.
  change (djoin bool (j Empty_set (Empty_set_rect _)) ≡ dbase). split.
  - eapply djoin_supremum; auto. intros [ | ]; auto. eapply djoin_supremum; auto; intros [].
  - eapply aleph_djoin_upperbound with (ds := j Empty_set (Empty_set_rect _)) (i := true); eauto.
Qed.

Lemma aleph_rec_succ (o : Tree) (alpha : Tree)
  (SUCC : o ≡ succ alpha)
  : rec o ≡ next (rec alpha).
Proof.
  transitivity (rec (succ alpha)); eauto with *.
  change (djoin bool (j { b : bool & children (if b then alpha else singleton alpha) } (fun c => childnodes (if projT1 c then alpha else singleton alpha) (projT2 c))) ≡ next (rec alpha)). split.
  - eapply djoin_supremum; auto. intros [ | ]; simpl; auto. eapply djoin_supremum; auto.
    intros [[ | ] c]; simpl; eapply aleph_rec_next_dle.
    + eapply rLt_implies_rLe. econs. exists c. reflexivity.
    + simpl in c. destruct c as [ | ]; reflexivity.
  - refine (let c : { b : bool & children (if b then alpha else singleton alpha) } := @existT _ _ false true in _).
    eapply dle_trans with (d2 := djoin { b : bool & children (if b then alpha else singleton alpha) } (fun c => next (rec (childnodes (if projT1 c then alpha else singleton alpha) (projT2 c))))); eauto.
    + eapply aleph_djoin_upperbound with (ds := fun c : { b : bool & children (if b then alpha else singleton alpha) } => next (rec (childnodes (if projT1 c then alpha else singleton alpha) (projT2 c)))) (i := c); eauto with *.
    + eapply aleph_djoin_upperbound with (ds := j { b : bool & children (if b then alpha else singleton alpha) } (fun c => childnodes (if projT1 c then alpha else singleton alpha) (projT2 c))) (i := false); eauto.
Qed.

Let djoin_rec_good (cs : Type@{Set_u}) (ts : cs -> Tree)
  : good (djoin cs (fun i : cs => rec (ts i))).
Proof.
  eauto with *.
Qed.

Let rec_good (cs : Type@{Set_u}) (ts : cs -> Tree)
  : forall c : cs, good (rec (ts c)).
Proof.
  eauto with *.
Qed.

Let dbase_le_rec (cs : Type@{Set_u}) (ts : cs -> Tree)
  : forall c : cs, dbase ⊑ rec (ts c).
Proof.
  eauto with *.
Qed.

Lemma aleph_rec_lim' (o : Tree) (cs : Type@{Set_u}) (ts : cs -> Tree)
  (APPROX : forall c1 : cs, exists c2 : cs, ts c1 <ᵣ ts c2)
  (INHABITED : inhabited cs)
  (LIM' : o ≡ indexed_union cs ts)
  : rec o ≡ djoin cs (fun c : cs => rec (ts c)).
Proof.
  destruct INHABITED as [c]. destruct o as [cs' ts']; simpl.
  change (djoin bool (j cs' ts') ≡ djoin cs (fun i : cs => rec (ts i))); split.
  - eapply djoin_supremum; auto. intros [ | ]; simpl.
    + eapply dle_trans with (d2 := rec (ts c)); auto.
      eapply aleph_djoin_upperbound with (ds := fun i : cs => rec (ts i)) (i := c); eauto with *.
    + eapply djoin_supremum; auto.
      clear c. intros c'. destruct LIM' as [LE1 LE2]; simpl in *. destruct LE1 as [H_rLt]; simpl in *.
      pose proof (H_rLt c') as [[c H_rLe]]; simpl in *. eapply dle_trans with (d2 := rec (ts (projT1 c))); auto.
      * eapply aleph_lt_rec. econs. exists (projT2 c). exact H_rLe.
      * eapply aleph_djoin_upperbound with (ds := fun i : cs => rec (ts i)) (i := projT1 c); eauto with *.
  - eapply djoin_supremum; auto with *. clear c. intros c. eapply dle_trans with (d2 := djoin cs (fun c => rec (ts c))); auto.
    + eapply aleph_djoin_upperbound with (ds := fun i : cs => rec (ts i)) (i := c); eauto with *.
    + clear c. eapply djoin_supremum; auto with *. intros c1. simpl in *. pose proof (APPROX c1) as [c2 H_rLt].
      destruct H_rLt as [[c H_rLe]]. destruct LIM' as [LE1 LE2]. destruct LE2 as [LE2]; simpl in *.
      pose proof (LE2 (@existT cs (fun i : cs => children (ts i)) c2 c)) as claim1. simpl in *. destruct claim1 as [[c' H_rLe']]. simpl in *.
      eapply dle_trans with (d2 := rec (ts' c')); auto.
      { eapply aleph_le_rec. transitivity (childnodes (ts c2) c); auto. }
      { eapply dle_trans with (d2 := djoin cs' (fun i : cs' => next (rec (ts' i)))); auto.
        - eapply dle_trans with (d2 := next (rec (ts' c'))); auto.
          eapply aleph_djoin_upperbound with (ds := fun i : cs' => next (rec (ts' i))) (i := c'); eauto with *.
        - eapply aleph_djoin_upperbound with (ds := j cs' ts') (i := false); eauto with *.
      }
Qed.

Lemma aleph_isCardinal (o : Tree)
  : isCardinal (aleph o).
Proof.
  exact (aleph_good_rec o).
Qed.

Lemma aleph_isOrdinal (o : Tree)
  : isOrdinal (aleph o).
Proof.
  eapply isCardinal_isOrdinal. eapply aleph_isCardinal.
Qed.

Lemma aleph_zero (o : Tree)
  (ZERO : o =ᵣ empty)
  : aleph o =ᵣ aleph0.
Proof.
  exact (aleph_rec_zero o ZERO).
Qed.

Lemma aleph_succ (o : Tree) (alpha : Tree)
  (SUCC : o =ᵣ succ alpha)
  : aleph o =ᵣ alephS (aleph alpha).
Proof.
  exact (aleph_rec_succ o alpha SUCC).
Qed.

Lemma aleph_lim' (o : Tree) (I : Type@{Set_u}) (alpha : I -> Tree)
  (APPROX : forall i1 : I, exists i2 : I, alpha i1 <ᵣ alpha i2)
  (INHABITED : inhabited I)
  (LIMIT : o =ᵣ indexed_union I alpha)
  : aleph o =ᵣ indexed_union I (fun i : I => aleph (alpha i)).
Proof.
  exact (aleph_rec_lim' o I alpha APPROX INHABITED LIMIT).
Qed.

Lemma le_aleph (alpha : Tree) (beta : Tree)
  (LE : alpha ≦ᵣ beta)
  : aleph alpha ≦ᵣ aleph beta.
Proof.
  exact (aleph_le_rec alpha beta LE).
Qed.

Lemma lt_aleph (alpha : Tree) (beta : Tree)
  (LT : alpha <ᵣ beta)
  : aleph alpha <ᵣ aleph beta.
Proof.
  eapply rLt_rLe_rLt with (y := alephS (aleph alpha)).
  - eapply alephS_gt. eapply aleph_isOrdinal.
  - eapply aleph_lt_rec. exact LT.
Qed.

Lemma aleph0_le_aleph (o : Tree)
  : aleph0 ≦ᵣ aleph o.
Proof.
  exact (aleph_rec_le_base o).
Qed.

Theorem aleph_expand
  : forall o : Tree, o ≦ᵣ aleph o.
Proof.
  eapply member_rect. intros o IH. eapply rLe_intro_var1. intros x x_in. eapply rLe_rLt_rLt.
  - eapply IH. exact x_in.
  - eapply rLt_rLe_rLt.
    + eapply alephS_gt. eapply aleph_isOrdinal.
    + eapply aleph_lt_rec. eapply member_implies_rLt. exact x_in.
Qed.

Theorem aleph_hasCardinality (o : Tree)
  : card (aleph o) `hasCardinality` aleph o.
Proof.
  eapply isCardinal_elim. eapply aleph_isCardinal.
Qed.

End ALEPH.

Section BETH.

Context `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}.

#[local] Existing Instance children_isSetoid.

#[local] Existing Instance children_isWoset.

#[local] Existing Instance Ord_isProset.

Definition powerCard (o : Tree) : Cardinality.t :=
  card (power o).

Definition beth0 : Tree :=
  omega.

Definition singleton_index (o : Tree) (c : children o) : children (power o) :=
  fun c' : children o => childnodes o c' == childnodes o c.

Lemma singleton_index_spec (o : Tree) (c : children o)
  : forall z, z \in childnodes (power o) (singleton_index o c) <-> z == childnodes o c.
Proof.
  i. unfold singleton_index. simpl childnodes. rewrite filterc_spec. split.
  - intros [c' [EQ H]]. transitivity (childnodes o c'); eauto.
  - intros EQ. exists c. split; eauto with *.
Qed.

Lemma subset_children_Cardinality_le x y
  (SUBSET : x \subseteq y)
  : card x =< card y.
Proof.
  destruct x as [csx tsx], y as [csy tsy]. simpl in *.
  exploit (Axiom_of_Choice csx (fun _ => csy) (fun c d => tsx c == tsy d)).
  { intros c. pose proof (SUBSET _ (member_intro _ _ c)) as [d EQ]; eauto. }
  intros [f Hf]. exists f.
  - intros c1 c2 H_EQ; simpl in c1, c2. change (tsy (f c1) == tsy (f c2)).
    do 2 rewrite <- Hf. exact H_EQ.
  - intros c1 c2 H_EQ; simpl in c1, c2. change (tsx c1 == tsx c2).
    do 2 rewrite -> Hf. exact H_EQ.
Qed.

Lemma power_isMmonotonic x y
  (SUBSET : x \subseteq y)
  : power x \subseteq power y.
Proof.
  intros z H_in. rewrite power_spec in H_in |- *. intros w H_w. eapply SUBSET. eauto with *.
Qed.

Lemma powerCard_le x y
  (SUBSET : x \subseteq y)
  : powerCard x =< powerCard y.
Proof.
  eapply subset_children_Cardinality_le. now eapply power_isMmonotonic.
Qed.

Lemma powerCard_lowerbound (o : Tree)
  : card o =< powerCard o.
Proof.
  exists (singleton_index o).
  - intros c1 c2 H_EQ. change (childnodes (power o) (singleton_index o c1) == childnodes (power o) (singleton_index o c2)).
    eapply extensionality. intros z. do 2 rewrite singleton_index_spec. simpl in H_EQ. unred_eqTree. now rewrite H_EQ.
  - intros c1 c2 H_EQ. change (childnodes (power o) (singleton_index o c1) == childnodes (power o) (singleton_index o c2)) in H_EQ.
    change (childnodes o c1 == childnodes o c2).
    assert (H_in : childnodes o c1 \in childnodes (power o) (singleton_index o c2)).
    { eapply member_eqProp_member.
      - rewrite singleton_index_spec. reflexivity.
      - exact H_EQ.
    }
    now rewrite singleton_index_spec in H_in.
Qed.

Theorem powerCard_not_le (o : Tree)
  : ~ powerCard o =< card o.
Proof.
  intros [f f_cong f_inj].
  pose (Diag := fun c : children o => exists P : children (power o), f P == c /\ ~ childnodes o c \in childnodes (power o) P).
  refine (let S : children (power o) := Diag in _).
  set (d := f S).
  assert (H_diag_not : ~ childnodes o d \in childnodes (power o) S).
  { intros H_in. simpl childnodes in H_in. rewrite filterc_spec in H_in.
    destruct H_in as [c [H_EQ [P [HfP HnotP]]]].
    assert (Hf_EQ : f P == f S).
    { transitivity c; auto. now symmetry. }
    assert (HP_EQ : P == S).
    { eapply f_inj. exact Hf_EQ. }
    assert (H_inP : childnodes o c \in childnodes (power o) P).
    { simpl. rewrite <- H_EQ. do 2 red in HP_EQ. simpl childnodes in HP_EQ. rewrite -> HP_EQ.
      rewrite filterc_spec. exists d. split; eauto with *. red. red. exists P. split; eauto.
      now rewrite -> H_EQ at 1.
    }
    contradiction (HnotP H_inP).
  }
  assert (H_diag_yes : childnodes o d \in childnodes (power o) S).
  { simpl. rewrite filterc_spec. exists d; split; auto with *.
    red. red. exists S; split; auto with *. reflexivity.
  }
  exact (H_diag_not H_diag_yes).
Qed.

Theorem powerCard_gt (o : Tree)
  : card o ≨ powerCard o.
Proof.
  split.
  - exact (powerCard_lowerbound o).
  - intros [f g f_cong g_cong f_inj g_inj]. eapply powerCard_not_le. exists g; eauto.
Qed.

Definition bethS (o : Tree) : Tree :=
  Cardinality.toTree (powerCard o).

Lemma bethS_isCardinal (o : Tree)
  : isCardinal (bethS o).
Proof.
  exists (powerCard o). eapply hasCardinality_intro.
Qed.

Lemma bethS_isOrdinal (o : Tree)
  : isOrdinal (bethS o).
Proof.
  eapply isCardinal_isOrdinal. eapply bethS_isCardinal.
Qed.

Lemma alephS_le_bethS (o : Tree)
  : alephS o ≦ᵣ bethS o.
Proof.
  unfold alephS, bethS. eapply Cardinality_toTree_isMonotonic1. rewrite next_le_iff_lt. exact (powerCard_gt o).
Qed.

Lemma bethS_gt (o : Tree)
  (ORDINAL : isOrdinal o)
  : o <ᵣ bethS o.
Proof.
  eapply rLt_rLe_rLt with (y := alephS o).
  - eapply alephS_gt. exact ORDINAL.
  - eapply alephS_le_bethS.
Qed.

Lemma bethS_ge (o : Tree)
  (ORDINAL : isOrdinal o)
  : o ≦ᵣ bethS o.
Proof.
  eapply rLt_implies_rLe. eapply bethS_gt. exact ORDINAL.
Qed.

Lemma bethS_le_bethS_intro (o o' : Tree)
  (ORDINAL : isOrdinal o)
  (ORDINAL' : isOrdinal o')
  (LE : o ≦ᵣ o')
  : bethS o ≦ᵣ bethS o'.
Proof.
  unfold bethS. eapply Cardinality_toTree_isMonotonic1. eapply powerCard_le.
  eapply Ordinal1.Ordinal_rLe_Ordinal_elim; eauto with *.
Qed.

Let beth_djoin_good (I : Type@{Set_u}) (ds : I -> Tree)
  (CHAIN : forall i1, forall i2, ds i1 ≦ᵣ ds i2 \/ ds i2 ≦ᵣ ds i1)
  (GOODs : forall i, isCardinal (ds i))
  : isCardinal (indexed_union I ds).
Proof.
  eapply indexed_union_ofCardinals_isCardinal; eauto.
Qed.

Lemma beth_djoin_isSupremum (I : Type@{Set_u}) (ds : I -> Tree) (d : Tree)
  (CHAIN : forall i1, forall i2, ds i1 ≦ᵣ ds i2 \/ ds i2 ≦ᵣ ds i1)
  (GOODs : forall i, isCardinal (ds i))
  (GOOD : isCardinal d)
  : indexed_union I ds ≦ᵣ d <-> (forall i, ds i ≦ᵣ d).
Proof.
  eapply indexed_union_ofCardinals_isSupremum; eauto.
Qed.

Let beth_base_good
  : isCardinal beth0.
Proof.
  exact aleph0_isCardinal.
Qed.

Let beth_next_good (d : Tree)
  (GOOD : isCardinal d)
  : isCardinal (bethS d).
Proof.
  eapply bethS_isCardinal.
Qed.

Lemma beth_next_extensive (d : Tree)
  (GOOD : isCardinal d)
  : d ≦ᵣ bethS d.
Proof.
  eapply bethS_ge. eapply isCardinal_isOrdinal. exact GOOD.
Qed.

Lemma beth_next_congruence d d'
  (GOOD : isCardinal d)
  (GOOD' : isCardinal d')
  (EQ : d =ᵣ d')
  : bethS d =ᵣ bethS d'.
Proof.
  destruct EQ as [LE GE]. split; eapply bethS_le_bethS_intro; eauto using isCardinal_isOrdinal.
Qed.

#[local] Hint Resolve beth_djoin_isSupremum beth_next_extensive beth_next_congruence : aczel_hints.

Definition beth : Tree -> Tree :=
  Ord.orec beth0 bethS.

#[local] Notation rank_trichotomy := (O.wlt_trichotomous (classic := classic) (WOSET := rLt_isWellOrdering)).

#[local] Infix "⊑" := rLe.

#[local] Infix "≡" := rEq.

#[local] Notation good := isCardinal.

#[local] Notation rec := beth.

#[local] Notation dbase := beth0.

#[local] Notation next := bethS.

#[local] Notation djoin := indexed_union.

#[local] Notation djoin_good := beth_djoin_good.

#[local] Notation djoin_supremum := beth_djoin_isSupremum.

#[local] Notation next_good := beth_next_good.

#[local] Notation next_extensive := beth_next_extensive.

#[local] Notation next_congruence := beth_next_congruence.

Let beth_djoin_upperbound (I : Type@{Set_u}) (ds : I -> Tree)
  (CHAIN : forall i1, forall i2, ds i1 ⊑ ds i2 \/ ds i2 ⊑ ds i1)
  (GOODs : forall i, good (ds i))
  : forall i, ds i ⊑ djoin I ds.
Proof.
  i. eapply djoin_supremum; eauto with *.
Qed.

#[local] Hint Resolve bethS_isCardinal : core.

Theorem beth_rec_spec (o : Tree)
  : ⟪ mono_rec : forall o', o' ≦ᵣ o -> rec o' ⊑ rec o ⟫ /\ ⟪ base_rec : dbase ⊑ rec o ⟫ /\ ⟪ next_rec : forall o', o' <ᵣ o -> next (rec o') ⊑ rec o ⟫ /\ ⟪ good_rec : good (rec o) ⟫.
Proof.
  rename o into t. pose proof (rLt_wf t) as H_ACC. induction H_ACC as [t _ IH]. destruct t as [cs ts]; simpl.
  assert (H_chain : forall cs' : Type@{Set_u}, forall ts' : cs' -> Tree, forall LE : forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c, forall c1 : cs', forall c2 : cs', next (rec (ts' c1)) ⊑ next (rec (ts' c2)) \/ next (rec (ts' c2)) ⊑ next (rec (ts' c1))).
  { ii.
    assert (ts' c1 <ᵣ mkNode cs ts /\ ts' c2 <ᵣ mkNode cs ts) as [helper1 helper2].
    { split; econs; eapply LE. }
    pose proof (rank_trichotomy (ts' c1) (ts' c2)) as [EQ | [LT | GT]].
    - hexploit (next_congruence (rec (ts' c1)) (rec (ts' c2))).
      + eapply IH; eauto.
      + eapply IH; eauto.
      + destruct EQ as [LE1 LE2]. split; eapply IH; eauto.
      + intros H_deq. left. exact (proj1 H_deq).
    - left. transitivity (rec (ts' c2)); eauto.
      + eapply IH; eauto.
      + eapply next_extensive. eapply IH; eauto.
    - right. transitivity (rec (ts' c1)); eauto.
      + eapply IH; eauto.
      + eapply next_extensive. eapply IH; eauto.
  }
  assert (H_next_good : forall cs' : Type@{Set_u}, forall ts' : cs' -> Tree,forall LE : forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c, forall c', good (next (rec (ts' c')))).
  { ii. eapply next_good. eapply IH; eauto. econs. eapply LE. }
  set (fun cs' : Type@{Set_u} => fun ts' : cs' -> Tree => fun b : bool => if b then dbase else djoin cs' (fun c' => next (rec (ts' c')))) as f.
  assert (claim1 : forall b1 : bool, forall b2 : bool, forall cs' : Type@{Set_u}, forall ts' : cs' -> Tree, forall LE : forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c, f cs' ts' b1 ⊑ f cs' ts' b2 \/ f cs' ts' b2 ⊑ f cs' ts' b1).
  { ii.
    assert (helper1 : forall c' : cs', ts' c' <ᵣ mkNode cs ts).
    { i; econs; eapply LE. }
    assert (GOOD1 : forall i : cs', isCardinal (next (rec (ts' i)))).
    { i. eapply next_good. exploit (IH (ts' i)); eauto. i; des; eauto. }
    assert (helper2 : dbase ⊑ djoin cs' (fun c' => next (rec (ts' c'))) \/ djoin cs' (fun c' => next (rec (ts' c'))) ⊑ dbase).
    { pose proof (classic (inhabited cs')) as [YES | NO]; [left | right].
      - destruct YES as [c']. exploit (IH (ts' c')); auto. i; des.
        enough (next (rec (ts' c')) ⊑ djoin cs' (fun i : cs' => next (rec (ts' i)))).
        { transitivity (next (rec (ts' c'))); auto with *. transitivity (rec (ts' c')); eauto with *. }
        eapply beth_djoin_upperbound with (ds := fun c' : cs' => next (rec (ts' c'))); eauto.
      - enough (forall i : cs', next (rec (ts' i)) ⊑ dbase) by now eapply djoin_supremum; eauto.
        intros c'. contradiction NO. econs. exact c'.
    }
    destruct b1, b2; simpl in *; eauto with *; tauto.
  }
  assert (claim2 : forall b : bool, forall cs' : Type@{Set_u}, forall ts' : cs' -> Tree, forall LE : forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c, good (f cs' ts' b)).
  { ii. destruct b; simpl; eauto. }
  set (djoin bool (f cs ts)) as x.
  assert (claim3 : good x).
  { eapply djoin_good; auto.
    - ii; eapply claim1; eauto with *.
    - ii; eapply claim2; eauto with *.
  }
  assert (claim4 : dbase ⊑ x).
  { eapply beth_djoin_upperbound with (ds := f cs ts) (i := true); auto.
    - ii; eapply claim1; eauto with *.
    - ii; eapply claim2; eauto with *.
  }
  assert (claim5 : forall cs' : Type@{Set_u}, forall ts' : cs' -> Tree, forall H_rLt : forall c, ts' c <ᵣ mkNode cs ts, forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c).
  { ii. pose proof (H_rLt c') as [[c H_rLe]]. simpl in *. exists c. exact H_rLe. }
  assert (claim6 : forall o : Tree, forall LE : o ≦ᵣ mkNode cs ts, rec o ⊑ x).
  { intros [cs' ts'] [H_rLt]. simpl in *. unfold Ord.join.
    change (fun b : bool => if b then dbase else djoin cs' (fun c : cs' => next (rec (ts' c)))) with (f cs' ts').
    rewrite -> djoin_supremum; eauto. destruct i; eauto. simpl. eapply djoin_supremum; i; eauto.
    { unfold x. transitivity (djoin cs' (fun c' => next (rec (ts' c')))); eauto.
      - eapply beth_djoin_upperbound with (ds := fun c' : cs' => next (rec (ts' c'))); eauto.
      - eapply djoin_supremum; eauto. intros c'. pose proof (H_rLt c') as [[c H_rLe]]; simpl in *.
        rewrite InducedOrdinal.rLe_iff_rLt_or_rEq in H_rLe. destruct H_rLe as [H_LT | H_EQ].
        + transitivity (next (rec (ts c))); auto.
          { transitivity (rec (ts c)); auto.
            - eapply IH; eauto with *.
            - eapply next_extensive; auto. eapply IH; eauto with *.
          }
          { unfold f. transitivity (djoin cs (fun i : cs => next (rec (ts i)))); auto.
            - eapply beth_djoin_upperbound with (ds := fun c : cs => next (rec (ts c))); eauto with *.
            - eapply beth_djoin_upperbound with (ds := f cs ts) (i := false); eauto with *.
          }
        + transitivity (next (rec (ts c))); auto.
          { eapply next_congruence.
            - eapply IH; eauto with *.
            - eapply IH; eauto with *.
            - destruct H_EQ as [H_LE1 H_LE2]. split; eapply IH; eauto with *.
          }
          { unfold f. transitivity (djoin cs (fun i : cs => next (rec (ts i)))); auto.
            - eapply beth_djoin_upperbound with (ds := fun c : cs => next (rec (ts c))); eauto with *.
            - eapply beth_djoin_upperbound with (ds := f cs ts) (i := false); eauto with *.
          }
    }
  }
  splits; auto. intros o H_rLt.
  pose proof (classic (exists o' : Tree, o <ᵣ o' /\ o' <ᵣ mkNode cs ts)) as [YES | NO].
  - unfold Ord.join. des. hexploit (IH o'); auto. i; des.
    transitivity (rec o'); eauto.
    eapply claim6. eapply rLt_implies_rLe; eauto.
  - assert (exists c, ts c =ᵣ o) as [c H_rEq].
    { eapply NNPP. intros H_contra. rewrite InducedOrdinal.rLt_iff_not_rGe in H_rLt.
      contradiction H_rLt. econs. simpl. intros c.
      pose proof (rank_trichotomy (ts c) o) as [H_EQ | [H_LT | H_GT]]; eauto.
      - contradiction H_contra; eauto.
      - contradiction NO; eauto with *.
    }
    assert (rec o ≡ rec (ts c)) as claim7.
    { destruct H_rEq; split; eapply IH; eauto with *. }
    unfold Ord.join.
    transitivity (next (rec (ts c))); auto.
    { eapply next_congruence.
      - eapply IH; eauto with *.
      - eapply IH; eauto with *.
      - now symmetry.
    }
    { transitivity (djoin cs (fun i : cs => next (rec (ts i)))); auto.
      - eapply beth_djoin_upperbound with (ds := fun c : cs => next (rec (ts c))); eauto with *.
      - eapply beth_djoin_upperbound with (ds := f cs ts) (i := false); eauto with *.
    }
Qed.

Lemma beth_le_rec t t'
  (H_rLe : t ⊑ t')
  : rec t ⊑ rec t'.
Proof.
  eapply beth_rec_spec; eauto.
Qed.

Lemma beth_eq_rec t t'
  (H_rEq : t ≡ t')
  : rec t ≡ rec t'.
Proof.
  destruct H_rEq; split; eapply beth_rec_spec; eauto.
Qed.

Lemma beth_lt_rec t t'
  (H_rLt : t <ᵣ t')
  : next (rec t) ⊑ rec t'.
Proof.
  eapply beth_rec_spec; eauto.
Qed.

Lemma beth_rec_le_base (t : Tree)
  : dbase ⊑ rec t.
Proof.
  eapply beth_rec_spec; eauto.
Qed.

Lemma beth_good_rec (t : Tree)
  : good (rec t).
Proof.
  eapply beth_rec_spec; eauto.
Qed.

#[local] Hint Resolve beth_le_rec beth_eq_rec beth_lt_rec : aczel_hints.

#[local] Hint Resolve beth_rec_le_base beth_good_rec : aczel_hints.

Lemma beth_rec_next_dle t t'
  (H_rLe : t ≦ᵣ t')
  : next (rec t) ⊑ next (rec t').
Proof.
  rewrite InducedOrdinal.rLe_iff_rLt_or_rEq in H_rLe.
  destruct H_rLe as [H_rLt | H_rEq].
  - transitivity (rec t'); eauto with *.
  - eapply next_congruence; eauto with *.
Qed.

Lemma beth_rec_chain t t'
  : rec t ⊑ rec t' \/ rec t' ⊑ rec t.
Proof.
  pose proof (InducedOrdinal.rLe_total t t') as [H | H]; [left | right]; eauto with *.
Qed.

Lemma beth_rec_next_chain t t'
  : next (rec t) ⊑ next (rec t') \/ next (rec t') ⊑ next (rec t).
Proof.
  pose proof (InducedOrdinal.rLe_total t t') as [H | H]; [left | right]; eapply beth_rec_next_dle; eauto.
Qed.

Lemma beth_good_next_rec (cs : Type@{Set_u}) (ts : cs -> Tree)
  : forall c : cs, good (next (rec (ts c))).
Proof.
  eauto.
Qed.

#[local] Hint Resolve beth_rec_next_dle beth_rec_chain : aczel_hints.

#[local] Hint Resolve beth_rec_next_chain beth_good_next_rec : core.

Let dbase_next_rec alpha
  : dbase ⊑ next (rec alpha).
Proof.
  transitivity (rec alpha); eauto with *.
Qed.

Let j (cs : Type@{Set_u}) (ts : cs -> Tree) (b : bool) : Tree :=
  if b then dbase else djoin cs (fun c => next (rec (ts c))).

Lemma beth_j_chain (cs : Type@{Set_u}) (ts : cs -> Tree) (b : bool) (b' : bool)
  : j cs ts b ⊑ j cs ts b' \/ j cs ts b' ⊑ j cs ts b.
Proof.
  assert (dbase ⊑ djoin cs (fun c => next (rec (ts c))) \/ djoin cs (fun c => next (rec (ts c))) ⊑ dbase) as claim1.
  { pose proof (classic (inhabited cs)) as [YES | NO]; [left | right].
    - destruct YES as [c]. transitivity (next (rec (ts c))); eauto.
      eapply beth_djoin_upperbound with (ds := fun c : cs => next (rec (ts c))); eauto with *.
    - eapply djoin_supremum; eauto.
      intros c. contradiction NO. econs. exact c.
  }
  destruct b, b'; simpl; eauto with *; try tauto.
Qed.

Lemma beth_good_j (cs : Type@{Set_u}) (ts : cs -> Tree)
  : forall b, good (j cs ts b).
Proof.
  intros [ | ]; simpl; eauto with *.
Qed.

#[local] Hint Resolve beth_j_chain beth_good_j : core.

Lemma beth_rec_zero (o : Tree)
  (ZERO : o ≡ empty)
  : rec o ≡ dbase.
Proof.
  transitivity (rec empty); eauto with *. change (djoin bool (j Empty_set (Empty_set_rect _)) ≡ dbase). split.
  - eapply djoin_supremum; auto. unfold j. intros [ | ]; auto with *. eapply djoin_supremum; auto; intros [].
  - eapply beth_djoin_upperbound with (ds := j Empty_set (Empty_set_rect _)) (i := true); eauto.
Qed.

Lemma beth_rec_succ (o : Tree) (alpha : Tree)
  (SUCC : o ≡ succ alpha)
  : rec o ≡ next (rec alpha).
Proof.
  transitivity (rec (succ alpha)); eauto with *.
  change (djoin bool (j { b : bool & children (if b then alpha else singleton alpha) } (fun c => childnodes (if projT1 c then alpha else singleton alpha) (projT2 c))) ≡ next (rec alpha)). split.
  - eapply djoin_supremum; auto. unfold j. intros [ | ]; simpl; auto.
    eapply djoin_supremum; auto. intros [[ | ] c]; simpl; eapply beth_rec_next_dle.
    + eapply rLt_implies_rLe. econs. exists c. reflexivity.
    + simpl in c. destruct c as [ | ]; reflexivity.
  - refine (let c : { b : bool & children (if b then alpha else singleton alpha) } := @existT _ _ false true in _).
    transitivity (djoin { b : bool & children (if b then alpha else singleton alpha) } (fun c => next (rec (childnodes (if projT1 c then alpha else singleton alpha) (projT2 c))))); auto.
    + eapply beth_djoin_upperbound with (ds := fun c : { b : bool & children (if b then alpha else singleton alpha) } => next (rec (childnodes (if projT1 c then alpha else singleton alpha) (projT2 c)))) (i := c); eauto with *.
    + eapply beth_djoin_upperbound with (ds := j { b : bool & children (if b then alpha else singleton alpha) } (fun c => childnodes (if projT1 c then alpha else singleton alpha) (projT2 c))) (i := false); eauto.
Qed.

Let djoin_rec_good (cs : Type@{Set_u}) (ts : cs -> Tree)
  : good (djoin cs (fun i : cs => rec (ts i))).
Proof.
  eauto with *.
Qed.

Let rec_good (cs : Type@{Set_u}) (ts : cs -> Tree)
  : forall c : cs, good (rec (ts c)).
Proof.
  eauto with *.
Qed.

Let dbase_le_rec (cs : Type@{Set_u}) (ts : cs -> Tree)
  : forall c : cs, dbase ⊑ rec (ts c).
Proof.
  eauto with *.
Qed.

Lemma beth_rec_lim' (o : Tree) (cs : Type@{Set_u}) (ts : cs -> Tree)
  (APPROX : forall c1 : cs, exists c2 : cs, ts c1 <ᵣ ts c2)
  (INHABITED : inhabited cs)
  (LIM' : o ≡ indexed_union cs ts)
  : rec o ≡ djoin cs (fun c : cs => rec (ts c)).
Proof.
  destruct INHABITED as [c]. destruct o as [cs' ts']; simpl. change (djoin bool (j cs' ts') ≡ djoin cs (fun i : cs => rec (ts i))). split.
  - eapply djoin_supremum; auto. intros [ | ]; simpl.
    + transitivity (rec (ts c)); auto. eapply beth_djoin_upperbound with (ds := fun i : cs => rec (ts i)) (i := c); eauto with *.
    + eapply djoin_supremum; auto. clear c. intros c'. destruct LIM' as [LE1 LE2]; simpl in *. destruct LE1 as [H_rLt]; simpl in *.
      pose proof (H_rLt c') as [[c H_rLe]]. simpl in *. transitivity (rec (ts (projT1 c))).
      * eapply beth_lt_rec. econs. exists (projT2 c). exact H_rLe.
      * eapply beth_djoin_upperbound with (ds := fun i : cs => rec (ts i)) (i := projT1 c); eauto with *.
  - eapply djoin_supremum; auto with *. clear c. intros c. transitivity (djoin cs (fun c => rec (ts c))).
    + eapply beth_djoin_upperbound with (ds := fun i : cs => rec (ts i)) (i := c); eauto with *.
    + clear c. eapply djoin_supremum; auto with *. intros c1. simpl in *.
      pose proof (APPROX c1) as [c2 H_rLt]. destruct H_rLt as [[c H_rLe]]. destruct LIM' as [LE1 LE2]. destruct LE2 as [LE2]. simpl in *.
      pose proof (LE2 (@existT cs (fun i : cs => children (ts i)) c2 c)) as claim1. simpl in *.
      destruct claim1 as [[c' H_rLe']]. simpl in *.
      transitivity (rec (ts' c')).
      { eapply beth_le_rec. transitivity (childnodes (ts c2) c); auto. }
      { transitivity (djoin cs' (fun i : cs' => next (rec (ts' i)))); auto.
        - transitivity (next (rec (ts' c'))); auto with *.
          eapply beth_djoin_upperbound with (ds := fun i : cs' => next (rec (ts' i))) (i := c'); eauto with *.
        - eapply beth_djoin_upperbound with (ds := j cs' ts') (i := false); eauto with *.
      }
Qed.

Lemma beth_isCardinal (o : Tree)
  : isCardinal (beth o).
Proof.
  exact (beth_good_rec o).
Qed.

Lemma beth_isOrdinal (o : Tree)
  : isOrdinal (beth o).
Proof.
  eapply isCardinal_isOrdinal. eapply beth_isCardinal.
Qed.

Lemma beth_zero (o : Tree)
  (ZERO : o =ᵣ empty)
  : beth o =ᵣ beth0.
Proof.
  exact (beth_rec_zero o ZERO).
Qed.

Lemma beth_succ (o : Tree) (alpha : Tree)
  (SUCC : o =ᵣ succ alpha)
  : beth o =ᵣ bethS (beth alpha).
Proof.
  exact (beth_rec_succ o alpha SUCC).
Qed.

Lemma beth_lim' (o : Tree) (I : Type@{Set_u}) (alpha : I -> Tree)
  (APPROX : forall i1 : I, exists i2 : I, alpha i1 <ᵣ alpha i2)
  (INHABITED : inhabited I)
  (LIMIT : o =ᵣ indexed_union I alpha)
  : beth o =ᵣ indexed_union I (fun i => beth (alpha i)).
Proof.
  exact (beth_rec_lim' o I alpha APPROX INHABITED LIMIT).
Qed.

Lemma beth_le_beth_intro o o'
  (LE : o ≦ᵣ o')
  : beth o ≦ᵣ beth o'.
Proof.
  exact (beth_le_rec o o' LE).
Qed.

Lemma beth_lt_beth_intro o o'
  (LT : o <ᵣ o')
  : beth o <ᵣ beth o'.
Proof.
  eapply rLt_rLe_rLt with (y := bethS (beth o)).
  - eapply bethS_gt. eapply beth_isOrdinal.
  - eapply beth_lt_rec. exact LT.
Qed.

Lemma beth0_le_beth (o : Tree)
  : beth0 ≦ᵣ beth o.
Proof.
  exact (beth_rec_le_base o).
Qed.

Theorem beth_expand
  : forall o : Tree, o ≦ᵣ beth o.
Proof.
  eapply member_rect. intros o IH. eapply rLe_intro_var1. intros x x_in. eapply rLe_rLt_rLt.
  - eapply IH. exact x_in.
  - eapply rLt_rLe_rLt.
    + eapply bethS_gt. eapply beth_isOrdinal.
    + eapply beth_lt_rec. eapply member_implies_rLt. exact x_in.
Qed.

Theorem beth_hasCardinality (o : Tree)
  : Cardinality.mk (children (beth o)) (children_isSetoid (beth o)) `hasCardinality` beth o.
Proof.
  eapply isCardinal_elim. eapply beth_isCardinal.
Qed.

Theorem aleph_le_beth
  : forall o : Tree, aleph o ≦ᵣ beth o.
Proof.
  induction o as [cs ts IH]; simpl. eapply rLe_intro_var1. intros x x_in.
  change (x \in indexed_union bool (fun b => if b then aleph0 else djoin cs (fun c : cs => alephS (aleph (ts c))))) in x_in.
  change (x <ᵣ indexed_union bool (fun b => if b then beth0 else djoin cs (fun c : cs => bethS (beth (ts c))))).
  rewrite indexed_union_spec in x_in. destruct x_in as [[ | ] x_in].
  - eapply member_implies_rLt. rewrite indexed_union_spec. exists true. exact x_in.
  - rewrite indexed_union_spec in x_in. destruct x_in as [c x_in]. eapply member_implies_rLt.
    rewrite indexed_union_spec. exists false. rewrite indexed_union_spec. exists c.
    revert x x_in. change (alephS (aleph (ts c)) \subseteq bethS (beth (ts c))).
    eapply Ordinal1.Ordinal_rLe_Ordinal_elim; eauto.
    { eapply alephS_isOrdinal. }
    { eapply bethS_isOrdinal. }
    eapply rLe_trans.
    { eapply alephS_le_bethS. }
    eapply bethS_le_bethS_intro.
    { eapply aleph_isOrdinal. }
    { eapply beth_isOrdinal. }
    exact (IH c).
Qed.

End BETH.

Theorem CantorSchröderBernstein `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t) (lambda : Cardinality.t)
  (LE1 : kappa =< lambda)
  (LE2 : lambda =< kappa)
  : exists f : kappa.(Cardinality.carrier) -> lambda.(Cardinality.carrier), ⟪ f_inj : forall x1, forall x2, x1 == x2 <-> f x1 == f x2 ⟫ /\ ⟪ f_surj : forall y, exists x, y == f x ⟫.
Proof.
  assert (H_EQ : kappa == lambda).
  { destruct LE1 as [f f_cong f_inj], LE2 as [g g_cong g_inj]. now exists f g. }
  assert (H_tree : Cardinality.toTree kappa =ᵣ Cardinality.toTree lambda).
  { now rewrite <- Cardinality_eq_iff. }
  pose proof (hasCardinality_intro kappa) as [(Rk & Rk_wf & Rk_total & Rk_Transitive & Rk_eqPropCompatible2 & Hk) _].
  pose proof (hasCardinality_intro lambda) as [(Rl & Rl_wf & Rl_total & Rl_Transitive & Rl_eqPropCompatible2 & Hl) _].
  set (WPOSET1 := {| wltProp := Rk; wltProp_well_founded := Rk_wf; wltProp_Transitive := Rk_Transitive; |}).
  set (WPOSET2 := {| wltProp := Rl; wltProp_well_founded := Rl_wf; wltProp_Transitive := Rl_Transitive; |}).
  set (WOSET1 := @O.WellfoundedToset_isWoset classic kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid) WPOSET1 Rk_eqPropCompatible2 Rk_total).
  set (WOSET2 := @O.WellfoundedToset_isWoset classic lambda.(Cardinality.carrier) lambda.(Cardinality.carrier_isSetoid) WPOSET2 Rl_eqPropCompatible2 Rl_total).
  assert (H_fromWfSet : @fromWfSet kappa.(Cardinality.carrier) Rk Rk_wf == @fromWfSet lambda.(Cardinality.carrier) Rl Rl_wf).
  { eapply Ordinal1.Ordinal_rEq_Ordinal_elim.
    - change (isOrdinal (@FromOrderType _ _ WOSET1)). eapply FromOrderType_isOrdinal.
    - change (isOrdinal (@FromOrderType _ _ WOSET2)). eapply FromOrderType_isOrdinal.
    - rewrite -> Hl, -> Hk. exact H_tree.
  }
  destruct H_fromWfSet as [H_left H_right].
  exploit (Axiom_of_Choice kappa.(Cardinality.carrier) (fun _ => lambda.(Cardinality.carrier)) (fun x y => @fromWf _ Rl Rl_wf y == @fromWf _ Rk Rk_wf x)).
  { intro x. pose proof (H_left x) as [y Hy]. exists y. eauto with *. }
  intros [f Hf].
  exploit (Axiom_of_Choice lambda.(Cardinality.carrier) (fun _ => kappa.(Cardinality.carrier)) (fun y x => @fromWf _ Rk Rk_wf x == @fromWf _ Rl Rl_wf y)).
  { intro y. pose proof (H_right y) as [x Hx]. exists x. eauto with *. }
  intros [g Hg].
  exists f. split.
  - intros x1 x2. split.
    + intros Hxx. rewrite <- fromOrderType_eq_fromOrderType_iff in Hxx.
      change (fromWf Rk Rk_wf x1 == fromWf Rk Rk_wf x2) in Hxx.
      do 2 rewrite <- Hf in Hxx. now rewrite <- fromOrderType_eq_fromOrderType_iff.
    + intros Hff. rewrite <- fromOrderType_eq_fromOrderType_iff in Hff.
      change (fromWf Rl Rl_wf (f x1) == fromWf Rl Rl_wf (f x2)) in Hff.
      do 2 rewrite -> Hf in Hff. now rewrite <- fromOrderType_eq_fromOrderType_iff.
  - intro y. exists (g y). rewrite <- fromOrderType_eq_fromOrderType_iff.
    change (fromWf Rl Rl_wf y == fromWf Rl Rl_wf (f (g y))).
    now rewrite -> Hf, -> Hg.
Qed.

Theorem makeOrdinalIndexedSequence `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (X : Type@{Set_u}) (SETOID : isSetoid X)
  : { c : Ord.t | Cardinality.mk X SETOID `hasCardinality` c /\ exists f : children c -> X, ⟪ f_inj : forall x1, forall x2, eqProp (isSetoid := children_isSetoid c) x1 x2 <-> eqProp (isSetoid := SETOID) (f x1) (f x2) ⟫ /\ ⟪ f_surj : forall y, exists x, eqProp (isSetoid := SETOID) y (f x) ⟫ }.
Proof.
  exists (Cardinality.toTree (Cardinality.mk X SETOID)). split.
  { eapply hasCardinality_intro. }
  set (kappa := Cardinality.mk X SETOID).
  set (lambda := card (Cardinality.toTree kappa)).
  assert (kappa == lambda) as [h1 h2 h1_cong h2_cong h1_inj h2_inj].
  { unfold kappa, lambda. exploit (isCardinal_elim (Cardinality.toTree kappa)); eauto; intros HCARD. rewrite <- Cardinality_toTree_eq_iff in HCARD. rewrite Cardinality_eq_iff. rewrite HCARD. reflexivity. }
  assert (claim2 : kappa =< lambda) by now exists h1.
  assert (claim3 : lambda =< kappa) by now exists h2.
  now eapply CantorSchröderBernstein with (kappa := card (Cardinality.toTree kappa)) (lambda := Cardinality.mk X SETOID).
Qed.

End CARDINALITY.

End Cardinal1.

Module Cardinal2.

Section CARDINALITY.

#[local] Infix "\in" := E.In.

#[local] Infix "\subseteq" := E.isSubsetOf.

Lemma sig_eq_from_proj1 {A : Type@{Set_u}} {P : A -> Prop} (x : @sig A P) (y : @sig A P)
  (EQ : proj1_sig x = proj1_sig y)
  : x = y.
Proof.
  destruct x as [x Hx], y as [y Hy]. simpl in EQ. subst y. rewrite proof_irrelevance with (p1 := Hx) (p2 := Hy). reflexivity.
Qed.

Lemma Cardinality_ofType_sig_le (A : Type@{Set_u}) (P : A -> Prop)
  : Cardinality.mk { a : A | P a } mkSetoid_from_eq =< Cardinality.ofType A.
Proof.
  exists (@proj1_sig A P).
  - intros x y EQ. change (x = y) in EQ. now subst y.
  - intros x y EQ. change (proj1_sig x = proj1_sig y) in EQ. change (x = y). now eapply sig_eq_from_proj1.
Qed.

Lemma Cardinality_ofType_le_ofType (A : Type@{Set_u}) (B : Type@{Set_u}) (f : A -> B)
  (f_inj : forall x1 : A, forall x2 : A, f x1 = f x2 -> x1 = x2)
  : Cardinality.ofType A =< Cardinality.ofType B.
Proof.
  exists f.
  - intros x y EQ. change (x = y) in EQ. now subst y.
  - intros x y EQ. change (f x = f y) in EQ. change (x = y). now eapply f_inj.
Qed.

Lemma Cardinality_ofType_image_le `{Axms : ClassicalAxioms (b_AC := true)} (A : Type@{Set_u}) (B : Type@{Set_u}) (P : B -> Prop) (f : A -> B)
  (IMAGE : forall y : B, P y <-> (exists x, y = f x))
  : Cardinality.mk (@sig B P) mkSetoid_from_eq =< Cardinality.ofType A.
Proof.
  assert (Hchoice : forall y : { b : B | P b }, exists x : A, proj1_sig y = f x).
  { intros [y Hy]. exact (proj1 (IMAGE y) Hy). }
  pose proof (Axiom_of_Choice { b : B | P b } (fun _ : { b : B | P b } => A) (fun y : { b : B | P b } => fun x : A => proj1_sig y = f x) Hchoice) as [pick PICK].
  exists pick.
  - intros x y EQ. change (x = y) in EQ. now subst y.
  - intros y1 y2 EQ. change (pick y1 = pick y2) in EQ. change (y1 = y2). eapply sig_eq_from_proj1. do 2 rewrite PICK. now rewrite EQ.
Qed.

Lemma Cardinality_ofType_image_lt `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (A : Type@{Set_u}) (B : Type@{Set_u}) (P : B -> Prop) (f : A -> B) (kappa : Cardinality.t)
  (IMAGE : forall y : B, P y <-> (exists x, y = f x))
  (LT : Cardinality.ofType A ≨ kappa)
  : Cardinality.mk (@sig B P) mkSetoid_from_eq ≨ kappa.
Proof.
  eapply Cardinal1.Cardinality_le_lt_lt.
  - eapply Cardinality_ofType_image_le. exact IMAGE.
  - exact LT.
Qed.

Definition isFiniteEnsemble {D : Type@{Set_u}} (X : ensemble D) : Prop :=
  exists xs : list D, forall x : D, x \in X <-> L.In x xs.

Definition ensemble_card {D : Type@{Set_u}} (X : ensemble D) : Cardinality.t :=
  Cardinality.mk { x : D | x \in X } mkSetoid_from_eq.

Lemma ensemble_card_image_le `{Axms : ClassicalAxioms (b_AC := true)} {D : Type@{Set_u}} (A : Type@{Set_u}) (Y : ensemble D) (f : A -> D)
  (IMAGE : forall y : D, y \in Y <-> (exists x : A, y = f x))
  : ensemble_card Y =< Cardinality.ofType A.
Proof.
  unfold ensemble_card. eapply Cardinality_ofType_image_le. exact IMAGE.
Qed.

Lemma ensemble_card_image_lt `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} {D : Type@{Set_u}} (A : Type@{Set_u}) (Y : ensemble D) (f : A -> D) (kappa : Cardinality.t)
  (IMAGE : forall y : D, y \in Y <-> (exists x : A, y = f x))
  (LT : Cardinality.ofType A ≨ kappa)
  : ensemble_card Y ≨ kappa.
Proof.
  unfold ensemble_card. eapply Cardinality_ofType_image_lt.
  - exact IMAGE.
  - exact LT.
Qed.

Lemma ensemble_card_subset_le {D : Type@{Set_u}} (X : ensemble D) (Y : ensemble D)
  (SUB : X \subseteq Y)
  : ensemble_card X =< ensemble_card Y.
Proof.
  exists (fun x : (ensemble_card X).(Cardinality.carrier) => @exist D (fun y : D => y \in Y) (proj1_sig x) (SUB (proj1_sig x) (proj2_sig x))).
  - intros x y EQ. change (x = y) in EQ. subst y. reflexivity.
  - intros [x Hx] [y Hy] EQ. change (@exist D (fun z : D => z \in Y) x (SUB x Hx) = @exist D (fun z : D => z \in Y) y (SUB y Hy)) in EQ.
    apply exist_eq_iff in EQ. subst y. change (@exist D (fun z : D => z \in X) x Hx = @exist D (fun z : D => z \in X) x Hy). apply exist_eq_iff. reflexivity.
Qed.

Lemma finite_if_card_le_finite `{Axms : ClassicalAxioms (b_AC := true)} {D : Type@{Set_u}} (X : ensemble D) (Y : ensemble D)
  (X_INHABITED : exists x : D, x \in X)
  (LE : ensemble_card X =< ensemble_card Y)
  (Y_FIN : isFiniteEnsemble Y)
  : isFiniteEnsemble X.
Proof.
  destruct X_INHABITED as [x0 x0_in].
  destruct LE as [f f_cong f_inj].
  destruct Y_FIN as [ys Y_SPEC].
  assert (Hchoice : forall y : D, exists x : D, x \in X /\ (exists Hx : x \in X, proj1_sig (f (@exist D (fun z : D => z \in X) x Hx)) = y) \/ x = x0 /\ ~ exists x' : D, exists Hx' : x' \in X, proj1_sig (f (@exist D (fun z : D => z \in X) x' Hx')) = y).
  { intro y. pose proof (classic (exists x : D, exists Hx : x \in X, proj1_sig (f (@exist D (fun z : D => z \in X) x Hx)) = y)) as [(x & Hx & Hx_eq) | Hnone].
    - exists x. left. split.
      + exact Hx.
      + exists Hx. exact Hx_eq.
    - exists x0. right. split; [reflexivity | exact Hnone].
  }
  pose proof (Axiom_of_Choice D (fun _ : D => D) (fun y : D => fun x : D => x \in X /\ (exists Hx : x \in X, proj1_sig (f (@exist D (fun z : D => z \in X) x Hx)) = y) \/ x = x0 /\ ~ exists x' : D, exists Hx' : x' \in X, proj1_sig (f (@exist D (fun z : D => z \in X) x' Hx')) = y) Hchoice) as [pick PICK].
  exists (L.map pick ys). intro x. split.
  - intro x_in. rewrite L.in_map_iff.
    pose (fx := f (@exist D (fun z : D => z \in X) x x_in)).
    exists (proj1_sig fx). split.
    + pose proof (PICK (proj1_sig fx)) as [(pick_in & Hpick & Hpick_eq) | (Hpick_eq & Hnone)].
      * assert (EQf : f (@exist D (fun z : D => z \in X) (pick (proj1_sig fx)) Hpick) == f (@exist D (fun z : D => z \in X) x x_in)).
        { change (f (@exist D (fun z : D => z \in X) (pick (proj1_sig fx)) Hpick) = fx). destruct (f (@exist D (fun z : D => z \in X) (pick (proj1_sig fx)) Hpick)) as [y0 Hy0]. destruct fx as [y1 Hy1]. simpl in Hpick_eq. subst y1. apply exist_eq_iff. reflexivity. }
        pose proof (f_inj _ _ EQf) as EQx. change (@exist D (fun z : D => z \in X) (pick (proj1_sig fx)) Hpick = @exist D (fun z : D => z \in X) x x_in) in EQx. exact (f_equal (@proj1_sig D (fun z : D => z \in X)) EQx).
      * contradiction Hnone. exists x, x_in. reflexivity.
    + exact (proj1 (Y_SPEC (proj1_sig fx)) (proj2_sig fx)).
  - intro x_in. rewrite L.in_map_iff in x_in. destruct x_in as (y & EQ & y_in). subst x.
    pose proof (PICK y) as [(pick_in & _) | (pick_eq & _)].
    + exact pick_in.
    + rewrite pick_eq. exact x0_in.
Qed.

Lemma finite_subset_card_lt `{Axms : ClassicalAxioms (b_AC := true)} {D : Type@{Set_u}} (X : ensemble D) (Y : ensemble D)
  (X_INHABITED : exists x : D, x \in X)
  (Y_SUB : Y \subseteq X)
  (Y_FIN : isFiniteEnsemble Y)
  (X_INF : ~ isFiniteEnsemble X)
  : ensemble_card Y ≨ ensemble_card X.
Proof.
  split.
  - eapply ensemble_card_subset_le. exact Y_SUB.
  - intros [f g f_cong g_cong f_inj g_inj].
    contradiction X_INF. eapply finite_if_card_le_finite with (Y := Y).
    + exact X_INHABITED.
    + exists g; eauto.
    + exact Y_FIN.
Qed.

Lemma Cardinality_ofType_countable_le_nat {A : Type@{Set_u}} `{COUNTABLE : isCountable A}
  : Cardinality.ofType A =< Cardinality.ofType nat.
Proof.
  eapply Cardinality_ofType_le_ofType with (f := @encode A COUNTABLE). intros x1 x2 EQ. exact (@encode_inj A COUNTABLE x1 x2 EQ).
Qed.

Lemma Cardinality_ofType_Fin_le_nat (n : nat)
  : Cardinality.ofType (Fin.t n) =< Cardinality.ofType nat.
Proof.
  eapply Cardinality_ofType_countable_le_nat.
Qed.

Lemma nat_lt_of_uncountable `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t)
  (UNCOUNTABLE : ~ kappa =< Cardinality.ofType nat)
  : Cardinality.ofType nat ≨ kappa.
Proof.
  pose proof (Cardinal1.Cardinality_le_total kappa (Cardinality.ofType nat)) as [LE | LE].
  - contradiction UNCOUNTABLE.
  - split.
    + exact LE.
    + intros EQ. contradiction UNCOUNTABLE. destruct EQ as [f g f_cong g_cong f_inj g_inj]. exists g; eauto.
Qed.

Lemma countable_lt_of_uncountable `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} {A : Type@{Set_u}} `{COUNTABLE : isCountable A} (kappa : Cardinality.t)
  (UNCOUNTABLE : ~ kappa =< Cardinality.ofType nat)
  : Cardinality.ofType A ≨ kappa.
Proof.
  eapply Cardinal1.Cardinality_le_lt_lt.
  - eapply Cardinality_ofType_countable_le_nat.
  - eapply nat_lt_of_uncountable. exact UNCOUNTABLE.
Qed.

Lemma finite_lt_of_uncountable `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t) (n : nat)
  (UNCOUNTABLE : ~ kappa =< Cardinality.ofType nat)
  : Cardinality.ofType (Fin.t n) ≨ kappa.
Proof.
  eapply Cardinal1.Cardinality_le_lt_lt.
  - eapply Cardinality_ofType_Fin_le_nat.
  - eapply nat_lt_of_uncountable. exact UNCOUNTABLE.
Qed.

Lemma Cardinality_ofType_sum_eq (A : Type@{Set_u}) (B : Type@{Set_u})
  : Cardinality.ofType (A + B) == Cardinality.add (Cardinality.ofType A) (Cardinality.ofType B).
Proof.
  exists (fun x : A + B => x) (fun x : A + B => x).
  - intros x y EQ. change (x = y) in EQ. subst y. destruct x as [x | y]; econs; reflexivity.
  - intros [x | y] [x' | y'] EQ; inv EQ.
    + change (@inl A B x = @inl A B x'). now f_equal.
    + change (@inr A B y = @inr A B y'). now f_equal.
  - intros [x | y] [x' | y'] EQ; inv EQ.
    + change (@inl A B x = @inl A B x'). now f_equal.
    + change (@inr A B y = @inr A B y'). now f_equal.
  - intros x y EQ. change (x = y) in EQ. now subst y.
Qed.

Lemma Cardinality_ofType_prod_eq (A : Type@{Set_u}) (B : Type@{Set_u})
  : Cardinality.ofType (A * B) == Cardinality.mul (Cardinality.ofType A) (Cardinality.ofType B).
Proof.
  exists (fun x : A * B => x) (fun x : A * B => x).
  - intros x y EQ. change (x = y) in EQ. subst y. destruct x as [x y]; split; reflexivity.
  - intros [x y] [x' y'] EQ. destruct EQ as [EQ1 EQ2]. change (x = x') in EQ1. change (y = y') in EQ2. change ((x, y) = (x', y')). now subst x' y'.
  - intros [x y] [x' y'] EQ. destruct EQ as [EQ1 EQ2]. change (x = x') in EQ1. change (y = y') in EQ2. change ((x, y) = (x', y')). now subst x' y'.
  - intros x y EQ. change (x = y) in EQ. now subst y.
Qed.

Lemma Cardinality_ofType_sum_le (A : Type@{Set_u}) (B : Type@{Set_u}) (C : Type@{Set_u})
  (LEA : Cardinality.ofType A =< Cardinality.ofType C)
  (LEB : Cardinality.ofType B =< Cardinality.ofType C)
  : Cardinality.ofType (A + B) =< Cardinality.mul (Cardinality.ofType bool) (Cardinality.ofType C).
Proof.
  pose proof (Cardinality_ofType_sum_eq A B) as EQ. rewrite EQ. now eapply Cardinal1.Cardinality_add_le.
Qed.

Lemma Cardinality_ofType_prod_le (A : Type@{Set_u}) (B : Type@{Set_u}) (C : Type@{Set_u}) (D : Type@{Set_u})
  (LEA : Cardinality.ofType A =< Cardinality.ofType C)
  (LEB : Cardinality.ofType B =< Cardinality.ofType D)
  : Cardinality.ofType (A * B) =< Cardinality.ofType (C * D).
Proof.
  pose proof (Cardinality_ofType_prod_eq A B) as EQ1. pose proof (Cardinality_ofType_prod_eq C D) as EQ2.
  rewrite EQ1, EQ2. now eapply Cardinal1.Cardinality_mul_le.
Qed.

Lemma Cardinality_ofType_prod_countable_le_nat {A : Type@{Set_u}} {B : Type@{Set_u}} `{COUNTABLE_A : isCountable A} `{COUNTABLE_B : isCountable B}
  : Cardinality.ofType (A * B) =< Cardinality.ofType nat.
Proof.
  eapply Cardinality_ofType_countable_le_nat.
Qed.

Lemma Cardinality_ofType_prod_countable_lt_of_uncountable `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} {A : Type@{Set_u}} {B : Type@{Set_u}} `{COUNTABLE_A : isCountable A} `{COUNTABLE_B : isCountable B} (kappa : Cardinality.t)
  (UNCOUNTABLE : ~ kappa =< Cardinality.ofType nat)
  : Cardinality.ofType (A * B) ≨ kappa.
Proof.
  eapply Cardinal1.Cardinality_le_lt_lt.
  - eapply Cardinality_ofType_prod_countable_le_nat.
  - eapply nat_lt_of_uncountable. exact UNCOUNTABLE.
Qed.

End CARDINALITY.

#[universes(template)]
Inductive rose {A : Type} : Type :=
  | leaf (x : A)
  | node (ts : list (@rose A)).

#[global] Arguments rose : clear implicits.

Fixpoint rose_map {A : Type} {B : Type} (f : A -> B) (t : rose A) {struct t} : rose B :=
  match t with
  | leaf x => leaf (f x)
  | node ts => node (map (rose_map f) ts)
  end.

Fixpoint eval_rose {A : Type} {B : Type} (merge : list B -> B) (seed : A -> B) (t : rose A) {struct t} : B :=
  match t with
  | leaf x => seed x
  | node ts => merge (map (eval_rose merge seed) ts)
  end.

Section LIST_ROSE_BOUND.

Fixpoint encode_list {A : Type} (enc : A -> nat) (xs : list A) : nat :=
  match xs with
  | [] => O
  | x :: xs => S (cpInv (enc x) (encode_list enc xs))
  end.

Lemma cpInv_ge_r (x : nat) (y : nat)
  : y <= cpInv x y.
Proof.
  unfold cpInv. enough (0 <= sum_from_0_to (x + y)) by lia. induction (x + y); simpl; lia.
Qed.

Fixpoint decode_list_fuel {A : Type} (dec : nat -> option A) (fuel : nat) (n : nat) : option (list A) :=
  match fuel with
  | O => None
  | S fuel' =>
    match n with
    | O => Some []
    | S n' =>
      let '(n_x, n_xs) := cp n' in
      match dec n_x, decode_list_fuel dec fuel' n_xs with
      | Some x, Some xs => Some (x :: xs)
      | _, _ => None
      end
    end
  end.

Definition decode_list {A : Type} (dec : nat -> option A) (n : nat) : option (list A) :=
  decode_list_fuel dec (S n) n.

Lemma decode_encode_list_fuel {A : Type} (enc : A -> nat) (dec : nat -> option A)
  (DEC_ENC : forall x : A, dec (enc x) = Some x)
  : forall xs : list A, forall fuel : nat, encode_list enc xs < fuel -> decode_list_fuel dec fuel (encode_list enc xs) = Some xs.
Proof.
  induction xs as [ | x xs IH]; intros [ | fuel] FUEL; simpl in *; try lia.
  - reflexivity.
  - rewrite cpInv_rightInv. simpl. rewrite DEC_ENC. assert (TAIL : decode_list_fuel dec fuel (encode_list enc xs) = Some xs) by (eapply IH; pose proof (cpInv_ge_r (enc x) (encode_list enc xs)) as LE; lia). now rewrite TAIL.
Qed.

Lemma decode_encode_list {A : Type} (enc : A -> nat) (dec : nat -> option A)
  (DEC_ENC : forall x : A, dec (enc x) = Some x)
  : forall xs : list A, decode_list dec (encode_list enc xs) = Some xs.
Proof.
  intro xs. unfold decode_list. eapply decode_encode_list_fuel.
  - exact DEC_ENC.
  - lia.
Qed.

#[global]
Instance list_isCountable {A : Type} (COUNTABLE : isCountable A)
  : isCountable (list A).
Proof.
  refine {| encode := encode_list (@encode A COUNTABLE); decode := decode_list (@decode A COUNTABLE); decode_encode := _ |}.
  exact (decode_encode_list (@encode A COUNTABLE) (@decode A COUNTABLE) (@decode_encode A COUNTABLE)).
Defined.

Lemma list_eq_of_nth_error {A : Type} (xs : list A) (ys : list A)
  (EQ : forall n : nat, nth_error xs n = nth_error ys n)
  : xs = ys.
Proof.
  revert ys EQ. induction xs as [ | x xs IH]; intros [ | y ys] EQ; simpl in *.
  - reflexivity.
  - specialize (EQ O). discriminate EQ.
  - specialize (EQ O). discriminate EQ.
  - f_equal.
    + specialize (EQ O). simpl in EQ. congruence.
    + eapply IH. intro n. specialize (EQ (S n)). simpl in EQ. exact EQ.
Qed.

Lemma list_map_inj {A : Type} {B : Type} (f : A -> B)
  (f_inj : forall x1 : A, forall x2 : A, f x1 = f x2 -> x1 = x2)
  : forall xs : list A, forall ys : list A, map f xs = map f ys -> xs = ys.
Proof.
  induction xs as [ | x xs IH]; intros [ | y ys] EQ; simpl in EQ; try discriminate EQ.
  - reflexivity.
  - injection EQ as EQ_head EQ_tail. f_equal.
    + eapply f_inj. exact EQ_head.
    + eapply IH. exact EQ_tail.
Qed.

Lemma Cardinality_ofType_list_le (A : Type@{Set_u}) (B : Type@{Set_u})
  (LE : Cardinality.ofType A =< Cardinality.ofType B)
  : Cardinality.ofType (list A) =< Cardinality.ofType (list B).
Proof.
  destruct LE as [f f_cong f_inj].
  eapply Cardinality_ofType_le_ofType with (f := map f).
  intros xs ys EQ. eapply list_map_inj.
  - intros x1 x2 EQ'. change (x1 = x2). eapply f_inj. change (f x1 = f x2). exact EQ'.
  - exact EQ.
Qed.

Definition list_nth_function {A : Type@{Set_u}} (xs : list A)
  : (Cardinality.exp (Cardinality.ofType nat) (Cardinality.ofType (option A))).(Cardinality.carrier).
Proof.
  exists (fun n : nat => nth_error xs n). intros n n' EQ. change (n = n') in EQ. now subst n'.
Defined.

Lemma Cardinality_ofType_list_le_exp (A : Type@{Set_u})
  : Cardinality.ofType (list A) =< Cardinality.exp (Cardinality.ofType nat) (Cardinality.ofType (option A)).
Proof.
  exists (@list_nth_function A).
  - intros xs ys EQ. change (xs = ys) in EQ. subst ys. intros n n' EQ. change (n = n') in EQ. now subst n'.
  - intros xs ys EQ. change (xs = ys). eapply list_eq_of_nth_error. intro n. pose proof (EQ n n eq_refl) as Hn. change (nth_error xs n = nth_error ys n) in Hn. exact Hn.
Qed.

Definition list_out {A : Type} (xs : list A) : unit + (A * list A) :=
  match xs with
  | [] => inl tt
  | x :: xs => inr (x, xs)
  end.

Definition list_in {A : Type} (s : unit + (A * list A)) : list A :=
  match s with
  | inl _ => []
  | inr p => Datatypes.fst p :: Datatypes.snd p
  end.

Lemma Cardinality_ofType_list_unfold_eq (A : Type@{Set_u})
  : Cardinality.ofType (list A) == Cardinality.ofType (unit + A * list A).
Proof.
  exists (@list_out A) (@list_in A).
  - intros xs ys EQ. change (xs = ys) in EQ. now subst ys.
  - intros s1 s2 EQ. change (s1 = s2) in EQ. now subst s2.
  - intros xs ys EQ. change (list_out xs = list_out ys) in EQ. destruct xs as [ | x xs], ys as [ | y ys]; simpl in EQ; inv EQ; reflexivity.
  - intros s1 s2 EQ. change (list_in s1 = list_in s2) in EQ. destruct s1 as [[ ] | p1], s2 as [[ ] | p2]; simpl in EQ; inv EQ.
    + reflexivity.
    + destruct p1 as [x xs], p2 as [y ys]. simpl in *. subst. reflexivity.
Qed.

Definition rose_out {A : Type} (t : rose A) : A + list (rose A) :=
  match t with
  | leaf x => inl x
  | node ts => inr ts
  end.

Definition rose_in {A : Type} (s : A + list (rose A)) : rose A :=
  match s with
  | inl x => leaf x
  | inr ts => node ts
  end.

Fixpoint encode_rose {A : Type} (t : rose A) {struct t} : list (A + nat) :=
  match t with
  | leaf x => [inl x]
  | node ts => inr (length ts) :: concat (map encode_rose ts)
  end.

Definition encode_roses {A : Type} (ts : list (rose A)) : list (A + nat) :=
  concat (map encode_rose ts).

Fixpoint rose_size {A : Type} (t : rose A) : nat :=
  match t with
  | leaf _ => S O
  | node ts => S (fold_right (fun t : rose A => fun n : nat => rose_size t + n) 0 ts)
  end.

Definition roses_size {A : Type} (ts : list (rose A)) : nat :=
  fold_right (fun t : rose A => fun n : nat => rose_size t + n) O ts.

Lemma rose_size_pos {A : Type} (t : rose A)
  : 0 < rose_size t.
Proof.
  destruct t; simpl; lia.
Qed.

Lemma rose_size_in_roses_size_le {A : Type} (t : rose A) (ts : list (rose A))
  (IN : L.In t ts)
  : rose_size t <= roses_size ts.
Proof.
  unfold roses_size. induction ts as [ | t1 ts IH]; simpl in *.
  - contradiction.
  - destruct IN as [<- | IN].
    + lia.
    + pose proof (IH IN) as LE. lia.
Qed.

Lemma eval_rose_map {A : Type} {B : Type} {C : Type} (merge : list C -> C) (seedA : A -> C) (seedB : B -> C) (f : A -> B)
  (SEED : forall x : A, seedA x = seedB (f x))
  : forall t : rose A, eval_rose merge seedA t = eval_rose merge seedB (rose_map f t).
Proof.
  enough (REC : forall n : nat, forall t : rose A, rose_size t <= n -> eval_rose merge seedA t = eval_rose merge seedB (rose_map f t)).
  { intro t. eapply REC. reflexivity. }
  induction n as [n IH] using lt_wf_ind. intros t SIZE.
  destruct t as [x | ts]; simpl in *.
  - exact (SEED x).
  - f_equal. induction ts as [ | t ts IHlist]; simpl.
    + reflexivity.
    + f_equal.
      * eapply IH with (m := rose_size t).
        { pose proof (rose_size_in_roses_size_le t (t :: ts) (or_introl eq_refl)) as LE. unfold roses_size in LE. lia. }
        { reflexivity. }
      * eapply IHlist. pose proof (rose_size_pos t) as POS. unfold roses_size in SIZE. simpl in SIZE. lia.
Qed.

Lemma eval_rose_image_card_lt `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} {D : Type@{Set_u}} (X : ensemble D) (merge : list D -> D) (A : Type@{Set_u}) (seed : A -> D)
  (LT : Cardinality.ofType (rose A) ≨ ensemble_card X)
  : ensemble_card (fun z : D => exists t : rose A, z = eval_rose merge seed t) ≨ ensemble_card X.
Proof.
  eapply ensemble_card_image_lt with (f := eval_rose merge seed).
  - intros y. reflexivity.
  - exact LT.
Qed.

Lemma encode_rose_prefix {A : Type} (t1 : rose A) (t2 : rose A) (rest1 : list (A + nat)) (rest2 : list (A + nat))
  : encode_rose t1 ++ rest1 = encode_rose t2 ++ rest2 -> t1 = t2 /\ rest1 = rest2.
Proof.
  revert t2 rest1 rest2.
  remember (rose_size t1) as n eqn: SIZE. revert t1 SIZE.
  induction n as [n IH] using lt_wf_ind. intros t1 SIZE t2 rest1 rest2 EQ.
  destruct t1 as [x1 | ts1], t2 as [x2 | ts2]; simpl in EQ.
  - inv EQ. split; reflexivity.
  - discriminate EQ.
  - discriminate EQ.
  - inv EQ.
    assert (LIST : forall ts1' : list (rose A), forall ts2' : list (rose A), forall rest1' : list (A + nat), forall rest2' : list (A + nat), roses_size ts1' <= roses_size ts1 -> length ts1' = length ts2' -> encode_roses ts1' ++ rest1' = encode_roses ts2' ++ rest2' -> ts1' = ts2' /\ rest1' = rest2').
    { induction ts1' as [ | t1' ts1' IHlist]; intros [ | t2' ts2'] rest1' rest2' BOUND EQ_length EQ'; simpl in *.
      - split; [reflexivity | exact EQ'].
      - discriminate EQ_length.
      - discriminate EQ_length.
      - inv EQ_length. unfold encode_roses in EQ'. simpl in EQ'. do 2 rewrite <- app_assoc in EQ'. fold (@encode_roses A) in EQ'.
        unfold roses_size in BOUND. simpl in BOUND. fold (@roses_size A) in BOUND.
        assert (LT_head : rose_size t1' < S (fold_right (fun t : rose A => fun n : nat => rose_size t + n) 0 ts1)) by lia.
        pose proof (IH (rose_size t1') LT_head t1' eq_refl t2' (encode_roses ts1' ++ rest1') (encode_roses ts2' ++ rest2') EQ') as [EQ_t EQ_rest].
        assert (BOUND_tail : roses_size ts1' <= roses_size ts1).
        { unfold roses_size. lia. }
        pose proof (IHlist ts2' rest1' rest2' BOUND_tail H2 EQ_rest) as [EQ_ts EQ_rest']. split; now subst t2' ts2'.
    }
    assert (BOUND_all : roses_size ts1 <= roses_size ts1) by reflexivity.
    pose proof (LIST ts1 ts2 rest1 rest2 BOUND_all H0 H1) as [EQ_ts EQ_rest]. split; now subst ts2.
Qed.

Lemma encode_rose_inj {A : Type} (t1 : rose A) (t2 : rose A)
  (EQ : encode_rose t1 = encode_rose t2)
  : t1 = t2.
Proof.
  assert (EQ_app : encode_rose t1 ++ [] = encode_rose t2 ++ []).
  { now do 2 rewrite app_nil_r. }
  pose proof (@encode_rose_prefix A t1 t2 [] [] EQ_app) as [EQ_t _]. exact EQ_t.
Qed.

Lemma Cardinality_ofType_rose_le_list_sum_nat (A : Type@{Set_u})
  : Cardinality.ofType (rose A) =< Cardinality.ofType (list (A + nat)).
Proof.
  eapply Cardinality_ofType_le_ofType with (f := @encode_rose A). intros t1 t2 EQ. now eapply encode_rose_inj.
Qed.

Lemma Cardinality_ofType_rose_unfold_eq (A : Type@{Set_u})
  : Cardinality.ofType (rose A) == Cardinality.ofType (A + list (rose A)).
Proof.
  exists (@rose_out A) (@rose_in A).
  - intros t1 t2 EQ. change (t1 = t2) in EQ. now subst t2.
  - intros s1 s2 EQ. change (s1 = s2) in EQ. now subst s2.
  - intros t1 t2 EQ. change (rose_out t1 = rose_out t2) in EQ. destruct t1 as [x1 | ts1], t2 as [x2 | ts2]; simpl in EQ; inv EQ; reflexivity.
  - intros s1 s2 EQ. change (rose_in s1 = rose_in s2) in EQ. destruct s1 as [x1 | ts1], s2 as [x2 | ts2]; simpl in EQ; inv EQ; reflexivity.
Qed.

Lemma Cardinality_ofType_list_countable_le_nat {A : Type@{Set_u}} `{COUNTABLE : isCountable A}
  : Cardinality.ofType (list A) =< Cardinality.ofType nat.
Proof.
  eapply Cardinality_ofType_countable_le_nat.
Qed.

Lemma Cardinality_ofType_list_countable_lt_of_uncountable `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} {A : Type@{Set_u}} `{COUNTABLE : isCountable A} (kappa : Cardinality.t)
  (UNCOUNTABLE : ~ kappa =< Cardinality.ofType nat)
  : Cardinality.ofType (list A) ≨ kappa.
Proof.
  eapply Cardinal1.Cardinality_le_lt_lt.
  - eapply Cardinality_ofType_list_countable_le_nat.
  - eapply nat_lt_of_uncountable. exact UNCOUNTABLE.
Qed.

Lemma Cardinality_ofType_sum_countable_le_nat {A : Type@{Set_u}} {B : Type@{Set_u}} `{COUNTABLE_A : isCountable A} `{COUNTABLE_B : isCountable B}
  : Cardinality.ofType (A + B) =< Cardinality.ofType nat.
Proof.
  eapply Cardinality_ofType_countable_le_nat.
Qed.

Lemma Cardinality_ofType_sum_countable_lt_of_uncountable `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} {A : Type@{Set_u}} {B : Type@{Set_u}} `{COUNTABLE_A : isCountable A} `{COUNTABLE_B : isCountable B} (kappa : Cardinality.t)
  (UNCOUNTABLE : ~ kappa =< Cardinality.ofType nat)
  : Cardinality.ofType (A + B) ≨ kappa.
Proof.
  eapply Cardinal1.Cardinality_le_lt_lt.
  - eapply Cardinality_ofType_sum_countable_le_nat.
  - eapply nat_lt_of_uncountable. exact UNCOUNTABLE.
Qed.

Lemma Cardinality_ofType_option_countable_le_nat {A : Type@{Set_u}} `{COUNTABLE : isCountable A}
  : Cardinality.ofType (option A) =< Cardinality.ofType nat.
Proof.
  eapply Cardinality_ofType_countable_le_nat.
Qed.

Lemma Cardinality_ofType_option_countable_lt_of_uncountable `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} {A : Type@{Set_u}} `{COUNTABLE : isCountable A} (kappa : Cardinality.t)
  (UNCOUNTABLE : ~ kappa =< Cardinality.ofType nat)
  : Cardinality.ofType (option A) ≨ kappa.
Proof.
  eapply Cardinal1.Cardinality_le_lt_lt.
  - eapply Cardinality_ofType_option_countable_le_nat.
  - eapply nat_lt_of_uncountable. exact UNCOUNTABLE.
Qed.

Lemma Cardinality_ofType_option_le_self_of_nat_le `{Axms : ClassicalAxioms (b_AC := true)} (A : Type@{Set_u})
  (NAT_LE : Cardinality.ofType nat =< Cardinality.ofType A)
  : Cardinality.ofType (option A) =< Cardinality.ofType A.
Proof.
  destruct NAT_LE as [f f_cong f_inj].
  assert (Hchoice : forall a : A, exists n_opt : option nat, match n_opt with Some n => a = f n | None => forall n : nat, a <> f n end).
  { intro a. pose proof (classic (exists n : nat, a = f n)) as [[n EQ] | NONE].
    - exists (Some n). exact EQ.
    - exists None. intros n EQ. contradiction NONE. exists n. exact EQ.
  }
  pose proof (Axiom_of_Choice A (fun _ : A => option nat) (fun a : A => fun n_opt : option nat => match n_opt with Some n => a = f n | None => forall n : nat, a <> f n end) Hchoice) as [code CODE].
  exists (fun x : option A => match x with Some a => match code a with Some n => f (S n) | None => a end | None => f O end).
  - intros x y EQ. change (x = y) in EQ. now subst y.
  - intros [a | ] [b | ] EQ; simpl in *.
    + destruct (code a) as [n | ] eqn: CODE_a, (code b) as [m | ] eqn: CODE_b; simpl in *.
      * pose proof (f_inj (S n) (S m) EQ) as EQ_nm. change (S n = S m) in EQ_nm. inv EQ_nm.
        pose proof (CODE a) as CODE_a_spec. rewrite CODE_a in CODE_a_spec.
        pose proof (CODE b) as CODE_b_spec. rewrite CODE_b in CODE_b_spec.
        change (Some a = Some b). now rewrite CODE_a_spec, CODE_b_spec.
      * pose proof (CODE b) as CODE_b_spec. rewrite CODE_b in CODE_b_spec.
        exfalso. exact (CODE_b_spec (S n) (eq_sym EQ)).
      * pose proof (CODE a) as CODE_a_spec. rewrite CODE_a in CODE_a_spec.
        exfalso. exact (CODE_a_spec (S m) EQ).
      * now rewrite EQ.
    + destruct (code a) as [n | ] eqn: CODE_a; simpl in *.
      * pose proof (f_inj (S n) O EQ) as EQ_n. discriminate EQ_n.
      * pose proof (CODE a) as CODE_a_spec. rewrite CODE_a in CODE_a_spec.
        exfalso. exact (CODE_a_spec O EQ).
    + destruct (code b) as [n | ] eqn: CODE_b; simpl in *.
      * pose proof (f_inj O (S n) EQ) as EQ_n. discriminate EQ_n.
      * pose proof (CODE b) as CODE_b_spec. rewrite CODE_b in CODE_b_spec.
        exfalso. exact (CODE_b_spec O (eq_sym EQ)).
    + reflexivity.
Qed.

Lemma Cardinality_ofType_option_lt_of_lt_uncountable `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (A : Type@{Set_u}) (kappa : Cardinality.t)
  (LT : Cardinality.ofType A ≨ kappa)
  (UNCOUNTABLE : ~ kappa =< Cardinality.ofType nat)
  : Cardinality.ofType (option A) ≨ kappa.
Proof.
  pose proof (Cardinal1.Cardinality_le_total (Cardinality.ofType A) (Cardinality.ofType nat)) as [A_LE_NAT | NAT_LE_A].
  - eapply Cardinal1.Cardinality_le_lt_lt.
    + transitivity (Cardinality.ofType (option nat)).
      * destruct A_LE_NAT as [f f_cong f_inj].
        eapply Cardinality_ofType_le_ofType with (f := option_map f).
        intros [x | ] [y | ] EQ; simpl in *.
        { inv EQ. change (Some x = Some y). f_equal. eapply f_inj. exact H0. }
        { discriminate EQ. }
        { discriminate EQ. }
        { reflexivity. }
      * eapply Cardinality_ofType_option_countable_le_nat.
    + eapply nat_lt_of_uncountable. exact UNCOUNTABLE.
  - eapply Cardinal1.Cardinality_le_lt_lt.
    + eapply Cardinality_ofType_option_le_self_of_nat_le. exact NAT_LE_A.
    + exact LT.
Qed.

Lemma Cardinality_ofType_unit_lt_of_uncountable `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} (kappa : Cardinality.t)
  (UNCOUNTABLE : ~ kappa =< Cardinality.ofType nat)
  : Cardinality.ofType unit ≨ kappa.
Proof.
  eapply Cardinal1.Cardinality_le_lt_lt.
  - eapply Cardinality_ofType_le_ofType with (f := fun _ : unit => O). intros [ ] [ ] EQ. reflexivity.
  - eapply nat_lt_of_uncountable. exact UNCOUNTABLE.
Qed.

Lemma Cardinality_ofType_rose_countable_le_nat {A : Type@{Set_u}} `{COUNTABLE : isCountable A}
  : Cardinality.ofType (rose A) =< Cardinality.ofType nat.
Proof.
  transitivity (Cardinality.ofType (list (A + nat))).
  - eapply Cardinality_ofType_rose_le_list_sum_nat.
  - eapply Cardinality_ofType_list_countable_le_nat.
Qed.

Lemma Cardinality_ofType_rose_countable_lt_of_uncountable `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} {A : Type@{Set_u}} `{COUNTABLE : isCountable A} (kappa : Cardinality.t)
  (UNCOUNTABLE : ~ kappa =< Cardinality.ofType nat)
  : Cardinality.ofType (rose A) ≨ kappa.
Proof.
  eapply Cardinal1.Cardinality_le_lt_lt.
  - eapply Cardinality_ofType_rose_countable_le_nat.
  - eapply nat_lt_of_uncountable. exact UNCOUNTABLE.
Qed.

End LIST_ROSE_BOUND.

End Cardinal2.

Section ZORN.

#[local] Infix "\in" := E.In.

#[local] Infix "\subseteq" := E.isSubsetOf.

#[local] Hint Unfold flip : simplication_hints.

Context `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}.

#[local, program]
Instance Proset_fromStrictOrder (B : Type@{U_discourse}) (SETOID : isSetoid B) (LT : B -> B -> Prop) (LT_StrictOrder : StrictOrder LT) (LT_eqPropCompatible2 : eqPropCompatible2 LT) : isProset B :=
  { leProp x y := LT x y \/ x == y
  ; Proset_isSetoid := SETOID
  }.
Next Obligation.
  split.
  - intros x. right. reflexivity.
  - intros x y z Hxy Hyz. destruct Hxy as [Hxy | Hxy], Hyz as [Hyz | Hyz].
    + left. eapply StrictOrder_Transitive; eauto.
    + left. eapply LT_eqPropCompatible2 with (x2 := x) (y2 := y); eauto with *.
    + left. eapply LT_eqPropCompatible2 with (x2 := y) (y2 := z); eauto with *.
    + right. transitivity y; eauto with *.
Qed.
Next Obligation.
  intros x y. split.
  - intros Hxy. cbn. split; eauto with *.
  - intros [Hxy Hyx]. s!. destruct Hxy as [Hxy | Hxy], Hyx as [Hyx | Hyx].
    + exfalso. eapply StrictOrder_Irreflexive with (x := x). transitivity y; eauto.
    + exfalso. eapply StrictOrder_Irreflexive with (x := x). eapply LT_eqPropCompatible2 with (x2 := x) (y2 := y); eauto with *.
    + exfalso. eapply StrictOrder_Irreflexive with (x := y). eapply LT_eqPropCompatible2 with (x2 := y) (y2 := x); eauto with *.
    + transitivity y; eauto with *.
Qed.

Section ZORNLT.

Context {B : Type@{U_discourse}} {SETOID : isSetoid B} {LT : B -> B -> Prop}.

Hypothesis LT_StrictOrder : StrictOrder LT.

Hypothesis LT_eqPropCompatible2 : eqPropCompatible2 LT.

Let B_isProset : isProset B :=
  Proset_fromStrictOrder B SETOID LT LT_StrictOrder LT_eqPropCompatible2.

#[local] Existing Instance B_isProset.

Let chain : Type@{U_discourse} :=
  ensemble B.

Let chain_le (c : chain) (c' : chain) : Prop :=
  c \subseteq c' /\ (forall b, b \in c' -> b \in c \/ b \in upperboundsOf c).

Lemma chain_le_refl (c : chain)
  (CHAIN : isChain c)
  : chain_le c c.
Proof.
  split; eauto with *.
Qed.

Lemma chain_le_trans (c : chain) (c' : chain) (c'' : chain)
  (CHAIN : isChain c)
  (CHAIN' : isChain c')
  (CHAIN'' : isChain c'')
  (LE1 : chain_le c c')
  (LE2 : chain_le c' c'')
  : chain_le c c''.
Proof.
  destruct LE1 as [SUB01 EXT01], LE2 as [SUB12 EXT12]. split.
  - intros b Hb; eauto with *.
  - intros b Hb. pose proof (EXT12 b Hb) as [Hb1 | Hub1].
    + pose proof (EXT01 b Hb1) as [Hb0 | Hub0]; eauto with *.
    + right. intros x Hx. eapply Hub1. eapply SUB01. exact Hx.
Qed.

Lemma chain_le_antisymmetry (c : chain) (c' : chain)
  (LE1 : chain_le c c')
  (LE2 : chain_le c' c)
  : c = c'.
Proof.
  eapply @Functional_Extensionality with (b_fun_ext := true); eauto with *. intros b.
  eapply @Propositional_Extensionality with (b_prop_ext := true); eauto with *.
  destruct LE1 as [SUB01 _], LE2 as [SUB10 _]; ss!.
Qed.

Definition chain_join (I : Type) (cs : I -> chain) : chain :=
  fun b => exists i, b \in cs i.

Lemma chain_join_good (I : Type) (ds : I -> chain)
  (CHAIN : forall i1, forall i2, chain_le (ds i1) (ds i2) \/ chain_le (ds i2) (ds i1))
  (GOODs : forall i, isChain (ds i))
  : isChain (chain_join I ds).
Proof.
  intros x y [i Hx] [j Hy]. pose proof (CHAIN i j) as [LE | LE].
  - eapply GOODs with (i := j); auto with *. now eapply LE.
  - eapply GOODs with (i := i); auto with *. now eapply LE.
Qed.

Lemma chain_join_supremum (I : Type) (ds : I -> chain)
  (CHAIN : forall i1, forall i2, chain_le (ds i1) (ds i2) \/ chain_le (ds i2) (ds i1))
  (GOODs : forall i, isChain (ds i))
  : forall d : chain, forall GOOD : isChain d, chain_le (chain_join I ds) d <-> (forall i, chain_le (ds i) d).
Proof.
  ii. split.
  - intros LE i. destruct LE as [H1 H2]. split.
    + intros b Hb. eapply H1. now exists i.
    + intros b Hb. pose proof (H2 b Hb) as [Hjoin | Hub].
      * destruct Hjoin as [j Hj]. pose proof (CHAIN i j) as [LEij | LEji].
        { exact (proj2 LEij b Hj). }
        { left. exact (proj1 LEji _ Hj). }
      * right. intros x Hx. eapply Hub. now exists i.
  - intros LE. split.
    + intros b [i Hb]. pose proof (proj1 (LE i)). eauto.
    + intros b Hb. pose proof (classic (b \in chain_join I ds)) as [Hjoin | Hjoin].
      * left. exact Hjoin.
      * right. intros x [i Hx]. pose proof (proj2 (LE i) b Hb) as [Hb' | Hub].
        { contradiction Hjoin. now exists i. }
        { eapply Hub. exact Hx. }
Qed.

Section INCR.

Definition chain_base : chain :=
  fun _ => False.

Lemma chain_base_good
  : isChain chain_base.
Proof.
  intros x y Hx. contradiction.
Qed.

Variable f : chain -> B.

Definition chain_next (c : chain) : chain :=
  fun b => b \in c \/ b == f c.

Hypothesis INCR : forall c, isChain c -> forall b, b \in c -> LT b (f c).

Lemma chain_next_good (c : chain)
  (CHAIN : isChain c)
  : isChain (chain_next c).
Proof.
  intros x y Hx Hy. unfold chain_next in *. destruct Hx as [Hx | Hx], Hy as [Hy | Hy].
  - exact (CHAIN x y Hx Hy).
  - left. left. eapply LT_eqPropCompatible2 with (x2 := x) (y2 := f c); eauto with *.
  - right. left. eapply LT_eqPropCompatible2 with (x2 := y) (y2 := f c); eauto with *.
  - left. right. transitivity (f c); eauto with *.
Qed.

Lemma chain_next_extensive (c : chain)
  (CHAIN : isChain c)
  : chain_le c (chain_next c).
Proof.
  split.
  - intros b Hb. now left.
  - intros b Hb. unfold chain_next in Hb. destruct Hb as [Hb | Hb].
    + left. exact Hb.
    + right. intros x Hx. left. eapply LT_eqPropCompatible2 with (x2 := x) (y2 := f c); eauto with *.
Qed.

Lemma chain_next_congruence (c0 : chain) (c1 : chain)
  (CHAIN0 : isChain c0)
  (CHAIN1 : isChain c1)
  (EQ : chain_le c0 c1 /\ chain_le c1 c0)
  : chain_le (chain_next c0) (chain_next c1) /\ chain_le (chain_next c1) (chain_next c0).
Proof.
  destruct EQ as [LE01 LE10].
  assert (c0 = c1) by now eapply chain_le_antisymmetry.
  subst c1. split; eapply chain_le_refl; eapply chain_next_good; eauto.
Qed.

#[local] Hint Resolve chain_le_refl chain_le_trans chain_base_good chain_join_good chain_next_good chain_next_extensive chain_next_congruence : core.

Lemma eventually_maximal
  : False.
Proof.
  set (c := Ord.rec chain_base chain_next chain_join (hartogs chain)).
  pose proof (@InducedOrdinal.rec_good chain isChain chain_le chain_le_refl chain_le_trans chain_join chain_join_good chain_join_supremum chain_base chain_base_good chain_next chain_next_good chain_next_extensive chain_next_congruence (hartogs chain)) as Hgood.
  pose proof (@InducedOrdinal.BourbakiWittFixedpointTheorem chain isChain chain_le chain_le_refl chain_le_trans chain_join chain_join_good chain_join_supremum chain_base chain_base_good chain_next chain_next_good chain_next_extensive chain_next_congruence) as Hfix.
  destruct Hfix as [[H1 H2] H3].
  assert (f c \in chain_next c).
  { right. reflexivity. }
  assert (H_in : f c \in c).
  { eapply H1. now right. }
  pose proof (INCR c Hgood (f c) H_in) as Hlt.
  exact (StrictOrder_Irreflexive _ Hlt).
Qed.

End INCR.

Theorem zorn_lemma_lt
  (upperbound_exists : forall c : chain, forall GOOD : isChain c, exists b_u, b_u \in upperboundsOf c)
  : exists b_m, forall b, ~ LT b_m b.
Proof.
  eapply NNPP. intros H_contra.
  assert (NOT_MAX : forall b : B, exists b' : B, LT b b').
  { intros b. pose proof (classic (exists b' : B, LT b b')) as [H | H]; auto.
    contradiction H_contra. exists b. intros b' Hb'; eauto.
  }
  pose proof (upperbound_exists chain_base chain_base_good) as [b0 IN0].
  assert (Hchoice : forall c : chain, exists b1 : B, forall GOOD : isChain c, forall b0' : B, b0' \in c -> LT b0' b1).
  { intros c. pose proof (classic (isChain c)) as [CHAIN | NCHAIN].
    - pose proof (upperbound_exists c CHAIN) as [b_u HUB].
      pose proof (NOT_MAX b_u) as [b1 Hb1].
      exists b1. intros _ b IN.
      pose proof (HUB b IN) as [Hlt | Heq].
      + transitivity b_u; eauto.
      + now rewrite -> Heq.
    - exists b0. contradiction.
  }
  pose proof (Axiom_of_Choice chain (fun _ => B) (fun c => fun b => forall GOOD : isChain c, forall x : B, forall IN : x \in c, LT x b) Hchoice) as [f Hf].
  eapply eventually_maximal with (f := f); eauto.
Qed.

End ZORNLT.

Section ZORN_PREORDER.

Context {B : Type@{U_discourse}} {PROSET : isProset B}.

Let lt (x : B) (y : B) : Prop :=
  (x =< y) /\ ~ (y =< x).

#[local]
Instance lt_StrictOrder
  : StrictOrder lt.
Proof.
  split.
  - intros x [Hle Hnle]. exact (Hnle Hle).
  - intros x y z [Hxy Hnxy] [Hyz Hnyz]. split.
    + transitivity y; assumption.
    + intro Hzx. apply Hnxy. transitivity z; assumption.
Qed.

#[local]
Instance lt_eqPropCompatible2
  : eqPropCompatible2 lt.
Proof.
  intros x1 x2 y1 y2 Hx Hy. change (lt x1 y1 <-> lt x2 y2). split; [intros [Hle Hnle] | intros [Hle Hnle]].
  - split; now rewrite <- Hx, <- Hy.
  - split; now rewrite -> Hx, -> Hy.
Qed.

Theorem zorn_lemma
  (upperbound_exists : forall c : ensemble B, forall GOOD : isChain c, exists b_u, b_u \in upperboundsOf c)
  : exists b_m, forall b, b_m =< b -> b =< b_m.
Proof.
  refine (let PROSET' : isProset B := Proset_fromStrictOrder B PROSET.(Proset_isSetoid) lt lt_StrictOrder lt_eqPropCompatible2 in _).
  assert (upperbound_exists_strict : forall c : ensemble B, forall GOOD : @isChain B PROSET' c, exists b_u : B, b_u \in @upperboundsOf B PROSET' c).
  { intros c CHAIN. pose proof (upperbound_exists c) as [b_u HUB].
    - intros x y Hx Hy. pose proof (CHAIN x y Hx Hy) as [[Hlt | Heq] | [Hlt | Heq]].
      + left. exact (proj1 Hlt).
      + left. eapply eqProp_implies_leProp. exact Heq.
      + right. exact (proj1 Hlt).
      + right. eapply eqProp_implies_leProp. exact Heq.
    - exists b_u. intros x Hx. pose proof (HUB x Hx) as HH. pose proof (classic (leProp (isProset := PROSET) b_u x)) as [Hbx | Hbx].
      + right. eapply leProp_antisymmetry; eauto.
      + left. split; eauto.
  }
  exploit (zorn_lemma_lt (LT := lt)).
  { ii. pose proof (upperbound_exists_strict c GOOD) as [b_u HH]. exists b_u. eauto. }
  intros [b_m Hm]. exists b_m. intros b Hle.
  pose proof (classic (leProp (isProset := PROSET) b b_m)) as [YES | NO]; auto.
  contradiction (Hm b). split; eauto.
Qed.

End ZORN_PREORDER.

Theorem Zorn's_lemma (D : Type@{U_discourse}) (PROSET : isProset D)
  (INHABITED : inhabited D)
  (upperbound_exists : forall C : ensemble D, ⟪ NONEMPTY : exists d : D, d \in C ⟫ -> ⟪ CHAIN : forall x1 : D, forall x2 : D, forall IN1 : x1 \in C, forall IN2 : x2 \in C, leProp (isProset := PROSET) x1 x2 \/ leProp (isProset := PROSET) x2 x1 ⟫ -> ⟪ upperbound_exists : exists u : D, forall d : D, forall IN : d \in C, leProp (isProset := PROSET) d u ⟫)
  : exists d_m : D, ⟪ MAXIMAL : forall d : D, forall LE : leProp (isProset := PROSET) d_m d, leProp (isProset := PROSET) d d_m ⟫.
Proof.
  unnw. eapply zorn_lemma. intros C CHAIN. pose proof (classic (exists d : D, d \in C)) as [Hin | Hempty].
  - eapply upperbound_exists; eauto.
  - destruct INHABITED as [d0]. exists d0. intros d Hd. contradiction Hempty. now exists d.
Qed.

End ZORN.

Theorem hartogs_rEq_Hartogs `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} {D : Type@{Set_u}}
  : hartogs D =ᵣ @Cardinal1.Hartogs D (@mkSetoid_from_eq D).
Proof.
  refine (let lift (P : D -> Prop) (R : @sig D P -> @sig D P -> Prop) (x : D) (y : D) : Prop := exists Hx : P x, exists Hy : P y, R (@exist D P x Hx) (@exist D P y Hy) in _).
  assert (lift_wf : forall P : D -> Prop, forall R : @sig D P -> @sig D P -> Prop, well_founded R -> well_founded (lift P R)).
  { intros P R R_wf x. unfold lift. pose proof (classic (P x)) as [YES | NO].
    - remember (@exist D P x YES) as sx eqn: H_eq. revert x YES H_eq. induction (R_wf sx) as [sx _ IH].
      intros x Hx ?. subst sx. econs. intros y (Hy & Hx' & Hrel).
      rewrite (proof_irrelevance _ Hx' Hx) in Hrel.
      exact (IH (@exist D P y Hy) Hrel y Hy eq_refl).
    - econs. intros y (_ & Hyx & _). contradiction.
  }
  split.
  - unfold hartogs. eapply rLe_intro_var1. intros t [[R R_wf] H_t]. simpl in H_t. rewrite H_t.
    pose proof (extendedOrder_exists D (@mkSetoid_from_eq D) R R_wf) as (R' & R'_wf & R_incl & R'_total & R'_trans); unnw.
    pose (P := fun _ : D => True).
    refine (let Rsig : @sig D P -> @sig D P -> Prop := binary_relation_on_image R' (@proj1_sig D P) in _).
    assert (Rsig_wf : well_founded Rsig).
    { eapply relation_on_image_liftsWellFounded. exact R'_wf. }
    assert (Rsig_total : forall x : @sig D P, forall y : @sig D P, proj1_sig x = proj1_sig y \/ Rsig x y \/ Rsig y x).
    { intros [x Hx'] [y Hy']. simpl. pose proof (R'_total x y) as [H | [H | H]]; eauto. }
    assert (Rsig_trans : Transitive Rsig).
    { ii; eapply R'_trans; eauto. }
    assert (Rsig_compat : eqPropCompatible2 (A_isSetoid := @subSetoid D mkSetoid_from_eq P) (B_isSetoid := @subSetoid D mkSetoid_from_eq P) Rsig).
    { intros [x1 H_x1] [x2 H_x2] [y1 H_y1] [y2 H_y2]; simpl; ii; subst x2 y2. rewrite proof_irrelevance with (p1 := H_x1) (p2 := H_y1). rewrite proof_irrelevance with (p1 := H_x2) (p2 := H_y2). reflexivity. }
    eapply rLt_intro_var1. exists (@fromWfSet (@sig D P) Rsig Rsig_wf). split.
    + assert (H_Rsig : well_founded Rsig /\ (forall x : @sig D P, forall y : @sig D P, (` x)%prg = (` y)%prg \/ Rsig x y \/ Rsig y x) /\ Transitive Rsig /\ eqPropCompatible2 (A_isSetoid := @subSetoid D mkSetoid_from_eq P) (B_isSetoid := @subSetoid D mkSetoid_from_eq P) Rsig) by eauto.
      pattern Rsig in H_Rsig. pose (W := @exist (@sig D P -> @sig D P -> Prop) _ Rsig H_Rsig). exists (@existT _ _ P W). simpl. split; intros c; exists c; eapply fromWf_pirrel.
    + transitivity (@fromWfSet D R' R'_wf).
      * eapply fromWfSet_isMonotonic. exact R_incl.
      * eapply fromWfSet_cong with (f := fun d : D => @exist D P d I); eauto.
  - unfold hartogs. eapply rLe_intro_var1. intros x [[P [R HR]] Hx].
    destruct HR as [R_wf [R_total [R_trans R_compat]]]. simpl in Hx. rewrite Hx.
    eapply rLt_intro_var1. exists (@fromWfSet D (lift P R) (lift_wf P R R_wf)). split.
    + exists (B.exist (lift P R) (lift_wf P R R_wf)). reflexivity.
    + eapply fromWfSet_cong with (f := @proj1_sig D P). intros [a H_a] [b H_b] Hab; simpl. exists H_a. exists H_b. exact Hab.
Qed.

Module Cardinal3.

Section CARDINALITY.

Context `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}.

#[local] Existing Instance Aczel.children_isSetoid.

Lemma Cardinality_ofType_bool_le_of_nat_le (A : Type@{Set_u})
  (NAT_LE : Cardinality.ofType nat =< Cardinality.ofType A)
  : Cardinality.ofType bool =< Cardinality.ofType A.
Proof.
  destruct NAT_LE as [f f_cong f_inj].
  eapply Cardinal2.Cardinality_ofType_le_ofType with (f := fun b : bool => if b then f O else f (S O)).
  intros [ | ] [ | ] EQ; try reflexivity.
  - pose proof (f_inj O (S O) EQ) as H. discriminate H.
  - pose proof (f_inj (S O) O EQ) as H. discriminate H.
Qed.

Definition option_pair_code {A : Type@{Set_u}} (tag : nat -> A) (pair : A * A -> A) (xy : option A * option A) : A :=
  match xy with
  | (None, None) => pair (tag O, tag O)
  | (None, Some y) => pair (tag (S O), y)
  | (Some x, None) => pair (tag (S (S O)), x)
  | (Some x, Some y) => pair (tag (S (S (S O))), pair (x, y))
  end.

Lemma option_pair_code_inj {A : Type@{Set_u}} (tag : nat -> A) (pair : A * A -> A)
  (TAG_INJ : forall n : nat, forall m : nat, tag n = tag m -> n = m)
  (PAIR_INJ : forall p : A * A, forall q : A * A, pair p = pair q -> p = q)
  : forall p : option A * option A, forall q : option A * option A, option_pair_code tag pair p = option_pair_code tag pair q -> p = q.
Proof.
  intros [[x | ] [y | ]] [[x' | ] [y' | ]] EQ; unfold option_pair_code in EQ.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (PAIR_INJ _ _ H0) as EQ_xy. inv EQ_xy. reflexivity.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S (S (S O))) (S (S O)) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S (S (S O))) (S O) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S (S (S O))) O H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S (S O)) (S (S (S O))) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair. reflexivity.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S (S O)) (S O) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S (S O)) O H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S O) (S (S (S O))) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S O) (S (S O)) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair. reflexivity.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S O) O H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ O (S (S (S O))) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ O (S (S O)) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ O (S O) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair. reflexivity.
Qed.

Lemma Cardinality_ofType_option_prod_le_self_of_nat_le_square_le (A : Type@{Set_u})
  (NAT_LE : Cardinality.ofType nat =< Cardinality.ofType A)
  (SQUARE_LE : Cardinality.ofType (A * A) =< Cardinality.ofType A)
  : Cardinality.ofType (option A * option A) =< Cardinality.ofType A.
Proof.
  destruct NAT_LE as [tag tag_cong tag_inj]. destruct SQUARE_LE as [pair pair_cong pair_inj].
  eapply Cardinal2.Cardinality_ofType_le_ofType with (f := option_pair_code tag pair).
  eapply option_pair_code_inj.
  - intros n m EQ. change (n = m). eapply tag_inj. change (tag n = tag m). exact EQ.
  - intros [x y] [x' y'] EQ. change ((x, y) = (x', y')). eapply pair_inj. change (pair (x, y) = pair (x', y')). exact EQ.
Qed.

Fixpoint encode_list_by_pair {A : Type@{Set_u}} (pair : A * A -> A) (pack : option A -> A) (xs : list A) : option A :=
  match xs with
  | [] => None
  | x :: xs => Some (pair (x, pack (encode_list_by_pair pair pack xs)))
  end.

Lemma encode_list_by_pair_inj {A : Type@{Set_u}} (pair : A * A -> A) (pack : option A -> A)
  (PAIR_INJ : forall p : A * A, forall q : A * A, pair p = pair q -> p = q)
  (PACK_INJ : forall x : option A, forall y : option A, pack x = pack y -> x = y)
  : forall xs : list A, forall ys : list A, encode_list_by_pair pair pack xs = encode_list_by_pair pair pack ys -> xs = ys.
Proof.
  induction xs as [ | x xs IH]; intros [ | y ys] EQ; simpl in EQ.
  - reflexivity.
  - discriminate EQ.
  - discriminate EQ.
  - injection EQ as EQ_code. pose proof (PAIR_INJ _ _ EQ_code) as EQ_pair.
    injection EQ_pair as EQ_x EQ_pack. subst y. f_equal. eapply IH. eapply PACK_INJ. exact EQ_pack.
Qed.

Lemma Cardinality_ofType_list_le_self_of_nat_le_square_le (A : Type@{Set_u})
  (NAT_LE : Cardinality.ofType nat =< Cardinality.ofType A)
  (SQUARE_LE : Cardinality.ofType (A * A) =< Cardinality.ofType A)
  : Cardinality.ofType (list A) =< Cardinality.ofType A.
Proof.
  destruct SQUARE_LE as [pair pair_cong pair_inj].
  pose proof (Cardinal2.Cardinality_ofType_option_le_self_of_nat_le A NAT_LE) as OPTION_LE.
  pose proof OPTION_LE as OPTION_LE'.
  destruct OPTION_LE as [pack pack_cong pack_inj].
  transitivity (Cardinality.ofType (option A)).
  - eapply Cardinal2.Cardinality_ofType_le_ofType with (f := encode_list_by_pair pair pack).
    eapply encode_list_by_pair_inj.
    + intros [x y] [x' y'] EQ. change ((x, y) = (x', y')). eapply pair_inj. change (pair (x, y) = pair (x', y')). exact EQ.
    + intros x y EQ. change (x = y). eapply pack_inj. change (pack x = pack y). exact EQ.
  - exact OPTION_LE'.
Qed.

Lemma Cardinality_ofType_sum_nat_le_self_of_nat_le_square_le (A : Type@{Set_u})
  (NAT_LE : Cardinality.ofType nat =< Cardinality.ofType A)
  (SQUARE_LE : Cardinality.ofType (A * A) =< Cardinality.ofType A)
  : Cardinality.ofType (A + nat) =< Cardinality.ofType A.
Proof.
  transitivity (Cardinality.ofType (bool * A)).
  - destruct NAT_LE as [tag tag_cong tag_inj].
    eapply Cardinal2.Cardinality_ofType_le_ofType with (f := fun x : A + nat => match x with inl a => (true, a) | inr n => (false, tag n) end).
    intros [a | n] [a' | n'] EQ; simpl in EQ.
    + inv EQ. reflexivity.
    + inv EQ.
    + inv EQ.
    + injection EQ as EQ_tag. f_equal. eapply tag_inj. exact EQ_tag.
  - transitivity (Cardinality.ofType (A * A)).
    + eapply Cardinal2.Cardinality_ofType_prod_le.
      * eapply Cardinality_ofType_bool_le_of_nat_le. exact NAT_LE.
      * reflexivity.
    + exact SQUARE_LE.
Qed.

Lemma Cardinality_ofType_list_sum_nat_le_self_of_nat_le_square_le (A : Type@{Set_u})
  (NAT_LE : Cardinality.ofType nat =< Cardinality.ofType A)
  (SQUARE_LE : Cardinality.ofType (A * A) =< Cardinality.ofType A)
  : Cardinality.ofType (list (A + nat)) =< Cardinality.ofType A.
Proof.
  transitivity (Cardinality.ofType (list A)).
  - eapply Cardinal2.Cardinality_ofType_list_le.
    eapply Cardinality_ofType_sum_nat_le_self_of_nat_le_square_le; eauto.
  - eapply Cardinality_ofType_list_le_self_of_nat_le_square_le; eauto.
Qed.

Lemma Cardinality_ofType_rose_le_self_of_nat_le_square_le (A : Type@{Set_u})
  (NAT_LE : Cardinality.ofType nat =< Cardinality.ofType A)
  (SQUARE_LE : Cardinality.ofType (A * A) =< Cardinality.ofType A)
  : Cardinality.ofType (Cardinal2.rose A) =< Cardinality.ofType A.
Proof.
  transitivity (Cardinality.ofType (list (A + nat))).
  - eapply Cardinal2.Cardinality_ofType_rose_le_list_sum_nat.
  - eapply Cardinality_ofType_list_sum_nat_le_self_of_nat_le_square_le; eauto.
Qed.

Lemma Cardinality_ofType_rose_lt_of_lt_uncountable_square_le (A : Type@{Set_u}) (kappa : Cardinality.t)
  (LT : Cardinality.ofType A ≨ kappa)
  (UNCOUNTABLE : ~ kappa =< Cardinality.ofType nat)
  (SQUARE : forall B : Type@{Set_u}, Cardinality.ofType nat =< Cardinality.ofType B -> Cardinality.ofType (B * B) =< Cardinality.ofType B)
  : Cardinality.ofType (Cardinal2.rose A) ≨ kappa.
Proof.
  pose proof (Cardinal1.Cardinality_le_total (Cardinality.ofType A) (Cardinality.ofType nat)) as [A_LE_NAT | NAT_LE_A].
  - eapply Cardinal1.Cardinality_le_lt_lt.
    + transitivity (Cardinality.ofType (list (nat + nat))).
      * destruct A_LE_NAT as [f f_cong f_inj].
        eapply Cardinal2.Cardinality_ofType_le_ofType with (f := fun t : Cardinal2.rose A => map (fun x : A + nat => match x with inl a => inl (f a) | inr n => inr n end) (Cardinal2.encode_rose t)).
        intros t1 t2 EQ. eapply Cardinal2.encode_rose_inj.
        eapply Cardinal2.list_map_inj in EQ.
        { exact EQ. }
        intros [a | n] [a' | n'] EQ'; inv EQ'.
        { f_equal. eapply f_inj. exact H0. }
        { reflexivity. }
      * eapply Cardinal2.Cardinality_ofType_list_countable_le_nat.
    + eapply Cardinal2.nat_lt_of_uncountable. exact UNCOUNTABLE.
  - eapply Cardinal1.Cardinality_le_lt_lt.
    + eapply Cardinality_ofType_rose_le_self_of_nat_le_square_le.
      * exact NAT_LE_A.
      * eapply SQUARE. exact NAT_LE_A.
    + exact LT.
Qed.

Theorem Cardinality_ofType_rank_strict_initial_segment_lt (A : Type@{Set_u}) (kappa : Ord.t)
  (K_CARD : Cardinal1.hasCardinality (Cardinality.ofType A) kappa)
  (enum : Aczel.children kappa -> A)
  (enum_inj : forall c1 : Aczel.children kappa, forall c2 : Aczel.children kappa, c1 == c2 <-> enum c1 = enum c2)
  (rank : A -> Aczel.children kappa)
  (RANK : forall x : A, enum (rank x) = x)
  : forall a : A, Cardinality.ofType { x : A | Aczel.isElemOf kappa (rank x) (rank a) } ≨ Cardinality.ofType A.
Proof.
  i.
  pose proof (Cardinal1.hasCardinality_isOrdinal _ _ K_CARD) as K_ORD.
  set (alpha := Aczel.childnodes kappa (rank a)).
  assert (ALPHA_ORD : Aczel.isOrdinal alpha).
  { eapply Aczel.isOrdinal_member_isOrdinal.
    - exact K_ORD.
    - unfold alpha. eapply Aczel.member_intro.
  }
  assert (ALPHA_LT : alpha <ᵣ kappa).
  { unfold alpha. eapply Aczel.member_implies_rLt. eapply Aczel.member_intro. }
  assert (STRICT_LE : Cardinality.ofType { x : A | Aczel.isElemOf kappa (rank x) (rank a) } =< card alpha).
  { assert (Hchoice : forall i : { x : A | Aczel.isElemOf kappa (rank x) (rank a) }, exists c : Aczel.children alpha, Aczel.childnodes alpha c == Aczel.childnodes kappa (rank (proj1_sig i))).
    { intros [x Hx]. unfold alpha. unfold Aczel.isElemOf in Hx. destruct Hx as [c EQ]. exists c. symmetry. exact EQ. }
    pose proof (Axiom_of_Choice { x : A | Aczel.isElemOf kappa (rank x) (rank a) } (fun _ : { x : A | Aczel.isElemOf kappa (rank x) (rank a) } => Aczel.children alpha) (fun i : { x : A | Aczel.isElemOf kappa (rank x) (rank a) } => fun c : Aczel.children alpha => Aczel.childnodes alpha c == Aczel.childnodes kappa (rank (proj1_sig i))) Hchoice) as [pick PICK].
    exists pick.
    - intros i j EQ. change (i = j) in EQ. subst j. reflexivity.
    - intros [x Hx] [y Hy] EQ. eapply Cardinal2.sig_eq_from_proj1. simpl.
      assert (RANK_EQ : rank x == rank y).
      { change (Aczel.childnodes kappa (rank x) == Aczel.childnodes kappa (rank y)).
        transitivity (Aczel.childnodes alpha (pick (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a)) x Hx))).
        - symmetry. exact (PICK (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a)) x Hx)).
        - transitivity (Aczel.childnodes alpha (pick (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a)) y Hy))).
          + exact EQ.
          + exact (PICK (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a)) y Hy)).
      }
      pose proof (proj1 (enum_inj (rank x) (rank y)) RANK_EQ) as ENUM_EQ. now rewrite 2 RANK in ENUM_EQ.
  }
  assert (K_CARDINAL : Cardinal1.isCardinal kappa).
  { exists (Cardinality.ofType A). exact K_CARD. }
  pose proof (Cardinal1.card_children_lt_card_of_rLt alpha kappa ALPHA_ORD K_CARDINAL ALPHA_LT) as CARD_ALPHA_LT_KAPPA.
  assert (CARD_KAPPA_LE : card kappa =< Cardinality.ofType A).
  { pose proof (Cardinal1.isCardinal_elim kappa K_CARDINAL) as CARD_KAPPA.
    rewrite Cardinal1.Cardinality_le_iff. rewrite (Cardinal1.Cardinality_toTree_eq_intro (card kappa) kappa CARD_KAPPA).
    rewrite (Cardinal1.Cardinality_toTree_eq_intro (Cardinality.ofType A) kappa K_CARD). reflexivity.
  }
  eapply Cardinal1.Cardinality_le_lt_lt.
  - exact STRICT_LE.
  - eapply Cardinal1.Cardinality_lt_le_lt.
    + exact CARD_ALPHA_LT_KAPPA.
    + exact CARD_KAPPA_LE.
Qed.

Theorem Cardinality_ofType_rank_initial_segment_lt (A : Type@{Set_u}) (kappa : Ord.t)
  (K_CARD : Cardinal1.hasCardinality (Cardinality.ofType A) kappa)
  (UNCOUNTABLE : ~ Cardinality.ofType A =< Cardinality.ofType nat)
  (enum : Aczel.children kappa -> A)
  (enum_inj : forall c1 : Aczel.children kappa, forall c2 : Aczel.children kappa, c1 == c2 <-> enum c1 = enum c2)
  (rank : A -> Aczel.children kappa)
  (RANK : forall x : A, enum (rank x) = x)
  : forall a : A, Cardinality.ofType { x : A | Aczel.isElemOf kappa (rank x) (rank a) \/ Aczel.eqTree (Aczel.childnodes kappa (rank x)) (Aczel.childnodes kappa (rank a)) } ≨ Cardinality.ofType A.
Proof.
  i.
  set (StrictIdx := { x : A | Aczel.isElemOf kappa (rank x) (rank a) }).
  set (Idx := { x : A | Aczel.isElemOf kappa (rank x) (rank a) \/ Aczel.eqTree (Aczel.childnodes kappa (rank x)) (Aczel.childnodes kappa (rank a)) }).
  assert (IDX_LE : Cardinality.ofType Idx =< Cardinality.ofType (option StrictIdx)).
  { assert (Hchoice : forall i : Idx, exists oi : option StrictIdx, match oi with | Some j => proj1_sig j = proj1_sig i | None => rank (proj1_sig i) == rank a end).
    { intros [x [LT | EQ]].
      - exists (Some (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a)) x LT)). reflexivity.
      - exists None. exact EQ.
    }
    pose proof (Axiom_of_Choice Idx (fun _ : Idx => option StrictIdx) (fun i : Idx => fun oi : option StrictIdx => match oi with | Some j => proj1_sig j = proj1_sig i | None => rank (proj1_sig i) == rank a end) Hchoice) as [pick PICK].
    exists pick.
    - intros i j EQ. change (i = j) in EQ. subst j. reflexivity.
    - intros [x Hx] [y Hy] EQ. unfold Idx in *. simpl in *.
      pose proof (PICK (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a) \/ Aczel.eqTree (Aczel.childnodes kappa (rank z)) (Aczel.childnodes kappa (rank a))) x Hx)) as PICKx.
      pose proof (PICK (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a) \/ Aczel.eqTree (Aczel.childnodes kappa (rank z)) (Aczel.childnodes kappa (rank a))) y Hy)) as PICKy.
      destruct (pick (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a) \/ Aczel.eqTree (Aczel.childnodes kappa (rank z)) (Aczel.childnodes kappa (rank a))) x Hx)) as [[x' Hx'] | ] eqn:PICK_X; destruct (pick (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a) \/ Aczel.eqTree (Aczel.childnodes kappa (rank z)) (Aczel.childnodes kappa (rank a))) y Hy)) as [[y' Hy'] | ] eqn:PICK_Y; simpl in *.
      + injection EQ as STRICT_EQ. eapply Cardinal2.sig_eq_from_proj1. simpl.
        rewrite <- PICKx. rewrite <- PICKy. exact STRICT_EQ.
      + discriminate EQ.
      + discriminate EQ.
      + eapply Cardinal2.sig_eq_from_proj1. simpl.
        assert (RANK_EQ : rank x == rank y).
        { transitivity (rank a); [exact PICKx | symmetry; exact PICKy]. }
        pose proof (proj1 (enum_inj (rank x) (rank y)) RANK_EQ) as ENUM_EQ. now rewrite 2 RANK in ENUM_EQ.
  }
  eapply Cardinal1.Cardinality_le_lt_lt.
  - unfold Idx in IDX_LE. exact IDX_LE.
  - eapply Cardinal2.Cardinality_ofType_option_lt_of_lt_uncountable.
    + unfold StrictIdx. eapply Cardinality_ofType_rank_strict_initial_segment_lt; eauto.
    + exact UNCOUNTABLE.
Qed.

Section SQUARE_ABSORPTION.

Variable A : Type@{Set_u}.

Variable nat_embed : nat -> A.

Hypothesis nat_embed_inj : forall n : nat, forall m : nat, nat_embed n = nat_embed m -> n = m.

Record square_state : Type :=
  mk_square_state
  { st_carrier : Type@{Set_u}
  ; st_isSetoid : isSetoid st_carrier
  ; st_emb : st_carrier -> A
  ; st_emb_cong : forall x : st_carrier, forall y : st_carrier, @eqProp st_carrier st_isSetoid x y -> st_emb x = st_emb y
  ; st_emb_inj : forall x : st_carrier, forall y : st_carrier, st_emb x = st_emb y -> @eqProp st_carrier st_isSetoid x y
  ; st_nat : nat -> st_carrier
  ; st_nat_emb : forall n : nat, st_emb (st_nat n) = nat_embed n
  ; st_code : st_carrier * st_carrier -> st_carrier
  ; st_code_cong : forall x1 : st_carrier, forall x2 : st_carrier, forall y1 : st_carrier, forall y2 : st_carrier, @eqProp st_carrier st_isSetoid x1 x2 -> @eqProp st_carrier st_isSetoid y1 y2 -> @eqProp st_carrier st_isSetoid (st_code (x1, y1)) (st_code (x2, y2))
  ; st_code_inj : forall x1 : st_carrier, forall x2 : st_carrier, forall y1 : st_carrier, forall y2 : st_carrier, @eqProp st_carrier st_isSetoid (st_code (x1, y1)) (st_code (x2, y2)) -> @eqProp st_carrier st_isSetoid x1 x2 /\ @eqProp st_carrier st_isSetoid y1 y2
  }.

Definition state_card (s : square_state) : Cardinality.t :=
  Cardinality.mk (st_carrier s) (st_isSetoid s).

Lemma st_nat_inj (s : square_state) (n : nat) (m : nat)
  (EQ : @eqProp (st_carrier s) (st_isSetoid s) (st_nat s n) (st_nat s m))
  : n = m.
Proof.
  eapply nat_embed_inj. rewrite <- (st_nat_emb s n). rewrite <- (st_nat_emb s m). now eapply st_emb_cong.
Qed.

Definition square_state_initial
  : square_state.
Proof.
  refine (
    {|
      st_carrier := nat;
      st_isSetoid := mkSetoid_from_eq;
      st_emb := nat_embed;
      st_emb_cong := _;
      st_emb_inj := _;
      st_nat := fun n : nat => n;
      st_nat_emb := fun _ : nat => eq_refl;
      st_code := fun xy : nat * nat => cpInv (Datatypes.fst xy) (Datatypes.snd xy);
      st_code_cong := _;
      st_code_inj := _;
    |}
  ).
  - intros x y EQ. change (x = y) in EQ. subst y. reflexivity.
  - intros x y EQ. eapply nat_embed_inj. exact EQ.
  - intros x1 x2 y1 y2 EQ_x EQ_y. change (x1 = x2) in EQ_x. change (y1 = y2) in EQ_y. now subst x2 y2.
  - intros x1 x2 y1 y2 EQ. eapply cpInv_inj. exact EQ.
Defined.

Record state_embedding (s : square_state) (t : square_state) : Type :=
  mk_state_embedding
  { st_lift : st_carrier s -> st_carrier t
  ; st_lift_cong : forall x : st_carrier s, forall y : st_carrier s, @eqProp (st_carrier s) (st_isSetoid s) x y -> @eqProp (st_carrier t) (st_isSetoid t) (st_lift x) (st_lift y)
  ; st_lift_emb : forall x : st_carrier s, st_emb t (st_lift x) = st_emb s x
  ; st_lift_code : forall x : st_carrier s, forall y : st_carrier s, @eqProp (st_carrier t) (st_isSetoid t) (st_lift (st_code s (x, y))) (st_code t (st_lift x, st_lift y))
  }.

Definition state_le (s : square_state) (t : square_state) : Prop :=
  exists emb : state_embedding s t, True.

#[local]
Instance state_le_PreOrder
  : PreOrder state_le.
Proof.
  split.
  - intro s.
    exists (
      {|
        st_lift := fun x : st_carrier s => x;
        st_lift_cong := fun _ _ H => H;
        st_lift_emb := fun _ => eq_refl;
        st_lift_code := fun _ _ => eqProp_refl _;
      |}
    ).
    exact I.
  - intros s t u [emb_st _] [emb_tu _].
    unshelve eexists (
      {|
        st_lift := fun x : st_carrier s => st_lift t u emb_tu (st_lift s t emb_st x);
        st_lift_cong := fun x y H => st_lift_cong t u emb_tu _ _ (st_lift_cong s t emb_st _ _ H);
        st_lift_emb := _;
        st_lift_code := _;
      |}
    ); [simpl | simpl | exact I].
    + intro x. rewrite st_lift_emb. eapply st_lift_emb.
    + intros x y. transitivity (st_lift t u emb_tu (st_code t (st_lift s t emb_st x, st_lift s t emb_st y))).
      * eapply st_lift_cong. eapply st_lift_code.
      * eapply st_lift_code.
Qed.

#[local]
Instance square_state_isProset : isProset square_state :=
  { leProp := state_le
  ; Proset_isSetoid := mkSetoidFromPreOrder state_le_PreOrder
  ; leProp_PreOrder := state_le_PreOrder
  ; leProp_PartialOrder := mkSetoidFromPreOrder_good state_le_PreOrder
  }.

Definition state_encode_sum (s : square_state) (x : st_carrier s + st_carrier s) : st_carrier s :=
  match x with
  | inl a => st_code s (st_nat s O, a)
  | inr a => st_code s (st_nat s (S O), a)
  end.

Definition state_sum_isSetoid (s : square_state) : isSetoid (st_carrier s + st_carrier s) :=
  @sum_isSetoid (st_carrier s) (st_carrier s) (st_isSetoid s) (st_isSetoid s).

Definition state_sum_prod_isSetoid (s : square_state) : isSetoid ((st_carrier s + st_carrier s) * (st_carrier s + st_carrier s)) :=
  @prod_isSetoid _ _ (state_sum_isSetoid s) (state_sum_isSetoid s).

Lemma state_encode_sum_cong (s : square_state)
  : forall x : st_carrier s + st_carrier s, forall y : st_carrier s + st_carrier s, @eqProp (st_carrier s + st_carrier s) (state_sum_isSetoid s) x y -> @eqProp (st_carrier s) (st_isSetoid s) (state_encode_sum s x) (state_encode_sum s y).
Proof.
  intros [x | x] [y | y] EQ; inv EQ; simpl.
  - eapply st_code_cong; [reflexivity | exact x_corres].
  - eapply st_code_cong; [reflexivity | exact y_corres].
Qed.

Lemma state_encode_sum_inj (s : square_state)
  : forall x : st_carrier s + st_carrier s, forall y : st_carrier s + st_carrier s, @eqProp (st_carrier s) (st_isSetoid s) (state_encode_sum s x) (state_encode_sum s y) -> @eqProp (st_carrier s + st_carrier s) (state_sum_isSetoid s) x y.
Proof.
  intros [x | x] [y | y] EQ; simpl in EQ.
  - pose proof (st_code_inj s (st_nat s O) (st_nat s O) x y EQ) as [_ EQ_xy]. econs. exact EQ_xy.
  - pose proof (st_code_inj s (st_nat s O) (st_nat s (S O)) x y EQ) as [EQ_tag _].
    pose proof (st_nat_inj s O (S O) EQ_tag) as BAD. discriminate BAD.
  - pose proof (st_code_inj s (st_nat s (S O)) (st_nat s O) x y EQ) as [EQ_tag _].
    pose proof (st_nat_inj s (S O) O EQ_tag) as BAD. discriminate BAD.
  - pose proof (st_code_inj s (st_nat s (S O)) (st_nat s (S O)) x y EQ) as [_ EQ_xy]. econs. exact EQ_xy.
Qed.

Definition state_encode_pair (s : square_state) (xy : (st_carrier s + st_carrier s) * (st_carrier s + st_carrier s)) : st_carrier s :=
  st_code s (state_encode_sum s (Datatypes.fst xy), state_encode_sum s (Datatypes.snd xy)).

Lemma state_encode_pair_cong (s : square_state)
  : forall p : (st_carrier s + st_carrier s) * (st_carrier s + st_carrier s), forall q : (st_carrier s + st_carrier s) * (st_carrier s + st_carrier s), @eqProp ((st_carrier s + st_carrier s) * (st_carrier s + st_carrier s)) (state_sum_prod_isSetoid s) p q -> @eqProp (st_carrier s) (st_isSetoid s) (state_encode_pair s p) (state_encode_pair s q).
Proof.
  intros [x1 y1] [x2 y2] [EQ_x EQ_y]. simpl.
  eapply st_code_cong; eapply state_encode_sum_cong; assumption.
Qed.

Lemma state_encode_pair_inj (s : square_state)
  : forall p : (st_carrier s + st_carrier s) * (st_carrier s + st_carrier s), forall q : (st_carrier s + st_carrier s) * (st_carrier s + st_carrier s), @eqProp (st_carrier s) (st_isSetoid s) (state_encode_pair s p) (state_encode_pair s q) -> @eqProp ((st_carrier s + st_carrier s) * (st_carrier s + st_carrier s)) (state_sum_prod_isSetoid s) p q.
Proof.
  intros [x1 y1] [x2 y2] EQ. simpl in EQ.
  pose proof (st_code_inj s (state_encode_sum s x1) (state_encode_sum s x2) (state_encode_sum s y1) (state_encode_sum s y2) EQ) as [EQ_x EQ_y].
  split; eapply state_encode_sum_inj; assumption.
Qed.

Definition square_state_extend (s : square_state) (fresh : st_carrier s -> A)
  (fresh_cong : forall x : st_carrier s, forall y : st_carrier s, @eqProp (st_carrier s) (st_isSetoid s) x y -> fresh x = fresh y)
  (fresh_inj : forall x : st_carrier s, forall y : st_carrier s, fresh x = fresh y -> @eqProp (st_carrier s) (st_isSetoid s) x y)
  (fresh_out : forall x : st_carrier s, forall y : st_carrier s, fresh x <> st_emb s y)
  : square_state.
Proof.
  pose (B := st_carrier s).
  pose (B_isSetoid := st_isSetoid s).
  refine (
    {|
      st_carrier := B + B;
      st_isSetoid := @sum_isSetoid B B B_isSetoid B_isSetoid;
      st_emb := fun x : B + B => match x with inl b => st_emb s b | inr b => fresh b end;
      st_emb_cong := _;
      st_emb_inj := _;
      st_nat := fun n : nat => inl (st_nat s n);
      st_nat_emb := _;
      st_code := fun xy : (B + B) * (B + B) => match Datatypes.fst xy, Datatypes.snd xy with inl x, inl y => inl (st_code s (x, y)) | _, _ => inr (state_encode_pair s xy) end;
      st_code_cong := _;
      st_code_inj := _;
    |}
  ).
  - intros [x | x] [y | y] EQ; inv EQ; simpl.
    + eapply st_emb_cong. exact x_corres.
    + eapply fresh_cong. exact y_corres.
  - intros [x | x] [y | y] EQ; simpl in EQ.
    + econs. eapply st_emb_inj. exact EQ.
    + exfalso. exact (fresh_out y x (eq_sym EQ)).
    + exfalso. exact (fresh_out x y EQ).
    + econs. eapply fresh_inj. exact EQ.
  - intro n. eapply st_nat_emb.
  - intros [x1 | x1] [x2 | x2] [y1 | y1] [y2 | y2] EQ_x EQ_y; inv EQ_x; inv EQ_y; simpl.
    + econs. eapply st_code_cong; eauto.
    + econs. eapply state_encode_pair_cong. split; econs; eauto.
    + econs. eapply state_encode_pair_cong. split; econs; eauto.
    + econs. eapply state_encode_pair_cong. split; econs; eauto.
  - intros [x1 | x1] [x2 | x2] [y1 | y1] [y2 | y2] EQ; simpl in EQ; inv EQ.
    + pose proof (st_code_inj s x1 x2 y1 y2 x_corres) as [EQ_x EQ_y]. split; econs; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
Defined.

Lemma square_state_extend_exists (s : square_state) (fresh : st_carrier s -> A)
  (fresh_cong : forall x : st_carrier s, forall y : st_carrier s, @eqProp (st_carrier s) (st_isSetoid s) x y -> fresh x = fresh y)
  (fresh_inj : forall x : st_carrier s, forall y : st_carrier s, fresh x = fresh y -> @eqProp (st_carrier s) (st_isSetoid s) x y)
  (fresh_out : forall x : st_carrier s, forall y : st_carrier s, fresh x <> st_emb s y)
  : exists t : square_state, state_le s t.
Proof.
  exists (square_state_extend s fresh fresh_cong fresh_inj fresh_out).
  unfold state_le. cbn. eexists; [change (state_embedding s (square_state_extend s fresh fresh_cong fresh_inj fresh_out)) | exact I].
  unshelve refine (
    {|
      st_lift := fun x : st_carrier s => (inl x : st_carrier (square_state_extend s fresh fresh_cong fresh_inj fresh_out));
      st_lift_cong := _;
      st_lift_emb := _;
      st_lift_code := _;
    |}
  ).
  - intros x y H. econs. exact H.
  - intro x. reflexivity.
  - intros x y. reflexivity.
Qed.

End SQUARE_ABSORPTION.

Section GRAPH_SQUARE_ABSORPTION.

#[local] Infix "\in" := E.In : type_scope.

Variable A : Type@{Set_u}.

Variable nat_embed : nat -> A.

Hypothesis nat_embed_inj : forall n : nat, forall m : nat, nat_embed n = nat_embed m -> n = m.

Record graph_state : Type@{Set_u} :=
  mk_graph_state
  { gs_carrier : A -> Prop
  ; gs_nat : forall n : nat, gs_carrier (nat_embed n)
  ; gs_code : A -> A -> A -> Prop
  ; gs_code_dom : forall x : A, forall y : A, forall z : A, gs_code x y z -> gs_carrier x /\ gs_carrier y /\ gs_carrier z
  ; gs_code_total : forall x : A, forall y : A, gs_carrier x -> gs_carrier y -> exists z : A, gs_code x y z
  ; gs_code_functional : forall x : A, forall y : A, forall z1 : A, forall z2 : A, gs_code x y z1 -> gs_code x y z2 -> z1 = z2
  ; gs_code_inj : forall x1 : A, forall y1 : A, forall z1 : A, forall x2 : A, forall y2 : A, forall z2 : A, gs_code x1 y1 z1 -> gs_code x2 y2 z2 -> z1 = z2 -> x1 = x2 /\ y1 = y2
  }.

Definition graph_state_le (s : graph_state) (t : graph_state) : Prop :=
  (forall a : A, gs_carrier s a -> gs_carrier t a) /\ (forall x : A, forall y : A, forall z : A, gs_code s x y z -> gs_code t x y z).

#[local]
Instance graph_state_le_PreOrder
  : PreOrder graph_state_le.
Proof.
  split.
  - intros s. split; eauto.
  - intros s t u LE_st LE_tu. split.
    + intros a Ha. exact (proj1 LE_tu a (proj1 LE_st a Ha)).
    + intros x y z Hcode. exact (proj2 LE_tu x y z (proj2 LE_st x y z Hcode)).
Qed.

#[local]
Instance graph_state_isProset : isProset graph_state :=
  { leProp := graph_state_le
  ; Proset_isSetoid := mkSetoidFromPreOrder graph_state_le_PreOrder
  ; leProp_PreOrder := graph_state_le_PreOrder
  ; leProp_PartialOrder := mkSetoidFromPreOrder_good graph_state_le_PreOrder
  }.

Definition graph_state_initial_code (x : A) (y : A) (z : A) : Prop :=
  exists n : nat, exists m : nat, x = nat_embed n /\ y = nat_embed m /\ z = nat_embed (cpInv n m).

Definition graph_state_initial
  : graph_state.
Proof.
  refine (
    {|
      gs_carrier := fun a : A => exists n : nat, a = nat_embed n;
      gs_nat := _;
      gs_code := graph_state_initial_code;
      gs_code_dom := _;
      gs_code_total := _;
      gs_code_functional := _;
      gs_code_inj := _;
    |}
  ).
  - intro n. exists n. reflexivity.
  - intros x y z (n & m & Hx & Hy & Hz). subst. splits; eauto.
  - intros x y (n & Hx) (m & Hy). subst. exists (nat_embed (cpInv n m)). exists n, m. splits; reflexivity.
  - intros x y z1 z2 (n1 & m1 & Hx1 & Hy1 & Hz1) (n2 & m2 & Hx2 & Hy2 & Hz2). subst.
    assert (n1 = n2) by now eapply nat_embed_inj.
    assert (m1 = m2) by now eapply nat_embed_inj.
    now subst n2 m2.
  - intros x1 y1 z1 x2 y2 z2 (n1 & m1 & Hx1 & Hy1 & Hz1) (n2 & m2 & Hx2 & Hy2 & Hz2) Hz. subst.
    pose proof (nat_embed_inj _ _ Hz) as Hpair. pose proof (cpInv_inj _ _ _ _ Hpair) as [Hn Hm]. subst n2 m2. split; reflexivity.
Defined.

Definition graph_state_chain_upperbound (C : ensemble graph_state)
  (NONEMPTY : exists s : graph_state, s \in C)
  (CHAIN : forall s1 : graph_state, forall s2 : graph_state, s1 \in C -> s2 \in C -> graph_state_le s1 s2 \/ graph_state_le s2 s1)
  : exists u : graph_state, forall s : graph_state, s \in C -> graph_state_le s u.
Proof.
  destruct NONEMPTY as [s0 IN0]. unshelve eexists.
  { refine (
      {|
        gs_carrier := fun a : A => exists s : graph_state, s \in C /\ gs_carrier s a;
        gs_nat := _;
        gs_code := fun x : A => fun y : A => fun z : A => exists s : graph_state, s \in C /\ gs_code s x y z;
        gs_code_dom := _;
        gs_code_total := _;
        gs_code_functional := _;
        gs_code_inj := _;
      |}
    ).
    - intros n. exists s0. split; [exact IN0 | exact (gs_nat s0 n)].
    - intros x y z (s & INs & Hcode). pose proof (gs_code_dom s x y z Hcode) as (Hx & Hy & Hz). splits; exists s; split; assumption.
    - intros x y (sx & INx & Hx) (sy & INy & Hy). pose proof (CHAIN sx sy INx INy) as [LE | LE].
      + pose proof (gs_code_total sy x y (proj1 LE x Hx) Hy) as [z Hcode]. exists z. exists sy. split; assumption.
      + pose proof (gs_code_total sx x y Hx (proj1 LE y Hy)) as [z Hcode]. exists z. exists sx. split; assumption.
    - intros x y z1 z2 (s1 & IN1 & Hcode1) (s2 & IN2 & Hcode2). pose proof (CHAIN s1 s2 IN1 IN2) as [LE | LE].
      + eapply gs_code_functional; [exact (proj2 LE x y z1 Hcode1) | exact Hcode2].
      + eapply gs_code_functional; [exact Hcode1 | exact (proj2 LE x y z2 Hcode2)].
    - intros x1 y1 z1 x2 y2 z2 (s1 & IN1 & Hcode1) (s2 & IN2 & Hcode2) Hz. pose proof (CHAIN s1 s2 IN1 IN2) as [LE | LE].
      + eapply gs_code_inj; [exact (proj2 LE x1 y1 z1 Hcode1) | exact Hcode2 | exact Hz].
      + eapply gs_code_inj; [exact Hcode1 | exact (proj2 LE x2 y2 z2 Hcode2) | exact Hz].
  }
  intros s INs. split.
  - intros a Ha. exists s. split; assumption.
  - intros x y z Hcode. exists s. split; assumption.
Defined.

Lemma graph_state_maximal_exists
  : exists m : graph_state, forall t : graph_state, graph_state_le m t -> graph_state_le t m.
Proof.
  eapply Zorn's_lemma with (D := graph_state) (PROSET := graph_state_isProset).
  - econs. exact graph_state_initial.
  - intros C NONEMPTY CHAIN. eapply graph_state_chain_upperbound; eauto.
Qed.

Definition graph_state_type (s : graph_state) : Type@{Set_u} :=
  { a : A | gs_carrier s a }.

Definition graph_state_nat (s : graph_state) (n : nat) : graph_state_type s :=
  @exist A (gs_carrier s) (nat_embed n) (gs_nat s n).

Lemma graph_state_nat_inj (s : graph_state) (n : nat) (m : nat)
  (EQ : graph_state_nat s n = graph_state_nat s m)
  : n = m.
Proof.
  eapply nat_embed_inj. injection EQ as EQ_proj. exact EQ_proj.
Qed.

Definition graph_sum_type (s : graph_state) : Type@{Set_u} :=
  (graph_state_type s + graph_state_type s)%type.

Definition graph_pair_type (s : graph_state) : Type@{Set_u} :=
  (graph_sum_type s * graph_sum_type s)%type.

Inductive graph_sum_code (s : graph_state) : graph_sum_type s -> graph_state_type s -> Prop :=
  | graph_sum_code_l (x : graph_state_type s) (b : graph_state_type s)
    (CODE : gs_code s (nat_embed O) (proj1_sig x) (proj1_sig b))
    : graph_sum_code s (inl x) b
  | graph_sum_code_r (x : graph_state_type s) (b : graph_state_type s)
    (CODE : gs_code s (nat_embed (S O)) (proj1_sig x) (proj1_sig b))
    : graph_sum_code s (inr x) b.

Lemma graph_sum_code_total (s : graph_state) (x : graph_sum_type s)
  : exists b : graph_state_type s, graph_sum_code s x b.
Proof.
  destruct x as [x | x].
  - pose proof (gs_code_total s (nat_embed O) (proj1_sig x) (gs_nat s O) (proj2_sig x)) as [b Hcode].
    pose proof (gs_code_dom s _ _ _ Hcode) as (_ & _ & Hb). exists (@exist A (gs_carrier s) b Hb). econs. exact Hcode.
  - pose proof (gs_code_total s (nat_embed (S O)) (proj1_sig x) (gs_nat s (S O)) (proj2_sig x)) as [b Hcode].
    pose proof (gs_code_dom s _ _ _ Hcode) as (_ & _ & Hb). exists (@exist A (gs_carrier s) b Hb). econs. exact Hcode.
Qed.

Lemma graph_sum_code_functional (s : graph_state) (x : graph_sum_type s) (b1 : graph_state_type s) (b2 : graph_state_type s)
  (CODE1 : graph_sum_code s x b1)
  (CODE2 : graph_sum_code s x b2)
  : b1 = b2.
Proof.
  destruct x as [x | x]; inv CODE1; inv CODE2; eapply Cardinal2.sig_eq_from_proj1; eapply gs_code_functional; eauto.
Qed.

Lemma graph_sum_code_inj (s : graph_state) (x1 : graph_sum_type s) (x2 : graph_sum_type s) (b1 : graph_state_type s) (b2 : graph_state_type s)
  (CODE1 : graph_sum_code s x1 b1)
  (CODE2 : graph_sum_code s x2 b2)
  (EQ : b1 = b2)
  : x1 = x2.
Proof.
  subst b2.
  destruct x1 as [x1 | x1], x2 as [x2 | x2]; inv CODE1; inv CODE2.
  - pose proof (gs_code_inj s _ _ _ _ _ _ CODE CODE0 eq_refl) as [_ EQ_x]. f_equal. eapply Cardinal2.sig_eq_from_proj1. exact EQ_x.
  - pose proof (gs_code_inj s _ _ _ _ _ _ CODE CODE0 eq_refl) as [EQ_tag _].
    pose proof (nat_embed_inj O (S O) EQ_tag) as BAD. discriminate BAD.
  - pose proof (gs_code_inj s _ _ _ _ _ _ CODE CODE0 eq_refl) as [EQ_tag _].
    pose proof (nat_embed_inj (S O) O EQ_tag) as BAD. discriminate BAD.
  - pose proof (gs_code_inj s _ _ _ _ _ _ CODE CODE0 eq_refl) as [_ EQ_x]. f_equal. eapply Cardinal2.sig_eq_from_proj1. exact EQ_x.
Qed.

Inductive graph_pair_code (s : graph_state) : graph_pair_type s -> graph_state_type s -> Prop :=
  | graph_pair_code_intro (x : graph_sum_type s) (y : graph_sum_type s) (bx : graph_state_type s) (by0 : graph_state_type s) (b : graph_state_type s)
    (CODE_x : graph_sum_code s x bx)
    (CODE_y : graph_sum_code s y by0)
    (CODE : gs_code s (proj1_sig bx) (proj1_sig by0) (proj1_sig b))
    : graph_pair_code s (x, y) b.

Lemma graph_pair_code_total (s : graph_state) (p : graph_pair_type s)
  : exists b : graph_state_type s, graph_pair_code s p b.
Proof.
  destruct p as [x y]. pose proof (graph_sum_code_total s x) as [bx CODE_x]. pose proof (graph_sum_code_total s y) as [by0 CODE_y].
  pose proof (gs_code_total s (proj1_sig bx) (proj1_sig by0) (proj2_sig bx) (proj2_sig by0)) as [b CODE].
  pose proof (gs_code_dom s _ _ _ CODE) as (_ & _ & Hb). exists (@exist A (gs_carrier s) b Hb). econs; eauto.
Qed.

Lemma graph_pair_code_functional (s : graph_state) (p : graph_pair_type s) (b1 : graph_state_type s) (b2 : graph_state_type s)
  (CODE1 : graph_pair_code s p b1)
  (CODE2 : graph_pair_code s p b2)
  : b1 = b2.
Proof.
  inv CODE1. inv CODE2. pose proof (graph_sum_code_functional s _ _ _ CODE_x CODE_x0). subst bx0.
  pose proof (graph_sum_code_functional s _ _ _ CODE_y CODE_y0). subst by0.
  eapply Cardinal2.sig_eq_from_proj1. eapply gs_code_functional; eauto.
Qed.

Lemma graph_pair_code_inj (s : graph_state) (p1 : graph_pair_type s) (p2 : graph_pair_type s) (b1 : graph_state_type s) (b2 : graph_state_type s)
  (CODE1 : graph_pair_code s p1 b1)
  (CODE2 : graph_pair_code s p2 b2)
  (EQ : b1 = b2)
  : p1 = p2.
Proof.
  subst b2. inv CODE1. inv CODE2.
  pose proof (gs_code_inj s _ _ _ _ _ _ CODE CODE0 eq_refl) as [EQ_bx EQ_by].
  pose proof (graph_sum_code_inj s _ _ _ _ CODE_x CODE_x0 (Cardinal2.sig_eq_from_proj1 _ _ EQ_bx)) as EQ_x.
  pose proof (graph_sum_code_inj s _ _ _ _ CODE_y CODE_y0 (Cardinal2.sig_eq_from_proj1 _ _ EQ_by)) as EQ_y.
  subst. reflexivity.
Qed.

Definition graph_state_complement_type (s : graph_state) : Type@{Set_u} :=
  { a : A | ~ gs_carrier s a }.

Inductive graph_extend_repr (s : graph_state) (fresh : graph_state_type s -> graph_state_complement_type s) : A -> graph_sum_type s -> Prop :=
  | graph_extend_repr_old (b : graph_state_type s)
    : graph_extend_repr s fresh (proj1_sig b) (inl b)
  | graph_extend_repr_new (b : graph_state_type s)
    : graph_extend_repr s fresh (proj1_sig (fresh b)) (inr b).

Definition graph_extend_nonold (s : graph_state) (p : graph_pair_type s) : Prop :=
  match p with
  | (inl _, inl _) => False
  | _ => True
  end.

Lemma graph_extend_repr_unique (s : graph_state) (fresh : graph_state_type s -> graph_state_complement_type s) (a : A) (x : graph_sum_type s) (y : graph_sum_type s)
  (fresh_inj : forall b1 : graph_state_type s, forall b2 : graph_state_type s, proj1_sig (fresh b1) = proj1_sig (fresh b2) -> b1 = b2)
  (REPR_x : graph_extend_repr s fresh a x)
  (REPR_y : graph_extend_repr s fresh a y)
  : x = y.
Proof.
  inv REPR_x; inv REPR_y.
  - f_equal. eapply Cardinal2.sig_eq_from_proj1. symmetry. exact H0.
  - destruct b as [a Ha]. simpl in H0. subst a. contradiction (proj2_sig (fresh b0)).
  - destruct b0 as [a Ha]. simpl in H0. subst a. contradiction (proj2_sig (fresh b)).
  - f_equal. eapply fresh_inj. symmetry. exact H0.
Qed.

Lemma graph_extend_repr_same (s : graph_state) (fresh : graph_state_type s -> graph_state_complement_type s)
  (a : A) (b : A) (x : graph_sum_type s)
  (REPR_a : graph_extend_repr s fresh a x)
  (REPR_b : graph_extend_repr s fresh b x)
  : a = b.
Proof.
  inv REPR_a; inv REPR_b; reflexivity.
Qed.

Inductive graph_extend_code (s : graph_state) (fresh : graph_state_type s -> graph_state_complement_type s) : A -> A -> A -> Prop :=
  | graph_extend_code_old (x : A) (y : A) (z : A)
    (CODE : gs_code s x y z)
    : graph_extend_code s fresh x y z
  | graph_extend_code_new (x : A) (y : A) (z : A) (sx : graph_sum_type s) (sy : graph_sum_type s) (b : graph_state_type s)
    (REPR_x : graph_extend_repr s fresh x sx)
    (REPR_y : graph_extend_repr s fresh y sy)
    (NONOLD : graph_extend_nonold s (sx, sy))
    (CODE : graph_pair_code s (sx, sy) b)
    (EQ_z : z = proj1_sig (fresh b))
    : graph_extend_code s fresh x y z.

Lemma graph_extend_repr_of_carrier (s : graph_state) (fresh : graph_state_type s -> graph_state_complement_type s) (a : A)
  (Ha : exists x : graph_sum_type s, graph_extend_repr s fresh a x)
  : gs_carrier s a \/ exists b : graph_state_type s, a = proj1_sig (fresh b).
Proof.
  destruct Ha as [x Hx]. inv Hx.
  - left. exact (proj2_sig b).
  - right. exists b. reflexivity.
Qed.

Definition graph_state_extend (s : graph_state) (fresh : graph_state_type s -> graph_state_complement_type s)
  (fresh_inj : forall b1 : graph_state_type s, forall b2 : graph_state_type s, proj1_sig (fresh b1) = proj1_sig (fresh b2) -> b1 = b2)
  : graph_state.
Proof.
  refine (
    {|
      gs_carrier := fun a : A => exists x : graph_sum_type s, graph_extend_repr s fresh a x;
      gs_nat := _;
      gs_code := graph_extend_code s fresh;
      gs_code_dom := _;
      gs_code_total := _;
      gs_code_functional := _;
      gs_code_inj := _;
    |}
  ).
  - intros n. exists (inl (graph_state_nat s n)).
    change (graph_extend_repr s fresh (proj1_sig (graph_state_nat s n)) (inl (graph_state_nat s n))). eapply graph_extend_repr_old.
  - intros x y z Hcode. inv Hcode.
    + pose proof (gs_code_dom s x y z CODE) as (Hx & Hy & Hz). splits.
      * exists (inl (@exist A (gs_carrier s) x Hx)). change (graph_extend_repr s fresh (proj1_sig (@exist A (gs_carrier s) x Hx)) (inl (@exist A (gs_carrier s) x Hx))). eapply graph_extend_repr_old.
      * exists (inl (@exist A (gs_carrier s) y Hy)). change (graph_extend_repr s fresh (proj1_sig (@exist A (gs_carrier s) y Hy)) (inl (@exist A (gs_carrier s) y Hy))). eapply graph_extend_repr_old.
      * exists (inl (@exist A (gs_carrier s) z Hz)). change (graph_extend_repr s fresh (proj1_sig (@exist A (gs_carrier s) z Hz)) (inl (@exist A (gs_carrier s) z Hz))). eapply graph_extend_repr_old.
    + splits; [exists sx | exists sy | exists (inr b)]; eauto using graph_extend_repr_new.
  - intros x y [sx REPR_x] [sy REPR_y]. destruct sx as [bx | bx], sy as [by0 | by0].
    + pose proof (gs_code_total s x y) as [z CODE].
      { inv REPR_x. exact (proj2_sig bx). }
      { inv REPR_y. exact (proj2_sig by0). }
      exists z. econs. exact CODE.
    + pose proof (graph_pair_code_total s (inl bx, inr by0)) as [b CODE]. exists (proj1_sig (fresh b)).
      eapply graph_extend_code_new with (sx := inl bx) (sy := inr by0) (b := b); eauto.
      simpl. exact I.
    + pose proof (graph_pair_code_total s (inr bx, inl by0)) as [b CODE]. exists (proj1_sig (fresh b)).
      eapply graph_extend_code_new with (sx := inr bx) (sy := inl by0) (b := b); eauto.
      simpl. exact I.
    + pose proof (graph_pair_code_total s (inr bx, inr by0)) as [b CODE]. exists (proj1_sig (fresh b)).
      eapply graph_extend_code_new with (sx := inr bx) (sy := inr by0) (b := b); eauto.
      simpl. exact I.
  - intros x y z1 z2 CODE1 CODE2. inv CODE1; inv CODE2.
    + eapply gs_code_functional; eauto.
    + pose proof (gs_code_dom s x y z1 CODE) as (Hx & Hy & _).
      pose proof (graph_extend_repr_unique s fresh x sx (inl (@exist A (gs_carrier s) x Hx)) fresh_inj REPR_x (graph_extend_repr_old s fresh (@exist A (gs_carrier s) x Hx))) as EQ_x.
      pose proof (graph_extend_repr_unique s fresh y sy (inl (@exist A (gs_carrier s) y Hy)) fresh_inj REPR_y (graph_extend_repr_old s fresh (@exist A (gs_carrier s) y Hy))) as EQ_y.
      subst sx sy. contradiction.
    + pose proof (gs_code_dom s x y z2 CODE0) as (Hx & Hy & _).
      pose proof (graph_extend_repr_unique s fresh x sx (inl (@exist A (gs_carrier s) x Hx)) fresh_inj REPR_x (graph_extend_repr_old s fresh (@exist A (gs_carrier s) x Hx))) as EQ_x.
      pose proof (graph_extend_repr_unique s fresh y sy (inl (@exist A (gs_carrier s) y Hy)) fresh_inj REPR_y (graph_extend_repr_old s fresh (@exist A (gs_carrier s) y Hy))) as EQ_y.
      subst sx sy. contradiction.
    + pose proof (graph_extend_repr_unique s fresh x sx sx0 fresh_inj REPR_x REPR_x0) as EQ_x.
      pose proof (graph_extend_repr_unique s fresh y sy sy0 fresh_inj REPR_y REPR_y0) as EQ_y.
      subst sx0 sy0. pose proof (graph_pair_code_functional s _ _ _ CODE CODE0) as EQ_b. subst b0. reflexivity.
  - intros x1 y1 z1 x2 y2 z2 CODE1 CODE2 EQ_z. inv CODE1; inv CODE2.
    + eapply gs_code_inj; eauto.
    + pose proof (gs_code_dom s _ _ _ CODE) as (_ & _ & Hz_old).
      destruct (fresh b) as [fb Hfb]. simpl in *. subst. contradiction.
    + pose proof (gs_code_dom s _ _ _ CODE0) as (_ & _ & Hz_old).
      destruct (fresh b) as [fb Hfb]. simpl in *. subst. contradiction.
    + pose proof (fresh_inj b b0 EQ_z) as EQ_b. subst b0.
      pose proof (graph_pair_code_inj s _ _ _ _ CODE CODE0 eq_refl) as EQ_pair. inv EQ_pair.
      split; eapply graph_extend_repr_same; eauto.
Defined.

Lemma graph_state_extend_le (s : graph_state) (fresh : graph_state_type s -> graph_state_complement_type s)
  (fresh_inj : forall b1 : graph_state_type s, forall b2 : graph_state_type s, proj1_sig (fresh b1) = proj1_sig (fresh b2) -> b1 = b2)
  : graph_state_le s (graph_state_extend s fresh fresh_inj).
Proof.
  split.
  - intros a Ha. exists (inl (@exist A (gs_carrier s) a Ha)).
    change (graph_extend_repr s fresh (proj1_sig (@exist A (gs_carrier s) a Ha)) (inl (@exist A (gs_carrier s) a Ha))). eapply graph_extend_repr_old.
  - intros x y z Hcode. econs. exact Hcode.
Qed.

Lemma graph_state_type_nat_le (s : graph_state)
  : Cardinality.ofType nat =< Cardinality.ofType (graph_state_type s).
Proof.
  eapply Cardinal2.Cardinality_ofType_le_ofType with (f := graph_state_nat s).
  intros n m EQ. eapply graph_state_nat_inj. exact EQ.
Qed.

Lemma graph_state_type_prod_le (s : graph_state)
  : Cardinality.ofType (graph_state_type s * graph_state_type s) =< Cardinality.ofType (graph_state_type s).
Proof.
  assert (Hchoice : forall p : graph_state_type s * graph_state_type s, exists b : graph_state_type s, gs_code s (proj1_sig (Datatypes.fst p)) (proj1_sig (Datatypes.snd p)) (proj1_sig b)).
  { intros [x y]. pose proof (gs_code_total s (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y)) as [z CODE].
    pose proof (gs_code_dom s _ _ _ CODE) as (_ & _ & Hz). exists (@exist A (gs_carrier s) z Hz). exact CODE.
  }
  pose proof (Axiom_of_Choice (graph_state_type s * graph_state_type s) (fun _ : graph_state_type s * graph_state_type s => graph_state_type s) (fun p : graph_state_type s * graph_state_type s => fun b : graph_state_type s => gs_code s (proj1_sig (Datatypes.fst p)) (proj1_sig (Datatypes.snd p)) (proj1_sig b)) Hchoice) as [code CODE].
  eapply Cardinal2.Cardinality_ofType_le_ofType with (f := code).
  intros [x1 y1] [x2 y2] EQ. change (code (x1, y1) = code (x2, y2)) in EQ.
  assert (EQ_proj : proj1_sig (code (x1, y1)) = proj1_sig (code (x2, y2))) by now rewrite EQ.
  pose proof (gs_code_inj s _ _ _ _ _ _ (CODE (x1, y1)) (CODE (x2, y2)) EQ_proj) as [EQ_x EQ_y].
  f_equal; eapply Cardinal2.sig_eq_from_proj1; assumption.
Qed.

Definition graph_cover_sum_type (s : graph_state) : Type@{Set_u} :=
  (graph_state_type s + graph_state_complement_type s)%type.

Definition graph_sum_proj (s : graph_state) (x : graph_cover_sum_type s) : A :=
  match x with
  | inl b => proj1_sig b
  | inr c => proj1_sig c
  end.

Lemma graph_state_cover_le_sum (s : graph_state)
  : Cardinality.ofType A =< Cardinality.ofType (graph_cover_sum_type s).
Proof.
  assert (Hchoice : forall a : A, exists x : graph_cover_sum_type s, graph_sum_proj s x = a).
  { intro a. pose proof (classic (gs_carrier s a)) as [Ha | Ha].
    - exists (inl (@exist A (gs_carrier s) a Ha)). reflexivity.
    - exists (inr (@exist A (fun x : A => ~ gs_carrier s x) a Ha)). reflexivity.
  }
  pose proof (Axiom_of_Choice A (fun _ : A => graph_cover_sum_type s) (fun a : A => fun x : graph_cover_sum_type s => graph_sum_proj s x = a) Hchoice) as [pick PICK].
  eapply Cardinal2.Cardinality_ofType_le_ofType with (f := pick).
  intros a1 a2 EQ. change (pick a1 = pick a2) in EQ. rewrite <- (PICK a1). rewrite <- (PICK a2). now rewrite EQ.
Qed.

Lemma graph_state_complement_le_carrier (m : graph_state)
  (MAX : forall t : graph_state, graph_state_le m t -> graph_state_le t m)
  : Cardinality.ofType (graph_state_complement_type m) =< Cardinality.ofType (graph_state_type m).
Proof.
  pose proof (Cardinal1.Cardinality_le_total (Cardinality.ofType (graph_state_type m)) (Cardinality.ofType (graph_state_complement_type m))) as [LE | LE].
  - destruct LE as [fresh fresh_cong fresh_inj].
    assert (fresh_inj_proj : forall b1 : graph_state_type m, forall b2 : graph_state_type m, proj1_sig (fresh b1) = proj1_sig (fresh b2) -> b1 = b2).
    { intros b1 b2 EQ. eapply fresh_inj. change (fresh b1 = fresh b2). eapply Cardinal2.sig_eq_from_proj1. exact EQ. }
    pose proof (MAX (graph_state_extend m fresh fresh_inj_proj) (graph_state_extend_le m fresh fresh_inj_proj)) as BACK.
    pose (b0 := graph_state_nat m O).
    pose proof (proj1 BACK (proj1_sig (fresh b0))) as IN_BACK.
    assert (IN_EXT : gs_carrier (graph_state_extend m fresh fresh_inj_proj) (proj1_sig (fresh b0))).
    { exists (inr b0). econs. }
    specialize (IN_BACK IN_EXT). exact (False_rect _ (proj2_sig (fresh b0) IN_BACK)).
  - exact LE.
Qed.

End GRAPH_SQUARE_ABSORPTION.

Theorem Cardinality_ofType_prod_self_le_of_nat_le (A : Type@{Set_u})
  (NAT_LE : Cardinality.ofType nat =< Cardinality.ofType A)
  : Cardinality.ofType (A * A) =< Cardinality.ofType A.
Proof.
  destruct NAT_LE as [nat_emb nat_emb_cong nat_emb_inj].
  assert (nat_emb_inj_raw : forall n : nat, forall m : nat, nat_emb n = nat_emb m -> n = m).
  { intros n m EQ. eapply nat_emb_inj. change (nat_emb n = nat_emb m). exact EQ. }
  pose proof (@graph_state_maximal_exists A nat_emb nat_emb_inj_raw) as [m MAX].
  pose proof (@graph_state_type_nat_le A nat_emb nat_emb_inj_raw m) as NAT_LE_B.
  pose proof (@graph_state_type_prod_le A nat_emb m) as PROD_B_LE_B.
  pose proof (@graph_state_complement_le_carrier A nat_emb nat_emb_inj_raw m MAX) as COMP_LE_B.
  assert (B_LE_A : Cardinality.ofType (graph_state_type A nat_emb m) =< Cardinality.ofType A).
  { eapply Cardinal2.Cardinality_ofType_sig_le. }
  assert (A_LE_B : Cardinality.ofType A =< Cardinality.ofType (graph_state_type A nat_emb m)).
  { transitivity (Cardinality.ofType (graph_cover_sum_type A nat_emb m)).
    - eapply graph_state_cover_le_sum.
    - transitivity (Cardinality.mul (Cardinality.ofType bool) (Cardinality.ofType (graph_state_type A nat_emb m))).
      + eapply Cardinal2.Cardinality_ofType_sum_le.
        * reflexivity.
        * exact COMP_LE_B.
      + transitivity (Cardinality.ofType (graph_state_type A nat_emb m * graph_state_type A nat_emb m)).
        * pose proof (Cardinal2.Cardinality_ofType_prod_eq bool (graph_state_type A nat_emb m)) as PROD_EQ. rewrite <- PROD_EQ.
          eapply Cardinal2.Cardinality_ofType_prod_le.
          { eapply Cardinality_ofType_bool_le_of_nat_le. exact NAT_LE_B. }
          { reflexivity. }
        * exact PROD_B_LE_B.
  }
  transitivity (Cardinality.ofType (graph_state_type A nat_emb m * graph_state_type A nat_emb m)).
  - eapply Cardinal2.Cardinality_ofType_prod_le; exact A_LE_B.
  - transitivity (Cardinality.ofType (graph_state_type A nat_emb m)); [exact PROD_B_LE_B | exact B_LE_A].
Qed.

Theorem Cardinality_ofType_rose_lt_of_lt_uncountable (A : Type@{Set_u}) (kappa : Cardinality.t)
  (LT : Cardinality.ofType A ≨ kappa)
  (UNCOUNTABLE : ~ kappa =< Cardinality.ofType nat)
  : Cardinality.ofType (Cardinal2.rose A) ≨ kappa.
Proof.
  eapply Cardinality_ofType_rose_lt_of_lt_uncountable_square_le; eauto.
  intros B NAT_LE. eapply Cardinality_ofType_prod_self_le_of_nat_le. exact NAT_LE.
Qed.

End CARDINALITY.

End Cardinal3.

Module Inaccessible.

Section CLASSICAL.

#[local] Existing Instance Ord_isProset.

Record inaccessible (X : Type@{Set_u}) (base : Ord.t) (next : Ord.t -> Ord.t) (k : Ord.t) : Prop :=
  mk_inaccessible
  { inaccessible_base : base <ᵣ k
  ; inaccessible_next : forall alpha : Ord.t, alpha <ᵣ k -> next alpha <ᵣ k
  ; inaccessible_join : forall os : X -> Ord.t, (forall x : X, os x <ᵣ k) -> Ord.sup X os <ᵣ k
  ; inaccessible_union : forall alpha : Ord.t, forall beta : Ord.t, alpha <ᵣ k -> beta <ᵣ k -> Ord_join alpha beta <ᵣ k
  }.

Record ginaccessible (X : Type@{Set_u}) (base : Ord.t) (next : Ord.t -> Ord.t) (k : Ord.t) : Prop :=
  mk_ginaccessible
  { ginaccessible_base : base <ᵣ k
  ; ginaccessible_next : forall alpha : Ord.t, alpha <ᵣ k -> next alpha <ᵣ k
  ; ginaccessible_join : forall P : X -> Prop, forall os : @sig X P -> Ord.t, (forall x : @sig X P, os x <ᵣ k) -> Ord.sup (@sig X P) os <ᵣ k
  ; ginaccessible_union : forall alpha : Ord.t, forall beta : Ord.t, alpha <ᵣ k -> beta <ᵣ k -> Ord_join alpha beta <ᵣ k
  }.

Context `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}.

Lemma inaccessible_mon (X0 : Type@{Set_u}) (X1 : Type@{Set_u}) (base0 : Ord.t) (base1 : Ord.t) (next0 : Ord.t -> Ord.t) (next1 : Ord.t -> Ord.t) (k : Ord.t)
  (H_surj : exists f : X1 -> X0, forall x0 : X0, exists x1 : X1, f x1 = x0)
  (H_base : base0 <ᵣ k)
  (H_next : forall alpha : Ord.t, alpha <ᵣ k -> next0 alpha ≦ᵣ next1 alpha)
  (H_inaccessible : inaccessible X1 base1 next1 k)
  : inaccessible X0 base0 next0 k.
Proof.
  destruct H_surj as [f H_surj]. econs.
  - exact H_base.
  - intros alpha H_rLt. eapply rLe_rLt_rLt.
    + eapply H_next. exact H_rLt.
    + eapply H_inaccessible. exact H_rLt.
  - intros os H_rLt. eapply rLe_rLt_rLt with (y := Ord.sup X1 (fun x1 : X1 => os (f x1))).
    + eapply Ord_sup_rLe_intro. intros x0. pose proof (H_surj x0) as [x1 H_eq]. subst x0.
      change ((fun x1 : X1 => os (f x1)) x1 ≦ᵣ Ord.sup X1 (fun x2 : X1 => os (f x2))). eapply Ord_rLe_sup_intro.
    + eapply H_inaccessible. intros x1. eapply H_rLt.
  - intros alpha beta H_rLt0 H_rLt1. eapply H_inaccessible; assumption.
Qed.

Lemma ginaccessible_inaccessible (X : Type@{Set_u}) (base : Ord.t) (next : Ord.t -> Ord.t) (k : Ord.t)
  (H_inaccessible : ginaccessible X base next k)
  : inaccessible X base next k.
Proof.
  econs.
  - eapply H_inaccessible.
  - eapply H_inaccessible.
  - intros os H_rLt. eapply rLe_rLt_rLt with (y := Ord.sup (@sig X (fun _ : X => True)) (fun x : @sig X (fun _ : X => True) => os (proj1_sig x))).
    + eapply Ord_sup_rLe_intro. intros x.
      change ((fun x : @sig X (fun _ : X => True) => os (proj1_sig x)) (@exist X (fun _ : X => True) x I) ≦ᵣ Ord.sup (@sig X (fun _ : X => True)) (fun x0 : @sig X (fun _ : X => True) => os (proj1_sig x0))).
      eapply Ord_rLe_sup_intro.
    + eapply H_inaccessible. intros x. eapply H_rLt.
  - eapply H_inaccessible.
Qed.

Inductive tree {X : Type@{Set_u}} : Type@{Set_u} :=
  | tree_O : @tree X
  | tree_S : @tree X -> @tree X
  | tree_join : (X -> @tree X) -> @tree X
  | tree_union : @tree X -> @tree X -> @tree X.

#[global] Arguments tree : clear implicits.

Definition tree_lt {X : Type@{Set_u}} (tr0 : tree X) (tr1 : tree X) : Prop :=
  match tr1 with
  | tree_O => False
  | tree_S tr => tr0 = tr
  | tree_join trs => exists x : X, tr0 = trs x
  | tree_union trl trr => tr0 = trl \/ tr0 = trr
  end.

Lemma tree_lt_well_founded (X : Type@{Set_u})
  : well_founded (@tree_lt X).
Proof.
  ii. induction a as [ | tr IH | trs IH | tr0 IH0 tr1 IH1].
  - econs. intros y H_rLt. contradiction.
  - econs. intros y H_rLt. simpl in H_rLt. subst y. exact IH.
  - econs. intros y H_rLt. simpl in H_rLt. destruct H_rLt as [x ->]. exact (IH x).
  - econs. intros y H_rLt. simpl in H_rLt. destruct H_rLt as [-> | ->]; assumption.
Qed.

Definition tree_top (X : Type@{Set_u}) : Ord.t :=
  @fromWfSet (tree X) (@tree_lt X) (tree_lt_well_founded X).

Lemma tree_O_rEq (X : Type@{Set_u})
  : @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tree_O =ᵣ Ord.zer.
Proof.
  rewrite rEq_iff. split.
  - eapply fromWf_isSupremum. intros y H_rLt. contradiction H_rLt.
  - eapply Ord_zer_rLe.
Qed.

Lemma tree_S_rEq (X : Type@{Set_u}) (tr : tree X)
  : @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_S tr) =ᵣ Ord.suc (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr).
Proof.
  rewrite rEq_iff. split.
  - eapply fromWf_isSupremum. intros y H_rLt. simpl in H_rLt. subst y. unfold Ord.suc. eapply rLt_succ_intro.
  - unfold Ord.suc. rewrite succ_rLe_iff. eapply member_implies_rLt. rewrite fromWf_unfold.
    exists tr. split; [reflexivity | reflexivity].
Qed.

Lemma tree_join_rEq (X : Type@{Set_u}) (trs : X -> tree X)
  : @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_join trs) =ᵣ mkNode X (fun x : X => @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (trs x)).
Proof.
  rewrite rEq_iff. split.
  - eapply fromWf_isSupremum. intros y H_rLt. simpl in H_rLt. destruct H_rLt as [x ->].
    eapply member_implies_rLt. exists x. reflexivity.
  - econs. intros x. eapply member_implies_rLt. rewrite fromWf_unfold.
    exists (trs x). split; [now exists x | reflexivity].
Qed.

Lemma tree_union_le (X : Type@{Set_u}) (tr0 : tree X) (tr1 : tree X)
  : @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_union tr0 tr1) ≦ᵣ Ord.suc (Ord_join (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0) (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1)).
Proof.
  eapply fromWf_isSupremum. intros y H_rLt. simpl in H_rLt. unfold Ord.suc. rewrite rLt_succ_iff. destruct H_rLt as [-> | ->].
  - eapply Ord_join_l.
  - eapply Ord_join_r.
Qed.

Lemma tree_union_le_rev (X : Type@{Set_u}) (tr0 : tree X) (tr1 : tree X)
  : Ord_join (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0) (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1) ≦ᵣ @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_union tr0 tr1).
Proof.
  eapply Ord_join_spec; eapply rLt_implies_rLe; eapply member_implies_rLt; rewrite fromWf_unfold.
  - exists tr0. split; [now left | reflexivity].
  - exists tr1. split; [now right | reflexivity].
Qed.

Lemma tree_top_O (X : Type@{Set_u})
  : Ord.zer <ᵣ tree_top X.
Proof.
  eapply rLe_rLt_rLt with (y := @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tree_O).
  - exact (proj2 (tree_O_rEq X)).
  - eapply member_implies_rLt. exists tree_O. reflexivity.
Qed.

Lemma tree_top_S (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ tree_top X)
  : Ord.suc alpha <ᵣ tree_top X.
Proof.
  destruct H_rLt as [[tr H_rLe]]. eapply rLe_rLt_rLt with (y := @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_S tr)).
  - transitivity (Ord.suc (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr)).
    + eapply Ord_suc_rLe. exact H_rLe.
    + exact (proj2 (tree_S_rEq X tr)).
  - eapply member_implies_rLt. exists (tree_S tr). reflexivity.
Qed.

Lemma tree_top_union (X : Type@{Set_u}) (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ tree_top X)
  (H_rLt1 : beta <ᵣ tree_top X)
  : Ord_join alpha beta <ᵣ tree_top X.
Proof.
  destruct H_rLt0 as [[tr0 H_rLe0]], H_rLt1 as [[tr1 H_rLe1]].
  eapply rLe_rLt_rLt with (y := @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_union tr0 tr1)).
  - transitivity (Ord_join (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0) (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1)).
    + eapply Ord_join_spec.
      * transitivity (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0); [exact H_rLe0 | eapply Ord_join_l].
      * transitivity (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1); [exact H_rLe1 | eapply Ord_join_r].
    + eapply tree_union_le_rev.
  - eapply member_implies_rLt. exists (tree_union tr0 tr1). reflexivity.
Qed.

Lemma tree_top_join (X : Type@{Set_u}) (os : X -> Ord.t)
  (H_rLt : forall x : X, os x <ᵣ tree_top X)
  : Ord.sup X os <ᵣ tree_top X.
Proof.
  exploit (Axiom_of_Choice X (fun _ : X => tree X) (fun x : X => fun tr : tree X => os x ≦ᵣ @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr)).
  { intros x. pose proof (H_rLt x) as [[tr H_rLe]]. exists tr. exact H_rLe. }
  intros [f H_f]. eapply rLe_rLt_rLt with (y := @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_join f)).
  - eapply Ord_sup_rLe_intro. intros x. transitivity (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (f x)).
    + eapply H_f.
    + eapply rLt_implies_rLe. eapply member_implies_rLt. rewrite fromWf_unfold.
      exists (f x). split; [now exists x | reflexivity].
  - eapply member_implies_rLt. exists (tree_join f). reflexivity.
Qed.

Lemma tree_top_S_inaccessible (X : Type@{Set_u})
  : inaccessible X Ord.zer Ord.suc (tree_top X).
Proof.
  econs.
  - eapply tree_top_O.
  - eapply tree_top_S.
  - eapply tree_top_join.
  - eapply tree_top_union.
Qed.

Lemma tree_top_orec (X : Type@{Set_u}) (base0 : Ord.t) (next : Ord.t -> Ord.t) (base1 : Ord.t)
  (H_next_le : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (H_next_mon : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  (H_inaccessible : inaccessible X base0 next (tree_top X))
  (H_base1 : base1 <ᵣ tree_top X)
  : forall alpha : Ord.t, alpha <ᵣ tree_top X -> Ord.orec base1 next alpha <ᵣ tree_top X.
Proof.
  intros alpha H_rLt.
  enough (H_recs : forall tr : tree X, Ord.orec base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr) <ᵣ tree_top X).
  { destruct H_rLt as [[tr H_rLe]]. eapply rLe_rLt_rLt; [eapply Ord_orec_rLe; eauto; exact H_rLe | eapply H_recs]. }
  intros tr. induction tr as [ | tr IH | trs IH | tr0 IH0 tr1 IH1].
  - eapply rLe_rLt_rLt with (y := base1).
    + pose proof (Ord_orec_rEq_r base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tree_O) Ord.zer H_next_le H_next_mon (tree_O_rEq X)) as H_eq.
      pose proof (Ord_orec_zer base1 next) as H_eq0. transitivity (Ord.orec base1 next Ord.zer).
      * eapply H_eq.
      * exact (proj1 H_eq0).
    + exact H_base1.
  - eapply rLe_rLt_rLt with (y := next (Ord.orec base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr))).
    + pose proof (Ord_orec_rEq_r base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_S tr)) (Ord.suc (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr)) H_next_le H_next_mon (tree_S_rEq X tr)) as H_eq.
      transitivity (Ord.orec base1 next (Ord.suc (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr))).
      * eapply H_eq.
      * exact (proj1 (Ord_orec_suc base1 next H_next_le H_next_mon (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr))).
    + eapply H_inaccessible. exact IH.
  - eapply rLe_rLt_rLt with (y := Ord_join base1 (Ord.sup X (fun x : X => next (Ord.orec base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (trs x)))))).
    + pose proof (Ord_orec_rEq_r base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_join trs)) (mkNode X (fun x : X => @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (trs x))) H_next_le H_next_mon (tree_join_rEq X trs)) as H_eq.
      transitivity (Ord.orec base1 next (mkNode X (fun x : X => @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (trs x)))).
      * eapply H_eq.
      * rewrite Ord_orec_unfold. reflexivity.
    + eapply H_inaccessible.
      * exact H_base1.
      * eapply H_inaccessible. intros x. eapply H_inaccessible. exact (IH x).
  - eapply rLe_rLt_rLt with (y := Ord.orec base1 next (Ord.suc (Ord_join (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0) (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1)))).
    + eapply Ord_orec_rLe; eauto. eapply tree_union_le.
    + eapply rLe_rLt_rLt with (y := next (Ord.orec base1 next (Ord_join (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0) (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1)))).
      * exact (proj1 (Ord_orec_suc base1 next H_next_le H_next_mon (Ord_join (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0) (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1)))).
      * eapply H_inaccessible. eapply rLe_rLt_rLt with (y := Ord_join (Ord.orec base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0)) (Ord.orec base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1))).
        { exact (proj1 (Ord_orec_join base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0) (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1) H_next_le H_next_mon)). }
        { eapply H_inaccessible; assumption. }
Qed.

Lemma tree_top_rec_inaccessible (X : Type@{Set_u}) (base0 : Ord.t) (next : Ord.t -> Ord.t) (base1 : Ord.t)
  (H_next_le : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (H_next_mon : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  (H_inaccessible : inaccessible X base0 next (tree_top X))
  (H_base1 : base1 <ᵣ tree_top X)
  : inaccessible X base0 (Ord.orec base1 next) (tree_top X).
Proof.
  econs.
  - eapply H_inaccessible.
  - eapply tree_top_orec; eauto.
  - eapply H_inaccessible.
  - eapply H_inaccessible.
Qed.

Lemma tree_top_add_inaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ tree_top X)
  : inaccessible X Ord.zer (Ord.add alpha) (tree_top X).
Proof.
  unfold Ord.add. eapply tree_top_rec_inaccessible; eauto.
  - intros x. eapply Ord_rLe_suc.
  - intros x y H_rLe. eapply Ord_suc_rLe. exact H_rLe.
  - eapply tree_top_S_inaccessible.
Qed.

Lemma tree_top_add (X : Type@{Set_u}) (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ tree_top X)
  (H_rLt1 : beta <ᵣ tree_top X)
  : Ord.add alpha beta <ᵣ tree_top X.
Proof.
  eapply tree_top_add_inaccessible; eauto.
Qed.

Lemma tree_top_flip_add_inaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ tree_top X)
  : inaccessible X Ord.zer (fun x : Ord.t => Ord.add x alpha) (tree_top X).
Proof.
  econs.
  - eapply tree_top_O.
  - intros x LT_x. eapply tree_top_add; eauto.
  - eapply tree_top_join.
  - eapply tree_top_union.
Qed.

Lemma tree_top_mul_inaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ tree_top X)
  : inaccessible X Ord.zer (Ord.mul alpha) (tree_top X).
Proof.
  unfold Ord.mul. eapply tree_top_rec_inaccessible; eauto.
  - intros x. eapply Ord_add_base_l.
  - intros x y H_rLe. eapply Ord_add_rLe_l. exact H_rLe.
  - eapply tree_top_flip_add_inaccessible. exact H_rLt.
  - eapply tree_top_O.
Qed.

Lemma tree_top_mul (X : Type@{Set_u}) (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ tree_top X)
  (H_rLt1 : beta <ᵣ tree_top X)
  : Ord.mul alpha beta <ᵣ tree_top X.
Proof.
  eapply tree_top_mul_inaccessible; eauto.
Qed.

Lemma tree_top_flip_mul_inaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ tree_top X)
  : inaccessible X Ord.zer (fun x : Ord.t => Ord.mul x alpha) (tree_top X).
Proof.
  econs.
  - eapply tree_top_O.
  - intros x LT_x. eapply tree_top_mul; eauto.
  - eapply tree_top_join.
  - eapply tree_top_union.
Qed.

Lemma tree_top_exp_inaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_pos : Ord.zer <ᵣ alpha)
  (H_rLt : alpha <ᵣ tree_top X)
  : inaccessible X Ord.zer (Ord.exp alpha) (tree_top X).
Proof.
  unfold Ord.exp. eapply tree_top_rec_inaccessible; eauto.
  - intros x. eapply Ord_mul_base_l. exact H_pos.
  - intros x y H_rLe. eapply Ord_mul_rLe_l. exact H_rLe.
  - eapply tree_top_flip_mul_inaccessible. exact H_rLt.
  - unfold Ord.one. eapply tree_top_S. eapply tree_top_O.
Qed.

Lemma tree_top_exp (X : Type@{Set_u}) (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ tree_top X)
  (H_rLt1 : beta <ᵣ tree_top X)
  : Ord.exp alpha beta <ᵣ tree_top X.
Proof.
  eapply rLe_rLt_rLt with (y := Ord.exp (Ord.suc alpha) beta).
  - eapply Ord_exp_rLe_l. eapply Ord_rLe_suc.
  - eapply tree_top_exp_inaccessible.
    + eapply rLe_rLt_rLt with (y := alpha); [eapply Ord_zer_rLe | unfold Ord.suc; eapply rLt_succ_intro].
    + eapply tree_top_S. exact H_rLt0.
    + exact H_rLt1.
Qed.

Lemma tree_top_flip_exp_inaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ tree_top X)
  : inaccessible X Ord.zer (fun x : Ord.t => Ord.exp x alpha) (tree_top X).
Proof.
  econs.
  - eapply tree_top_O.
  - intros x LT_x. eapply tree_top_exp; eauto.
  - eapply tree_top_join.
  - eapply tree_top_union.
Qed.

Inductive gtree {X : Type@{Set_u}} : Type@{Set_u} :=
  | gtree_O : @gtree X
  | gtree_S : @gtree X -> @gtree X
  | gtree_join : forall P : X -> Prop, (@sig X P -> @gtree X) -> @gtree X
  | gtree_union : @gtree X -> @gtree X -> @gtree X.

#[global] Arguments gtree : clear implicits.

Definition gtree_lt {X : Type@{Set_u}} (tr0 : gtree X) (tr1 : gtree X) : Prop :=
  match tr1 with
  | gtree_O => False
  | gtree_S tr => tr0 = tr
  | gtree_join P trs => exists x : @sig X P, tr0 = trs x
  | gtree_union trl trr => tr0 = trl \/ tr0 = trr
  end.

Lemma gtree_lt_well_founded (X : Type@{Set_u})
  : well_founded (@gtree_lt X).
Proof.
  ii. induction a as [ | tr IH | P trs IH | tr0 IH0 tr1 IH1].
  - econs. intros y H_rLt. contradiction.
  - econs. intros y H_rLt. simpl in H_rLt. subst y. exact IH.
  - econs. intros y H_rLt. simpl in H_rLt. destruct H_rLt as [x ->]. exact (IH x).
  - econs. intros y H_rLt. simpl in H_rLt. destruct H_rLt as [-> | ->]; assumption.
Qed.

Definition gtree_top (X : Type@{Set_u}) : Ord.t :=
  @fromWfSet (gtree X) (@gtree_lt X) (gtree_lt_well_founded X).

Lemma gtree_O_rEq (X : Type@{Set_u})
  : @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) gtree_O =ᵣ Ord.zer.
Proof.
  rewrite rEq_iff. split.
  - eapply fromWf_isSupremum. intros y H_rLt. contradiction H_rLt.
  - eapply Ord_zer_rLe.
Qed.

Lemma gtree_S_rEq (X : Type@{Set_u}) (tr : gtree X)
  : @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_S tr) =ᵣ Ord.suc (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr).
Proof.
  rewrite rEq_iff. split.
  - eapply fromWf_isSupremum. intros y H_rLt. simpl in H_rLt. subst y. unfold Ord.suc. eapply rLt_succ_intro.
  - unfold Ord.suc. rewrite succ_rLe_iff. eapply member_implies_rLt. rewrite fromWf_unfold.
    exists tr. split; [reflexivity | reflexivity].
Qed.

Lemma gtree_join_rEq (X : Type@{Set_u}) (P : X -> Prop) (trs : @sig X P -> gtree X)
  : @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_join P trs) =ᵣ mkNode (@sig X P) (fun x : @sig X P => @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (trs x)).
Proof.
  rewrite rEq_iff. split.
  - eapply fromWf_isSupremum. intros y H_rLt. simpl in H_rLt. destruct H_rLt as [x ->].
    eapply member_implies_rLt. exists x. reflexivity.
  - econs. intros x. eapply member_implies_rLt. rewrite fromWf_unfold.
    exists (trs x). split; [now exists x | reflexivity].
Qed.

Lemma gtree_union_le (X : Type@{Set_u}) (tr0 : gtree X) (tr1 : gtree X)
  : @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_union tr0 tr1) ≦ᵣ Ord.suc (Ord_join (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0) (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1)).
Proof.
  eapply fromWf_isSupremum. intros y H_rLt. simpl in H_rLt. unfold Ord.suc. rewrite rLt_succ_iff. destruct H_rLt as [-> | ->].
  - eapply Ord_join_l.
  - eapply Ord_join_r.
Qed.

Lemma gtree_union_le_rev (X : Type@{Set_u}) (tr0 : gtree X) (tr1 : gtree X)
  : Ord_join (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0) (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1) ≦ᵣ @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_union tr0 tr1).
Proof.
  eapply Ord_join_spec; eapply rLt_implies_rLe; eapply member_implies_rLt; rewrite fromWf_unfold.
  - exists tr0. split; [now left | reflexivity].
  - exists tr1. split; [now right | reflexivity].
Qed.

Lemma gtree_top_O (X : Type@{Set_u})
  : Ord.zer <ᵣ gtree_top X.
Proof.
  eapply rLe_rLt_rLt with (y := @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) gtree_O).
  - exact (proj2 (gtree_O_rEq X)).
  - eapply member_implies_rLt. exists gtree_O. reflexivity.
Qed.

Lemma gtree_top_S (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ gtree_top X)
  : Ord.suc alpha <ᵣ gtree_top X.
Proof.
  destruct H_rLt as [[tr H_rLe]]. eapply rLe_rLt_rLt with (y := @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_S tr)).
  - transitivity (Ord.suc (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr)).
    + eapply Ord_suc_rLe. exact H_rLe.
    + exact (proj2 (gtree_S_rEq X tr)).
  - eapply member_implies_rLt. exists (gtree_S tr). reflexivity.
Qed.

Lemma gtree_top_union (X : Type@{Set_u}) (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ gtree_top X)
  (H_rLt1 : beta <ᵣ gtree_top X)
  : Ord_join alpha beta <ᵣ gtree_top X.
Proof.
  destruct H_rLt0 as [[tr0 H_rLe0]], H_rLt1 as [[tr1 H_rLe1]].
  eapply rLe_rLt_rLt with (y := @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_union tr0 tr1)).
  - transitivity (Ord_join (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0) (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1)).
    + eapply Ord_join_spec.
      * transitivity (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0); [exact H_rLe0 | eapply Ord_join_l].
      * transitivity (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1); [exact H_rLe1 | eapply Ord_join_r].
    + eapply gtree_union_le_rev.
  - eapply member_implies_rLt. exists (gtree_union tr0 tr1). reflexivity.
Qed.

Lemma gtree_top_join (X : Type@{Set_u}) (P : X -> Prop) (os : @sig X P -> Ord.t)
  (H_rLt : forall x : @sig X P, os x <ᵣ gtree_top X)
  : Ord.sup (@sig X P) os <ᵣ gtree_top X.
Proof.
  pose proof (Axiom_of_Choice (@sig X P) (fun _ : @sig X P => gtree X) (fun x : @sig X P => fun tr : gtree X => os x ≦ᵣ @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr)) as [f H_f].
  { intros x. pose proof (H_rLt x) as [[tr H_rLe]]. exists tr. exact H_rLe. }
  eapply rLe_rLt_rLt with (y := @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_join P f)).
  - eapply Ord_sup_rLe_intro. intros x. transitivity (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (f x)).
    + eapply H_f.
    + eapply rLt_implies_rLe. eapply member_implies_rLt. rewrite fromWf_unfold. exists (f x). split; [now exists x | reflexivity].
  - eapply member_implies_rLt. exists (gtree_join P f). reflexivity.
Qed.

Lemma gtree_top_S_ginaccessible (X : Type@{Set_u})
  : ginaccessible X Ord.zer Ord.suc (gtree_top X).
Proof.
  econs.
  - eapply gtree_top_O.
  - eapply gtree_top_S.
  - eapply gtree_top_join.
  - eapply gtree_top_union.
Qed.

Lemma gtree_top_orec (X : Type@{Set_u}) (base0 : Ord.t) (next : Ord.t -> Ord.t) (base1 : Ord.t)
  (H_next_le : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (H_next_mon : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  (H_inaccessible : ginaccessible X base0 next (gtree_top X))
  (H_base1 : base1 <ᵣ gtree_top X)
  : forall alpha : Ord.t, alpha <ᵣ gtree_top X -> Ord.orec base1 next alpha <ᵣ gtree_top X.
Proof.
  intros alpha H_rLt.
  enough (H_recs : forall tr : gtree X, Ord.orec base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr) <ᵣ gtree_top X).
  { destruct H_rLt as [[tr H_rLe]]. eapply rLe_rLt_rLt; [eapply Ord_orec_rLe; eauto; exact H_rLe | eapply H_recs]. }
  intros tr. induction tr as [ | tr IH | P trs IH | tr0 IH0 tr1 IH1].
  - eapply rLe_rLt_rLt with (y := base1).
    + pose proof (Ord_orec_rEq_r base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) gtree_O) Ord.zer H_next_le H_next_mon (gtree_O_rEq X)) as H_eq.
      pose proof (Ord_orec_zer base1 next) as H_eq0. transitivity (Ord.orec base1 next Ord.zer).
      * eapply H_eq.
      * exact (proj1 H_eq0).
    + exact H_base1.
  - eapply rLe_rLt_rLt with (y := next (Ord.orec base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr))).
    + pose proof (Ord_orec_rEq_r base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_S tr)) (Ord.suc (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr)) H_next_le H_next_mon (gtree_S_rEq X tr)) as H_eq.
      transitivity (Ord.orec base1 next (Ord.suc (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr))).
      * eapply H_eq.
      * exact (proj1 (Ord_orec_suc base1 next H_next_le H_next_mon (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr))).
    + eapply H_inaccessible. exact IH.
  - eapply rLe_rLt_rLt with (y := Ord_join base1 (Ord.sup (@sig X P) (fun x : @sig X P => next (Ord.orec base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (trs x)))))).
    + pose proof (Ord_orec_rEq_r base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_join P trs)) (mkNode (@sig X P) (fun x : @sig X P => @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (trs x))) H_next_le H_next_mon (gtree_join_rEq X P trs)) as H_eq.
      transitivity (Ord.orec base1 next (mkNode (@sig X P) (fun x : @sig X P => @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (trs x)))).
      * eapply H_eq.
      * rewrite Ord_orec_unfold. reflexivity.
    + eapply H_inaccessible.
      * exact H_base1.
      * eapply H_inaccessible. intros x. eapply H_inaccessible. exact (IH x).
  - eapply rLe_rLt_rLt with (y := Ord.orec base1 next (Ord.suc (Ord_join (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0) (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1)))).
    + eapply Ord_orec_rLe; eauto. eapply gtree_union_le.
    + eapply rLe_rLt_rLt with (y := next (Ord.orec base1 next (Ord_join (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0) (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1)))).
      * exact (proj1 (Ord_orec_suc base1 next H_next_le H_next_mon (Ord_join (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0) (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1)))).
      * eapply H_inaccessible. eapply rLe_rLt_rLt with (y := Ord_join (Ord.orec base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0)) (Ord.orec base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1))).
        { exact (proj1 (Ord_orec_join base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0) (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1) H_next_le H_next_mon)). }
        { eapply H_inaccessible; assumption. }
Qed.

Lemma gtree_top_rec_ginaccessible (X : Type@{Set_u}) (base0 : Ord.t) (next : Ord.t -> Ord.t) (base1 : Ord.t)
  (H_next_le : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (H_next_mon : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  (H_inaccessible : ginaccessible X base0 next (gtree_top X))
  (H_base1 : base1 <ᵣ gtree_top X)
  : ginaccessible X base0 (Ord.orec base1 next) (gtree_top X).
Proof.
  econs.
  - eapply H_inaccessible.
  - eapply gtree_top_orec; eauto.
  - eapply H_inaccessible.
  - eapply H_inaccessible.
Qed.

Lemma gtree_top_add_ginaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ gtree_top X)
  : ginaccessible X Ord.zer (Ord.add alpha) (gtree_top X).
Proof.
  unfold Ord.add. eapply gtree_top_rec_ginaccessible; eauto.
  - intros x. eapply Ord_rLe_suc.
  - intros x y H_rLe. eapply Ord_suc_rLe. exact H_rLe.
  - eapply gtree_top_S_ginaccessible.
Qed.

Lemma gtree_top_add (X : Type@{Set_u}) (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ gtree_top X)
  (H_rLt1 : beta <ᵣ gtree_top X)
  : Ord.add alpha beta <ᵣ gtree_top X.
Proof.
  eapply gtree_top_add_ginaccessible; eauto.
Qed.

Lemma gtree_top_flip_add_ginaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ gtree_top X)
  : ginaccessible X Ord.zer (fun x : Ord.t => Ord.add x alpha) (gtree_top X).
Proof.
  econs.
  - eapply gtree_top_O.
  - intros x LT_x. eapply gtree_top_add; eauto.
  - eapply gtree_top_join.
  - eapply gtree_top_union.
Qed.

Lemma gtree_top_mul_ginaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ gtree_top X)
  : ginaccessible X Ord.zer (Ord.mul alpha) (gtree_top X).
Proof.
  unfold Ord.mul. eapply gtree_top_rec_ginaccessible; eauto.
  - intros x. eapply Ord_add_base_l.
  - intros x y H_rLe. eapply Ord_add_rLe_l. exact H_rLe.
  - eapply gtree_top_flip_add_ginaccessible. exact H_rLt.
  - eapply gtree_top_O.
Qed.

Lemma gtree_top_mul (X : Type@{Set_u}) (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ gtree_top X)
  (H_rLt1 : beta <ᵣ gtree_top X)
  : Ord.mul alpha beta <ᵣ gtree_top X.
Proof.
  eapply gtree_top_mul_ginaccessible; eauto.
Qed.

Lemma gtree_top_flip_mul_ginaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ gtree_top X)
  : ginaccessible X Ord.zer (fun x : Ord.t => Ord.mul x alpha) (gtree_top X).
Proof.
  econs.
  - eapply gtree_top_O.
  - intros x LT_x. eapply gtree_top_mul; eauto.
  - eapply gtree_top_join.
  - eapply gtree_top_union.
Qed.

Lemma gtree_top_exp_ginaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_pos : Ord.zer <ᵣ alpha)
  (H_rLt : alpha <ᵣ gtree_top X)
  : ginaccessible X Ord.zer (Ord.exp alpha) (gtree_top X).
Proof.
  unfold Ord.exp. eapply gtree_top_rec_ginaccessible; eauto.
  - intros x. eapply Ord_mul_base_l. exact H_pos.
  - intros x y H_rLe. eapply Ord_mul_rLe_l. exact H_rLe.
  - eapply gtree_top_flip_mul_ginaccessible. exact H_rLt.
  - unfold Ord.one. eapply gtree_top_S. eapply gtree_top_O.
Qed.

Lemma gtree_top_exp (X : Type@{Set_u}) (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ gtree_top X)
  (H_rLt1 : beta <ᵣ gtree_top X)
  : Ord.exp alpha beta <ᵣ gtree_top X.
Proof.
  eapply rLe_rLt_rLt with (y := Ord.exp (Ord.suc alpha) beta).
  - eapply Ord_exp_rLe_l. eapply Ord_rLe_suc.
  - eapply gtree_top_exp_ginaccessible.
    + eapply rLe_rLt_rLt with (y := alpha); [eapply Ord_zer_rLe | unfold Ord.suc; eapply rLt_succ_intro].
    + eapply gtree_top_S. exact H_rLt0.
    + exact H_rLt1.
Qed.

Lemma gtree_top_flip_exp_ginaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ gtree_top X)
  : ginaccessible X Ord.zer (fun x : Ord.t => Ord.exp x alpha) (gtree_top X).
Proof.
  econs.
  - eapply gtree_top_O.
  - intros x LT_x. eapply gtree_top_exp; eauto.
  - eapply gtree_top_join.
  - eapply gtree_top_union.
Qed.

Definition kappa : Ord.t :=
  @mkNode { A : Type & { R : A -> A -> Prop | well_founded R } } (fun RWF => @fromWfSet (projT1 RWF) (proj1_sig (projT2 RWF)) (proj2_sig (projT2 RWF))).

Lemma kappa_complete (alpha : Ord.t)
  (H_rLt : alpha <ᵣ kappa)
  : exists A : Type, exists R : A -> A -> Prop, exists R_wf : well_founded R, alpha ≦ᵣ @fromWfSet A R R_wf.
Proof.
  destruct H_rLt as [[[A [R R_wf]] H_rLe]]. exists A, R, R_wf. exact H_rLe.
Qed.

Lemma kappa_inaccessible_from_wf_set (A : Type) (R : A -> A -> Prop) (R_wf : well_founded R)
  : @fromWfSet A R R_wf <ᵣ kappa.
Proof.
  econs. exists (@existT Type (fun A : Type => { R : A -> A -> Prop | well_founded R }) A (@exist (A -> A -> Prop) (@well_founded A) R R_wf)). reflexivity.
Qed.

Lemma kappa_inaccessible_from_wf (A : Type) (R : A -> A -> Prop) (R_wf : well_founded R) (a : A)
  : @fromWf A R R_wf a <ᵣ kappa.
Proof.
  eapply rLt_rLe_rLt with (y := @fromWfSet A R R_wf).
  - eapply member_implies_rLt. exists a. reflexivity.
  - eapply rLt_implies_rLe. eapply kappa_inaccessible_from_wf_set.
Qed.

Lemma kappa_inaccessible_cardinality (A : Type)
  : Cardinality.toTree (Cardinality.ofType A) <ᵣ kappa.
Proof.
  pose proof (well_ordering_thm A (@mkSetoid_from_eq A)) as (R & R_wf & R_total & R_trans & R_compat).
  eapply rLe_rLt_rLt with (y := @fromWfSet A R R_wf).
  - eapply Cardinal1.Cardinality_lowerbound; eauto.
  - eapply kappa_inaccessible_from_wf_set.
Qed.

Lemma kappa_inaccessible_O
  : Ord.zer <ᵣ kappa.
Proof.
  eapply rLe_rLt_rLt with (y := @fromWfSet Empty_set (fun x : Empty_set => fun _ : Empty_set => False) (Empty_set_ind _)).
  - eapply Ord_zer_rLe.
  - eapply kappa_inaccessible_from_wf_set.
Qed.

Lemma kappa_inaccessible_is_S (alpha : Ord.t) (beta : Ord.t)
  (H_succ : beta =ᵣ Ord.suc alpha)
  (H_rLt : alpha <ᵣ kappa)
  : beta <ᵣ kappa.
Proof.
  rewrite H_succ. pose proof (kappa_complete alpha H_rLt) as (A & R & R_wf & H_rLe).
  set (Ropt := fun x : option A => fun y : option A =>
    match x, y with
    | Some x', Some y' => R x' y'
    | Some x', None => True
    | None, _ => False
    end
  ).
  assert (Ropt_wf : well_founded Ropt).
  { assert (H_some_acc : forall a : A, Acc Ropt (Some a)).
    { intros a. induction (R_wf a) as [a _ IH]. econs. intros [b | ] H_rel.
      - eapply IH. exact H_rel.
      - contradiction.
    }
    intros [a | ]. eapply H_some_acc. econs. intros [a | ] H_rel.
    - eapply H_some_acc.
    - contradiction.
  }
  assert (H_top : @fromWfSet A R R_wf ≦ᵣ @fromWf (option A) Ropt Ropt_wf None).
  { econs. intros a.
    assert (H_rLe_a : @fromWf A R R_wf a ≦ᵣ @fromWf (option A) Ropt Ropt_wf (Some a)).
    { eapply fromWf_cong with (RA := R) (RB := Ropt) (f := @Some A) (RA_wf := R_wf) (RB_wf := Ropt_wf). intros x y H_xy. exact H_xy. }
    assert (H_rLt_a : @fromWf (option A) Ropt Ropt_wf (Some a) <ᵣ @fromWf (option A) Ropt Ropt_wf None).
    { eapply member_implies_rLt. rewrite fromWf_unfold. exists (Some a). split; [reflexivity | reflexivity]. }
    eapply rLe_rLt_rLt; eauto.
  }
  eapply rLe_rLt_rLt with (y := Ord.suc (@fromWfSet A R R_wf)).
  - eapply Ord_suc_rLe. exact H_rLe.
  - eapply rLe_rLt_rLt with (y := @fromWfSet (option A) Ropt Ropt_wf).
    + unfold Ord.suc. rewrite succ_rLe_iff. eapply rLe_rLt_rLt with (y := @fromWf (option A) Ropt Ropt_wf None).
      * exact H_top.
      * eapply member_implies_rLt. exists None. reflexivity.
    + eapply kappa_inaccessible_from_wf_set.
Qed.

Lemma kappa_inaccessible_S (alpha : Ord.t)
  (H_rLt : alpha <ᵣ kappa)
  : Ord.suc alpha <ᵣ kappa.
Proof.
  eapply kappa_inaccessible_is_S; eauto. reflexivity.
Qed.

Lemma kappa_inaccessible_Ord_of_nat (n : nat)
  : Ord_of_nat n <ᵣ kappa.
Proof.
  induction n as [ | n IH].
  - eapply kappa_inaccessible_O.
  - simpl. eapply kappa_inaccessible_S. exact IH.
Qed.

Lemma kappa_inaccessible_join (A : Type) (os : A -> Ord.t)
  (H_rLt : forall a : A, os a <ᵣ kappa)
  : Ord.sup A os <ᵣ kappa.
Proof.
  pose proof (Axiom_of_Choice A (fun _ : A => { B : Type & { R : B -> B -> Prop | well_founded R } }) (fun a : A => fun RWF : { B : Type & { R : B -> B -> Prop | well_founded R } } => os a ≦ᵣ @fromWfSet (projT1 RWF) (proj1_sig (projT2 RWF)) (proj2_sig (projT2 RWF)))) as [f H_f].
  { intros a. pose proof (kappa_complete (os a) (H_rLt a)) as (B & R & R_wf & H_rLe). exists (@existT Type (fun B : Type => { R : B -> B -> Prop | well_founded R }) B (@exist (B -> B -> Prop) (@well_founded B) R R_wf)). exact H_rLe. }
  set (B := fun a : A => projT1 (f a)).
  set (R := fun a : A => proj1_sig (projT2 (f a))).
  set (R_wf := fun a : A => proj2_sig (projT2 (f a))).
  pose (A_join := { a : A & option (B a) }).
  pose (R_join := fun x : A_join => fun y : A_join => match y with | @existT _ _ a None => match x with | @existT _ _ a' (Some _) => a = a' | _ => False end | @existT _ _ a (Some y') => match x with | @existT _ _ a' (Some x') => exists H_eq : a' = a, R a (eq_rect a' B x' a H_eq) y' | _ => False end end).
  assert (R_join_wf : well_founded R_join).
  { intros [a [x | ]].
    + induction (R_wf a x) as [x _ IH]. econs. intros [a' [y | ]] H_rel.
      * unfold R_join in H_rel. destruct H_rel as [H_eq H_rel]. subst a'. simpl in H_rel. eapply IH. exact H_rel.
      * contradiction.
    + econs. intros [a' [y | ]] H_rel.
      * unfold R_join in H_rel. subst a'. induction (R_wf a y) as [y _ IH]. econs. intros [a' [z | ]] H_rel.
        { unfold R_join in H_rel. destruct H_rel as [H_eq H_rel]. subst a'. simpl in H_rel. eapply IH. exact H_rel. }
        { contradiction. }
      * contradiction.
  }
  eapply rLe_rLt_rLt with (y := @fromWfSet A_join R_join R_join_wf).
  - eapply Ord_sup_rLe_intro. intros a. transitivity (@fromWfSet (B a) (R a) (R_wf a)).
    + eapply H_f.
    + eapply rLt_implies_rLe. eapply rLe_rLt_rLt with (y := @fromWf A_join R_join R_join_wf (@existT A (fun a : A => option (B a)) a None)).
      * econs. intros x. eapply rLe_rLt_rLt with (y := @fromWf A_join R_join R_join_wf (@existT A (fun a : A => option (B a)) a (Some x))).
        { eapply fromWf_cong with (RA := R a) (RB := R_join) (f := fun x : B a => @existT A (fun a : A => option (B a)) a (Some x)) (RA_wf := R_wf a) (RB_wf := R_join_wf). intros x0 y0 H_xy. exists eq_refl. exact H_xy. }
        { eapply member_implies_rLt. rewrite fromWf_unfold. exists (@existT A (fun a : A => option (B a)) a (Some x)). split; [reflexivity | reflexivity]. }
      * eapply member_implies_rLt. exists (@existT A (fun a : A => option (B a)) a None). reflexivity.
  - eapply kappa_inaccessible_from_wf_set.
Qed.

Lemma kappa_inaccessible_union (alpha : Ord.t) (beta : Ord.t)
  (H_rLt : alpha <ᵣ kappa)
  (H_rLt' : beta <ᵣ kappa)
  : Ord_join alpha beta <ᵣ kappa.
Proof.
  unfold Ord_join. eapply kappa_inaccessible_join. intros [ | ]; assumption.
Qed.

Lemma kappa_inaccessible_omega
  : omega <ᵣ kappa.
Proof.
  unfold omega. eapply kappa_inaccessible_join. intros n. eapply kappa_inaccessible_Ord_of_nat.
Qed.

Lemma kappa_inaccessible_orec (base : Ord.t) (next : Ord.t -> Ord.t)
  (H_next_le : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (H_next_mon : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  (H_base : base <ᵣ kappa)
  (H_next : forall alpha : Ord.t, alpha <ᵣ kappa -> next alpha <ᵣ kappa)
  : forall alpha : Ord.t, alpha <ᵣ kappa -> Ord.orec base next alpha <ᵣ kappa.
Proof.
  intros alpha H_rLt.
  pose proof (kappa_complete alpha H_rLt) as (A & R & R_wf & H_rLe).
  assert (H_rec : forall a : A, Ord.orec base next (@fromWf A R R_wf a) <ᵣ kappa).
  { intros a. induction (R_wf a) as [a _ IH].
    eapply rLe_rLt_rLt with (y := Ord.orec base next (Ord.suc (Ord.sup (@sig A (fun b : A => R b a)) (fun b : @sig A (fun b : A => R b a) => @fromWf A R R_wf (proj1_sig b))))).
    - eapply Ord_orec_rLe; eauto. eapply fromWf_isSupremum. intros b R_b_a.
      eapply rLe_rLt_rLt with (y := Ord.sup (@sig A (fun b : A => R b a)) (fun b : @sig A (fun b : A => R b a) => @fromWf A R R_wf (proj1_sig b))).
      + change ((fun b0 : @sig A (fun b : A => R b a) => @fromWf A R R_wf (proj1_sig b0)) (@exist A (fun b : A => R b a) b R_b_a) ≦ᵣ Ord.sup (@sig A (fun b : A => R b a)) (fun b0 : @sig A (fun b : A => R b a) => @fromWf A R R_wf (proj1_sig b0))). eapply Ord_rLe_sup_intro.
      + unfold Ord.suc. eapply rLt_succ_intro.
    - eapply rLe_rLt_rLt with (y := next (Ord.orec base next (Ord.sup (@sig A (fun b : A => R b a)) (fun b : @sig A (fun b : A => R b a) => @fromWf A R R_wf (proj1_sig b))))).
      + exact (proj1 (Ord_orec_suc base next H_next_le H_next_mon (Ord.sup (@sig A (fun b : A => R b a)) (fun b : @sig A (fun b : A => R b a) => @fromWf A R R_wf (proj1_sig b))))).
      + eapply H_next. eapply rLe_rLt_rLt with (y := Ord_join base (Ord.sup (@sig A (fun b : A => R b a)) (fun b : @sig A (fun b : A => R b a) => Ord.orec base next (@fromWf A R R_wf (proj1_sig b))))).
        * exact (proj1 (Ord_orec_sup base next (@sig A (fun b : A => R b a)) (fun b : @sig A (fun b : A => R b a) => @fromWf A R R_wf (proj1_sig b)) H_next_le H_next_mon)).
        * eapply kappa_inaccessible_union.
          { exact H_base. }
          { eapply kappa_inaccessible_join. intros [b R_b_a]. eapply IH. exact R_b_a. }
  }
  eapply rLe_rLt_rLt with (y := Ord.orec base next (@fromWfSet A R R_wf)).
  - eapply Ord_orec_rLe; [exact H_next_le | exact H_next_mon | exact H_rLe].
  - eapply rLe_rLt_rLt with (y := Ord_join base (Ord.sup A (fun a : A => next (Ord.orec base next (@fromWf A R R_wf a))))).
    + unfold fromWfSet. rewrite Ord_orec_unfold. reflexivity.
    + eapply kappa_inaccessible_union.
      * exact H_base.
      * eapply kappa_inaccessible_join. intros a. eapply H_next. eapply H_rec.
Qed.

Lemma kappa_inaccessible_add (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ kappa)
  (H_rLt1 : beta <ᵣ kappa)
  : Ord.add alpha beta <ᵣ kappa.
Proof.
  unfold Ord.add. eapply kappa_inaccessible_orec; eauto.
  - intros x. eapply Ord_rLe_suc.
  - intros x y H_rLe. eapply Ord_suc_rLe. exact H_rLe.
  - intros x H_rLt. eapply kappa_inaccessible_S. exact H_rLt.
Qed.

Lemma kappa_inaccessible_mul (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ kappa)
  (H_rLt1 : beta <ᵣ kappa)
  : Ord.mul alpha beta <ᵣ kappa.
Proof.
  unfold Ord.mul. eapply kappa_inaccessible_orec; eauto.
  - intros x. eapply Ord_add_base_l.
  - intros x y H_rLe. eapply Ord_add_rLe_l. exact H_rLe.
  - eapply kappa_inaccessible_O.
  - intros x H_rLt. eapply kappa_inaccessible_add; eauto.
Qed.

Lemma kappa_inaccessible_exp (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ kappa)
  (H_rLt1 : beta <ᵣ kappa)
  : Ord.exp alpha beta <ᵣ kappa.
Proof.
  eapply rLe_rLt_rLt with (y := Ord.exp (Ord.suc alpha) beta).
  - eapply Ord_exp_rLe_l. eapply Ord_rLe_suc.
  - unfold Ord.exp. eapply kappa_inaccessible_orec; eauto.
    + intros x. eapply Ord_mul_base_l. eapply rLe_rLt_rLt with (y := alpha).
      * eapply Ord_zer_rLe.
      * unfold Ord.suc. eapply rLt_succ_intro.
    + intros x y H_rLe. eapply Ord_mul_rLe_l. exact H_rLe.
    + unfold Ord.one. eapply kappa_inaccessible_S. eapply kappa_inaccessible_O.
    + intros x H_rLt. eapply kappa_inaccessible_mul.
      * exact H_rLt.
      * eapply kappa_inaccessible_S. exact H_rLt0.
Qed.

End CLASSICAL.

End Inaccessible.
