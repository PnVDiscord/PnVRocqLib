Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.subset.
#[local] Obligation Tactic := i.

#[local] Hint Resolve Equivalence_Reflexive Equivalence_Symmetric Equivalence_Transitive : core.
#[local] Hint Resolve eqProp_refl eqProp_sym eqProp_trans leProp_refl leProp_trans leProp_antisymmetry eqProp_implies_leProp : core.
#[local] Hint Resolve supremum_monotonic supremum_unique supremum_congruence is_supremum_of_compatWith_eqProp : core.

Class isBA (B : Type) : Type :=
  { andB : B -> B -> B
  ; orB : B -> B -> B
  ; notB : B -> B
  ; trueB : B
  ; falseB : B
  }.

Class BooleanAlgebraLaws {B : Type} {SETOID : isSetoid B} (BA : isBA B) : Prop :=
  { andB_compathWith_eqProp :: eqPropCompatible2 andB
  ; orB_compatWith_eqProp :: eqPropCompatible2 orB
  ; notB_compatWith_eqProp :: eqPropCompatible1 notB
  ; andB_assoc :: isAssociative andB
  ; orB_assoc :: isAssociative orB
  ; andB_comm :: isCommutative andB
  ; orB_comm :: isCommutative orB
  ; andB_distr_orB :: distributesOver andB orB
  ; orB_distr_andB :: distributesOver orB andB
  ; trueB_id_andB :: isIdentityElementOf trueB andB
  ; falseB_id_orB :: isIdentityElementOf falseB orB
  ; falseB_ann_andB :: isAnnihilatorFor falseB andB
  ; trueB_ann_orB :: isAnnihilatorFor trueB orB
  ; andB_idem :: isIdempotent andB
  ; orBA_idem :: isIdempotent orB
  ; AbsorptionLaw_andB_orB :: AbsorptionLaw andB orB
  ; andB_notB_falseB x
    : andB x (notB x) == falseB
  ; orB_notB_trueB x
    : orB x (notB x) == trueB
  }.

Section BOOLEAN_ALGEBRA. (* Reference: << Constructive Completeness Proofs and Delimited Control >> written by "Danko Ilik" *)

Import ListNotations.

Context {B : Type} {BA : isBA B}.

#[local] Notation andB := (andB (isBA := BA)).

Definition andsB : list B -> B :=
  fold_right andB trueB.

Context {SETOID : isSetoid B}.

Definition leB lhs rhs : Prop :=
  andB lhs rhs == lhs.

Context {BOOLEAN_ALGEBRA_LAWS : BooleanAlgebraLaws BA}.

#[global]
Instance leB_PreOrder
  : PreOrder leB.
Proof.
  split.
  - intros x. eapply andB_idem.
  - intros x y z LE LE'. unfold leB in *.
    rewrite <- LE at 2. rewrite <- LE'. now rewrite andB_assoc, LE.
Qed.

#[global]
Instance leB_PartialOrder
  : PartialOrder eqProp leB.
Proof.
  intros x y; unfold flip; cbn. unfold leB. split.
  - intros EQ. rewrite EQ. split; now eapply andB_idem.
  - intros [LE GE]. rewrite <- LE at 1. rewrite <- GE at 2. eapply andB_comm.
Qed.

#[global]
Instance BA_isProset : isProset B :=
  { leProp lhs rhs := andB lhs rhs == lhs
  ; Proset_isSetoid := SETOID
  ; leProp_PreOrder := leB_PreOrder
  ; leProp_PartialOrder := leB_PartialOrder
  }.

Lemma andB_le_intro_l x1 x2
  : andB x1 x2 =< x1.
Proof.
  rewrite andB_comm. cbn.
  now rewrite <- andB_assoc, andB_idem.
Qed.

Lemma andB_le_intro_r x1 x2
  : andB x1 x2 =< x2.
Proof.
  rewrite andB_comm. eapply andB_le_intro_l.
Qed.

#[global]
Instance andB_compathWith_leProp
  : isMonotonic2 andB.
Proof.
  ii. cbn in *. transitivity (andB (andB x1 x2) (andB y1 y2)).
  - repeat rewrite andB_assoc.
    rewrite @comm with (isCommutative := andB_comm) (x := andB x1 y1) (y := x2).
    rewrite @assoc with (isAssociative := andB_assoc) (x := x2) (y := x1) (z := y1).
    rewrite @comm with (isCommutative := andB_comm) (x := x2) (y := x1).
    reflexivity.
  - now rewrite x_LE, y_LE.
Qed.

Lemma andsB_app xs1 xs2
  : andsB (xs1 ++ xs2) == andB (andsB xs1) (andsB xs2).
Proof.
  cbn. revert xs2. induction xs1 as [ | x1 xs1 IH]; simpl; ii.
  - now rewrite @left_id with (isIdentityElementOf := trueB_id_andB).
  - rewrite <- andB_assoc. now rewrite IH.
Qed.

Lemma andsB_zero
  : andsB [] == trueB.
Proof.
  reflexivity.
Qed.

Lemma andsB_one x1
  : andsB [x1] == x1.
Proof.
  cbn. eapply trueB_id_andB.
Qed.

Lemma andsB_two x1 x2
  : andsB [x1; x2] == andB x1 x2.
Proof.
  replace ([x1; x2]) with ([x1] ++ [x2]); trivial. rewrite andsB_app. now do 2 rewrite andsB_one.
Qed.

Lemma falseB_isBottom x
  : falseB =< x.
Proof.
  simpl. eapply falseB_ann_andB.
Qed.

Lemma andsB_le_In xs x
  (x_in_xs : In x xs)
  : andsB xs =< x.
Proof.
  revert x x_in_xs.
  induction xs as [ | x1 xs1 IH]; simpl in *.
  - tauto.
  - intros x [x_eq_x1 | x_in_xs1].
    + subst x.
      rewrite <- @assoc with (isAssociative := andB_assoc) (x := x1) (y := andsB xs1) (z := x1).
      rewrite -> @comm with (isCommutative := andB_comm) (x := andsB xs1) (y := x1).
      rewrite -> @assoc with (isAssociative := andB_assoc) (x := x1) (z := andsB xs1) (y := x1).
      rewrite -> @idem with (isIdempotent := andB_idem) (x := x1).
      reflexivity.
    + rewrite <- @assoc with (isAssociative := andB_assoc) (x := x1) (y := andsB xs1) (z := x).
      rewrite IH with (x := x) (x_in_xs := x_in_xs1).
      reflexivity.
Qed.

#[local] Hint Resolve andsB_le_In : core.

Variant isFilter (F : ensemble B) : Prop :=
  | isFilter_if
    (CLOSED_andsB : forall xs, L.is_finsubset_of xs F -> andsB xs \in F)
    (CLOSED_UPWARD : forall x, x \in F -> forall x', x =< x' -> x' \in F)
    : isFilter F.

Lemma isFilter_intro F
  (NONEMPTY : exists x0, x0 \in F)
  (CLOSED_MEET : forall x1, forall x2, x1 \in F -> x2 \in F -> andB x1 x2 \in F)
  (CLOSED_UPWARD : forall x, x \in F -> forall x', x =< x' -> x' \in F)
  : isFilter F.
Proof.
  split; trivial. induction xs as [ | x xs IH]; simpl; ii.
  - des. eapply CLOSED_UPWARD with (x := x0); trivial. cbn. eapply trueB_id_andB.
  - eapply CLOSED_MEET; [eapply CLOSED_UPWARD; [eapply H; left; reflexivity | reflexivity] | eapply IH]; eauto.
Qed.

Lemma isFilter_compatWith_eqProp F F'
  (F_isFilter : isFilter F)
  (F_eq_F' : F == F')
  : isFilter F'.
Proof.
  inversion F_isFilter. eapply isFilter_intro.
  - exists (trueB). eapply F_eq_F'. now eapply CLOSED_andsB with (xs := []).
  - ii. eapply F_eq_F'. eapply CLOSED_UPWARD with (x := andsB [x1; x2]).
    + eapply CLOSED_andsB. intros z [z_eq_x1 | [z_eq_x2 | []]]; subst z. all: now eapply F_eq_F'.
    + now rewrite andsB_two.
  - ii; des. eapply F_eq_F'. eapply CLOSED_UPWARD with (x := x); unnw; trivial. now eapply F_eq_F'.
Qed.

#[global]
Add Parametric Morphism
  : isFilter with signature (eqProp ==> iff)
  as isFilter_eqProp_iff.
Proof.
  ii; split; i; eapply isFilter_compatWith_eqProp; eauto with *.
Qed.

Definition inconsistent X : Prop :=
  exists botB, botB \in X /\ botB == falseB.

Lemma inconsistent_compatWith_isSubsetOf X X'
  (INCONSISTENT : inconsistent X)
  (SUBSET : X \subseteq X')
  : inconsistent X'.
Proof.
  destruct INCONSISTENT as [botB [botB_in_X botB_eq_falseB]].
  exists (botB). split; [exact (SUBSET botB botB_in_X) | exact (botB_eq_falseB)].
Qed.

#[global]
Add Parametric Morphism :
  inconsistent with signature (eqProp ==> iff)
  as inconsistent_compatWith_eqProp.
Proof.
  intros X X' X_eq_X'; split; ii; eapply inconsistent_compatWith_isSubsetOf; eauto; intros z z_in; eapply X_eq_X'; eauto.
Qed.

Definition isProperFilter F : Prop :=
  ⟪ IS_FILTER : isFilter F ⟫ /\ ⟪ CONSISTENT : ~ inconsistent F ⟫.

Lemma isProperFilter_compatWith_eqProp F F'
  (F_isProperFilter : isProperFilter F)
  (F_eq_F' : F == F')
  : isProperFilter F'.
Proof.
  r in F_isProperFilter. des. split; unnw.
  - eapply isFilter_compatWith_eqProp; eauto.
  - now rewrite <- F_eq_F'.
Qed.

Definition equiconsistent X X' : Prop :=
  inconsistent X <-> inconsistent X'.

#[global]
Instance equiconsistent_Equivalence : Equivalence equiconsistent :=
  relation_on_image_liftsEquivalence iff_equivalence inconsistent.

#[global]
Add Parametric Morphism :
  equiconsistent with signature (eqProp ==> eqProp ==> iff)
  as equiconsistent_compatWith_eqProp.
Proof.
  intros X X' X_eq_X' Y Y' Y_eq_Y'. split; intros EQUICONSISTENT.
  - split; intros INCONSISTENT.
    + rewrite <- X_eq_X' in INCONSISTENT.
      apply EQUICONSISTENT in INCONSISTENT.
      now rewrite -> Y_eq_Y' in INCONSISTENT.
    + rewrite <- Y_eq_Y' in INCONSISTENT.
      apply EQUICONSISTENT in INCONSISTENT.
      now rewrite -> X_eq_X' in INCONSISTENT.
  - split; intros INCONSISTENT.
    + rewrite -> X_eq_X' in INCONSISTENT.
      apply EQUICONSISTENT in INCONSISTENT.
      now rewrite <- Y_eq_Y' in INCONSISTENT.
    + rewrite -> Y_eq_Y' in INCONSISTENT.
      apply EQUICONSISTENT in INCONSISTENT.
      now rewrite <- X_eq_X' in INCONSISTENT.
Qed.

Definition cl X : ensemble B :=
  fun x => exists xs, ⟪ FINITE_SUBSET : L.is_finsubset_of xs X ⟫ /\ ⟪ andsB_LE : andsB xs =< x ⟫.

#[global]
Add Parametric Morphism :
  cl with signature (eqProp ==> eqProp)
  as cl_lifts_eqProp.
Proof.
  intros X X' X_eq_X' b. split; intros [xs ?]; des; exists (xs); unnw; split; eauto.
  all: ii; now eapply X_eq_X', FINITE_SUBSET.
Qed.

Lemma fact1_of_1_2_8 X
  : isFilter (cl X).
Proof with eauto with *.
  eapply isFilter_intro.
  - exists (trueB). exists ([]). unnw. split.
    + intros z z_in. inversion z_in.
    + rewrite andsB_zero...
  - unfold cl. intros x1 x2 [xs1 ?] [xs2 ?]; des. exists (xs1 ++ xs2). unnw. split.
    + ii. rewrite L.in_app_iff in H. done!.
    + rewrite andsB_app. eapply andB_compathWith_leProp...
  - intros x [xs ?] ? LE; des. exists (xs). unnw. split; [ | etransitivity]...
Qed.

Lemma fact2_of_1_2_8 X
  (X_isFilter : isFilter X)
  : trueB \in X.
Proof.
  inversion X_isFilter. eapply CLOSED_UPWARD with (x := andsB []).
  - eapply CLOSED_andsB. intros z z_in. inversion z_in.
  - red. reflexivity.
Qed.

Lemma fact3_of_1_2_8 X
  : X \subseteq cl X.
Proof with eauto with *.
  intros b b_in. exists ([b]). unnw. split.
  - intros z [z_eq_b | []]; subst z...
  - rewrite andsB_one...
Qed.

Lemma fact4_of_1_2_8 X X'
  (X_isSubsetOf_X' : X \subseteq X')
  : cl X \subseteq cl X'.
Proof.
  intros b b_in. destruct b_in as [xs ?]; des.
  exists (xs); unnw. split; eauto with *.
Qed.

Lemma fact5_of_1_2_8 X
  (X_isFilter : isFilter X)
  : cl X \subseteq X.
Proof.
  intros b b_in. destruct b_in as [xs ?]; des.
  inversion X_isFilter. eauto with *.
Qed.

#[global]
Instance cl_preserves_leProp : isMonotonic1 cl :=
  fact4_of_1_2_8.

#[global]
Instance cl_isClosureOperator
  : isClosureOperator cl.
Proof.
  split; i.
  - eapply fact3_of_1_2_8.
  - eapply leProp_antisymmetry.
    + eapply fact5_of_1_2_8. eapply fact1_of_1_2_8.
    + eapply fact4_of_1_2_8. eapply fact3_of_1_2_8.
  - ii; eapply fact4_of_1_2_8; done!.
Qed.

Lemma proposition1_of_1_2_9 X
  (X_isFilter : isFilter X)
  : forall b, b \in X -> forall b', b == b' -> b' \in X.
Proof.
  ii. inversion X_isFilter. eauto with *.
Qed.

Definition isElementCompleteFor X b : Prop :=
  forall EQUICONSISTENT : equiconsistent X (cl (E.insert b X)), b \in X.

Definition isComplete X : Prop :=
  forall b, isElementCompleteFor X b.

Variant isUltraFilter F : Prop :=
  | isUltraFilterIf
    (IS_FILTER : isFilter F)
    (ULTRAFILTER : forall F', isFilter F' -> forall EQUICONSISTENT : equiconsistent F F', F \subseteq F' -> F == F')
    : isUltraFilter F.

End BOOLEAN_ALGEBRA.

Class isCBA (B : Type) {SETOID : isSetoid B} : Type :=
  { CBA_isBA :: isBA B
  ; CBA_satisfiesBooleanAlgebraLaws :: BooleanAlgebraLaws CBA_isBA
  ; CBA_countable :: isEnumerable B
  }.

Section section_2_of_chapter_1_PART2. (* Reference: << Constructive Completeness Proofs and Delimited Control >> written by "Danko Ilik" *)

Context {B : Type} {SETOID : isSetoid B} {CBA : isCBA B}.

Variant insertion X n : ensemble B :=
  | In_insertion
    (EQUICONSISTENT : equiconsistent X (cl (E.insert (enum n) X)))
    : enum n \in insertion X n.

#[global]
Add Parametric Morphism :
  insertion with signature (eqProp ==> eq ==> eqProp)
  as insertion_lifts_eqProp.
Proof with eauto with *.
  enough (to_show : forall X, forall X', X == X' -> forall n, insertion X n \subseteq insertion X' n).
  { ii. split; eapply to_show... }
  intros X X' X_eq_X' n b b_in.
  inversion b_in; subst. econstructor. rewrite <- X_eq_X' at 1.
  rewrite EQUICONSISTENT. clear EQUICONSISTENT b_in.
  enough (EQUAL : cl (E.insert (enum n) X) == cl (E.insert (enum n) X')).
  { red. now rewrite EQUAL. }
  now rewrite X_eq_X'.
Qed.

Definition Insertion X n : ensemble B :=
  E.union X (insertion X n).

Fixpoint improveFilter (X : ensemble B) (n : nat) {struct n} : ensemble B :=
  match n with
  | O => X
  | S n' => cl (Insertion (improveFilter X n') n')
  end.

Definition completeFilterOf X : ensemble B :=
  fun b => exists n, b \in improveFilter X n.

Lemma lemma1_of_1_2_11 n
  : forall X, isFilter X -> isFilter (improveFilter X n).
Proof.
  induction n as [ | n IH]; simpl; eauto.
  ii. eapply fact1_of_1_2_8.
Qed.

Lemma lemma1_of_1_2_12 (n1 : nat) (n2 : nat)
  (n1_le_n2 : n1 <= n2)
  : forall X, improveFilter X n1 \subseteq improveFilter X n2.
Proof with eauto with *.
  change (forall X : ensemble B, improveFilter X n1 =< improveFilter X n2).
  induction n1_le_n2 as [ | n2 n1_le_n2 IH]; intros X...
  rewrite IH with (X := X). transitivity (Insertion (improveFilter X n2) n2).
  - intros z z_in; left...
  - simpl; eapply fact3_of_1_2_8...
Qed.

Lemma lemma1_of_1_2_13_aux1 bs F n
  (F_isFilter : isFilter F)
  (FINITE_SUBSET : L.is_finsubset_of bs (E.union (improveFilter F n) (insertion (improveFilter F n) n)))
  : andsB bs \in improveFilter F n \/ (exists b, L.In b bs /\ b \in insertion (improveFilter F n) n).
Proof.
  revert F n F_isFilter FINITE_SUBSET. induction bs as [ | b1 bs1 IH]; simpl; ii.
  - left. now eapply fact2_of_1_2_8, lemma1_of_1_2_11.
  - pose proof (lemma1_of_1_2_11 n F F_isFilter) as claim1. inversion claim1. unnw.
    assert (H_IN : b1 \in improveFilter F n \/ b1 \in insertion (improveFilter F n) n).
    { rewrite <- E.in_union_iff. eapply FINITE_SUBSET. now left. }
    assert (claim2 : L.is_finsubset_of bs1 (E.union (improveFilter F n) (insertion (improveFilter F n) n))).
    { ii. eapply FINITE_SUBSET. now right. }
    pose proof (IH F n F_isFilter claim2) as [H_in | [b [b_in b_in_insertion]]].
    { destruct H_IN as [H_IN | H_IN].
      - left. eapply CLOSED_andsB with (xs := b1 :: bs1).
        intros z [z_eq_b | z_in_bs1].
        + now subst z.
        + eapply CLOSED_UPWARD with (x := andsB bs1); trivial.
          now eapply andsB_le_In.
      - right. exists (b1). split; trivial. now left.
    }
    { right. exists (b). split; trivial. now right. }
Qed.

Lemma lemma1_of_1_2_13_aux2 X n
  : Insertion (improveFilter X n) n \subseteq E.insert (enum n) (improveFilter X n).
Proof.
  intros ? [? | ?]; [right | left]; trivial.
  inversion H_inr; subst. reflexivity.
Qed.

Lemma lemma1_of_1_2_13 (F : ensemble B) n
  (F_isFilter : isFilter F)
  : equiconsistent F (improveFilter F n).
Proof.
  revert F F_isFilter. induction n as [ | n IH]; simpl; ii.
  - reflexivity.
  - rewrite IH with (F_isFilter := F_isFilter) at 1.
    split; intros INCONSISTENT.
    { eapply inconsistent_compatWith_isSubsetOf.
      - exact INCONSISTENT.
      - change (improveFilter F n =< cl (Insertion (improveFilter F n) n)).
        rewrite <- fact3_of_1_2_8. ii; now left.
    }
    { destruct INCONSISTENT as [botB [botB_in botB_eq_falseB]].
      destruct botB_in as [xs ?]; des.
      pose proof (lemma1_of_1_2_11 n F F_isFilter) as claim1. inversion claim1; unnw.
      assert (claim2 : cl (Insertion (improveFilter F n) n) \subseteq cl (E.insert (enum n) (improveFilter F n))).
      { eapply fact4_of_1_2_8, lemma1_of_1_2_13_aux2. }
      pose proof (lemma1_of_1_2_13_aux1 xs F n F_isFilter FINITE_SUBSET) as [H_in | [b [b_in b_in_insertion]]].
      - exists (andB botB (andsB xs)). split.
        + eapply CLOSED_UPWARD with (x := andsB xs); trivial.
          rewrite <- andsB_LE, andB_idem. reflexivity.
        + rewrite botB_eq_falseB. change (falseB =< andsB xs). eapply falseB_isBottom.
      - inversion b_in_insertion; subst. eapply EQUICONSISTENT. exists (andsB xs). split.
        + eapply claim2. exists (xs). split; unnw; trivial.
        + eapply @leProp_antisymmetry with (A_isProset := BA_isProset).
          { now rewrite <- botB_eq_falseB. }
          { eapply falseB_isBottom. }
    }
Qed.

Lemma lemma2_of_1_2_13 F n1 n2
  (F_isFilter : isFilter F)
  : equiconsistent (improveFilter F n1) (improveFilter F n2).
Proof.
  transitivity (F).
  - symmetry. now eapply lemma1_of_1_2_13.
  - now eapply lemma1_of_1_2_13.
Qed.

Lemma lemma3_of_1_2_13 F
  (F_isFilter : isFilter F)
  : equiconsistent F (completeFilterOf F).
Proof.
  split; intros [botB [botB_in botB_eq_falseB]].
  - exists (botB). split.
    + exists (0). trivial.
    + trivial.
  - destruct botB_in as [n H_IN].
    eapply lemma1_of_1_2_13; trivial.
    exists (botB); eauto.
Qed.

Theorem theorem_of_1_2_14_aux1 F n
  (F_isFilter : isFilter F)
  (EQUICONSISTENT : equiconsistent (completeFilterOf F) (cl (E.insert (enum n) (completeFilterOf F))))
  : equiconsistent (improveFilter F n) (cl (E.insert (enum n) (improveFilter F n))).
Proof.
  split.
  - intros [botB [botB_in botB_eq_falseB]].
    exists (botB). split; trivial.
    eapply fact3_of_1_2_8. now right.
  - intros INCONSISTENT.
    pose proof (claim1 := lemma1_of_1_2_13 F n F_isFilter).
    pose proof (claim2 := lemma3_of_1_2_13 F F_isFilter).
    assert (claim3 : inconsistent (cl (E.insert (enum n) (completeFilterOf F)))).
    { eapply inconsistent_compatWith_isSubsetOf.
      - exact (INCONSISTENT).
      - eapply fact4_of_1_2_8.
        intros z z_in. rewrite E.in_insert_iff in z_in. destruct z_in as [z_in | z_in].
        + subst z. now left.
        + right. now exists (n).
    }
    unfold equiconsistent in *. tauto. 
Qed.

Variant completeFilterOf_spec X F : Prop :=
  | completeFilterOf_spec_intro
    (SUBSET : X \subseteq F)
    (IS_FILTER : isFilter F)
    (COMPLETE : isComplete F)
    (EQUICONSISTENT : equiconsistent X F)
    : completeFilterOf_spec X F.

Theorem theorem_of_1_2_14 F
  (F_isFilter : isFilter F)
  : completeFilterOf_spec F (completeFilterOf F).
Proof.
  inversion F_isFilter. split.
  - intros z z_in. exists (0). trivial.
  - eapply isFilter_intro.
    + exists (trueB). exists (0). eapply fact2_of_1_2_8. trivial.
    + intros ? ? [n1 H_IN1] [n2 H_IN2].
      assert (n1 <= n2 \/ n2 <= n1) as [n1_le_n2 | n2_le_n1] by lia.
      { pose proof (lemma1_of_1_2_12 n1 n2 n1_le_n2 F x1 H_IN1) as claim1.
        pose proof (lemma1_of_1_2_11 n2 F F_isFilter) as [claim2 claim3].
        exists (n2). eapply claim3 with (x := andsB [x1; x2]); unnw.
        - eapply claim2. now intros z [z_eq | [z_eq | []]]; subst z.
        - now rewrite andsB_two.
      }
      { pose proof (lemma1_of_1_2_12 n2 n1 n2_le_n1 F x2 H_IN2) as claim1.
        pose proof (lemma1_of_1_2_11 n1 F F_isFilter) as [claim2 claim3].
        exists (n1). eapply claim3 with (x := andsB [x1; x2]); unnw.
        - eapply claim2. now intros z [z_eq | [z_eq | []]]; subst z.
        - now rewrite andsB_two.
      }
    + intros ? [n ?] x' LE. pose proof (lemma1_of_1_2_11 n F F_isFilter) as [claim1 claim2].
      exists (n). eapply claim2; eauto.
  - ii. pose proof (enum_spec b) as [n b_eq_enum_n]. subst b.
    pose proof (claim1 := theorem_of_1_2_14_aux1 F n F_isFilter EQUICONSISTENT).
    exists (1 + n). simpl. exists ([enum n]). split.
    + intros z [z_eq | []]; subst z. right. now econstructor.
    + unnw. now rewrite andsB_one.
  - now eapply lemma3_of_1_2_13.
Qed.

Corollary corollary_of_1_2_16_aux1 X F b
  (SUBSET : completeFilterOf X \subseteq F)
  (H_IN : b \in F)
  (INCONSISTENT : inconsistent (cl (E.insert b (completeFilterOf X))))
  : inconsistent (cl (E.insert b F)).
Proof.
  assert (claim1 : (E.insert b (completeFilterOf X)) \subseteq (E.insert b F)).
  { intros z [z_in | z_in]; [now left | right; now eapply SUBSET]. }
  destruct INCONSISTENT as [botB [botB_in botB_eq_falseB]].
  assert (claim2 : (cl (E.insert b (completeFilterOf X))) \subseteq (cl (E.insert b F))).
  { now eapply fact4_of_1_2_8. }
  exists (botB). split; trivial. now eapply claim2.
Qed.

Corollary corollary_of_1_2_16_aux2 X F
  (F_isFilter : isFilter F)
  (EQUICONSISTENT : equiconsistent (completeFilterOf X) F)
  (SUBSET : completeFilterOf X \subseteq F)
  : forall b, b \in F -> equiconsistent (completeFilterOf X) (cl (E.insert b (completeFilterOf X))).
Proof.
  intros b H_IN.
  assert (claim1 : (cl (E.insert b F)) \subseteq (cl F)).
  { eapply fact4_of_1_2_8. intros z [z_in | z_in]; trivial. repeat red in z_in. now subst. }
  split; intros INCONSISTENT.
  - destruct INCONSISTENT as [botB [botB_in botB_eq_falseB]].
    exists (botB). split; trivial.
    eapply fact3_of_1_2_8. now right.
  - pose proof (corollary_of_1_2_16_aux1 X F b SUBSET H_IN INCONSISTENT) as [botB [botB_in botB_eq_falseB]].
    eapply EQUICONSISTENT. exists (botB). split; trivial.
    eapply fact5_of_1_2_8; trivial. now eapply claim1.
Qed.

Corollary corollary_of_1_2_16 F
  (F_isFilter : isFilter F)
  : isUltraFilter (completeFilterOf F).
Proof.
  pose proof (theorem_of_1_2_14 F F_isFilter) as [? ? ? ?]. split; trivial.
  intros F' IS_FILTER' EQUICONSISTENT' SUBSET' b; unnw. split.
  - exact (SUBSET' b).
  - intros H_IN.
    enough (claim1 : equiconsistent (completeFilterOf F) (cl (E.insert b (completeFilterOf F)))).
    { now eapply COMPLETE. }
    eapply corollary_of_1_2_16_aux2; eauto.
Qed.

End section_2_of_chapter_1_PART2.
