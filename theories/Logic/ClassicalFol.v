Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Data.Vector.
Require Import PnV.Math.BooleanAlgebra.
Require Import PnV.Logic.BasicFol.
Require Import PnV.Logic.BasicFol2.
Require Import PnV.Logic.HilbertFol.
Require Import PnV.Logic.HilbertFol2.
Require Import PnV.Math.ThN.

Import FolNotations.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.
#[local] Notation In := L.In.

Section SOUNDNESS_OF_HilbertCalculus.

Import FolHilbert.

#[local] Existing Instance V.vec_isSetoid.

Context {L : language}.

Theorem HilbertCalculus_sound (Gamma : ensemble (frm L)) (C : frm L)
  (PROVE : Gamma ⊢ C)
  : Gamma ⊨ C.
Proof with eauto with *.
  destruct PROVE as (ps & INCL & (PF)). revert Gamma INCL. induction PF; ii.
  - eapply SATISFY. done!.
  - eapply MP_preserves_truth with (p := p) (ps1 := ps1) (ps2 := ps2)...
  - eapply Gen_preserves_truth with (ps := ps)...
  - done!.
  - done!.
  - simpl in H. pose proof (classic (satisfies_frm STRUCTURE env q)). done!.
  - simpl in H. rewrite <- substitution_lemma_frm. specialize (H (interpret_trm STRUCTURE env t)).
    eapply interpret_frm_ext_upto with (env := upd_env x (interpret_trm STRUCTURE env t) env); trivial.
    ii. unfold "∘". unfold upd_env, one_subst, cons_subst, nil_subst. destruct (eq_dec z x) as [EQ | NE]... reflexivity.
  - rewrite <- not_free_no_effect_on_interpret_frm...
  - red in H, H0. simpl in H, H0. red. specialize (H y_value); specialize (H0 y_value)...
  - cbn; done!.
  - cbn in *; done!.
  - now cbn in *; transitivity (env 1).
  - eapply Fun_eqAxm_preserves_truth.
  - eapply Rel_eqAxm_preserves_truth.
Qed.

End SOUNDNESS_OF_HilbertCalculus.

Section COMPLETENESS_OF_HilbertCalculus.

Import FolHilbert.

#[local] Existing Instance V.vec_isSetoid.

Context {L : language} {enum_function_symbols : isEnumerable L.(function_symbols)} {enum_constant_symbols : isEnumerable L.(constant_symbols)} {enum_relation_symbols : isEnumerable L.(relation_symbols)}.

Notation L' := (augmented_language L Henkin_constants).

#[local]
Instance augmented_language_isEnumerable : isEnumerable (frm L') :=
  @frm_isEnumerable L' enum_function_symbols (@sum_isEnumerable L.(constant_symbols) Henkin_constants enum_constant_symbols nat_isEnumerable) enum_relation_symbols.

Section MODEL_EXISTENCE.

Variable X : ensemble (frm L).

Let Delta : ensemble (frm L') :=
  MaximallyConsistentSet (AddHenkin (E.image embed_frm X)).

Let D : Type :=
  trm L'.

Definition interpret_equation (lhs : D) (rhs : D) : Prop :=
  Delta ⊢ Eqn_frm lhs rhs.

#[global]
Instance interpret_equation_Equivalence
  : Equivalence interpret_equation.
Proof with eauto.
  unfold interpret_equation. split.
  - intros x. eapply proves_reflexivity...
  - intros x y EQ. eapply proves_symmetry...
  - intros x y z EQ EQ'. eapply proves_transitivity...
Qed.

Lemma pairwise_equal_intro n vs1 vs2
  (EQ : forall i : Fin.t n, interpret_equation (vs1 !! i) (vs2 !! i))
  : pairwise_equal Delta (vec_to_trms vs1) (vec_to_trms vs2).
Proof.
  revert vs2 EQ. induction vs1 as [ | n v1 vs1 IH].
  - introVNil; simpl; i. econs.
  - introVCons v2 vs2; simpl; i. econs.
    + eapply EQ with (i := FZ).
    + eapply IH. intros i. eapply EQ with (i := FS i).
Qed.

Lemma pairwise_equal_symmetry n (vs1 : Vector.t (trm L') n) (vs2 : Vector.t (trm L') n)
  (EQUAL : pairwise_equal Delta (vec_to_trms vs1) (vec_to_trms vs2))
  : pairwise_equal Delta (vec_to_trms vs2) (vec_to_trms vs1).
Proof.
  revert vs2 EQUAL. induction vs1 as [ | n v1 vs1 IH].
  - introVNil; simpl; i. econs.
  - introVCons v2 vs2; simpl; intros [EQ EQUAL]. econs.
    + eapply proves_symmetry; trivial.
    + eapply IH; trivial.
Qed.

#[local, program]
Instance mkModel : isStructureOf L' :=
  { domain_of_discourse := D
  ; equation_interpret := {| eqProp := interpret_equation; eqProp_Equivalence := interpret_equation_Equivalence |}
  ; function_interpret f vs := Fun_trm f (vec_to_trms vs)
  ; constant_interpret c := Con_trm c
  ; relation_interpret R vs := Delta ⊢ Rel_frm R (vec_to_trms vs)
  }.
Next Obligation.
  econs. exact (Var_trm 0).
Qed.
Next Obligation.
  red. eapply proves_eqn_fun. eapply pairwise_equal_intro; trivial.
Qed.
Next Obligation.
  split; intros INFERS.
  - eapply for_Imp_E. eapply proves_eqn_rel. 2: exact INFERS. eapply pairwise_equal_intro; trivial.
  - eapply for_Imp_E. eapply proves_eqn_rel. 2: exact INFERS. eapply pairwise_equal_symmetry; eapply pairwise_equal_intro; trivial.
Qed.

Definition ivar_interpret : ivar -> domain_of_discourse :=
  Var_trm.

Lemma interpret_trm_MkModel_ivar_interpret (t : trm L')
  : interpret_trm mkModel ivar_interpret t = t
with interpret_trms_MkModel_ivar_interpret n (ts : trms L' n)
  : vec_to_trms (interpret_trms mkModel ivar_interpret ts) = ts.
Proof.
  - trm_ind t; simpl.
    + reflexivity.
    + rewrite interpret_trm_unfold. simpl. f_equal. eapply interpret_trms_MkModel_ivar_interpret.
    + reflexivity.
  - trms_ind ts.
    + reflexivity.
    + rewrite interpret_trms_unfold. simpl. f_equal.
      * eapply interpret_trm_MkModel_ivar_interpret.
      * eapply IH.
Qed.

Theorem mkModel_isModel (p : frm L')
  (CONSISTENT : X ⊬ Bot_frm)
  : p \in Delta <-> interpret_frm mkModel ivar_interpret p.
Proof with eauto with *.
  exploit (@theorem_of_1_2_14 (frm L') (@formula_isSetoid L') LindenbaumBooleanAlgebra (Th (AddHenkin (E.image embed_frm X)))).
  { eapply lemma1_of_1_3_8. }
  intros [SUBSET' IS_FILTER' COMPLETE' EQUICONSISTENT']. fold (MaximallyConsistentSet (AddHenkin (E.image embed_frm X))) in SUBSET', IS_FILTER', COMPLETE', EQUICONSISTENT'.
  fold Delta in SUBSET', IS_FILTER', COMPLETE', EQUICONSISTENT'.
  pose proof (theorem_of_1_3_10 X) as [? ? ? ? ? ?]. fold Delta in SUBSET, EQUICONSISTENT, CLOSED_infers, META_DN, IMPLICATION_FAITHFUL, FORALL_FAITHFUL. unnw.
  assert (CONSISTENT' : Delta ⊬ Bot_frm).
  { intros INCONSISTENT.
    assert (claim1 : ~ BooleanAlgebra.inconsistent Delta).
    { red in EQUICONSISTENT'. rewrite <- EQUICONSISTENT'. rewrite <- cl_eq_Th. rewrite <- inconsistent_okay. rewrite <- AddHenkin_equiconsistent.
      - rewrite <- similar_equiconsistent with (Gamma := X).
        + rewrite inconsistent_iff; trivial.
        + rewrite <- embed_frms_spec. reflexivity.
      - ii. rewrite E.in_image_iff in H. destruct H as [q [-> IN]]. eapply embed_frm_HC_free.
    }
    contradiction claim1. rewrite <- inconsistent_iff in INCONSISTENT.
    rewrite inconsistent_okay in INCONSISTENT. eapply inconsistent_compatWith_isSubsetOf... eapply fact5_of_1_2_8...
  }
  rewrite CLOSED_infers. pattern p. revert p. eapply @frm_depth_lt_ind. intros [R ts | t1 t2 | p1 | p1 p2 | y p1]; simpl; i.
  - rewrite interpret_trms_MkModel_ivar_interpret. reflexivity.
  - do 2 rewrite interpret_trm_MkModel_ivar_interpret. reflexivity.
  - rewrite <- IH with (p' := p1). 2: lia. split.
    + intros INFERS1 INFERS2. contradiction CONSISTENT'.
      eapply ContradictionI with (A := p1); trivial.
    + intros NO. eapply NNPP. intros CONTRA. contradiction NO.
      rewrite <- CLOSED_infers. eapply META_DN. intros INFERS. rewrite CLOSED_infers in INFERS. contradiction.
  - rewrite <- IH with (p' := p1). 2: lia. rewrite <- IH with (p' := p2). 2: lia. split.
    + intros INFERS1 INFERS2. eapply ImplicationE with (A := p1); trivial.
    + intros INFERS. rewrite <- CLOSED_infers. eapply IMPLICATION_FAITHFUL. do 2 rewrite CLOSED_infers; trivial.
  - unfold D. split.
    + intros INFERS t. rename y into x. set (s := one_subst x t).
      assert (IFF : interpret_frm mkModel ivar_interpret (subst_frm s p1) <-> interpret_frm mkModel (upd_env x t ivar_interpret) p1).
      { rewrite <- substitution_lemma_frm. eapply interpret_frm_ext. ii. unfold compose, upd_env, s, one_subst, cons_subst, nil_subst.
        destruct (eq_dec z x) as [EQ1 | NE1]; trivial. eapply interpret_trm_MkModel_ivar_interpret.
      }
      rewrite <- IFF. rewrite <- IH with (p' := subst_frm s p1). 2: rewrite subst_preserves_rank; lia.
      unfold s. eapply for_All_E; trivial.
    + intros INTERPRET. rewrite <- CLOSED_infers. eapply FORALL_FAITHFUL.
      intros t. eapply CLOSED_infers. rewrite -> IH with (p' := subst_frm (one_subst y t) p1). 2: rewrite subst_preserves_rank; lia.
      rewrite <- substitution_lemma_frm. eapply interpret_frm_ext with (env' := upd_env y (interpret_trm mkModel ivar_interpret t) ivar_interpret). ii. unfold compose, upd_env, one_subst, cons_subst, nil_subst.
      destruct (eq_dec z y) as [EQ1 | NE1]; trivial. eapply INTERPRET.
Qed.

End MODEL_EXISTENCE.

#[local] Hint Resolve fact1_of_1_2_8 fact2_of_1_2_8 fact3_of_1_2_8 fact4_of_1_2_8 fact5_of_1_2_8 lemma1_of_1_2_11 : core.

Theorem HilbertCalculus_complete (X : ensemble (frm L)) (b : frm L)
  (CONSEQUENCE : X ⊨ b)
  : X ⊢ b.
Proof with eauto with *.
  eapply NNPP. intros NO.
  set (Gamma := E.insert (Neg_frm b) X).
  assert (CONSISTENT : Gamma ⊬ Bot_frm).
  { intros INCONSISTENT. contradiction NO. eapply NegationE... }
  exploit (@theorem_of_1_2_14 (frm L') (@formula_isSetoid L') LindenbaumBooleanAlgebra (Th (AddHenkin (E.image embed_frm Gamma)))).
  { eapply lemma1_of_1_3_8. }
  intros [SUBSET' IS_FILTER' COMPLETE' EQUICONSISTENT']. fold (MaximallyConsistentSet (AddHenkin (E.image embed_frm Gamma))) in SUBSET', IS_FILTER', COMPLETE', EQUICONSISTENT'.
  pose proof (theorem_of_1_3_10 Gamma) as [? ? ? ? ? ?]. unnw.
  assert (claim : Gamma ⊭ Bot_frm).
  { intros SAT. contradiction (SAT (restrict_structure (mkModel Gamma)) (ivar_interpret Gamma)).
    - red. set (STRUCTURE := mkModel Gamma). set (env := ivar_interpret Gamma).
      assert (MODEL : forall p : frm L, interpret_frm STRUCTURE env (embed_frm p) <-> interpret_frm (restrict_structure STRUCTURE) env p).
      { intros p. eapply restrict_structure_frm. }
      ii. red. rewrite <- MODEL. unfold STRUCTURE, env. rewrite <- mkModel_isModel; trivial.
      eapply SUBSET. rewrite in_Th_iff. eapply ByAssumption. done!.
    - simpl. intros t. unfold interpret_equation, ivar_interpret. simpl. eapply proves_reflexivity.
  }
  contradiction claim. intros ? ? ? SAT. unfold Gamma in SATISFY.
  red in SATISFY. pose proof (SATISFY (Neg_frm b)) as CONTRA. simpl in CONTRA. contradiction CONTRA.
  - left. reflexivity.
  - eapply CONSEQUENCE. ii. eapply SATISFY. right. trivial.
Qed.

End COMPLETENESS_OF_HilbertCalculus.
