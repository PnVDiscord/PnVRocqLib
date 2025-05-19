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

Context {L : language} {function_symbols_countable : isCountable L.(function_symbols)} {constant_symbols_countable : isCountable L.(constant_symbols)} {relation_symbols_countable : isCountable L.(relation_symbols)}.

Notation L' := (augmented_language L Henkin_constants).

#[local] Existing Instance trmModel.

#[local] Hint Resolve fact1_of_1_2_8 fact2_of_1_2_8 fact3_of_1_2_8 fact4_of_1_2_8 fact5_of_1_2_8 lemma1_of_1_2_11 : core.

Theorem HilbertCalculus_countable_complete (X : ensemble (frm L)) (b : frm L)
  (CONSEQUENCE : X ⊨ b)
  : X ⊢ b.
Proof with eauto with *.
  eapply NNPP. intros NO.
  set (Gamma := E.insert (Neg_frm b) X).
  assert (CONSISTENT : Gamma ⊬ Bot_frm).
  { intros INCONSISTENT. contradiction NO. eapply NegationE... }
  pose proof (@theorem_of_1_3_10 L augmented_language_isEnumerable Gamma) as [? ? ? ? ? ?]; unnw.
  assert (claim : Gamma ⊭ Bot_frm).
  { intros SAT. contradiction (SAT (restrict_structure (trmModel Gamma)) (ivar_interpret Gamma)).
    - red. set (STRUCTURE := trmModel Gamma). set (env := ivar_interpret Gamma).
      assert (MODEL : forall p : frm L, interpret_frm STRUCTURE env (embed_frm p) <-> interpret_frm (restrict_structure STRUCTURE) env p).
      { intros p. eapply restrict_structure_frm. }
      ii. red. rewrite <- MODEL. unfold STRUCTURE, env. rewrite <- trmModel_isModel; trivial.
      eapply SUBSET. rewrite in_Th_iff. eapply ByAssumption. done!.
    - simpl. intros t. unfold interpret_equation, ivar_interpret. simpl. eapply proves_reflexivity.
  }
  contradiction claim. intros ? ? ? SAT. unfold Gamma in SATISFY.
  red in SATISFY. pose proof (SATISFY (Neg_frm b)) as CONTRA. simpl in CONTRA. contradiction CONTRA.
  - left. reflexivity.
  - eapply CONSEQUENCE. ii. eapply SATISFY. right. trivial.
Qed.

End COMPLETENESS_OF_HilbertCalculus.
