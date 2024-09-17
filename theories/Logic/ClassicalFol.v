Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Data.Vector.
Require Import PnV.Math.BooleanAlgebra.
Require Import PnV.Logic.BasicFol.
Require Import PnV.Logic.HilbertFol.
Require Import PnV.Logic.HilbertFol2.

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
