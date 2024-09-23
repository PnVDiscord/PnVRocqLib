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

Section MODEL_EXISTENCE.

Context {L : language} (D := ensemble (trm L)).

Fixpoint Pairing {A : Type} {n : nat} (P : trm L -> A -> Prop) (xs : trms L n) : Vector.t A n -> Prop :=
  match xs with
  | O_trms => fun xs => True
  | S_trms n t ts => fun xs => P t (V.head xs) /\ Pairing P ts (V.tail xs)
  end.

(*
Variable Gamma : ensemble (frm L).

Theorem Pairing_lemma (n : nat) (ts : trms L n) (xs1 : Vector.t D n) (xs2 : Vector.t D n)
  (EQ : forall i, forall x, x \in xs1 !! i <-> x \in xs2 !! i)
  : Pairing E.In ts xs1 <-> Pairing E.In ts xs2.
Proof.
  revert xs1 xs2 EQ. induction ts as [ | n t ts IH]; simpl.
  - introVNil; introVNil; simpl; i; reflexivity.
  - introVCons x1 xs1; introVCons x2 xs2; simpl; i.
    rewrite EQ with (i := FZ). rewrite IH with (xs2 := xs2). reflexivity. i. eapply EQ with (i := FS i).
Qed.

Definition function_interpret (f : L.(function_symbols)) (vs : Vector.t D (L.(function_arity_table) f)) : D :=
  fun t : trm L => exists ts, Pairing E.In ts vs /\ Eqn_frm (Fun_trm f ts) t \in Gamma.

Definition constant_interpret (c : L.(constant_symbols)) : D :=
  fun t : trm L => Eqn_frm (Con_trm c) t \in Gamma.

Definition relation_interpret (R : L.(relation_symbols)) (vs : Vector.t D (L.(relation_arity_table) R)) : Prop :=
  exists ts, Pairing E.In ts vs /\ Rel_frm R ts \in Gamma.

#[local, program]
Instance mkModel : isStructureOf L :=
  { domain_of_discourse := ensemble (trm L)
  ; equation_interpret := E.ensemble_isProset.(Proset_isSetoid)
  ; function_interpret := function_interpret
  ; constant_interpret := constant_interpret
  ; relation_interpret := relation_interpret
  }.
Next Obligation.
  econs. exact (E.empty).
Qed.
Next Obligation.
  revert f vs1 vs2 EQ x.
  enough (WTS : forall f, forall vs1, forall vs2, (forall i, forall x, x \in vs1 !! i <-> x \in vs2 !! i) -> forall x, x \in function_interpret f vs1 -> x \in function_interpret f vs2).
  { ii. split. eapply WTS; trivial. eapply WTS. intros i t. rewrite EQ. reflexivity. }
  unfold function_interpret. intros f vs1 vs2 EQ t IN. red in IN. red.
  destruct IN as [ts [PAIRING IN]]. exists ts. split; trivial. rewrite <- Pairing_lemma; eauto.
Qed.
Next Obligation.
  revert R vs1 vs2 EQ.
  enough (WTS : forall R, forall vs1, forall vs2, (forall i, forall x, x \in vs1 !! i <-> x \in vs2 !! i) -> relation_interpret R vs1 -> relation_interpret R vs2).
  { ii. split. eapply WTS; trivial. eapply WTS. intros i t. rewrite EQ. reflexivity. }
  unfold relation_interpret. intros f vs1 vs2 EQ IN.
  destruct IN as [ts [PAIRING IN]]. exists ts. split; trivial. rewrite <- Pairing_lemma; eauto.
Qed.

Definition ivar_interpret : ivar -> domain_of_discourse :=
  fun z : ivar => fun t : trm L => Eqn_frm (Var_trm z) t \in Gamma.
*)

End MODEL_EXISTENCE.

Context {L : language} {enum_function_symbols : isEnumerable L.(function_symbols)} {enum_constant_symbols : isEnumerable L.(constant_symbols)} {enum_relation_symbols : isEnumerable L.(relation_symbols)}.

Notation L' := (augmented_language L Henkin_constants).

#[local]
Instance augmented_language_isEnumerable : isEnumerable (frm L') :=
  @frm_isEnumerable L' enum_function_symbols (@sum_isEnumerable L.(constant_symbols) Henkin_constants enum_constant_symbols nat_isEnumerable) enum_relation_symbols.

#[local] Hint Resolve fact1_of_1_2_8 fact2_of_1_2_8 fact3_of_1_2_8 fact4_of_1_2_8 fact5_of_1_2_8 lemma1_of_1_2_11 : core.

(* Theorem HilbertCalculus_complete (Gamma : ensemble (frm L)) (C : frm L)
  (PROVE : Gamma ⊨ C)
  : Gamma ⊢ C.
Proof with eauto with *.
  eapply NNPP. intros NO.
  set (X := E.insert (Neg_frm C) Gamma).
  assert (CONSISTENT : X ⊬ Bot_frm).
  { intros INCONSISTENT. contradiction NO. eapply NegationE... }
  exploit (@theorem_of_1_2_14 (frm L') (@formula_isSetoid L') LindenbaumBooleanAlgebra (Th (AddHenkin (E.image embed_frm X)))).
  { eapply lemma1_of_1_3_8. }
  intros [SUBSET' IS_FILTER' COMPLETE' EQUICONSISTENT']. fold (MaximallyConsistentSet (AddHenkin (E.image embed_frm X))) in SUBSET', IS_FILTER', COMPLETE', EQUICONSISTENT'.
Qed. *)

End COMPLETENESS_OF_HilbertCalculus.
