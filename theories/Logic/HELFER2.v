Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Math.ThN.
Require Import PnV.Math.BooleanAlgebra.
Require Import PnV.Math.ClassicalSetTheory.
Require Import PnV.Data.Vector.
Require Import Stdlib.Arith.Wf_nat.
Require Export PnV.Logic.HELFER1.

#[local] Hint Rewrite @eqb_spec@{Set} : simplication_hints.

Module HELFER2.

Import FolNotations.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.
#[local] Notation In := L.In.

Import FolHilbert.

#[local] Hint Resolve fact1_of_1_2_8 fact2_of_1_2_8 fact3_of_1_2_8 fact4_of_1_2_8 fact5_of_1_2_8 lemma1_of_1_2_11 : core.

Section COMPLETENESS_OF_HilbertCalculus.

Import HELFER1_i.
Import HELFER1_ii.

#[local] Existing Instance V.vec_isSetoid.

Context `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}.

Context {L : language} {function_symbols_hasEqDec : hasEqDec L.(function_symbols)} {constant_symbols_hasEqDec : hasEqDec L.(constant_symbols)} {relation_symbols_hasEqDec : hasEqDec L.(relation_symbols)}.

#[local] Notation L' := (augmented_language L (Henkin_constants L)).

#[local] Existing Instance Henkin_constants_hasEqDec.

#[local] Existing Instance abstract_Henkin_constants_instance.

Variable X : ensemble (frm L).

Hypothesis CONSISTENT : X ⊬ Bot_frm.

Let Hbase : ensemble (frm L') :=
  E.union HenkinAxiomSet (E.image embed_frm X).

Lemma Hbase_consistent
  : ~ Hbase ⊢ Bot_frm.
Proof.
  intros H.
  assert (INC : inconsistent Hbase).
  { rewrite inconsistent_iff. exact H. }
  unfold Hbase in INC.
  rewrite <- AddHenkin_embed_equiconsistent in INC.
  rewrite inconsistent_iff in INC.
  erewrite @embed_frm_proves_iff with (Henkin_constants := Henkin_constants L) (p := Bot_frm) in INC.
  apply CONSISTENT. exact INC.
Qed.

Let ConsistentExtension : Type :=
  { Delta : ensemble (frm L') | Hbase \subseteq Delta /\ ~ Delta ⊢ Bot_frm }.

#[local]
Instance ConsistentExtension_isProset : isProset ConsistentExtension :=
  subProset _.

Let ConsistentExtension_base : ConsistentExtension :=
  @exist _ _ Hbase (conj (reflexivity Hbase) Hbase_consistent).

Lemma chain_upperbound (C : ensemble ConsistentExtension)
  (NONEMPTY : exists d : ConsistentExtension, d \in C)
  (CHAIN : forall x1, forall x2 : ConsistentExtension, x1 \in C -> x2 \in C -> leProp x1 x2 \/ leProp x2 x1)
  : exists u : ConsistentExtension, forall d : ConsistentExtension, d \in C -> leProp d u.
Proof.
  set (U := fun p : frm L' => exists d : ConsistentExtension, d \in C /\ p \in proj1_sig d).
  assert (HSUB : Hbase \subseteq U).
  { intros p Hp. destruct NONEMPTY as [d0 Hd0]. exists d0. split; trivial.
    destruct d0 as [Delta0 [HB0 HC0]]. simpl. eapply HB0. exact Hp.
  }
  assert (HCONS : ~ U ⊢ Bot_frm).
  { intros PROV. destruct PROV as [ps [INCL [PF]]].
    assert (EACH : forall p, In p ps -> exists d : ConsistentExtension, d \in C /\ p \in proj1_sig d).
    { intros p Hp. apply INCL. eapply E.in_fromList_iff. exact Hp. }
    assert (UB_IN_CHAIN : exists d : ConsistentExtension, d \in C /\ forall p, In p ps -> p \in proj1_sig d).
    { clear INCL PF. induction ps as [ | q ps IH]; simpl in *.
      - destruct NONEMPTY as [d0 Hd0]. exists d0. split; trivial. intros p [].
      - assert (IHok : forall p, In p ps -> exists d : ConsistentExtension, d \in C /\ p \in proj1_sig d).
        { intros p Hp. eapply EACH. right. exact Hp. }
        specialize (IH IHok). destruct IH as [d_tail [Hd_tail Htail]].
        pose proof (EACH q (or_introl eq_refl)) as [d_q [Hd_q Hq_in]].
        pose proof (CHAIN d_q d_tail Hd_q Hd_tail) as [LE | LE].
        + exists d_tail. split; trivial. intros p [-> | Hp].
          * eapply LE. exact Hq_in.
          * eapply Htail. exact Hp.
        + exists d_q. split; trivial. intros p [-> | Hp].
          * exact Hq_in.
          * eapply LE. eapply Htail. exact Hp.
    }
    destruct UB_IN_CHAIN as [d [Hd Hps_in]].
    destruct d as [Delta [HBd HCd]]. simpl in Hps_in.
    apply HCd. exists ps. split.
    - intros p Hp. eapply E.in_fromList_iff in Hp. eapply Hps_in. exact Hp.
    - econs. exact PF.
  }
  exists (@exist _ _ U (conj HSUB HCONS)).
  intros d Hd. destruct d as [Delta [HBd HCd]]. simpl.
  intros p Hp. exists (@exist _ _ Delta (conj HBd HCd)). split; simpl; trivial.
Qed.

Lemma exists_MCS
  : exists Delta : ensemble (frm L'), Hbase \subseteq Delta /\ (~ Delta ⊢ Bot_frm) /\ (forall Delta' : ensemble (frm L'), Delta \subseteq Delta' -> (~ Delta' ⊢ Bot_frm) -> Delta' \subseteq Delta).
Proof.
  pose proof (Zorn's_lemma ConsistentExtension ConsistentExtension_isProset (inhabits ConsistentExtension_base)) as ZORN.
  exploit ZORN; unnw.
  { intros C NONEMPTY CHAIN. eapply chain_upperbound; eauto. }
  intros [d_m MAX]. destruct d_m as [Delta [HBd HCd]]. exists Delta.
  split; [| split]; eauto.
  intros Delta' SUB CONS'.
  specialize (MAX (@exist _ _ Delta' (conj (transitivity HBd SUB) CONS')) SUB).
  simpl in MAX. exact MAX.
Qed.

Section WITH_MCS.

Variable MaxCS : ensemble (frm L').

Hypothesis MaxCS_incl_Hbase : Hbase \subseteq MaxCS.

Hypothesis MaxCS_consistent : ~ MaxCS ⊢ Bot_frm.

Hypothesis MaxCS_maximal : forall Delta' : ensemble (frm L'), MaxCS \subseteq Delta' -> ~ Delta' ⊢ Bot_frm -> Delta' \subseteq MaxCS.

Lemma MaxCS_closed (p : frm L')
  (PROVE : MaxCS ⊢ p)
  : p \in MaxCS.
Proof.
  assert (CONS : ~ E.insert p MaxCS ⊢ Bot_frm).
  { intros INC. eapply MaxCS_consistent.
    assert (MaxCS ⊢ Imp_frm p Bot_frm).
    { eapply ImplicationI. exact INC. }
    eapply for_Imp_E; eauto.
  }
  eapply MaxCS_maximal with (Delta' := E.insert p MaxCS).
  - intros q Hq. right. exact Hq.
  - exact CONS.
  - left. reflexivity.
Qed.

Lemma MaxCS_infers_iff (p : frm L')
  : MaxCS ⊢ p <-> p \in MaxCS.
Proof.
  split.
  - eapply MaxCS_closed.
  - intros IN. eapply ByAssumption. exact IN.
Qed.

Lemma MaxCS_complete (p : frm L')
  : p \in MaxCS \/ Neg_frm p \in MaxCS.
Proof.
  destruct (classic (p \in MaxCS)) as [YES | NO]; [left; trivial |].
  right. eapply MaxCS_closed.
  eapply NegationI.
  assert (INC : E.insert p MaxCS ⊢ Bot_frm \/ ~ E.insert p MaxCS ⊢ Bot_frm) by eapply classic.
  destruct INC as [INC | NOINC]; trivial.
  exfalso. apply NO. eapply MaxCS_maximal with (Delta' := E.insert p MaxCS).
  + intros q Hq. right. exact Hq.
  + exact NOINC.
  + left. reflexivity.
Qed.

Lemma MaxCS_neg_iff (p : frm L')
  : p \in MaxCS <-> ~ Neg_frm p \in MaxCS.
Proof.
  split.
  - intros IN NEG. eapply MaxCS_consistent. eapply ContradictionI with (A := p).
    + eapply ByAssumption. exact IN.
    + eapply ByAssumption. exact NEG.
  - intros NNEG. destruct (MaxCS_complete p) as [YES | NO]; trivial. contradiction.
Qed.

Lemma MaxCS_META_DN (p : frm L')
  (NEGATION : Neg_frm p \in MaxCS -> Bot_frm \in MaxCS)
  : p \in MaxCS.
Proof.
  destruct (MaxCS_complete p) as [YES | NO]; trivial.
  exfalso. apply MaxCS_consistent.
  eapply ByAssumption. eapply NEGATION. exact NO.
Qed.

Lemma MaxCS_IMPLICATION_FAITHFUL (p q : frm L')
  : Imp_frm p q \in MaxCS <-> (p \in MaxCS -> q \in MaxCS).
Proof.
  split.
  - intros IMP IN. eapply MaxCS_closed.
    eapply ImplicationE with (A := p).
    + eapply ByAssumption. exact IMP.
    + eapply ByAssumption. exact IN.
  - intros IMP. destruct (classic (p \in MaxCS)) as [YES | NO].
    + eapply MaxCS_closed. eapply ImplicationI. eapply extend_proves with (Gamma := MaxCS).
      * intros r Hr. right. exact Hr.
      * eapply ByAssumption. eapply IMP. exact YES.
    + eapply MaxCS_closed.
      assert (NEG : Neg_frm p \in MaxCS).
      { destruct (MaxCS_complete p) as [|NEG]; [contradiction | exact NEG]. }
      eapply ImplicationI. eapply ContradictionE.
      eapply ContradictionI with (A := p).
      * eapply ByAssumption. left. reflexivity.
      * eapply ByAssumption. right. exact NEG.
Qed.

Lemma MaxCS_FORALL_FAITHFUL (x : ivar) (phi : frm L')
  : All_frm x phi \in MaxCS <-> (forall t : trm L', subst_frm (one_subst x t) phi \in MaxCS).
Proof.
  split.
  - intros UNIV t. eapply MaxCS_closed.
    eapply UniversalE with (A := phi). eapply ByAssumption. exact UNIV.
  - intros UNIV.
    pose proof (hc_decode_isSurjective x phi) as [hc Hdec].
    assert (HEN_IN : HenkinAxiom hc \in Hbase).
    { left. econs. }
    assert (HEN_IN_MCS : HenkinAxiom hc \in MaxCS).
    { eapply MaxCS_incl_Hbase. exact HEN_IN. }
    unfold HenkinAxiom in HEN_IN_MCS. rewrite Hdec in HEN_IN_MCS.
    eapply MaxCS_IMPLICATION_FAITHFUL with (p := subst_frm (one_subst x (@Con_trm L' (inr hc))) phi).
    + exact HEN_IN_MCS.
    + eapply UNIV.
Qed.

Let D : Type@{U_discourse} :=
  trm L'.

Definition interpret_equation (lhs : D) (rhs : D) : Prop :=
  MaxCS ⊢ Eqn_frm lhs rhs.

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
  : pairwise_equal MaxCS (vec_to_trms vs1) (vec_to_trms vs2).
Proof.
  revert vs2 EQ. induction vs1 as [ | n v1 vs1 IH].
  - introVNil; simpl; i. econs.
  - introVCons v2 vs2; simpl; i. econs.
    + eapply EQ with (i := FZ).
    + eapply IH. intros i. eapply EQ with (i := FS i).
Qed.

Lemma pairwise_equal_symmetry n (vs1 : Vector.t (trm L') n) (vs2 : Vector.t (trm L') n)
  (EQUAL : pairwise_equal MaxCS (vec_to_trms vs1) (vec_to_trms vs2))
  : pairwise_equal MaxCS (vec_to_trms vs2) (vec_to_trms vs1).
Proof.
  revert vs2 EQUAL. induction vs1 as [ | n v1 vs1 IH].
  - introVNil; simpl; i. econs.
  - introVCons v2 vs2; simpl; intros [EQ EQUAL]. econs.
    + eapply proves_symmetry; trivial.
    + eapply IH; trivial.
Qed.

#[local, program]
Instance trmModel : isStructureOf L' :=
  { domain_of_discourse := D
  ; equation_interpret := {| eqProp := interpret_equation; eqProp_Equivalence := interpret_equation_Equivalence |}
  ; function_interpret f vs := Fun_trm f (vec_to_trms vs)
  ; constant_interpret c := Con_trm c
  ; relation_interpret R vs := MaxCS ⊢ Rel_frm R (vec_to_trms vs)
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
  - eapply for_Imp_E. eapply proves_eqn_rel. 2: exact INFERS.
    eapply pairwise_equal_symmetry; eapply pairwise_equal_intro; trivial.
Qed.

Definition ivar_interpret : ivar -> domain_of_discourse :=
  Var_trm.

Lemma interpret_trm_trmModel (t : trm L')
  : interpret_trm trmModel ivar_interpret t = t
with interpret_trms_trmModel n (ts : trms L' n)
  : vec_to_trms (interpret_trms trmModel ivar_interpret ts) = ts.
Proof.
  - trm_ind t; simpl.
    + reflexivity.
    + f_equal. eapply interpret_trms_trmModel.
    + reflexivity.
  - trms_ind ts.
    + reflexivity.
    + rewrite interpret_trms_unfold. simpl. f_equal.
      * eapply interpret_trm_trmModel.
      * eapply IH.
Qed.

Theorem trmModel_isModel (p : frm L')
  : p \in MaxCS <-> interpret_frm trmModel ivar_interpret p.
Proof with eauto with *.
  rewrite <- MaxCS_infers_iff. pattern p. revert p. eapply @frm_depth_lt_ind.
  intros [R ts | t1 t2 | p1 | p1 p2 | y p1]; simpl; i.
  - rewrite interpret_trms_trmModel. reflexivity.
  - unfold interpret_equation. do 2 rewrite interpret_trm_trmModel. reflexivity.
  - rewrite <- IH with (p' := p1). 2: lia. split.
    + intros INFERS1 INFERS2. eapply MaxCS_consistent.
      eapply ContradictionI with (A := p1); trivial.
    + intros NO. rewrite MaxCS_infers_iff. eapply MaxCS_META_DN. intros YES.
      rewrite <- MaxCS_infers_iff in YES. contradiction NO.
      eapply NegationE. eapply ContradictionI with (A := Neg_frm p1).
      * eapply ByAssumption; done!.
      * eapply extend_infers with (Gamma := MaxCS); try done!.
  - rewrite <- IH with (p' := p1). 2: lia. rewrite <- IH with (p' := p2). 2: lia. split.
    + intros INFERS1 INFERS2. eapply ImplicationE with (A := p1); trivial.
    + intros INFERS. rewrite MaxCS_infers_iff.
      eapply MaxCS_IMPLICATION_FAITHFUL. intros IN. rewrite <- MaxCS_infers_iff.
      eapply INFERS. rewrite MaxCS_infers_iff. exact IN.
  - unfold D. split.
    + intros INFERS t. rename y into x. set (s := one_subst x t).
      assert (IFF : interpret_frm trmModel ivar_interpret (subst_frm s p1) <-> interpret_frm trmModel (upd_env x t ivar_interpret) p1).
      { rewrite <- substitution_lemma_frm. eapply interpret_frm_ext. ii. unfold compose, upd_env, s, one_subst, cons_subst, nil_subst.
        destruct (eq_dec z x) as [EQ1 | NE1]; trivial. eapply interpret_trm_trmModel.
      }
      rewrite <- IFF. rewrite <- IH with (p' := subst_frm s p1). 2: rewrite subst_preserves_rank; lia.
      unfold s. eapply UniversalE. exact INFERS.
    + intros INTERPRET. rewrite MaxCS_infers_iff. eapply MaxCS_FORALL_FAITHFUL.
      intros t. rewrite <- MaxCS_infers_iff. rewrite -> IH with (p' := subst_frm (one_subst y t) p1). 2: rewrite subst_preserves_rank; lia.
      rewrite <- substitution_lemma_frm. eapply interpret_frm_ext with (env' := upd_env y (interpret_trm trmModel ivar_interpret t) ivar_interpret). ii. unfold compose, upd_env, one_subst, cons_subst, nil_subst.
      destruct (eq_dec z y) as [EQ1 | NE1]; trivial. eapply INTERPRET.
Qed.

End WITH_MCS.

End COMPLETENESS_OF_HilbertCalculus.

Section COMPLETENESS_THEOREM.

Import HELFER1_i.
Import HELFER1_ii.

#[local] Existing Instance V.vec_isSetoid.

Context `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}.

Context {L : language} {function_symbols_hasEqDec : hasEqDec L.(function_symbols)} {constant_symbols_hasEqDec : hasEqDec L.(constant_symbols)} {relation_symbols_hasEqDec : hasEqDec L.(relation_symbols)}.

#[local] Notation L' := (augmented_language L (Henkin_constants L)).

#[local] Existing Instance Henkin_constants_hasEqDec.

#[local] Existing Instance abstract_Henkin_constants_instance.

Theorem HilbertCalculus_complete (X : ensemble (frm L)) (b : frm L)
  (CONSEQUENCE : X ⊨ b)
  : X ⊢ b.
Proof with eauto with *.
  eapply NNPP. intros NO.
  set (Gamma := E.insert (Neg_frm b) X).
  assert (CONSISTENT : Gamma ⊬ Bot_frm).
  { intros INCONSISTENT. contradiction NO. eapply NegationE... }
  pose proof (exists_MCS Gamma CONSISTENT) as [MCS [HBsub [HCons HMax]]].
  assert (claim : Gamma ⊭ Bot_frm).
  { intros SAT. contradiction (SAT (restrict_structure (trmModel MCS)) (ivar_interpret MCS)).
    - red. set (STRUCTURE := trmModel MCS). set (env := ivar_interpret MCS).
      assert (MODEL : forall p : frm L, interpret_frm STRUCTURE env (embed_frm p) <-> interpret_frm (restrict_structure STRUCTURE) env p).
      { intros p. eapply restrict_structure_frm. }
      intros A AIN. red. rewrite <- MODEL. unfold STRUCTURE, env.
      rewrite <- (trmModel_isModel Gamma MCS HBsub HCons HMax); trivial.
      eapply HBsub. right. eapply E.in_image_iff. exists A. split; trivial.
    - simpl. intros t. unfold interpret_equation. eapply proves_reflexivity.
  }
  contradiction claim. intros ? ? ? SAT. unfold Gamma in SATISFY.
  red in SATISFY. pose proof (SATISFY (Neg_frm b)) as CONTRA. simpl in CONTRA. contradiction CONTRA.
  - left. reflexivity.
  - eapply CONSEQUENCE. ii. eapply SATISFY. right. trivial.
Qed.

End COMPLETENESS_THEOREM.

End HELFER2.
