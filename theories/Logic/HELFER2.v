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

Context {L : language} {function_symbols_hasEqDec : hasEqDec L.(function_symbols)} {constant_symbols_hasEqDec : hasEqDec L.(constant_symbols)} {relation_symbols_hasEqDec : hasEqDec L.(relation_symbols)}.

#[local] Notation L' := (augmented_language L (Henkin_constants L)).

#[local] Existing Instance Henkin_constants_hasEqDec.

#[local] Existing Instance abstract_Henkin_constants_instance.

Variable X : ensemble (frm L).

Hypothesis CONSISTENT : X ⊬ Bot_frm.

Let Hbase : ensemble (frm L') :=
  E.union HenkinAxiomSet (E.image embed_frm X).

Lemma Hbase_consistent
  : Hbase ⊬ Bot_frm.
Proof.
  intros H.
  assert (INC : inconsistent Hbase).
  { rewrite inconsistent_iff. exact H. }
  unfold Hbase in INC.
  rewrite <- AddHenkin_embed_equiconsistent in INC.
  rewrite inconsistent_iff in INC.
  erewrite @embed_frm_proves_iff with (Henkin_constants := Henkin_constants L) (p := Bot_frm) in INC.
  eapply CONSISTENT. exact INC.
Qed.

Section WITH_MCS.

Variable MaxCS : ensemble (frm L').

Hypothesis MaxCS_incl_Hbase : Hbase \subseteq MaxCS.

Hypothesis MaxCS_consistent : MaxCS ⊬ Bot_frm.

Hypothesis MaxCS_maximal : forall Delta' : ensemble (frm L'), MaxCS \subseteq Delta' -> Delta' ⊬ Bot_frm -> Delta' \subseteq MaxCS.

Lemma MaxCS_closed (p : frm L')
  (PROVE : MaxCS ⊢ p)
  : p \in MaxCS.
Proof.
  assert (CONS : E.insert p MaxCS ⊬ Bot_frm).
  { intros INC. eapply MaxCS_consistent.
    enough (MaxCS ⊢ Imp_frm p Bot_frm).
    { eapply for_Imp_E; eauto. }
    eapply ImplicationI. exact INC.
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
  pose proof (classic (p \in MaxCS)) as [YES | NO]; [left; trivial | right].
  eapply MaxCS_closed. eapply NegationI.
  assert (INC : E.insert p MaxCS ⊢ Bot_frm \/ E.insert p MaxCS ⊬ Bot_frm) by eapply classic.
  destruct INC as [IN | NOT_IN]; trivial.
  exfalso. eapply NO. eapply MaxCS_maximal with (Delta' := E.insert p MaxCS).
  - intros q Hq. right. exact Hq.
  - exact NOT_IN.
  - left. reflexivity.
Qed.

Lemma MaxCS_neg_iff (p : frm L')
  : p \in MaxCS <-> ~ Neg_frm p \in MaxCS.
Proof.
  split.
  - intros IN NEG. eapply MaxCS_consistent. eapply ContradictionI with (A := p).
    + eapply ByAssumption. exact IN.
    + eapply ByAssumption. exact NEG.
  - intros NNEG. pose proof (MaxCS_complete p) as [YES | NO]; trivial. contradiction.
Qed.

Lemma MaxCS_META_DN (p : frm L')
  (NEGATION : Neg_frm p \in MaxCS -> Bot_frm \in MaxCS)
  : p \in MaxCS.
Proof.
  pose proof (MaxCS_complete p) as [YES | NO]; trivial.
  exfalso. eapply MaxCS_consistent.
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
  - intros IMP. pose proof (classic (p \in MaxCS)) as [YES | NO].
    + eapply MaxCS_closed. eapply ImplicationI. eapply extend_proves with (Gamma := MaxCS).
      * intros r Hr. right. exact Hr.
      * eapply ByAssumption. eapply IMP. exact YES.
    + eapply MaxCS_closed.
      assert (NEG : Neg_frm p \in MaxCS).
      { pose proof (MaxCS_complete p) as [YES | NO']; [contradiction | exact NO']. }
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
  { X : ensemble@{U_discourse} (trm L') | exists lhs, forall rhs, rhs \in X <-> MaxCS ⊢ Eqn_frm lhs rhs }.

Let vecD (n : nat) : Type@{U_discourse} :=
  { X : ensemble@{U_discourse} (trms L' n) | exists lhs, forall rhs, rhs \in X <-> pairwise_equal MaxCS lhs rhs }.

#[refine]
Fixpoint to_vecD (n : nat) (ds : Vector.t D n) {struct ds} : vecD n :=
  match ds in Vector.t _ n return vecD n with
  | Vector.VNil => @exist _ _ (pure (isMonad := E.t_isMonad) (@O_trms L')) _
  | Vector.VCons n v vs => @exist _ _ (liftM2 (MONAD := E.t_isMonad) (@S_trms L' n) (proj1_sig v) (proj1_sig (to_vecD n vs))) _
  end.
Proof.
  - clear n ds. exists (@O_trms L').
    intros rhs; pattern rhs; revert rhs; eapply trms_case0.
    simpl; split; econs.
  - clear n0 ds. destruct v as [v1 [lhs1 H_lhs1]]; simpl. destruct (to_vecD n vs) as [vs2 [lhs2 H_lhs2]]; simpl. exists (@S_trms L' n lhs1 lhs2).
    intros rhs; pattern rhs; revert rhs; eapply trms_caseS. unfold "\in".
    intros t' ts'. split; [intros (t & Ht & ts & Hts & EQ) | intros [PROVE1 PROVE2]].
    + inv EQ. apply projT2_eq in H1. subst ts'. split; simpl.
      * rewrite <- H_lhs1. eauto.
      * rewrite <- H_lhs2. eauto.
    + simpl in *. exists t'. split. { change (t' \in v1). rewrite -> H_lhs1. eauto. }
      exists ts'. split. { change (ts' \in vs2). rewrite -> H_lhs2. eauto. }
      reflexivity.
Defined.

Lemma ivar_interpret_aux (x : ivar)
  : exists lhs : trm L', forall rhs : trm L', MaxCS ⊢ Eqn_frm (Var_trm x) rhs <-> MaxCS ⊢ Eqn_frm lhs rhs.
Proof.
  exists (@Var_trm L' x). intros rhs; reflexivity.
Qed.

Lemma constant_interpret_aux (c' : L'.(constant_symbols))
  : exists lhs : trm L', forall rhs : trm L', MaxCS ⊢ Eqn_frm (Con_trm c') rhs <-> MaxCS ⊢ Eqn_frm lhs rhs.
Proof.
  exists (@Con_trm L' c'). intros rhs; reflexivity.
Qed.

Lemma function_interpret_aux (f' : L'.(function_symbols)) (vs : Vector.t D (function_arity_table L' f'))
  : exists lhs : trm L', forall rhs : trm L', (exists ts : trms L' (function_arity_table L f'), (proj1_sig (to_vecD (function_arity_table L f') vs)) ts /\ MaxCS ⊢ Eqn_frm (Fun_trm f' ts) rhs) <-> MaxCS ⊢ Eqn_frm lhs rhs.
Proof.
  destruct (to_vecD (function_arity_table L f') vs) as [vs' [lhs H_lhs]]; simpl.
  exists (@Fun_trm L' f' lhs). intros rhs. split; [intros (ts' & Hvs' & Hrhs) | intros Hrhs].
  - eapply proves_transitivity with (t2 := @Fun_trm L' f' ts'); trivial.
    eapply proves_eqn_fun. rewrite <- H_lhs. exact Hvs'.
  - exists lhs. split; trivial. change (lhs \in vs'). rewrite -> H_lhs. eapply pairwise_equal_reflexive.
Qed.

Definition ivar_interpret (x : ivar) : D :=
  @exist _ _ (fun t => MaxCS ⊢ Eqn_frm (Var_trm x) t) (ivar_interpret_aux x).

Definition constant_interpret (c' : L'.(constant_symbols)) : D :=
  @exist _ _ (fun t => MaxCS ⊢ Eqn_frm (Con_trm c') t) (constant_interpret_aux c').

Definition function_interpret (f' : L'.(function_symbols)) (vs : Vector.t D (L.(function_arity_table) f')) : D :=
  @exist _ _ (fun t => exists ts, ts \in proj1_sig (to_vecD _ vs) /\ MaxCS ⊢ Eqn_frm (Fun_trm f' ts) t) (function_interpret_aux f' vs).

Definition relation_interpret (R' : L'.(relation_symbols)) (vs : Vector.t D (L.(relation_arity_table) R')) : Prop :=
  exists ts, ts \in proj1_sig (to_vecD _ vs) /\ MaxCS ⊢ Rel_frm R' ts.

Definition interpret_equation : forall lhs : D, forall rhs : D, Prop :=
  @eq D.

#[local, program]
Instance trmModel : isStructureOf L' :=
  { domain_of_discourse := D
  ; equation_interpret := {| eqProp := interpret_equation; eqProp_Equivalence := eq_equivalence; |}
  ; function_interpret := function_interpret
  ; constant_interpret := constant_interpret
  ; relation_interpret := relation_interpret
  }.
Next Obligation.
  econs. exact (ivar_interpret O).
Qed.
Next Obligation.
  red in EQ |- *. f_equal.
  now rewrite V.vec_ext_eq.
Qed.
Next Obligation.
  unfold interpret_equation in EQ.
  rewrite <- V.vec_ext_eq in EQ. subst vs2.
  reflexivity.
Qed.

Lemma interpret_trm_trmModel (t : trm L')
  : t \in proj1_sig (interpret_trm trmModel ivar_interpret t)
with interpret_trms_trmModel (n : nat) (ts : trms L' n)
  : ts \in proj1_sig (to_vecD n (interpret_trms trmModel ivar_interpret ts)).
Proof.
  - destruct t as [x | f ts | c]; simpl; unfold "\in".
    + eapply proves_reflexivity.
    + exists ts. split; [eapply interpret_trms_trmModel | eapply proves_reflexivity].
    + eapply proves_reflexivity.
  - destruct ts as [ | n t ts]; simpl; unfold "\in".
    + reflexivity.
    + exists t. split. { eapply interpret_trm_trmModel. }
      exists ts. split. { eapply interpret_trms_trmModel. }
      reflexivity.
Qed.

Context `{Axms : ClassicalAxioms (b_fun_ext := true) (b_prop_ext := true)}.

Lemma interpret_equation_intro (lhs : D) (rhs : D)
  (EQ : forall t : trm L', t \in proj1_sig lhs <-> t \in proj1_sig rhs)
  : interpret_equation lhs rhs.
Proof.
  destruct lhs as [lhs H_lhs], rhs as [rhs H_rhs]; simpl in *.
  red. eapply exist_eq_iff.
  refine (@Functional_Extensionality _ _ _ Axms (trm L') (fun _ => Prop) lhs rhs _).
  intros t.
  refine (@Propositional_Extensionality _ _ _ Axms (lhs t) (rhs t) _).
  exact (EQ t).
Qed.

Theorem trmModel_isModel (p : frm L')
  : p \in MaxCS <-> interpret_frm trmModel ivar_interpret p.
Proof.
  rewrite <- MaxCS_infers_iff. pattern p. revert p. eapply @frm_depth_lt_ind.
  intros [R ts | t1 t2 | p1 | p1 p2 | y p1]; simpl; i.
  - unfold relation_interpret. pose proof (interpret_trms_trmModel _ ts) as HH.
    simpl in HH. destruct (to_vecD _ _) as [vs [ts' Hts']]; simpl in *. split.
    + intros INFERS. exists ts; split; eauto.
    + intros (vs' & Hvs' & INFERS). rewrite Hts' in HH, Hvs'. eapply for_Imp_E with (p := @Rel_frm L' R vs'); eauto.
      eapply @proves_eqn_rel. eapply pairwise_equal_transitive; [eapply pairwise_equal_symmetric | eapply HH]; eauto.
  - unfold interpret_equation. split; [intros INFERS | intros EQ].
    + eapply interpret_equation_intro. intros t; split.
      * pose proof (interpret_trm_trmModel t1) as HH1. pose proof (interpret_trm_trmModel t2) as HH2.
        destruct (interpret_trm _ _ _) as [t1' [v1 Ht1']]; simpl in *; destruct (interpret_trm _ _ _) as [t2' [v2 Ht2']]; simpl in *. intros H_in. 
        rewrite Ht1' in HH1, H_in. rewrite Ht2' in HH2 |- *.
        eapply proves_transitivity with (t2 := t2); eauto.
        eapply proves_symmetry.
        eapply proves_transitivity with (t2 := t1); eauto.
        eapply proves_transitivity with (t2 := v1); eauto.
        eapply proves_symmetry; eauto.
      * pose proof (interpret_trm_trmModel t1) as HH1. pose proof (interpret_trm_trmModel t2) as HH2.
        destruct (interpret_trm _ _ _) as [t1' [v1 Ht1']]; simpl in *; destruct (interpret_trm _ _ _) as [t2' [v2 Ht2']]; simpl in *. intros H_in. 
        rewrite Ht2' in HH2, H_in. rewrite -> Ht1' in HH1 |- *.
        eapply proves_transitivity with (t2 := t1); eauto.
        eapply proves_transitivity with (t2 := t2); eauto.
        eapply proves_transitivity with (t2 := v2); eauto.
        eapply proves_symmetry; eauto.
    + pose proof (interpret_trm_trmModel t1) as HH1. pose proof (interpret_trm_trmModel t2) as HH2.
      destruct (interpret_trm _ _ _) as [t1' [v1 Ht1']]; simpl in *; destruct (interpret_trm _ _ _) as [t2' [v2 Ht2']]; simpl in *. 
      apply exist_eq_iff in EQ. subst t2'. rewrite Ht1' in HH1, HH2.
      eapply proves_transitivity with (t2 := v1); eauto.
      eapply proves_symmetry; eauto.
  - rewrite <- IH with (p' := p1) by lia. split.
    + intros INFERS1 INFERS2. eapply MaxCS_consistent.
      eapply ContradictionI with (A := p1); trivial.
    + intros NO. rewrite MaxCS_infers_iff. eapply MaxCS_META_DN. intros YES.
      rewrite <- MaxCS_infers_iff in YES. contradiction NO.
      eapply NegationE. eapply ContradictionI with (A := Neg_frm p1).
      * eapply ByAssumption; done!.
      * eapply extend_infers with (Gamma := MaxCS); try done!.
  - rewrite <- IH with (p' := p1) by lia. rewrite <- IH with (p' := p2) by lia. split.
    + intros INFERS1 INFERS2. eapply ImplicationE with (A := p1); trivial.
    + intros INFERS. rewrite MaxCS_infers_iff.
      eapply MaxCS_IMPLICATION_FAITHFUL. intros IN. rewrite <- MaxCS_infers_iff.
      eapply INFERS. rewrite MaxCS_infers_iff. exact IN.
  - unfold D. split.
    + intros INFERS [P [t Ht]]. rename y into x. set (s := one_subst x t). set (d := @exist _ _ _ _).
      assert (claim : interpret_frm trmModel ivar_interpret (subst_frm s p1) <-> interpret_frm trmModel (upd_env x d ivar_interpret) p1).
      { rewrite <- substitution_lemma_frm. eapply interpret_frm_ext. ii. unfold compose, upd_env, s, one_subst, cons_subst, nil_subst.
        destruct (eq_dec z x) as [EQ1 | NE1]; trivial. subst z. eapply interpret_equation_intro. simpl. intros t'.
        rewrite -> Ht. pose proof (interpret_trm_trmModel t) as HH. split.
        - destruct (interpret_trm trmModel ivar_interpret t) as [P'' [t'' IFF]]; simpl in *; intros Ht''.
          rewrite -> IFF in HH, Ht''. eapply proves_symmetry. eapply proves_transitivity with (t2 := t''); eauto. eapply proves_symmetry; eauto.
        - destruct (interpret_trm trmModel ivar_interpret t) as [P'' [t'' IFF]]; simpl in *; intros Ht''.
          rewrite -> IFF in HH |- *. simpl. eapply proves_transitivity with (t2 := t); eauto.
      }
      rewrite <- claim. rewrite <- IH with (p' := subst_frm s p1) by now rewrite subst_preserves_rank; lia.
      unfold s. eapply UniversalE. exact INFERS.
    + intros INTERPRET. rewrite MaxCS_infers_iff. eapply MaxCS_FORALL_FAITHFUL.
      intros t. rewrite <- MaxCS_infers_iff. rewrite -> IH with (p' := subst_frm (one_subst y t) p1) by now rewrite subst_preserves_rank; lia.
      rewrite <- substitution_lemma_frm. eapply interpret_frm_ext with (env' := upd_env y (interpret_trm trmModel ivar_interpret t) ivar_interpret); eauto.
      ii. unfold compose, upd_env, one_subst, cons_subst, nil_subst. destruct (eq_dec z y) as [EQ1 | NE1]; trivial.
Qed.

End WITH_MCS.

Let ConsistentExtension : Type@{U_discourse} :=
  { Delta : ensemble@{U_discourse} (frm L') | Hbase \subseteq Delta /\ Delta ⊬ Bot_frm }.

#[local]
Instance ConsistentExtension_isProset : isProset ConsistentExtension :=
  @subProset (ensemble (frm L')) E.ensemble_isProset (fun Delta => Hbase \subseteq Delta /\ Delta ⊬ Bot_frm).

Let ConsistentExtension_base : ConsistentExtension :=
  @exist _ _ Hbase (conj (reflexivity Hbase) Hbase_consistent).

Lemma chain_upperbound (C : ensemble ConsistentExtension)
  (NONEMPTY : exists d : ConsistentExtension, d \in C)
  (CHAIN : forall x1, forall x2, x1 \in C -> x2 \in C -> (x1 =< x2 \/ x2 =< x1))
  : exists u : ConsistentExtension, forall d, d \in C -> d =< u.
Proof.
  pose (U := fun p : frm L' => exists d : ConsistentExtension, d \in C /\ p \in proj1_sig d).
  assert (HSUB : Hbase \subseteq U).
  { intros p Hp. destruct NONEMPTY as [d0 Hd0]. exists d0. split; trivial.
    destruct d0 as [Delta0 [HB0 HC0]]. simpl. eapply HB0. exact Hp.
  }
  enough (HCONS : U ⊬ Bot_frm).
  { exists (@exist _ _ U (conj HSUB HCONS)).
    intros d Hd. destruct d as [Delta [HBd HCd]]. simpl.
    intros p Hp. exists (@exist _ _ Delta (conj HBd HCd)). split; simpl; trivial.
  }
  intros PROV. destruct PROV as [ps [INCL [PF]]].
  assert (EACH : forall p : frm L', In p ps -> (exists d : ConsistentExtension, d \in C /\ p \in proj1_sig d)).
  { intros p Hp. eapply INCL. eapply E.in_fromList_iff. exact Hp. }
  enough (exists d : ConsistentExtension, d \in C /\ (forall p : frm L', In p ps -> p \in proj1_sig d)) as [d [Hd Hps_in]].
  { destruct d as [Delta [HBd HCd]]. simpl in Hps_in. eapply HCd. exists ps. split.
    - intros p Hp. eapply E.in_fromList_iff in Hp. eapply Hps_in. exact Hp.
    - econs. exact PF.
  }
  clear INCL PF. induction ps as [ | q ps IH]; simpl in *.
  - destruct NONEMPTY as [d0 Hd0]. exists d0. split; trivial. intros p [].
  - assert (IHok : forall p : frm L', In p ps -> exists d : ConsistentExtension, d \in C /\ p \in proj1_sig d).
    { intros p Hp. eapply EACH. right. exact Hp. }
    pose proof (IH IHok) as [d_tail [Hd_tail Htail]].
    pose proof (EACH q (or_introl eq_refl)) as [d_q [Hd_q Hq_in]].
    pose proof (CHAIN d_q d_tail Hd_q Hd_tail) as [LE | LE].
    + exists d_tail. split; trivial. intros p [-> | Hp].
      * eapply LE. exact Hq_in.
      * eapply Htail. exact Hp.
    + exists d_q. split; trivial. intros p [-> | Hp].
      * exact Hq_in.
      * eapply LE. eapply Htail. exact Hp.
Qed.

Context `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}.

Lemma exists_MCS
  : exists Delta : ensemble (frm L'), Hbase \subseteq Delta /\ Delta ⊬ Bot_frm /\ (forall Delta' : ensemble (frm L'), Delta \subseteq Delta' -> Delta' ⊬ Bot_frm -> Delta' \subseteq Delta).
Proof.
  exploit (Zorn's_lemma ConsistentExtension ConsistentExtension_isProset); unnw.
  { econs. exact ConsistentExtension_base. }
  { intros C NONEMPTY CHAIN. eapply chain_upperbound; eauto. }
  intros [d_m MAX]. destruct d_m as (Delta & HBd & HCd). exists Delta. splits; eauto.
  intros Delta' SUB CONS'. exact (MAX (@exist _ _ Delta' (conj (transitivity HBd SUB) CONS')) SUB).
Qed.

End COMPLETENESS_OF_HilbertCalculus.

Definition entails' {L : language} (Gamma : ensemble (frm L)) (C : frm L) : Prop :=
  forall STRUCTURE : isStructureOf L, (forall x : domain_of_discourse, forall x' : domain_of_discourse, equation_interpret.(eqProp) x x' -> x = x') -> forall env : ivar -> domain_of_discourse, forall SATISFY : satisfies_frms STRUCTURE env Gamma, satisfies_frm STRUCTURE env C.

Infix "⊨" := entails' : type_scope.

Notation "Gamma ⊭ C" := (~ entails' Gamma C) : type_scope.

Section COMPLETENESS_THEOREM.

Import HELFER1_i.
Import HELFER1_ii.

#[local] Existing Instance V.vec_isSetoid.

Context `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)} {L : language} {function_symbols_hasEqDec : hasEqDec L.(function_symbols)} {constant_symbols_hasEqDec : hasEqDec L.(constant_symbols)} {relation_symbols_hasEqDec : hasEqDec L.(relation_symbols)}.

#[local] Notation L' := (augmented_language L (Henkin_constants L)).

#[local] Existing Instance Henkin_constants_hasEqDec.

#[local] Existing Instance abstract_Henkin_constants_instance.

#[local] Hint Unfold E.In E.insert : core.

Theorem HilbertCalculus_complete (X : ensemble (frm L)) (b : frm L)
  (CONSEQUENCE : X ⊨ b)
  : X ⊢ b.
Proof with eauto.
  eapply NNPP. intros NO. set (Gamma := E.insert (Neg_frm b) X).
  assert (CONSISTENT : Gamma ⊬ Bot_frm).
  { intros INCONSISTENT. contradiction NO. eapply NegationE... }
  pose proof (exists_MCS Gamma CONSISTENT) as (MCS & HBsub & HCons & HMax).
  set (STRUCTURE := trmModel MCS). set (env := ivar_interpret MCS).
  assert (MODEL : forall p : frm L, interpret_frm STRUCTURE env (embed_frm p) <-> interpret_frm (restrict_structure STRUCTURE) env p).
  { ii. eapply restrict_structure_frm. }
  assert (claim : Gamma ⊭ Bot_frm).
  { intros SAT. eapply SAT with (STRUCTURE := restrict_structure (trmModel MCS)) (env := ivar_interpret MCS).
    - ii...
    - red. fold env. fold STRUCTURE. intros A AIN. red. rewrite <- MODEL with (p := A).
      unfold STRUCTURE, env. rewrite <- trmModel_isModel with (X := Gamma) (MaxCS := MCS)...
      eapply HBsub. right. rewrite E.in_image_iff. exists A...
    - simpl. intros t. unfold interpret_equation. reflexivity.
  }
  contradiction claim. subst STRUCTURE env. intros ? H_eqProp_iff_eq ? ? SAT. unfold Gamma in SATISFY.
  red in SATISFY. pose proof (SATISFY (Neg_frm b)) as CONTRA. simpl in CONTRA.
  contradiction CONTRA... eapply CONSEQUENCE... ii. eapply SATISFY...
Qed.

End COMPLETENESS_THEOREM.

End HELFER2.
