Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.Data.Vector.
Require Import PnV.Logic.BasicFol.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.

Reserved Infix "\proves" (at level 70, no associativity).

Import ListNotations.
Import FolNotations.

Section HILBERT_PROOF_SYSTEM.

#[local]
Tactic Notation "done" :=
  first [congruence | lia | done!].

Import ListNotations.

Context {L : language}.

Definition varcouples : forall n : nat, trms L n * trms L n :=
  nat_rec (fun n => (trms L n * trms L n)%type) (O_trms, O_trms) (fun n => prod_rec _ (fun lhs => fun rhs => (S_trms n (Var_trm (n + n)) lhs, S_trms n (Var_trm (S (n + n))) rhs))).

Definition eqns_imp p : nat -> frm L :=
  nat_rec (fun _ => frm L) p (fun n => fun q => Imp_frm (Eqn_frm (Var_trm (n + n)) (Var_trm (S (n + n)))) q).

Definition Fun_eqAxm (f : L.(function_symbols)) : frm L :=
  eqns_imp (prod_rec (fun _ => frm L) (fun lhs => fun rhs => Eqn_frm (Fun_trm f lhs) (Fun_trm f rhs)) (varcouples (L.(function_arity_table) f))) (L.(function_arity_table) f).

Definition Rel_eqAxm (R : L.(relation_symbols)) : frm L :=
  eqns_imp (prod_rec (fun _ => frm L) (fun lhs => fun rhs => Imp_frm (Rel_frm R lhs) (Rel_frm R rhs)) (varcouples (L.(relation_arity_table) R))) (L.(relation_arity_table) R).

Inductive proof : list (frm L) -> frm L -> Set := (* Reference: "https://github.com/princeton-vl/CoqGym/blob/master/coq_projects/goedel/folProof.v#L68" *)
  | AXM p
    : proof [p] p
  | MP ps1 ps2 p q
    (PF1 : proof ps1 (Imp_frm p q))
    (PF2 : proof ps2 p)
    : proof (ps1 ++ ps2) q
  | GEN ps q x
    (NOT_FREE : forall p, In p ps -> is_not_free_in_frm x p)
    (PF : proof ps q)
    : proof ps (All_frm x q)
  | IMP1 p q
    : proof [] (Imp_frm p (Imp_frm q p))
  | IMP2 p q r
    : proof [] (Imp_frm (Imp_frm p (Imp_frm q r)) (Imp_frm (Imp_frm p q) (Imp_frm p r)))
  | CP p q
    : proof [] (Imp_frm (Imp_frm (Neg_frm q) (Neg_frm p)) (Imp_frm p q))
  | FA1 p x t
    : proof [] (Imp_frm (All_frm x p) (subst_frm (one_subst x t) p))
  | FA2 p x
    (NOT_FREE : is_not_free_in_frm x p)
    : proof [] (Imp_frm p (All_frm x p))
  | FA3 p q x
    : proof [] (Imp_frm (All_frm x (Imp_frm p q)) (Imp_frm (All_frm x p) (All_frm x q)))
  | EQN_REFL
    : proof [] (Eqn_frm (Var_trm 0) (Var_trm 0))
  | EQN_SYM
    : proof [] (Imp_frm (Eqn_frm (Var_trm 0) (Var_trm 1)) (Eqn_frm (Var_trm 1) (Var_trm 0)))
  | EQN_TRANS
    : proof [] (Imp_frm (Eqn_frm (Var_trm 0) (Var_trm 1)) (Imp_frm (Eqn_frm (Var_trm 1) (Var_trm 2)) (Eqn_frm (Var_trm 0) (Var_trm 2))))
  | EQN_FUN f
    : proof [] (Fun_eqAxm f)
  | EQN_REL R
    : proof [] (Rel_eqAxm R).

Definition proves (Gamma : ensemble (frm L)) (C : frm L) : Prop :=
  exists ps, E.fromList ps \subseteq Gamma /\ inhabited (proof ps C).

#[local] Infix "\proves" := proves : type_scope.

Lemma proof_compose p q r
  : proof [] (Imp_frm (Imp_frm q r) (Imp_frm (Imp_frm p q) (Imp_frm p r))).
Proof.
  assert (PF1 : proof [] (Imp_frm (Imp_frm q r) (Imp_frm p (Imp_frm q r)))) by eapply IMP1.
  assert (PF2 : proof [] (Imp_frm (Imp_frm p (Imp_frm q r)) (Imp_frm (Imp_frm p q) (Imp_frm p r)))) by eapply IMP2.
  set (p2 := (Imp_frm (Imp_frm p (Imp_frm q r)) (Imp_frm (Imp_frm p q) (Imp_frm p r)))) in *.
  assert (PF3 : proof [] (Imp_frm p2 (Imp_frm (Imp_frm q r) p2))) by eapply IMP1.
  assert (PF4 : proof ([] ++ []) (Imp_frm (Imp_frm q r) p2)) by now eapply MP; [exact PF3 | exact PF2].
  simpl in PF4. set (p4 := Imp_frm (Imp_frm q r) p2) in *. set (p1 := Imp_frm (Imp_frm q r) (Imp_frm p (Imp_frm q r))) in *.
  assert (PF5 : proof [] (Imp_frm p4 (Imp_frm p1 (Imp_frm (Imp_frm q r) (Imp_frm (Imp_frm p q) (Imp_frm p r)))))) by eapply IMP2.
  assert (PF6 : proof ([] ++ []) (Imp_frm p1 (Imp_frm (Imp_frm q r) (Imp_frm (Imp_frm p q) (Imp_frm p r))))) by now eapply MP; [eapply PF5 | eapply PF4].
  eapply MP with (ps1 := [] ++ []) (ps2 := []); [exact PF6 | exact PF1].
Qed.

Lemma proof_id p
  : proof [] (Imp_frm p p).
Proof.
  pose proof (PF1 := @IMP1 p p).
  pose proof (PF2 := @IMP1 p (Imp_frm p p)).
  pose proof (PF3 := @IMP2 p (Imp_frm p p) p).
  pose proof (PF4 := @MP _ _ _ _ PF3 PF2).
  pose proof (PF5 := @MP _ _ _ _ PF4 PF1).
  exact PF5.
Qed.

Lemma syllogism p q r
  : proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Imp_frm q r) (Imp_frm p r))).
Proof.
  pose proof (proof_compose p q r) as PF7. set (p7 := (Imp_frm (Imp_frm q r) (Imp_frm (Imp_frm p q) (Imp_frm p r)))) in *.
  pose proof (PF8 := IMP2 (Imp_frm q r) (Imp_frm p q) (Imp_frm p r)). fold p7 in PF8.
  pose proof (PF9 := MP _ _ _ _ PF8 PF7). simpl in PF9. set (p9 := Imp_frm (Imp_frm (Imp_frm q r) (Imp_frm p q)) (Imp_frm (Imp_frm q r) (Imp_frm p r))) in *.
  pose proof (PF10 := IMP1 (Imp_frm p q) (Imp_frm q r)).
  pose proof (PF11 := IMP1 p9 (Imp_frm p q)).
  pose proof (PF12 := MP _ _ _ _ PF11 PF9). simpl in PF12.
  rewrite <- app_nil_l with (l := @nil (frm L)). eapply MP. 2: exact PF10.
  rewrite <- app_nil_l with (l := @nil (frm L)). eapply MP. 2: exact PF12.
  eapply IMP2.
Qed.

Lemma proof_flip p q r
  : proof [] (Imp_frm (Imp_frm q (Imp_frm p r)) (Imp_frm p (Imp_frm q r))).
Proof.
  pose proof (@syllogism) as PF1. specialize PF1 with (p := p) (q := Imp_frm q p) (r := Imp_frm q r).
  assert (PF2: proof [] (Imp_frm p (Imp_frm q p))) by eapply IMP1.
  pose proof (PF3 := MP _ _ _ _ PF1 PF2). simpl in PF3.
  1: rewrite <- app_nil_l with (l := @nil (frm L)); eapply MP.
  1: rewrite <- app_nil_l with (l := @nil (frm L)); eapply MP.
  1: eapply syllogism.
  2: eapply PF3.
  eapply IMP2.
Qed.

Lemma proof_rebind_All_frm (x : ivar) (z : ivar) (p : frm L)
  (FRESH : is_not_free_in_frm z (All_frm x p))
  : proof [] (Imp_frm (All_frm x p) (All_frm z (subst_frm (one_subst x (Var_trm z)) p))).
Proof.
  pose proof (@syllogism (All_frm x p) (All_frm z (All_frm x p)) (All_frm z (subst_frm (one_subst x (Var_trm z)) p))) as PF1.
  pose proof (@FA2 (All_frm x p) z FRESH) as PF2.
  pose proof (@MP _ _ _ _ PF1 PF2) as PF3. rewrite app_nil_r in PF3.
  rewrite <- app_nil_l with (l := @nil (frm L)). eapply MP. 1: exact PF3.
  pose proof (@FA3 (All_frm x p) (subst_frm (one_subst x (Var_trm z)) p) z) as PF4.
  rewrite <- app_nil_l with (l := @nil (frm L)). eapply MP. 1: exact PF4.
  eapply GEN. 1: intros ? []. eapply FA1.
Qed.

Lemma proof_ex_falso (p : frm L) (q : frm L)
  : proof [] (Imp_frm (Neg_frm p) (Imp_frm p q)).
Proof.
  pose proof (CP p q) as PF1.
  rewrite <- app_nil_l with (l := []). eapply MP with (p := Imp_frm (Neg_frm p) (Imp_frm (Neg_frm q) (Neg_frm p))). 2: exact (IMP1 (Neg_frm p) (Neg_frm q)).
  rewrite <- app_nil_l with (l := []). eapply MP. 1: eapply IMP2. rewrite <- app_nil_l with (l := []).
  eapply MP; [eapply IMP1 | exact PF1].
Qed.

Lemma proof_square (p1 : frm L) (p2 : frm L) (p3 : frm L) (p4 : frm L)
  (PROOF1 : proof [] (Imp_frm p1 p2))
  (PROOF2 : proof [] (Imp_frm p2 p3))
  (PROOF3 : proof [] (Imp_frm p3 p4))
  : proof [] (Imp_frm p1 p4).
Proof.
  1: rewrite <- app_nil_l with (l := []); eapply MP.
  1: rewrite <- app_nil_l with (l := []); eapply MP.
  1: eapply proof_compose with (q := p3).
  { exact PROOF3. }
  1: rewrite <- app_nil_l with (l := []); eapply MP.
  1: rewrite <- app_nil_l with (l := []); eapply MP.
  1: eapply proof_compose with (q := p2).
  { exact PROOF2. }
  { exact PROOF1. }
Qed.

Lemma proof_dni (p : frm L)
  : proof [] (Imp_frm p (Neg_frm (Neg_frm p))).
Proof.
  1: rewrite <- app_nil_l with (l := []); eapply MP. eapply CP.
  1: rewrite <- app_nil_l with (l := []); eapply MP.
  1: rewrite <- app_nil_l with (l := []); eapply MP.
  eapply IMP2 with (q := Imp_frm (Neg_frm (Neg_frm p)) (Neg_frm (Neg_frm (Neg_frm (Neg_frm p))))).
  - 1: rewrite <- app_nil_l with (l := []); eapply MP. eapply proof_flip. eapply CP.
  - eapply proof_ex_falso.
Qed.

Lemma proof_dne (p : frm L)
  : proof [] (Imp_frm (Neg_frm (Neg_frm p)) p).
Proof.
  1: rewrite <- app_nil_l with (l := []); eapply MP. eapply CP. eapply proof_dni.
Qed.

Lemma proof_cp1 (p : frm L) (q : frm L)
  : proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Neg_frm q) (Neg_frm p))).
Proof.
  assert (PF1: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Neg_frm (Neg_frm p)) (Imp_frm p q)))).
  { eapply IMP1. }
  assert (PF4: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Neg_frm (Neg_frm p)) p))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. eapply IMP1. eapply proof_dne. }
  assert (PF7: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Imp_frm (Neg_frm (Neg_frm p)) (Imp_frm p q)) (Imp_frm (Imp_frm (Neg_frm (Neg_frm p)) p ) (Imp_frm (Neg_frm (Neg_frm p)) q))))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. eapply IMP1. eapply IMP2. }
  assert (PF10: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Imp_frm (Neg_frm (Neg_frm p)) p) (Imp_frm (Neg_frm (Neg_frm p)) q)))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. 2: exact PF1. 1: rewrite <- app_nil_l with (l := []); eapply MP. 2: eapply PF7. eapply IMP2. }
  assert (PF13: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Neg_frm (Neg_frm p)) q))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. 2: exact PF4. 1: rewrite <- app_nil_l with (l := []); eapply MP. 2: exact PF10. eapply IMP2. }
  assert (PF16: proof [] (Imp_frm (Imp_frm p q) (Imp_frm q (Neg_frm (Neg_frm q))))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. 1: eapply IMP1. eapply proof_dni. }
  assert (PF19: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Imp_frm q (Neg_frm (Neg_frm q))) (Imp_frm (Neg_frm (Neg_frm p)) (Imp_frm q (Neg_frm (Neg_frm q))))))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. eapply IMP1. eapply IMP1. }
  assert (PF22: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Neg_frm (Neg_frm p)) (Imp_frm q (Neg_frm (Neg_frm q)))))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. 2: exact PF16. 1: rewrite <- app_nil_l with (l := []); eapply MP. eapply IMP2. exact PF19. }
  assert (PF25: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Imp_frm (Neg_frm (Neg_frm p)) (Imp_frm q (Neg_frm (Neg_frm q)))) (Imp_frm (Imp_frm (Neg_frm (Neg_frm p)) q) (Imp_frm (Neg_frm (Neg_frm p)) (Neg_frm (Neg_frm q))))))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. 1: eapply IMP1. eapply IMP2. }
  pose proof (PF26 := IMP2 (Imp_frm p q) (Imp_frm (Neg_frm (Neg_frm p)) (Imp_frm q (Neg_frm (Neg_frm q)))) (Imp_frm (Imp_frm (Neg_frm (Neg_frm p)) q) (Imp_frm (Neg_frm (Neg_frm p)) (Neg_frm (Neg_frm q))))).
  pose proof (PF27 := MP _ _ _ _ PF26 PF25). simpl in PF27.
  pose proof (PF28 := MP _ _ _ _ PF27 PF22). simpl in PF28.
  pose proof (PF29 := IMP2 (Imp_frm p q) (Imp_frm (Neg_frm (Neg_frm p)) q) (Imp_frm (Neg_frm (Neg_frm p)) (Neg_frm (Neg_frm q)))).
  pose proof (PF30 := MP _ _ _ _ PF29 PF28). simpl in PF30.
  pose proof (PF31 := MP _ _ _ _ PF30 PF13). simpl in PF31.
  assert (PF34: proof [] (Imp_frm (Imp_frm p q) (Imp_frm (Imp_frm (Neg_frm (Neg_frm p)) (Neg_frm (Neg_frm q))) (Imp_frm (Neg_frm q) (Neg_frm p))))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. eapply IMP1. eapply CP. }
  assert (PF36: proof [] (Imp_frm (Imp_frm (Imp_frm p q) (Imp_frm (Neg_frm (Neg_frm p)) (Neg_frm (Neg_frm q)))) (Imp_frm (Imp_frm p q) (Imp_frm (Neg_frm q) (Neg_frm p))))).
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. eapply IMP2. exact PF34. }
  { 1: rewrite <- app_nil_l with (l := []); eapply MP. exact PF36. exact PF31. }
Qed.

Section DEDUCTION_THEOREM.

Theorem Deduction_theorem (Gamma : ensemble (frm L)) (H : frm L) (C : frm L)
  : Gamma \proves (Imp_frm H C) <-> E.insert H Gamma \proves C.
Proof.
  revert Gamma H C.
  assert (EASY_CASE : forall Gamma, forall A, forall B,
    forall PF : proof [] B,
    E.intersection (E.fromList []) Gamma \proves Imp_frm A B
  ).
  { i. exists []. split. done. econstructor.
    change (proof ([] ++ []) (Imp_frm A B)). eapply MP with (p := B).
    eapply IMP1. exact PF.
  }
  assert (BWD : forall Gamma, forall H, forall C,
    forall PF: E.insert H Gamma \proves C,
    Gamma \proves Imp_frm H C
  ).
  { intros Gamma A B (ps&INCL&(PF)).
    assert (claim1 : E.intersection (E.fromList ps) Gamma \proves Imp_frm A B).
    { induction PF.
      - assert (H_IN : p \in E.insert A Gamma).
        { eapply INCL. ss!. }
        destruct H_IN as [<- | H_IN].
        + clear INCL. exists []. split. done. econstructor.
          pose proof (PF1 := IMP1 p p).
          pose proof (PF2 := IMP1 p (Imp_frm p p)).
          pose proof (PF3 := IMP2 p (Imp_frm p p) p).
          pose proof (PF4 := MP _ _ _ _ PF3 PF2). simpl in PF4.
          pose proof (PF5 := MP _ _ _ _ PF4 PF1). simpl in PF5.
          exact PF5.
        + exists [p]. split.
          { intros z z_in. econstructor; eauto. s!. simpl in z_in.
            destruct z_in as [z_in | []]. subst z. exact H_IN.
          }
          econstructor.
          pose proof (PF1 := IMP1 p A).
          pose proof (PF2 := AXM p).
          pose proof (PF3 := MP _ _ _ _ PF1 PF2). simpl in PF3.
          exact PF3.
      - exploit IHPF1.
        { ii. eapply INCL. ss!. }
        i. exploit IHPF2.
        { ii. eapply INCL. ss!. }
        i. destruct x0 as (ps1'&INCL1&(PF1')). destruct x1 as (ps2'&INCL2&(PF2')).
        exists (ps1' ++ ps2'). split.
        { intros z z_in. s!. destruct z_in as [z_in | z_in]; ss!. }
        econstructor. eapply MP with (p := Imp_frm A p); trivial.
        pose proof (RET := IMP2 A p q). change (proof ([] ++ ps1') (Imp_frm (Imp_frm A p) (Imp_frm A q))).
        eapply MP. exact RET. exact PF1'.
      - exploit IHPF. done. i. destruct x1 as (ps'&INCL'&(PF')).
        assert (claim : In A ps \/ E.fromList ps \subseteq Gamma).
        { clear ps' q x NOT_FREE PF PF' IHPF INCL'. revert A INCL. induction ps as [ | p ps IH]; i.
          - right. done.
          - assert (H_in : In p (p :: ps)) by done.
            s!. apply INCL in H_in. destruct H_in as [-> | H_in].
            + left. done.
            + assert (IH_supply : E.fromList ps \subseteq E.insert A Gamma).
              { ii. eapply INCL. revert H. ss!. }
              apply IH in IH_supply. destruct IH_supply as [IN | IN].
              * simpl. left. done.
              * right. done.
        }
        do 2 red in INCL'. destruct claim as [claim | claim].
        + pose proof (NOT_FREE A claim) as x_NOT_FREE_A.
          assert (NOT_FREE' : forall p : frm L, In p ps' -> is_not_free_in_frm x p).
          { i. ss!. }
          exists ps'. split. done. econstructor. rewrite <- app_nil_r with (l := ps').
          pose proof (GEN _ _ _ NOT_FREE' PF') as PF_1.
          pose proof (FA3 A q x) as PF_2.
          pose proof (MP _ _ _ _ PF_2 PF_1) as PF_3.
          pose proof (FA2 A x x_NOT_FREE_A) as PF_4.
          pose proof (IMP2 A (All_frm x A) (All_frm x q)) as PF_5.
          pose proof (IMP1 (Imp_frm (All_frm x A) (All_frm x q)) A) as PF_6.
          pose proof (MP _ _ _ _ PF_6 PF_3) as PF_7. simpl in *.
          pose proof (MP _ _ _ _ PF_5 PF_7) as PF_8. simpl in *.
          pose proof (MP _ _ _ _ PF_8 PF_4) as PF_9.
          exact PF_9.
        + exists ps. split. done. econstructor.
          pose proof (GEN _ _ _ NOT_FREE PF) as PF_1.
          pose proof (IMP1 (All_frm x q) A) as PF_2.
          pose proof (MP _ _ _ _ PF_2 PF_1) as PF_3.
          exact PF_3.
      - eapply EASY_CASE. eapply IMP1.
      - eapply EASY_CASE. eapply IMP2.
      - eapply EASY_CASE. eapply CP.
      - eapply EASY_CASE. eapply FA1.
      - eapply EASY_CASE. eapply FA2. done.
      - eapply EASY_CASE. eapply FA3.
      - eapply EASY_CASE. eapply EQN_REFL.
      - eapply EASY_CASE. eapply EQN_SYM.
      - eapply EASY_CASE. eapply EQN_TRANS.
      - eapply EASY_CASE. eapply EQN_FUN.
      - eapply EASY_CASE. eapply EQN_REL. 
    }
    destruct claim1 as (ps'&INCL'&(PF')).
    exists ps'. split.
    - ii. eapply INCL' in H. now firstorder.
    - eauto.
  }
  intros Gamma A B; split; intros PROVE.
  - destruct PROVE as (ps&INCL&(PF)). exists (ps ++ [A]). split.
    + red. simpl. intros p p_in. ss!.
    + econstructor. pose proof (PF_1 := AXM A). pose proof (PF_2 := MP _ _ _ _ PF PF_1). exact PF_2.
  - exact (BWD Gamma A B PROVE).
Qed.

End DEDUCTION_THEOREM.

Lemma MP_preserves_truth (p : frm L) (q : frm L) (ps1 : list (frm L)) (ps2 : list (frm L)) (Gamma : ensemble (frm L))
  (ENTAILS1 : forall Gamma, E.fromList ps1 \subseteq Gamma -> Gamma ⊨ Imp_frm p q)
  (ENTAILS2 : forall Gamma, E.fromList ps2 \subseteq Gamma -> Gamma ⊨ p)
  (INCL : E.fromList (ps1 ++ ps2) \subseteq Gamma)
  : Gamma ⊨ q.
Proof.
  assert (claim1 : E.fromList ps1 \subseteq Gamma) by now ii; eapply INCL; done!.
  assert (claim2 : E.fromList ps2 \subseteq Gamma) by now ii; eapply INCL; done!.
  specialize (ENTAILS1 Gamma claim1). specialize (ENTAILS2 Gamma claim2).
  red in ENTAILS1, ENTAILS2. ii. specialize (ENTAILS1 STRUCTURE env SATISFY). specialize (ENTAILS2 STRUCTURE env SATISFY).
  simpl in ENTAILS1. done.
Qed.

Lemma Gen_preserves_truth (x : ivar) (q : frm L) (ps : list (frm L)) (Gamma : ensemble (frm L))
  (NOT_FREE : forall p, In p ps -> is_not_free_in_frm x p)
  (ENTAILS1 : forall Gamma, E.fromList ps \subseteq Gamma -> Gamma ⊨ q)
  (INCL : E.fromList ps \subseteq Gamma)
  : Gamma ⊨ All_frm x q.
Proof.
  red in ENTAILS1. ii.
  assert (claim1 : is_free_in_frm x q = true \/ is_free_in_frm x q = false).
  { destruct (is_free_in_frm x q) as [ | ]; done. }
  destruct claim1 as [claim1 | claim1].
  - assert (claim2 : ~ In q ps).
    { intros H_contra. red in NOT_FREE. pose proof (NOT_FREE q H_contra). done. }
    red in SATISFY. eapply ENTAILS1 with (Gamma := E.delete q (E.fromList ps)).
    { ii. ss!. }
    ii. s!. rewrite <- not_free_no_effect_on_interpret_frm.
    { eapply SATISFY. eapply INCL. done!. }
    { eapply NOT_FREE. done!. }
  - rewrite <- not_free_no_effect_on_interpret_frm; trivial.
    eapply ENTAILS1 with (Gamma := Gamma); done.
Qed.

#[local] Existing Instance V.vec_isSetoid.

Lemma Fun_eqAxm_preserves_truth (f : L.(function_symbols)) (STRUCTURE : isStructureOf L) (env : ivar -> domain_of_discourse)
  : interpret_frm STRUCTURE env (Fun_eqAxm f).
Proof.
  enough (HACK : forall phi,
    forall phi_a_b : forall a, forall b, forall EQNS : interpret_trms STRUCTURE env a == interpret_trms STRUCTURE env b, interpret_frm STRUCTURE env (phi a b),
    interpret_frm STRUCTURE env (nat_rec (fun _ => frm L) (prod_rec (fun _ => frm L) phi (varcouples (function_arity_table L f))) (fun n => fun q => Imp_frm (Eqn_frm (Var_trm (n + n)) (Var_trm (S (n + n)))) q) (function_arity_table L f))
  ).
  { unfold Fun_eqAxm. eapply HACK. ii. simpl. do 2 rewrite interpret_trm_unfold. eapply function_interpret_preserves_eqProp. exact EQNS. }
  simpl. induction (function_arity_table L f) as [ | n IH].
  - ii. eapply phi_a_b. reflexivity.
  - ii. specialize IH with (phi := fun ts => fun ts' => phi (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts')).
    destruct (varcouples n) as [lhs rhs] eqn: OBS. simpl in *. rewrite OBS. simpl. eapply IH. ii. eapply phi_a_b. Fin.caseS i.
    + simpl. done.
    + rewrite interpret_trms_unfold. symmetry. rewrite interpret_trms_unfold. rewrite V.nth_unfold. symmetry. rewrite V.nth_unfold.
      do 2 rewrite V.tail_unfold. done.
Qed.

Lemma Rel_eqAxm_preserves_truth (R : L.(relation_symbols)) (STRUCTURE : isStructureOf L) (env : ivar -> domain_of_discourse)
  : interpret_frm STRUCTURE env (Rel_eqAxm R).
Proof.
  enough (HACK : forall phi,
    forall phi_a_b : forall a, forall b, forall EQNS : interpret_trms STRUCTURE env a == interpret_trms STRUCTURE env b, interpret_frm STRUCTURE env (phi a b),
    interpret_frm STRUCTURE env (nat_rec (fun _ => frm L) (prod_rec (fun _ => frm L) phi (varcouples (relation_arity_table L R))) (fun n => fun q => Imp_frm (Eqn_frm (Var_trm (n + n)) (Var_trm (S (n + n)))) q) (relation_arity_table L R))
  ).
  { unfold Rel_eqAxm. eapply HACK. ii. simpl. pose proof (@relation_interpret_preserves_eqProp L STRUCTURE R _ _ EQNS). done. }
  simpl. induction (relation_arity_table L R) as [ | n IH].
  - ii. eapply phi_a_b. reflexivity.
  - ii. specialize IH with (phi := fun ts => fun ts' => phi (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts')).
    destruct (varcouples n) as [lhs rhs] eqn: OBS. simpl in *. rewrite OBS. simpl. eapply IH. ii. eapply phi_a_b. Fin.caseS i.
    + simpl. done.
    + rewrite interpret_trms_unfold. symmetry. rewrite interpret_trms_unfold. rewrite V.nth_unfold. symmetry. rewrite V.nth_unfold.
      do 2 rewrite V.tail_unfold. done.
Qed.

Lemma for_ByHyp (Gamma : ensemble (frm L)) (p : frm L)
  (H_IN : p \in Gamma)
  : Gamma \proves p.
Proof.
  exists [p]. split.
  - intros ?. done!.
  - econstructor. eapply AXM.
Qed.

Lemma for_Imp_I (Gamma : ensemble (frm L)) (p : frm L) (q : frm L)
  (PROVE1 : E.insert p Gamma \proves q)
  : Gamma \proves Imp_frm p q.
Proof.
  rewrite Deduction_theorem. done.
Qed.

Lemma for_Imp_E (Gamma : ensemble (frm L)) (p : frm L) (q : frm L)
  (PROVE1 : Gamma \proves Imp_frm p q)
  (PROVE2 : Gamma \proves p)
  : Gamma \proves q.
Proof.
  destruct PROVE1 as (ps1 & INCL1 & (PF1)), PROVE2 as (ps2 & INCL2 & (PF2)).
  exists (ps1 ++ ps2). split.
  - ii. done!.
  - econstructor. eapply MP; [exact PF1 | exact PF2].
Qed.

Lemma for_compose Gamma p q r
  (PROVE1 : Gamma \proves Imp_frm q r)
  (PROVE2 : Gamma \proves Imp_frm p q)
  : Gamma \proves Imp_frm p r.
Proof.
  destruct PROVE1 as (ps1 & INCL1 & (PF1)), PROVE2 as (ps2 & INCL2 & (PF2)).
  exists (ps1 ++ ps2). split.
  - ii. done!.
  - econstructor. eapply MP.
    + rewrite <- app_nil_l with (l := ps1). eapply MP.
      * eapply proof_compose.
      * exact PF1.
    + exact PF2.
Qed.

Lemma for_CP1 Gamma p q
  (PROVE : Gamma \proves Imp_frm p q)
  : Gamma \proves Imp_frm (Neg_frm q) (Neg_frm p).
Proof.
  destruct PROVE as (ps1 & INCL1 & (PF1)).
  exists ps1. split; trivial. econstructor.
  rewrite <- app_nil_l with (l := ps1). eapply MP. eapply proof_cp1. exact PF1.
Qed.

Lemma for_MP (Gamma : ensemble (frm L)) (Gamma' : ensemble (frm L)) (p : frm L) (q : frm L)
  (PROVE1 : Gamma \proves Imp_frm p q)
  (PROVE2 : Gamma' \proves p)
  : E.union Gamma Gamma' \proves q.
Proof.
  destruct PROVE1 as (ps1 & INCL1 & (PF1)).
  destruct PROVE2 as (ps2 & INCL2 & (PF2)).
  exists (ps1 ++ ps2). split.
  - ii. done!.
  - econstructor. eapply MP; [exact PF1 | exact PF2].
Qed.

Lemma for_All_I (x : ivar) (p : frm L) (Gamma : ensemble (frm L))
  (FRESH : is_not_free_in_frms x Gamma)
  (PROVE : Gamma \proves p)
  : Gamma \proves All_frm x p.
Proof.
  destruct PROVE as (ps & INCL & (PF)). exists ps. split; trivial. econstructor. eapply GEN.
  - intros q q_in. done.
  - exact PF.
Qed.

Lemma proves_alpha_comm_lemma (p : frm L) (q : frm L)
  (ALPHA : p ≡ q)
  : E.singleton p \proves q /\ E.singleton q \proves p.
Proof.
  revert q ALPHA. pattern p. revert p. eapply @frm_depth_lt_ind; ii. destruct ALPHA.
  - rewrite <- EQ. split; eapply for_ByHyp; done.
  - rewrite <- EQ1, <- EQ2. split; eapply for_ByHyp; done.
  - assert (rank_LT1: frm_depth p1 < frm_depth (Neg_frm p1)) by now simpl; lia.
    pose proof (IH p1 rank_LT1 _ ALPHA) as [PROVE1 PROVE2].
    split.
    + eapply for_Imp_E. 2:{ eapply for_ByHyp. rewrite E.in_singleton_iff. reflexivity. }
      eapply for_CP1. eapply for_Imp_I. destruct PROVE2 as (ps&INCL&(PF)).
      exists ps. split. { intros z z_in. rewrite E.in_insert_iff; unnw. pose proof (INCL z z_in) as H_IN. rewrite E.in_singleton_iff in H_IN. done. } { econstructor. exact PF. }
    + eapply for_Imp_E. 2:{ eapply for_ByHyp. rewrite E.in_singleton_iff. reflexivity. }
      eapply for_CP1. eapply for_Imp_I. destruct PROVE1 as (ps&INCL&(PF)).
      exists ps. split. { intros z z_in. rewrite E.in_insert_iff; unnw. pose proof (INCL z z_in) as H_IN. rewrite E.in_singleton_iff in H_IN. done. } { econstructor. exact PF. }
  - assert (rank_LT1 : frm_depth p1 < frm_depth (Imp_frm p1 p2)) by now simpl; lia.
    pose proof (IH p1 rank_LT1 _ ALPHA1) as [PROVE1 PROVE2].
    assert (rank_LT2 : frm_depth p2 < frm_depth (Imp_frm p1 p2)) by now simpl; lia.
    pose proof (IH p2 rank_LT2 _ ALPHA2) as [PROVE3 PROVE4].
    split.
    + eapply for_Imp_I.
      assert (PROVE5 : E.insert p1' (E.singleton (Imp_frm p1 p2)) \proves p1).
      { destruct PROVE2 as (ps&INCL&(PF)). exists ps. split.
        - intros z z_in. pose proof (INCL z z_in) as H_IN. rewrite E.in_singleton_iff in H_IN; unnw. subst z. ss!.
        - econstructor. exact PF.
      }
      assert (PROVE6 : E.insert p1' (E.singleton (Imp_frm p1 p2)) \proves p2).
      { eapply for_Imp_E.
        - eapply for_ByHyp. right. ss!.
        - exact PROVE5.
      }
      eapply for_Imp_E. 2: exact PROVE6. eapply for_Imp_I.
      destruct PROVE3 as (ps&INCL&(PF)). exists ps. split.
      * intros z z_in. pose proof (INCL z z_in) as H_IN. ss!.
      * econstructor. exact PF.
    + eapply for_Imp_I.
      assert (PROVE5 : E.insert p1 (E.singleton (Imp_frm p1' p2')) \proves p1').
      { destruct PROVE1 as (ps&INCL&(PF)). exists ps. split.
        - intros z z_in. pose proof (INCL z z_in) as H_IN. ss!.
        - econstructor. exact PF.
      }
      assert (PROVE6 : E.insert p1 (E.singleton (Imp_frm p1' p2')) \proves p2').
      { eapply for_Imp_E.
        - eapply for_ByHyp. right. ss!.
        - exact PROVE5.
      }
      eapply for_Imp_E. 2: exact PROVE6. eapply for_Imp_I.
      destruct PROVE4 as (ps&INCL&(PF)). exists ps. split.
      * intros z z_in. pose proof (INCL z z_in) as H_IN. ss!.
      * econstructor. exact PF.
  - rename p1 into p, p1' into q. rename y into x, y' into y.
    assert (rank_EQ1 : frm_depth p = frm_depth (subst_frm (one_subst x (Var_trm z)) p)).
    { rewrite subst_preserves_rank. reflexivity. }
    assert (rank_EQ2 : frm_depth q = frm_depth (subst_frm (one_subst y (Var_trm z)) q)).
    { rewrite subst_preserves_rank. reflexivity. }
    assert (rank_EQ3 : frm_depth (subst_frm (one_subst x (Var_trm z)) p) = frm_depth (subst_frm (one_subst y (Var_trm z)) q)).
    { eapply alpha_equiv_compath_rank. exact ALPHA. }
    assert (rank_LT1 : frm_depth p < frm_depth (All_frm x p)) by now simpl; lia.
    assert (rank_LT2 : frm_depth q < frm_depth (All_frm x p)) by now simpl; lia.
    set (p' := subst_frm (one_subst x (Var_trm z)) p) in *. set (q' := subst_frm (one_subst y (Var_trm z)) q) in *.
    assert (rank_LT3 : frm_depth p' < frm_depth (All_frm x p)) by now simpl; lia.
    assert (rank_LT4 : frm_depth (subst_frm (one_subst y (Var_trm y)) q) < frm_depth (All_frm x p)) by now rewrite subst_preserves_rank; simpl; lia.
    assert (rank_LT5 : frm_depth (subst_frm (one_subst x (Var_trm x)) p) < frm_depth (All_frm x p)) by now rewrite subst_preserves_rank; simpl; lia.
    assert (ALPHA1 : subst_frm (one_subst y (Var_trm y)) q ≡ q).
    { eapply subst_nil_frm; intros w w_free. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec w y) as [ | ]; done. }
    assert (ALPHA2: subst_frm (one_subst x (Var_trm x)) p ≡ p).
    { eapply subst_nil_frm; intros w w_free. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec w x) as [ | ]; done. }
    pose proof (IH p' rank_LT3 q' ALPHA) as [PROVE1 PROVE2].
    pose proof (IH _ rank_LT4 q ALPHA1) as [PROVE3 PROVE4].
    pose proof (IH _ rank_LT5 p ALPHA2) as [PROVE5 PROVE6].
    assert (claim1 : E.empty \proves q' -> E.empty \proves All_frm z q').
    { intros (ps&INCL&(PF)). exists ps. split. intros ? H_in. done!. econstructor. eapply GEN. done!. exact PF. }
    assert (claim2 : E.empty \proves p' -> E.empty \proves All_frm z p').
    { intros (ps&INCL&(PF)). exists ps. split. intros ? H_in. done!. econstructor. eapply GEN. done!. exact PF. }
    clear rank_EQ1 rank_EQ2 rank_EQ3 rank_LT1 rank_LT2 rank_LT3 rank_LT4 rank_LT5.
    assert (EQ1 : subst_frm (one_subst z (Var_trm y)) q' = subst_frm (one_subst y (Var_trm y)) q).
    { unfold q'. rewrite <- subst_compose_frm_spec. eapply equiv_subst_in_frm_implies_subst_frm_same.
      intros w FREE. unfold subst_compose, one_subst, cons_subst, nil_subst. destruct (eq_dec w y) as [EQ | NE].
      - rewrite subst_trm_unfold. destruct (eq_dec z z) as [EQ' | NE']; done.
      - rewrite subst_trm_unfold. destruct (eq_dec w z) as [EQ' | NE'].
        + subst w. simpl in RFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in RFRESH. destruct RFRESH as [? | ?]; done.
        + done.
    }
    assert (EQ2 : subst_frm (one_subst z (Var_trm x)) p' = subst_frm (one_subst x (Var_trm x)) p).
    { unfold p'. rewrite <- subst_compose_frm_spec. eapply equiv_subst_in_frm_implies_subst_frm_same.
      intros w FREE. unfold subst_compose, one_subst, cons_subst, nil_subst. destruct (eq_dec w x) as [EQ | NE].
      - rewrite subst_trm_unfold. destruct (eq_dec z z) as [EQ' | NE']; done.
      - rewrite subst_trm_unfold. destruct (eq_dec w z) as [EQ' | NE'].
        + subst w. simpl in LFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in LFRESH. destruct LFRESH as [? | ?]; done.
        + done.
    }
    split.
    + assert (PROVE7 : E.singleton (All_frm x p) \proves All_frm z p').
      { eapply for_Imp_E.
        - exists []. split. done!. econstructor. eapply proof_rebind_All_frm. exact LFRESH.
        - eapply for_ByHyp. done.
      }
      assert (PROVE8 : E.singleton (All_frm x p) \proves (Imp_frm (All_frm z p') (All_frm z q'))).
      { enough (PROVE : E.empty \proves Imp_frm p' q').
        - destruct PROVE as (ps&INCL&(PF)). assert (EQ: ps = []). destruct ps as [ | p'' ps'']; trivial.
          + assert (IN : p'' \in E.fromList (p'' :: ps'')) by now done!. apply INCL in IN. inv IN.
          + subst ps. exists []. split. ss!. econstructor. rewrite <- app_nil_l with (l := []). eapply MP.
            * eapply FA3.
            * eapply GEN. intros ? []. exact PF.
        - destruct PROVE1 as (ps&INCL&(PF)). eapply for_Imp_I. exists ps. split.
          + intros w w_in. pose proof (INCL w w_in) as H_IN. done!.
          + econstructor. exact PF.
      }
      pose proof (PROVE9 := for_Imp_E _ _ _ PROVE8 PROVE7).
      assert (PROVE10 : E.singleton (All_frm x p) \proves Imp_frm (All_frm z q') (All_frm y q)).
      { assert (PROVE : E.insert (All_frm z q') (E.singleton (All_frm x p)) \proves (All_frm y (subst_frm (one_subst y (Var_trm y)) q))).
        { rewrite <- EQ1. rewrite <- Deduction_theorem. exists []. split. intros ? []. econstructor. eapply proof_rebind_All_frm.
          red. simpl. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. simpl in RFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in RFRESH. unfold q'.
          destruct (eq_dec y z) as [EQ | NE]; [done | destruct RFRESH as [FRESH' | <-]; [left | done]].
          eapply frm_is_fresh_in_subst_iff. unfold frm_is_fresh_in_subst. eapply forallb_forall. intros w w_free. rewrite fv_is_free_in_frm in w_free. unfold "∘"%prg.
          rewrite negb_true_iff. unfold one_subst, cons_subst, nil_subst.
          destruct (eq_dec w y) as [w_eq_y | w_ne_y].
          - rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
          - rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
        }
        assert (PROVE' : E.empty \proves (Imp_frm (subst_frm (one_subst y (Var_trm y)) q) q)).
        { eapply for_Imp_I. destruct PROVE3 as (ps&INCL&(PF)). exists ps. split. intros w w_in. pose proof (INCL w w_in) as H_IN. done!. econstructor. exact PF. }
        destruct PROVE' as (ps&INCL&(PF)).
        assert (EQ: ps = []).
        { destruct ps as [ | p'' ps'']. reflexivity. assert (IN : p'' \in E.fromList (p'' :: ps'')) by now done!. apply INCL in IN. inv IN. }
        subst ps. clear INCL. eapply for_Imp_I. destruct PROVE as (ps&INCL&(PF')). exists ps. split. exact INCL. econstructor.
        rewrite <- app_nil_l with (l := ps). eapply MP. 2: exact PF'. rewrite <- app_nil_l with (l := []). eapply MP. eapply FA3.
        eapply GEN. intros ? []. exact PF.
      }
      eapply for_Imp_E. exact PROVE10. exact PROVE9.
    + assert (PROVE7 : E.singleton (All_frm y q) \proves All_frm z q').
      { eapply for_Imp_E.
        - exists []. split. intros ? []. econstructor. eapply proof_rebind_All_frm. exact RFRESH.
        - eapply for_ByHyp. done.
      }
      assert (PROVE8 : E.singleton (All_frm y q) \proves (Imp_frm (All_frm z q') (All_frm z p'))).
      { enough (PROVE: E.empty \proves Imp_frm q' p').
        - destruct PROVE as (ps&INCL&(PF)).
          assert (EQ : ps = []).
          { destruct ps as [ | p'' ps'']; trivial. assert (IN : p'' \in E.fromList (p'' :: ps'')) by done!. apply INCL in IN. inv IN. }
          subst ps. exists []. split. intros ? []. econstructor. rewrite <- app_nil_l with (l := []). eapply MP.
          + eapply FA3.
          + eapply GEN. intros ? []. exact PF.
        - destruct PROVE2 as (ps&INCL&(PF)). eapply for_Imp_I. exists ps. split.
          + intros w w_in. pose proof (INCL w w_in) as H_IN. done!.
          + econstructor. exact PF.
      }
      pose proof (PROVE9 := for_Imp_E _ _ _ PROVE8 PROVE7).
      assert (PROVE10 : E.singleton (All_frm y q) \proves Imp_frm (All_frm z p') (All_frm x p)).
      { assert (PROVE : E.insert (All_frm z p') (E.singleton (All_frm y q)) \proves (All_frm x (subst_frm (one_subst x (Var_trm x)) p))).
        { rewrite <- EQ2. rewrite <- Deduction_theorem. exists []. split. intros ? []. econstructor. eapply proof_rebind_All_frm.
          red. simpl. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. simpl in LFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in LFRESH. unfold p'.
          destruct (eq_dec x z) as [EQ | NE]; [done | destruct LFRESH as [LFRESH | <-]; [left | done]].
          eapply frm_is_fresh_in_subst_iff. unfold frm_is_fresh_in_subst. eapply forallb_forall. intros w w_free. rewrite fv_is_free_in_frm in w_free. unfold "∘"%prg.
          rewrite negb_true_iff. unfold one_subst, cons_subst, nil_subst.
          destruct (eq_dec w x) as [w_eq_x | w_ne_x].
          - rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
          - rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
        }
        assert (PROVE' : E.empty \proves (Imp_frm (subst_frm (one_subst x (Var_trm x)) p) p)).
        { eapply for_Imp_I. destruct PROVE5 as (ps&INCL&(PF)). exists ps. split. intros w w_in. pose proof (INCL w w_in) as H_IN. done!. econstructor. exact PF. }
        destruct PROVE' as (ps&INCL&(PF)).
        assert (EQ: ps = []).
        { destruct ps as [ | p'' ps'']. reflexivity. assert (IN : p'' \in E.fromList (p'' :: ps'')) by done!. apply INCL in IN. inv IN. }
        subst ps. clear INCL. eapply for_Imp_I. destruct PROVE as (ps&INCL&(PF')). exists ps. split. exact INCL. econstructor.
        rewrite <- app_nil_l with (l := ps). eapply MP. 2: exact PF'. rewrite <- app_nil_l with (l := []). eapply MP. eapply FA3.
        eapply GEN. intros ? []. exact PF.
      }
      eapply for_Imp_E. exact PROVE10. exact PROVE9.
Qed.

Lemma proves_alpha_proves (Gamma : ensemble (frm L)) (p : frm L) (q : frm L)
  (PROVE : Gamma \proves p)
  (ALPHA : p ≡ q)
  : Gamma \proves q.
Proof.
  apply proves_alpha_comm_lemma in ALPHA. destruct ALPHA as [PROVE' _].
  eapply for_Imp_E. 2: exact PROVE. eapply for_Imp_I. destruct PROVE' as (ps&INCL&(PF)).
  exists ps. split. intros w w_in. pose proof (INCL w w_in) as H_IN. rewrite E.in_singleton_iff in H_IN; unnw.
  subst w. ss!. constructor. exact PF.
Qed.

#[global]
Add Parametric Morphism
  : proves with signature (eqProp ==> alpha_equiv ==> iff) as proves_alpha_comm.
Proof.
  intros Gamma Gamma' Gamma_eq_Gamma' p p' ALPHA. split; intros PROVE.
  - eapply proves_alpha_proves. 2: exact ALPHA. destruct PROVE as (ps&INCL&(PF)). exists ps. split.
    + ii. rewrite <- Gamma_eq_Gamma'. eapply INCL. assumption.
    + econstructor. exact PF.
  - symmetry in ALPHA. eapply proves_alpha_proves. 2: exact ALPHA. destruct PROVE as (ps&INCL&(PF)). exists ps. split.
    + ii. rewrite -> Gamma_eq_Gamma'. eapply INCL. assumption.
    + econstructor. exact PF.
Qed.

Lemma alpha_hyp (Gamma : ensemble (frm L)) (p : frm L) (q : frm L)
  (PROVE : p \in Gamma)
  (ALPHA : p ≡ q)
  : Gamma \proves q.
Proof.
  rewrite <- ALPHA. eapply for_ByHyp. done.
Qed.

Lemma extend_proves Gamma Gamma' A
  (SUBSET : Gamma \subseteq Gamma')
  (PROVES : Gamma \proves A)
  : Gamma' \proves A.
Proof.
  destruct PROVES as (ps&INCL&(PF)). exists ps. split. done. econstructor; exact PF.
Qed.

Lemma cut_one A B Gamma
  (PROVE1 : E.singleton A \proves B)
  (PROVE2 : Gamma \proves A)
  : Gamma \proves B.
Proof.
  assert (claim1 : E.singleton A == E.insert A E.empty).
  { change (forall x, x \in E.singleton A <-> x \in E.insert A E.empty). intros x. rewrite E.in_singleton_iff; unnw. rewrite E.in_insert_iff; unnw. rewrite E.in_empty_iff; unnw. done. }
  rewrite claim1 in PROVE1. rewrite <- Deduction_theorem in PROVE1.
  destruct PROVE1 as (ps1&INCL1&(PF1)), PROVE2 as (ps2&INCL2&(PF2)).
  exists ps2. split. done. econstructor. rewrite <- app_nil_l with (l := ps2).
  assert (claim2: ps1 = []).
  { destruct ps1 as [ | p' ps']. reflexivity. assert (IN : p' \in E.fromList (p' :: ps')) by now done!. apply INCL1 in IN. inv IN. }
  subst ps1. eapply MP; [exact PF1 | exact PF2].
Qed.

Lemma cut_one' A B Gamma
  (PROVE1 : E.insert A E.empty \proves B)
  (PROVE2 : Gamma \proves A)
  : Gamma \proves B.
Proof.
  assert (claim1 : E.singleton A == E.insert A E.empty).
  { change (forall x, x \in E.singleton A <-> x \in E.insert A E.empty). intros x. rewrite E.in_singleton_iff; unnw. rewrite E.in_insert_iff; unnw. rewrite E.in_empty_iff; unnw. done. }
  rewrite <- claim1 in PROVE1.  eapply cut_one; eauto.
Qed.

Lemma cut A B Gamma
  (PROVE1 : E.insert A Gamma \proves B)
  (PROVE2 : Gamma \proves A)
  : Gamma \proves B.
Proof.
  rewrite <- Deduction_theorem in PROVE1. destruct PROVE1 as (ps1&INCL1&(PF1)), PROVE2 as (ps2&INCL2&(PF2)).
  exists (ps1 ++ ps2). split.
  - intros q q_in. done!.
  - econstructor. eapply MP with (p := A); trivial.
Qed.

Lemma for_All_E (x : ivar) (t : trm L) (p : frm L) (Gamma : ensemble (frm L))
  (PROVE : Gamma \proves All_frm x p)
  : Gamma \proves subst_frm (one_subst x t) p.
Proof.
  eapply cut_one' with (A := All_frm x p).
  - rewrite <- Deduction_theorem. exists []. split. ii. done!. econstructor. eapply FA1.
  - done.
Qed.

Lemma rebind_All_frm_fwd (Gamma : ensemble (frm L)) (x : ivar) (x' : ivar) (p : frm L)
  (FRESH : is_not_free_in_frm x' (All_frm x p))
  : Gamma \proves Imp_frm (All_frm x p) (All_frm x' (subst_frm (one_subst x (Var_trm x')) p)).
Proof.
  exists []. split. intros ? H. done. econstructor. eapply proof_rebind_All_frm. exact FRESH.
Qed.

Lemma rebind_All_frm_bwd (Gamma : ensemble (frm L)) (x : ivar) (x' : ivar) (p : frm L)
  (FRESH : is_not_free_in_frm x' (All_frm x p))
  : Gamma \proves Imp_frm (All_frm x' (subst_frm (one_subst x (Var_trm x')) p)) (All_frm x p).
Proof.
  eapply extend_proves with (Gamma := E.empty). done.
  eapply for_Imp_I. eapply for_All_I.
  { intros q q_in. s!. destruct q_in as [-> | []]. s!. destruct (eq_dec x x') as [EQ | NE].
    - subst. right. done.
    - destruct FRESH as [FRESH | H_contra]. 2: done. left.
      rewrite <- frm_is_fresh_in_subst_iff. unfold frm_is_fresh_in_subst. rewrite forallb_forall.
      intros u u_free. unfold "∘"%prg. rewrite negb_true_iff. unfold one_subst, cons_subst, nil_subst.
      rewrite fv_is_free_in_frm in u_free. destruct (eq_dec u x) as [EQ' | NE'].
      + rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
      + rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
  }
  eapply proves_alpha_proves with (p := subst_frm (one_subst x' (Var_trm x)) (subst_frm (one_subst x (Var_trm x')) p)).
  - eapply for_All_E. eapply for_ByHyp. ss!.
  - rewrite <- subst_compose_frm_spec. rewrite <- subst_nil_frm with (p := p) (s := nil_subst) at 2. 2: done.
    eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
    ii. unfold subst_compose. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec z x) as [EQ1 | NE1].
    + rewrite subst_trm_unfold. destruct (eq_dec x' x') as [EQ2 | NE2]; done.
    + rewrite subst_trm_unfold. destruct (eq_dec z x') as [EQ2 | NE2]. 2: done.
      subst z. red in FRESH. simpl in FRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in FRESH. destruct FRESH as [FRESH | <-]; done.
Qed.

Lemma for_All_I' (x : ivar) (y : ivar) (p : frm L) (Gamma : ensemble (frm L))
  (NOT_FREE1 : is_not_free_in_frms y Gamma)
  (NOT_FREE2 : is_not_free_in_frm y (All_frm x p))
  (PROVE : Gamma \proves subst_frm (one_subst x (Var_trm y)) p)
  : Gamma \proves All_frm x p.
Proof.
  eapply cut_one' with (A := (All_frm y (subst_frm (one_subst x (Var_trm y)) p))).
  - rewrite <- Deduction_theorem. eapply rebind_All_frm_bwd. exact NOT_FREE2.
  - eapply for_All_I. exact NOT_FREE1. exact PROVE.
Qed.

Lemma rebind_All_frm (Gamma : ensemble (frm L)) (x : ivar) (x' : ivar) (p : frm L)
  (FRESH : is_not_free_in_frm x' (All_frm x p))
  : Gamma \proves (All_frm x p) <-> Gamma \proves (All_frm x' (subst_frm (one_subst x (Var_trm x')) p)).
Proof.
  split.
  - intros PROVE. eapply cut_one'. 2: exact PROVE.
    rewrite <- Deduction_theorem. eapply rebind_All_frm_fwd. exact FRESH.
  - intros PROVE. eapply cut_one'. 2: exact PROVE.
    rewrite <- Deduction_theorem. eapply rebind_All_frm_bwd. exact FRESH.
Qed.

Lemma open_closed_frm (Gamma : ensemble (frm L)) (p : frm L)
  (PROVE : Gamma \proves closed_frm p)
  : Gamma \proves p.
Proof.
  revert PROVE. unfold closed_frm. revert Gamma. induction (nodup eq_dec (fvs_frm p)) as [ | x xs IH]; simpl; ii.
  - exact PROVE.
  - eapply IH. eapply proves_alpha_proves with (p := subst_frm (one_subst x (Var_trm x)) (close_ivars p xs)).
    + eapply for_All_E. exact PROVE.
    + eapply subst_nil_frm. intros u u_free. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec u x) as [? | ?]; done.
Qed.

Definition equiv_deductible (p1 : frm L) (p2 : frm L) : Prop :=
  E.singleton p1 \proves p2 /\ E.singleton p2 \proves p1.

#[local]
Instance equiv_deductible_reflexive
  : Reflexive equiv_deductible.
Proof.
  intros p1. split; eapply for_ByHyp; done.
Qed.

#[local]
Instance equiv_deductible_symmetric
  : Symmetric equiv_deductible.
Proof.
  intros p1 p2 [? ?]; split; done.
Qed.

#[local]
Instance equiv_deductible_transitive
  : Transitive equiv_deductible.
Proof.
  intros p1 p2 p3 [PROVE1 PROVE2] [PROVE3 PROVE4]. split.
  - eapply cut with (A := p2). 2: done. eapply extend_proves with (Gamma := E.singleton p2). 2: done. intros q q_in. ss!.
  - eapply cut with (A := p2). 2: done. eapply extend_proves with (Gamma := E.singleton p2). 2: done. intros q q_in. ss!.
Qed.

#[local]
Instance equiv_deductible_Equivalence : Equivalence equiv_deductible :=
  { Equivalence_Reflexive := equiv_deductible_reflexive
  ; Equivalence_Symmetric := equiv_deductible_symmetric
  ; Equivalence_Transitive := equiv_deductible_transitive
  }.

#[local]
Instance upto_equiv_deductible : isSetoid (frm L) :=
  { eqProp := equiv_deductible
  ; eqProp_Equivalence := equiv_deductible_Equivalence
  }.

#[local]
Add Parametric Morphism
  : proves with signature (eqProp ==> eqProp ==> iff) as proves_equiv_deductible.
Proof.
  intros Gamma Gamma' Gamma_eq_Gamma' p1 p2 [PROVE1 PROVE2]. pose proof (@proves_alpha_comm Gamma Gamma' Gamma_eq_Gamma' p2 p2 (alpha_equiv_Reflexive p2)) as claim1. rewrite <- claim1. clear claim1.
  split; intros PROVE.
  - eapply cut with (A := p1). 2: done. eapply extend_proves. 2: exact PROVE1. intros q q_in. ss!.
  - eapply cut with (A := p2). 2: done. eapply extend_proves. 2: exact PROVE2. intros q q_in. ss!.
Qed.

Section SUBST. (* Reference: "https://github.com/princeton-vl/CoqGym/blob/master/coq_projects/goedel/subAll.v" *)

Fixpoint close_from (a : nat) (n : nat) (p : frm L) {struct n} : frm L :=
  match n with
  | O => p
  | S m => All_frm (a + m) (close_from a m p)
  end.

Lemma close_from_alpha (a : nat) (n : nat) (p : frm L) (p' : frm L)
  (ALPHA : p ≡ p')
  : close_from a n p ≡ close_from a n p'.
Proof.
  revert a n. induction ALPHA; i.
  - subst ts'. reflexivity.
  - subst t1' t2'. reflexivity.
  - induction n as [ | n IH]; simpl.
    + eapply alpha_Neg_frm. done.
    + eapply alpha_equiv_All_frm_intro. done.
  - induction n as [ | n IH]; simpl.
    + eapply alpha_Imp_frm; done.
    + eapply alpha_equiv_All_frm_intro. done.
  - induction n as [ | n IH]; simpl.
    + eapply alpha_All_frm with (z := z); try done.
    + eapply alpha_equiv_All_frm_intro. done.
Qed.

#[global]
Add Parametric Morphism
  : close_from with signature (eq ==> eq ==> alpha_equiv ==> alpha_equiv)
  as close_from_compat_with_alpha.
Proof.
  intros a n p p' ALPHA. eapply close_from_alpha. exact ALPHA.
Qed.

#[local] Opaque le_lt_dec.

Fixpoint multiple_subst (m : nat) (n : nat) (p : frm L) : frm L :=
  match n with
  | O => p
  | S n' => subst1 n' (Var_trm (m + n')) (multiple_subst m n' p)
  end.

Lemma multiple_subst_simultaneous_subst (m : nat) (n : nat) (p : frm L)
  (LE : n <= m)
  (BOUND : forall z : ivar, is_free_in_frm z p = true -> z < m)
  : multiple_subst m n p ≡ subst_frm (fun x : ivar => if le_lt_dec n x then Var_trm x else Var_trm (m + x)) p.
Proof.
  revert m p LE BOUND. induction n as [ | n IH]; simpl; i.
  - symmetry. eapply subst_nil_frm. intros u u_free.
    destruct (le_lt_dec 0 u) as [LE1 | LT1]; try done.
  - rewrite subst1_nice. rewrite IH with (p := p); try done. rewrite <- subst_compose_frm_spec.
    eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same. intros u u_free.
    unfold subst_compose, one_subst, cons_subst, nil_subst. destruct (le_lt_dec n u) as [EQ1 | NE1], (le_lt_dec (S n) u) as [LE2 | LT2]; try done.
    + rewrite subst_trm_unfold. destruct (eq_dec u n) as [EQ3 | NE3]; try done.
    + rewrite subst_trm_unfold. destruct (eq_dec u n) as [EQ3 | NE3]; try done.
    + rewrite subst_trm_unfold. unfold eq_dec. destruct (ivar_hasEqDec (m + u) n) as [EQ3 | NE3]; try done.
Qed.

Lemma lift_close_from (n : nat) (p : frm L) (m : nat)
  (LE : n <= m)
  (BOUND : forall z : ivar, is_free_in_frm z p = true -> z < m)
  : E.empty \proves Imp_frm (close_from 0 n p) (close_from m n (subst_frm (fun x : ivar => if le_lt_dec n x then Var_trm x else Var_trm (m + x)) p)).
Proof.
  rewrite <- multiple_subst_simultaneous_subst; trivial. revert m LE p BOUND. induction n as [ | n IH]; i; simpl in *.
  - eapply for_Imp_I. eapply for_ByHyp. ss!.
  - remember (m + n) as y eqn: H_y. eapply for_Imp_I. eapply for_All_I.
    + intros q q_in. autorewrite with simplication_hints in q_in. destruct q_in as [-> | []].
      destruct (is_free_in_frm y (All_frm n (close_from 0 n p))) as [ | ] eqn: H_OBS; trivial.
      assert (claim1 : forall z : ivar, n <= z -> m <= z -> is_free_in_frm z (All_frm n (close_from 0 n p)) = false).
      { clear H_OBS IH y H_y. intros z. revert p m z LE BOUND. induction n as [ | n IH]; simpl; intros p m z LE BOUND LE1 LE2.
        - simpl. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. pose proof (BOUND z). destruct (is_free_in_frm z p) as [ | ]; try done.
        - do 2 rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. pose proof (eq_dec z n) as [H | H]; try tauto. pose proof (eq_dec z (S n)) as [H' | H']; try tauto.
          left. left. exploit (IH p m z); try done.
      }
      rewrite <- claim1 with (z := y); done.
    + assert (claim1 : forall p : frm L, forall v1 : nat, forall v2 : nat, forall v3 : nat, forall v4 : nat, v3 < v1 -> v1 + v2 <= v4 -> E.empty \proves Imp_frm (subst1 v3 (Var_trm v4) (close_from v1 v2 p)) (close_from v1 v2 (subst1 v3 (Var_trm v4) p))).
      { clear. intros p s n. induction n as [ | n IH]; simpl; i.
        - eapply for_Imp_I; eapply for_ByHyp. autorewrite with simplication_hints. done.
        - rewrite subst1_unfold. set (z := fresh_var v3 (Var_trm v4) (close_from s n p)). simpl. remember (s + n) as y eqn: H_y.
          unfold eq_dec. destruct (ivar_hasEqDec v3 y) as [EQ1 | NE1]; try done. rewrite is_free_in_trm_unfold. obs_eqb v4 y; try done.
          eapply for_Imp_I. eapply for_All_I.
          + intros q q_in. autorewrite with simplication_hints in q_in. destruct q_in as [-> | []].
            simpl. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. done.
          + eapply cut_one' with (A := subst1 v3 (Var_trm v4) (close_from s n p)).
            * rewrite <- Deduction_theorem. eapply IH; done.
            * rewrite <- subst1_id with (x := y) (p := subst1 v3 (Var_trm v4) (close_from s n p)) at 2. rewrite subst1_nice with (x := y) (t := Var_trm y) (p := subst1 v3 (Var_trm v4) (close_from s n p)).
              eapply for_All_E. eapply for_ByHyp. autorewrite with simplication_hints. done.
      }
      eapply cut_one'.
      { rewrite <- Deduction_theorem. eapply claim1; try done. }
      rewrite subst1_nice. eapply for_All_E. eapply for_All_I.
      { intros q q_in. autorewrite with simplication_hints in q_in. destruct q_in as [-> | []]. simpl. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. done. }
      eapply cut_one' with (A := close_from 0 n p).
      { rewrite <- Deduction_theorem. eapply IH; try done. }
      rewrite <- subst1_id with (x := n) (p := close_from 0 n p) at 2. rewrite subst1_nice.
      eapply for_All_E. eapply for_ByHyp. autorewrite with simplication_hints. done.
Qed.

Lemma subst_frm_close_frm_1 (n : nat) (p : frm L) (m : nat) (s : subst L)
  (BOUND : forall y, y < n -> forall z : ivar, is_free_in_trm z (s (m + y)) = true -> z < m)
  : E.empty \proves Imp_frm (close_from m n p) (subst_frm (fun x : ivar => if le_lt_dec m x then if le_lt_dec (m + n) x then Var_trm x else s x else Var_trm x) p).
Proof.
  revert p m s BOUND. induction n as [ | n IH]; simpl; i.
  - clear BOUND. eapply for_Imp_I. eapply cut_one' with (A := subst_frm nil_subst p).
    + eapply for_ByHyp. autorewrite with simplication_hints. left. eapply alpha_equiv_inv_subst.
      rewrite subst_nil_frm. reflexivity.
      intros u u_free. rewrite Nat.add_0_r. destruct (le_lt_dec m u) as [LE1 | LT1]; try done.
    + rewrite subst_nil_frm. 2: done. eapply for_ByHyp. autorewrite with simplication_hints. done.
  - set (s1 := fun x : ivar => if le_lt_dec m x then if le_lt_dec (m + n) x then Var_trm x else s x else Var_trm x).
    set (s2 := fun x : ivar => if le_lt_dec m x then if le_lt_dec (m + S n) x then Var_trm x else s x else Var_trm x).
    assert (ALPHA : subst1 (m + n) (s (m + n)) (subst_frm s1 p) ≡ subst_frm s2 p).
    { rewrite subst1_nice. rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
      intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst, s1, s2.
      destruct (le_lt_dec m u) as [LE1 | LT1].
      - destruct (le_lt_dec (m + n) u) as [LE2 | LT2], (le_lt_dec (m + S n) u) as [LE3 | LT3]; try done.
        + rewrite subst_trm_unfold. destruct (eq_dec u (m + n)) as [EQ4 | NE4]; try done.
        + rewrite subst_trm_unfold. destruct (eq_dec u (m + n)) as [EQ4 | NE4]; try done.
        + eapply subst_nil_trm. intros y y_free. assert (LT : u - m < S n) by lia.
          pose proof (BOUND (u - m) LT y) as claim1. replace (m + (u - m)) with u in claim1 by lia. specialize (claim1 y_free).
          destruct (eq_dec y (m + n)) as [EQ4 | NE4]; try done.
      - rewrite subst_trm_unfold. destruct (eq_dec u (m + n)) as [EQ2 | NE2]; try done.
    }
    rewrite <- ALPHA. eapply for_Imp_I. rewrite subst1_nice. eapply for_All_E.
    clear s2 ALPHA. unfold s1. remember (m + n) as y eqn: H_y in *. fold s1. eapply for_All_I.
    { intros q q_in. autorewrite with simplication_hints in q_in. destruct q_in as [-> | []]. simpl. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. done. }
    eapply cut_one' with (A := close_from m n p).
    { unfold s1. rewrite <- Deduction_theorem. subst y. eapply IH; firstorder. }
    { rewrite <- subst1_id with (x := y) (p := close_from m n p) at 2. rewrite subst1_nice. eapply for_All_E. eapply for_ByHyp. autorewrite with simplication_hints. done. }
Qed.

Lemma subst_frm_close_frm (n : nat) (s : subst L) (p : frm L)
  : E.empty \proves Imp_frm (close_from 0 n p) (subst_frm (fun x : ivar => if le_lt_dec n x then Var_trm x else s x) p).
Proof.
  assert (BOUND : exists x, forall y : nat, y < n -> maxs (fvs_trm (s y)) <= x).
  { clear p. induction n as [ | n [x IH]]; simpl; i.
    - exists 0. lia.
    - exists (max x (maxs (fvs_trm (s n)))). intros y LT.
      assert (y = n \/ y < n) as [H | H] by lia.
      + subst y. enough (WTS : maxs (fvs_trm (s n)) <= maxs (fvs_trm (s n))) by lia. done.
      + transitivity x.
        * eapply IH. done.
        * done.
  }
  destruct BOUND as [x BOUND]. set (r := max n (1 + max x (maxs (fvs_frm p)))).
  set (p' := subst_frm (fun z : ivar => if le_lt_dec n z then Var_trm z else Var_trm (r + z)) p).
  set (s' := fun z : ivar => s (z - r)).
  eapply for_Imp_I. eapply cut_one' with (A := subst_frm (fun z : ivar => if le_lt_dec r z then if le_lt_dec (r + n) z then Var_trm z else s' z else Var_trm z) p').
  - eapply proves_alpha_proves.
    + eapply for_ByHyp. autorewrite with simplication_hints. left. reflexivity.
    + unfold p'. rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
      intros u u_free. unfold subst_compose. destruct (le_lt_dec n u) as [LE1 | LT1].
      * rewrite subst_trm_unfold. destruct (le_lt_dec r u) as [LE2 | LT2], (le_lt_dec (r + n) x) as [LE3 | LT3]; try done.
        assert (claim1 : u > last_ivar_frm p) by now unfold last_ivar_frm; lia. pose proof (@last_ivar_frm_gt L p u claim1). done.
      * rewrite subst_trm_unfold. destruct (le_lt_dec r (r + u)) as [LE2 | LT2], (le_lt_dec (r + n) (r + u)) as [LE3 | LT3]; try done.
        unfold s'. f_equal. done.
  - assert (BOUND' : forall y : nat, y < n -> forall z : ivar, is_free_in_trm z (s' (r + y)) = true -> z < r).
    { intros y LT z FREE. unfold s' in FREE. replace (r + y - r) with y in FREE by lia.
      apply BOUND in LT. pose proof (@last_ivar_trm_gt L (s y) z) as claim1. unfold last_ivar_trm in claim1. rewrite FREE in claim1. lia.
    }
    pose proof (subst_frm_close_frm_1 n p' r s' BOUND') as claim1. rewrite Deduction_theorem in claim1.
    eapply cut_one'. exact claim1. unfold p'. rewrite <- Deduction_theorem. eapply lift_close_from. lia.
    intros z FREE. pose proof (@last_ivar_frm_gt L p z) as claim2. rewrite FREE in claim2. unfold last_ivar_frm in claim2. done.
Qed.

End SUBST.

Section EQUATIONS. (* Reference: "https://github.com/princeton-vl/CoqGym/blob/master/coq_projects/goedel/folLogic3.v" *)

Lemma proves_reflexivity (Gamma : ensemble (frm L)) (t1 : trm L)
  : Gamma \proves Eqn_frm t1 t1.
Proof.
  set (s := fun z : ivar =>
    match z with
    | 0 => t1
    | _ => Var_trm z
    end
  ).
  eapply extend_proves with (Gamma := E.empty). done.
  replace (Eqn_frm t1 t1) with (subst_frm s (Eqn_frm (Var_trm 0) (Var_trm 0))) by reflexivity.
  pose proof (subst_frm_close_frm 1 s (Eqn_frm (Var_trm 0) (Var_trm 0))) as claim1.
  rewrite Deduction_theorem in claim1. eapply cut_one'. eapply claim1.
  simpl. eapply extend_proves with (Gamma := E.empty). done. eapply for_All_I.
  { intros q q_in. autorewrite with simplication_hints in q_in. done. }
  exists []. split.
  { intros q q_in. done. }
  econstructor. eapply EQN_REFL.
Qed.

Lemma proves_symmetry (Gamma : ensemble (frm L)) (t1 : trm L) (t2 : trm L)
  (PROVE1 : Gamma \proves Eqn_frm t1 t2)
  : Gamma \proves Eqn_frm t2 t1.
Proof.
  set (s := fun z : ivar =>
    match z with
    | 0 => t1
    | 1 => t2
    | _ => Var_trm z
    end
  ).
  eapply cut_one'. 2: exact PROVE1. rewrite <- Deduction_theorem.
  replace (Imp_frm (Eqn_frm t1 t2) (Eqn_frm t2 t1)) with (subst_frm s (Imp_frm (Eqn_frm (Var_trm 0) (Var_trm 1)) (Eqn_frm (Var_trm 1) (Var_trm 0)))) by reflexivity.
  pose proof (subst_frm_close_frm 2 s (Imp_frm (Eqn_frm (Var_trm 0) (Var_trm 1)) (Eqn_frm (Var_trm 1) (Var_trm 0)))) as claim1.
  rewrite Deduction_theorem in claim1. eapply cut_one'. eapply claim1.
  simpl. eapply for_All_I.
  { intros q q_in. autorewrite with simplication_hints in q_in. done. }
  eapply for_All_I.
  { intros q q_in. autorewrite with simplication_hints in q_in. done. }
  exists []. split.
  { intros q q_in. done. }
  econstructor. eapply EQN_SYM.
Qed.

Lemma proves_transitivity (Gamma : ensemble (frm L)) (t1 : trm L) (t2 : trm L) (t3 : trm L)
  (PROVE1 : Gamma \proves Eqn_frm t1 t2)
  (PROVE2 : Gamma \proves Eqn_frm t2 t3)
  : Gamma \proves Eqn_frm t1 t3.
Proof.
  set (s := fun z : ivar =>
    match z with
    | 0 => t1
    | 1 => t2
    | 2 => t3
    | _ => Var_trm z
    end
  ).
  eapply for_Imp_E. 2: exact PROVE2. eapply cut_one'. 2: exact PROVE1. rewrite <- Deduction_theorem.
  replace (Imp_frm (Eqn_frm t1 t2) (Imp_frm (Eqn_frm t2 t3) (Eqn_frm t1 t3))) with (subst_frm s (Imp_frm (Eqn_frm (Var_trm 0) (Var_trm 1)) (Imp_frm (Eqn_frm (Var_trm 1) (Var_trm 2)) (Eqn_frm (Var_trm 0) (Var_trm 2))))) by reflexivity.
  pose proof (subst_frm_close_frm 3 s (Imp_frm (Eqn_frm (Var_trm 0) (Var_trm 1)) (Imp_frm (Eqn_frm (Var_trm 1) (Var_trm 2)) (Eqn_frm (Var_trm 0) (Var_trm 2))))) as claim1.
  rewrite Deduction_theorem in claim1. eapply cut_one'. eapply claim1.
  simpl. eapply for_All_I.
  { intros q q_in. autorewrite with simplication_hints in q_in. done. }
  eapply for_All_I.
  { intros q q_in. autorewrite with simplication_hints in q_in. done. }
  eapply for_All_I.
  { intros q q_in. autorewrite with simplication_hints in q_in. done. }
  exists []. split.
  { intros q q_in. done. }
  econstructor. eapply EQN_TRANS.
Qed.

Fixpoint pairwise_equal {n : nat} (Gamma : ensemble (frm L)) {struct n} : trms L n -> trms L n -> Prop :=
  match n with
  | O => fun ts => fun ts' => True
  | S n' => fun ts => fun ts' => Gamma \proves (Eqn_frm (head ts) (head ts')) /\ pairwise_equal (n := n') Gamma (tail ts) (tail ts')
  end.

Definition trms_map : forall n, trms L n -> trms L n -> subst L :=
  nat_rec (fun n => trms L n -> trms L n -> ivar -> trm L) (fun _ => fun _ => fun z => Var_trm z) (fun n => fun ACC => fun ts => fun ts' => fun z => if eq_dec z (n + n) then head ts else if eq_dec z (S (n + n)) then head ts' else ACC (tail ts) (tail ts') z).

Lemma varcouples_subst_fst n (ts : trms L n) (ts' : trms L n)
  : subst_trms (trms_map n ts ts') (fst (varcouples n)) = ts.
Proof.
  revert n ts ts'. induction n as [ | n IH].
  - intros ts. pattern ts. revert ts. eapply trms_case0.
    intros ts'. pattern ts'. revert ts'. eapply trms_case0.
    reflexivity.
  - intros ts. pattern ts. revert ts. eapply trms_caseS. intros t ts.
    intros ts'. pattern ts'. revert ts'. eapply trms_caseS. intros t' ts'.
    assert (claim1 : forall z, forall FREE : is_free_in_trms z (fst (varcouples n)) = true, z < n + n).
    { clear IH t t' ts ts'. induction n as [ | n IH]; simpl; ii.
      - inv FREE.
      - simpl in FREE. destruct (varcouples n) as [FST SND] eqn: EQN.
        simpl in FREE, IH. rewrite is_free_in_trms_unfold in FREE.
        rewrite orb_true_iff in FREE. destruct FREE as [FREE | FREE].
        + rewrite is_free_in_trm_unfold in FREE. rewrite Nat.eqb_eq in FREE. lia.
        + apply IH in FREE. lia.
    }
    simpl. destruct (varcouples n) as [FST SND] eqn: EQN. simpl in *.
    unfold head, tail. simpl. rewrite subst_trms_unfold. simpl. f_equal.
    + rewrite subst_trm_unfold. destruct eq_dec as [EQ | NE]; done.
    + rewrite <- IH with (ts' := ts'). eapply equiv_subst_in_trms_implies_subst_trms_same.
      intros z FREE. destruct (eq_dec z (n + n)) as [EQ1 | NE1].
      { apply claim1 in FREE. done. }
      destruct (eq_dec z (S (n + n))) as [EQ2 | NE2].
      { apply claim1 in FREE. done. }
      { reflexivity. }
Qed.

Lemma varcouples_subst_snd n (ts : trms L n) (ts' : trms L n)
  : subst_trms (trms_map n ts ts') (snd (varcouples n)) = ts'.
Proof.
  revert n ts ts'. induction n as [ | n IH].
  - intros ts. pattern ts. revert ts. eapply trms_case0.
    intros ts'. pattern ts'. revert ts'. eapply trms_case0.
    reflexivity.
  - intros ts. pattern ts. revert ts. eapply trms_caseS. intros t ts.
    intros ts'. pattern ts'. revert ts'. eapply trms_caseS. intros t' ts'.
    assert (claim1 : forall z, forall FREE : is_free_in_trms z (snd (varcouples n)) = true, z < n + n).
    { clear IH t t' ts ts'. induction n as [ | n IH]; simpl; ii.
      - inv FREE.
      - simpl in FREE. destruct (varcouples n) as [FST SND] eqn: EQN.
        simpl in FREE, IH. rewrite is_free_in_trms_unfold in FREE.
        rewrite orb_true_iff in FREE. destruct FREE as [FREE | FREE].
        + rewrite is_free_in_trm_unfold in FREE. rewrite Nat.eqb_eq in FREE. lia.
        + apply IH in FREE. lia.
    }
    simpl. destruct (varcouples n) as [FST SND] eqn: EQN. simpl in *.
    unfold head, tail. simpl. rewrite subst_trms_unfold. simpl. f_equal.
    + rewrite subst_trm_unfold. destruct eq_dec as [EQ | NE]. done. destruct eq_dec; done.
    + rewrite <- IH with (ts := ts). eapply equiv_subst_in_trms_implies_subst_trms_same.
      intros z FREE. destruct (eq_dec z (n + n)) as [EQ1 | NE1].
      { apply claim1 in FREE. done. }
      destruct (eq_dec z (S (n + n))) as [EQ2 | NE2].
      { apply claim1 in FREE. done. }
      { reflexivity. }
Qed.

Lemma add_pairwise_equals n (ts : trms L n) (ts' : trms L n) (s : subst L) (Gamma : ensemble (frm L)) (p : frm L)
  (EQs : pairwise_equal Gamma ts ts')
  (BOUND : forall z : ivar, z < n + n -> s z = trms_map n ts ts' z)
  (PROVE : Gamma \proves subst_frm s (nat_rec (fun _ => frm L) p (fun m : nat => fun ACC : frm L => Imp_frm (Eqn_frm (Var_trm (m + m)) (Var_trm (S (m + m)))) ACC) n))
  : Gamma \proves subst_frm s p.
Proof.
  revert s Gamma p EQs BOUND PROVE. trms_ind2 ts ts'; simpl.
  - i. exact PROVE.
  - unfold head, tail. simpl. i. destruct EQs as [PROVE' EQs']. eapply IH with (ts' := ts'); trivial.
    + ii. rewrite BOUND. 2: lia. unfold eq_dec, ivar_hasEqDec. destruct (Nat.eq_dec z (n + n)) as [EQ1 | NE1], (Nat.eq_dec z (S (n + n))) as [EQ2 | NE2]; try done.
    + eapply for_Imp_E. 1: exact PROVE. exploit (BOUND (n + n)); [lia | intros H1]. exploit (BOUND (S (n + n))); [lia | intros H2].
      unfold eq_dec, ivar_hasEqDec in *. destruct (Nat.eq_dec (n + n) (n + n)) as [EQ1 | NE1]; try done.
      destruct (Nat.eq_dec (n + n) (S (n + n))) as [EQ2 | NE2]; try done. destruct (Nat.eq_dec (S (n + n)) (S (n + n))) as [EQ3 | NE3]; try done.
      destruct (Nat.eq_dec (S (n + n)) (n + n)) as [EQ4 | NE4]; try done.
Qed.

#[local] Opaque le_lt_dec.

#[local] Tactic Notation "des" :=
  unfold eq_dec, ivar_hasEqDec; lazymatch goal with [ |- context[ Nat.eq_dec ?P ?Q ] ] => destruct (Nat.eq_dec P Q); try lia | [ |- context[ le_lt_dec ?P ?Q ] ] => destruct (le_lt_dec P Q); try lia end.

Lemma Fun_eqAxm_free_vars (z : ivar) (f : L.(function_symbols))
  (n := L.(function_arity_table) f)
  : is_free_in_frm z (Fun_eqAxm f) = true <-> z < n + n.
Proof.
  unfold Fun_eqAxm. fold n. remember (fun lhs => fun rhs => Eqn_frm (Fun_trm f lhs) (Fun_trm f rhs)) as phi eqn: H_phi.
  fold n in phi, H_phi. rewrite <- H_phi. i. destruct (varcouples n) as [xs ys] eqn: H_OBS. simpl in *.
  assert (claim1 : is_free_in_frm z (phi xs ys) = is_free_in_trms z xs || is_free_in_trms z ys).
  { subst phi. i. rewrite is_free_in_frm_unfold. do 2 rewrite is_free_in_trm_unfold. done. }
  clear H_phi. subst n. revert z phi claim1 H_OBS. trms_ind2 xs ys; simpl; i.
  - rewrite claim1. rewrite is_free_in_trms_unfold. done.
  - do 2 rewrite is_free_in_trm_unfold. obs_eqb (n + n) z; obs_eqb (S (n + n)) z; simpl; try lia.
    transitivity (z < n + n). 2: lia. destruct (varcouples n) as [xs' ys'] eqn: H_OBS'. simpl in *.
    pose proof (claim2 := f_equal fst H_OBS). pose proof (claim3 := f_equal snd H_OBS). simpl in *.
    pose proof (claim4 := f_equal head claim2). pose proof (claim5 := f_equal head claim3). unfold head in claim4, claim5. simpl in *.
    pose proof (claim6 := f_equal tail claim2). pose proof (claim7 := f_equal tail claim3). unfold tail in claim6, claim7. simpl in *.
    subst xs' ys' t t'. clear claim2 claim3.
    eapply IH with (ys := ys) (phi := fun lhs => fun rhs => phi (S_trms _ (Var_trm (n + n)) lhs) (S_trms _ (Var_trm (S (n + n))) rhs)); trivial.
    rewrite claim1. rewrite is_free_in_trms_unfold with (ts := S_trms _ _ xs). rewrite is_free_in_trms_unfold with (ts := S_trms _ _ ys).
    do 2 rewrite is_free_in_trm_unfold with (t := Var_trm _). obs_eqb (n + n) z; obs_eqb (S (n + n)) z; try done.
Qed.

Lemma Rel_eqAxm_free_vars (z : ivar) (R : L.(relation_symbols))
  (n := L.(relation_arity_table) R)
  : is_free_in_frm z (Rel_eqAxm R) = true <-> z < n + n.
Proof.
  unfold Rel_eqAxm. fold n. remember (fun lhs => fun rhs => Imp_frm (Rel_frm R lhs) (Rel_frm R rhs)) as phi eqn: H_phi.
  fold n in phi, H_phi. rewrite <- H_phi. i. destruct (varcouples n) as [xs ys] eqn: H_OBS. simpl in *.
  assert (claim1 : is_free_in_frm z (phi xs ys) = is_free_in_trms z xs || is_free_in_trms z ys).
  { subst phi. i. rewrite is_free_in_frm_unfold. do 2 rewrite is_free_in_frm_unfold. done. }
  clear H_phi. subst n. revert z phi claim1 H_OBS. trms_ind2 xs ys; simpl; i.
  - rewrite claim1. rewrite is_free_in_trms_unfold. done.
  - do 2 rewrite is_free_in_trm_unfold. obs_eqb (n + n) z; obs_eqb (S (n + n)) z; simpl; try lia.
    transitivity (z < n + n). 2: lia. destruct (varcouples n) as [xs' ys'] eqn: H_OBS'. simpl in *.
    pose proof (claim2 := f_equal fst H_OBS). pose proof (claim3 := f_equal snd H_OBS). simpl in *.
    pose proof (claim4 := f_equal head claim2). pose proof (claim5 := f_equal head claim3). unfold head in claim4, claim5. simpl in *.
    pose proof (claim6 := f_equal tail claim2). pose proof (claim7 := f_equal tail claim3). unfold tail in claim6, claim7. simpl in *.
    subst xs' ys' t t'. clear claim2 claim3.
    eapply IH with (ys := ys) (phi := fun lhs => fun rhs => phi (S_trms _ (Var_trm (n + n)) lhs) (S_trms _ (Var_trm (S (n + n))) rhs)); trivial.
    rewrite claim1. rewrite is_free_in_trms_unfold with (ts := S_trms _ _ xs). rewrite is_free_in_trms_unfold with (ts := S_trms _ _ ys).
    do 2 rewrite is_free_in_trm_unfold with (t := Var_trm _). obs_eqb (n + n) z; obs_eqb (S (n + n)) z; try done.
Qed.

Lemma proves_eqn_fun (Gamma : ensemble (frm L)) (f : L.(function_symbols)) ts ts'
  (PROVE : pairwise_equal Gamma ts ts')
  : Gamma \proves Eqn_frm (Fun_trm f ts) (Fun_trm f ts').
Proof.
  rewrite <- varcouples_subst_fst with (ts := ts) (ts' := ts') at 1.
  rewrite <- varcouples_subst_snd with (ts := ts) (ts' := ts') at 2.
  set (s := trms_map _ _ _). set (lhs := fst _). set (rhs := snd _).
  change (Gamma \proves subst_frm (trms_map (L.(function_arity_table) f) ts ts') (Eqn_frm (Fun_trm f lhs) (Fun_trm f rhs))).
  eapply add_pairwise_equals with (n := L.(function_arity_table) f) (ts := ts) (ts' := ts'); trivial.
  rename lhs into xs, rhs into ys. fold s. set (n := L.(function_arity_table) f).
  eapply extend_proves with (Gamma := E.empty). done. eapply cut_one' with (A := close_from 0 (n + n) (Fun_eqAxm f)).
  - pose proof (subst_frm_close_frm (n + n) s (Fun_eqAxm f)) as claim1. rewrite Deduction_theorem in claim1.
    eapply cut_one'. 2: exact claim1. clear claim1. set (P := subst_frm _ (Fun_eqAxm f)). set (Q := subst_frm s _).
    enough (FACT : P = Q) by now rewrite FACT; eapply for_ByHyp; rewrite E.in_insert_iff; done.
    subst P Q. transitivity (subst_frm s (Fun_eqAxm f)).
    + eapply equiv_subst_in_frm_implies_subst_frm_same. clear. ii.
      enough (LT : z < n + n) by now des; done. rewrite Fun_eqAxm_free_vars in FREE. done.
    + f_equal. unfold Fun_eqAxm. remember (fun lhs => fun rhs => Eqn_frm (Fun_trm f lhs) (Fun_trm f rhs)) as phi eqn: H_phi.
      replace (Eqn_frm (Fun_trm f xs) (Fun_trm f ys)) with (phi xs ys) by now subst phi.
      clear. subst xs ys n. revert phi. induction (L.(function_arity_table) f) as [ | n IH]; simpl; i.
      * reflexivity.
      * specialize IH with (phi := fun ts => fun ts' => phi (S_trms _ (Var_trm (n + n)) ts) (S_trms _ (Var_trm (S (n + n))) ts')).
        simpl in *. destruct (varcouples n) as [xs ys] eqn: H_OBS. simpl in *. reflexivity.
  - induction (n + n) as [ | m IH]; simpl; i.
    + exists []. split. intros ?. done. econstructor. eapply EQN_FUN.
    + eapply for_All_I; done.
Qed.

Lemma proves_eqn_rel (Gamma : ensemble (frm L)) (R : L.(relation_symbols)) ts ts'
  (PROVE : pairwise_equal Gamma ts ts')
  : Gamma \proves Imp_frm (Rel_frm R ts) (Rel_frm R ts').
Proof.
  rewrite <- varcouples_subst_fst with (ts := ts) (ts' := ts') at 1.
  rewrite <- varcouples_subst_snd with (ts := ts) (ts' := ts') at 2.
  set (s := trms_map _ _ _). set (lhs := fst _). set (rhs := snd _).
  change (Gamma \proves subst_frm (trms_map (L.(relation_arity_table) R) ts ts') (Imp_frm (Rel_frm R lhs) (Rel_frm R rhs))).
  eapply add_pairwise_equals with (n := L.(relation_arity_table) R) (ts := ts) (ts' := ts'); trivial.
  rename lhs into xs, rhs into ys. fold s. set (n := L.(relation_arity_table) R).
  eapply extend_proves with (Gamma := E.empty). done. eapply cut_one' with (A := close_from 0 (n + n) (Rel_eqAxm R)).
  - pose proof (subst_frm_close_frm (n + n) s (Rel_eqAxm R)) as claim1. rewrite Deduction_theorem in claim1.
    eapply cut_one'. 2: exact claim1. clear claim1. set (P := subst_frm _ (Rel_eqAxm R)). set (Q := subst_frm s _).
    enough (FACT : P = Q) by now rewrite FACT; eapply for_ByHyp; rewrite E.in_insert_iff; done.
    subst P Q. transitivity (subst_frm s (Rel_eqAxm R)).
    + eapply equiv_subst_in_frm_implies_subst_frm_same. clear. ii.
      enough (LT : z < n + n) by now des; done. rewrite Rel_eqAxm_free_vars in FREE. done.
    + f_equal. unfold Rel_eqAxm. remember (fun lhs => fun rhs => Imp_frm (Rel_frm R lhs) (Rel_frm R rhs)) as phi eqn: H_phi.
      replace (Imp_frm (Rel_frm R xs) (Rel_frm R ys)) with (phi xs ys) by now subst phi.
      clear. subst xs ys n. revert phi. induction (L.(relation_arity_table) R) as [ | n IH]; simpl; i.
      * reflexivity.
      * specialize IH with (phi := fun ts => fun ts' => phi (S_trms _ (Var_trm (n + n)) ts) (S_trms _ (Var_trm (S (n + n))) ts')).
        simpl in *. destruct (varcouples n) as [xs ys] eqn: H_OBS. simpl in *. reflexivity.
  - induction (n + n) as [ | m IH]; simpl; i.
    + exists []. split. intros ?. done. econstructor. eapply EQN_REL.
    + eapply for_All_I; done.
Qed.

Lemma proves_eqn_trm (t : trm L) (lhs : trm L) (rhs : trm L) (Gamma : ensemble (frm L)) (y : ivar)
  (PROVE : Gamma \proves Eqn_frm lhs rhs)
  : Gamma \proves Eqn_frm (subst_trm (one_subst y lhs) t) (subst_trm (one_subst y rhs) t)
with proves_eqn_trms n (ts : trms L n) (lhs : trm L) (rhs : trm L) (Gamma : ensemble (frm L)) (y : ivar)
  (PROVE : Gamma \proves Eqn_frm lhs rhs)
  : pairwise_equal Gamma (subst_trms (one_subst y lhs) ts) (subst_trms (one_subst y rhs) ts).
Proof.
  - revert lhs rhs Gamma y PROVE. trm_ind t; simpl; i.
    + do 2 rewrite subst_trm_unfold. unfold one_subst, cons_subst, nil_subst. unfold eq_dec, ivar_hasEqDec. des.
      * exact PROVE.
      * eapply proves_reflexivity.
    + do 2 rewrite subst_trm_unfold. eapply proves_eqn_fun. eapply proves_eqn_trms. exact PROVE.
    + do 2 rewrite subst_trm_unfold. eapply proves_reflexivity.
  - revert lhs rhs Gamma y PROVE. trms_ind ts; simpl; i.
    + exact I.
    + do 2 rewrite subst_trms_unfold with (ts := S_trms _ _ _). unfold head, tail. simpl. split.
      * eapply proves_eqn_trm. exact PROVE.
      * eapply proves_eqn_trms. exact PROVE.
Qed.

Lemma proves_eqn_frm (p : frm L) (lhs : trm L) (rhs : trm L) (Gamma : ensemble (frm L)) (y : ivar)
  (PROVE : Gamma \proves Eqn_frm lhs rhs)
  : Gamma \proves Imp_frm (subst_frm (one_subst y lhs) p) (subst_frm (one_subst y rhs) p).
Proof.
  revert p lhs rhs Gamma y PROVE.
  enough (WTS : forall p, forall lhs, forall rhs, forall Gamma, forall x,
    Gamma \proves Eqn_frm lhs rhs ->
    Gamma \proves Imp_frm (subst1 x lhs p) (subst1 x rhs p) /\ Gamma \proves Imp_frm (subst1 x rhs p) (subst1 x lhs p)
  ).
  { ii. apply WTS with (x := y) (p := p) in PROVE. destruct PROVE as [PROVE PROVE'].
    do 2 rewrite subst1_nice in PROVE. exact PROVE.
  }
  intros p. pattern p. revert p. eapply frm_depth_lt_ind; intros p IH lhs rhs Gamma x PROVE; destruct p as [R ts | t1 t2 | p1 | p1 p2 | y p1].
  - split; (do 2 rewrite subst1_nice); (do 2 rewrite subst_frm_unfold with (p := Rel_frm _ _)); eapply proves_eqn_rel; eapply proves_eqn_trms; trivial; eapply proves_symmetry; trivial.
  - split; (do 2 rewrite subst1_nice); (do 2 rewrite subst_frm_unfold with (p := Eqn_frm _ _)).
    + eapply for_Imp_I. pose proof (proves_eqn_trm t1 lhs rhs Gamma x PROVE) as claim1. pose proof (proves_eqn_trm t2 lhs rhs Gamma x PROVE) as claim2.
      eapply proves_transitivity.
      { eapply proves_symmetry. eapply extend_proves with (Gamma := Gamma).
        - intros ?. done.
        - exact claim1.
      }
      eapply proves_transitivity.
      { eapply for_ByHyp. left. reflexivity. }
      eapply extend_proves with (Gamma := Gamma).
      { intros ?. done. }
      exact claim2.
    + eapply for_Imp_I. pose proof (proves_eqn_trm t1 lhs rhs Gamma x PROVE) as claim1. pose proof (proves_eqn_trm t2 lhs rhs Gamma x PROVE) as claim2.
      eapply proves_transitivity.
      { eapply proves_symmetry. eapply extend_proves with (Gamma := Gamma).
        - intros ?. done.
        - eapply proves_symmetry. exact claim1.
      }
      eapply proves_transitivity.
      { eapply for_ByHyp. left. reflexivity. }
      eapply extend_proves with (Gamma := Gamma).
      { intros ?. done. }
      eapply proves_symmetry. exact claim2.
  - do 2 rewrite subst1_unfold with (p := Neg_frm _). apply IH with (x := x) (p' := p1) in PROVE. 2: done. destruct PROVE as [PROVE PROVE']. split.
    + eapply for_CP1. done.
    + eapply for_CP1. done.
  - do 2 rewrite subst1_unfold with (p := Imp_frm _ _). pose proof (PROVE' := PROVE). apply IH with (x := x) (p' := p1) in PROVE. 2: simpl; done. apply IH with (x := x) (p' := p2) in PROVE'. 2: simpl; done. destruct PROVE as [PROVE1 PROVE2], PROVE' as [PROVE3 PROVE4]. split.
    + eapply for_Imp_I. eapply for_Imp_I. eapply for_Imp_E.
      { eapply extend_proves with (Gamma := Gamma).
        - intros ?. do 2 done.
        - exact PROVE3.
      }
      eapply for_Imp_E.
      { eapply for_ByHyp. right. left. reflexivity. }
      eapply for_Imp_E.
      { eapply extend_proves with (Gamma := Gamma).
        - intros ?. do 2 done.
        - exact PROVE2.
      }
      eapply for_ByHyp. left. reflexivity.
    + eapply for_Imp_I. eapply for_Imp_I. eapply for_Imp_E.
      { eapply extend_proves with (Gamma := Gamma).
        - intros ?. do 2 done.
        - exact PROVE4.
      }
      eapply for_Imp_E.
      { eapply for_ByHyp. right. left. reflexivity. }
      eapply for_Imp_E.
      { eapply extend_proves with (Gamma := Gamma).
        - intros ?. do 2 done.
        - exact PROVE1.
      }
      eapply for_ByHyp. left. reflexivity.
  - do 2 rewrite subst1_unfold with (p := All_frm _ _).
    pose proof (fresh_var_is_not_free_in_frm x lhs p1). pose proof (fresh_var_is_not_free_in_frm x rhs p1).
    pose proof (fresh_var_is_not_free_in_trm x lhs p1). pose proof (fresh_var_is_not_free_in_trm x rhs p1).
    pose proof (fresh_var_ne_x x lhs p1). pose proof (fresh_var_ne_x x rhs p1).
    set (y1 := fresh_var x lhs p1) in *. set (y2 := fresh_var x rhs p1) in *. simpl. destruct (eq_dec x y) as [EQ | NE].
    { split; eapply for_Imp_I; eapply for_ByHyp; left; reflexivity. }
    pose proof (IH p1 (le_n _)) as claim1. specialize claim1 with (lhs := lhs) (rhs := rhs) (Gamma := Gamma). specialize (claim1 x PROVE).
    destruct claim1 as [PROVE1 PROVE2]. destruct (is_free_in_trm y lhs) as [ | ] eqn: H_OBS1, (is_free_in_trm y rhs) as [ | ] eqn: H_OBS2.
    + rename lhs into t, rhs into t'. set (phi := fun z : ivar => All_frm z (subst1 x t (subst1 y (Var_trm z) p1))). set (phi' := fun z : ivar => All_frm z (subst1 x t' (subst1 y (Var_trm z) p1))).
      set (z := 1 + maxs ([x] ++ [y] ++ fvs_trm t ++ fvs_trm t' ++ fvs_frm p1)). fold (phi y1). fold (phi' y2). rename p1 into p. split.
      * eapply for_compose with (q := All_frm z (subst1 x t (subst1 y (Var_trm z) p))); cycle 1.
        { unfold phi. eapply extend_proves with (Gamma := E.empty). done. eapply for_compose with (q := All_frm z (subst1 y1 (Var_trm z) (subst1 x t (subst1 y (Var_trm y1) p)))); cycle 1.
          - rewrite subst1_nice with (x := y1) (t := Var_trm z). eapply rebind_All_frm_fwd.
            red. rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. pose proof (Nat.eq_dec z y1) as [? | ?]; [right | left]; trivial.
            eapply alpha_is_not_free_in_frm. do 2 rewrite subst1_nice. reflexivity. rewrite <- subst_compose_frm_spec. eapply frm_is_fresh_in_subst_iff.
            unfold frm_is_fresh_in_subst. s!. rewrite forallb_forall. intros u u_free. rewrite negb_true_iff. rewrite fv_is_free_in_frm in u_free.
            repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
            + subst u. eapply last_ivar_trm_gt. unfold z, last_ivar_trm. repeat rewrite maxs_app. done.
            + rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros ->.
              enough (CONTRA : is_free_in_frm z p = false) by done. eapply last_ivar_frm_gt. unfold z, last_ivar_frm. repeat rewrite maxs_app. done.
          - eapply for_Imp_E with (p := All_frm z (Imp_frm (subst1 y1 (Var_trm z) (subst1 x t (subst1 y (Var_trm y1) p))) (subst1 x t (subst1 y (Var_trm z) p)))).
            { exists []. split. intros ?. done!. econstructor. eapply FA3. }
            eapply for_All_I. done. eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
            repeat rewrite subst1_nice. repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
            intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + enough (CONTRA : z > x) by done. unfold z. repeat rewrite maxs_app. simpl; done.
            + eapply subst_nil_trm. subst u. rename u_free into FREE. intros u u_free. des. subst u. done. done.
            + subst u. done.
        }
        eapply for_compose with (q := All_frm z (subst1 x t' (subst1 y (Var_trm z) p))).
        { unfold phi'. eapply extend_proves with (Gamma := E.empty). done. eapply for_compose.
          - eapply rebind_All_frm_bwd with (x' := z). red. rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. pose proof (Nat.eq_dec z y2) as [? | ?]; [right | left]; trivial.
            eapply alpha_is_not_free_in_frm. do 2 rewrite subst1_nice. reflexivity. rewrite <- subst_compose_frm_spec. eapply frm_is_fresh_in_subst_iff.
            unfold frm_is_fresh_in_subst. rewrite forallb_forall. intros u u_free. unfold subst_compose, compose, one_subst, cons_subst, nil_subst. rewrite negb_true_iff.
            rewrite fv_is_free_in_frm in u_free. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
            + subst u. eapply last_ivar_trm_gt. unfold z, last_ivar_trm. repeat rewrite maxs_app. done.
            + rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros ->.
              enough (CONTRA : is_free_in_frm z p = false) by done. eapply last_ivar_frm_gt. unfold z, last_ivar_frm. repeat rewrite maxs_app. done.
          - rewrite <- subst1_nice. eapply for_Imp_E with (p := All_frm z (Imp_frm (subst1 x t' (subst1 y (Var_trm z) p)) (subst1 y2 (Var_trm z) (subst1 x t' (subst1 y (Var_trm y2) p))))).
            { exists []. split. intros ?. done. econstructor. eapply FA3. }
            eapply for_All_I. done. eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
            repeat rewrite subst1_nice. repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
            intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + enough (CONTRA : z > x) by done. unfold z. repeat rewrite maxs_app. simpl; done.
            + symmetry. eapply subst_nil_trm. subst u. rename u_free into FREE. intros u u_free. des. subst u. done. done.
            + subst u. done.
        }
        eapply cut_one'. 2: exact PROVE. eapply for_Imp_I. eapply for_All_I.
        { intros q q_in; autorewrite with simplication_hints in q_in; destruct q_in as [-> | [-> | []]].
          - rewrite is_free_in_frm_unfold; rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq; done.
          - rewrite is_free_in_frm_unfold; rewrite orb_false_iff. split; eapply last_ivar_trm_gt; unfold z, last_ivar_trm; repeat rewrite maxs_app; done.
        }
        pose proof (IH (subst1 y (Var_trm z) p)) as claim1. rewrite subst1_preserves_rank in claim1. specialize (claim1 (le_n _)).
        assert (PROVE' : (E.insert (All_frm z (subst1 x t (subst1 y (Var_trm z) p))) (E.insert (Eqn_frm t t') E.empty)) \proves Eqn_frm t t').
        { eapply for_ByHyp. right. left. reflexivity. }
        specialize claim1 with (lhs := t) (rhs := t'). destruct (claim1 _ x PROVE') as [PROVE3 PROVE4]. clear claim1.
        eapply for_Imp_E. exact PROVE3. eapply cut_one' with (A := All_frm z (subst1 x t (subst1 y (Var_trm z) p))).
        { rewrite <- subst1_id with (x := z) (p := subst1 x t (subst1 y (Var_trm z) p)) at 2. rewrite subst1_nice with (x := z) (t := Var_trm z). eapply for_All_E. eapply for_ByHyp. left. reflexivity. }
        { eapply for_ByHyp. left. reflexivity. }
    * rename phi into phi', phi' into phi. rename y1 into y2, y2 into y1, t into t', t' into t, PROVE1 into PROVE2, PROVE2 into PROVE1.
      eapply for_compose with (q := All_frm z (subst1 x t (subst1 y (Var_trm z) p))); cycle 1.
      { unfold phi. eapply extend_proves with (Gamma := E.empty). done. eapply for_compose with (q := All_frm z (subst1 y1 (Var_trm z) (subst1 x t (subst1 y (Var_trm y1) p)))); cycle 1.
        - rewrite subst1_nice with (x := y1) (t := Var_trm z). eapply rebind_All_frm_fwd.
          red. rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. pose proof (Nat.eq_dec z y1) as [? | ?]; [right | left]; trivial.
          eapply alpha_is_not_free_in_frm. do 2 rewrite subst1_nice. reflexivity. rewrite <- subst_compose_frm_spec. eapply frm_is_fresh_in_subst_iff.
          unfold frm_is_fresh_in_subst. rewrite forallb_forall. intros u u_free. unfold subst_compose, compose, one_subst, cons_subst, nil_subst. rewrite negb_true_iff.
          rewrite fv_is_free_in_frm in u_free. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
          + subst u. rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
          + subst u. eapply last_ivar_trm_gt. unfold z, last_ivar_trm. repeat rewrite maxs_app. done.
          + rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros ->.
            enough (CONTRA : is_free_in_frm z p = false) by done. eapply last_ivar_frm_gt. unfold z, last_ivar_frm. repeat rewrite maxs_app. done.
        - eapply for_Imp_E with (p := All_frm z (Imp_frm (subst1 y1 (Var_trm z) (subst1 x t (subst1 y (Var_trm y1) p))) (subst1 x t (subst1 y (Var_trm z) p)))).
          { exists []. split. intros ?. done. econstructor. eapply FA3. }
          eapply for_All_I. done. eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
          repeat rewrite subst1_nice. repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
          intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
          + enough (CONTRA : z > x) by done. unfold z. repeat rewrite maxs_app. simpl; done.
          + eapply subst_nil_trm. subst u. rename u_free into FREE. intros u u_free. des. subst u. done. done.
          + subst u. done.
      }
      eapply for_compose with (q := All_frm z (subst1 x t' (subst1 y (Var_trm z) p))).
      { unfold phi'. eapply extend_proves with (Gamma := E.empty). done. eapply for_compose.
        - eapply rebind_All_frm_bwd with (x' := z). red. rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. pose proof (Nat.eq_dec z y2) as [? | ?]; [right | left]; trivial.
          eapply alpha_is_not_free_in_frm. do 2 rewrite subst1_nice. reflexivity. rewrite <- subst_compose_frm_spec. eapply frm_is_fresh_in_subst_iff.
          unfold frm_is_fresh_in_subst. rewrite forallb_forall. intros u u_free. unfold subst_compose, compose, one_subst, cons_subst, nil_subst. rewrite negb_true_iff.
          rewrite fv_is_free_in_frm in u_free. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
          + subst u. rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
          + subst u. eapply last_ivar_trm_gt. unfold z, last_ivar_trm. repeat rewrite maxs_app. done.
          + rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros ->.
            enough (CONTRA : is_free_in_frm z p = false) by done. eapply last_ivar_frm_gt. unfold z, last_ivar_frm. repeat rewrite maxs_app. done.
        - rewrite <- subst1_nice. eapply for_Imp_E with (p := All_frm z (Imp_frm (subst1 x t' (subst1 y (Var_trm z) p)) (subst1 y2 (Var_trm z) (subst1 x t' (subst1 y (Var_trm y2) p))))).
          { exists []. split. intros ?. done. econstructor. eapply FA3. }
          eapply for_All_I. done. eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
          repeat rewrite subst1_nice. repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
          intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
          + enough (CONTRA : z > x) by done. unfold z. repeat rewrite maxs_app. simpl; done.
          + symmetry. eapply subst_nil_trm. subst u. rename u_free into FREE. intros u u_free. des. subst u. done. done.
          + subst u. done.
      }
      eapply cut_one'. 2: exact PROVE. eapply for_Imp_I. eapply for_All_I.
      { intros q q_in; autorewrite with simplication_hints in q_in; destruct q_in as [-> | [-> | []]].
        - rewrite is_free_in_frm_unfold; rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq; done.
        - rewrite is_free_in_frm_unfold; rewrite orb_false_iff. split; eapply last_ivar_trm_gt; unfold z, last_ivar_trm; repeat rewrite maxs_app; done.
      }
      pose proof (IH (subst1 y (Var_trm z) p)) as claim1. rewrite subst1_preserves_rank in claim1. specialize (claim1 (le_n _)). apply proves_symmetry in PROVE.
      assert (PROVE' : (E.insert (All_frm z (subst1 x t (subst1 y (Var_trm z) p))) (E.insert (Eqn_frm t' t) E.empty)) \proves Eqn_frm t' t).
      { eapply for_ByHyp. right. left. reflexivity. }
      specialize claim1 with (lhs := t') (rhs := t). destruct (claim1 _ x PROVE') as [PROVE3 PROVE4]. clear claim1.
      eapply for_Imp_E. exact PROVE4. eapply cut_one' with (A := All_frm z (subst1 x t (subst1 y (Var_trm z) p))).
      { rewrite <- subst1_id with (x := z) (p := subst1 x t (subst1 y (Var_trm z) p)) at 2. rewrite subst1_nice with (x := z) (t := Var_trm z). eapply for_All_E. eapply for_ByHyp. left. reflexivity. }
      { eapply for_ByHyp. left. reflexivity. }
    + rename lhs into t, rhs into t', p1 into p. set (z := 1 + maxs ([x] ++ [y] ++ fvs_trm t ++ fvs_trm t' ++ fvs_frm p)). split.
      * eapply for_compose with (q := All_frm z (subst1 x t (subst1 y (Var_trm z) p))); cycle 1.
        { eapply extend_proves with (Gamma := E.empty). done. eapply for_compose; cycle 1.
          - rewrite subst1_nice with (x := x) (t := t). eapply rebind_All_frm_fwd with (x' := z).
            red. rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. destruct (Nat.eq_dec z y1) as [? | ?]; [right | left]; trivial.
            eapply alpha_is_not_free_in_frm. rewrite subst1_nice. reflexivity.
            rewrite <- subst_compose_frm_spec. eapply frm_is_fresh_in_subst_iff.
            unfold frm_is_fresh_in_subst. rewrite forallb_forall. intros u u_free. rewrite fv_is_free_in_frm in u_free.
            unfold subst_compose, compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + rewrite negb_true_iff. subst u. rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
            + rewrite negb_true_iff. subst u. eapply last_ivar_trm_gt. unfold z, last_ivar_trm. repeat rewrite maxs_app. done.
            + rewrite negb_true_iff. rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros ->.
              enough (CONTRA : is_free_in_frm z p = false) by done. eapply last_ivar_frm_gt. unfold z, last_ivar_frm. repeat rewrite maxs_app. done.
          - rewrite <- subst1_nice with (x := x). rewrite <- subst1_nice with (x := y1). eapply for_Imp_E.
            { exists []. econstructor. intros ?. done. econstructor. eapply FA3. }
            eapply for_All_I. done. eapply for_compose with (q := subst1 x t (subst1 y1 (Var_trm z) (subst1 y (Var_trm y1) p))); cycle 1.
            { eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
              rewrite subst1_nice with (x := y1) at 1. rewrite subst1_nice with (x := x) at 1. rewrite subst1_nice with (x := y) at 1.
              rewrite subst1_nice with (x := x) at 1. rewrite subst1_nice with (x := y1) at 1. rewrite subst1_nice with (x := y) at 1.
              repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same. intros u u_free.
              unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
              - enough (CONTRA : z > x) by done. unfold z. repeat rewrite maxs_app. simpl; done.
              - eapply subst_nil_trm. subst u. rename u_free into FREE. intros u u_free. des. subst u. done. done.
              - subst u. done.
            }
            eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
            repeat rewrite subst1_nice. repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
            intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + enough (CONTRA : z > x) by done. unfold z. repeat rewrite maxs_app. simpl; done.
            + subst u. done.
        }
        eapply for_compose with (q := All_frm z (subst1 x t' (subst1 y (Var_trm z) p))).
        { eapply extend_proves with (Gamma := E.empty). done. eapply for_compose.
          - eapply rebind_All_frm_bwd with (x' := z). red. rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. pose proof (Nat.eq_dec z y) as [? | ?]; [right | left]; trivial.
            eapply alpha_is_not_free_in_frm. rewrite subst1_nice. reflexivity. apply frm_is_fresh_in_subst_iff.
            unfold frm_is_fresh_in_subst. rewrite forallb_forall. intros u u_free. unfold subst_compose, compose, one_subst, cons_subst, nil_subst. rewrite negb_true_iff.
            rewrite fv_is_free_in_frm in u_free. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. eapply last_ivar_trm_gt. unfold z, last_ivar_trm. repeat rewrite maxs_app. done.
            + rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros ->.
              enough (CONTRA : is_free_in_frm z p = false) by done. eapply last_ivar_frm_gt. unfold z, last_ivar_frm. repeat rewrite maxs_app. done.
          - rewrite <- subst1_nice. eapply for_Imp_E with (p := All_frm z (Imp_frm (subst1 x t' (subst1 y (Var_trm z) p)) (subst1 y (Var_trm z) (subst1 x t' p)))).
            { exists []. split. intros ?. done. econstructor. eapply FA3. }
            eapply for_All_I. done. eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
            repeat rewrite subst1_nice. repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
            intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. enough (CONTRA : z > x) by done. unfold z. repeat rewrite maxs_app. simpl. done.
            + symmetry. eapply subst_nil_trm. subst u. rename u_free into FREE. intros u u_free. des. subst u. done. done.
        }
        eapply cut_one'. 2: exact PROVE. eapply for_Imp_I. eapply for_All_I.
        { intros q q_in; autorewrite with simplication_hints in q_in; destruct q_in as [-> | [-> | []]].
          - rewrite is_free_in_frm_unfold; rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq; done.
          - rewrite is_free_in_frm_unfold; rewrite orb_false_iff. split; eapply last_ivar_trm_gt; unfold z, last_ivar_trm; repeat rewrite maxs_app; done.
        }
        pose proof (IH (subst1 y (Var_trm z) p)) as claim1. rewrite subst1_preserves_rank in claim1. specialize (claim1 (le_n _)).
        assert (PROVE' : (E.insert (All_frm z (subst1 x t (subst1 y (Var_trm z) p))) (E.insert (Eqn_frm t t') E.empty)) \proves Eqn_frm t t').
        { eapply for_ByHyp. right. left. reflexivity. }
        specialize claim1 with (lhs := t) (rhs := t'). destruct (claim1 _ x PROVE') as [PROVE3 PROVE4]. clear claim1.
        eapply for_Imp_E. exact PROVE3. eapply cut_one' with (A := All_frm z (subst1 x t (subst1 y (Var_trm z) p))).
        { rewrite <- subst1_id with (x := z) (p := subst1 x t (subst1 y (Var_trm z) p)) at 2. rewrite subst1_nice with (x := z) (t := Var_trm z). eapply for_All_E. eapply for_ByHyp. left. reflexivity. }
        { eapply for_ByHyp. left. reflexivity. }
      * eapply for_compose with (q := All_frm z (subst1 x t' (subst1 y (Var_trm z) p))); cycle 1.
        { eapply extend_proves with (Gamma := E.empty). done. eapply for_compose; cycle 1.
          - rewrite subst1_nice with (x := x) (t := t'). eapply rebind_All_frm_fwd with (x' := z).
            red. rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. destruct (Nat.eq_dec z y) as [? | ?]; [right | left]; trivial.
            eapply alpha_is_not_free_in_frm. reflexivity. eapply frm_is_fresh_in_subst_iff.
            unfold frm_is_fresh_in_subst. rewrite forallb_forall. intros u u_free. rewrite fv_is_free_in_frm in u_free.
            unfold subst_compose, compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + rewrite negb_true_iff. subst u. eapply last_ivar_trm_gt. unfold z, last_ivar_trm. repeat rewrite maxs_app. done.
            + rewrite negb_true_iff. rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros ->.
              enough (CONTRA : is_free_in_frm z p = false) by done. eapply last_ivar_frm_gt. unfold z, last_ivar_frm. repeat rewrite maxs_app. done.
          - rewrite <- subst1_nice with (x := x). rewrite <- subst1_nice with (x := y). eapply for_Imp_E.
            { exists []. econstructor. intros ?. done. econstructor. eapply FA3. }
            eapply for_All_I. done. eapply for_compose with (q := subst1 x t' (subst1 y (Var_trm z) (subst1 y1 (Var_trm y) p))); cycle 1.
            { eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
              rewrite subst1_nice with (x := y) at 1. rewrite subst1_nice with (x := x) at 1.
              rewrite subst1_nice with (x := x) at 1. rewrite subst1_nice with (x := y) at 1. rewrite subst1_nice with (x := y1) at 1.
              repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same. intros u u_free.
              unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
              - eapply subst_nil_trm. subst u. rename u_free into FREE. intros u u_free. des. subst u. done. done.
              - subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
              - subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
              - subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
              - subst u. done.
            }
            eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
            repeat rewrite subst1_nice. repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
            intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
            + subst u. done.
        }
        eapply for_compose with (q := All_frm z (subst1 x t (subst1 y (Var_trm z) p))).
        { eapply extend_proves with (Gamma := E.empty). done. eapply for_compose.
          - eapply rebind_All_frm_bwd with (x' := z). red. rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. pose proof (Nat.eq_dec z y1) as [? | ?]; [right | left]; trivial.
            eapply alpha_is_not_free_in_frm. repeat rewrite subst1_nice. reflexivity. rewrite <- subst_compose_frm_spec. apply frm_is_fresh_in_subst_iff.
            unfold frm_is_fresh_in_subst. rewrite forallb_forall. intros u u_free. unfold subst_compose, compose, one_subst, cons_subst, nil_subst. rewrite negb_true_iff.
            rewrite fv_is_free_in_frm in u_free. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
            + subst u. eapply last_ivar_trm_gt. unfold z, last_ivar_trm. repeat rewrite maxs_app. done.
            + rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros ->.
              enough (CONTRA : is_free_in_frm z p = false) by done. eapply last_ivar_frm_gt. unfold z, last_ivar_frm. repeat rewrite maxs_app. done.
          - rewrite <- subst1_nice. eapply for_Imp_E with (p := ?[p]).
            { exists []. split. intros ?. done. econstructor. eapply FA3. }
            eapply for_All_I. done. eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
            repeat rewrite subst1_nice. repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
            intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
            + symmetry. eapply subst_nil_trm. subst u. rename u_free into FREE. intros u u_free. des. subst u. done. done.
            + subst u. done.
        }
        eapply cut_one'. 2: exact PROVE. eapply for_Imp_I. eapply for_All_I.
        { intros q q_in; autorewrite with simplication_hints in q_in; destruct q_in as [-> | [-> | []]].
          - rewrite is_free_in_frm_unfold; rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq; done.
          - rewrite is_free_in_frm_unfold; rewrite orb_false_iff. split; eapply last_ivar_trm_gt; unfold z, last_ivar_trm; repeat rewrite maxs_app; done.
        }
        pose proof (IH (subst1 y (Var_trm z) p)) as claim1. rewrite subst1_preserves_rank in claim1. specialize (claim1 (le_n _)).
        assert (PROVE' : E.insert (All_frm z (subst1 x t' (subst1 y (Var_trm z) p))) (E.insert (Eqn_frm t t') E.empty) \proves Eqn_frm t t').
        { eapply for_ByHyp. right. left. reflexivity. }
        specialize claim1 with (lhs := t) (rhs := t') (Gamma := E.insert (All_frm z (subst1 x t' (subst1 y (Var_trm z) p))) (E.insert (Eqn_frm t t') E.empty)) (x := x).
        specialize (claim1 PROVE'). destruct claim1 as [PROVE3 PROVE4].
        eapply for_Imp_E. eapply PROVE4. rewrite <- subst1_id with (x := z) (p := subst1 x t' (subst1 y (Var_trm z) p)) at 2.
        rewrite subst1_nice with (x := z) (t := Var_trm z). eapply for_All_E. eapply for_ByHyp. left. reflexivity.
    + rename lhs into t, rhs into t', p1 into p. set (z := 1 + maxs ([x] ++ [y] ++ fvs_trm t ++ fvs_trm t' ++ fvs_frm p)). split.
      * eapply for_compose with (q := All_frm z (subst1 x t (subst1 y (Var_trm z) p))); cycle 1.
        { eapply extend_proves with (Gamma := E.empty). done. eapply for_compose; cycle 1.
          - rewrite subst1_nice with (x := x) (t := t). eapply rebind_All_frm_fwd with (x' := z).
            red. rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. destruct (Nat.eq_dec z y) as [? | ?]; [right | left]; trivial.
            eapply alpha_is_not_free_in_frm. reflexivity. eapply frm_is_fresh_in_subst_iff.
            unfold frm_is_fresh_in_subst. rewrite forallb_forall. intros u u_free. rewrite fv_is_free_in_frm in u_free.
            unfold subst_compose, compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + rewrite negb_true_iff. subst u. eapply last_ivar_trm_gt. unfold z, last_ivar_trm. repeat rewrite maxs_app. done.
            + rewrite negb_true_iff. rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros ->.
              enough (CONTRA : is_free_in_frm z p = false) by done. eapply last_ivar_frm_gt. unfold z, last_ivar_frm. repeat rewrite maxs_app. done.
          - rewrite <- subst1_nice with (x := x). rewrite <- subst1_nice with (x := y). eapply for_Imp_E.
            { exists []. econstructor. intros ?. done. econstructor. eapply FA3. }
            eapply for_All_I. done. eapply for_compose with (q := subst1 x t (subst1 y (Var_trm z) (subst1 y1 (Var_trm y) p))); cycle 1.
            { eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
              rewrite subst1_nice with (x := y) at 1. rewrite subst1_nice with (x := x) at 1.
              rewrite subst1_nice with (x := x) at 1. rewrite subst1_nice with (x := y) at 1. rewrite subst1_nice with (x := y1) at 1.
              repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same. intros u u_free.
              unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
              - eapply subst_nil_trm. subst u. rename u_free into FREE. intros u u_free. des. subst u. done. done.
              - subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
              - subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
              - subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
              - subst u. done.
            }
            eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
            repeat rewrite subst1_nice. repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
            intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
            + subst u. done.
        }
        eapply for_compose with (q := All_frm z (subst1 x t' (subst1 y (Var_trm z) p))).
        { eapply extend_proves with (Gamma := E.empty). done. eapply for_compose.
          - eapply rebind_All_frm_bwd with (x' := z). red. rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. pose proof (Nat.eq_dec z y2) as [? | ?]; [right | left]; trivial.
            eapply alpha_is_not_free_in_frm. repeat rewrite subst1_nice. reflexivity. rewrite <- subst_compose_frm_spec. apply frm_is_fresh_in_subst_iff.
            unfold frm_is_fresh_in_subst. rewrite forallb_forall. intros u u_free. unfold subst_compose, compose, one_subst, cons_subst, nil_subst. rewrite negb_true_iff.
            rewrite fv_is_free_in_frm in u_free. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
            + subst u. eapply last_ivar_trm_gt. unfold z, last_ivar_trm. repeat rewrite maxs_app. done.
            + rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros ->.
              enough (CONTRA : is_free_in_frm z p = false) by done. eapply last_ivar_frm_gt. unfold z, last_ivar_frm. repeat rewrite maxs_app. done.
          - rewrite <- subst1_nice. eapply for_Imp_E with (p := ?[p]).
            { exists []. split. intros ?. done. econstructor. eapply FA3. }
            eapply for_All_I. done. eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
            repeat rewrite subst1_nice. repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
            intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
            + symmetry. eapply subst_nil_trm. subst u. rename u_free into FREE. intros u u_free. des. subst u. done. done.
            + subst u. done.
        }
        eapply cut_one'. 2: exact PROVE. eapply for_Imp_I. eapply for_All_I.
        { intros q q_in; autorewrite with simplication_hints in q_in; destruct q_in as [-> | [-> | []]].
          - rewrite is_free_in_frm_unfold; rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq; done.
          - rewrite is_free_in_frm_unfold; rewrite orb_false_iff. split; eapply last_ivar_trm_gt; unfold z, last_ivar_trm; repeat rewrite maxs_app; done.
        }
        pose proof (IH (subst1 y (Var_trm z) p)) as claim1. rewrite subst1_preserves_rank in claim1. specialize (claim1 (le_n _)).
        assert (PROVE' : E.insert (All_frm z (subst1 x t (subst1 y (Var_trm z) p))) (E.insert (Eqn_frm t t') E.empty) \proves Eqn_frm t t').
        { eapply for_ByHyp. right. left. reflexivity. }
        specialize claim1 with (lhs := t) (rhs := t') (Gamma := E.insert (All_frm z (subst1 x t (subst1 y (Var_trm z) p))) (E.insert (Eqn_frm t t') E.empty)) (x := x).
        specialize (claim1 PROVE'). destruct claim1 as [PROVE3 PROVE4].
        eapply for_Imp_E. eapply PROVE3. rewrite <- subst1_id with (x := z) (p := subst1 x t (subst1 y (Var_trm z) p)) at 2.
        rewrite subst1_nice with (x := z) (t := Var_trm z). eapply for_All_E. eapply for_ByHyp. left. reflexivity.
      * eapply for_compose with (q := All_frm z (subst1 x t' (subst1 y (Var_trm z) p))); cycle 1.
        { eapply extend_proves with (Gamma := E.empty). done. eapply for_compose; cycle 1.
          - rewrite subst1_nice with (x := x) (t := t'). eapply rebind_All_frm_fwd with (x' := z).
            red. rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. destruct (Nat.eq_dec z y2) as [? | ?]; [right | left]; trivial.
            eapply alpha_is_not_free_in_frm. rewrite subst1_nice. reflexivity.
            rewrite <- subst_compose_frm_spec. eapply frm_is_fresh_in_subst_iff.
            unfold frm_is_fresh_in_subst. rewrite forallb_forall. intros u u_free. rewrite fv_is_free_in_frm in u_free.
            unfold subst_compose, compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + rewrite negb_true_iff. subst u. rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done.
            + rewrite negb_true_iff. subst u. eapply last_ivar_trm_gt. unfold z, last_ivar_trm. repeat rewrite maxs_app. done.
            + rewrite negb_true_iff. rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros ->.
              enough (CONTRA : is_free_in_frm z p = false) by done. eapply last_ivar_frm_gt. unfold z, last_ivar_frm. repeat rewrite maxs_app. done.
          - rewrite <- subst1_nice with (x := x). rewrite <- subst1_nice with (x := y2). eapply for_Imp_E.
            { exists []. econstructor. intros ?. done. econstructor. eapply FA3. }
            eapply for_All_I. done. eapply for_compose with (q := subst1 x t' (subst1 y2 (Var_trm z) (subst1 y (Var_trm y2) p))); cycle 1.
            { eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
              rewrite subst1_nice with (x := y2) at 1. rewrite subst1_nice with (x := x) at 1. rewrite subst1_nice with (x := y) at 1.
              rewrite subst1_nice with (x := x) at 1. rewrite subst1_nice with (x := y2) at 1. rewrite subst1_nice with (x := y) at 1.
              repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same. intros u u_free.
              unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
              - enough (CONTRA : z > x) by done. unfold z. repeat rewrite maxs_app. simpl; done.
              - eapply subst_nil_trm. subst u. rename u_free into FREE. intros u u_free. des. subst u. done. done.
              - subst u. done.
            }
            eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
            repeat rewrite subst1_nice. repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
            intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + enough (CONTRA : z > x) by done. unfold z. repeat rewrite maxs_app. simpl; done.
            + subst u. done.
        }
        eapply for_compose with (q := All_frm z (subst1 x t (subst1 y (Var_trm z) p))).
        { eapply extend_proves with (Gamma := E.empty). done. eapply for_compose.
          - eapply rebind_All_frm_bwd with (x' := z). red. rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. pose proof (Nat.eq_dec z y) as [? | ?]; [right | left]; trivial.
            eapply alpha_is_not_free_in_frm. rewrite subst1_nice. reflexivity. apply frm_is_fresh_in_subst_iff.
            unfold frm_is_fresh_in_subst. rewrite forallb_forall. intros u u_free. unfold subst_compose, compose, one_subst, cons_subst, nil_subst. rewrite negb_true_iff.
            rewrite fv_is_free_in_frm in u_free. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. eapply last_ivar_trm_gt. unfold z, last_ivar_trm. repeat rewrite maxs_app. done.
            + rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros ->.
              enough (CONTRA : is_free_in_frm z p = false) by done. eapply last_ivar_frm_gt. unfold z, last_ivar_frm. repeat rewrite maxs_app. done.
          - rewrite <- subst1_nice. eapply for_Imp_E with (p := All_frm z (Imp_frm (subst1 x t (subst1 y (Var_trm z) p)) (subst1 y (Var_trm z) (subst1 x t p)))).
            { exists []. split. intros ?. done. econstructor. eapply FA3. }
            eapply for_All_I. done. eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
            repeat rewrite subst1_nice. repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
            intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. enough (CONTRA : z > x) by done. unfold z. repeat rewrite maxs_app. simpl. done.
            + symmetry. eapply subst_nil_trm. subst u. rename u_free into FREE. intros u u_free. des. subst u. done. done.
        }
        eapply cut_one'. 2: exact PROVE. eapply for_Imp_I. eapply for_All_I.
        { intros q q_in; autorewrite with simplication_hints in q_in; destruct q_in as [-> | [-> | []]].
          - rewrite is_free_in_frm_unfold; rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq; done.
          - rewrite is_free_in_frm_unfold; rewrite orb_false_iff. split; eapply last_ivar_trm_gt; unfold z, last_ivar_trm; repeat rewrite maxs_app; done.
        }
        pose proof (IH (subst1 y (Var_trm z) p)) as claim1. rewrite subst1_preserves_rank in claim1. specialize (claim1 (le_n _)). apply proves_symmetry in PROVE.
        assert (PROVE' : (E.insert (All_frm z (subst1 x t' (subst1 y (Var_trm z) p))) (E.insert (Eqn_frm t t') E.empty)) \proves Eqn_frm t t').
        { eapply for_ByHyp. right. left. reflexivity. }
        specialize claim1 with (lhs := t) (rhs := t'). destruct (claim1 _ x PROVE') as [PROVE3 PROVE4]. clear claim1.
        eapply for_Imp_E. exact PROVE4. eapply cut_one' with (A := All_frm z (subst1 x t' (subst1 y (Var_trm z) p))).
        { rewrite <- subst1_id with (x := z) (p := subst1 x t' (subst1 y (Var_trm z) p)) at 2. rewrite subst1_nice with (x := z) (t := Var_trm z). eapply for_All_E. eapply for_ByHyp. left. reflexivity. }
        { eapply for_ByHyp. left. reflexivity. }
    + rename lhs into t, rhs into t', p1 into p. set (z := 1 + maxs ([x] ++ [y] ++ fvs_trm t ++ fvs_trm t' ++ fvs_frm p)). split.
      * eapply for_compose with (q := All_frm z (subst1 x t (subst1 y (Var_trm z) p))); cycle 1.
        { eapply extend_proves with (Gamma := E.empty). done. eapply for_compose; cycle 1.
          - rewrite subst1_nice with (x := x) (t := t). eapply rebind_All_frm_fwd with (x' := z).
            red. rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. destruct (Nat.eq_dec z y) as [? | ?]; [right | left]; trivial.
            eapply alpha_is_not_free_in_frm. reflexivity. eapply frm_is_fresh_in_subst_iff.
            unfold frm_is_fresh_in_subst. rewrite forallb_forall. intros u u_free. rewrite fv_is_free_in_frm in u_free.
            unfold subst_compose, compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + rewrite negb_true_iff. subst u. eapply last_ivar_trm_gt. unfold z, last_ivar_trm. repeat rewrite maxs_app. done.
            + rewrite negb_true_iff. rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros ->.
              enough (CONTRA : is_free_in_frm z p = false) by done. eapply last_ivar_frm_gt. unfold z, last_ivar_frm. repeat rewrite maxs_app. done.
          - rewrite <- subst1_nice with (x := x). rewrite <- subst1_nice with (x := y). eapply for_Imp_E.
            { exists []. econstructor. intros ?. done. econstructor. eapply FA3. }
            eapply for_All_I. done. eapply for_compose with (q := subst1 x t (subst1 y (Var_trm z) (subst1 y1 (Var_trm y) p))); cycle 1.
            { eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
              rewrite subst1_nice with (x := y) at 1. rewrite subst1_nice with (x := x) at 1.
              rewrite subst1_nice with (x := x) at 1. rewrite subst1_nice with (x := y) at 1. rewrite subst1_nice with (x := y1) at 1.
              repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same. intros u u_free.
              unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
              - eapply subst_nil_trm. subst u. rename u_free into FREE. intros u u_free. des. subst u. done. done.
              - subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
              - subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
              - subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
              - subst u. done.
            }
            eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
            repeat rewrite subst1_nice. repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
            intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
            + subst u. done.
        }
        eapply for_compose with (q := All_frm z (subst1 x t' (subst1 y (Var_trm z) p))).
        { eapply extend_proves with (Gamma := E.empty). done. eapply for_compose.
          - eapply rebind_All_frm_bwd with (x' := z). red. rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. pose proof (Nat.eq_dec z y) as [? | ?]; [right | left]; trivial.
            eapply alpha_is_not_free_in_frm. repeat rewrite subst1_nice. reflexivity. eapply frm_is_fresh_in_subst_iff.
            unfold frm_is_fresh_in_subst. rewrite forallb_forall. intros u u_free. unfold subst_compose, compose, one_subst, cons_subst, nil_subst. rewrite negb_true_iff.
            rewrite fv_is_free_in_frm in u_free. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. eapply last_ivar_trm_gt. unfold z, last_ivar_trm. repeat rewrite maxs_app. done.
            + rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros ->.
              enough (CONTRA : is_free_in_frm z p = false) by done. eapply last_ivar_frm_gt. unfold z, last_ivar_frm. repeat rewrite maxs_app. done.
          - rewrite <- subst1_nice. eapply for_Imp_E with (p := ?[p]).
            { exists []. split. intros ?. done. econstructor. eapply FA3. }
            eapply for_All_I. done. eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
            repeat rewrite subst1_nice. repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
            intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
            + symmetry. eapply subst_nil_trm. subst u. rename u_free into FREE. intros u u_free. des. subst u. done. done.
        }
        eapply cut_one'. 2: exact PROVE. eapply for_Imp_I. eapply for_All_I.
        { intros q q_in; autorewrite with simplication_hints in q_in; destruct q_in as [-> | [-> | []]].
          - rewrite is_free_in_frm_unfold; rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq; done.
          - rewrite is_free_in_frm_unfold; rewrite orb_false_iff. split; eapply last_ivar_trm_gt; unfold z, last_ivar_trm; repeat rewrite maxs_app; done.
        }
        pose proof (IH (subst1 y (Var_trm z) p)) as claim1. rewrite subst1_preserves_rank in claim1. specialize (claim1 (le_n _)).
        assert (PROVE' : E.insert (All_frm z (subst1 x t (subst1 y (Var_trm z) p))) (E.insert (Eqn_frm t t') E.empty) \proves Eqn_frm t t').
        { eapply for_ByHyp. right. left. reflexivity. }
        specialize claim1 with (lhs := t) (rhs := t') (Gamma := E.insert (All_frm z (subst1 x t (subst1 y (Var_trm z) p))) (E.insert (Eqn_frm t t') E.empty)) (x := x).
        specialize (claim1 PROVE'). destruct claim1 as [PROVE3 PROVE4].
        eapply for_Imp_E. eapply PROVE3. rewrite <- subst1_id with (x := z) (p := subst1 x t (subst1 y (Var_trm z) p)) at 2.
        rewrite subst1_nice with (x := z) (t := Var_trm z). eapply for_All_E. eapply for_ByHyp. left. reflexivity.
      * eapply for_compose with (q := All_frm z (subst1 x t' (subst1 y (Var_trm z) p))); cycle 1.
        { eapply extend_proves with (Gamma := E.empty). done. eapply for_compose; cycle 1.
          - rewrite subst1_nice with (x := x) (t := t'). eapply rebind_All_frm_fwd with (x' := z).
            red. rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. destruct (Nat.eq_dec z y) as [? | ?]; [right | left]; trivial.
            eapply alpha_is_not_free_in_frm. reflexivity. eapply frm_is_fresh_in_subst_iff.
            unfold frm_is_fresh_in_subst. rewrite forallb_forall. intros u u_free. rewrite fv_is_free_in_frm in u_free.
            unfold subst_compose, compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + rewrite negb_true_iff. subst u. eapply last_ivar_trm_gt. unfold z, last_ivar_trm. repeat rewrite maxs_app. done.
            + rewrite negb_true_iff. rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros ->.
              enough (CONTRA : is_free_in_frm z p = false) by done. eapply last_ivar_frm_gt. unfold z, last_ivar_frm. repeat rewrite maxs_app. done.
          - rewrite <- subst1_nice with (x := x). rewrite <- subst1_nice with (x := y). eapply for_Imp_E.
            { exists []. econstructor. intros ?. done. econstructor. eapply FA3. }
            eapply for_All_I. done. eapply for_compose with (q := subst1 x t' (subst1 y (Var_trm z) (subst1 y1 (Var_trm y) p))); cycle 1.
            { eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
              rewrite subst1_nice with (x := y) at 1. rewrite subst1_nice with (x := x) at 1.
              rewrite subst1_nice with (x := x) at 1. rewrite subst1_nice with (x := y) at 1. rewrite subst1_nice with (x := y1) at 1.
              repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same. intros u u_free.
              unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
              - eapply subst_nil_trm. subst u. rename u_free into FREE. intros u u_free. des. subst u. done. done.
              - subst u. done.
              - subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
              - subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
              - subst u. enough (CONTRA : z > x) by done. unfold z. simpl. lia.
            }
            eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
            repeat rewrite subst1_nice. repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
            intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + enough (CONTRA : z > x) by done. unfold z. repeat rewrite maxs_app. simpl; done.
            + subst u. done.
        }
        eapply for_compose with (q := All_frm z (subst1 x t (subst1 y (Var_trm z) p))).
        { eapply extend_proves with (Gamma := E.empty). done. eapply for_compose.
          - eapply rebind_All_frm_bwd with (x' := z). red. rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. pose proof (Nat.eq_dec z y) as [? | ?]; [right | left]; trivial.
            eapply alpha_is_not_free_in_frm. rewrite subst1_nice. reflexivity. apply frm_is_fresh_in_subst_iff.
            unfold frm_is_fresh_in_subst. rewrite forallb_forall. intros u u_free. unfold subst_compose, compose, one_subst, cons_subst, nil_subst. rewrite negb_true_iff.
            rewrite fv_is_free_in_frm in u_free. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. eapply last_ivar_trm_gt. unfold z, last_ivar_trm. repeat rewrite maxs_app. done.
            + rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros ->.
              enough (CONTRA : is_free_in_frm z p = false) by done. eapply last_ivar_frm_gt. unfold z, last_ivar_frm. repeat rewrite maxs_app. done.
          - rewrite <- subst1_nice. eapply for_Imp_E with (p := All_frm z (Imp_frm (subst1 x t (subst1 y (Var_trm z) p)) (subst1 y (Var_trm z) (subst1 x t p)))).
            { exists []. split. intros ?. done. econstructor. eapply FA3. }
            eapply for_All_I. done. eapply for_Imp_I. eapply alpha_hyp. left. reflexivity.
            repeat rewrite subst1_nice. repeat rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
            intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. repeat (des; try rewrite subst_trm_unfold with (t := Var_trm _)); trivial.
            + subst u. enough (CONTRA : z > x) by done. unfold z. repeat rewrite maxs_app. simpl. done.
            + subst u. symmetry. rename u_free into FREE. eapply subst_nil_trm. intros u u_free. des. subst u. done. done.
        }
        eapply cut_one'. 2: exact PROVE. eapply for_Imp_I. eapply for_All_I.
        { intros q q_in; autorewrite with simplication_hints in q_in; destruct q_in as [-> | [-> | []]].
          - rewrite is_free_in_frm_unfold; rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq; done.
          - rewrite is_free_in_frm_unfold; rewrite orb_false_iff. split; eapply last_ivar_trm_gt; unfold z, last_ivar_trm; repeat rewrite maxs_app; done.
        }
        pose proof (IH (subst1 y (Var_trm z) p)) as claim1. rewrite subst1_preserves_rank in claim1. specialize (claim1 (le_n _)). apply proves_symmetry in PROVE.
        assert (PROVE' : (E.insert (All_frm z (subst1 x t' (subst1 y (Var_trm z) p))) (E.insert (Eqn_frm t t') E.empty)) \proves Eqn_frm t t').
        { eapply for_ByHyp. right. left. reflexivity. }
        specialize claim1 with (lhs := t) (rhs := t'). destruct (claim1 _ x PROVE') as [PROVE3 PROVE4]. clear claim1.
        eapply for_Imp_E. exact PROVE4. eapply cut_one' with (A := All_frm z (subst1 x t' (subst1 y (Var_trm z) p))).
        { rewrite <- subst1_id with (x := z) (p := subst1 x t' (subst1 y (Var_trm z) p)) at 2. rewrite subst1_nice with (x := z) (t := Var_trm z). eapply for_All_E. eapply for_ByHyp. left. reflexivity. }
        { eapply for_ByHyp. left. reflexivity. }
Qed.

End EQUATIONS.

Theorem proves_substitutivity (s : subst L) (Gamma : ensemble (frm L)) (p : frm L)
  (PROVE : Gamma \proves p)
  : E.image (subst_frm s) Gamma \proves subst_frm s p.
Proof.
  assert (empty_proof_intro : forall q : frm L, proof [] q -> E.empty \proves q).
  { ii. exists []. split. intros ?. done. econstructor. eassumption. }
  destruct PROVE as (ps&INCL&(PF)).
  assert (PROVE : E.fromList ps \proves p).
  { exists ps. split. done. econstructor. exact PF. }
  clear PF. revert Gamma p INCL PROVE s. induction ps as [ | q ps IH]; i.
  - clear INCL. destruct PROVE as (ps&INCL&(PF)).
    assert (ps_spec : forall q : frm L, ~ L.In q ps).
    { intros q q_in. done!. }
    clear INCL. eapply extend_proves with (Gamma := E.empty). done.
    clear Gamma. revert s. induction PF; i.
    + pose proof (ps_spec p (or_introl eq_refl)) as [].
    + eapply for_Imp_E with (p := subst_frm s p).
      * eapply IHPF1. intros p' H_in. eapply ps_spec with (q := p'). rewrite in_app_iff. done.
      * eapply IHPF2. intros p' H_in. eapply ps_spec with (q := p'). rewrite in_app_iff. done.
    + simpl. eapply for_All_I.
      * intros p' H_in. inv H_in.
      * eapply IHPF. intros p' H_in. pose proof (ps_spec p' H_in) as [].
    + simpl. eapply empty_proof_intro. eapply IMP1.
    + simpl. eapply empty_proof_intro. eapply IMP2.
    + simpl. eapply empty_proof_intro. eapply CP.
    + simpl. eapply empty_proof_intro. set (chi := chi_frm s (All_frm x p)). set (s' := cons_subst x (Var_trm chi) s). rewrite compose_one_subst_frm.
      enough (ENOUGH : subst_frm (one_subst chi (subst_trm s t)) (subst_frm s' p) = subst_frm (cons_subst x (subst_trm s t) s) p).
      { rewrite <- ENOUGH. eapply FA1. }
      unfold s'. rewrite <- subst_compose_frm_spec. eapply equiv_subst_in_frm_implies_subst_frm_same. intros u u_free.
      unfold subst_compose, one_subst, cons_subst, nil_subst. destruct (eq_dec u x) as [EQ1 | NE1].
      * subst u. rewrite subst_trm_unfold. destruct (eq_dec chi chi) as [EQ2 | NE2]; try done.
      * eapply subst_nil_trm. intros w w_free. destruct (eq_dec w chi) as [EQ2 | NE2]; [subst w | reflexivity]. 
        assert (claim1 : is_free_in_frm u (All_frm x p) = true).
        { simpl. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq. split; trivial. }
        apply chi_frm_not_free with (s := s) (p := All_frm x p) in claim1. subst chi. done.
    + simpl. eapply empty_proof_intro. set (chi := chi_frm s (All_frm x p)).
      replace (All_frm chi (subst_frm (cons_subst x (Var_trm chi) s) p)) with (All_frm chi (subst_frm s p)).
      * eapply FA2. red. rewrite <- frm_is_fresh_in_subst_iff. unfold frm_is_fresh_in_subst.
        rewrite forallb_forall. intros u u_free. unfold compose. rewrite negb_true_iff. rewrite fv_is_free_in_frm in u_free.
        eapply chi_frm_not_free. simpl. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq. split; trivial.
        intros CONTRA. subst u. red in NOT_FREE. done.
      * f_equal. eapply equiv_subst_in_frm_implies_subst_frm_same. intros u u_free.
        unfold cons_subst. destruct (eq_dec u x) as [EQ1 | NE1]; trivial. subst u. red in NOT_FREE. done.
    + set (n := 1 + last_ivar_frm (Imp_frm (All_frm x (Imp_frm p q)) (Imp_frm (All_frm x p) (All_frm x q)))).
      replace (subst_frm s (Imp_frm (All_frm x (Imp_frm p q)) (Imp_frm (All_frm x p) (All_frm x q)))) with (subst_frm (fun z : ivar => if le_lt_dec n z then Var_trm z else s z) (Imp_frm (All_frm x (Imp_frm p q)) (Imp_frm (All_frm x p) (All_frm x q)))).
      * eapply for_Imp_E. eapply subst_frm_close_frm. clearbody n. induction n as [ | n IH]; simpl; i.
        { eapply empty_proof_intro. eapply FA3. }
        { eapply for_All_I. done. exact IH. }
      * eapply equiv_subst_in_frm_implies_subst_frm_same. intros u u_free. destruct (le_lt_dec n u) as [LE | LT]; trivial.
        pose proof (claim1 := @last_ivar_frm_gt L (Imp_frm (All_frm x (Imp_frm p q)) (Imp_frm (All_frm x p) (All_frm x q))) u). done.
    + simpl. eapply proves_reflexivity.
    + pose (n := 2). replace (subst_frm s (Imp_frm (Eqn_frm (Var_trm 0) (Var_trm 1)) (Eqn_frm (Var_trm 1) (Var_trm 0)))) with (subst_frm (fun x : ivar => if le_lt_dec n x then Var_trm x else s x) (Imp_frm (Eqn_frm (Var_trm 0) (Var_trm 1)) (Eqn_frm (Var_trm 1) (Var_trm 0)))).
      * eapply for_Imp_E. eapply subst_frm_close_frm.
        simpl. eapply for_All_I. done. eapply for_All_I. done. eapply empty_proof_intro. eapply EQN_SYM.
      * eapply equiv_subst_in_frm_implies_subst_frm_same. intros u u_free. simpl in u_free. repeat rewrite is_free_in_trm_unfold in u_free. repeat rewrite orb_true_iff in u_free. repeat rewrite Nat.eqb_eq in u_free.
        destruct (le_lt_dec n u) as [LE | LT]; done.
    + pose (n := 3). replace (subst_frm s (Imp_frm (Eqn_frm (Var_trm 0) (Var_trm 1)) (Imp_frm (Eqn_frm (Var_trm 1) (Var_trm 2)) (Eqn_frm (Var_trm 0) (Var_trm 2))))) with (subst_frm (fun x : ivar => if le_lt_dec n x then Var_trm x else s x) (Imp_frm (Eqn_frm (Var_trm 0) (Var_trm 1)) (Imp_frm (Eqn_frm (Var_trm 1) (Var_trm 2)) (Eqn_frm (Var_trm 0) (Var_trm 2))))).
      * eapply for_Imp_E. eapply subst_frm_close_frm.
        simpl. eapply for_All_I. done. eapply for_All_I. done. eapply for_All_I. done. eapply empty_proof_intro. eapply EQN_TRANS.
      * eapply equiv_subst_in_frm_implies_subst_frm_same. intros u u_free. simpl in u_free. repeat rewrite is_free_in_trm_unfold in u_free. repeat rewrite orb_true_iff in u_free. repeat rewrite Nat.eqb_eq in u_free.
        destruct (le_lt_dec n u) as [LE | LT]; done.
    + set (m := L.(function_arity_table) f). replace (subst_frm s (Fun_eqAxm f)) with (subst_frm (fun x : ivar => if le_lt_dec (m + m) x then Var_trm x else s x) (Fun_eqAxm f)).
      * eapply for_Imp_E. eapply subst_frm_close_frm.
        clearbody m. induction (m + m) as [ | n IH]; simpl; i.
        { eapply empty_proof_intro. eapply EQN_FUN. }
        { eapply for_All_I. done. exact IH. }
      * eapply equiv_subst_in_frm_implies_subst_frm_same. intros u u_free.
        destruct (le_lt_dec (m + m) u) as [LE1 | LT1]; trivial. rewrite Fun_eqAxm_free_vars in u_free. done.
    + set (m := L.(relation_arity_table) R). replace (subst_frm s (Rel_eqAxm R)) with (subst_frm (fun x : ivar => if le_lt_dec (m + m) x then Var_trm x else s x) (Rel_eqAxm R)).
      * eapply for_Imp_E. eapply subst_frm_close_frm.
        clearbody m. induction (m + m) as [ | n IH]; simpl; i.
        { eapply empty_proof_intro. eapply EQN_REL. }
        { eapply for_All_I. done. exact IH. }
      * eapply equiv_subst_in_frm_implies_subst_frm_same. intros u u_free.
        destruct (le_lt_dec (m + m) u) as [LE1 | LT1]; trivial. rewrite Rel_eqAxm_free_vars in u_free. done.
  - eapply for_Imp_E with (p := subst_frm s q).
    + change (E.image (subst_frm s) Gamma \proves subst_frm s (Imp_frm q p)). eapply IH.
      * intros p' H_in. done!.
      * rewrite Deduction_theorem. eapply extend_proves with (Gamma := E.fromList (q :: ps)).
        { intros p' H_in. done!. }
        { exact PROVE. }
    + eapply for_ByHyp. rewrite E.in_image_iff. exists q. split; trivial. eapply INCL. simpl. left. trivial.
Qed.

End HILBERT_PROOF_SYSTEM.
