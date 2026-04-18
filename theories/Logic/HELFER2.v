Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Math.ThN.
Require Import PnV.Data.Vector.
Require Import Stdlib.Arith.Wf_nat.
Require Export PnV.Logic.HELFER1.

#[local] Hint Rewrite @eqb_spec@{Set} : simplication_hints.

Section MAPPING_HSUBST_GENERAL.

Import BasicFol2.
Import HELFER1_i.

#[local] Infix "=~=" := is_similar_to.

Context {L : language} {K1 : Set} {K2 : Set}.

Variable h : K1 -> K2.

#[local] Notation L1 := (augmented_language L K1).
#[local] Notation L2 := (augmented_language L K2).
#[local] Notation hatom1 := (ivar + K1)%type.
#[local] Notation hatom2 := (ivar + K2)%type.

Inductive constant_symbols_similarity : Similarity L1.(constant_symbols) L2.(constant_symbols) :=
  | constant_symbols_similarity_inl (c : L.(constant_symbols))
    : inl c =~= inl c
  | constant_symbols_similarity_inr (hc : K1)
    : inr (h hc) =~= inr hc.

#[local] Existing Instance constant_symbols_similarity.

#[local]
Instance trm_similarity
  : Similarity (trm L1) (trm L2).
Proof.
  eapply trm_similarity. eapply constant_symbols_similarity.
Defined.

#[local]
Instance trms_similarity n
  : Similarity (trms L1 n) (trms L2 n).
Proof.
  eapply trms_similarity. eapply constant_symbols_similarity.
Defined.

#[local]
Instance frm_similarity
  : Similarity (frm L1) (frm L2).
Proof.
  eapply frm_similarity. eapply constant_symbols_similarity.
Defined.

#[local]
Instance hatom_similarity : Similarity hatom1 hatom2 :=
  fun z => fun z' =>
  match z, z' with
  | inl x, inl x' => x = x'
  | inr hc, inr hc' => h hc = hc'
  | _, _ => False
  end.

#[local]
Instance hsubst_similarity : Similarity (hatom1 -> trm L1) (hatom2 -> trm L2) :=
  fun sigma1 => fun sigma2 => forall z1, forall z2, hatom_similarity z1 z2 -> trm_similarity (sigma1 z1) (sigma2 z2).

Lemma trm_mapping_similarity (t : trm L1)
  : t =~= trm_mapping h t
with trms_mapping_similarity n (ts : trms L1 n)
  : ts =~= trms_mapping h ts.
Proof.
- destruct t as [x | f ts | [x | c]]; simpl.
  + econstructor.
  + econstructor. eapply trms_mapping_similarity.
  + econstructor. econstructor.
  + econstructor. econstructor.
- destruct ts as [ | n t ts]; simpl.
  + constructor.
  + econstructor.
    * eapply trm_mapping_similarity.
    * eapply trms_mapping_similarity.
Qed.

Lemma frm_mapping_similarity (p : frm L1)
  : p =~= frm_mapping h p.
Proof.
  induction p; simpl.
  - econstructor. eapply trms_mapping_similarity.
  - econstructor; eapply trm_mapping_similarity.
  - econstructor. exact IHp.
  - econstructor; assumption.
  - econstructor. exact IHp.
Qed.

Context {K1_hasEqDec : hasEqDec K1} {K2_hasEqDec : hasEqDec K2}.

Lemma trm_similarity_graph_eq (t1 : trm L1) (t2 : trm L2)
  (SIM : t1 =~= t2)
  : trm_mapping h t1 = t2
with trms_similarity_graph_eq n (ts1 : trms L1 n) (ts2 : trms L2 n)
  (SIM : ts1 =~= ts2)
  : trms_mapping h ts1 = ts2.
Proof.
- induction SIM; simpl.
  + reflexivity.
  + f_equal. eapply trms_similarity_graph_eq. exact ts_SIM.
  + destruct c_SIM; reflexivity.
- induction SIM; simpl.
  + reflexivity.
  + f_equal.
    * eapply trm_similarity_graph_eq. exact t_SIM.
    * eapply trms_similarity_graph_eq. exact ts_SIM.
Qed.

Lemma frm_similarity_graph_eq (p1 : frm L1) (p2 : frm L2)
  (SIM : p1 =~= p2)
  : frm_mapping h p1 = p2.
Proof.
  induction SIM; simpl.
  - f_equal. eapply trms_similarity_graph_eq; eauto.
  - f_equal.
    + eapply trm_similarity_graph_eq; eauto.
    + eapply trm_similarity_graph_eq; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
  - f_equal; eauto.
Qed.

Lemma HC_occurs_in_trm_map (c : K1) (t : trm L1) : HC_occurs_in_trm c t = true -> HC_occurs_in_trm (h c) (trm_mapping h t) = true
with HC_occurs_in_trms_map (c : K1) (n : nat) (ts : trms L1 n) : HC_occurs_in_trms c ts = true -> HC_occurs_in_trms (h c) (trms_mapping h ts) = true.
Proof.
  - destruct t as [x | f ts | [cc | c']]; simpl; intro H.
    + exact H.
    + exact (HC_occurs_in_trms_map c _ ts H).
    + exact H.
    + s!. congruence.
  - destruct ts as [ |  n t ts]; simpl; intro H.
    + exact H.
    + s!. destruct H as [H | H].
      * left. exact (HC_occurs_in_trm_map c t H).
      * right. exact (HC_occurs_in_trms_map c _ ts H).
Qed.

Lemma HC_occurs_in_trm_map_inv (c2 : K2) (t : trm L1) : HC_occurs_in_trm c2 (trm_mapping h t) = true -> (exists c1, HC_occurs_in_trm c1 t = true /\ h c1 = c2)
with HC_occurs_in_trms_map_inv (c2 : K2) (n : nat) (ts : trms L1 n) : HC_occurs_in_trms c2 (trms_mapping h ts) = true -> (exists c1, HC_occurs_in_trms c1 ts = true /\ h c1 = c2).
Proof.
  - destruct t as [x | f ts | [cc | c1]]; simpl; intro H.
    + inv H.
    + exact (HC_occurs_in_trms_map_inv c2 _ ts H).
    + inv H.
    + clear HC_occurs_in_trm_map_inv. s!. exists c1. split; ss!.
  - destruct ts as [| n t ts]; simpl; intro H.
    + inv H.
    + s!. destruct H as [H | H].
      * pose proof (HC_occurs_in_trm_map_inv c2 t H) as [c1 [H1 H2]].
        exists c1. split; ss!.
      * pose proof (HC_occurs_in_trms_map_inv c2 _ ts H) as [c1 [H1 H2]].
        exists c1. split; ss!.
Qed.

Lemma HC_occurs_in_frm_map (c : K1) (p : frm L1) : HC_occurs_in_frm c p = true -> HC_occurs_in_frm (h c) (frm_mapping h p) = true.
Proof.
  induction p as [R ts | t1 t2 | p1 IHp1 | p1 IHp1 p2 IHp2 | y p1 IHp1]; simpl; intro H.
  - exact (HC_occurs_in_trms_map c _ ts H).
  - rewrite orb_true_iff in H |- *.
    destruct H as [H | H].
    + left. exact (HC_occurs_in_trm_map c t1 H).
    + right. exact (HC_occurs_in_trm_map c t2 H).
  - exact (IHp1 H).
  - rewrite orb_true_iff in H |- *.
    destruct H as [H | H].
    + left. exact (IHp1 H).
    + right. exact (IHp2 H).
  - exact (IHp1 H).
Qed.

Lemma HC_occurs_in_frm_map_inv (c2 : K2) (p : frm L1) : HC_occurs_in_frm c2 (frm_mapping h p) = true -> (exists c1, HC_occurs_in_frm c1 p = true /\ h c1 = c2).
Proof.
  induction p as [R ts | t1 t2 | p1 IHp1 | p1 IHp1 p2 IHp2 | y p1 IHp1]; simpl; intro H.
  - exact (HC_occurs_in_trms_map_inv c2 _ ts H).
  - rewrite orb_true_iff in H.
    destruct H as [H | H].
    + destruct (HC_occurs_in_trm_map_inv c2 t1 H) as [c1 [H1 H2]].
      exists c1. split.
      { rewrite orb_true_iff. now left. }
      exact H2.
    + destruct (HC_occurs_in_trm_map_inv c2 t2 H) as [c1 [H1 H2]].
      exists c1. split.
      { rewrite orb_true_iff. now right. }
      exact H2.
  - exact (IHp1 H).
  - rewrite orb_true_iff in H.
    destruct H as [H | H].
    + destruct (IHp1 H) as [c1 [H1 H2]].
      exists c1. split.
      { rewrite orb_true_iff. now left. }
      exact H2.
    + destruct (IHp2 H) as [c1 [H1 H2]].
      exists c1. split.
      { rewrite orb_true_iff. now right. }
      exact H2.
  - exact (IHp1 H).
Qed.

Lemma hchi_frm_graph_eq (sigma1 : hatom1 -> trm L1) (sigma2 : hatom2 -> trm L2) (p : frm L1)
  (SIG : forall z1 z2, hatom_similarity z1 z2 -> trm_mapping h (sigma1 z1) = sigma2 z2)
  : hchi_frm sigma1 p = hchi_frm sigma2 (frm_mapping h p).
Proof.
  unfold hchi_frm. f_equal. f_equal.
  eapply maxs_ext. intro n. unfold "∘"%prg.
  split; intro H.
  - rewrite in_map_iff in H.
    destruct H as [z2 [Hz2 IN2]].
    destruct z2 as [x | c2]; s!.
    + exists (inl x). split.
      * rewrite <- Hz2. unfold last_ivar_trm. symmetry. f_equal. f_equal.
        exploit (SIG (inl x) (inl x)); [econs | intros EQ].
        rewrite <- EQ. now rewrite trm_mapping_fvs_eq.
      * rewrite in_accum_hatom_in_frm_iff_is_free_in_frm in IN2.
        rewrite in_accum_hatom_in_frm_iff_is_free_in_frm.
        rewrite <- fv_is_free_in_frm.
        rewrite frm_mapping_fvs_eq.
        rewrite -> fv_is_free_in_frm.
        exact IN2.
    + exploit (HC_occurs_in_frm_map_inv (h c2) p).
      { rewrite HC_occurs_in_frm_map; eauto. now rewrite -> in_accum_hatom_in_frm_iff_HC_occurs_in_frm in IN2. }
      intros [c1 [? ?]]. exists (inr (h c1)). split.
      * rewrite <- Hz2. unfold last_ivar_trm. symmetry. f_equal. f_equal. rewrite -> H0.
        exploit (SIG (inr c2) (inr (h c2))); [econs | intros EQ].
        rewrite <- EQ. now rewrite trm_mapping_fvs_eq.
      * rewrite in_accum_hatom_in_frm_iff_HC_occurs_in_frm.
        rewrite HC_occurs_in_frm_map; eauto.
  - rewrite in_map_iff in H.
    destruct H as [z2 [Hz2 IN2]].
    destruct z2 as [x | c2]; s!.
    + exists (inl x). split.
      * rewrite <- Hz2. unfold last_ivar_trm. symmetry. f_equal. f_equal.
        exploit (SIG (inl x) (inl x)); [econs | intros EQ].
        rewrite <- EQ. now rewrite trm_mapping_fvs_eq.
      * rewrite in_accum_hatom_in_frm_iff_is_free_in_frm in IN2.
        rewrite in_accum_hatom_in_frm_iff_is_free_in_frm.
        rewrite <- fv_is_free_in_frm in IN2.
        rewrite frm_mapping_fvs_eq in IN2.
        rewrite -> fv_is_free_in_frm in IN2.
        exact IN2.
    + exploit (HC_occurs_in_frm_map_inv c2 p).
      { rewrite -> in_accum_hatom_in_frm_iff_HC_occurs_in_frm in IN2; eauto. }
      intros [c1 [? ?]]. exists (inr c1). split.
      * rewrite <- Hz2. subst c2. unfold last_ivar_trm. symmetry. f_equal. f_equal.
        exploit (SIG (inr c1) (inr (h c1))); [econs | intros EQ].
        rewrite <- EQ. now rewrite trm_mapping_fvs_eq.
      * rewrite in_accum_hatom_in_frm_iff_HC_occurs_in_frm. subst c2; eauto.
Qed.

Lemma hsubst_trm_graph_eq (sigma1 : hatom1 -> trm L1) (sigma2 : hatom2 -> trm L2) (t : trm L1)
  (SIG : forall z1 z2, hatom_similarity z1 z2 -> trm_mapping h (sigma1 z1) = sigma2 z2)
  : trm_mapping h (hsubst_trm sigma1 t) = hsubst_trm sigma2 (trm_mapping h t)
with hsubst_trms_graph_eq (sigma1 : hatom1 -> trm L1) (sigma2 : hatom2 -> trm L2) (n : nat) (ts : trms L1 n)
  (SIG : forall z1 z2, hatom_similarity z1 z2 -> trm_mapping h (sigma1 z1) = sigma2 z2)
  : trms_mapping h (hsubst_trms sigma1 ts) = hsubst_trms sigma2 (trms_mapping h ts).
Proof.
- destruct t as [x | f ts | [cc | c]]; simpl.
  + exact (SIG (inl x) (inl x) eq_refl).
  + f_equal. eapply hsubst_trms_graph_eq. exact SIG.
  + reflexivity.
  + exact (SIG (inr c) (inr (h c)) eq_refl).
- destruct ts as [| n t ts]; simpl.
  + reflexivity.
  + f_equal.
    * eapply hsubst_trm_graph_eq. exact SIG.
    * eapply hsubst_trms_graph_eq. exact SIG.
Qed.

Lemma hsubst_frm_graph_eq (sigma1 : hatom1 -> trm L1) (sigma2 : hatom2 -> trm L2) (p : frm L1)
  (SIG : forall z1 z2, hatom_similarity z1 z2 -> trm_mapping h (sigma1 z1) = sigma2 z2)
  : frm_mapping h (hsubst_frm sigma1 p) = hsubst_frm sigma2 (frm_mapping h p).
Proof.
  revert sigma1 sigma2 SIG.
  induction p as [R ts | t1 t2 | p1 IHp1 | p1 IHp1 p2 IHp2 | y p1 IHp1];
    intros sigma1 sigma2 SIG; simpl.
  - f_equal. eapply hsubst_trms_graph_eq. exact SIG.
  - f_equal.
    + eapply hsubst_trm_graph_eq. exact SIG.
    + eapply hsubst_trm_graph_eq. exact SIG.
  - f_equal. eapply IHp1. exact SIG.
  - f_equal.
    + eapply IHp1. exact SIG.
    + eapply IHp2. exact SIG.
  - pose proof (hchi_frm_graph_eq sigma1 sigma2 (All_frm y p1) SIG) as HH.
    simpl in HH. rewrite <- HH.
    f_equal.
    eapply IHp1.
    intros z1 z2 ZSIM.
    unfold cons_hsubst. unfold eqb.
    destruct (eq_dec z1 (inl y)) as [-> | NE1].
    + destruct z2 as [x | c2]; simpl in ZSIM; try contradiction.
      subst x.
      destruct (eq_dec (inl y) (inl y)); [reflexivity | congruence].
    + assert (NE2 : z2 <> inl y).
      { intro EZ.
        destruct z1 as [x1 | c1], z2 as [x2 | c2];
          simpl in ZSIM; try contradiction; congruence. }
      destruct (eq_dec z2 (inl y)) as [EZ1 | _]; [contradiction|].
      exact (SIG z1 z2 ZSIM).
Qed.

Theorem frm_mapping_replace_constant_in_frm_inj (h_inj : forall c1, forall c2, h c1 = h c2 -> c1 = c2) (c : K1) (ct : trm L1) (q : frm L1)
  : frm_mapping h (replace_constant_in_frm c ct q) = replace_constant_in_frm (h c) (trm_mapping h ct) (frm_mapping h q).
Proof.
  unfold replace_constant_in_frm.
  eapply hsubst_frm_graph_eq.
  intros z1 z2 ZSIM.
  unfold one_hsubst, cons_hsubst, nil_hsubst.
  destruct z1 as [x1 | c1], z2 as [x2 | c2]; simpl in ZSIM; try contradiction.
  - subst x2. unfold eqb.
    destruct (eq_dec (inl x1) (inr c)); [congruence | reflexivity].
  - subst c2. unfold eqb.
    destruct (eq_dec (inr c1) (inr c)) as [E1 | NE1].
    + inversion E1. subst c1.
      destruct (eq_dec (inr (h c)) (inr (h c))); [reflexivity | congruence].
    + destruct (eq_dec (inr (h c1)) (inr (h c))) as [E2 | NE2].
      * exfalso. apply NE1. f_equal.
        eapply h_inj. now inversion E2.
      * reflexivity.
Qed.

End MAPPING_HSUBST_GENERAL.

Module HELFER1_ii.

Import FolHilbert.
Import HELFER1_i.

Section HELFER1_ii_a.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.
#[local] Notation "x ≠ y" := (~ eq x y) : type_scope.
#[local] Infix "⊢" := HilbertFol.proves : type_scope.
#[local] Notation inconsistent := FolHilbert.inconsistent.

Context {L : language}.

Section MAPPING_REPLACE_CONSTANT.

Context {K1 : Set} {K2 : Set} {K1_hasEqDec : hasEqDec K1} {K2_hasEqDec : hasEqDec K2}.

Variable h : K1 -> K2.

#[local] Notation L1 := (augmented_language L K1).

#[local] Notation L2 := (augmented_language L K2).

Hypothesis h_inj : forall c1, forall c2, h c1 = h c2 -> c1 = c2.

Lemma trm_mapping_replace_constant_in_trm (c : K1) (ct : trm L1) (t : trm L1)
  : trm_mapping h (replace_constant_in_trm c ct t) = replace_constant_in_trm (h c) (trm_mapping h ct) (trm_mapping h t)
with trms_mapping_replace_constant_in_trms (c : K1) (ct : trm L1) (n : nat) (ts : trms L1 n)
  : trms_mapping h (replace_constant_in_trms c ct ts)
    = replace_constant_in_trms (h c) (trm_mapping h ct) (trms_mapping h ts).
Proof.
  - destruct t as [x | f ts | c']; simpl.
    + reflexivity.
    + f_equal. eapply trms_mapping_replace_constant_in_trms.
    + destruct c' as [c' | hc']; simpl.
      * reflexivity.
      * unfold one_hsubst, cons_hsubst, nil_hsubst.
        destruct (eqb (inr hc') (inr c)) as [ | ] eqn: H_OBS1; rewrite eqb_spec in H_OBS1.
        { destruct (eqb _ _) as [ | ] eqn: H_OBS2; rewrite eqb_spec in H_OBS2.
          - inv H_OBS2. apply h_inj in H0. subst. congruence.
          - inv H_OBS1. congruence.
        }
        { destruct (eqb _ _) as [ | ] eqn: H_OBS2; rewrite eqb_spec in H_OBS2.
          - inv H_OBS2. apply h_inj in H0. subst. congruence.
          - reflexivity.
        }
  - destruct ts as [ | n t ts]; simpl.
    + reflexivity.
    + f_equal.
      * eapply trm_mapping_replace_constant_in_trm.
      * eapply trms_mapping_replace_constant_in_trms.
Qed.

#[local] Hint Rewrite trm_mapping_replace_constant_in_trm trms_mapping_replace_constant_in_trms : simplication_hints.

End MAPPING_REPLACE_CONSTANT.

Context {Henkin_constants : Set} {Henkin_constants_hasEqDec : hasEqDec Henkin_constants}.

#[local] Notation L' := (augmented_language L Henkin_constants).
#[local] Infix "≡" := alpha_equiv.

Section GOOD.

Definition hcs_of_ps_p (hc0 : Henkin_constants) (ps : list (frm L')) (p : frm L') : list Henkin_constants :=
  L.nodup eq_dec (hc0 :: flat_map accum_HCs_frm ps ++ accum_HCs_frm p).

Lemma in_hcs_of_ps_p_hc0 (hc0 : Henkin_constants) (ps : list (frm L')) (p : frm L')
  : In hc0 (hcs_of_ps_p hc0 ps p).
Proof.
  unfold hcs_of_ps_p. rewrite L.nodup_In. simpl. left. reflexivity.
Qed.

Lemma in_hcs_of_ps_p_of_ps (hc0 : Henkin_constants) (ps : list (frm L')) (p q : frm L') (hc : Henkin_constants)
  (IN : In q ps)
  (OCC : HC_occurs_in_frm hc q = true)
  : In hc (hcs_of_ps_p hc0 ps p).
Proof.
  unfold hcs_of_ps_p. rewrite L.nodup_In. simpl. right. rewrite in_app_iff.
  left. rewrite in_flat_map. exists q. ss!.
Qed.

Lemma in_hcs_of_ps_p_of_p (hc0 : Henkin_constants) (ps : list (frm L')) (p : frm L') (hc : Henkin_constants)
  (OCC : HC_occurs_in_frm hc p = true)
  : In hc (hcs_of_ps_p hc0 ps p).
Proof.
  unfold hcs_of_ps_p. rewrite L.nodup_In. simpl. right. rewrite in_app_iff.
  right. s!. eauto.
Qed.

Definition Kf (hc0 : Henkin_constants) (ps : list (frm L')) (p : frm L') : Set :=
  { hc : Henkin_constants | (if in_dec eq_dec hc (hcs_of_ps_p hc0 ps p) then true else false) = true }.

#[program]
Definition f (hc0 : Henkin_constants) (ps : list (frm L')) (p : frm L') : Henkin_constants -> Kf hc0 ps p :=
  fun hc => (@exist _ _ (if in_dec eq_dec hc (hcs_of_ps_p hc0 ps p) then hc else hc0) _).
Next Obligation.
  - destruct (in_dec _ hc _) as [IN | NOT_IN].
    + destruct (in_dec _ hc _) as [IN1 | NOT_IN1].
      * reflexivity.
      * contradiction (NOT_IN1 IN).
    + destruct (in_dec _ hc0 _) as [IN1 | NOT_IN1].
      * reflexivity.
      * unfold hcs_of_ps_p in NOT_IN1. rewrite L.nodup_In in NOT_IN1.
        simpl in NOT_IN1. contradiction NOT_IN1. left. reflexivity.
Qed.

Lemma f_id_on_hcs_of_ps_p (hc0 : Henkin_constants) (ps : list (frm L')) (p : frm L') (hc : Henkin_constants)
  (IN : In hc (hcs_of_ps_p hc0 ps p))
  : proj1_sig (f hc0 ps p hc) = hc.
Proof.
  unfold f. simpl proj1_sig. destruct (in_dec _ _ _) as [IN1 | NOT_IN1].
  - reflexivity.
  - contradiction.
Qed.

Lemma finite_HC_type_nat_embed (hc0 : Henkin_constants) (ps : list (frm L')) (p : frm L')
  : { g : Kf hc0 ps p -> nat & { g_back : nat -> Kf hc0 ps p | forall k : Kf hc0 ps p, g_back (g k) = k } }.
Proof.
  set (xs := hcs_of_ps_p hc0 ps p).
  assert (HC0_IN : In hc0 xs).
  { subst xs. eapply in_hcs_of_ps_p_hc0. }
  pose (
    fix index_of (hc : Henkin_constants) (xs : list Henkin_constants) : nat :=
      match xs with
      | nil => 0
      | hc' :: xs' => if eq_dec hc hc' then 0 else S (index_of hc xs')
      end
  ) as index_of.
  rename xs into hcs.
  assert (INDEX_OF_OK : forall hc, forall xs, In hc xs -> nth (index_of hc xs) xs hc = hc).
  { intros hc xs.
    induction xs as [ | hc' xs IH]; simpl; intros IN.
    - contradiction.
    - destruct (eq_dec hc hc') as [-> | NE]; ss!.
  }
  assert (HH : forall n : nat, In (L.nth n hcs hc0) hcs).
  { intros n. assert (length hcs <= n \/ n < length hcs)%nat as [ | ] by lia.
    - rewrite L.nth_overflow; eauto.
    - eapply nth_In; eauto.
  }
  exists (fun k => index_of (proj1_sig k) hcs).
  assert (H_nth : forall n : nat, (if in_dec eq_dec (L.nth n hcs hc0) (hcs_of_ps_p hc0 ps p) then true else false) = true).
  { intros n. destruct (in_dec _ _ _) as [IN1 | NOT_IN1].
    - reflexivity.
    - contradiction NOT_IN1. fold hcs. eapply HH.
  }
  exists (fun n => @exist _ _ (nth n hcs hc0) (H_nth n)). intros [k Hk]; simpl.
  eapply exist_eq_bool. destruct (in_dec _ _ _) as [ | ]; try congruence.
  pose proof (INDEX_OF_OK k hcs i). rewrite <- H at 2. eapply L.nth_indep.
  revert i. fold hcs. clearbody hcs. clear. revert k. induction hcs as [ | h hcs IH]; simpl; intros.
  - lia.
  - destruct i as [? | ?].
    + subst. destruct (eq_dec _ _) as [ | ]; ss!.
    + destruct (eq_dec _ _) as [ | ]; ss!.
Qed.

Lemma trm_mapping_proj1_sig_f_fix (hc0 : Henkin_constants) (ps : list (frm L')) (p : frm L') (t : trm L')
  (SUPPORT : forall hc, HC_occurs_in_trm hc t = true -> In hc (hcs_of_ps_p hc0 ps p))
  : trm_mapping (@proj1_sig _ _) (trm_mapping (f hc0 ps p) t) = t
with trms_mapping_proj1_sig_f_fix (hc0 : Henkin_constants) (ps : list (frm L')) (p : frm L') (n : nat) (ts : trms L' n)
  (SUPPORT : forall hc, HC_occurs_in_trms hc ts = true -> In hc (hcs_of_ps_p hc0 ps p))
  : trms_mapping (@proj1_sig _ _) (trms_mapping (f hc0 ps p) ts) = ts.
Proof.
  - destruct t; simpl.
    + reflexivity.
    + f_equal. eapply trms_mapping_proj1_sig_f_fix. exact SUPPORT.
    + destruct c as [c' | hc']; simpl.
      * reflexivity.
      * destruct (in_dec _ _ _) as [IN1 | NOT_IN1].
        { reflexivity. }
        { contradiction NOT_IN1. eapply SUPPORT. clear. ss!. }
  - destruct ts as [ | n t ts]; simpl.
    + reflexivity.
    + f_equal.
      * eapply trm_mapping_proj1_sig_f_fix. ii.
        eapply SUPPORT. s!. now left.
      * eapply trms_mapping_proj1_sig_f_fix. ii.
        eapply SUPPORT. s!. now right.
Qed.

Lemma frm_mapping_proj1_sig_f_fix (hc0 : Henkin_constants) (ps : list (frm L')) (p q : frm L') (SUPPORT : forall hc, HC_occurs_in_frm hc q = true -> In hc (hcs_of_ps_p hc0 ps p))
  : frm_mapping (@proj1_sig _ _) (frm_mapping (f hc0 ps p) q) = q.
Proof.
  frm_ind q; simpl.
  - f_equal. eapply trms_mapping_proj1_sig_f_fix. exact SUPPORT.
  - f_equal; eapply trm_mapping_proj1_sig_f_fix; ii; eapply SUPPORT; ss!.
  - rewrite IH1; eauto.
  - rewrite IH1, IH2; eauto; ii; eapply SUPPORT; ss!.
  - rewrite IH1; eauto.
Qed.

Lemma proj1_sig_Kf_inj hc0 ps p
  : forall k1 : Kf hc0 ps p, forall k2 : Kf hc0 ps p, proj1_sig k1 = proj1_sig k2 -> k1 = k2.
Proof.
  intros [? ?] [? ?] ?; simpl in *. rewrite <- exist_eq_bool in H. exact H.
Qed.

Section FINITE_TO_NAT_FIX.

Context (hc0 : Henkin_constants) (ps : list (frm L')) (p : frm L').

#[local] Notation K := (Kf hc0 ps p).
#[local] Notation LK := (augmented_language L K).
#[local] Notation LN := (augmented_language L nat).

Variable g : K -> nat.
Variable g_back : nat -> K.
Hypothesis G_BACK_G : forall k, g_back (g k) = k.

Lemma trm_mapping_g_back_g_fix
  (t : trm LK)
  : trm_mapping g_back (trm_mapping g t) = t
with trms_mapping_g_back_g_fix
  (n : nat) (ts : trms LK n)
  : trms_mapping g_back (trms_mapping g ts) = ts.
Proof.
  - trm_ind t.
    + simpl. reflexivity.
    + simpl. f_equal. eapply trms_mapping_g_back_g_fix.
    + simpl. destruct c as [c | ck]; simpl.
      * reflexivity.
      * rewrite G_BACK_G. reflexivity.
  - trms_ind ts.
    + simpl. reflexivity.
    + simpl. f_equal.
      * eapply trm_mapping_g_back_g_fix.
      * eapply trms_mapping_g_back_g_fix.
Qed.

#[local] Hint Rewrite trm_mapping_g_back_g_fix trms_mapping_g_back_g_fix : simplication_hints.

Lemma frm_mapping_g_back_g_fix (q : frm LK)
  : frm_mapping g_back (frm_mapping g q) = q.
Proof.
  frm_ind q; s!; f_equal; eauto.
Qed.

End FINITE_TO_NAT_FIX.

Theorem proves_replace_constant_in_frm (hc0 : Henkin_constants) (y0 : ivar) (Gamma : ensemble (frm L')) (p : frm L')
  (PROVE : Gamma ⊢ p)
  : E.image (replace_constant_in_frm hc0 (Var_trm y0)) Gamma ⊢ replace_constant_in_frm hc0 (Var_trm y0) p.
Proof.
  destruct PROVE as [ps [INCL [PF]]].
  assert (Kf_hasEqDec : hasEqDec (Kf hc0 ps p)).
  { unfold Kf. intros [hc Hhc] [hc' Hhc']; simpl. pose proof (eq_dec hc hc') as [EQ | NE].
    - left. now eapply exist_eq_bool.
    - right. congruence.
  }
  (*
    1. destruct PROVE as [ps [INCL [PF]]].
    2. set (hcs := hcs_of_ps_p hc0 ps p).
    3. use proof_mapping (f hc0 ps p) to move PF to (augmented_language L (Kf hc0 ps p)).
    4. obtain g, g_back from finite_HC_type_nat_embed.
    5. use proof_mapping g to move further to (augmented_language L nat).
    6. apply proves_hsubstitutivity with sigma := one_hsubst (inr (g (f hc0 ps p hc0))) (Var_trm y0).
    7. pull the proof back with proof_mapping g_back, then proof_mapping proj1_sig.
    8. simplify with
      - frm_mapping_g_back_g_fix
      - frm_mapping_proj1_sig_f_fix
      - frm_mapping_replace_constant_in_frm
    9. extend from E.fromList ps to Gamma using INCL.
  *)
  set (K := Kf hc0 ps p).
  set (f0 := fun k => (f hc0 ps p k)).
  pose proof (proof_mapping f0 ps p PF) as PF0.
  pose proof (finite_HC_type_nat_embed hc0 ps p) as [g [g_back G_BACK_G]].
  assert (g_inj : forall k1 : K, forall k2 : K, g k1 = g k2 -> k1 = k2).
  { intros k1 k2 Hg. pose proof (G_BACK_G k1). pose proof (G_BACK_G k2). congruence. }
  assert (proj1_sig_inj : forall k1 : K, forall k2 : K, proj1_sig k1 = proj1_sig k2 -> k1 = k2).
  { intros [k1 H1] [k2 H2] Hk; simpl in Hk. now eapply exist_eq_bool. }
  pose proof (proof_mapping g _ _ PF0) as PF1.
  assert (PROVE1 : E.fromList (map (frm_mapping g) (map (frm_mapping f0) ps)) ⊢ frm_mapping g (frm_mapping f0 p)).
  { exists (map (frm_mapping g) (map (frm_mapping f0) ps)); ss!. }
  pose proof (proves_hsubstitutivity (one_hsubst (inr (g (f0 hc0))) (Var_trm y0)) (E.fromList (map (frm_mapping g) (map (frm_mapping f0) ps))) (frm_mapping g (frm_mapping f0 p)) PROVE1) as [qs [INCL2 [PF2]]].
  replace (replace_constant_in_frm (Henkin_constants_hasEqDec := nat_hasEqDec) (g (f0 hc0)) (Var_trm y0) (frm_mapping g (frm_mapping f0 p))) with (frm_mapping g (replace_constant_in_frm (Henkin_constants_hasEqDec := Kf_hasEqDec) (f0 hc0) (Var_trm y0) (frm_mapping f0 p))) in PF2.
  2:{ symmetry. erewrite @frm_mapping_replace_constant_in_frm_inj; eauto. }
  pose proof (proof_mapping g_back _ _ PF2) as PF3.
  replace (frm_mapping g_back (frm_mapping g (replace_constant_in_frm (Henkin_constants_hasEqDec := Kf_hasEqDec) (f0 hc0) (Var_trm y0) (frm_mapping f0 p)))) with (replace_constant_in_frm (f0 hc0) (Var_trm y0) (frm_mapping f0 p)) in PF3.
  2:{ symmetry. erewrite frm_mapping_g_back_g_fix; eauto. }
  assert (PROVE3 : E.image (replace_constant_in_frm (f0 hc0) (Var_trm y0)) (E.fromList (map (frm_mapping f0) ps)) ⊢ replace_constant_in_frm (f0 hc0) (Var_trm y0) (frm_mapping f0 p)).
  { eapply extend_proves; cycle 1.
    - exists (map (frm_mapping g_back) qs). split.
      + intros r Hr.
        do 2 red in Hr.
        rewrite in_map_iff in Hr.
        destruct Hr as [q [<- INq]].
        assert (Hin : q \in E.fromList qs) by done.
        pose proof (INCL2 _ Hin) as H.
        rewrite E.in_image_iff in H.
        destruct H as [r [-> INr]].
        do 2 red in INr.
        rewrite in_map_iff in INr.
        destruct INr as [r0 [<- INr0]].
        rewrite E.in_image_iff.
        rewrite L.in_map_iff in INr0.
        destruct INr0 as [r' [<- Hr']].
        exists (replace_constant_in_frm
                  (Henkin_constants_hasEqDec := Kf_hasEqDec)
                  (f0 hc0) (Var_trm y0) (frm_mapping f0 r')).
        split; cycle 1.
        * eapply E.in_image_iff with (X := E.fromList _). exists (frm_mapping f0 r'). split.
          { reflexivity. }
          { eapply in_map_iff. exists r'. split; eauto. }
        * rewrite <- frm_mapping_g_back_g_fix with
                        (g := g) (g_back := g_back)
                        (q := replace_constant_in_frm
                                (Henkin_constants_hasEqDec := Kf_hasEqDec)
                                (f0 hc0) (Var_trm y0) (frm_mapping f0 r')); eauto.
          erewrite @frm_mapping_replace_constant_in_frm_inj
            with (h := g); eauto. instantiate (1 := id). reflexivity.
      + econs. change
  (proof (map (frm_mapping g_back) qs)
     (frm_mapping g_back
        (replace_constant_in_frm
           (Henkin_constants_hasEqDec := nat_hasEqDec)
           (g (f0 hc0)) (Var_trm y0)
           (frm_mapping g (frm_mapping f0 p))))) in PF3.
replace
  (frm_mapping g_back
     (replace_constant_in_frm
        (Henkin_constants_hasEqDec := nat_hasEqDec)
        (g (f0 hc0)) (Var_trm y0)
        (frm_mapping g (frm_mapping f0 p))))
with
  (replace_constant_in_frm
     (Henkin_constants_hasEqDec := Kf_hasEqDec)
     (f0 hc0) (Var_trm y0) (frm_mapping f0 p))
in PF3.
2:{
  pose proof (@frm_mapping_replace_constant_in_frm_inj L _ _ _ _ _ g_inj (f0 hc0) (Var_trm y0) (frm_mapping f0 p)) as HH.
  simpl trm_mapping  in HH. set (X := 
(replace_constant_in_frm (g (f0 hc0)) (Var_trm y0)
(frm_mapping g (frm_mapping f0 p)))). change (frm_mapping g (replace_constant_in_frm (f0 hc0) (Var_trm y0) (frm_mapping f0 p)) = X) in HH.
  rewrite <- HH. symmetry. eapply frm_mapping_g_back_g_fix; exact G_BACK_G.
}
  eauto.
  - ii. rewrite E.in_image_iff in H. destruct H as [y [-> H]].
    unfold id. eauto.
  }
  destruct PROVE3 as [rs [INCL3 [PF3']]].
  pose proof (proof_mapping (@proj1_sig _ _) _ _ PF3') as PF4.
  assert (HC0_FIX : proj1_sig (f0 hc0) = hc0).
  { eapply f_id_on_hcs_of_ps_p. eapply in_hcs_of_ps_p_hc0. }
  replace (frm_mapping (@proj1_sig _ _) (replace_constant_in_frm (f0 hc0) (Var_trm y0) (frm_mapping f0 p))) with (replace_constant_in_frm hc0 (Var_trm y0) p) in PF4; cycle 1.
  { symmetry.
erewrite @frm_mapping_replace_constant_in_frm_inj
  with (h := @proj1_sig _ _)
       (c := f0 hc0)
       (ct := Var_trm y0)
       (q := frm_mapping f0 p); eauto.
rewrite HC0_FIX.
simpl.
exploit (frm_mapping_proj1_sig_f_fix hc0 ps p p).
- intros hc OCC.
  eapply in_hcs_of_ps_p_of_p.
  exact OCC.
- intros X. set (XX := (frm_mapping
(proj1_sig
(P:=fun hc : Henkin_constants =>
(if in_dec eq_dec hc (hcs_of_ps_p hc0 ps p) then true else false) =
true)) (frm_mapping f0 p))). change (XX = p) in X. congruence.
  }
 eapply extend_proves; cycle 1.
{
  exists (map (frm_mapping (@proj1_sig _ _)) rs). split.
  - intros r Hr.
    do 2 red in Hr.
    rewrite L.in_map_iff in Hr.
    destruct Hr as [q [<- INq]].
    pose proof (INCL3 q INq) as HH.
    rewrite E.in_image_iff in HH.
    destruct HH as [q0 [-> INq0]].
    rewrite E.in_image_iff.
    exists q0. split.
    + reflexivity.
    + exact INq0.
  - econs; eauto.
}
intros r Hr.
rewrite E.in_image_iff in Hr.
destruct Hr as [q0 [-> INq0]].
do 2 red in INq0.
rewrite L.in_map_iff in INq0.
destruct INq0 as [q' [<- INq']].
rewrite E.in_image_iff.
exists q'. split.
- symmetry.
  erewrite @frm_mapping_replace_constant_in_frm_inj
    with (h := @proj1_sig _ _)
         (c := f0 hc0)
         (ct := Var_trm y0)
         (q := frm_mapping f0 q'); eauto.
  rewrite HC0_FIX.
  simpl.
  exploit (frm_mapping_proj1_sig_f_fix hc0 ps p q').
  + intros hc OCC.
    eapply in_hcs_of_ps_p_of_ps; eauto.
  + intros X. set ((frm_mapping
(proj1_sig
(P:=fun hc : Henkin_constants =>
(if in_dec eq_dec hc (hcs_of_ps_p hc0 ps p) then true else false) =
true)) (frm_mapping f0 q'))) as XX.
change (XX = q') in X. congruence.
- eapply INCL.
  do 2 red.
  exact INq'.
Qed.

End GOOD.

Context {AHC : abstract_Henkin_contants Henkin_constants L (Henkin_constants_hasEqDec := Henkin_constants_hasEqDec)}.

Definition HenkinAxiom (hc : Henkin_constants) : frm L' :=
  let '(x, phi) := hc_decode hc in
  Imp_frm (subst_frm (one_subst x (@Con_trm L' (inr hc))) phi) (All_frm x phi).

Section HELFER1_ii_a_1.

Lemma HC_occurs_in_subst_trm_inv (t : trm L') :
  forall s, forall hc, forall hc',
  (forall z, HC_occurs_in_trm hc (s z) = true -> hc = hc') ->
  (HC_occurs_in_trm hc (subst_trm s t) = true) ->
  (hc = hc' \/ HC_occurs_in_trm hc t = true)
with HC_occurs_in_subst_trms_inv (n : nat) (ts : trms L' n) :
  forall s, forall hc, forall hc',
  (forall z, HC_occurs_in_trm hc (s z) = true -> hc = hc') ->
  (HC_occurs_in_trms hc (subst_trms s ts) = true) ->
  (hc = hc' \/ HC_occurs_in_trms hc ts = true).
Proof.
  - destruct t as [x | f ts | c]; simpl; intros s hc hc' HS.
    + rewrite subst_trm_unfold. intro H.
      left. eapply HS. exact H.
    + rewrite subst_trm_unfold. intro H.
      pose proof (HC_occurs_in_subst_trms_inv _ ts s hc hc' HS H) as [-> | Hts].
      * now left.
      * right. exact Hts.
    + intro H. right. exact H.
  - intros s hc hc' HS. destruct ts as [ | n t ts]; simpl.
    + rewrite subst_trms_unfold. s!. congruence.
    + rewrite subst_trms_unfold. s!. intros [Ht | Hts].
      * pose proof (HC_occurs_in_subst_trm_inv t s hc hc' HS Ht) as [-> | Ht'].
        { now left. }
        { right. left. exact Ht'. }
      * pose proof (HC_occurs_in_subst_trms_inv _ ts s hc hc' HS Hts) as [-> | Hts'].
        { now left. }
        { right. right. exact Hts'. }
Qed.

Fixpoint HC_occurs_in_subst_frm_inv (p : frm L') :
  forall s, forall hc, forall hc',
  (forall z, HC_occurs_in_trm hc (s z) = true -> hc = hc') ->
  (HC_occurs_in_frm hc (subst_frm s p) = true) ->
  (hc = hc' \/ HC_occurs_in_frm hc p = true).
Proof.
  destruct p as [R ts | t1 t2 | p1 | p1 p2 | y p1]; simpl; intros s hc hc' HS.
  - intro H.
    pose proof (HC_occurs_in_subst_trms_inv _ ts s hc hc' HS H) as [? | Hts].
    + now left.
    + right. exact Hts.
  - intro H. s!. destruct H as [Ht1 | Ht2].
    + pose proof (HC_occurs_in_subst_trm_inv t1 s hc hc' HS Ht1) as [? | Ht1'].
      * now left.
      * right. left. exact Ht1'.
    + pose proof (HC_occurs_in_subst_trm_inv t2 s hc hc' HS Ht2) as [? | Ht2'].
      * now left.
      * right. right. exact Ht2'.
  - intro H. s!.
    pose proof (HC_occurs_in_subst_frm_inv p1 s hc hc' HS H) as [? | Hp1].
    + now left.
    + right. exact Hp1.
  - intro H. s!. destruct H as [Hp1 | Hp2].
    + pose proof (HC_occurs_in_subst_frm_inv p1 s hc hc' HS Hp1) as [? | Hp1'].
      * now left.
      * right. left. exact Hp1'.
    + pose proof (HC_occurs_in_subst_frm_inv p2 s hc hc' HS Hp2) as [? | Hp2'].
      * now left.
      * right. right. exact Hp2'.
  - set (chi := chi_frm s (All_frm y p1)). intro H.
    assert (HS' : forall z, HC_occurs_in_trm hc (cons_subst y (Var_trm chi) s z) = true -> hc = hc').
    { s!. intros z Hz. destruct (eq_dec _ _) as [EQ | NE].
      - s!. congruence.
      - eapply HS. exact Hz.
    }
    pose proof (HC_occurs_in_subst_frm_inv p1 (cons_subst y (Var_trm chi) s) hc hc' HS' H) as [? | Hp1].
    * now left.
    * right. exact Hp1.
Qed.

Lemma one_subst_only_introduces_hc' hc hc' x z
  (H_occurs : HC_occurs_in_trm hc (one_subst x (@Con_trm L' (inr hc')) z) = true)
  : hc = hc'.
Proof.
  unfold one_subst, cons_subst, nil_subst in H_occurs. destruct (eq_dec _ _).
  - s!. exact H_occurs.
  - s!. congruence.
Qed.

Lemma occurs_in_other_HenkinAxiom_inv hc hc' x phi
  (Hdec : hc_decode hc' = (x, phi))
  (Hneq : hc ≠ hc')
  (H_occurs : HC_occurs_in_frm hc (HenkinAxiom hc') = true)
  : HC_occurs_in_frm hc phi = true.
Proof.
  revert H_occurs. unfold HenkinAxiom. rewrite Hdec. simpl.
  intro H. s!. destruct H as [Hsub | Hphi].
  - pose proof (HC_occurs_in_subst_frm_inv phi (one_subst x (@Con_trm L' (inr hc'))) hc hc' (fun z => fun Hz => one_subst_only_introduces_hc' hc hc' x z Hz) Hsub) as [Heq | Hphi'].
    + contradiction.
    + exact Hphi'.
  - exact Hphi.
Qed.

Lemma same_stage_other_axiom_hc_free
  (hc hc' : Henkin_constants) (n : nat)
  (Hneq : hc ≠ hc')
  (Hst : hc_stage hc = n)
  (Hst' : hc_stage hc' = n)
  : HC_occurs_in_frm hc (HenkinAxiom hc') = false.
Proof.
  destruct (hc_decode hc') as [x phi] eqn: Hdec.
  rewrite <- not_true_iff_false.
  intro Hocc.
  pose proof (occurs_in_other_HenkinAxiom_inv hc hc' x phi Hdec Hneq Hocc) as Hphi.
  pose proof (hc_stage_well_founded hc' x phi Hdec hc Hphi) as Hlt.
  lia.
Qed.

End HELFER1_ii_a_1.

#[local] Infix "≡" := alpha_equiv.

Lemma embed_trm_HC_free (t : trm L)
  : forall c : Henkin_constants, HC_occurs_in_trm c (embed_trm t) = false
with embed_trms_HC_free n (ts : trms L n)
  : forall c : Henkin_constants, HC_occurs_in_trms c (embed_trms ts) = false.
Proof.
  - trm_ind t; simpl; i.
    + reflexivity.
    + s!. eapply embed_trms_HC_free.
    + reflexivity.
  - trms_ind ts; simpl; i.
    + reflexivity.
    + s!. split.
      * eapply embed_trm_HC_free.
      * eapply IH.
Qed.

#[local] Hint Rewrite embed_trm_HC_free embed_trms_HC_free : simplication_hints.

Lemma embed_frm_HC_free (p : frm L)
  : forall c : Henkin_constants, HC_occurs_in_frm c (embed_frm p) = false.
Proof.
  frm_ind p; done!.
Qed.

#[local] Hint Rewrite embed_frm_HC_free : simplication_hints.

Section HELFER1_ii_a_2.

#[local] Notation hatom := (ivar + Henkin_constants)%type.

#[local] Notation hsubst := (hatom -> trm L').

Definition HenkinAxms_upto (n : nat) : ensemble (frm L') :=
  fun A => exists hc, (hc_stage hc < n)%nat /\ A = HenkinAxiom hc.

Definition HenkinAxms_at_stage (n : nat) : ensemble (frm L') :=
  fun A => exists hc, hc_stage hc = n /\ A = HenkinAxiom hc.

Definition AddHenkin_stage (X : ensemble (frm L)) (n : nat) : ensemble (frm L') :=
  E.union (HenkinAxms_upto n) (E.image embed_frm X).

Lemma replace_constant_in_trm_irrelevant (t : trm L')
  : forall hc, forall t0, HC_occurs_in_trm hc t = false -> replace_constant_in_trm hc t0 t = t
with replace_constant_in_trms_irrelevant n (ts : trms L' n)
  : forall hc, forall t0, HC_occurs_in_trms hc ts = false -> replace_constant_in_trms hc t0 ts = ts.
Proof.
  - destruct t as [x | f ts | c]; simpl; intros hc t0; s!.
    + intros _; reflexivity.
    + intros H_EQ. f_equal. eapply replace_constant_in_trms_irrelevant. exact H_EQ.
    + unfold one_hsubst, cons_hsubst, nil_hsubst. destruct c; intros H_EQ.
      * reflexivity.
      * s!. destruct (eqb _ _) as [ | ] eqn: H_OBS; s!; congruence.
  - destruct ts as [ | n t ts]; simpl; intros hc t0; s!.
    + intros _; reflexivity.
    + intros [H1 H2]. f_equal.
      * eapply replace_constant_in_trm_irrelevant. exact H1.
      * eapply replace_constant_in_trms_irrelevant. exact H2.
Qed.

Lemma replace_constant_in_frm_irrelevant (A : frm L') (hc : Henkin_constants) (t : trm L')
  (NOT_OCCUR : HC_occurs_in_frm hc A = false)
  : replace_constant_in_frm hc t A ≡ A.
Proof.
  unfold replace_constant_in_frm. rename A into p. revert p NOT_OCCUR. frm_ind p; s!; i.
  - econs; eapply replace_constant_in_trms_irrelevant; tauto.
  - econs; eapply replace_constant_in_trm_irrelevant; tauto.
  - econs; eapply IH1; tauto.
  - econs; [eapply IH1 | eapply IH2]; tauto.
  - set (s := one_hsubst _ _).
    assert (chi_fresh : is_free_in_frm (hchi_frm s (All_frm y p1)) (All_frm y p1) = false).
    { pose proof (hchi_frm_is_fresh_in_hsubst (All_frm y p1) s) as claim.
      unfold frm_is_fresh_in_hsubst in claim. rewrite forallb_forall in claim.
      unfold "∘"%prg in claim. enough (ENOUGH : is_free_in_frm (hchi_frm s (All_frm y p1)) (All_frm y p1) <> true) by now destruct (is_free_in_frm (hchi_frm s (All_frm y p1)) (All_frm y p1)).
      intros CONTRA. rewrite <- in_accum_hatom_in_frm_iff_is_free_in_frm in CONTRA. specialize (claim (inl (hchi_frm s (All_frm y p1))) CONTRA).
      rewrite negb_true_iff in claim. unfold s in claim. unfold one_hsubst, cons_hsubst, nil_hsubst in claim. simpl in claim.
      rewrite is_free_in_trm_unfold in claim. rewrite Nat.eqb_neq in claim. contradiction.
    }
    eapply alpha_All_frm with (z := hchi_frm s (All_frm y p1)).
    { eapply alpha_equiv_eq_intro. erewrite -> subst_hsubst_compat_in_frm by now ii; reflexivity.
      rewrite <- hsubst_compose_frm_spec. erewrite -> subst_hsubst_compat_in_frm by now ii; reflexivity.
      eapply equiv_hsubst_in_frm_implies_hsubst_frm_same. ii. unfold hsubst_compose, one_hsubst, cons_hsubst, nil_hsubst.
      unfold to_hsubst. destruct (eqb _ _) as [ | ] eqn: H_OBS; rewrite eqb_spec in H_OBS; destruct z; simpl.
      - unfold one_subst, cons_subst, nil_subst. repeat destruct (eq_dec _ _) as [? | ?]; try congruence.
      - unfold one_subst, cons_subst, nil_subst. repeat destruct (eq_dec _ _) as [? | ?]; try congruence.
      - unfold one_subst, cons_subst, nil_subst. repeat destruct (eq_dec _ _) as [? | ?]; try congruence.
      - unfold one_subst, cons_subst, nil_subst. repeat destruct (eq_dec _ _) as [? | ?]; try congruence.
        unfold s, one_hsubst, cons_hsubst, nil_hsubst. destruct (eqb _ _) as [ | ] eqn: H_OBS'; rewrite eqb_spec in H_OBS'.
        + inv H_OBS'. rewrite occurs_free_in_frm_iff in FREE. rewrite in_accum_hatom_in_frm_iff_HC_occurs_in_frm in FREE. congruence.
        + simpl; reflexivity. 
    }
    { rewrite is_free_in_frm_unfold, andb_false_iff, negb_false_iff, Nat.eqb_eq. done!. }
    { exact chi_fresh. }
Qed.

Lemma embed_image_HC_free (X : ensemble (frm L)) (hc : Henkin_constants)
  : forall A : frm L', A \in E.image embed_frm X -> HC_occurs_in_frm hc A = false.
Proof.
  intros p H_in. rewrite E.in_image_iff in H_in; des. subst p. eapply embed_frm_HC_free.
Qed.

Lemma HenkinAxiom_at_stage_HC_free (n : nat) hc hc'
  (Hneq : hc ≠ hc')
  (Hst : hc_stage hc = n)
  (Hst' : hc_stage hc' = n)
  : HC_occurs_in_frm hc (HenkinAxiom hc') = false.
Proof.
  eapply same_stage_other_axiom_hc_free; eauto.
Qed.

Lemma stage_axioms_other_than_hc_are_HC_free n hc
  (Hst : hc_stage hc = n)
  : forall A : frm L', A \in HenkinAxms_at_stage n -> A ≠ HenkinAxiom hc -> HC_occurs_in_frm hc A = false.
Proof.
  intros A HA HneqA. destruct HA as [hc' [Hst' ->]].
  eapply same_stage_other_axiom_hc_free; eauto. congruence.
Qed.

Lemma earlier_stage_axiom_HC_free n hc hc'
  (Hlt : hc_stage hc' < n)
  (Hst : hc_stage hc = n)
  : HC_occurs_in_frm hc (HenkinAxiom hc') = false.
Proof.
  destruct (hc_decode hc') as [x phi] eqn:Hdec.
  rewrite <- not_true_iff_false.
  intro Hocc.
  assert (Hneq : hc <> hc').
  { intro Heq. subst hc'. lia. }
  pose proof (occurs_in_other_HenkinAxiom_inv hc hc' x phi Hdec Hneq Hocc) as Hphi.
  pose proof (hc_stage_well_founded hc' x phi Hdec hc Hphi) as Hlt'.
  lia.
Qed.

Lemma earlier_stage_axioms_are_HC_free n hc
  (Hst : hc_stage hc = n)
  : forall A, A \in HenkinAxms_upto n -> HC_occurs_in_frm hc A = false.
Proof.
  intros A HA. destruct HA as [hc' [Hlt ->]].
  eapply earlier_stage_axiom_HC_free; eauto.
Qed.

Lemma AddHenkin_stage_background_HC_free (X : ensemble (frm L)) (n : nat) (hc : Henkin_constants) (A : frm L')
  (Hst : hc_stage hc = n)
  (Hin : A \in E.union (HenkinAxms_upto n) (E.union (HenkinAxms_at_stage n) (E.image embed_frm X)))
  (Hne : A ≠ HenkinAxiom hc)
  : HC_occurs_in_frm hc A = false.
Proof.
  destruct Hin as [Hin | [Hin | Hin]].
  - eapply earlier_stage_axioms_are_HC_free; eauto.
  - eapply stage_axioms_other_than_hc_are_HC_free; eauto.
  - rewrite E.in_image_iff in Hin. destruct Hin as [p [EQ IN]]; subst A.
    eapply HC_occurs_in_embed_frm_false.
Qed.

Lemma AddHenkin_stage_prev_HC_free (X : ensemble (frm L)) (n : nat) (hc : Henkin_constants)
  (Hst : hc_stage hc = n)
  : forall A : frm L', A \in AddHenkin_stage X n -> HC_occurs_in_frm hc A = false.
Proof.
  intros A HA. destruct HA as [HA | HA].
  - eapply earlier_stage_axioms_are_HC_free; eauto.
  - rewrite E.in_image_iff in HA. destruct HA as [B [HB1 HB2]]. subst A.
    eapply HC_occurs_in_embed_frm_false.
Qed.

Lemma remove_one_Henkin_axiom (Gamma : ensemble (frm L')) (hc : Henkin_constants)
  (BG_free : forall A, A \in Gamma -> HC_occurs_in_frm hc A = false)
  (INCONSISTENT : inconsistent (E.insert (HenkinAxiom hc) Gamma))
  : inconsistent Gamma.
Proof.
  rewrite inconsistent_iff in INCONSISTENT |- *.
  destruct (hc_decode hc) as [x phi] eqn:Hdec.
  set (c := @Con_trm L' (inr hc)).
  assert (PROVE1 : Gamma ⊢ Neg_frm (HenkinAxiom hc)).
  { eapply NegationI. exact INCONSISTENT. }
  unfold HenkinAxiom in PROVE1.
  rewrite Hdec in PROVE1.
  fold c in PROVE1.
  assert (PROVE2 : Gamma ⊢ subst_frm (one_subst x c) phi).
  { eapply for_Imp_E. exists []. split. done. econs. eapply proof_dne. eapply for_Imp_E. 2: eapply PROVE1. eapply for_CP1. exists []. split. done. econs. eapply proof_ex_falso. }
  assert (PROVE3 : Gamma ⊢ Neg_frm (All_frm x phi)).
  { eapply for_Imp_E. 2: exact PROVE1. eapply for_CP1. eapply for_Imp_I. eapply for_Imp_I.  eapply for_ByHyp. done!. }
  eapply ContradictionI with (A := All_frm x phi).
  - clear PROVE1 PROVE3. rename PROVE2 into PROVE. destruct PROVE as [ps [INCL PF]].
    set (y := 1 + max (max x (maxs (map last_ivar_frm ps))) (max (last_ivar_frm (All_frm x phi)) (last_ivar_frm (subst_frm (one_subst x c) phi)))).
    eapply extend_alpha_proves with (Gamma := E.image (replace_constant_in_frm hc (Var_trm y)) (E.fromList ps)).
    + intros p IN. rewrite E.in_image_iff in IN. destruct IN as [q [-> INq]]. exists q. split.
      * eapply replace_constant_in_frm_irrelevant. eapply BG_free. eapply INCL. exact INq.
      * eapply INCL. exact INq.
    + eapply for_All_I' with (y := y).
      * intros p Hp. rewrite E.in_image_iff in Hp. destruct Hp as [q [-> INq]]. unfold replace_constant_in_frm. eapply frm_is_fresh_in_hsubst_iff. unfold frm_is_fresh_in_hsubst. rewrite L.forallb_forall. unfold compose. intros u u_free.
        rewrite negb_true_iff. unfold one_hsubst, cons_hsubst, nil_hsubst. destruct (eqb _ _) as [ | ] eqn:Hobs; rewrite eqb_spec in Hobs.
        { subst u. rewrite in_accum_hatom_in_frm_iff_HC_occurs_in_frm in u_free. pose proof (BG_free q (INCL _ INq)) as Hfree. congruence. }
        { destruct u as [u | u].
          - rewrite in_accum_hatom_in_frm_iff_is_free_in_frm in u_free. rewrite is_free_in_trm_unfold. erewrite Nat.eqb_neq.
            intro Hy. subst u. rewrite <- not_false_iff_true in u_free.
            eapply u_free. eapply last_ivar_frm_gt. red. red.
            transitivity (1 + maxs (map last_ivar_frm ps)).
            + enough (WTS : last_ivar_frm q <= maxs (map last_ivar_frm ps)) by lia.
              eapply in_maxs_ge. rewrite L.in_map_iff. exists q. split; eauto.
            + lia.
          - simpl; reflexivity.
        }
      * red. eapply last_ivar_frm_gt. lia.
      * assert (ALPHA : subst_frm (one_subst x (Var_trm y)) phi ≡ replace_constant_in_frm hc (Var_trm y) (subst_frm (one_subst x c) phi)).
        { eapply alpha_equiv_eq_intro. unfold replace_constant_in_frm. erewrite subst_hsubst_compat_in_frm.
          2: { intros z. reflexivity. }
          erewrite subst_hsubst_compat_in_frm.
          2: { intros z. reflexivity. }
          rewrite <- hsubst_compose_frm_spec. eapply equiv_hsubst_in_frm_implies_hsubst_frm_same. intros [u | u] u_free.
          - unfold to_hsubst, hsubst_compose. unfold one_subst, cons_subst, nil_subst. unfold one_hsubst, cons_hsubst, nil_hsubst.
            destruct (eq_dec u x) as [Hu | Hu].
            + subst u. unfold c. rewrite hsubst_trm_unfold.
              destruct (eqb _ _) as [ | ] eqn: Hobs; rewrite eqb_spec in Hobs; congruence.
            + reflexivity.
          - unfold to_hsubst, hsubst_compose. unfold one_subst, cons_subst, nil_subst. unfold one_hsubst, cons_hsubst, nil_hsubst. rewrite hsubst_trm_unfold.
            destruct (eqb _ _) as [ | ] eqn:Hobs; rewrite eqb_spec in Hobs.
            + rewrite Hobs in u_free. rewrite occurs_free_in_frm_iff in u_free. rewrite in_accum_hatom_in_frm_iff_HC_occurs_in_frm in u_free.
              assert (Hfresh : HC_occurs_in_frm hc phi = false).
              { rewrite <- not_true_iff_false. intro Hocc. pose proof (hc_stage_well_founded hc x phi Hdec hc Hocc) as Hlt. lia. }
              congruence.
            + reflexivity.
        }
        rewrite ALPHA. eapply proves_replace_constant_in_frm. exists ps. split; done.
  - exact PROVE3.
Qed.

Fixpoint AddHenkin_stage_list (X : ensemble (frm L)) (n : nat) (hcs : list Henkin_constants)
  : ensemble (frm L') :=
  match hcs with
  | nil => AddHenkin_stage X n
  | hc :: hcs => E.insert (HenkinAxiom hc) (AddHenkin_stage_list X n hcs)
  end.

Lemma AddHenkin_stage_list_contains_base (X : ensemble (frm L)) (n : nat) (hcs : list Henkin_constants)
  : forall A, A \in AddHenkin_stage X n -> A \in AddHenkin_stage_list X n hcs.
Proof.
  induction hcs as [ | hc hcs IH]; simpl; ii; ss!.
Qed.

Lemma AddHenkin_stage_list_contains_axiom (X : ensemble (frm L)) (n : nat) (hcs : list Henkin_constants)
  : forall hc, L.In hc hcs -> HenkinAxiom hc \in AddHenkin_stage_list X n hcs.
Proof.
  induction hcs as [ | hc' hcs IH]; simpl; intros hc Hin; ss!.
Qed.

Lemma AddHenkin_stage_list_HC_free (X : ensemble (frm L)) (n : nat) (hc : Henkin_constants)
  : forall hcs,
    (~ L.In hc hcs) ->
    (forall hc', L.In hc' hcs -> hc_stage hc' = n) ->
    (hc_stage hc = n) ->
    (forall A, A \in AddHenkin_stage_list X n hcs -> HC_occurs_in_frm hc A = false).
Proof.
  induction hcs as [|hc' hcs IH]; simpl; intros Hnin Hstage Hst A HA.
  - eapply AddHenkin_stage_prev_HC_free; eauto.
  - destruct HA as [-> | HA].
    + eapply HenkinAxiom_at_stage_HC_free; eauto.
    + eapply IH; eauto.
Qed.

Lemma remove_Henkin_axioms_list (X : ensemble (frm L)) (n : nat)
  : forall hcs,
    L.NoDup hcs ->
    (forall hc, L.In hc hcs -> hc_stage hc = n) ->
    inconsistent (AddHenkin_stage_list X n hcs) ->
    inconsistent (AddHenkin_stage X n).
Proof.
  induction hcs as [|hc hcs IH]; simpl; intros Hnodup Hstage Hincon.
  - exact Hincon.
  - inv Hnodup.
    eapply IH.
    + exact H2.
    + intros hc' Hin. eapply Hstage. right. exact Hin.
    + eapply remove_one_Henkin_axiom with (hc := hc).
      * eapply AddHenkin_stage_list_HC_free; eauto.
      * exact Hincon.
Qed.

Lemma collect_stage_axioms (X : ensemble (frm L)) (n : nat)
  : forall ps : list (frm L'),
    (forall p, p \in E.fromList ps -> p \in AddHenkin_stage X (S n)) ->
    exists hcs : list Henkin_constants, L.NoDup hcs /\ (forall hc, L.In hc hcs -> hc_stage hc = n) /\ (forall p, p \in E.fromList ps -> p \in AddHenkin_stage_list X n hcs).
Proof.
  induction ps as [|p ps IH]; intros INCL.
  - exists nil. repeat split.
    + constructor.
    + intros hc Hin. contradiction.
    + intros q Hq. contradiction.
  - assert (INCL_tail : forall q, q \in E.fromList ps -> q \in AddHenkin_stage X (S n)).
    { intros q Hq. eapply INCL. right. exact Hq. }
    destruct (IH INCL_tail) as [hcs [Hnodup [Hstage Hsub]]].
    pose proof (INCL p (or_introl eq_refl)) as Hp.
    destruct Hp as [Hp | Hp].
    + destruct Hp as [hc [Hlt ->]].
      assert (Hcases : hc_stage hc < n \/ hc_stage hc = n) by lia.
      destruct Hcases as [Hlt' | Hst].
      * exists hcs. repeat split; try exact Hnodup; try exact Hstage.
        intros q Hq. s!. destruct Hq as [<- | Hq].
        { eapply AddHenkin_stage_list_contains_base. left. exists hc. split; [exact Hlt' | reflexivity]. }
        { eapply Hsub. exact Hq. }
      * pose proof (in_dec eq_dec hc hcs) as [Hin | Hnin].
        { exists hcs. repeat split; try exact Hnodup; try exact Hstage.
          intros q Hq. s!. destruct Hq as [<- | Hq].
          - eapply AddHenkin_stage_list_contains_axiom. exact Hin.
          - eapply Hsub. exact Hq.
        }
        { exists (hc :: hcs). repeat split.
          - constructor; assumption.
          - intros hc' [-> | Hin].
            + exact Hst.
            + eapply Hstage. exact Hin.
          - intros q Hq. s!. destruct Hq as [<- | Hq].
            + left. reflexivity.
            + right. eapply Hsub. exact Hq.
        }
    + exists hcs. repeat split; try exact Hnodup; try exact Hstage.
      intros q Hq. destruct Hq as [-> | Hq].
      * eapply AddHenkin_stage_list_contains_base. right. exact Hp.
      * eapply Hsub. exact Hq.
Qed.

Lemma AddHenkin_stage_equiconsistent (X : ensemble (frm L)) (n : nat)
  : inconsistent (AddHenkin_stage X n) <-> inconsistent (AddHenkin_stage X (S n)).
Proof.
  split.
  - intros Hincon. rewrite inconsistent_iff in *. eapply extend_proves with (Gamma := AddHenkin_stage X n).
    + intros A HA. destruct HA as [HA | HA].
      * left. destruct HA as [hc [Hlt ->]].
        exists hc. split; [lia | reflexivity].
      * right. exact HA.
    + exact Hincon.
  - intros Hincon.
    rewrite inconsistent_iff in Hincon.
    destruct Hincon as [ps [INCL PF]].
    destruct (collect_stage_axioms X n ps INCL) as [hcs [Hnodup [Hstage Hsub]]].
    assert (PROVE_ps : E.fromList ps ⊢ Bot_frm).
    { exists ps. split; [done | eauto]. }
    assert (PROVE_hcs : AddHenkin_stage_list X n hcs ⊢ Bot_frm).
    { eapply extend_proves with (Gamma := E.fromList ps).
      - intros p Hp. eapply Hsub. exact Hp.
      - exact PROVE_ps.
    }
    assert (INCON_hcs : inconsistent (AddHenkin_stage_list X n hcs)).
    { rewrite inconsistent_iff. exact PROVE_hcs. }
    eapply remove_Henkin_axioms_list; eauto.
Qed.

#[local] Notation embed_frm := (embed_frm (Henkin_constants := Henkin_constants)).

Lemma AddHenkin_stage0_equiconsistent (X : ensemble (frm L))
  : inconsistent (E.image embed_frm X) <-> inconsistent (AddHenkin_stage X 0).
Proof.
  split; intro H.
  - rewrite inconsistent_iff in *. eapply extend_proves; eauto.
    intros A HA. right. exact HA.
  - rewrite inconsistent_iff in *. eapply extend_proves; eauto.
    intros A HA. destruct HA as [HA | HA].
    + destruct HA as [hc [Hlt _]]. lia.
    + exact HA.
Qed.

Lemma AddHenkin_stage_monotone (X : ensemble (frm L)) n m
  (Hle : n <= m)
  : AddHenkin_stage X n \subseteq AddHenkin_stage X m.
Proof.
  intros A HA. destruct HA as [HA | HA].
  - left. destruct HA as [hc [Hlt ->]].
    exists hc. split; [lia | reflexivity].
  - right. exact HA.
Qed.

Lemma AddHenkin_stage_all_equiconsistent (X : ensemble (frm L)) (n : nat)
  : inconsistent (E.image embed_frm X) <-> inconsistent (AddHenkin_stage X n).
Proof.
  induction n as [|n IH].
  - apply AddHenkin_stage0_equiconsistent.
  - destruct IH as [IH1 IH2].
    destruct (AddHenkin_stage_equiconsistent X n) as [H1 H2].
    split; intro H.
    + apply H1. apply IH1. exact H.
    + apply IH2. apply H2. exact H.
Qed.

Inductive HenkinAxiomSet : ensemble (frm L') :=
  | in_HenkinAxiomSet (hc : Henkin_constants)
    : HenkinAxiom hc \in HenkinAxiomSet.

Lemma collect_AddHenkin_stage (X : ensemble (frm L))
  : forall ps : list (frm L'),
    (forall p, p \in E.fromList ps -> p \in E.union HenkinAxiomSet (E.image embed_frm X)) ->
    exists n, forall p, p \in E.fromList ps -> p \in AddHenkin_stage X n.
Proof.
  induction ps as [|p ps IH]; intros INCL.
  - exists 0. intros q Hq. contradiction.
  - assert (INCL_ps : forall q, q \in E.fromList ps -> q \in E.union HenkinAxiomSet (E.image embed_frm X)).
    { intros q Hq. eapply INCL. right. exact Hq. }
    destruct (IH INCL_ps) as [n IHn].
    pose proof (INCL p (or_introl eq_refl)) as Hp.
    destruct Hp as [Hp | Hp].
    + inv Hp. exists (Nat.max n (hc_stage hc + 1)).
      intros q Hq. s!. destruct Hq as [<- | Hq].
      * left. exists hc. split; [lia | reflexivity].
      * eapply AddHenkin_stage_monotone with (n := n); [lia | eapply IHn; eauto].
    + exists n. intros q Hq. destruct Hq as [-> | Hq].
      * right. exact Hp.
      * eapply IHn. exact Hq.
Qed.

Lemma AddHenkin_embed_equiconsistent (X : ensemble (frm L))
  : inconsistent (E.image embed_frm X) <-> inconsistent (E.union HenkinAxiomSet (E.image embed_frm X)).
Proof.
  split.
  - i. rewrite inconsistent_iff in *. eapply extend_proves; eauto. intros A HA. right. exact HA.
  - intros H.
    rewrite inconsistent_iff in H.
    destruct H as [ps [INCL PF]].
    destruct (collect_AddHenkin_stage X ps INCL) as [n Hn].
    assert (Hstage : inconsistent (AddHenkin_stage X n)).
    { rewrite inconsistent_iff.
      exists ps. split.
      - intros p Hp. eapply Hn. exact Hp.
      - exact PF. }
    destruct (AddHenkin_stage_all_equiconsistent X n) as [_ Hback].
    exact (Hback Hstage).
Qed.

Corollary AddHenkin_equiconsistent (X : ensemble (frm L))
  : inconsistent X <-> inconsistent (E.union HenkinAxiomSet (E.image embed_frm X)).
Proof.
  rewrite <- AddHenkin_embed_equiconsistent.
  split; i; rewrite inconsistent_iff in *.
  - set (f := embed_frm). change (E.image f X ⊢ f Bot_frm). unfold f.
    erewrite -> @embed_frm_proves_iff with (Henkin_constants := Henkin_constants).
    now rewrite inconsistent_iff in H.
  - set (f := embed_frm) in H. erewrite <- @embed_frm_proves_iff with (Henkin_constants := Henkin_constants).
    rewrite inconsistent_iff in H. exact H.
Qed.

End HELFER1_ii_a_2.

End HELFER1_ii_a.

End HELFER1_ii.
