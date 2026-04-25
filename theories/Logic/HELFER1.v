Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.Data.Vector.
Require Import Stdlib.Arith.Wf_nat.
Require Export PnV.Logic.BasicFol.
Require Export PnV.Logic.BasicFol2.
Require Export PnV.Logic.HilbertFol.
Require Export PnV.Logic.HilbertFol2.

#[local] Hint Rewrite @eqb_spec@{Set} : simplication_hints.

Module HELFER1_i.

Section HENKIN_INFRASTRUCTURE.

#[local] Notation "x ≠ y" := (~ eq x y) : type_scope.

Section ABSTRACT_HENKIN_CONSTANTS.

Class abstract_Henkin_constants (Henkin_constants : Set) (L : language) {Henkin_constants_hasEqDec : hasEqDec@{Set} Henkin_constants} : Set :=
  { hc_decode (hc : Henkin_constants) : ivar * frm (augmented_language L Henkin_constants)
  ; hc_stage (hc : Henkin_constants) : nat
  ; hc_decode_isSurjective (x : ivar) (theta : frm (augmented_language L Henkin_constants))
    : { hc : Henkin_constants | hc_decode hc = (x, theta) }
  ; hc_new (hcs : list Henkin_constants) (x : ivar) (theta : frm (augmented_language L Henkin_constants))
    : exists hc, hc_decode hc = (x, theta) /\ (HC_occurs_in_frm hc theta = false) /\ (~ L.In hc hcs)
  ; hc_stage_well_founded (hc_k : Henkin_constants) (x_k : ivar) (theta_k : frm (augmented_language L Henkin_constants))
    (H_hc_k : hc_decode hc_k = (x_k, theta_k))
    : forall hc_k', HC_occurs_in_frm hc_k' theta_k = true -> (hc_stage hc_k' < hc_stage hc_k)%nat
  }.

Context {L : language} {Henkin_constants : Set} {Henkin_constants_hasEqDec : hasEqDec Henkin_constants}.

#[local] Notation L' := (augmented_language L Henkin_constants).

Context {AHC : abstract_Henkin_constants Henkin_constants L}.

Lemma hc_fresh (x_n : ivar) (theta_n : frm L')
  (hc_n := proj1_sig (hc_decode_isSurjective x_n theta_n))
  : HC_occurs_in_frm hc_n theta_n = false.
Proof.
  enough (HC_occurs_in_frm hc_n theta_n ≠ true) by now destruct (HC_occurs_in_frm _ _).
  intros H_contra. enough (hc_stage hc_n < hc_stage hc_n)%nat by lia.
  exact (hc_stage_well_founded hc_n x_n theta_n (proj2_sig (hc_decode_isSurjective x_n theta_n)) hc_n H_contra).
Qed.

End ABSTRACT_HENKIN_CONSTANTS.

#[local] Infix "=~=" := is_similar_to : type_scope.

Section CONSTANT_MAPPING.

Context {L : language} {constant_symbols1 : Set} {constant_symbols2 : Set}.

Variable constant_symbols_mapping : constant_symbols1 -> constant_symbols2.

#[local] Notation L1 := (augmented_language L constant_symbols1).

#[local] Notation L2 := (augmented_language L constant_symbols2).

Fixpoint trm_mapping (t : trm L1) : trm L2 :=
  match t with
  | Var_trm x => @Var_trm L2 x
  | Fun_trm f ts => @Fun_trm L2 f (@trms_mapping (function_arity_table L2 f) ts)
  | Con_trm c' =>
    match c' with
    | inl c => @Con_trm L2 (inl c)
    | inr hc => @Con_trm L2 (inr (constant_symbols_mapping hc))
    end
  end
with trms_mapping {n : nat} (ts : trms L1 n) : trms L2 n :=
  match ts with
  | O_trms => @O_trms L2
  | S_trms n t ts => @S_trms L2 n (trm_mapping t) (trms_mapping ts)
  end.

Fixpoint frm_mapping (p : frm L1) : frm L2 :=
  match p with
  | Eqn_frm t1 t2 => @Eqn_frm L2 (trm_mapping t1) (trm_mapping t2)
  | Rel_frm R ts => @Rel_frm L2 R (@trms_mapping (relation_arity_table L2 R) ts)
  | Neg_frm p1 => @Neg_frm L2 (frm_mapping p1)
  | Imp_frm p1 p2 => @Imp_frm L2 (frm_mapping p1) (frm_mapping p2)
  | All_frm y p1 => @All_frm L2 y (frm_mapping p1)
  end.

End CONSTANT_MAPPING.

Section STAGED_HENKIN_CONSTANTS.

Variable L : language.

Fixpoint Henkin_constants_stage (k : nat) : Set :=
  match k with
  | O => void
  | S k' => Henkin_constants_stage k' + (ivar * frm (augmented_language L (Henkin_constants_stage k')))
  end.

Definition L_stage (k : nat) : language :=
  augmented_language L (Henkin_constants_stage k).

Definition Henkin_constants : Set :=
  { k : nat & ivar * frm (L_stage k) }.

#[local] Notation L_infty := (augmented_language L Henkin_constants).

Fixpoint hc_k_to_hc_infty (k : nat) : Henkin_constants_stage k -> Henkin_constants :=
  match k as k return Henkin_constants_stage k -> Henkin_constants with
  | O => Empty_set_rect _
  | S k' => fun c =>
    match c with
    | inl old => hc_k_to_hc_infty k' old
    | inr xp => @existT _ _ k' xp
    end
  end.

Definition L_k_to_L_infty (k : nat) : frm (L_stage k) -> frm L_infty :=
  frm_mapping (hc_k_to_hc_infty k).

Definition hc_decode_impl (hc : Henkin_constants) : ivar * frm L_infty :=
  let '(@existT _ _ k (x, theta)) := hc in
  (x, L_k_to_L_infty k theta).

Fixpoint max_hc_stage_trm (t : trm L_infty) : nat :=
  match t with
  | Var_trm x => O
  | Fun_trm f ts => max_hc_stage_trms ts
  | Con_trm c =>
    match c with
    | inl c' => O
    | inr hc => S (projT1 hc)
    end
  end
with max_hc_stage_trms {n : nat} (ts : trms L_infty n) : nat :=
  match ts with
  | O_trms => O
  | S_trms n t ts => Nat.max (max_hc_stage_trm t) (max_hc_stage_trms ts)
  end.

Fixpoint max_hc_stage_frm (p : frm L_infty) : nat :=
  match p with
  | Rel_frm R ts => max_hc_stage_trms ts
  | Eqn_frm t1 t2 => Nat.max (max_hc_stage_trm t1) (max_hc_stage_trm t2)
  | Neg_frm p1 => max_hc_stage_frm p1
  | Imp_frm p1 p2 => Nat.max (max_hc_stage_frm p1) (max_hc_stage_frm p2)
  | All_frm y p1 => max_hc_stage_frm p1
  end.

Fixpoint max_hc_stage_list (hcs : list Henkin_constants) : nat :=
  match hcs with
  | nil => O
  | hc :: hcs => Nat.max (projT1 hc + 1) (max_hc_stage_list hcs)
  end.

Variable Henkin_constants_hasEqDec : hasEqDec Henkin_constants.

Fixpoint occurs_stage_le_trm (t : trm L_infty)
  : forall hc : Henkin_constants, HC_occurs_in_trm hc t = true -> projT1 hc < max_hc_stage_trm t
with occurs_stage_le_trms (n : nat) (ts : trms L_infty n)
  : forall hc : Henkin_constants, HC_occurs_in_trms hc ts = true -> projT1 hc < max_hc_stage_trms ts.
Proof.
  - destruct t as [x | f ts | c]; intros hc H; s!.
    + congruence.
    + exact (occurs_stage_le_trms _ ts hc H).
    + destruct c as [c | hc'].
      * congruence.
      * s!. subst hc'. econs.
  - destruct ts as [ | n t ts]; simpl; intros hc H; s!.
    + congruence.
    + destruct H as [H | H].
      * enough (S (projT1 hc) <= max_hc_stage_trm t) by lia.
        exact (occurs_stage_le_trm t hc H).
      * enough (S (projT1 hc) <= max_hc_stage_trms ts) by lia.
        exact (occurs_stage_le_trms n ts hc H).
Defined.

Fixpoint occurs_stage_le_frm (p : frm L_infty)
  : forall hc : Henkin_constants, HC_occurs_in_frm hc p = true -> projT1 hc < max_hc_stage_frm p.
Proof.
  destruct p as [R ts | t1 t2 | p1 | p1 p2 | y p1]; intros hc H; s!.
  - exact (occurs_stage_le_trms _ ts hc H).
  - destruct H as [H | H].
    + enough (S (projT1 hc) <= max_hc_stage_trm t1) by lia. exact (occurs_stage_le_trm t1 hc H).
    + enough (S (projT1 hc) <= max_hc_stage_trm t2) by lia. exact (occurs_stage_le_trm t2 hc H).
  - exact (occurs_stage_le_frm p1 hc H).
  - destruct H as [H | H].
    + enough (S (projT1 hc) <= max_hc_stage_frm p1) by lia. exact (occurs_stage_le_frm p1 hc H).
    + enough (S (projT1 hc) <= max_hc_stage_frm p2) by lia. exact (occurs_stage_le_frm p2 hc H).
  - exact (occurs_stage_le_frm p1 hc H).
Defined.

Lemma in_list_stage_le (hcs : list Henkin_constants)
  : forall hc : Henkin_constants, L.In hc hcs -> projT1 hc < max_hc_stage_list hcs.
Proof.
  induction hcs as [ | hc' hcs IH]; simpl; intros hc.
  - intros [].
  - intros [<- | Hin].
    + lia.
    + pose proof (IH hc Hin) as HH. lia.
Qed.

Fixpoint hc_k_to_hc_infty_stage_lt (k : nat)
  : forall c : Henkin_constants_stage k, (projT1 (hc_k_to_hc_infty k c) < k)%nat.
Proof.
  destruct k as [ | k']; intros c.
  - destruct c.
  - destruct c as [old | xp]; simpl.
    + enough (projT1 (hc_k_to_hc_infty k' old) < k') by lia. exact (hc_k_to_hc_infty_stage_lt k' old).
    + lia.
Defined.

Fixpoint max_stage_L_k_to_L_infty_trm_le (k : nat) (t : trm (L_stage k))
  : max_hc_stage_trm (trm_mapping (hc_k_to_hc_infty k) t) <= k
with max_stage_L_k_to_L_infty_trms_le (k : nat) (n : nat) (ts : trms (L_stage k) n)
  : max_hc_stage_trms (trms_mapping (hc_k_to_hc_infty k) ts) <= k.
Proof.
  - destruct t as [x | f ts | c]; s!.
    + lia.
    + exact (max_stage_L_k_to_L_infty_trms_le k _ ts).
    + destruct c as [c | hc]; simpl.
      * lia.
      * enough (projT1 (hc_k_to_hc_infty k hc) < k) by lia. exact (hc_k_to_hc_infty_stage_lt k hc).
  - destruct ts as [ | n t ts]; s!.
    + lia.
    + pose proof (HH1 := max_stage_L_k_to_L_infty_trm_le k t).
      pose proof (HH2 := max_stage_L_k_to_L_infty_trms_le k n ts).
      lia.
Defined.

Fixpoint max_stage_L_k_to_L_infty_frm_le (k : nat) (p : frm (L_stage k))
  : max_hc_stage_frm (L_k_to_L_infty k p) <= k.
Proof.
  destruct p as [R ts | t1 t2 | p1 | p1 p2 | y p1]; s!.
  - exact (max_stage_L_k_to_L_infty_trms_le k _ ts).
  - pose proof (HH1 := max_stage_L_k_to_L_infty_trm_le k t1).
    pose proof (HH2 := max_stage_L_k_to_L_infty_trm_le k t2).
    lia.
  - exact (max_stage_L_k_to_L_infty_frm_le k p1).
  - pose proof (HH1 := max_stage_L_k_to_L_infty_frm_le k p1).
    pose proof (HH2 := max_stage_L_k_to_L_infty_frm_le k p2).
    lia.
  - exact (max_stage_L_k_to_L_infty_frm_le k p1).
Defined.

Fixpoint hc_infty_to_hc_k (k : nat) (hc : Henkin_constants) : option (Henkin_constants_stage k) :=
  match k as k return option (Henkin_constants_stage k) with
  | O => None
  | S k' =>
    let '(@existT _ _ j xp) := hc in
    match Nat.eq_dec j k' with
    | left H_EQ =>
      match H_EQ with
      | eq_refl => Some (inr xp)
      end
    | right _ =>
      match hc_infty_to_hc_k k' hc with
      | Some old => Some (inl old)
      | None => None
      end
    end
  end.

Lemma hc_infty_to_hc_k_total (k : nat)
  : forall hc : Henkin_constants, S (projT1 hc) <= k -> { c : Henkin_constants_stage k | hc_infty_to_hc_k k hc = Some c }.
Proof.
  destruct hc as [j xp]. revert j xp.
  induction k as [ | k IH]; simpl; intros j xp Hle.
  - lia.
  - destruct (Nat.eq_dec j k) as [-> | Hneq].
    + eexists. reflexivity.
    + assert (HH : S j <= k) by lia.
      apply IH with (j := j) (xp := xp) in HH.
      destruct HH as [c Hc]. rewrite Hc. eauto.
Qed.

Lemma hc_infty_to_hc_k_sound (k : nat) (hc : Henkin_constants) (c : Henkin_constants_stage k)
  (Hc : hc_infty_to_hc_k k hc = Some c)
  : hc_k_to_hc_infty k c = hc.
Proof.
  destruct hc as [j xp]. revert j xp c Hc.
  induction k as [ | k IH]; intros j xp c Hc; simpl in *; ss!.
  destruct (Nat.eq_dec j k) as [Heq | Hneq].
  - subst. now inv Hc.
  - destruct (hc_infty_to_hc_k k (@existT _ _ j xp)) eqn: Hrec; try congruence.
    inv Hc; eauto.
Qed.

Definition const_infty_to_k (k : nat) (c : constant_symbols L_infty) : option (constant_symbols (L_stage k)) :=
  match c with
  | inl c => Some (inl c)
  | inr hc =>
    match hc_infty_to_hc_k k hc with
    | Some hc_k => Some (inr hc_k)
    | None => None
    end
  end.

Lemma const_infty_to_k_total (k : nat) (c : constant_symbols L_infty)
  (Hc : match c with inl _ => True | inr hc => S (projT1 hc) <= k end)
  : { c_k : constant_symbols (L_stage k) | const_infty_to_k k c = Some c_k }.
Proof.
  destruct c as [c0 | hc].
  - exists (inl c0). reflexivity.
  - simpl. pose proof (hc_infty_to_hc_k_total k hc Hc) as [hc_k Hhc].
    exists (inr hc_k). now rewrite Hhc.
Qed.

Lemma const_infty_to_k_sound (k : nat) (c : constant_symbols L_infty) (c_k : constant_symbols (L_stage k))
  (H_c_k : const_infty_to_k k c = Some c_k)
  : match c_k with inl c0 => c = inl c0 | inr hc_k => c = inr (hc_k_to_hc_infty k hc_k) end.
Proof.
  destruct c as [c | hc].
  - simpl in *. now inv H_c_k.
  - simpl in *. destruct (hc_infty_to_hc_k k hc) eqn:Hhc; try congruence.
    inv H_c_k. now rewrite (hc_infty_to_hc_k_sound k hc h Hhc).
Qed.

Fixpoint L_infty_to_L_k_trm_bound (t : trm L_infty) {struct t}
  : forall k : nat, max_hc_stage_trm t <= k -> { t_k : trm (L_stage k) | t = trm_mapping (hc_k_to_hc_infty k) t_k }
with L_infty_to_L_k_trms_bound (n : nat) (ts : trms L_infty n) {struct ts}
  : forall k : nat, max_hc_stage_trms ts <= k -> { ts_k : trms (L_stage k) n | ts = trms_mapping (hc_k_to_hc_infty k) ts_k }.
Proof.
  - destruct t as [x | f ts | c]; simpl; intros k Hk.
    + exists (@Var_trm (L_stage k) x). reflexivity.
    + destruct (L_infty_to_L_k_trms_bound _ ts k Hk) as [ts_k Hts].
      exists (@Fun_trm (L_stage k) f ts_k). simpl. subst ts. reflexivity.
    + destruct c as [c | hc]; simpl.
      * exists (@Con_trm (L_stage k) (inl c)). simpl. reflexivity.
      * pose proof (const_infty_to_k_total k (inr hc) Hk) as [c_k Hc].
        exists (@Con_trm (L_stage k) c_k). simpl.
        pose proof (const_infty_to_k_sound k (inr hc) c_k Hc) as HH.
        destruct c_k; congruence.
  - destruct ts as [ | n t ts]; simpl; intros k Hk.
    + exists (@O_trms (L_stage k)). reflexivity.
    + assert (Ht : max_hc_stage_trm t <= k) by lia.
      assert (Hts : max_hc_stage_trms ts <= k) by lia.
      pose proof (L_infty_to_L_k_trm_bound t k Ht) as [t_k Ht_eq].
      destruct (L_infty_to_L_k_trms_bound _ ts k Hts) as [ts_k Hts_eq].
      exists (@S_trms (L_stage k) n t_k ts_k). simpl. congruence.
Qed.

Fixpoint L_infty_to_L_k_frm_bound (p : frm L_infty)
  : forall k : nat, max_hc_stage_frm p <= k -> { p_k : frm (L_stage k) | p = L_k_to_L_infty k p_k }.
Proof.
  destruct p as [R ts | t1 t2 | p1 | p1 p2 | y p1]; simpl; intros k Hk.
  - pose proof (L_infty_to_L_k_trms_bound _ ts k Hk) as [ts_k Hts].
    exists (@Rel_frm (L_stage k) R ts_k). simpl. subst ts. reflexivity.
  - assert (Ht1 : max_hc_stage_trm t1 <= k) by lia.
    assert (Ht2 : max_hc_stage_trm t2 <= k) by lia.
    pose proof (L_infty_to_L_k_trm_bound t1 k Ht1) as [t1_k H1].
    pose proof (L_infty_to_L_k_trm_bound t2 k Ht2) as [t2_k H2].
    exists (Eqn_frm t1_k t2_k). simpl. congruence.
  - pose proof (L_infty_to_L_k_frm_bound p1 k Hk) as [p1_k H1].
    exists (@Neg_frm (L_stage k) p1_k). simpl. congruence.
  - assert (H1b : max_hc_stage_frm p1 <= k) by lia.
    assert (H2b : max_hc_stage_frm p2 <= k) by lia.
    pose proof (L_infty_to_L_k_frm_bound p1 k H1b) as [p1_k H1].
    pose proof (L_infty_to_L_k_frm_bound p2 k H2b) as [p2_k H2].
    exists (@Imp_frm (L_stage k) p1_k p2_k). simpl. congruence.
  - pose proof (L_infty_to_L_k_frm_bound p1 k Hk) as [p1_k H1].
    exists (@All_frm (L_stage k) y p1_k). simpl. congruence.
Defined.

Lemma L_infty_to_L_k_frm_above (k0 : nat) (theta : frm L_infty)
  : exists k, k0 <= k /\ (exists theta_k : frm (L_stage k), theta = L_k_to_L_infty k theta_k).
Proof.
  exists (Nat.max k0 (max_hc_stage_frm theta)). split; [lia | ].
  pose proof (L_infty_to_L_k_frm_bound theta _ (Nat.le_max_r k0 (max_hc_stage_frm theta))) as [theta_k Htheta].
  now exists theta_k.
Qed.

End STAGED_HENKIN_CONSTANTS.

Section EQDEC_INSTANCES.

#[local] Obligation Tactic := idtac.

Context {L : language} {function_symbols_hasEqDec : hasEqDec@{Set} L.(function_symbols)} {constant_symbols_hasEqDec : hasEqDec@{Set} L.(constant_symbols)} {relation_symbols_hasEqDec : hasEqDec@{Set} L.(relation_symbols)}.

#[global]
Instance Henkin_constants_stage_hasEqDec (n : nat)
  : hasEqDec (Henkin_constants_stage L n).
Proof.
  induction n as [ | n IHn]; simpl.
  - red; decide equality.
  - eapply sum_hasEqDec.
    + exact IHn.
    + eapply pair_hasEqdec.
      { exact ivar_hasEqDec. }
      { eapply frm_hasEqDec.
        - exact function_symbols_hasEqDec.
        - eapply sum_hasEqDec.
          + exact constant_symbols_hasEqDec.
          + exact IHn.
        - exact relation_symbols_hasEqDec.
      }
Defined.

#[global]
Instance Henkin_constants_hasEqDec
  : hasEqDec (Henkin_constants L).
Proof.
  eapply sigT_hasEqDec.
  - exact nat_hasEqDec.
  - induction a as [ | n IHn].
    + unfold L_stage. simpl. eapply pair_hasEqdec.
      * exact ivar_hasEqDec.
      * eapply frm_hasEqDec.
        { unfold augmented_language. simpl. exact function_symbols_hasEqDec. }
        { unfold augmented_language. simpl. eapply sum_hasEqDec; [exact constant_symbols_hasEqDec | red; decide equality]. }
        { unfold augmented_language. simpl. exact relation_symbols_hasEqDec. }
    + unfold L_stage in *. simpl. eapply pair_hasEqdec.
      * exact ivar_hasEqDec.
      * eapply frm_hasEqDec.
        { unfold augmented_language. simpl. exact function_symbols_hasEqDec. }
        { unfold augmented_language. simpl.
          eapply sum_hasEqDec; [exact constant_symbols_hasEqDec | ].
          eapply sum_hasEqDec; [eapply Henkin_constants_stage_hasEqDec | ].
          exact IHn. 
        }
        { unfold augmented_language. simpl. exact relation_symbols_hasEqDec. }
Defined.

#[global, refine]
Instance abstract_Henkin_constants_instance : abstract_Henkin_constants (Henkin_constants L) L :=
  { hc_decode := hc_decode_impl L
  ; hc_stage := @projT1 nat (fun k => ivar * frm (L_stage L k))%type
  ; hc_decode_isSurjective := _
  ; hc_new := _
  ; hc_stage_well_founded := _
  }.
Proof.
  - intros x theta. pose (k := max_hc_stage_frm L theta).
    pose proof (L_infty_to_L_k_frm_bound L _ theta k (le_n _)) as [theta_k Htheta].
    exists (@existT _ _ k (x, theta_k)). simpl. now rewrite Htheta.
  - intros hcs x theta.
    pose (k := Nat.max (max_hc_stage_frm L theta) (max_hc_stage_list L hcs)).
    pose proof (L_infty_to_L_k_frm_bound L _ theta k) as [theta_k Htheta].
    unfold k. lia.
    + exists (@existT _ _ k (x, theta_k)); splits.
      * simpl. now rewrite Htheta.
      * rewrite <- not_true_iff_false. intros Hocc.
        pose proof (occurs_stage_le_frm L _ theta (@existT _ _ k (x, theta_k)) Hocc) as H1.
        simpl in H1. unfold k in H1. lia.
      * intros Hin.
        pose proof (in_list_stage_le L _ (@existT _ _ k (x, theta_k)) Hin) as H1.
        simpl in H1. unfold k in H1. lia.
  - intros hc_k x_k theta_k H_hc_k hc_k' Hocc.
    destruct hc_k as [k [x theta]]. simpl in H_hc_k. inv H_hc_k.
    pose proof (occurs_stage_le_frm L _ (L_k_to_L_infty L k theta) hc_k' Hocc) as H1.
    pose proof (max_stage_L_k_to_L_infty_frm_le L _ theta) as H2.
    simpl in *. lia.
Qed.

End EQDEC_INSTANCES.

End HENKIN_INFRASTRUCTURE.

Section HSUBST.

#[local] Notation "x ≠ y" := (~ eq x y).

Context {L : language} {Henkin_constants : Set} {Henkin_constants_hasEqDec : hasEqDec Henkin_constants}.

#[local] Notation L' := (augmented_language L Henkin_constants).

Lemma HC_occurs_in_embed_trm_false (t : trm L)
  : forall hc : Henkin_constants, HC_occurs_in_trm hc (embed_trm t) = false
with HC_occurs_in_embed_trms_false n (ts : trms L n)
  : forall hc : Henkin_constants, HC_occurs_in_trms hc (embed_trms ts) = false.
Proof.
  - destruct t as [x | f ts | c]; simpl; intros hc; s!.
    + reflexivity.
    + eapply HC_occurs_in_embed_trms_false.
    + reflexivity.
  - destruct ts as [ | n t ts]; simpl; intros hc; s!.
    + reflexivity.
    + split.
      * eapply HC_occurs_in_embed_trm_false.
      * eapply HC_occurs_in_embed_trms_false.
Qed.

#[local] Hint Rewrite HC_occurs_in_embed_trm_false HC_occurs_in_embed_trms_false : simplication_hints.

Lemma HC_occurs_in_embed_frm_false (A : frm L)
  : forall hc : Henkin_constants, HC_occurs_in_frm hc (embed_frm A) = false.
Proof.
  induction A; simpl; intros hc; ss!.
Qed.

#[local] Hint Rewrite HC_occurs_in_embed_frm_false : simplication_hints.

#[local] Notation hatom := (ivar + Henkin_constants)%type.

#[local] Notation hsubst := (hatom -> trm L').

#[local] Open Scope list_scope.

Definition to_hsubst (s : subst L') : hsubst :=
  fun z : hatom =>
  match z with
  | inl x => s x
  | inr c => @Con_trm L' (inr c)
  end.

Definition from_hsubst (sigma : hsubst) : subst L' :=
  fun z : ivar => sigma (inl z).

Fixpoint accum_hatom_in_trm (t : trm L') : list hatom :=
  match t with
  | Var_trm x => [inl x]
  | Fun_trm f ts => accum_hatom_in_trms ts
  | Con_trm c =>
    match c with
    | inl cc => []
    | inr hc => [inr hc]
    end
  end
with accum_hatom_in_trms {n : nat} (ts : trms L' n) : list hatom :=
  match ts with
  | O_trms => []
  | S_trms n t ts => accum_hatom_in_trm t ++ accum_hatom_in_trms ts
  end.

Lemma in_accum_hatom_in_trm_iff_is_free_in_trm x (t : trm L')
  : L.In (inl x) (accum_hatom_in_trm t) <-> is_free_in_trm x t = true
with in_accum_hatom_in_trms_iff_is_free_in_trms n x (ts : trms L' n)
  : L.In (inl x) (accum_hatom_in_trms ts) <-> is_free_in_trms x ts = true.
Proof.
  - clear in_accum_hatom_in_trm_iff_is_free_in_trm; revert x. trm_ind t; intros z.
    + s!. firstorder congruence.
    + simpl. rewrite is_free_in_trm_unfold. eapply in_accum_hatom_in_trms_iff_is_free_in_trms.
    + destruct c as [cc | hc]; ss!.
  - clear in_accum_hatom_in_trms_iff_is_free_in_trms; revert x. trms_ind ts; intros z.
    + s!. clear. firstorder congruence.
    + simpl. rewrite is_free_in_trms_unfold. rewrite orb_true_iff. rewrite <- IH with (x := z). rewrite L.in_app_iff. rewrite in_accum_hatom_in_trm_iff_is_free_in_trm. reflexivity.
Qed.

Lemma in_accum_hatom_in_trm_iff_HC_occurs_in_trm hc (t : trm L')
  : L.In (inr hc) (accum_hatom_in_trm t) <-> HC_occurs_in_trm hc t = true
with in_accum_hatom_in_trms_iff_HC_occurs_in_trms n hc (ts : trms L' n)
  : L.In (inr hc) (accum_hatom_in_trms ts) <-> HC_occurs_in_trms hc ts = true.
Proof.
  - clear in_accum_hatom_in_trm_iff_HC_occurs_in_trm; revert hc. trm_ind t; intros z.
    + s!. firstorder congruence.
    + s!. eapply in_accum_hatom_in_trms_iff_HC_occurs_in_trms.
    + clear. destruct c as [hc | cc]; ss!.
  - clear in_accum_hatom_in_trms_iff_HC_occurs_in_trms; revert hc. trms_ind ts; intros z.
    + s!. firstorder congruence.
    + s!. rewrite IH. rewrite in_accum_hatom_in_trm_iff_HC_occurs_in_trm. reflexivity.
Qed.

Fixpoint accum_hatom_in_frm (p : frm L') : list hatom :=
  match p with
  | Rel_frm R ts => accum_hatom_in_trms ts
  | Eqn_frm t1 t2 => accum_hatom_in_trm t1 ++ accum_hatom_in_trm t2
  | Neg_frm p1 => accum_hatom_in_frm p1
  | Imp_frm p1 p2 => accum_hatom_in_frm p1 ++ accum_hatom_in_frm p2
  | All_frm y p1 => L.remove (eq_dec@{Set} (hasEqDec := @sum_hasEqDec ivar Henkin_constants nat_hasEqDec Henkin_constants_hasEqDec)) (inl y) (accum_hatom_in_frm p1)
  end.

Lemma in_accum_hatom_in_frm_iff_is_free_in_frm x (p : frm L')
  : L.In (inl x) (accum_hatom_in_frm p) <-> is_free_in_frm x p = true.
Proof.
  revert x. frm_ind p; i.
  - simpl. eapply in_accum_hatom_in_trms_iff_is_free_in_trms.
  - simpl. rewrite orb_true_iff. do 2 rewrite <- in_accum_hatom_in_trm_iff_is_free_in_trm. rewrite L.in_app_iff. reflexivity.
  - ss!.
  - ss!.
  - ss!.
Qed.

#[local] Hint Rewrite in_accum_hatom_in_trm_iff_HC_occurs_in_trm in_accum_hatom_in_trms_iff_HC_occurs_in_trms : simplication_hints.

Lemma in_accum_hatom_in_frm_iff_HC_occurs_in_frm hc (p : frm L')
  : L.In (inr hc) (accum_hatom_in_frm p) <-> HC_occurs_in_frm hc p = true.
Proof.
  revert hc. frm_ind p; done!.
Qed.

#[local] Hint Rewrite in_accum_hatom_in_frm_iff_HC_occurs_in_frm : simplication_hints.

Definition hchi_frm (sigma : hsubst) (p : frm L') : ivar :=
  1 + 36 * maxs (L.map (last_ivar_trm ∘ sigma)%prg (accum_hatom_in_frm p)).

Definition nil_hsubst : hsubst :=
  fun z : hatom =>
  match z with
  | inl x => Var_trm x
  | inr c => @Con_trm L' (inr c)
  end.

Lemma to_hsubst_nil_subst
  : forall z, to_hsubst nil_subst z = nil_hsubst z.
Proof.
  intros [z | z]; reflexivity.
Qed.

Definition cons_hsubst (x : hatom) (t : trm L') (sigma : hsubst) : hsubst :=
  fun z : hatom => if Prelude.eqb@{Set} (hasEqDec := @sum_hasEqDec ivar Henkin_constants nat_hasEqDec Henkin_constants_hasEqDec) z x then t else sigma z.

Lemma to_hsubst_cons_subst (x : ivar) (t : trm L') (s : subst L')
  : forall z, to_hsubst (cons_subst x t s) z = cons_hsubst (inl x) t (to_hsubst s) z.
Proof.
  intros [z | z]; unfold to_hsubst, cons_hsubst, nil_hsubst, cons_subst, nil_subst.
  - destruct (eq_dec _ _) as [EQ | NE], (eqb _ _) as [ | ] eqn: H_OBS; done!.
  - destruct (eqb (inr z) (inl x)) as [ | ] eqn: H_OBS; done!.
Qed.

Definition one_hsubst (x : hatom) (t : trm L') : hsubst :=
  cons_hsubst x t nil_hsubst.

Lemma to_hsubst_one_subst (x : ivar) (t : trm L')
  : forall z, to_hsubst (one_subst x t) z = one_hsubst (inl x) t z.
Proof.
  intros [z | z]; unfold to_hsubst, one_hsubst, cons_hsubst, nil_hsubst, one_subst, cons_subst, nil_subst.
  - destruct (eq_dec z x) as [EQ | NE], (eqb (inl z) (inl x)) as [ | ] eqn: H_OBS; done!.
  - destruct (eqb (inr z) (inl x)) as [ | ] eqn: H_OBS; done!.
Qed.

Fixpoint hsubst_trm (sigma : hsubst) (t : trm L') : trm L' :=
  match t with
  | Var_trm x => sigma (inl x)
  | Fun_trm f ts => Fun_trm f (hsubst_trms sigma ts)
  | Con_trm c =>
    match c with
    | inl cc => Con_trm c
    | inr hc => sigma (inr hc)
    end
  end
with hsubst_trms {n : nat} (sigma : hsubst) (ts : trms L' n) : trms L' n :=
  match ts with
  | O_trms => O_trms
  | S_trms n t ts => S_trms n (hsubst_trm sigma t) (hsubst_trms sigma ts)
  end.

Fixpoint hsubst_frm (sigma : hsubst) (p : frm L') : frm L' :=
  let chi : ivar := hchi_frm sigma p in
  match p with
  | Rel_frm R ts => Rel_frm R (hsubst_trms sigma ts)
  | Eqn_frm t1 t2 => Eqn_frm (hsubst_trm sigma t1) (hsubst_trm sigma t2)
  | Neg_frm p1 => Neg_frm (hsubst_frm sigma p1)
  | Imp_frm p1 p2 => Imp_frm (hsubst_frm sigma p1) (hsubst_frm sigma p2)
  | All_frm y p1 => All_frm chi (hsubst_frm (cons_hsubst (inl y) (Var_trm chi) sigma) p1)
  end.

Lemma hsubst_trm_unfold (sigma : hsubst) (t : trm L') :
  hsubst_trm sigma t =
  match t with
  | Var_trm x => sigma (inl x)
  | Fun_trm f ts => Fun_trm f (hsubst_trms sigma ts)
  | Con_trm c =>
    match c with
    | inl cc => Con_trm c
    | inr hc => sigma (inr hc)
    end
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma hsubst_trms_unfold n (sigma : hsubst) (ts : trms L' n) :
  hsubst_trms sigma ts =
  match ts with
  | O_trms => O_trms
  | S_trms n t ts => S_trms n (hsubst_trm sigma t) (hsubst_trms sigma ts)
  end.
Proof.
  destruct ts; reflexivity.
Defined.

Lemma hsubst_frm_unfold (sigma : hsubst) (p : frm L') :
  hsubst_frm sigma p =
  match p with
  | Rel_frm R ts => Rel_frm R (hsubst_trms sigma ts)
  | Eqn_frm t1 t2 => Eqn_frm (hsubst_trm sigma t1) (hsubst_trm sigma t2)
  | Neg_frm p1 => Neg_frm (hsubst_frm sigma p1)
  | Imp_frm p1 p2 => Imp_frm (hsubst_frm sigma p1) (hsubst_frm sigma p2)
  | All_frm y p1 =>
    let z : ivar := hchi_frm sigma p in
    All_frm z (hsubst_frm (cons_hsubst (inl y) (Var_trm z) sigma) p1)
  end.
Proof.
  destruct p; reflexivity.
Defined.

Definition hsubst_compose (sigma : hsubst) (sigma' : hsubst) : hsubst :=
  fun z : hatom => hsubst_trm sigma' (sigma z).

Fixpoint occurs_free_in_trm (z : hatom) (t : trm L') : bool :=
  match t with
  | Var_trm x => Prelude.eqb@{Set} (hasEqDec := @sum_hasEqDec ivar Henkin_constants nat_hasEqDec Henkin_constants_hasEqDec) z (inl x)
  | Fun_trm f ts => occurs_free_in_trms z ts
  | Con_trm c =>
    match c with
    | inl cc => false
    | inr hc => Prelude.eqb@{Set} (hasEqDec := @sum_hasEqDec ivar Henkin_constants nat_hasEqDec Henkin_constants_hasEqDec) z (inr hc)
    end
  end
with occurs_free_in_trms {n : nat} (z : hatom) (ts : trms L' n) : bool :=
  match ts with
  | O_trms => false
  | S_trms n t ts => occurs_free_in_trm z t || occurs_free_in_trms z ts
  end.

Fixpoint occurs_free_in_frm (z : hatom) (p : frm L') : bool :=
  match p with
  | Rel_frm R ts => occurs_free_in_trms z ts
  | Eqn_frm t1 t2 => occurs_free_in_trm z t1 || occurs_free_in_trm z t2
  | Neg_frm p1 => occurs_free_in_frm z p1
  | Imp_frm p1 p2 => occurs_free_in_frm z p1 || occurs_free_in_frm z p2
  | All_frm y p1 => occurs_free_in_frm z p1 && negb (Prelude.eqb@{Set} (hasEqDec := @sum_hasEqDec ivar Henkin_constants nat_hasEqDec Henkin_constants_hasEqDec) z (inl y))
  end.

Lemma occurs_free_in_trm_unfold (z : hatom) (t : trm L') :
  occurs_free_in_trm z t =
  match t with
  | Var_trm x => Prelude.eqb@{Set} (hasEqDec := @sum_hasEqDec ivar Henkin_constants nat_hasEqDec Henkin_constants_hasEqDec) z (inl x)
  | Fun_trm f ts => occurs_free_in_trms z ts
  | Con_trm c =>
    match c with
    | inl cc => false
    | inr hc => Prelude.eqb@{Set} (hasEqDec := @sum_hasEqDec ivar Henkin_constants nat_hasEqDec Henkin_constants_hasEqDec) z (inr hc)
    end
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma occurs_free_in_trms_unfold n (z : hatom) (ts : trms L' n) :
  occurs_free_in_trms z ts =
  match ts with
  | O_trms => false
  | S_trms n t ts => occurs_free_in_trm z t || occurs_free_in_trms z ts
  end.
Proof.
  destruct ts; reflexivity.
Defined.

Lemma occurs_free_in_frm_unfold (z : hatom) (p : frm L') :
  occurs_free_in_frm z p =
  match p with
  | Rel_frm R ts => occurs_free_in_trms z ts
  | Eqn_frm t1 t2 => occurs_free_in_trm z t1 || occurs_free_in_trm z t2
  | Neg_frm p1 => occurs_free_in_frm z p1
  | Imp_frm p1 p2 => occurs_free_in_frm z p1 || occurs_free_in_frm z p2
  | All_frm y p1 => occurs_free_in_frm z p1 && negb (Prelude.eqb@{Set} (hasEqDec := @sum_hasEqDec ivar Henkin_constants nat_hasEqDec Henkin_constants_hasEqDec) z (inl y))
  end.
Proof.
  destruct p; reflexivity.
Defined.

Lemma occurs_free_in_trm_iff (z : hatom) (t : trm L')
  : occurs_free_in_trm z t = true <-> In z (accum_hatom_in_trm t)
with occurs_free_in_trms_iff n (z : hatom) (ts : trms L' n)
  : occurs_free_in_trms z ts = true <-> In z (accum_hatom_in_trms ts).
Proof.
  - clear occurs_free_in_trm_iff. revert z; trm_ind t; simpl; i.
    + rewrite eqb_eq. done!.
    + eapply occurs_free_in_trms_iff.
    + destruct c as [cc | hc]; simpl.
      * firstorder congruence.
      * rewrite eqb_eq. clear. firstorder.
  - clear occurs_free_in_trms_iff. revert z; trms_ind ts; simpl; i.
    + done!.
    + done!.
Qed.

#[local] Hint Rewrite occurs_free_in_trm_iff occurs_free_in_trms_iff : simplication_hints.

Lemma occurs_free_in_frm_iff (z : hatom) (p : frm L')
  : occurs_free_in_frm z p = true <-> In z (accum_hatom_in_frm p).
Proof.
  revert z. frm_ind p; done!.
Qed.

Lemma hchi_frm_not_free (sigma : hsubst) (p : frm L') (z : hatom)
  (OCCURS : occurs_free_in_frm z p = true)
  : is_free_in_trm (hchi_frm sigma p) (sigma z) = false.
Proof.
  eapply last_ivar_trm_gt. unfold hchi_frm.
  enough (WTS : last_ivar_trm (sigma z) <= maxs (L.map (last_ivar_trm ∘ sigma)%prg (accum_hatom_in_frm p))) by lia.
  eapply in_maxs_ge. unfold "∘"%prg. eapply in_map_iff.
  rewrite occurs_free_in_frm_iff in OCCURS. done!.
Qed.

Definition trm_is_fresh_in_hsubst (x : ivar) (sigma : hsubst) (t : trm L') : bool :=
  L.forallb (negb ∘ is_free_in_trm x ∘ sigma)%prg (accum_hatom_in_trm t).

Definition trms_is_fresh_in_hsubst {n : nat} (x : ivar) (sigma : hsubst) (ts : trms L' n) : bool :=
  L.forallb (negb ∘ is_free_in_trm x ∘ sigma)%prg (accum_hatom_in_trms ts).

Definition frm_is_fresh_in_hsubst (x : ivar) (sigma : hsubst) (p : frm L') : bool :=
  L.forallb (negb ∘ is_free_in_trm x ∘ sigma)%prg (accum_hatom_in_frm p).

Lemma trm_is_fresh_in_hsubst_iff (t : trm L') (z : ivar) (sigma : hsubst)
  : trm_is_fresh_in_hsubst z sigma t = true <-> is_free_in_trm z (hsubst_trm sigma t) = false
with trms_is_fresh_in_hsubst_iff n (ts : trms L' n) (z : ivar) (sigma : hsubst)
  : trms_is_fresh_in_hsubst z sigma ts = true <-> is_free_in_trms z (hsubst_trms sigma ts) = false.
Proof.
  - unfold trm_is_fresh_in_hsubst. unfold "∘"%prg. clear trm_is_fresh_in_hsubst_iff. revert z sigma. trm_ind t; simpl; i.
    + split; intros H; [rewrite andb_true_iff in H; destruct H as [H _]; rewrite negb_true_iff in H; done| rewrite andb_true_iff; split; [rewrite negb_true_iff; done | done]].
    + eapply trms_is_fresh_in_hsubst_iff.
    + destruct c as [cc | hc].
      * ss!. 
      * simpl. split.
        { rewrite andb_true_iff. intros [H _]. rewrite negb_true_iff in H. done!. }
        { rewrite andb_true_iff. rewrite negb_true_iff. done!. }
  - unfold trms_is_fresh_in_hsubst. clear trms_is_fresh_in_hsubst_iff. revert z sigma. trms_ind ts; simpl; i.
    + done!.
    + rewrite forallb_app. rewrite is_free_in_trms_unfold. rewrite orb_false_iff. rewrite andb_true_iff. rewrite IH. rewrite <- trm_is_fresh_in_hsubst_iff. reflexivity.
Qed.

Lemma frm_is_fresh_in_hsubst_iff (p : frm L') (z : ivar) (sigma : hsubst)
  : frm_is_fresh_in_hsubst z sigma p = true <-> is_free_in_frm z (hsubst_frm sigma p) = false.
Proof.
  revert z sigma. unfold frm_is_fresh_in_hsubst. frm_ind p; simpl; ii.
  - eapply trms_is_fresh_in_hsubst_iff.
  - rewrite orb_false_iff. do 2 rewrite <- trm_is_fresh_in_hsubst_iff.
    unfold "∘"%prg. rewrite forallb_app. rewrite andb_true_iff. done!.
  - done!.
  - rewrite forallb_app. rewrite orb_false_iff. rewrite andb_true_iff. rewrite IH1, IH2. done!.
  - split.
    + intros H_forallb. rewrite andb_false_iff.
      destruct (z =? hchi_frm sigma (All_frm y p1))%nat as [ | ] eqn : OBS.
      { simpl. right. done!. }
      { left. rewrite Nat.eqb_neq in OBS. eapply IH1. rewrite forallb_forall.
        intros x x_in. unfold "∘"%prg. rewrite negb_true_iff. unfold cons_hsubst.
        unfold Prelude.eqb. destruct (Prelude.eq_dec x (inl y)) as [H_eq | H_ne].
        - destruct (is_free_in_trm z (Var_trm (hchi_frm sigma (All_frm y p1)))) as [ | ] eqn : EQ.
          + contradiction OBS. symmetry. subst x. rewrite <- fv_is_free_in_trm in EQ.
            simpl in EQ. done!.
          + done!.
        - rewrite forallb_forall in H_forallb. unfold "∘"%prg in H_forallb.
          rewrite <- negb_true_iff. eapply H_forallb. eapply L.in_remove_iff. done!.
      }
    + rewrite andb_false_iff. rewrite negb_false_iff. rewrite Nat.eqb_eq. unfold "∘"%prg in *. intros [NOT_FREE | ->].
      { eapply IH1 in NOT_FREE. rewrite forallb_forall in NOT_FREE. rewrite forallb_forall.
        intros x x_in. rewrite negb_true_iff. rewrite L.in_remove_iff in x_in. destruct x_in as [x_in x_ne_y].
        apply NOT_FREE in x_in. rewrite negb_true_iff in x_in. unfold cons_hsubst in x_in.
        unfold Prelude.eqb in *. destruct (Prelude.eq_dec x (inl y)) as [H_eq | H_ne]; try done!.
      }
      { rewrite forallb_forall. intros x x_in. apply L.in_remove_iff in x_in. destruct x_in as [x_in x_ne_y].
        rewrite negb_true_iff. eapply hchi_frm_not_free. simpl. rewrite andb_true_iff.
        split; [rewrite <- occurs_free_in_frm_iff in x_in | rewrite negb_true_iff; unfold Prelude.eqb; destruct (eq_dec x (inl y))]; try done!.
      }
Qed.

Theorem hchi_frm_is_fresh_in_hsubst (p : frm L') (sigma : hsubst)
  : frm_is_fresh_in_hsubst (hchi_frm sigma p) sigma p = true.
Proof.
  unfold frm_is_fresh_in_hsubst. rewrite forallb_forall. ii.
  unfold "∘"%prg. rewrite negb_true_iff. eapply hchi_frm_not_free.
  rewrite occurs_free_in_frm_iff. done!.
Qed.

Lemma hchi_frm_nil (p : frm L')
  : is_free_in_frm (hchi_frm nil_hsubst p) p = false.
Proof.
  pose proof (hchi_frm_is_fresh_in_hsubst p nil_hsubst) as claim1.
  unfold frm_is_fresh_in_hsubst in claim1.
  rewrite <- not_true_iff_false. intros CONTRA. 
  rewrite forallb_forall in claim1. unfold "∘"%prg in claim1.
  rewrite <- in_accum_hatom_in_frm_iff_is_free_in_frm in CONTRA.
  apply claim1 in CONTRA. rewrite negb_true_iff in CONTRA.
  unfold nil_hsubst in CONTRA at 2. rewrite is_free_in_trm_unfold in CONTRA.
  rewrite Nat.eqb_neq in CONTRA. contradiction.
Qed.

Definition equiv_hsubst_in_frm (sigma1 : hsubst) (sigma2 : hsubst) (p : frm L') : Prop :=
  forall z : hatom, forall FREE : occurs_free_in_frm z p = true, sigma1 z = sigma2 z.

Theorem hchi_frm_compat_equiv_hsubst (sigma1 : hsubst) (sigma2 : hsubst) (p : frm L')
  (EQUIV : equiv_hsubst_in_frm sigma1 sigma2 p)
  : hchi_frm sigma1 p = hchi_frm sigma2 p.
Proof.
  unfold hchi_frm. f_equal. f_equal. eapply maxs_ext. intros n. unfold "∘"%prg.
  split; intros H_in; eapply in_map_iff; apply in_map_iff in H_in; destruct H_in as [x [<- H_in]].
  - exists x. rewrite -> EQUIV. try done!.
    rewrite occurs_free_in_frm_iff. done!.
  - exists x. rewrite -> EQUIV. try done!.
    rewrite occurs_free_in_frm_iff. done!.
Qed.

Lemma equiv_hsubst_in_trm_implies_hsubst_trm_same (sigma1 : hsubst) (sigma2 : hsubst) (t : trm L')
  (EQUIV : forall z : hatom, forall FREE : occurs_free_in_trm z t = true, sigma1 z = sigma2 z)
  : hsubst_trm sigma1 t = hsubst_trm sigma2 t
with equiv_hsubst_in_trms_implies_hsubst_trms_same n (sigma1 : hsubst) (sigma2 : hsubst) (ts : trms L' n)
  (EQUIV : forall z : hatom, forall FREE : occurs_free_in_trms z ts = true, sigma1 z = sigma2 z)
  : hsubst_trms sigma1 ts = hsubst_trms sigma2 ts.
Proof.
  - clear equiv_hsubst_in_trm_implies_hsubst_trm_same. revert sigma1 sigma2 EQUIV. trm_ind t; simpl; ii.
    + eapply EQUIV. rewrite eqb_eq. done!.
    + f_equal. eapply equiv_hsubst_in_trms_implies_hsubst_trms_same. exact EQUIV.
    + destruct c as [cc | hc].
      * reflexivity.
      * eapply EQUIV. rewrite eqb_eq. done!.
  - clear equiv_hsubst_in_trms_implies_hsubst_trms_same. revert sigma1 sigma2 EQUIV. trms_ind ts; simpl; ii.
    + reflexivity.
    + f_equal.
      * eapply equiv_hsubst_in_trm_implies_hsubst_trm_same. ii. eapply EQUIV. rewrite orb_true_iff. left. exact FREE.
      * eapply IH. ii. eapply EQUIV. rewrite orb_true_iff. right. exact FREE.
Qed.

Lemma equiv_hsubst_in_frm_implies_hsubst_frm_same (sigma1 : hsubst) (sigma2 : hsubst) (p : frm L')
  (EQUIV : equiv_hsubst_in_frm sigma1 sigma2 p)
  : hsubst_frm sigma1 p = hsubst_frm sigma2 p.
Proof.
  revert sigma1 sigma2 EQUIV. unfold equiv_hsubst_in_frm. frm_ind p; simpl; ii.
  - simpl in EQUIV. f_equal.
    eapply equiv_hsubst_in_trms_implies_hsubst_trms_same. done.
  - simpl in EQUIV. f_equal.
    + eapply equiv_hsubst_in_trm_implies_hsubst_trm_same. ii.
      eapply EQUIV. rewrite orb_true_iff. done!.
    + eapply equiv_hsubst_in_trm_implies_hsubst_trm_same. ii.
      eapply EQUIV. rewrite orb_true_iff. done!.
  - f_equal. eapply IH1. done!.
  - f_equal.
    + eapply IH1. ii. eapply EQUIV. rewrite orb_true_iff. done!.
    + eapply IH2. ii. eapply EQUIV. rewrite orb_true_iff. done!.
  - f_equal.
    + eapply hchi_frm_compat_equiv_hsubst. unfold equiv_hsubst_in_frm. simpl. done.
    + eapply IH1. ii. unfold cons_hsubst. unfold eqb in *. destruct (eq_dec z (inl y)) as [H_yes | H_no].
      { f_equal. subst z. eapply hchi_frm_compat_equiv_hsubst. unfold equiv_hsubst_in_frm. simpl. done. }
      { eapply EQUIV. rewrite andb_true_iff. split. done. eapply negb_true_iff. unfold Prelude.eqb. destruct (eq_dec z (inl y)); done. }
Qed.

Lemma distr_hcompose_one (sigma1 : hsubst) (sigma2 : hsubst) (x : hatom) (y : ivar) (z : hatom) (t : trm L') (p : frm L')
  (FRESH : forallb (negb ∘ occurs_free_in_trm (inl y) ∘ sigma1)%prg (remove (eq_dec@{Set} (hasEqDec := @sum_hasEqDec ivar Henkin_constants nat_hasEqDec Henkin_constants_hasEqDec)) x (accum_hatom_in_frm p)) = true)
  (FREE : occurs_free_in_frm z p = true)
  : cons_hsubst x t (hsubst_compose sigma1 sigma2) z = hsubst_compose (cons_hsubst x (Var_trm y) sigma1) (cons_hsubst (inl y) t sigma2) z.
Proof.
  unfold hsubst_compose, cons_hsubst. unfold Prelude.eqb. destruct (eq_dec z x) as [H_eq | H_ne].
  - subst z. simpl. destruct (eq_dec (inl y) (inl y)); done!.
  - rewrite forallb_forall in FRESH. unfold "∘"%prg in FRESH.
    assert (NOT_FREE : occurs_free_in_trm (inl y) (sigma1 z) = false).
    { rewrite <- negb_true_iff. eapply FRESH. rewrite L.in_remove_iff. rewrite <- occurs_free_in_frm_iff. done!. }
    eapply equiv_hsubst_in_trm_implies_hsubst_trm_same. intros z' FREE'. destruct (eq_dec z' (inl y)) as [EQ | NE]; try done!.
Qed.

#[local] Tactic Notation "done" :=
  first [now firstorder | done!].

Definition occurs_free_in_trm_wrt (z : hatom) (sigma : hsubst) (t : trm L') : Prop :=
  exists x : hatom, occurs_free_in_trm x t = true /\ occurs_free_in_trm z (sigma x) = true.

Definition occurs_free_in_trms_wrt {n : nat} (z : hatom) (sigma : hsubst) (ts : trms L' n) : Prop :=
  exists x : hatom, occurs_free_in_trms x ts = true /\ occurs_free_in_trm z (sigma x) = true.

Definition occurs_free_in_frm_wrt (z : hatom) (sigma : hsubst) (p : frm L') : Prop :=
  exists x : hatom, occurs_free_in_frm x p = true /\ occurs_free_in_trm z (sigma x) = true.

Fixpoint occurs_free_in_trm_wrt_iff (t : trm L') (z : hatom) (sigma : hsubst) {struct t}
  : occurs_free_in_trm_wrt z sigma t <-> occurs_free_in_trm z (hsubst_trm sigma t) = true
with occurs_free_in_trms_wrt_iff n (ts : trms L' n) (z : hatom) (sigma : hsubst) {struct ts}
  : occurs_free_in_trms_wrt z sigma ts <-> occurs_free_in_trms z (hsubst_trms sigma ts) = true.
Proof.
  - clear occurs_free_in_trm_wrt_iff. destruct t as [x | f ts | [cc | hc]]; simpl; i.
    + clear occurs_free_in_trms_wrt_iff. split.
      * intros [y [FREE FREE']]. s!. destruct FREE; [subst y | contradiction]. exact FREE'.
      * unfold occurs_free_in_trm_wrt. intros FREE. exists (inl x). simpl. rewrite eqb_eq. done.
    + pose proof (occurs_free_in_trms_wrt_iff (L.(function_arity_table) f) ts z sigma) as H. clear occurs_free_in_trms_wrt_iff. split.
      * intros [y [FREE FREE']]. done.
      * intros FREE. done.
    + clear occurs_free_in_trms_wrt_iff. done.
    + clear occurs_free_in_trms_wrt_iff. split.
      * intros [y [FREE FREE']]. unfold Prelude.eqb in FREE. ss!.
      * unfold occurs_free_in_trm_wrt. intros FREE. exists (inr hc). simpl. rewrite eqb_eq. split; trivial.
  - destruct ts as [ | n t ts]; simpl; i.
    + clear occurs_free_in_trm_wrt_iff occurs_free_in_trms_wrt_iff. done.
    + pose proof (occurs_free_in_trm_wrt_iff t z sigma) as H. clear occurs_free_in_trm_wrt_iff. pose proof (occurs_free_in_trms_wrt_iff n ts z sigma) as H'. clear occurs_free_in_trms_wrt_iff. split.
      * intros [x [FREE FREE']]. rewrite orb_true_iff. simpl in FREE. rewrite orb_true_iff in FREE. destruct FREE as [FREE | FREE].
        { left. rewrite <- H. exists x. split; trivial. }
        { right. rewrite <- H'. exists x. split; trivial. }
      * rewrite orb_true_iff. intros [FREE | FREE].
        { rewrite <- H in FREE. destruct FREE as [x [FREE FREE']]. exists x. simpl. rewrite orb_true_iff. split; [left; exact FREE | exact FREE']. }
        { rewrite <- H' in FREE. destruct FREE as [x [FREE FREE']]. exists x. simpl. rewrite orb_true_iff. split; [right; exact FREE | exact FREE']. }
Qed.

Lemma occurs_free_in_frm_wrt_iff (p : frm L') (z : hatom) (sigma : hsubst)
  : occurs_free_in_frm_wrt z sigma p <-> occurs_free_in_frm z (hsubst_frm sigma p) = true.
Proof.
  revert z sigma. unfold occurs_free_in_frm_wrt. frm_ind p; simpl; i.
  - split.
    + intros [y [FREE FREE']]. eapply occurs_free_in_trms_wrt_iff. done.
    + intros FREE. apply occurs_free_in_trms_wrt_iff in FREE. done!.
  - split.
    + intros [y [FREE FREE']]. rewrite orb_true_iff in FREE. rewrite orb_true_iff. destruct FREE as [FREE | FREE].
      * left. eapply occurs_free_in_trm_wrt_iff. done.
      * right. eapply occurs_free_in_trm_wrt_iff. done.
    + intros FREE. rewrite orb_true_iff in FREE. destruct FREE as [FREE | FREE].
      * apply occurs_free_in_trm_wrt_iff in FREE. destruct FREE as [y [FREE FREE']].
        exists y. rewrite orb_true_iff. done!.
      * apply occurs_free_in_trm_wrt_iff in FREE. destruct FREE as [y [FREE FREE']].
        exists y. rewrite orb_true_iff. done!.
  - done!.
  - split.
    + intros [y [FREE FREE']]. rewrite orb_true_iff in FREE. rewrite orb_true_iff. destruct FREE as [FREE | FREE].
      * left. eapply IH1. done.
      * right. eapply IH2. done.
    + intros FREE. rewrite orb_true_iff in FREE. destruct FREE as [FREE | FREE].
      * apply IH1 in FREE. destruct FREE as [y [FREE FREE']].
        exists y. rewrite orb_true_iff. done!.
      * apply IH2 in FREE. destruct FREE as [y [FREE FREE']].
        exists y. rewrite orb_true_iff. done!.
  - split.
    + intros [w [FREE FREE']]. rewrite andb_true_iff in FREE. rewrite negb_true_iff in FREE. rewrite eqb_neq in FREE.
      destruct FREE as [FREE w_ne_y]. rewrite andb_true_iff. rewrite negb_true_iff. split.
      * eapply IH1. exists w. split; trivial. unfold cons_hsubst.
        unfold Prelude.eqb. destruct (eq_dec w (inl y)) as [EQ | NE]; done!.
      * rewrite eqb_neq. intros CONTRA.
        assert (claim1 : frm_is_fresh_in_hsubst (hchi_frm sigma (All_frm y p1)) sigma (All_frm y p1) = true).
        { exact (hchi_frm_is_fresh_in_hsubst (All_frm y p1) sigma). }
        unfold frm_is_fresh_in_hsubst in claim1. rewrite forallb_forall in claim1.
        assert (claim2 : In w (accum_hatom_in_frm (All_frm y p1))).
        { rewrite <- occurs_free_in_frm_iff. simpl. rewrite andb_true_iff. rewrite negb_true_iff. rewrite eqb_neq. done!. }
        apply claim1 in claim2. unfold "∘"%prg in claim2. rewrite negb_true_iff in claim2.
        subst z. rewrite occurs_free_in_trm_iff in FREE'. rewrite in_accum_hatom_in_trm_iff_is_free_in_trm in FREE'. done!.
    + rewrite andb_true_iff. rewrite negb_true_iff. rewrite eqb_neq.
      set (w := hchi_frm sigma (All_frm y p1)). intros [FREE NE].
      apply IH1 in FREE. destruct FREE as [x [FREE FREE']].
      unfold cons_hsubst in FREE'. unfold eqb in FREE'. destruct (eq_dec x (inl y)) as [x_eq_y | x_ne_y].
      * subst x. contradiction NE. apply occurs_free_in_trm_iff in FREE'. simpl in FREE'. done!.
      * exists x. rewrite andb_true_iff. rewrite negb_true_iff. rewrite eqb_neq. done!.
Qed.

Lemma hchi_frm_ext (sigma1 : hsubst) (sigma2 : hsubst) (p1 : frm L') (p2 : frm L')
  (EQUIV : forall z : hatom, occurs_free_in_frm_wrt z sigma1 p1 <-> occurs_free_in_frm_wrt z sigma2 p2)
  : hchi_frm sigma1 p1 = hchi_frm sigma2 p2.
Proof.
  assert (ENOUGH : forall xs : list hatom, forall f : hatom -> list ivar, maxs (L.map (maxs ∘ f)%prg xs) = maxs (L.flat_map f xs)).
  { induction xs; simpl; i; eauto. unfold "∘"%prg. rewrite maxs_app. f_equal. eauto. }
  unfold hchi_frm. f_equal. unfold last_ivar_trm. f_equal.
  change (maxs (L.map (maxs ∘ (fvs_trm ∘ sigma1))%prg (accum_hatom_in_frm p1)) = maxs (L.map (maxs ∘ (fvs_trm ∘ sigma2))%prg (accum_hatom_in_frm p2))).
  do 2 rewrite ENOUGH. eapply maxs_ext. intros z. do 2 rewrite in_flat_map.
  unfold "∘"%prg. split; intros (y&IN&IN').
  - assert (claim : occurs_free_in_frm_wrt (inl z) sigma1 p1).
    { exists y. split.
      - rewrite occurs_free_in_frm_iff; trivial.
      - rewrite occurs_free_in_trm_iff, in_accum_hatom_in_trm_iff_is_free_in_trm; done!.
    }
    rewrite -> EQUIV in claim. destruct claim as (x&OCCURS&OCCURS'). exists x. split.
    + rewrite occurs_free_in_frm_iff in OCCURS. done!.
    + rewrite fv_is_free_in_trm, <- in_accum_hatom_in_trm_iff_is_free_in_trm, <- occurs_free_in_trm_iff. done!.
  - assert (claim : occurs_free_in_frm_wrt (inl z) sigma2 p2).
    { exists y. split.
      - rewrite occurs_free_in_frm_iff; trivial.
      - rewrite occurs_free_in_trm_iff, in_accum_hatom_in_trm_iff_is_free_in_trm; done!.
    }
    rewrite <- EQUIV in claim. destruct claim as (x&OCCURS&OCCURS'). exists x. split.
    + rewrite occurs_free_in_frm_iff in OCCURS. done!.
    + rewrite fv_is_free_in_trm, <- in_accum_hatom_in_trm_iff_is_free_in_trm, <- occurs_free_in_trm_iff. done!.
Qed.

Theorem hsubst_compose_trm_spec (t : trm L') (sigma : hsubst) (sigma': hsubst)
  : hsubst_trm (hsubst_compose sigma sigma') t = hsubst_trm sigma' (hsubst_trm sigma t)
with hsubst_compose_trms_spec n (ts : trms L' n) (sigma : hsubst) (sigma': hsubst)
  : hsubst_trms (hsubst_compose sigma sigma') ts = hsubst_trms sigma' (hsubst_trms sigma ts).
Proof.
  - revert sigma sigma'. trm_ind t; simpl; i.
    + done!.
    + f_equal. eapply hsubst_compose_trms_spec.
    + destruct c as [cc | hc]; done!.
  - revert sigma sigma'. trms_ind ts; simpl; i.
    + done!.
    + f_equal.
      * eapply hsubst_compose_trm_spec.
      * eapply IH.
Qed.

Theorem hsubst_compose_frm_spec (p : frm L') (sigma : hsubst) (sigma': hsubst)
  : hsubst_frm (hsubst_compose sigma sigma') p = hsubst_frm sigma' (hsubst_frm sigma p).
Proof.
  revert sigma sigma'. frm_ind p; simpl; i.
  - f_equal; eapply hsubst_compose_trms_spec.
  - f_equal; eapply hsubst_compose_trm_spec.
  - done!.
  - done!.
  - enough (ENOUGH : hchi_frm sigma' (hsubst_frm sigma (All_frm y p1)) = hchi_frm (hsubst_compose sigma sigma') (All_frm y p1)).
    { revert ENOUGH.
      set (x := hchi_frm sigma (All_frm y p1)).
      set (z := hchi_frm (hsubst_compose sigma sigma') (All_frm y p1)).
      set (w := hchi_frm sigma' (All_frm x (hsubst_frm (cons_hsubst (inl y) (Var_trm x) sigma) p1))).
      i. rewrite <- IH1. assert (EQ : z = w) by done!. subst z. f_equal; trivial.
      eapply equiv_hsubst_in_frm_implies_hsubst_frm_same.
      unfold equiv_hsubst_in_frm. ii.
      rewrite <- distr_hcompose_one with (p := p1).
      - ss!.
      - pose proof (claim1 := hchi_frm_is_fresh_in_hsubst). unfold frm_is_fresh_in_hsubst in claim1.
        eapply forallb_forall. intros u u_in. rewrite L.in_remove_iff in u_in. destruct u_in as [u_in NE].
        unfold "∘"%prg. rewrite negb_true_iff.
        enough (WTS : occurs_free_in_trm (inl x) (sigma u) ≠ true) by now destruct (occurs_free_in_trm (inl x) (sigma u)).
        intros CONTRA. rewrite occurs_free_in_trm_iff in CONTRA. rewrite in_accum_hatom_in_trm_iff_is_free_in_trm in CONTRA.
        specialize claim1 with (p := All_frm y p1) (sigma := sigma). unfold "∘"%prg in claim1. rewrite forallb_forall in claim1.
        assert (claim2: In u (accum_hatom_in_frm (All_frm y p1))) by ss!.
        apply claim1 in claim2. ss!.
      - ss!.
    }
    eapply hchi_frm_ext. intros z. split.
    + simpl. unfold occurs_free_in_frm_wrt. intros [x [FREE FREE']]. simpl in FREE.
      rewrite andb_true_iff in FREE. rewrite negb_true_iff in FREE. rewrite eqb_neq in FREE.
      destruct FREE as [FREE NE]. apply occurs_free_in_frm_wrt_iff in FREE. unfold free_in_frm_wrt in FREE.
      destruct FREE as [w [FREE1 FREE2]]. unfold cons_hsubst in FREE2. unfold eqb in FREE2. destruct (eq_dec w (inl y)) as [w_eq_y | w_ne_y].
      * unfold occurs_free_in_trm in FREE2. rewrite eqb_eq in FREE2. subst. done!.
      * exists w. simpl. rewrite andb_true_iff. rewrite negb_true_iff. rewrite eqb_neq. split; try tauto.
        eapply occurs_free_in_trm_wrt_iff. done.
    + intros [x [FREE FREE']]. simpl in FREE. rewrite andb_true_iff in FREE. rewrite negb_true_iff in FREE. rewrite eqb_neq in FREE. destruct FREE as [FREE NE].
      apply occurs_free_in_trm_wrt_iff in FREE'. destruct FREE' as [u [FREE' FREE'']]. exists u. split.
      * eapply occurs_free_in_frm_wrt_iff. exists x. simpl. rewrite andb_true_iff. rewrite negb_true_iff. rewrite eqb_neq. done!.
      * done!.
Qed.

Lemma hcompose_one_hsubst_frm (x1 : hatom) (t1 : trm L') (sigma : hsubst) (p : frm L')
  : hsubst_frm sigma (hsubst_frm (one_hsubst x1 t1) p) = hsubst_frm (cons_hsubst x1 (hsubst_trm sigma t1) sigma) p.
Proof.
  unfold one_hsubst. rewrite <- hsubst_compose_frm_spec. eapply equiv_hsubst_in_frm_implies_hsubst_frm_same. ii.
  unfold cons_hsubst, hsubst_compose, eqb. destruct (eq_dec z x1) as [z_eq_x1 | z_ne_x1]; try done!.
  unfold nil_hsubst. destruct z; try done!.
Qed.

Lemma cons_hsubst_hsubst_frm (x1 : hatom) (t1 : trm L') (y : hatom) (p : frm L') (sigma : hsubst)
  (NOT_FREE : occurs_free_in_frm y p = false \/ y = x1)
  : hsubst_frm (cons_hsubst x1 t1 sigma) p = hsubst_frm (cons_hsubst y t1 sigma) (hsubst_frm (one_hsubst x1 (nil_hsubst y)) p).
Proof.
  unfold one_hsubst. rewrite <- hsubst_compose_frm_spec. eapply equiv_hsubst_in_frm_implies_hsubst_frm_same.
  ii. unfold cons_hsubst, hsubst_compose, eqb. destruct (eq_dec z x1) as [z_eq_x1 | z_ne_x1].
  - subst z. unfold nil_hsubst. destruct y as [x | c]; simpl.
    + destruct (eq_dec (inl x) (inl x)); try done!.
    + destruct (eq_dec (inr c) (inr c)); try done!.
  - destruct z as [x | c]; simpl.
    + destruct (eq_dec (inl x) y) as [z_eq_y | z_ne_y]; try done!.
    + destruct (eq_dec (inr c) y) as [z_eq_y | z_ne_y]; try done!.
Qed.

Lemma nil_hsubst_trm (t : trm L')
  : hsubst_trm nil_hsubst t = t
with nil_hsubst_trms n (ts : trms L' n)
  : hsubst_trms nil_hsubst ts = ts.
Proof.
  - clear nil_hsubst_trm. trm_ind t; simpl.
    + reflexivity.
    + f_equal. eapply nil_hsubst_trms.
    + destruct c as [cc | hc]; reflexivity.
  - clear nil_hsubst_trms. trms_ind ts; simpl.
    + reflexivity.
    + f_equal.
      * eapply nil_hsubst_trm.
      * eapply IH.
Qed.

Lemma trivial_hsubst (x : hatom) (p : frm L')
  : hsubst_frm (one_hsubst x (nil_hsubst x)) p = hsubst_frm nil_hsubst p.
Proof.
  eapply equiv_hsubst_in_frm_implies_hsubst_frm_same. ii. unfold one_hsubst, cons_hsubst.
  unfold eqb. destruct (eq_dec z x); try done!.
Qed.

Theorem subst_hsubst_compat_in_trm (s : subst L') (sigma : hsubst) (t : trm L')
  (SIM : forall z : hatom, to_hsubst s z = sigma z)
  : subst_trm s t = hsubst_trm sigma t
with subst_hsubst_compat_in_trms n (s : subst L') (sigma : hsubst) (ts : trms L' n)
  (SIM : forall z : hatom, to_hsubst s z = sigma z)
  : subst_trms s ts = hsubst_trms sigma ts.
Proof.
  - clear subst_hsubst_compat_in_trm. revert s sigma SIM. trm_ind t; simpl; i.
    + rewrite subst_trm_unfold. exact (SIM (inl x)).
    + rewrite <- subst_hsubst_compat_in_trms with (s := s); trivial.
    + destruct c as [cc | hc]; [reflexivity | exact (SIM (inr hc))].
  - clear subst_hsubst_compat_in_trms. revert s sigma SIM. trms_ind ts; simpl; i.
    + reflexivity.
    + rewrite <- subst_hsubst_compat_in_trm with (s := s); trivial. rewrite <- IH with (s := s); trivial.
Qed.

Theorem subst_hsubst_compat_in_frm (s : subst L') (sigma : hsubst) (p : frm L')
  (SIM : forall z : hatom, to_hsubst s z = sigma z)
  : subst_frm s p = hsubst_frm sigma p.
Proof.
  revert s sigma SIM. revert p.
  assert (LEMMA : forall A : Set, forall xs : list A, forall f: A -> list ivar, maxs (L.map (maxs ∘ f)%prg xs) = maxs (L.flat_map f xs)).
  { intros A. induction xs; simpl; i; eauto. unfold "∘"%prg. rewrite maxs_app. f_equal. eauto. }
  frm_ind p; simpl; i.
  - f_equal. eapply subst_hsubst_compat_in_trms. done!.
  - f_equal; eapply subst_hsubst_compat_in_trm; done!.
  - f_equal. done!.
  - f_equal; done!.
  - assert (claim : chi_frm s (All_frm y p1) = hchi_frm sigma (All_frm y p1)).
    { unfold hchi_frm, chi_frm. f_equal. f_equal.
      change (maxs (L.map (maxs ∘ (fvs_trm ∘ s))%prg (fvs_frm (All_frm y p1))) = maxs (L.map (maxs ∘ (fvs_trm ∘ sigma))%prg (accum_hatom_in_frm (All_frm y p1)))).
      do 2 rewrite LEMMA. eapply maxs_ext. intros z. do 2 rewrite in_flat_map. unfold "∘"%prg.
      split; intros (x&IN&IN').
      - rewrite fv_is_free_in_frm in IN. simpl in IN. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq in IN. destruct IN as [IN NE].
        specialize SIM with (z := inl x). simpl in SIM.
        exists (inl x). rewrite <- SIM. split; trivial.
        rewrite in_accum_hatom_in_frm_iff_is_free_in_frm. done!.
      - destruct x as [x | c].
        + rewrite in_accum_hatom_in_frm_iff_is_free_in_frm in IN. specialize SIM with (z := inl x). simpl in SIM.
          exists x. rewrite SIM. split; done!.
        + specialize SIM with (z := inr c). simpl in SIM.
          rewrite <- SIM in IN'. simpl in IN'. done!. 
    }
    f_equal; trivial. rewrite claim. eapply IH1. intros [x | c]; simpl.
    + unfold cons_hsubst, cons_subst. destruct (eqb (inl x) (inl y)) as [ | ] eqn : H_OBS.
      { rewrite eqb_eq in H_OBS. inv H_OBS. destruct (eq_dec y y); try done!. }
      { rewrite eqb_neq in H_OBS. destruct (eq_dec x y); try done!. eapply SIM with (z := inl x). }
    + unfold cons_hsubst, cons_subst. unfold eqb.
      destruct (eq_dec (inr c) (inl y)) as [EQ | NE].
      { inv EQ. }
      { eapply SIM with (z := inr c). }
Qed.

Definition replace_constant_in_trm (c : Henkin_constants) (ct : trm L') (t : trm L') : trm L' :=
  hsubst_trm (one_hsubst (inr c) ct) t.

Definition replace_constant_in_trms {n : nat} (c : Henkin_constants) (ct : trm L') (ts : trms L' n) : trms L' n :=
  hsubst_trms (one_hsubst (inr c) ct) ts.

Definition replace_constant_in_frm (c : Henkin_constants) (ct : trm L') (p : frm L') : frm L' :=
  hsubst_frm (one_hsubst (inr c) ct) p.

Theorem replace_constant_in_frm_compat_subst (c : Henkin_constants) (ct : trm L') (s : subst L') (p : frm L')
  (FRESH : forall x : ivar, is_free_in_trm x ct = true -> hsubst_trm (one_hsubst (inr c) ct) (s x) = Var_trm x)
  : replace_constant_in_frm c ct (subst_frm s p) = subst_frm (replace_constant_in_trm c ct ∘ s)%prg (replace_constant_in_frm c ct p).
Proof.
  unfold replace_constant_in_frm at 2. symmetry. erewrite subst_hsubst_compat_in_frm. 2:{ ii. reflexivity. }
  rewrite <- hsubst_compose_frm_spec. unfold replace_constant_in_frm.
  erewrite subst_hsubst_compat_in_frm. 2:{ ii. reflexivity. }
  rewrite <- hsubst_compose_frm_spec. eapply equiv_hsubst_in_frm_implies_hsubst_frm_same.
  ii. unfold hsubst_compose. unfold "∘"%prg. destruct z as [x | c'].
  - unfold one_hsubst. simpl. unfold replace_constant_in_trm. reflexivity.
  - unfold one_hsubst. simpl. unfold cons_hsubst, nil_hsubst.
    destruct (Prelude.eqb (inr c') (inr c)) as [ | ] eqn : H_OBS.
    + rewrite eqb_eq in H_OBS. inv H_OBS. unfold replace_constant_in_trm.
      rewrite <- nil_hsubst_trm. eapply equiv_hsubst_in_trm_implies_hsubst_trm_same.
      intros [x | c'] OCCURS.
      * apply occurs_free_in_trm_iff, in_accum_hatom_in_trm_iff_is_free_in_trm, fv_is_free_in_trm in OCCURS. simpl. eapply FRESH. done!.
      * done!.
    + simpl. reflexivity.
Qed.

Theorem replace_constant_with_fresh_ivar_in_frm (c : Henkin_constants) (s : subst L') (p : frm L') (z : ivar)
  (FRESH : s z = Var_trm z)
  : replace_constant_in_frm c (Var_trm z) (subst_frm s p) = subst_frm (replace_constant_in_trm c (Var_trm z) ∘ s)%prg (replace_constant_in_frm c (Var_trm z) p).
Proof.
  eapply replace_constant_in_frm_compat_subst. intros x FREE.
  rewrite is_free_in_trm_unfold in FREE. rewrite Nat.eqb_eq in FREE. subst z.
  now rewrite FRESH.
Qed.

Lemma quick_draw_constant (c : Henkin_constants) (x : ivar) (t : trm L') (y : ivar) (p : frm L')
  (NE : y ≠ x)
  : replace_constant_in_frm c (Var_trm y) (subst_frm (one_subst x t) p) = subst_frm (one_subst x (replace_constant_in_trm c (Var_trm y) t)) (replace_constant_in_frm c (Var_trm y) p).
Proof.
  rewrite replace_constant_in_frm_compat_subst.
  - eapply equiv_subst_in_frm_implies_subst_frm_same. unfold "∘"%prg. ii.
    unfold replace_constant_in_trm, one_hsubst, one_subst, cons_hsubst, cons_subst.
    destruct (eq_dec z x); try done!.
  - intros z FREE. apply fv_is_free_in_trm in FREE. simpl in FREE. destruct FREE as [-> | []].
    unfold one_subst, nil_subst, cons_subst. unfold one_hsubst, cons_hsubst, nil_hsubst.
    destruct (eq_dec z x); try done!.
Qed.

Lemma embed_frm_Fun_eqAxm (f : L.(function_symbols))
  : embed_frm (@Fun_eqAxm L f) = @Fun_eqAxm L' f.
Proof.
  eapply embed_frm_Fun_eqAxm.
Qed.

Lemma embed_frm_Rel_eqAxm (R : L.(relation_symbols))
  : embed_frm (@Rel_eqAxm L R) = @Rel_eqAxm L' R.
Proof.
  eapply embed_frm_Rel_eqAxm.
Qed.

End HSUBST.

End HELFER1_i.

Section MAPPING_EMBED.

Import HELFER1_i.

Context {L : language} {constant_symbols1 : Set} {constant_symbols2 : Set}.
Variable constant_symbols_mapping : constant_symbols1 -> constant_symbols2.

#[local] Notation L1 := (augmented_language L constant_symbols1).
#[local] Notation L2 := (augmented_language L constant_symbols2).

#[local] Notation h := constant_symbols_mapping.

Definition subst_mapping (s : subst L1) : subst L2 :=
  fun z => trm_mapping h (s z).

Lemma trm_mapping_fvs_eq (t : trm L1)
  : fvs_trm (trm_mapping h t) = fvs_trm t
with trms_mapping_fvs_eq {n : nat} (ts : trms L1 n)
  : fvs_trms (trms_mapping h ts) = fvs_trms ts.
Proof.
  - trm_ind t; simpl; do 2 rewrite fvs_trm_unfold.
    + reflexivity.
    + exact (@trms_mapping_fvs_eq _ ts).
    + destruct c as [c' | hc']; reflexivity.
  - trms_ind ts; simpl; rewrite fvs_trms_unfold.
    + reflexivity.
    + now rewrite trm_mapping_fvs_eq, IH.
Qed.

Lemma frm_mapping_fvs_eq (p : frm L1)
  : fvs_frm (frm_mapping h p) = fvs_frm p.
Proof.
  frm_ind p; simpl.
  - exact (trms_mapping_fvs_eq ts).
  - now rewrite trm_mapping_fvs_eq, trm_mapping_fvs_eq.
  - exact IH1.
  - now rewrite IH1, IH2.
  - now rewrite IH1.
Qed.

Lemma trm_mapping_fv (z : ivar) (t : trm L1)
  : is_free_in_trm z (trm_mapping h t) = is_free_in_trm z t
with trms_mapping_fv {n : nat} (z : ivar) (ts : trms L1 n)
  : is_free_in_trms z (trms_mapping h ts) = is_free_in_trms z ts.
Proof.
  - trm_ind t; simpl.
    + reflexivity.
    + do 2 rewrite is_free_in_trm_unfold. exact (@trms_mapping_fv _ z ts).
    + destruct c as [ | ]; reflexivity.
  - trms_ind ts; simpl.
    + reflexivity.
    + rewrite is_free_in_trms_unfold. now rewrite trm_mapping_fv, IH.
Qed.

Lemma frm_mapping_fv (z : ivar) (p : frm L1)
  : is_free_in_frm z (frm_mapping h p) = is_free_in_frm z p.
Proof.
  frm_ind p; simpl.
  - exact (trms_mapping_fv z ts).
  - now rewrite trm_mapping_fv, trm_mapping_fv.
  - exact IH1.
  - now rewrite IH1, IH2.
  - now rewrite IH1.
Qed.

Lemma trm_mapping_last_ivar (t : trm L1)
  : last_ivar_trm (trm_mapping h t) = last_ivar_trm t.
Proof.
  unfold last_ivar_trm.
  now rewrite trm_mapping_fvs_eq.
Qed.

Lemma frm_mapping_chi (s : subst L1) (p : frm L1)
  : chi_frm (subst_mapping s) (frm_mapping h p) = chi_frm s p.
Proof.
  unfold chi_frm, subst_mapping.
  rewrite frm_mapping_fvs_eq.
  f_equal. f_equal. eapply maxs_ext.
  intro x. unfold compose. s!. split; i; des.
  - exists x0. now rewrite trm_mapping_last_ivar in H.
  - exists x0. now rewrite trm_mapping_last_ivar.
Qed.

Lemma trm_mapping_subst_trm (s : subst L1) (t : trm L1)
  : trm_mapping h (subst_trm s t) = subst_trm (subst_mapping s) (trm_mapping h t)
with trms_mapping_subst_trms {n : nat} (s : subst L1) (ts : trms L1 n)
  : trms_mapping h (subst_trms s ts) = subst_trms (subst_mapping s) (trms_mapping h ts).
Proof.
  - trm_ind t; simpl.
    + reflexivity.
    + do 2 rewrite subst_trm_unfold. simpl. f_equal. eapply trms_mapping_subst_trms.
    + do 2 rewrite subst_trm_unfold. destruct c as [c' | hc']; reflexivity.
  - trms_ind ts; simpl.
    + reflexivity.
    + rewrite subst_trms_unfold. simpl. rewrite subst_trms_unfold with (ts := S_trms _ _ _).
      now rewrite trm_mapping_subst_trm, IH.
Qed.

Lemma frm_mapping_subst_frm (s : subst L1) (p : frm L1)
  : frm_mapping h (subst_frm s p) = subst_frm (subst_mapping s) (frm_mapping h p).
Proof.
  revert s.
  frm_ind p; intro s; simpl.
  - now rewrite trms_mapping_subst_trms.
  - now rewrite trm_mapping_subst_trm, trm_mapping_subst_trm.
  - now rewrite IH1.
  - now rewrite IH1, IH2.
  - rewrite <- (frm_mapping_chi s (All_frm y p1)). f_equal.
    rewrite IH1. eapply equiv_subst_in_frm_implies_subst_frm_same.
    intros z z_free. unfold subst_mapping, cons_subst. simpl.
    destruct (eq_dec z y); reflexivity.
Qed.

Lemma frm_mapping_not_free (x : ivar) (p : frm L1)
  : is_not_free_in_frm x (frm_mapping h p) <-> is_not_free_in_frm x p.
Proof.
  unfold is_not_free_in_frm.
  now rewrite frm_mapping_fv.
Qed.

Lemma trm_mapping_embed_trm (t : trm L)
  : trm_mapping constant_symbols_mapping (embed_trm t) = embed_trm t
with trms_mapping_embed_trms (n : nat) (ts : trms L n)
  : trms_mapping constant_symbols_mapping (embed_trms ts) = embed_trms ts.
Proof.
  - trm_ind t; simpl.
    + reflexivity.
    + now rewrite trms_mapping_embed_trms.
    + reflexivity.
  - trms_ind ts; simpl.
    + reflexivity.
    + now rewrite trm_mapping_embed_trm, IH.
Qed.

Lemma frm_mapping_embed_frm (p : frm L)
  : frm_mapping constant_symbols_mapping (embed_frm p) = embed_frm p.
Proof.
  frm_ind p; simpl.
  - now rewrite trms_mapping_embed_trms.
  - now rewrite trm_mapping_embed_trm, trm_mapping_embed_trm.
  - now rewrite IH1.
  - now rewrite IH1, IH2.
  - now rewrite IH1.
Qed.

Fixpoint proof_mapping (ps : list (frm L1)) (p : frm L1)
  (PF : @proof L1 ps p)
  : @proof L2 (map (frm_mapping constant_symbols_mapping) ps) (frm_mapping constant_symbols_mapping p).
Proof.
  destruct PF.
  - simpl. constructor.
  - simpl. rewrite map_app. econs.
    + exact (proof_mapping _ _ PF1).
    + exact (proof_mapping _ _ PF2).
  - simpl. econs.
    + intros p Hp. rewrite in_map_iff in Hp.
      destruct Hp as [q0 [<- Hq0]].
      rewrite -> frm_mapping_not_free; eapply NOT_FREE; exact Hq0.
    + exact (proof_mapping _ _ PF).
  - simpl. constructor.
  - simpl. constructor.
  - simpl. constructor.
  - simpl. rewrite frm_mapping_subst_frm.
    replace (subst_frm (subst_mapping (one_subst x t)) (frm_mapping h p)) with (subst_frm (one_subst x (trm_mapping h t)) (frm_mapping h p)).
    + constructor.
    + eapply equiv_subst_in_frm_implies_subst_frm_same. intros z z_free.
      unfold subst_mapping, one_subst, cons_subst, nil_subst.
      destruct (eq_dec z x); reflexivity.
  - simpl. constructor.
    rewrite -> frm_mapping_not_free. exact NOT_FREE.
  - simpl. constructor.
  - simpl. constructor.
  - simpl. constructor.
  - simpl. constructor.
  - simpl. rewrite <- embed_frm_Fun_eqAxm.
    rewrite frm_mapping_embed_frm.
    rewrite -> embed_frm_Fun_eqAxm.
    econs.
  - simpl. rewrite <- embed_frm_Rel_eqAxm.
    rewrite frm_mapping_embed_frm.
    rewrite -> embed_frm_Rel_eqAxm.
    econs.
Qed.

End MAPPING_EMBED.

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
  + econs.
  + econs. eapply trms_mapping_similarity.
  + econs. econs.
  + econs. econs.
- destruct ts as [ | n t ts]; simpl.
  + constructor.
  + econs.
    * eapply trm_mapping_similarity.
    * eapply trms_mapping_similarity.
Qed.

Lemma frm_mapping_similarity (p : frm L1)
  : p =~= frm_mapping h p.
Proof.
  frm_ind p; simpl.
  - econs. eapply trms_mapping_similarity.
  - econs; eapply trm_mapping_similarity.
  - econs. exact IH1.
  - econs; assumption.
  - econs. exact IH1.
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
  frm_ind p; simpl; intro H.
  - exact (HC_occurs_in_trms_map c _ ts H).
  - rewrite orb_true_iff in H |- *.
    destruct H as [H | H].
    + left. exact (HC_occurs_in_trm_map c t1 H).
    + right. exact (HC_occurs_in_trm_map c t2 H).
  - exact (IH1 H).
  - rewrite orb_true_iff in H |- *.
    destruct H as [H | H].
    + left. exact (IH1 H).
    + right. exact (IH2 H).
  - exact (IH1 H).
Qed.

Lemma HC_occurs_in_frm_map_inv (c2 : K2) (p : frm L1) : HC_occurs_in_frm c2 (frm_mapping h p) = true -> (exists c1, HC_occurs_in_frm c1 p = true /\ h c1 = c2).
Proof.
  frm_ind p; simpl; intro H.
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
  - exact (IH1 H).
  - rewrite orb_true_iff in H.
    destruct H as [H | H].
    + destruct (IH1 H) as [c1 [H1 H2]].
      exists c1. split.
      { rewrite orb_true_iff. now left. }
      exact H2.
    + destruct (IH2 H) as [c1 [H1 H2]].
      exists c1. split.
      { rewrite orb_true_iff. now right. }
      exact H2.
  - exact (IH1 H).
Qed.

Lemma hchi_frm_graph_eq (sigma1 : hatom1 -> trm L1) (sigma2 : hatom2 -> trm L2) (p : frm L1)
  (SIG : forall z1, forall z2, hatom_similarity z1 z2 -> trm_mapping h (sigma1 z1) = sigma2 z2)
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
  (SIG : forall z1, forall z2, hatom_similarity z1 z2 -> trm_mapping h (sigma1 z1) = sigma2 z2)
  : trm_mapping h (hsubst_trm sigma1 t) = hsubst_trm sigma2 (trm_mapping h t)
with hsubst_trms_graph_eq (sigma1 : hatom1 -> trm L1) (sigma2 : hatom2 -> trm L2) (n : nat) (ts : trms L1 n)
  (SIG : forall z1, forall z2, hatom_similarity z1 z2 -> trm_mapping h (sigma1 z1) = sigma2 z2)
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
  (SIG : forall z1, forall z2, hatom_similarity z1 z2 -> trm_mapping h (sigma1 z1) = sigma2 z2)
  : frm_mapping h (hsubst_frm sigma1 p) = hsubst_frm sigma2 (frm_mapping h p).
Proof.
  revert sigma1 sigma2 SIG.
  frm_ind p; intros sigma1 sigma2 SIG; simpl.
  - f_equal. eapply hsubst_trms_graph_eq. exact SIG.
  - f_equal.
    + eapply hsubst_trm_graph_eq. exact SIG.
    + eapply hsubst_trm_graph_eq. exact SIG.
  - f_equal. eapply IH1. exact SIG.
  - f_equal.
    + eapply IH1. exact SIG.
    + eapply IH2. exact SIG.
  - pose proof (hchi_frm_graph_eq sigma1 sigma2 (All_frm y p1) SIG) as HH.
    simpl in HH. rewrite <- HH.
    f_equal. eapply IH1. intros z1 z2 ZSIM.
    unfold cons_hsubst. unfold eqb.
    destruct (eq_dec z1 (inl y)) as [-> | NE1].
    + destruct z2 as [x | c2]; simpl in ZSIM; try contradiction.
      subst x.
      destruct (eq_dec (inl y) (inl y)); [reflexivity | congruence].
    + assert (NE2 : ~ z2 = inl y).
      { intro EZ. destruct z1 as [x1 | c1], z2 as [x2 | c2]; simpl in ZSIM; try contradiction; congruence. }
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
      * exfalso. eapply NE1. f_equal.
        eapply h_inj. now inversion E2.
      * reflexivity.
Qed.

End MAPPING_HSUBST_GENERAL.

Module HELFER1_ii.

Import FolHilbert.
Import HELFER1_i.

Section DEDUCTION.

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

Section BOUNDED_HC.

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
        assert (Hin : q \in E.fromList qs) by done!.
        pose proof (INCL2 _ Hin) as H.
        rewrite E.in_image_iff in H.
        destruct H as [r [-> INr]].
        do 2 red in INr.
        rewrite in_map_iff in INr.
        destruct INr as [r0 [<- INr0]].
        rewrite E.in_image_iff.
        rewrite L.in_map_iff in INr0.
        destruct INr0 as [r' [<- Hr']].
        exists (replace_constant_in_frm (Henkin_constants_hasEqDec := Kf_hasEqDec) (f0 hc0) (Var_trm y0) (frm_mapping f0 r')).
        split; cycle 1.
        * eapply E.in_image_iff with (X := E.fromList _). exists (frm_mapping f0 r'). split.
          { reflexivity. }
          { eapply in_map_iff. exists r'. split; eauto. }
        * rewrite <- frm_mapping_g_back_g_fix with (g := g) (g_back := g_back) (q := replace_constant_in_frm (Henkin_constants_hasEqDec := Kf_hasEqDec) (f0 hc0) (Var_trm y0) (frm_mapping f0 r')); eauto.
          erewrite @frm_mapping_replace_constant_in_frm_inj
            with (h := g); eauto. instantiate (1 := id). reflexivity.
      + econs.
        change (proof (map (frm_mapping g_back) qs) (frm_mapping g_back (replace_constant_in_frm (Henkin_constants_hasEqDec := nat_hasEqDec) (g (f0 hc0)) (Var_trm y0) (frm_mapping g (frm_mapping f0 p))))) in PF3.
        replace (frm_mapping g_back (replace_constant_in_frm (Henkin_constants_hasEqDec := nat_hasEqDec) (g (f0 hc0)) (Var_trm y0) (frm_mapping g (frm_mapping f0 p))))
        with (replace_constant_in_frm (Henkin_constants_hasEqDec := Kf_hasEqDec) (f0 hc0) (Var_trm y0) (frm_mapping f0 p))
        in PF3.
        2:{ pose proof (@frm_mapping_replace_constant_in_frm_inj L _ _ _ _ _ g_inj (f0 hc0) (Var_trm y0) (frm_mapping f0 p)) as HH.
            simpl trm_mapping in HH.
            set (X := replace_constant_in_frm (g (f0 hc0)) (Var_trm y0) (frm_mapping g (frm_mapping f0 p))).
            change (frm_mapping g (replace_constant_in_frm (f0 hc0) (Var_trm y0) (frm_mapping f0 p)) = X) in HH.
            rewrite <- HH. symmetry. eapply frm_mapping_g_back_g_fix; exact G_BACK_G. }
        eauto.
    - ii. rewrite E.in_image_iff in H. destruct H as [y [-> H]].
      unfold id. eauto.
  }
  destruct PROVE3 as [rs [INCL3 [PF3']]].
  pose proof (proof_mapping (@proj1_sig _ _) _ _ PF3') as PF4.
  assert (HC0_FIX : proj1_sig (f0 hc0) = hc0).
  { eapply f_id_on_hcs_of_ps_p. eapply in_hcs_of_ps_p_hc0. }
  replace (frm_mapping (@proj1_sig _ _) (replace_constant_in_frm (f0 hc0) (Var_trm y0) (frm_mapping f0 p)))
  with (replace_constant_in_frm hc0 (Var_trm y0) p) in PF4; cycle 1.
  { symmetry.
    erewrite @frm_mapping_replace_constant_in_frm_inj with (h := @proj1_sig _ _) (c := f0 hc0) (ct := Var_trm y0) (q := frm_mapping f0 p); eauto.
    rewrite HC0_FIX. simpl.
    exploit (frm_mapping_proj1_sig_f_fix hc0 ps p p).
    - intros hc OCC. eapply in_hcs_of_ps_p_of_p. exact OCC.
    - intros X.
      set (XX := frm_mapping
             (@proj1_sig _ (fun hc => (if in_dec eq_dec hc (hcs_of_ps_p hc0 ps p) then true else false) = true))
             (frm_mapping f0 p)).
      change (XX = p) in X. congruence.
  }
  eapply extend_proves; cycle 1.
  { exists (map (frm_mapping (@proj1_sig _ _)) rs). split.
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
    erewrite @frm_mapping_replace_constant_in_frm_inj with (h := @proj1_sig _ _) (c := f0 hc0) (ct := Var_trm y0) (q := frm_mapping f0 q'); eauto.
    rewrite HC0_FIX. simpl.
    exploit (frm_mapping_proj1_sig_f_fix hc0 ps p q').
    + intros hc OCC. eapply in_hcs_of_ps_p_of_ps; eauto.
    + intros X.
      set (XX := frm_mapping (@proj1_sig _ (fun hc => (if in_dec eq_dec hc (hcs_of_ps_p hc0 ps p) then true else false) = true)) (frm_mapping f0 q')).
      change (XX = q') in X. congruence.
  - eapply INCL. do 2 red. exact INq'.
Qed.

End BOUNDED_HC.

Context {AHC : abstract_Henkin_constants Henkin_constants L (Henkin_constants_hasEqDec := Henkin_constants_hasEqDec)}.

Definition HenkinAxiom (hc : Henkin_constants) : frm L' :=
  let '(x, phi) := hc_decode hc in
  Imp_frm (subst_frm (one_subst x (@Con_trm L' (inr hc))) phi) (All_frm x phi).

Section HC_SUBST_INV.

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

Lemma same_stage_other_axiom_hc_free hc hc' n
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

End HC_SUBST_INV.

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

Section HENKIN_STAGES.

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
      unfold "∘"%prg in claim. enough (ENOUGH : is_free_in_frm (hchi_frm s (All_frm y p1)) (All_frm y p1) ≠ true) by now destruct (is_free_in_frm (hchi_frm s (All_frm y p1)) (All_frm y p1)).
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
  assert (Hneq : hc ≠ hc').
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
  { eapply for_Imp_E. exists []. split. done!. econs. eapply proof_dne. eapply for_Imp_E. 2: eapply PROVE1. eapply for_CP1. exists []. split. done!. econs. eapply proof_ex_falso. }
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
        rewrite ALPHA. eapply proves_replace_constant_in_frm. exists ps. split; done!.
  - exact PROVE3.
Qed.

Fixpoint AddHenkin_stage_list (X : ensemble (frm L)) (n : nat) (hcs : list Henkin_constants) : ensemble (frm L') :=
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
  - eapply AddHenkin_stage0_equiconsistent.
  - destruct IH as [IH1 IH2].
    destruct (AddHenkin_stage_equiconsistent X n) as [H1 H2].
    split; intro H.
    + eapply H1. eapply IH1. exact H.
    + eapply IH2. eapply H2. exact H.
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
      - exact PF.
    }
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
  - erewrite <- @embed_frm_proves_iff with (Henkin_constants := Henkin_constants).
    rewrite inconsistent_iff in H. exact H.
Qed.

End HENKIN_STAGES.

End DEDUCTION.

End HELFER1_ii.
