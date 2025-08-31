Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.ThN.

#[local] Opaque Nat.div.
#[local] Opaque Nat.modulo.

Module POS.

Inductive bit : Set :=
  | bO 
  | bI.

Definition t : Set :=
  list bit.

Notation pos := POS.t.

Definition to_nat (p : pos) : nat :=
  fold_left (fun i : nat => bit_rec _ (i * 2) (i * 2 + 1)) p 1.

Lemma to_nat_gt_0 (p : pos)
  : to_nat p > 0.
Proof.
  unfold to_nat. rewrite <- fold_left_rev_right.
  generalize (rev p) as rev_p. clear p. intros p.
  induction p as [ | [ | ] ? ?]; simpl; (lia || eauto).
Qed.

Lemma to_nat_inj (p1 : pos) (p2 : pos)
  (to_nat_EQ : to_nat p1 = to_nat p2)
  : p1 = p2.
Proof with lia || eauto.
  revert to_nat_EQ. unfold to_nat; do 2 rewrite <- fold_left_rev_right.
  intros to_nat_EQ; eapply rev_inj; revert to_nat_EQ.
  generalize (rev p2) as bs2. generalize (rev p1) as bs1. clear p1 p2.
  set (myF := fold_right (fun d : bit => fun i : nat => bit_rec _ (i * 2) (i * 2 + 1) d) 1).
  assert (claim : forall bs, myF bs > 0).
  { induction bs as [ | b bs IH]... simpl... destruct b as [ | ]; simpl bit_rec... }
  induction bs1 as [ | b1 bs1 IH], bs2 as [ | b2 bs2]; simpl...
  - destruct b2; simpl bit_rec... pose proof (claim bs2)...
  - destruct b1; simpl bit_rec... pose proof (claim bs1)...
  - destruct b1, b2; simpl bit_rec...
    all: intros ?; assert (claim1: myF bs1 = myF bs2)...
    all: f_equal...
Qed.

Lemma to_nat_last (p : pos) (b : bit) :
  to_nat (p ++ [b]) =
  match b with
  | bO => to_nat p * 2
  | bI => to_nat p * 2 + 1
  end.
Proof.
  unfold to_nat at 1. rewrite <- fold_left_rev_right, -> rev_unit.
  unfold to_nat. rewrite <- fold_left_rev_right. now destruct b as [ | ].
Qed.

#[local] Notation b0 := bO.
#[local] Notation b1 := bI.

Lemma to_nat_unfold (p : pos) :
  to_nat p =
  match p with
  | [] => 1
  | bO :: p' => to_nat p' + 2^(length p')
  | bI :: p' => to_nat p' + 2^(length p' + 1)
  end.
Proof with lia || eauto.
  destruct p as [ | [ | ] p]...
  - induction p as [ | [ | ] p IH] using rev_ind...
    + replace (b0 :: p ++ [b0]) with ((b0 :: p) ++ [b0]) by reflexivity.
      repeat rewrite to_nat_last. rewrite IH. rewrite last_length. simpl...
    + replace (b0 :: p ++ [b1]) with ((b0 :: p) ++ [b1]) by reflexivity.
      repeat rewrite to_nat_last. rewrite IH. rewrite last_length. simpl...
  - induction p as [ | [ | ] p IH] using rev_ind...
    + replace (b1 :: p ++ [b0]) with ((b1 :: p) ++ [b0]) by reflexivity.
      repeat rewrite to_nat_last. rewrite IH. rewrite last_length. simpl...
    + replace (b1 :: p ++ [b1]) with ((b1 :: p) ++ [b1]) by reflexivity.
      repeat rewrite to_nat_last. rewrite IH. rewrite last_length. simpl...
Qed.

Lemma pos_from_nat (n : nat)
  (n_gt_0 : n > 0)
  : { p : pos | to_nat p = n }.
Proof with try lia.
  revert n n_gt_0. induction n as [n IH] using lt_wf_rec. i. destruct n as [ | [ | n']].
  - exfalso...
  - exists []. reflexivity.
  - remember (S (S n')) as n eqn: n_is.
    assert (n_le_2 : n >= 2) by lia.
    clear n' n_is n_gt_0.
    destruct (n mod 2) as [ | [ | n_mod_2]] eqn: H_OBS.
    + assert ({ p : pos | to_nat p = n / 2 }) as [p H_p].
      { eapply IH.
        - pose proof (positive_even n ((n) / 2)) as H.
          assert (H1 : n = 2 * ((n) / 2))...
          pose proof (Nat.div_mod n 2)...
        - pose proof (Nat.div_mod n 2)... 
      }
      exists (p ++ [b0]). rewrite to_nat_last.
      pose proof (Nat.div_mod n 2)...
    + assert ({ p : pos | to_nat p = (n - 1) / 2 }) as [p H_p].
      { eapply IH.
        - pose proof (positive_odd n ((n - 1) / 2)) as H.
          assert (H1 : n = 2 * ((n - 1) / 2) + 1)...
        - pose proof (Nat.div_mod (n - 1) 2) as H.
          pose proof (positive_odd n ((n - 1) / 2))...
      }
      exists (p ++ [b1]). rewrite to_nat_last.
      pose proof (positive_odd n ((n - 1) / 2))...
    + pose proof (Nat.mod_bound_pos n 2)...
Qed.

Definition of_nat (n : nat) (n_gt_0 : n > 0) : pos :=
  proj1_sig (pos_from_nat n n_gt_0).

Lemma of_nat_spec (n : nat) (n_gt_0 : n > 0)
  : to_nat (of_nat n n_gt_0) = n.
Proof.
  exact (proj2_sig (pos_from_nat n n_gt_0)).
Qed.

#[global] Opaque of_nat.

End POS.

Variant digit : Set :=
  | D0
  | D1
  | D2
  | D3
  | D4
  | D5
  | D6
  | D7
  | D8
  | D9.

#[global]
Instance digit_hasEqDec
  : hasEqDec digit.
Proof.
  red; decide equality.
Qed.

Definition N10 : Set :=
  list digit.

Module LittleEndianDecimal.

Fixpoint to_nat (n : N10) : nat :=
  match n with
  | []       => 0
  | D0 :: n' => 0 + 10 * to_nat n'
  | D1 :: n' => 1 + 10 * to_nat n'
  | D2 :: n' => 2 + 10 * to_nat n'
  | D3 :: n' => 3 + 10 * to_nat n'
  | D4 :: n' => 4 + 10 * to_nat n'
  | D5 :: n' => 5 + 10 * to_nat n'
  | D6 :: n' => 6 + 10 * to_nat n'
  | D7 :: n' => 7 + 10 * to_nat n'
  | D8 :: n' => 8 + 10 * to_nat n'
  | D9 :: n' => 9 + 10 * to_nat n'
  end.

#[local]
Instance N10_isSetoid : isSetoid N10 :=
  { eqProp (lhs : N10) (rhs : N10) := to_nat lhs = to_nat rhs
  ; eqProp_Equivalence := relation_on_image_liftsEquivalence eq_equivalence to_nat
  }.

#[global]
Instance N10_hasEqDec
  : hasEqDec N10.
Proof.
  pose proof digit_hasEqDec as H; red in H; red; decide equality.
Defined.

Fixpoint succ (n : N10) : N10 :=
  match n with
  | []       => D1 :: []     
  | D0 :: n' => D1 :: n'     
  | D1 :: n' => D2 :: n'     
  | D2 :: n' => D3 :: n'     
  | D3 :: n' => D4 :: n'     
  | D4 :: n' => D5 :: n'     
  | D5 :: n' => D6 :: n'     
  | D6 :: n' => D7 :: n'     
  | D7 :: n' => D8 :: n'     
  | D8 :: n' => D9 :: n'     
  | D9 :: n' => D0 :: succ n'
  end.

Lemma to_nat_succ_comm (n : N10)
  : to_nat (succ n) = 1 + to_nat n.
Proof.
  induction n as [ | [ | | | | | | | | | ] n IH]; simpl; eauto; lia.
Qed.

Fixpoint of_nat (n : nat) : N10 :=
  match n with
  | O => []
  | S n' => succ (of_nat n')
  end.

Lemma to_nat_of_nat (n : nat)
  : to_nat (of_nat n) = n.
Proof.
  induction n as [ | n IH]; simpl; eauto.
  rewrite <- IH at 2. eapply to_nat_succ_comm.
Qed.

Lemma of_nat_10_times (n : nat)
  (n_ne_0 : n <> 0)
  : of_nat (n * 10) = D0 :: of_nat n.
Proof.
  induction n as [ | n IH]; simpl.
  - contradiction.
  - clear n_ne_0. destruct n as [ | n'].
    + reflexivity.
    + rewrite IH; [reflexivity | discriminate].
Qed.

Fixpoint norm (n : N10) : N10 :=
  match n with
  | [] => []
  | D0 :: n' =>
    match norm n' with
    | [] => []
    | nn' => D0 :: nn'
    end
  | d :: n' => d :: norm n'
  end.

Lemma to_nat_eq_0_implies_norm_eq_0 (n : N10)
  (to_nat_returns_0 : to_nat n = 0)
  : norm n = [].
Proof.
  induction n as [ | [ | | | | | | | | | ] n IH]; eauto.
  - simpl in *; rewrite IH; eauto. lia.
  - simpl in *; lia.
  - simpl in *; lia.
  - simpl in *; lia.
  - simpl in *; lia.
  - simpl in *; lia.
  - simpl in *; lia.
  - simpl in *; lia.
  - simpl in *; lia.
  - simpl in *; lia.
Qed.

Lemma of_nat_returns_nil_iff (n : nat)
  : of_nat n = [] <-> 0 = n.
Proof.
  split.
  - induction n as [ | n IH]; intros of_nat_returns_0.
    + reflexivity.
    + apply f_equal with (f := to_nat) in of_nat_returns_0.
      simpl in of_nat_returns_0. rewrite <- of_nat_returns_0.
      rewrite to_nat_succ_comm. rewrite to_nat_of_nat. reflexivity.
  - intros <-. reflexivity.
Qed.

Lemma of_nat_to_nat_10_times (n : N10)
  (n_ne_0 : norm n <> [])
  : of_nat (to_nat n * 10) = D0 :: of_nat (to_nat n).
Proof.
  destruct n as [ | [ | | | | | | | | | ] n].
  - contradiction.
  - enough (H_NE : to_nat (D0 :: n) <> 0) by now rewrite of_nat_10_times.
    destruct n as [ | n'].
    + contradiction.
    + intros H_false. contradiction n_ne_0. now eapply to_nat_eq_0_implies_norm_eq_0.
  - enough (H_NE : to_nat (D1 :: n) <> 0) by now rewrite of_nat_10_times. simpl. lia.
  - enough (H_NE : to_nat (D2 :: n) <> 0) by now rewrite of_nat_10_times. simpl. lia.
  - enough (H_NE : to_nat (D3 :: n) <> 0) by now rewrite of_nat_10_times. simpl. lia.
  - enough (H_NE : to_nat (D4 :: n) <> 0) by now rewrite of_nat_10_times. simpl. lia.
  - enough (H_NE : to_nat (D5 :: n) <> 0) by now rewrite of_nat_10_times. simpl. lia.
  - enough (H_NE : to_nat (D6 :: n) <> 0) by now rewrite of_nat_10_times. simpl. lia.
  - enough (H_NE : to_nat (D7 :: n) <> 0) by now rewrite of_nat_10_times. simpl. lia.
  - enough (H_NE : to_nat (D8 :: n) <> 0) by now rewrite of_nat_10_times. simpl. lia.
  - enough (H_NE : to_nat (D9 :: n) <> 0) by now rewrite of_nat_10_times. simpl. lia.
Qed.

Theorem of_nat_to_nat_norm (n : N10)
  : of_nat (to_nat n) = norm n.
Proof.
  induction n as [ | [ | | | | | | | | | ] n IH]; eauto.
  all: simpl; replace (to_nat n + (to_nat n + (to_nat n + (to_nat n + (to_nat n + (to_nat n + (to_nat n + (to_nat n + (to_nat n + (to_nat n + 0)))))))))) with (to_nat n * 10) by lia.
  all: destruct (norm n) as [ | d n'] eqn: H_OBS; [apply of_nat_returns_nil_iff in IH; rewrite <- IH; reflexivity | rewrite -> of_nat_to_nat_10_times; [now rewrite IH | now rewrite H_OBS]].
Qed.

Corollary N10_eq_thm (lhs : N10) (rhs : N10)
  : lhs == rhs <-> norm lhs = norm rhs.
Proof.
  split; intros H_EQ.
  - rewrite <- of_nat_to_nat_norm with (n := lhs).
    rewrite <- of_nat_to_nat_norm with (n := rhs).
    now eapply f_equal with (f := of_nat).
  - rewrite <- of_nat_to_nat_norm with (n := lhs) in H_EQ.
    rewrite <- of_nat_to_nat_norm with (n := rhs) in H_EQ.
    apply f_equal with (f := to_nat) in H_EQ.
    now do 2 rewrite -> to_nat_of_nat in H_EQ.
Qed.

Fixpoint double (n : N10) {struct n} : N10 :=
  match n with
  | [] => []
  | D0 :: n => D0 :: double n
  | D1 :: n => D2 :: double n
  | D2 :: n => D4 :: double n
  | D3 :: n => D6 :: double n
  | D4 :: n => D8 :: double n
  | D5 :: n => D0 :: succ_double n
  | D6 :: n => D2 :: succ_double n
  | D7 :: n => D4 :: succ_double n
  | D8 :: n => D6 :: succ_double n
  | D9 :: n => D8 :: succ_double n
  end
with succ_double (n : N10) {struct n} : N10 :=
  match n with
  | [] => [D1]
  | D0 :: n => D1 :: double n
  | D1 :: n => D3 :: double n
  | D2 :: n => D5 :: double n
  | D3 :: n => D7 :: double n
  | D4 :: n => D9 :: double n
  | D5 :: n => D1 :: succ_double n
  | D6 :: n => D3 :: succ_double n
  | D7 :: n => D5 :: succ_double n
  | D8 :: n => D7 :: succ_double n
  | D9 :: n => D9 :: succ_double n
  end.

Theorem double_correct (n : N10)
  : to_nat (double n) = (to_nat n) * 2
with succ_double_correct (n : N10)
  : to_nat (succ_double n) = (to_nat n) * 2 + 1.
Proof.
  - induction n as [ | d n IH].
    + reflexivity.
    + destruct d as [ | | | | | | | | | ]; simpl; try lia.
      all: rewrite -> succ_double_correct; try lia.
  - induction n as [ | d n IH].
    + reflexivity.
    + destruct d as [ | | | | | | | | | ]; simpl; try lia.
      all: rewrite -> double_correct; try lia.
Qed.

Definition pos_to_N10 (p : POS.t) : N10 :=
  fold_left (fun n => POS.bit_rec _ (double n) (succ_double n)) p (of_nat 1).

Lemma pos_to_N10_last (p : POS.t) (b : POS.bit) :
  pos_to_N10 (p ++ [b]) =
  match b with
  | POS.bO => double (pos_to_N10 p)
  | POS.bI => succ_double (pos_to_N10 p)
  end.
Proof.
  unfold pos_to_N10 at 1. rewrite <- fold_left_rev_right, -> rev_unit.
  unfold pos_to_N10. rewrite <- fold_left_rev_right. now destruct b as [ | ].
Qed.

Theorem pos_to_N10_correct (p : POS.t)
  : LittleEndianDecimal.to_nat (pos_to_N10 p) = POS.to_nat p.
Proof.
  unfold pos_to_N10. pattern p. revert p.
  induction p as [ | [ | ] p IH] using rev_ind.
  - reflexivity.
  - fold (pos_to_N10 (p ++ [POS.bO])).
    rewrite POS.to_nat_last.
    fold (pos_to_N10 p) in IH.
    rewrite pos_to_N10_last. rewrite <- IH.
    now rewrite double_correct.
  - fold (pos_to_N10 (p ++ [POS.bI])).
    rewrite POS.to_nat_last.
    fold (pos_to_N10 p) in IH.
    rewrite pos_to_N10_last. rewrite <- IH.
    now rewrite succ_double_correct.
Qed.

End LittleEndianDecimal.

Module BijectiveNumeration.

Section BijectiveNumeration_basic_theory.

Variable b : nat.

Hypothesis b_ge_2 : b >= 2.

Lemma from_num_aux_aux1 (n : nat)
  (NE_0 : n <> 0)
  : n / b < n.
Proof.
  pose proof (Nat.mod_bound_pos n b).
  pose proof (Nat.div_mod n b). nia.
Qed.

Lemma from_num_aux_aux2 (n : nat)
  (NE_0 : n <> 0)
  : (n / b) - 1 < n.
Proof.
  pose proof (from_num_aux_aux1 n NE_0). lia.
Qed.

#[local] Hint Resolve from_num_aux_aux1 : core.
#[local] Hint Resolve from_num_aux_aux2 : core.

Fixpoint from_num_aux (n : nat) (H_Acc : @Acc nat lt n) {struct H_Acc} : list nat :=
  match eq_dec n 0 with
  | left EQ => []
  | right NE =>
    let r := n mod b in
    if eq_dec r 0 then
      from_num_aux ((n / b) - 1) (Acc_inv H_Acc _ (from_num_aux_aux2 _ NE)) ++ [b]
    else
      from_num_aux (n / b) (Acc_inv H_Acc _ (from_num_aux_aux1 _ NE)) ++ [r]
  end.

Fixpoint from_num_aux_pirrel1 (n : nat) (H_Acc : Acc lt n) (H_Acc' : Acc lt n) {struct H_Acc} : from_num_aux n H_Acc = from_num_aux n H_Acc'.
Proof.
  destruct H_Acc, H_Acc'; simpl. destruct (eq_dec _ _); f_equal. destruct (eq_dec _ _); f_equal; eapply from_num_aux_pirrel1.
Qed.

Lemma from_num_aux_pirrel (n : nat) (m : nat) (EQ : n = m) (H_Acc : Acc lt n) (H_Acc' : Acc lt m) : from_num_aux n H_Acc = from_num_aux m H_Acc'.
Proof.
  subst m. eapply from_num_aux_pirrel1.
Qed.

Lemma from_num_aux_unfold (n : nat) (H_Acc : @Acc nat lt n) :
  from_num_aux n H_Acc =
  match eq_dec n 0 with
  | left EQ => []
  | right NE =>
    let r := n mod b in
    if eq_dec r 0 then
      from_num_aux ((n / b) - 1) (Acc_inv H_Acc _ (from_num_aux_aux2 _ NE)) ++ [b]
    else
      from_num_aux (n / b) (Acc_inv H_Acc _ (from_num_aux_aux1 _ NE)) ++ [r]
  end.
Proof.
  destruct H_Acc. reflexivity.
Qed.

Definition from_num (n : nat) : list nat :=
  from_num_aux n (lt_wf n).

Lemma from_num_unfold n :
  from_num n =
  match eq_dec n 0 with
  | left EQ => []
  | right NE =>
    let r := n mod b in
    if eq_dec r 0 then
      from_num ((n / b) - 1) ++ [b]
    else
      from_num (n / b) ++ [r]
  end.
Proof.
  unfold from_num at 1. rewrite from_num_aux_unfold.
  destruct (eq_dec _ _) as [EQ1 | NE1].
  - reflexivity.
  - cbn zeta. destruct (eq_dec _ _) as [EQ2 | NE2]; f_equal; eapply from_num_aux_pirrel1.
Qed.

#[local] Opaque from_num.

Definition to_num (ns : list nat) : nat :=
  fold_left (fun n => fun a => a + b * n) ns 0.

Lemma to_num_from_num n
  : to_num (from_num n) = n.
Proof.
  induction (lt_wf n) as [n _ IH]. rewrite from_num_unfold.
  destruct (eq_dec _ _) as [EQ1 | NE1]; eauto.
  cbn zeta. destruct (eq_dec _ _) as [EQ2 | NE2].
  - unfold to_num in *. rewrite fold_left_app. simpl. rewrite IH; eauto.
    erewrite Nat.div_mod with (x := n) (y := b) at 2; try lia. rewrite EQ2.
    rewrite Nat.add_0_r. replace (n / b) with (1 + ((n / b) - 1)) at 2; try lia.
    pose proof (Nat.div_mod n b). pose proof (Nat.mod_bound_pos n 0). nia.
  - unfold to_num in *. rewrite fold_left_app. simpl. rewrite IH; eauto.
    symmetry. rewrite Nat.add_comm. eapply Nat.div_mod. lia.
Qed.

Lemma from_num_to_num ns
  (ns_bound : Forall (fun n => 1 <= n /\ n <= b) ns)
  : from_num (to_num ns) = ns.
Proof.
  induction ns as [ | n ns IH] using L.list_rev_rect; eauto.
  rewrite Forall_app in ns_bound. destruct ns_bound as [ns_bound n_bound].
  specialize (IH ns_bound). unfold to_num. rewrite fold_left_app. simpl.
  rewrite from_num_unfold. cbn zeta. inv n_bound.
  destruct (eq_dec _ _) as [EQ1 | NE1]; try lia. destruct (eq_dec _ _) as [EQ2 | NE2].
  - rewrite Nat.mul_comm in EQ2. rewrite Nat.Div0.mod_add in EQ2.
    assert (claim1 : n = b).
    { enough (~ n < b) by lia. intros H_contra.
      pose proof (COPY := H_contra). rewrite <- Nat.div_small_iff in COPY; try lia.
      pose proof (Nat.div_mod n b) as claim. rewrite -> COPY, -> EQ2 in claim. lia.
    }
    subst n. f_equal. rewrite <- IH at 2. f_equal. unfold to_num. set (X := fold_left _ _ _) in *.
    replace ((b + b * X) / b) with (1 + X); try lia.
    pose proof (div_mod_uniqueness (b + b * X) b (1 + X) 0). lia.
  - revert NE1 NE2. set (fold_left _ _ _) as X. i.
    assert (n < b) as claim1.
    { enough (~ n = b) as H_contra by lia. intros H_contra. subst n.
      rewrite Nat.mul_comm in NE2. rewrite Nat.Div0.mod_add in NE2.
      rewrite Nat.Div0.mod_same in NE2. contradiction.
    }
    assert ((n + b * X) mod b = n) as claim2.
    { pose proof (div_mod_uniqueness (n + b * X) b X n). lia. }
    rewrite claim2. f_equal. rewrite <- IH. f_equal. transitivity X; eauto.
    pose proof (div_mod_uniqueness (n + b * X) b X n). lia.
Qed.

End BijectiveNumeration_basic_theory.

End BijectiveNumeration.
