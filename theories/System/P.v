Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Byte.

Inductive name : Set :=
  | mk_name (seed : nat) : name.

Declare Scope name_scope.
Bind Scope name_scope with name.
Delimit Scope name_scope with name.

#[global]
Instance name_hasEqDec
  : hasEqDec name.
Proof.
  red; decide equality; eapply Nat.eq_dec.
Defined.

Definition un_name (nm : name) : nat :=
  match nm with
  | mk_name seed => seed
  end.

Section PP_name.

Lemma print_name1_aux_lemma (n : nat)
  (NE : n <> 0)
  : (n / 36) < n.
Proof.
  pose proof (Nat.mod_bound_pos n 36).
  pose proof (Nat.div_mod n 36).
  lia.
Qed.

Definition mkAlphaNum (n : nat) : Byte.byte :=
  match n with
  | 0 => x30
  | 1 => x31
  | 2 => x32
  | 3 => x33
  | 4 => x34
  | 5 => x35
  | 6 => x36
  | 7 => x37
  | 8 => x38
  | 9 => x39
  | 10 => x61
  | 11 => x62
  | 12 => x63
  | 13 => x64
  | 14 => x65
  | 15 => x66
  | 16 => x67
  | 17 => x68
  | 18 => x69
  | 19 => x6a
  | 20 => x6b
  | 21 => x6c
  | 22 => x6d
  | 23 => x6e
  | 24 => x6f
  | 25 => x70
  | 26 => x71
  | 27 => x72
  | 28 => x73
  | 29 => x74
  | 30 => x75
  | 31 => x76
  | 32 => x77
  | 33 => x78
  | 34 => x79
  | 35 => x7a
  | _ => x5f
  end.

Fixpoint print_name1 (n : nat) (H_Acc : Acc lt n) : list Byte.byte :=
  match H_Acc with
  | Acc_intro _ H_Acc_inv =>
    match Nat.eq_dec n 0 with
    | left _ => []
    | right NE => print_name1 (n / 36) (H_Acc_inv (n / 36) (print_name1_aux_lemma n NE)) ++ [mkAlphaNum (n mod 36)]
    end
  end.

#[local] Opaque "/" "mod".

Fixpoint print_name1_pirrel (n : nat) (H_Acc : Acc lt n) (H_Acc' : Acc lt n) {struct H_Acc} : print_name1 n H_Acc = print_name1 n H_Acc'.
Proof.
  destruct H_Acc, H_Acc'. simpl. destruct (Nat.eq_dec n 0) as [EQ | NE].
  - reflexivity.
  - f_equal. eapply print_name1_pirrel.
Qed.

Definition unAlphaNum (b : Byte.byte) : option nat :=
  match b with
  | x30 => Some 0
  | x31 => Some 1
  | x32 => Some 2
  | x33 => Some 3
  | x34 => Some 4
  | x35 => Some 5
  | x36 => Some 6
  | x37 => Some 7
  | x38 => Some 8
  | x39 => Some 9
  | x61 => Some 10
  | x62 => Some 11
  | x63 => Some 12
  | x64 => Some 13
  | x65 => Some 14
  | x66 => Some 15
  | x67 => Some 16
  | x68 => Some 17
  | x69 => Some 18
  | x6a => Some 19
  | x6b => Some 20
  | x6c => Some 21
  | x6d => Some 22
  | x6e => Some 23
  | x6f => Some 24
  | x70 => Some 25
  | x71 => Some 26
  | x72 => Some 27
  | x73 => Some 28
  | x74 => Some 29
  | x75 => Some 30
  | x76 => Some 31
  | x77 => Some 32
  | x78 => Some 33
  | x79 => Some 34
  | x7a => Some 35
  | _ => None
  end.

Lemma unAlphaNum_mkAlphaNum n n'
  : unAlphaNum (mkAlphaNum n) = Some n' <-> (n = n' /\ n < 36).
Proof.
  unfold unAlphaNum, mkAlphaNum in *. split; intros H_OBS.
  - (do 36 try destruct n as [ | n]); (do 36 try destruct n' as [ | n']); try congruence; lia.
  - destruct H_OBS as [<- H_OBS]. (do 36 try destruct n as [ | n]); try congruence; lia.
Qed.

Lemma rewrite_unAlphaNum_mkAlphaNum n
  (BOUND : n < 36)
  : unAlphaNum (mkAlphaNum n) = Some n.
Proof.
  rewrite -> unAlphaNum_mkAlphaNum. lia.
Qed.

Definition parse_name1 (bs : list Byte.byte) : option nat :=
  fold_left (fun ACC : option nat => fun b : Byte.byte => liftM2 (fun n : nat => fun m : nat => m + 36 * n) ACC (unAlphaNum b)) bs (Some 0).

Definition next_name (nm : name) : name :=
  mk_name (1 + 36 * un_name nm).

Definition print_name (nm : name) : option (list Byte.byte) :=
  let seed : nat := un_name nm in
  let bs : list Byte.byte := print_name1 seed (lt_wf seed) in
  match bs with
  | [] => None
  | b :: _ => unAlphaNum b >>= fun d : nat => if Nat.ltb d 10 then None else Some bs
  end.

Definition parse_name (bs : list Byte.byte) : option name :=
  match bs with
  | [] => None
  | b :: _ => unAlphaNum b >>= fun d : nat => if Nat.ltb d 10 then None else parse_name1 bs >>= fun seed : nat => pure (mk_name seed)
  end.

#[local] Opaque "+" "*" Nat.ltb.

Lemma print_next_name (bs : list Byte.byte) nm
  (NAME : print_name nm = Some bs)
  : print_name (next_name nm) = Some (bs ++ [x31]).
Proof.
  unfold next_name; unfold print_name; simpl.
  destruct (Nat.eq_dec (1 + 36 * un_name nm) 0) as [EQ1 | NE1]; simpl in *; try lia.
  replace ((1 + 36 * un_name nm) mod 36) with 1 in *; cycle 1.
  { pose proof (div_mod_inv (1 + 36 * un_name nm) 36 (un_name nm) 1); lia. }
  replace (print_name1 ((1 + 36 * un_name nm) / 36) _) with (print_name1 (un_name nm) (lt_wf (un_name nm))); cycle 1.
  { rewrite print_name1_pirrel with (H_Acc' := lt_wf ((1 + 36 * un_name nm) / 36)).
    replace ((1 + 36 * un_name nm) / 36) with (un_name nm); trivial.
    pose proof (div_mod_uniqueness (1 + 36 * un_name nm) 36 (un_name nm) 1); lia.
  }
  unfold print_name in NAME; destruct (print_name1 (un_name nm) (lt_wf (un_name nm))) as [ | b bs'] eqn: H_OBS; try congruence.
  simpl in NAME |- *; destruct (unAlphaNum b) as [n | ] eqn: H_OBS'; simpl in NAME |- *; try congruence.
  destruct (n <? 10)%nat as [ | ] eqn: H_OBS''; try congruence.
  change (b :: bs' ++ ["1"%byte]) with ((b :: bs') ++ ["1"%byte]); congruence.
Qed.

Lemma parse_next_name (bs : list Byte.byte) nm
  (NAME : parse_name bs = Some nm)
  : parse_name (bs ++ [x31]) = Some (next_name nm).
Proof.
  unfold parse_name in *; destruct bs as [ | b bs]; simpl in *; try congruence.
  destruct (unAlphaNum b) as [n0 | ] eqn: H_n0; simpl in *; try congruence.
  destruct (n0 <? 10)%nat as [ | ] eqn: H_OBS; simpl in *; try congruence.
  unfold parse_name1 in *; change (b :: bs ++ ["1"%byte]) with ((b :: bs) ++ ["1"%byte]).
  rewrite fold_left_app; revert NAME; set (fold_left _) as loop; i.
  destruct (loop (b :: bs) (Some 0)) as [r | ] eqn: H_r; simpl in *; try congruence.
  now replace nm with (mk_name r) by congruence.
Qed.

End PP_name.

String Notation name parse_name print_name : name_scope.

Module Name.

Notation t := name.

Definition is_valid (nm : Name.t) : bool :=
  B.isSome (print_name nm >>= parse_name).

Definition max (nm1 : Name.t) (nm2 : Name.t) : Name.t :=
  mk_name (Nat.max (un_name nm1) (un_name nm2)).

Fixpoint maxs (nms : list Name.t) : Name.t :=
  match nms with
  | [] => mk_name 0
  | nm :: nms' => max nm (maxs nms')
  end.

Lemma in_le_maxs (nms : list name) (nm : name)
  (IN : L.In nm nms)
  : un_name nm <= un_name (maxs nms).
Proof.
  revert nm IN. induction nms as [ | [n] nms IH]; simpl.
  - tauto.
  - intros nm [<- | IN]; simpl.
    + lia.
    + rewrite IH; trivial; lia.
Qed.

Definition ne (nm1 : Name.t) (nm2 : Name.t) : Prop :=
  un_name nm1 ≠ un_name nm2.

Lemma ne_pirrel nm1 nm2
  (NE1 : ne nm1 nm2)
  (NE2 : ne nm1 nm2)
  : NE1 = NE2.
Proof.
  destruct nm1, nm2. red in NE1, NE2. simpl in *. eapply ne_pirrel.
Qed.

Lemma ne_iff nm1 nm2
  : ne nm1 nm2 <-> nm1 <> nm2.
Proof.
  destruct nm1, nm2. unfold ne. simpl. rewrite ne_iff. split; congruence.
Qed.

Lemma eq_ne_dec nm1 nm2
  : {eq nm1 nm2} + {ne nm1 nm2}.
Proof.
  pose proof (eq_dec nm1 nm2) as [EQ | NE].
  - left; exact (EQ).
  - right; exact (proj2 (ne_iff nm1 nm2) NE).
Defined.

Section GOOD.

#[local] Opaque "+" "*" Nat.ltb L.replicate "*" "/" "mod".

Theorem print_parse nm nm'
  (EQ : (print_name nm >>= parse_name) = Some nm')
  : nm = nm'.
Proof.
  enough (WTS : Some nm = Some nm') by congruence.
  simpl in EQ. destruct (print_name nm) as [bs | ] eqn: PRINT; simpl in *; try congruence.
  unfold print_name in PRINT. unfold parse_name in EQ.
  destruct bs as [ | b bs]; try congruence.
  destruct (print_name1 _ _) as [ | b' bs'] eqn: H_OBS; try congruence. simpl bind in *.
  destruct (unAlphaNum b') as [d' | ] eqn: H_b'; simpl B.maybe in *; try congruence.
  destruct (unAlphaNum b) as [d | ] eqn: H_b; simpl B.maybe in *; try congruence.
  destruct (d' <? 10)%nat as [ | ] eqn: H_d'; try congruence.
  destruct (d <? 10)%nat as [ | ] eqn: H_d; try congruence.
  assert (b = b' /\ bs = bs') as [EQ_b EQ_bs] by now split; congruence.
  subst b' bs'. remember (b :: bs) as vecb eqn: E. clear b bs E H_b H_b' d d' H_d H_d' PRINT.
  rename vecb into bs. revert nm nm' H_OBS EQ. induction bs as [ | b bs IH] using L.list_rev_rect; simpl; intros.
  - destruct (Nat.eq_dec _ _) as [YES | NO].
    + rewrite <- EQ. rewrite <- YES. simpl. destruct nm; simpl; reflexivity.
    + erewrite print_name1_pirrel with (H_Acc' := lt_wf (un_name nm / 36)) in H_OBS.
      destruct (print_name1 (un_name nm / 36) (lt_wf (un_name nm / 36))) as [ | ? ?]; simpl in *; try congruence.
  - destruct (Nat.eq_dec _ _) as [YES | NO].
    + destruct bs as [ | ? ?]; simpl in *; try congruence.
    + erewrite print_name1_pirrel with (H_Acc' := lt_wf (un_name nm / 36)) in H_OBS.
      rewrite L.snoc_inv_iff in H_OBS. destruct H_OBS as [EQ1 EQ2].
      destruct nm as [n], nm' as [m]; simpl un_name in *.
      rewrite B.observe_bind in EQ. destruct EQ as (N & EQ & H_N). subst.
      rewrite <- H_N. pose proof (IH (mk_name (n / 36)) (mk_name (N / 36))) as IH_inst. simpl un_name in IH_inst.
      specialize (IH_inst eq_refl).
      assert (Some (mk_name (n / 36)) = Some (mk_name (N / 36))) as GO1.
      { eapply IH_inst. rewrite B.observe_bind. exists (N / 36). split; trivial.
        unfold parse_name1 in EQ |- *. rewrite fold_left_app in EQ. unfold fold_left in EQ at 1.
        unfold liftM2 in EQ. change bind with (fun m => fun k => @B.maybe _ (fun _ : option nat => option nat) None k m) in EQ.
        cbn beta in EQ. rewrite B.observe_bind in EQ. des. rewrite B.observe_bind in EQ0. des. replace (N / 36) with x; eauto. inv EQ1.
        assert (x0 < 36) as LT.
        { revert EQ0. clear. unfold unAlphaNum, mkAlphaNum.
          pose proof (Nat.mod_bound_pos n 36) as LT.
          assert (n mod 36 < 36) as H_lt by lia.
          clear LT; revert H_lt. generalize (n mod 36) as m. clear.
          do 36 (destruct m as [ | m]; try congruence || lia).
        }
        pose proof (div_mod_uniqueness (x0 + 36 * x) 36 x x0). lia.
      }
      assert (Some (mk_name (n mod 36)) = Some (mk_name (N mod 36))) as GO2.
      { unfold parse_name1 in EQ |- *. rewrite fold_left_app in EQ. unfold fold_left in EQ at 1.
        unfold liftM2 in EQ. change bind with (fun m => fun k => @B.maybe _ (fun _ : option nat => option nat) None k m) in EQ.
        cbn beta in EQ. rewrite B.observe_bind in EQ. des. rewrite B.observe_bind in EQ0. des. inv EQ1. do 2 f_equal.
        assert (x0 < 36) as LT.
        { revert EQ0. clear. unfold unAlphaNum, mkAlphaNum.
          pose proof (Nat.mod_bound_pos n 36) as LT.
          assert (n mod 36 < 36) as H_lt by lia.
          clear LT; revert H_lt. generalize (n mod 36) as m. clear.
          do 36 (destruct m as [ | m]; try congruence || lia).
        }
        replace ((x0 + 36 * x) mod 36) with x0; cycle 1.
        { pose proof (div_mod_uniqueness (x0 + 36 * x) 36 x x0). lia. }
        revert EQ0. clear. unfold unAlphaNum, mkAlphaNum.
        pose proof (Nat.mod_bound_pos n 36) as LT.
        assert (n mod 36 < 36) as H_lt by lia.
        clear LT; revert H_lt. generalize (n mod 36) as m. clear.
        do 36 (destruct m as [ | m]; try congruence || lia).
      }
      assert (n / 36 = N / 36) as YES1 by congruence.
      assert (n mod 36 = N mod 36) as YES2 by congruence.
      do 2 f_equal. pose proof (Nat.div_mod n 36). pose proof (Nat.div_mod N 36). lia.
Qed.

End GOOD.

Section PRINCE_NAME.

Definition gen_prince_name (n : nat) : name :=
  mk_name (10 * 36 ^ n).

#[local] Opaque "+" "*" Nat.ltb L.replicate "*" "/" "mod".

Lemma print_prince_name n
  : print_name (gen_prince_name n) = Some (x61 :: L.replicate n x30).
Proof.
  unfold gen_prince_name. unfold print_name. induction n as [ | n IH]; simpl.
  - destruct (Nat.eq_dec _ _) as [EQ | NE].
    + lia.
    + reflexivity.
  - destruct (Nat.eq_dec _ _) as [EQ | NE].
    + exfalso. clear IH. induction n as [ | n IH]; simpl in *; lia.
    + erewrite print_name1_pirrel with (H_Acc' := lt_wf (10 * (36 * 36 ^ n) / 36)).
      replace (10 * (36 * 36 ^ n) / 36) with (10 * 36 ^ n); cycle 1.
      { pose proof (div_mod_uniqueness (10 * (36 * 36 ^ n)) 36 (10 * 36 ^ n) 0). lia. }
      simpl un_name in IH. destruct (print_name1 (10 * 36 ^ n) (lt_wf (10 * 36 ^ n))) as [ | b bs]; simpl; try congruence.
      replace ((10 * (36 * 36 ^ n)) mod 36) with 0; cycle 1.
      { pose proof (div_mod_uniqueness (10 * (36 * 36 ^ n)) 36 (10 * 36 ^ n) 0). lia. }
      rewrite L.replicate_rev_unfold. simpl in *. destruct (unAlphaNum b) as [d | ]; simpl in *.
      * destruct (d <? 10)%nat as [ | ]; congruence.
      * congruence.
Qed.

Lemma parse_prince_name n
  : parse_name (x61 :: L.replicate n x30) = Some (gen_prince_name n).
Proof.
  unfold gen_prince_name. unfold parse_name. induction n as [ | n IH]; simpl in *.
  - reflexivity.
  - replace (10 <? 10)%nat with false in * by reflexivity.
    rewrite B.observe_bind in IH |- *. destruct IH as [x [H_x EQ]].
    exists (36 * x). split.
    + rewrite L.replicate_rev_unfold. unfold parse_name1 in H_x |- *.
      simpl. rewrite fold_left_app. simpl. rewrite B.observe_bind.
      exists x. split.
      * unfold liftM2 in H_x. simpl in H_x. congruence.
      * f_equal; lia.
    + assert (x = 10 * 36 ^ n) as -> by congruence.
      do 2 f_equal. lia.
Qed.

Theorem prince_name_is_valid n
  : is_valid (gen_prince_name n) = true.
Proof.
  unfold is_valid. eapply B.bind_isSome_iff.
  exists (x61 :: L.replicate n x30).
  rewrite print_prince_name. rewrite parse_prince_name. simpl. split; trivial.
Qed.

Definition fresh_nm (nms : list name) : name :=
  let LE1 : 2 <= 36 := ltac:(repeat econs) in
  let LE2 : 1 <= 1 + un_name (maxs nms) := le_intro_plus_l _ _ in
  gen_prince_name (1 + log 36 (1 + un_name (maxs nms)) LE1 LE2).

Lemma fresh_nm_is_valid (nms : list name)
  : is_valid (fresh_nm nms) = true.
Proof.
  unfold fresh_nm. simpl. eapply prince_name_is_valid.
Qed.

Lemma fresh_nm_gt_maxs (nms : list name)
  : un_name (maxs nms) < un_name (fresh_nm nms).
Proof.
  unfold fresh_nm. set (maxs nms) as nm. set (1 + un_name nm) as n.
  simpl un_name. unfold n. red. replace (S (un_name nm)) with (1 + un_name nm) by reflexivity.
  fold n. set (m := log 36 n _ _).
  pose proof (exp_gt_0 36 m ltac:(repeat econs)).
  enough (n < 36 ^ (1 + m)) by lia.
  pose proof (exp_log_sandwitch 36 n ltac:(repeat econs) (le_intro_plus_l _ _)) as claim1.
  cbn zeta in claim1. destruct claim1 as [_ claim1]. simpl in claim1. fold m in claim1. trivial.
Qed.

Lemma fresh_nm_gt (nms : list name)
  : forall nm, In nm nms -> un_name nm < un_name (fresh_nm nms).
Proof.
  intros nm H_IN. pose proof (fresh_nm_gt_maxs nms) as claim1.
  red in claim1 |- *. rewrite <- claim1. eapply le_intro_S_n_le_S_m.
  clear claim1. revert nm H_IN. induction nms as [ | [n] nms IH]; simpl.
  - tauto.
  - intros nm [<- | H_IN]; simpl.
    + lia.
    + rewrite IH; trivial; lia.
Qed.

Lemma fresh_nm_notin (nms : list name)
  : ~ L.In (fresh_nm nms) nms.
Proof.
  intros IN. apply fresh_nm_gt in IN. lia.
Qed.

End PRINCE_NAME.

Definition fresh_nm_variant (nms : list name) : name :=
  next_name (maxs nms).

Lemma fresh_nm_variant_ne nms nm
  (IN : L.In nm nms)
  : ne nm (fresh_nm_variant nms).
Proof.
  unfold fresh_nm_variant. left. unfold next_name. simpl.
  enough (un_name nm <= un_name (maxs nms)) by lia.
  revert nm IN. induction nms as [ | nm' nms' IH]; simpl; intros.
  - contradiction.
  - destruct IN as [EQ | IN].
    + subst nm'. lia.
    + pose proof (IH nm IN) as claim. lia.
Qed.

Section PP_name_EXAMPLE1.

Let x1 : name :=
  "x1".

End PP_name_EXAMPLE1.

End Name.

Infix "≠" := Name.ne.
