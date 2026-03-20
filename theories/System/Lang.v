Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.ThN.
Require Import PnV.System.P.

Module LANG1.

Variant alphabet : Set :=
  | L
  | R.

#[local] Notation string := (list alphabet).
#[local] Notation lang := (ensemble string).
#[local] Infix " \in " := E.In : type_scope.

#[local]
Instance alphabet_hasEqDec
  : hasEqDec alphabet.
Proof.
  red. decide equality.
Defined.

Inductive L_cfg1 : lang :=
  | cfg1_rule1
    : [] \in L_cfg1
  | cfg1_rule2 str
    (H_str : str \in L_cfg1)
    : [L] ++ str ++ [R] \in L_cfg1
  | cfg1_rule3 str
    (H_str : str \in L_cfg1)
    : [R] ++ str ++ [L] \in L_cfg1
  | cfg1_rule4 str1 str2
    (H_str1 : str1 \in L_cfg1)
    (H_str2 : str2 \in L_cfg1)
    : str1 ++ str2 \in L_cfg1.

#[local] Hint Constructors L_cfg1 : core.

#[local] Notation count a s := (count_occ eq_dec s a).

Variant cfg1_spec LANG : Prop :=
  | cfg1_lang_spec
    (nL_eq_nR : forall str, str \in LANG <-> count L str = count R str)
    : cfg1_spec LANG.

Section THEORY.

Lemma count_app a s s'
  : count a (s ++ s') = count a s + count a s'.
Proof.
  revert a s'; induction s as [ | [ | ] s IH]; intros [ | ] s'; simpl; eauto.
Qed.

Lemma count_app_cancel_l a s s' n n'
  (H_s_app_s' : count a (s ++ s') = n + n')
  (H_s : count a s = n)
  : count a s' = n'.
Proof.
  revert a s' n n' H_s_app_s' H_s; induction s as [ | [ | ] s IH]; intros [ | ]; simpl; i; subst n; eauto.
Qed.

Lemma count_app_cancel_r a s s' n n'
  (H_s_app_s' : count a (s ++ s') = n + n')
  (H_s' : count a s' = n')
  : count a s = n.
Proof.
  subst n'. revert a s' n H_s_app_s'. induction s' as [ | [ | ] s' IH] using List.rev_ind; simpl; i.
  all: try rewrite Nat.add_0_r in *; try rewrite app_nil_r in *; eauto.
  all: erewrite count_occ_app with (l1 := s) (l2 := s' ++ [_]) in H_s_app_s'; lia.
Qed.

Lemma cfg1_soundness s
  (H_in : s \in L_cfg1)
  : count L s = count R s.
Proof with eauto.
  induction H_in as [ | s1 H_in1 IH1 | s2 H_in2 IH2 | s1 s2 H_in1 IH1 H_in2 IH2]; simpl...
  - rewrite <- rev_involutive with (l := _ ++ [_]). rewrite rev_unit.
    do 2 rewrite count_occ_rev. simpl. do 2 rewrite count_occ_rev...
  - rewrite <- rev_involutive with (l := _ ++ [_]). rewrite rev_unit.
    do 2 rewrite count_occ_rev. simpl. do 2 rewrite count_occ_rev...
  - do 2 rewrite count_occ_app...
Qed.

Inductive isLast a : string -> Prop :=
  | isLast_1
    : isLast a [a]
  | isLast_S a' s
    (H_isLast : isLast a s)
    : isLast a (a' :: s).

#[local] Hint Constructors isLast : core.

Lemma isLast_elim a s
  (H_isLast : isLast a s)
  : exists s', s = s' ++ [a].
Proof.
  induction H_isLast as [ | a' s H_isLast [s' IH]].
  - exists []; eauto.
  - rewrite IH. exists (a' :: s'). reflexivity.
Qed.

Variant string_cut s : Prop :=
  | string_cut_intro s_prefix s'
    (H_app : s = s_prefix ++ s')
    (H_len : length s' > 0)
    (H_cut : count L s' = count R s')
    : string_cut s.

Lemma if_count_L_s_lt_count_R_s s
  (count_L_s_lt_count_R_s : count L s < count R s)
  : string_cut s \/ isLast R s.
Proof with eauto.
  revert count_L_s_lt_count_R_s; set (black := L); set (white := R).
  induction s as [ | [ | ] s IHs]; simpl; try lia; i.
  - assert (IH : count black s < count white s) by lia.
    apply IHs in IH. destruct IH as [IH | IH]...
    inversion IH; subst. left. eapply string_cut_intro with (s' := s') (s_prefix := black :: s_prefix)...
  - assert (count black s = count white s \/ count black s < count white s) as [IH | IH] by lia.
    + destruct s as [ | a' s']...
      left. eapply string_cut_intro with (s' := a' :: s') (s_prefix := [white])... simpl; lia.
    + apply IHs in IH. destruct IH as [IH | IH]...
      left. inversion IH; subst. eapply string_cut_intro with (s' := s') (s_prefix := white :: s_prefix)...
Qed.

Lemma if_count_L_s_gt_count_R_s s
  (count_L_s_gt_count_R_s : count L s > count R s)
  : string_cut s \/ isLast L s.
Proof with eauto.
  revert count_L_s_gt_count_R_s; set (black := R); set (white := L).
  induction s as [ | [ | ] s IHs]; simpl; try lia; i; cycle -1.
  - assert (IH : count black s < count white s) by lia.
    apply IHs in IH. destruct IH as [IH | IH]...
    inversion IH; subst. left. eapply string_cut_intro with (s' := s') (s_prefix := black :: s_prefix)...
  - assert (count black s = count white s \/ count black s < count white s) as [IH | IH] by lia.
    + destruct s as [ | a' s']...
      left. eapply string_cut_intro with (s' := a' :: s') (s_prefix := [white])... simpl; lia.
    + apply IHs in IH. destruct IH as [IH | IH]...
      left. inversion IH; subst. eapply string_cut_intro with (s' := s') (s_prefix := white :: s_prefix)...
Qed.

Theorem cfg1_completeness s
  (count_L_eq_count_R : count L s = count R s)
  : s \in L_cfg1.
Proof with eauto.
  revert count_L_eq_count_R. pose proof (relation_on_image_liftsWellFounded lt (@length alphabet) lt_wf s) as H_ACC.
  unfold binary_relation_on_image in H_ACC. induction H_ACC as [[ | [ | ] s] _ IHs]; simpl in *; i...
  - assert (count_L_s_lt_count_R_s : count L s < count R s) by lia.
    apply if_count_L_s_lt_count_R_s in count_L_s_lt_count_R_s.
    destruct count_L_s_lt_count_R_s as [[? ? ? ? ?] | H_last_R].
    + assert (IH1 : length s' < S (length s)) by now pose proof (@length_app _ s_prefix s'); subst s; lia.
      pose proof (IHs s' IH1 H_cut) as H_s'.
      assert (IH2: length (L :: s_prefix) < S (length s)) by now simpl; pose proof (@length_app _ s_prefix s'); subst s; lia.
      assert (CLAIM : count L (L :: s_prefix) = count R (L :: s_prefix)).
      { eapply count_app_cancel_r with (s := L :: s_prefix) (s' := s') (n' := count R s')...
        simpl. rewrite <- H_app. rewrite <- count_app. rewrite <- H_app...
      }
      assert (H_prefix : L :: s_prefix \in L_cfg1)...
      rewrite H_app. eapply cfg1_rule4 with (str1 := L :: s_prefix) (str2 := s')...
    + apply isLast_elim in H_last_R. destruct H_last_R as [s' ->]; simpl in *. eapply cfg1_rule2. eapply IHs.
      * replace (length (s' ++ [R])) with (length (rev (R :: rev s'))) by now simpl; f_equal; rewrite rev_involutive.
        rewrite length_rev. simpl. rewrite length_rev. lia.
      * rewrite <- rev_involutive with (l := s' ++ [R]) in count_L_eq_count_R.
        rewrite -> rev_unit in count_L_eq_count_R. do 2 rewrite count_occ_rev in count_L_eq_count_R.
        simpl in count_L_eq_count_R. apply f_equal with (f := Nat.pred) in count_L_eq_count_R.
        simpl in count_L_eq_count_R. do 2 rewrite count_occ_rev in count_L_eq_count_R...
  - assert (count_L_s_gt_count_R_s : count L s > count R s) by lia.
    apply if_count_L_s_gt_count_R_s in count_L_s_gt_count_R_s.
    destruct count_L_s_gt_count_R_s as [[? ? ? ? ?] | H_last_L].
    + assert (IH1 : length s' < S (length s)) by now pose proof (@length_app _ s_prefix s'); subst s; lia.
      pose proof (IHs s' IH1 H_cut) as H_s'.
      assert (IH2 : length (R :: s_prefix) < S (length s)) by now simpl; pose proof (@length_app _ s_prefix s'); subst s; lia.
      assert (CLAIM : count L (R :: s_prefix) = count R (R :: s_prefix)).
      { eapply count_app_cancel_r with (s := R :: s_prefix) (s' := s') (n' := count R s')...
        simpl. rewrite <- H_app. rewrite <- count_app. rewrite <- H_app...
      }
      assert (H_prefix : R :: s_prefix \in L_cfg1)...
      rewrite H_app. eapply cfg1_rule4 with (str1 := R :: s_prefix) (str2 := s')...
    + apply isLast_elim in H_last_L. destruct H_last_L as [s' ->]; simpl in *. eapply cfg1_rule3. eapply IHs.
      * replace (length (s' ++ [L])) with (length (rev (L :: rev s'))) by now simpl; f_equal; rewrite rev_involutive.
        rewrite length_rev. simpl. rewrite length_rev. lia.
      * rewrite <- rev_involutive with (l := s' ++ [L]) in count_L_eq_count_R.
        rewrite -> rev_unit in count_L_eq_count_R. do 2 rewrite count_occ_rev in count_L_eq_count_R.
        simpl in count_L_eq_count_R. apply f_equal with (f := Nat.pred) in count_L_eq_count_R.
        simpl in count_L_eq_count_R. do 2 rewrite count_occ_rev in count_L_eq_count_R...
Qed.

Corollary L_cfg1_satisfies_its_spec
  : cfg1_spec L_cfg1.
Proof.
  constructor. intros s. split.
  - exact (cfg1_soundness s).
  - exact (cfg1_completeness s).
Qed.

End THEORY.

End LANG1.

Module LANG2.

Variant alphabet : Set :=
  | L
  | R.

#[local] Notation string := (list alphabet).
#[local] Notation lang := (ensemble string).
#[local] Infix " \in " := E.In : type_scope.

#[local]
Instance alphabet_hasEqDec
  : hasEqDec alphabet.
Proof.
  red. decide equality.
Defined.

Inductive L_cfg2 : lang :=
  | cfg2_epsilon
    : [] \in L_cfg2
  | cfg2_paren str
    (H_cfg2 : str \in L_cfg2)
    : [L] ++ str ++ [R] \in L_cfg2
  | cfg2_app str1 str2
    (H_str1: str1 \in L_cfg2)
    (H_str2: str2 \in L_cfg2)
    : str1 ++ str2 \in L_cfg2.

#[local] Hint Constructors L_cfg2 : core.

#[local] Notation count a s := (count_occ eq_dec s a).

End LANG2.
