Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.System.P.

Module LANG1.

Variant alphabet : Set :=
  | L
  | R.

#[local] Notation string := (list alphabet).
#[local] Notation lang := (ensemble string).
#[local] Infix " \in " := E.In : type_scope.

#[global]
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
      assert (IH2 : length (L :: s_prefix) < S (length s)) by now simpl; pose proof (@length_app _ s_prefix s'); subst s; lia.
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

Import LANG1.

#[local] Notation string := (list alphabet).
#[local] Notation lang := (ensemble string).
#[local] Infix " \in " := E.In : type_scope.

Inductive L_cfg2 : lang :=
  | cfg2_epsilon
    : [] \in L_cfg2
  | cfg2_paren str
    (H_in : str \in L_cfg2)
    : [L] ++ str ++ [R] \in L_cfg2
  | cfg2_concat str1 str2
    (H1_in : str1 \in L_cfg2)
    (H2_in : str2 \in L_cfg2)
    : str1 ++ str2 \in L_cfg2.

Section THEORY.

#[local] Hint Constructors L_cfg2 : core.

#[local] Notation count a s := (count_occ eq_dec s a).

Lemma count_L_sum_count_R s
  : count L s + count R s = length s.
Proof.
  induction s as [ | [ | ] s IHs]; simpl; lia.
Qed.

Inductive isPrefixOf (s_prefix : string) : string -> Prop :=
  | isPrefixOf_intro s_suffix
    : isPrefixOf s_prefix (s_prefix ++ s_suffix).

#[local] Infix "\prefix" := isPrefixOf (at level 70, no associativity) : type_scope.

#[local] Hint Constructors isPrefixOf : simplication_hints.

#[local] Hint Rewrite length_app length_firstn : simplication_hints.

#[global]
Instance isPrefixOf_Reflexive
  : Reflexive isPrefixOf.
Proof.
  intros s. rewrite <- app_nil_r with (l := s) at 2. econs.
Qed.

#[global]
Instance isPrefixOf_Transitive
  : Transitive isPrefixOf.
Proof.
  intros s1 s2 s3 H12 H23. inv H23. inv H12. rewrite <- app_assoc. econs.
Qed.

#[global]
Instance isPrefixOf_Antisymmetric
  : Antisymmetric string eq isPrefixOf.
Proof.
  intros s1 s2 H12 H21.
  inv H12. rename s_suffix into s2.
  inv H21. rename s_suffix into s3.
  pose proof (f_equal (@length alphabet) H) as HH.
  destruct s2, s3; ss!.
Qed.

Lemma app_isPrefixOf s s1 s2
  (PREFIX : s1 \prefix s2)
  : s ++ s1 \prefix s ++ s2.
Proof.
  inv PREFIX. rewrite -> app_assoc. econs.
Qed.

Lemma firstn_isPrefixOf n s
  : L.firstn n s \prefix s.
Proof.
  rewrite <- firstn_skipn with (n := n) (l := s) at 2. econs.
Qed.

Lemma isPrefixOf_inv {s : string} {s1 : string} {s2 : string}
  (H_prefix : s \prefix s1 ++ s2)
  : {s \prefix s1} + {exists s', s = s1 ++ s' /\ length s' > 0 /\ s' \prefix s2}.
Proof.
  destruct (Nat.leb (length s) (length s1)) as [ | ] eqn: H_OBS.
  - left. rewrite Nat.leb_le in H_OBS. inv H_prefix.
    pose proof (f_equal (firstn (length s)) H0) as HH.
    rewrite firstn_app in HH. replace (length s - length s)%nat with 0%nat in HH by lia.
    rewrite firstn_0 in HH. rewrite app_nil_r in HH. rewrite firstn_all in HH.
    rewrite firstn_app in HH. replace (length s - length s1)%nat with 0%nat in HH by lia.
    rewrite firstn_0 in HH. rewrite app_nil_r in HH. rewrite HH. eapply firstn_isPrefixOf.
  - right. rewrite Nat.leb_nle in H_OBS. inv H_prefix.
    pose proof (f_equal (firstn (length s)) H0) as HH.
    rewrite firstn_app in HH. replace (length s - length s)%nat with 0%nat in HH by lia.
    rewrite firstn_0 in HH. rewrite app_nil_r in HH. rewrite firstn_all in HH.
    rewrite firstn_app in HH. rewrite firstn_all2 with (l := s1) (n := length s) in HH by lia.
    exists (L.firstn (length s - length s1)%nat s2). repeat rewrite length_firstn.
    split; eauto. split.
    + pose proof (f_equal (@length alphabet) HH) as HH'. s!. lia.
    + pose proof (COPY := H0). rewrite HH in COPY. rewrite <- app_assoc in COPY.
      apply L.app_cancel_l with (prefix := s1) in COPY. rewrite <- COPY at 2. econs.
Qed.

Variant WellParen (s : string) : Prop :=
  | WellParen_intro
    (count_L_eq_count_R : count L s = count R s)
    (PREFIX : forall s_prefix, forall H_prefix : s_prefix \prefix s, count L s_prefix >= count R s_prefix).

Variant WellParen' (s : string) : Prop :=
  | WellParen'_intro
    (count_L_eq_count_R : count L s = count R s)
    (PREFIX : forall prefix, length prefix > 0 -> forall suffix, length suffix > 0 -> [L] ++ s ++ [R] = prefix ++ suffix -> count L prefix > count R prefix).

#[local] Hint Rewrite count_app app_assoc length_app app_nil_r : simplication_hints.

Lemma WellParen_iff_WellParen' s
  : WellParen s <-> WellParen' s.
Proof with eauto.
  split; intros [? ?].
  - econs... intros ? POS ? POS' H.
    destruct prefix as [ | [ | ] prefix]; s!; cycle -1.
    { congruence. }
    { exfalso; lia. }
    induction suffix as [ | [ | ] suffix _] using rev_ind; s!.
    { exfalso. lia. }
    { enough (R = L) by congruence.
      assert (H_view : R = last (L :: s ++ [R]) R).
      { rewrite L.last_cons. rewrite L.last_last... }
      assert (H_view' : L = last (L :: (prefix ++ suffix) ++ [L]) R).
      { rewrite L.last_cons. rewrite L.last_last... }
      congruence.
    }
    { apply L.app_cancel_l with (prefix := [L]) in H.
      apply L.app_cancel_r with (suffix := [R]) in H.
      exploit (PREFIX prefix); ss!.
    }
  - split... intros ? H_prefix; inversion H_prefix.
    rename s_prefix into s1, s_suffix into s2. subst s.
    enough (count L ([L] ++ s1) > count R ([L] ++ s1)) by ss!.
    eapply PREFIX with (prefix := [L] ++ s1) (suffix := s2 ++ [R]); ss!.
Qed.

Lemma WellParen_epsilon
  : WellParen [].
Proof.
  econs.
  - ss!.
  - intros ? H_prefix. inv H_prefix. destruct s_prefix as [ | [ | ] xs], s_suffix as [ | [ | ] ys]; s!; congruence || lia.
Qed.

Lemma WellParen_paren s
  (WELLPAREN : WellParen s)
  : WellParen ([L] ++ s ++ [R]).
Proof with eauto.
  econs.
  - ss!.
  - destruct WELLPAREN. intros xs Hxs. inv Hxs. destruct xs as [ | [ | ] s_prefix]; s!; try congruence || lia.
    induction s_suffix as [ | [ | ] s_suffix _] using rev_ind; s!.
    { apply L.app_cancel_l with (prefix := [L]) in H0. subst s_prefix. s!. lia. }
    { enough (R = L) by congruence.
      assert (H_view : R = last (L :: s ++ [R]) R).
      { rewrite L.last_cons. rewrite L.last_last... }
      assert (H_view' : L = last (L :: (s_prefix ++ s_suffix) ++ [L]) R).
      { rewrite L.last_cons. rewrite L.last_last... }
      congruence.
    }
    { apply L.app_cancel_l with (prefix := [L]) in H0.
      apply L.app_cancel_r with (suffix := [R]) in H0.
      exploit (PREFIX s_prefix); ss!.
    }
Qed.

Lemma WellParen_concat s1 s2
  (WELLPAREN1 : WellParen s1)
  (WELLPAREN2 : WellParen s2)
  : WellParen (s1 ++ s2).
Proof.
  destruct WELLPAREN1 as [H1H1 H1H2], WELLPAREN2 as [H2H1 H2H2]. econs.
  - s!. lia.
  - ii. pose proof (isPrefixOf_inv H_prefix) as [PREFIX | (s' & H_s_prefix & NOT_NIL & PREFIX')].
    + ss!.
    + subst s_prefix. s!.
      enough (count L s' >= count R s') by lia.
      ss!.
Qed.

#[local] Hint Resolve WellParen_epsilon WellParen_paren WellParen_concat : core.

Theorem cfg2_equiv_WellParen
  : L_cfg2 == WellParen.
Proof.
  change (forall s : string, s \in L_cfg2 <-> WellParen s). intros s. split.
  { intros H_in. induction H_in; eauto. }
  pose proof (relation_on_image_liftsWellFounded lt (@length alphabet) lt_wf s) as H_ACC.
  induction H_ACC as [s _ IH]. change (forall s' : string, length s' < length s -> WellParen s' -> s' \in L_cfg2) in IH.
  intros WELLPAREN. destruct s as [ | [ | ] s]; cycle -1.
  { inv WELLPAREN. exploit (PREFIX [R]); ss!. change ([R] \prefix [R] ++ s). econs. }
  { econs 1. }
  set (w := L :: s) in *.
  set (P := fun i : nat => i > 0 /\ count L (L.firstn i w) = count R (L.firstn i w)).
  assert (P_dec : forall i, {P i} + {~ P i}).
  { intros [ | n].
    - right. unfold P. intros [? ?]; lia.
    - set (i := S n) in *. pose proof (Nat.eq_dec (count L (L.firstn i w)) (count R (L.firstn i w))) as [YES | NO]; [left | right]; unfold P; lia.
  }
  exploit (dec_finds_minimum_if_exists P P_dec).
  { exists (length w). red. rewrite firstn_all. split; [cbn; lia | inv WELLPAREN; eauto]. }
  intros (j & H_j & MIN). change (forall i : nat, P i -> i >= j) in MIN.
  rewrite <- firstn_skipn with (n := j) (l := w). econs 3.
  - destruct H_j as [POS count_L_eq_count_R]. remember (L.firstn j w) as u eqn: H_u.
    assert (claim1 : forall v, v \prefix u -> length v > 0 -> length v < length u -> count L v > count R v).
    { intros v H_v H1_len_v H2_len_v.
      assert (H_prefix : v \prefix w).
      { transitivity u; [eauto | subst u; eapply firstn_isPrefixOf]. }
      assert (count L v >= count R v) as Hge.
      { destruct WELLPAREN. now eapply PREFIX. }
      enough (count L v <> count R v) by lia.
      intros H_contra.
      enough (length v >= j) by now rewrite H_u in H2_len_v; rewrite length_firstn in H2_len_v; lia.
      eapply MIN. split; eauto. replace (L.firstn (length v) w) with v; eauto.
      symmetry. inv H_prefix. rewrite firstn_app. replace (length v - length v)%nat with 0%nat by lia.
      simpl. rewrite app_nil_r. eapply firstn_all.
    }
    induction u as [ | [ | ] u _] using rev_ind.
    { destruct j as [ | n]; [lia | now subst w; simpl in *]. }
    { subst w. s!. destruct u as [ | [ | ] u].
      - s!. lia.
      - s!. exploit (claim1 (L :: u)).
        { eapply app_isPrefixOf with (s := [L]). econs. }
        { s!. lia. }
        { s!. lia. }
        intros HH. s!. exfalso; lia.
      - destruct j as [ | n]; s!; [lia | congruence].
    }
    { subst w. destruct j as [ | n]; s!; [lia | ]. destruct u as [ | [ | ] u]; s!; try congruence.
      econs 2. eapply IH.
      - apply L.app_cancel_l with (prefix := [L]) in H_u.
        pose proof (f_equal (@length alphabet) H_u). s!. lia.
      - econs.
        + lia.
        + intros ? H_prefix.
          assert (length s_prefix = 0 \/ length s_prefix > 0) as [NIL | NOT_NIL] by lia.
          { destruct s_prefix; s!; [lia | exfalso; lia]. }
          assert (length s_prefix < length u \/ length s_prefix >= length u) as [NOT_FULL | FULL] by lia.
          { enough (count L (L :: s_prefix) > count R (L :: s_prefix)) by now s!; lia. eapply claim1.
            - eapply app_isPrefixOf with (s := [L]). transitivity u; eauto. econs.
            - s!. lia.
            - s!. lia.
          }
          { inv H_prefix. destruct s_suffix; s!; lia. }
    }
  - destruct H_j as [POS count_L_eq_count_R]. eapply IH.
    + rewrite length_skipn. subst w. s!. destruct j; simpl; lia.
    + destruct WELLPAREN as [H1 H2]. econs.
      * rewrite <- firstn_skipn with (n := j) (l := w) in H1. s!. lia.
      * intros s_prefix H_prefix. exploit (H2 (L.firstn j w ++ s_prefix)).
        { rewrite <- firstn_skipn with (n := j) (l := w) at 2. now eapply app_isPrefixOf with (s := L.firstn j w). }
        { s!. lia. }
Qed.

End THEORY.

End LANG2.