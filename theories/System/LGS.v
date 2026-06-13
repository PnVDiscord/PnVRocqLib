Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Strings.String.
Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Monad.
Require Import PnV.Data.FiniteMap.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Data.Graph.
Require Import PnV.System.Regex.

Import DoNotations.
Import DigraphFixedpoint.

#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "=~=" := (is_similar_to (Similarity := Re.in_regex eq)) : type_scope.
#[local] Infix "∈" := L.In.
#[local] Infix "⊑" := is_similar_to.

#[local] Existing Instance Similarity_bool_Prop.

#[global]
Instance ascii_hasEqDec
  : hasEqDec@{Set} ascii.
Proof.
  exact Ascii.ascii_dec.
Defined.

#[global]
Instance regex_hasEqDec {A : Set}
  (A_hasEqDec : hasEqDec@{Set} A)
  : hasEqDec@{Set} (regex A).
Proof.
  red in A_hasEqDec |- *. decide equality.
Defined.

Module Bool_FinEnum <: FINITE_ENUM.

Definition t : Set :=
  bool.

Definition t_hasEqDec : hasEqDec@{Set} Bool_FinEnum.t :=
  bool_hasEqDec.

Definition all : list bool :=
  [false; true].

Lemma all_complete
  : forall x : Bool_FinEnum.t, L.In x Bool_FinEnum.all.
Proof.
  intros x; destruct x; simpl; tauto.
Qed.

Lemma all_no_dup
  : NoDup Bool_FinEnum.all.
Proof.
  assert (EQ : L.nodup (@eq_dec bool bool_hasEqDec) all = all) by (vm_compute; reflexivity).
  rewrite <- EQ. eapply L.NoDup_nodup.
Qed.

End Bool_FinEnum.

Notation all_bools := Bool_FinEnum.all.

Notation all_bools_complete := Bool_FinEnum.all_complete.

Module Ascii_FinEnum <: FINITE_ENUM.

Definition t : Set :=
  ascii.

Definition t_hasEqDec : hasEqDec@{Set} Ascii_FinEnum.t :=
  ascii_hasEqDec.

Definition all : list ascii := do
  'b0 <- all_bools;
  'b1 <- all_bools;
  'b2 <- all_bools;
  'b3 <- all_bools;
  'b4 <- all_bools;
  'b5 <- all_bools;
  'b6 <- all_bools;
  'b7 <- all_bools;
  ret (Ascii b0 b1 b2 b3 b4 b5 b6 b7)
  end.

Lemma all_complete
  : forall x : Ascii_FinEnum.t, L.In x Ascii_FinEnum.all.
Proof.
  intros c; unfold all; destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  eapply list_bind_complete with (x := b0); [eapply all_bools_complete | ].
  eapply list_bind_complete with (x := b1); [eapply all_bools_complete | ].
  eapply list_bind_complete with (x := b2); [eapply all_bools_complete | ].
  eapply list_bind_complete with (x := b3); [eapply all_bools_complete | ].
  eapply list_bind_complete with (x := b4); [eapply all_bools_complete | ].
  eapply list_bind_complete with (x := b5); [eapply all_bools_complete | ].
  eapply list_bind_complete with (x := b6); [eapply all_bools_complete | ].
  eapply list_bind_complete with (x := b7); [eapply all_bools_complete | ].
  eapply list_pure_complete.
Qed.

Lemma all_no_dup
  : NoDup Ascii_FinEnum.all.
Proof.
  assert (EQ : L.nodup (@eq_dec ascii ascii_hasEqDec) all = all) by reflexivity.
  rewrite <- EQ. eapply L.NoDup_nodup.
Qed.

End Ascii_FinEnum.

Notation all_asciis := Ascii_FinEnum.all.

Notation all_asciis_complete := Ascii_FinEnum.all_complete.

Module LGS.

#[projections(primitive)]
Class isToken `(Token : Set) : Set :=
  { Token_hasEqDec : hasEqDec@{Set} Token
  ; rulesForTokens : list (Token * regex ascii)
  }.

#[global] Existing Instance Token_hasEqDec.

Fact mem_spec (A : Set) `(A_hasEqDec : hasEqDec@{Set} A) (x : A) (xs : list A) (b : bool)
  : mem x xs = b <-> (if b then x ∈ xs else ~ x ∈ xs).
Proof.
  destruct b; [eapply mem_true_iff | eapply mem_false_iff].
Qed.

Fact eqb_iff (A : Set) `(A_hasEqDec : hasEqDec@{Set} A) (x : A) (y : A) (b : bool)
  : eqb x y = b <-> (if b then x = y else ~ x = y).
Proof.
  eapply eqb_spec.
Qed.

Fact existsb_iff (A : Set) (p : A -> bool) (xs : list A)
  : existsb p xs = true <-> (exists x, x ∈ xs /\ p x = true).
Proof.
  eapply L.existsb_exists.
Qed.

Fact forallb_iff (A : Set) (p : A -> bool) (xs : list A)
  : forallb p xs = true <-> (forall x, x ∈ xs -> p x = true).
Proof.
  eapply forallb_forall.
Qed.

#[local] Hint Rewrite mem_spec eqb_iff existsb_iff forallb_iff : simplication_hints.

#[local] Existing Instance list_corresponds_to_finite_ensemble.
#[local] Existing Instance alist_corresponds_to_finite_partial_map.

Module Input.

Definition t : Set :=
  list ascii.

Fixpoint of_string (s : string) : Input.t :=
  match s with
  | EmptyString => []
  | String c s' => c :: of_string s'
  end.

Fixpoint to_string (s : Input.t) : string :=
  match s with
  | [] => EmptyString
  | c :: s' => String c (to_string s')
  end.

Fact to_of_string (s : string)
  : to_string (of_string s) = s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Fact of_to_string (s : Input.t)
  : of_string (to_string s) = s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Fact length_of_string (s : string)
  : length (of_string s) = String.length s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Fact to_string_app (s1 : Input.t) (s2 : Input.t)
  : to_string (s1 ++ s2) = String.append (to_string s1) (to_string s2).
Proof.
  induction s1 as [ | c s1 IH]; simpl; congruence.
Qed.

Fact prefix_suffix_decompose (s : Input.t) (n : nat)
  (LE : n <= length s)
  : exists prefix, exists suffix, s = prefix ++ suffix /\ length prefix = n.
Proof.
  exists (firstn n s). exists (skipn n s). rewrite firstn_skipn. 
  split; [reflexivity | rewrite length_firstn; lia].
Qed.

Fact app_cancel_prefix (prefix : Input.t) (s1 : Input.t) (s2 : Input.t)
  (EQ : prefix ++ s1 = prefix ++ s2)
  : s1 = s2.
Proof.
  eapply L.app_cancel_l; eauto.
Qed.

Fact app_cancel_suffix (s1 : Input.t) (s2 : Input.t) (suffix : Input.t)
  (EQ : s1 ++ suffix = s2 ++ suffix)
  : s1 = s2.
Proof.
  eapply L.app_cancel_r; eauto.
Qed.

Fact empty_or_nonempty (s : Input.t)
  : { s = [] } + { exists c, exists s', s = c :: s' }.
Proof.
  destruct s as [ | c s']; [left; reflexivity | right; exists c, s'; reflexivity].
Defined.

Fact nonempty_prefix_rest_shorter (consumed : Input.t) (rest : Input.t)
  (NONEMPTY : ~ consumed = [])
  : length rest < length (consumed ++ rest).
Proof.
  destruct consumed as [ | c consumed]; [contradiction | simpl; rewrite length_app; simpl; lia].
Qed.

End Input.

Fixpoint nullable (e : regex ascii) {struct e} : bool :=
  match e with
  | Re.Null => false
  | Re.Empty => true
  | Re.Char c => false
  | Re.Union e1 e2 => nullable e1 || nullable e2
  | Re.Append e1 e2 => nullable e1 && nullable e2
  | Re.Star e1 => true
  end.

Lemma nullable_spec (e : regex ascii)
  : nullable e = true <-> [] =~= e.
Proof.
  split.
  - induction e as [ | | c | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH]; simpl; i; try congruence.
    + econs.
    + rewrite orb_true_iff in H. destruct H as [H | H]; eauto with *.
    + rewrite andb_true_iff in H. destruct H as [H1 H2]. change (@nil ascii) with (@nil ascii ++ @nil ascii). eauto with *.
    + econs.
  - revert e.
    enough (CLAIM : forall s, forall e, s =~= e -> s = [] -> nullable e = true).
    { i; eapply CLAIM; eauto. }
    intros s e H_IN. induction H_IN; simpl; i; subst; try congruence; eauto.
    + rewrite orb_true_iff. left. eauto.
    + rewrite orb_true_iff. right. eauto.
    + pose proof (app_eq_nil _ _ H) as [EQ1 EQ2]; ss!.
Qed.

Theorem nullable_true_iff (e : regex ascii)
  : nullable e = true <-> [] \in eval_regex e.
Proof.
  rewrite eval_regex_good. eapply nullable_spec.
Qed.

Theorem nullable_false_iff (e : regex ascii)
  : nullable e = false <-> (~ [] \in eval_regex e).
Proof.
  destruct (nullable e) eqn: H_OBS; split; intros H.
  - congruence.
  - contradiction H. rewrite <- nullable_true_iff. exact H_OBS.
  - intros IN. rewrite <- nullable_true_iff in IN. congruence.
  - reflexivity.
Qed.

Corollary nullable_refinement (e : regex ascii)
  : nullable e ⊑ ([] \in eval_regex e).
Proof.
  destruct (nullable e) as [ | ] eqn: H_OBS; red; simpl.
  - now rewrite nullable_true_iff in H_OBS.
  - now rewrite nullable_false_iff in H_OBS.
Qed.

Lemma union_inv (s : Input.t) (e1 : regex ascii) (e2 : regex ascii)
  (IN : s \in eval_regex (Re.Union e1 e2))
  : s \in eval_regex e1 \/ s \in eval_regex e2.
Proof.
  simpl in IN. destruct IN as [IN | IN]; [left | right]; exact IN.
Qed.

Lemma append_inv (s : Input.t) (e1 : regex ascii) (e2 : regex ascii)
  (IN : s \in eval_regex (Re.Append e1 e2))
  : exists s1, exists s2, s = s1 ++ s2 /\ s1 \in eval_regex e1 /\ s2 \in eval_regex e2.
Proof.
  cbn [eval_regex] in IN. rewrite E.liftM2_spec in IN. firstorder.
Qed.

Fact star_nil (e : regex ascii)
  : [] \in eval_regex (Re.Star e).
Proof.
  econs 1.
Qed.

Lemma star_inv (s : Input.t) (e : regex ascii)
  (IN : s \in eval_regex (Re.Star e))
  : s = [] \/ (exists s1, exists s2, s = s1 ++ s2 /\ s1 \in eval_regex e /\ s2 \in eval_regex (Re.Star e)).
Proof.
  inv IN; firstorder.
Qed.

End LGS.
