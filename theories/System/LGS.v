Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Strings.String.
Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Monad.
Require Import PnV.Data.FiniteMap.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Data.Graph.
Require Import PnV.System.Regex.
Require Import PnV.Prelude.X.

Import DoNotations.

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

Abbreviation all_bools := Bool_FinEnum.all.

Abbreviation in_all_bools_intro := Bool_FinEnum.in_all_intro.

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
  ret (Ascii b0 b1 b2 b3 b4 b5 b6 b7).

Lemma in_all_intro
  : forall x : Ascii_FinEnum.t, L.In x Ascii_FinEnum.all.
Proof.
  unfold all; intros [b0 b1 b2 b3 b4 b5 b6 b7].
  eapply in_list_bind_intro with (x := b0); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b1); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b2); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b3); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b4); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b5); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b6); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b7); [eapply in_all_bools_intro | ].
  eapply in_list_pure_intro.
Qed.

Lemma all_no_dup
  : NoDup Ascii_FinEnum.all.
Proof.
  assert (EQ : L.nodup (@eq_dec@{Set} ascii ascii_hasEqDec) all = all) by reflexivity.
  rewrite <- EQ. eapply L.NoDup_nodup.
Qed.

End Ascii_FinEnum.

Abbreviation all_asciis := Ascii_FinEnum.all.

Abbreviation in_all_asciis_intro := Ascii_FinEnum.in_all_intro.

Module Type TOKEN_SPEC.

Parameter t : Set.

Parameter t_hasEqDec : hasEqDec@{Set} TOKEN_SPEC.t.

Parameter rules : list (TOKEN_SPEC.t * regex ascii).

End TOKEN_SPEC.

Module BuildError.

Inductive t : Set :=
  | NullableTokenRule (idx : nat).

End BuildError.

#[universes(polymorphic=yes)]
Definition BuildErrorM@{u | } (A : Type@{u}) : Type@{u} :=
  BuildError.t + A.

#[universes(polymorphic=yes)]
Instance BuildErrorM_isMonad@{u} : isMonad@{u u} BuildErrorM@{u} :=
  { pure {A : Type@{u}} (x : A) := inr x
  ; bind {A : Type@{u}} {B : Type@{u}} (m : BuildErrorM A) (k : A -> BuildErrorM B) := B.either (@inl BuildError.t B) k m
  }.

#[local] Hint Rewrite eqb_spec@{Set} : simplication_hints.
#[local] Hint Rewrite mem_spec : simplication_hints.
#[local] Hint Rewrite existsb_iff : simplication_hints.
#[local] Hint Rewrite forallb_iff : simplication_hints.
#[global] Hint Rewrite in_union_iff: simplication_hints.
#[global] Hint Rewrite in_normalize_iff : simplication_hints.
#[global] Hint Rewrite in_unions_iff : simplication_hints.
#[global] Hint Rewrite product_iff : simplication_hints.

#[local] Hint Rewrite L.filter_In : simplication_hints.

#[local] Existing Instance list_corresponds_to_finite_ensemble.
#[local] Existing Instance alist_corresponds_to_finite_partial_map.

Module MkLGS (Token : TOKEN_SPEC).

#[global] Existing Instance Token.t_hasEqDec.

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

Theorem to_of_string (s : string)
  : to_string (of_string s) = s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Theorem of_to_string (s : Input.t)
  : of_string (to_string s) = s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Theorem length_of_string (s : string)
  : length (of_string s) = String.length s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Theorem to_string_app (s1 : Input.t) (s2 : Input.t)
  : to_string (s1 ++ s2) = String.append (to_string s1) (to_string s2).
Proof.
  induction s1 as [ | c s1 IH]; simpl; congruence.
Qed.

Theorem prefix_suffix_decompose (s : Input.t) (n : nat)
  (LE : n <= length s)
  : exists prefix, exists suffix, s = prefix ++ suffix /\ length prefix = n.
Proof.
  exists (firstn n s), (skipn n s). rewrite firstn_skipn. rewrite length_firstn. done.
Qed.

Theorem app_cancel_prefix (prefix : Input.t) (s1 : Input.t) (s2 : Input.t)
  (EQ : prefix ++ s1 = prefix ++ s2)
  : s1 = s2.
Proof.
  eapply L.app_cancel_l. exact EQ.
Qed.

Theorem app_cancel_suffix (s1 : Input.t) (s2 : Input.t) (suffix : Input.t)
  (EQ : s1 ++ suffix = s2 ++ suffix)
  : s1 = s2.
Proof.
  eapply L.app_cancel_r. exact EQ.
Qed.

Theorem empty_or_nonempty (s : Input.t)
  : { s = [] } + { exists c, exists s', s = c :: s' }.
Proof.
  destruct s as [ | c s']; [left; reflexivity | right; exists c, s'; reflexivity].
Defined.

Theorem nonempty_prefix_rest_shorter (consumed : Input.t) (rest : Input.t)
  (NONEMPTY : consumed ≠ [])
  : length rest < length (consumed ++ rest).
Proof.
  destruct consumed as [ | c consumed]; done.
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

Lemma nullable_similar_spec (e : regex ascii)
  : nullable e = true <-> [] =~= e.
Proof.
  split.
  - induction e as [ | | c | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH]; simpl; i; try congruence.
    + econs.
    + rewrite orb_true_iff in H. destruct H as [H | H]; eauto with *.
    + rewrite andb_true_iff in H. destruct H as [H1 H2].
      change (@nil ascii) with (@nil ascii ++ @nil ascii); eauto with *.
    + econs.
  - revert e.
    enough (CLAIM : forall s, forall e, s =~= e -> s = [] -> nullable e = true).
    { i. eapply CLAIM; eauto. }
    intros s e H_IN; induction H_IN; simpl; i; subst; try congruence.
    + rewrite orb_true_iff. left. eauto.
    + rewrite orb_true_iff. right. eauto.
    + pose proof (app_eq_nil _ _ H) as [EQ1 EQ2]. done.
Qed.

Theorem nullable_true_iff (e : regex ascii)
  : nullable e = true <-> [] \in eval_regex e.
Proof.
  rewrite eval_regex_good. eapply nullable_similar_spec.
Qed.

Theorem nullable_false_iff (e : regex ascii)
  : nullable e = false <-> (~ [] \in eval_regex e).
Proof.
  destruct (nullable _) eqn: EQ; split; intros H.
  - congruence.
  - contradiction H. rewrite <- nullable_true_iff. exact EQ.
  - intros IN. rewrite <- nullable_true_iff in IN. congruence.
  - reflexivity.
Qed.

Corollary nullable_refines (e : regex ascii)
  : nullable e ⊑ ([] \in eval_regex e).
Proof.
  destruct (nullable _) as [ | ] eqn: H_OBS.
  - now rewrite nullable_true_iff in H_OBS.
  - now rewrite nullable_false_iff in H_OBS.
Qed.

Lemma union_inv (s : Input.t) (e1 : regex ascii) (e2 : regex ascii)
  (IN : s \in eval_regex (Re.Union e1 e2))
  : s \in eval_regex e1 \/ s \in eval_regex e2.
Proof.
  ss!.
Qed.

Theorem append_inv (s : Input.t) (e1 : regex ascii) (e2 : regex ascii)
  (IN : s \in eval_regex (Re.Append e1 e2))
  : exists s1, exists s2, s = s1 ++ s2 /\ s1 \in eval_regex e1 /\ s2 \in eval_regex e2.
Proof.
  ss!.
Qed.

Lemma star_nil (e : regex ascii)
  : [] \in eval_regex (Re.Star e).
Proof.
  ss!.
Qed.

Lemma star_inv (s : Input.t) (e : regex ascii)
  (IN : s \in eval_regex (Re.Star e))
  : s = [] \/ (exists s1, exists s2, s = s1 ++ s2 /\ s1 \in eval_regex e /\ s2 \in eval_regex (Re.Star e)).
Proof.
  simpl in IN; inv IN; ss!.
Qed.

Module Rule.

#[projections(primitive)]
Record t : Set :=
  mk
  { index : nat
  ; token : Token.t
  ; regex : Re.t ascii
  } as rule.

#[global]
Instance Rule_hasEqDec
  : hasEqDec@{Set} Rule.t.
Proof.
  red; decide equality; eapply eq_dec.
Defined.

Definition compileRule (rule : Rule.t) : BuildErrorM@{Set} Rule.t :=
  if nullable rule.(Rule.regex) then
    inl (BuildError.NullableTokenRule rule.(Rule.index))
  else
    pure rule.

Lemma compileRule_preserves (rule : Rule.t) (rule' : Rule.t)
  (COMPILE : compileRule rule = inr rule')
  : rule = rule'.
Proof.
  unfold compileRule in COMPILE. now destruct (nullable _); inv COMPILE.
Qed.

Theorem compileRule_spec (rule : Rule.t) (rule' : Rule.t)
  (COMPILE : compileRule rule = inr rule')
  : forall s, s \in eval_regex rule.(Rule.regex) <-> s \in eval_regex rule'.(Rule.regex).
Proof.
  now i; rewrite compileRule_preserves with (rule := rule) (rule' := rule').
Qed.

Lemma compileRule_guarantees_consumption (rule : Rule.t) (rule' : Rule.t)
  (COMPILE : compileRule rule = inr rule')
  : ~ ([] \in eval_regex rule'.(Rule.regex)).
Proof.
  rewrite <- nullable_false_iff. now unfold compileRule in COMPILE; destruct (nullable _) eqn: NULLABLE; inv COMPILE.
Qed.

Fixpoint compileRules (rules : list Rule.t) {struct rules} : BuildErrorM (list Rule.t) :=
  match rules with
  | [] => pure (@nil Rule.t)
  | rule :: rules => liftM2 (@cons Rule.t) (compileRule rule) (compileRules rules)
  end.

Theorem compileRules_preserves (rules : list Rule.t) (rules' : list Rule.t)
  (COMPILE : compileRules rules = inr rules')
  : rules = rules'.
Proof.
  revert rules' COMPILE; induction rules as [ | rule rules IH]; ii; simpl in *; try congruence.
  destruct (compileRule _) as [err | rule1] eqn: H_OBS1; simpl in *; try congruence.
  destruct (compileRules _) as [err | rules2] eqn: H_OBS2; simpl in *; try congruence.
  rewrite compileRule_preserves with (rule := rule) (rule' := rule1) by eauto.
  inv COMPILE. f_equal. now eapply IH.
Qed.

Definition accepts (rule : Rule.t) (s : Input.t) : Prop :=
  s \in eval_regex rule.(Rule.regex).

Theorem compileRules_success_intro (rules : list Rule.t)
  (NOT_NULLABLE : forall rule, rule ∈ rules -> nullable rule.(Rule.regex) = false)
  : compileRules rules = inr rules.
Proof.
  induction rules as [ | rule rules IH]; simpl; eauto.
  unfold compileRule at 1. rewrite NOT_NULLABLE by now left.
  cbn. now rewrite IH by ss!.
Qed.

Theorem compileRules_success_elim (rules : list Rule.t) (rules' : list Rule.t) (rule : Rule.t)
  (COMPILE : compileRules rules = inr rules')
  (IN : rule ∈ rules')
  : rule ∈ rules /\ (~ accepts rule []).
Proof.
  revert rules' COMPILE rule IN; induction rules as [ | rule rules IH]; intros rules' COMPILE rule0 IN; simpl in COMPILE.
  - now inv COMPILE. 
  - destruct (compileRule _) as [err | rule'] eqn: COMPILE_RULE; cbn in COMPILE; try congruence.
    destruct (compileRules _) as [err | rules0] eqn: COMPILE_RULES; cbn in COMPILE; try congruence.
    inv COMPILE. simpl in IN. destruct IN as [EQ | IN]; subst.
    + pose proof (compileRule_preserves rule rule0 COMPILE_RULE) as EQ; subst rule0.
      split; eauto with *. eapply compileRule_guarantees_consumption. exact COMPILE_RULE.
    + pose proof (IH rules0 eq_refl rule0 IN) as [IN_RULES NONEMPTY]; ss!.
Qed.

Theorem compile_rules_failure_intro (rules : list Rule.t)
  (NULLABLE : exists rule, rule ∈ rules /\ nullable rule.(Rule.regex) = true)
  : exists idx, compileRules rules = inl (BuildError.NullableTokenRule idx).
Proof.
  induction rules as [ | rule rules IH].
  - now destruct NULLABLE as (rule & IN & _).
  - destruct NULLABLE as (bad_rule & [EQ | IN_RULES] & NULLABLE); subst; simpl.
    + unfold compileRule at 1. rewrite NULLABLE. ss!.
    + destruct (compileRule _) as [[idx] | rule'] eqn: COMPILE_RULE; cbn; eauto.
      pose proof (IH (@ex_intro _ _ bad_rule (conj IN_RULES NULLABLE))) as (idx & FAILURE).
      rewrite FAILURE. ss!.
Qed.

Theorem compileRules_failure_elim (rules : list Rule.t) (err : BuildError.t)
  (COMPILE : compileRules rules = inl err)
  : exists rule, rule ∈ rules /\ nullable rule.(Rule.regex) = true /\ err = BuildError.NullableTokenRule rule.(Rule.index).
Proof.
  revert err COMPILE; induction rules as [ | rule rules IH]; ii; simpl in COMPILE; try congruence.
  destruct (compileRule _) as [err' | rule'] eqn: COMPILE_RULE; cbn in COMPILE.
  - inv COMPILE. unfold compileRule in COMPILE_RULE.
    destruct (nullable _) eqn: NULLABLE; inv COMPILE_RULE; ss!.
  - destruct (compileRules _) as [err' | rules'] eqn: COMPILE_RULES; cbn in COMPILE; try congruence.
    inv COMPILE. pose proof (IH err eq_refl) as (? & IN_RULES & NULLABLE & ERR); ss!.
Qed.

Definition raws : list Rule.t :=
  L.mapi_from 1 (fun index => fun '(token, regex) => {| index := index; token := token; regex := regex |}) Token.rules.

Definition compileds : BuildErrorM@{Set} (list Rule.t) :=
  compileRules raws.

End Rule.

End MkLGS.
