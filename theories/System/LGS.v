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

Abbreviation all_bools_complete := Bool_FinEnum.all_complete.

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

Lemma all_complete
  : forall x : Ascii_FinEnum.t, L.In x Ascii_FinEnum.all.
Proof.
  unfold all; intros [b0 b1 b2 b3 b4 b5 b6 b7].
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
  assert (EQ : L.nodup (@eq_dec@{Set} ascii ascii_hasEqDec) all = all) by reflexivity.
  rewrite <- EQ. eapply L.NoDup_nodup.
Qed.

End Ascii_FinEnum.

Abbreviation all_asciis := Ascii_FinEnum.all.

Abbreviation all_asciis_complete := Ascii_FinEnum.all_complete.

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

Fact mem_spec (A : Set) `(A_hasEqDec : hasEqDec@{Set} A) (x : A) (xs : list A) (b : bool)
  : mem@{Set} x xs = b <-> (if b then x ∈ xs else ~ x ∈ xs).
Proof.
  destruct b; [eapply mem_true_iff | eapply mem_false_iff].
Qed.

Fact eqb_iff (A : Set) `(A_hasEqDec : hasEqDec@{Set} A) (x : A) (y : A) (b : bool)
  : eqb@{Set} x y = b <-> (if b then x = y else x ≠ y).
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
  eapply L.forallb_forall.
Qed.

#[local] Hint Rewrite mem_spec : simplication_hints.
#[local] Hint Rewrite eqb_iff : simplication_hints.
#[local] Hint Rewrite existsb_iff : simplication_hints.
#[local] Hint Rewrite forallb_iff : simplication_hints.

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
  exists (firstn n s), (skipn n s).
  rewrite firstn_skipn. split; [reflexivity | ].
  rewrite length_firstn. lia.
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
  : s = [] \/ (exists c, exists s', s = c :: s').
Proof.
  destruct s as [ | c s']; [left; reflexivity | right; exists c, s'; reflexivity].
Qed.

Theorem nonempty_prefix_rest_shorter (consumed : Input.t) (rest : Input.t)
  (NONEMPTY : ~ consumed = [])
  : length rest < length (consumed ++ rest).
Proof.
  destruct consumed as [ | c consumed]; [contradiction | simpl; rewrite length_app; simpl; lia].
Qed.

End Input.

Lemma Input_to_of_string (s : string)
  : Input.to_string (Input.of_string s) = s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Lemma Input_of_to_string (s : Input.t)
  : Input.of_string (Input.to_string s) = s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Lemma Input_length_of_string (s : string)
  : length (Input.of_string s) = String.length s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Lemma Input_to_string_app (s1 : Input.t) (s2 : Input.t)
  : Input.to_string (s1 ++ s2) = String.append (Input.to_string s1) (Input.to_string s2).
Proof.
  induction s1 as [ | c s1 IH]; simpl; congruence.
Qed.

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
      change (@nil ascii) with (@nil ascii ++ @nil ascii).
      eauto with *.
    + econs.
  - revert e.
    enough (CLAIM : forall s, forall e, s =~= e -> s = [] -> nullable e = true).
    { i. eapply CLAIM; eauto. }
    intros s e H_IN. induction H_IN; simpl; i; subst; try congruence; eauto.
    + rewrite orb_true_iff. left. eauto.
    + rewrite orb_true_iff. right. eauto.
    + pose proof (app_eq_nil _ _ H) as [EQ1 EQ2]. subst s1 s2. ss!.
Qed.

Theorem nullable_true_iff (e : regex ascii)
  : nullable e = true <-> [] \in eval_regex e.
Proof.
  rewrite eval_regex_good. eapply nullable_similar_spec.
Qed.

Theorem nullable_false_iff (e : regex ascii)
  : nullable e = false <-> (~ [] \in eval_regex e).
Proof.
  destruct (nullable e) eqn: EQ; split; intros H.
  - congruence.
  - contradiction H. rewrite <- nullable_true_iff. exact EQ.
  - intros IN. rewrite <- nullable_true_iff in IN. congruence.
  - reflexivity.
Qed.

Corollary nullable_refines (e : regex ascii)
  : nullable e ⊑ ([] \in eval_regex e).
Proof.
  destruct (nullable e) as [ | ] eqn: H_OBS.
  - now rewrite nullable_true_iff in H_OBS.
  - now rewrite nullable_false_iff in H_OBS.
Qed.

Lemma union_inv (s : Input.t) (e1 : regex ascii) (e2 : regex ascii)
  (IN : s \in eval_regex (Re.Union e1 e2))
  : s \in eval_regex e1 \/ s \in eval_regex e2.
Proof.
  done!.
Qed.

Lemma append_inv (s : Input.t) (e1 : regex ascii) (e2 : regex ascii)
  (IN : s \in eval_regex (Re.Append e1 e2))
  : exists s1, exists s2, s = s1 ++ s2 /\ s1 \in eval_regex e1 /\ s2 \in eval_regex e2.
Proof.
  done!.
Qed.

Lemma star_nil (e : regex ascii)
  : [] \in eval_regex (Re.Star e).
Proof.
  econs 1.
Qed.

Theorem star_inv (s : Input.t) (e : regex ascii)
  (IN : s \in eval_regex (Re.Star e))
  : s = [] \/ (exists s1, exists s2, s = s1 ++ s2 /\ s1 \in eval_regex e /\ s2 \in eval_regex (Re.Star e)).
Proof.
  simpl in IN. inv IN; [left | right]; ss!.
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

Definition compileRule (rule : Rule.t) : BuildErrorM Rule.t :=
  if nullable rule.(Rule.regex) then
    inl (BuildError.NullableTokenRule rule.(Rule.index))
  else
    pure rule.

Theorem compileRule_spec (rule : Rule.t) (rule' : Rule.t)
  (COMPILE : compileRule rule = inr rule')
  : forall s, s \in eval_regex rule.(Rule.regex) <-> s \in eval_regex rule'.(Rule.regex).
Proof.
  intros s; split; intros ACCEPTS; unfold compileRule in COMPILE; now destruct (nullable rule.(Rule.regex)) eqn: NULLABLE; inv COMPILE.
Qed.

Lemma compileRule_not_match_empty (rule : Rule.t) (rule' : Rule.t)
  (COMPILE : compileRule rule = inr rule')
  : ~ ([] \in eval_regex rule'.(Rule.regex)).
Proof.
  unfold compileRule in COMPILE; destruct (nullable rule.(Rule.regex)) eqn: NULLABLE; inv COMPILE; now rewrite <- nullable_false_iff.
Qed.

Fixpoint compileRules (rules : list Rule.t) : BuildErrorM (list Rule.t) :=
  match rules with
  | [] => pure (@nil Rule.t)
  | rule :: rules => liftM2 (@cons Rule.t) (compileRule rule) (compileRules rules)
  end.

Definition raws : list Rule.t :=
  L.mapi_from 1 (fun index => fun '(token, regex) => Rule.mk index token regex) Token.rules.

Definition compileds : BuildErrorM (list Rule.t) :=
  compileRules raws.

Definition accepts (rule : Rule.t) (s : Input.t) : Prop :=
  s \in eval_regex rule.(Rule.regex).

Definition first_rule_for (rules : list Rule.t) (s : Input.t) (rule : Rule.t) : Prop :=
  exists prefix, exists suffix, rules = prefix ++ rule :: suffix /\ accepts rule s /\ (forall prior, prior ∈ prefix -> ~ accepts prior s).

Definition priority (rules : list Rule.t) (rule1 : Rule.t) (rule2 : Rule.t) : Prop :=
  exists between, exists suffix, rules = rule1 :: between ++ rule2 :: suffix.

Lemma compileRule_success_identity (rule : Rule.t) (rule' : Rule.t)
  (COMPILE : compileRule rule = inr rule')
  : rule = rule'.
Proof.
  unfold compileRule in *. now destruct (nullable rule.(Rule.regex)); inv COMPILE.
Qed.

Lemma compileRules_preserve_order (rules : list Rule.t) (rules' : list Rule.t)
  (COMPILE : compileRules rules = inr rules')
  : rules = rules'.
Proof.
  revert rules' COMPILE; induction rules as [ | rule rules IH]; intros compiled_rules COMPILE; simpl in COMPILE.
  - now inv COMPILE.
  - destruct (compileRule rule) as [err | rules'] eqn: COMPILE_RULE; cbn in COMPILE; [discriminate | ].
    destruct (compileRules rules) as [err | compiled_rules']; cbn in COMPILE; [discriminate | ].
    inv COMPILE. f_equal.
    + now eapply compileRule_success_identity.
    + now eapply IH.
Qed.

Theorem compileRules_sound (rules : list Rule.t) (rules' : list Rule.t) (rule : Rule.t)
  (COMPILE : compileRules rules = inr rules')
  (IN : rule ∈ rules')
  : rule ∈ rules /\ (~ accepts rule []).
Proof.
  split.
  - revert rule rules' COMPILE IN; induction rules as [ | rule rules IH]; ii; simpl in *.
    + now inv COMPILE.
    + destruct (compileRule rule) as [err | rule'] eqn: H_OBS1; simpl in *; inv COMPILE.
      destruct (compileRules rules) as [err | rules0] eqn: H_OBS2; simpl in *; inv H0.
      destruct IN as [EQ | IN]; [left | right]; eauto.
      eapply compileRule_success_identity. congruence.
  - revert rule rules' COMPILE IN; induction rules as [ | rule rules IH]; ii; simpl in *.
    + now inv COMPILE.
    + destruct (compileRule rule) as [err | rule'] eqn: H_OBS1; simpl in *; inv COMPILE.
      destruct (compileRules rules) as [err | rules0] eqn: H_OBS2; simpl in *; inv H1.
      destruct IN as [EQ | IN].
      * eapply compileRule_not_match_empty with (rule := rule) (rule' := rule0); eauto. congruence.
      * eapply IH with (rule := rule0) (rules' := rules0); eauto.
Qed.

Theorem compileRules_complete (rules : list Rule.t)
  (NONNULL : forall rule, rule ∈ rules -> nullable rule.(Rule.regex) = false)
  : compileRules rules = inr rules.
Proof.
  induction rules as [ | rule rules IH]; simpl; eauto.
  unfold compileRule at 1. rewrite NONNULL by now left.
  cbn. rewrite IH; ss!.
Qed.

Theorem compileRules_failure_nullable (rules : list Rule.t) (err : BuildError.t)
  (COMPILE : compileRules rules = inl err)
  : exists rule, rule ∈ rules /\ nullable rule.(Rule.regex) = true /\ err = BuildError.NullableTokenRule rule.(Rule.index).
Proof.
  revert err COMPILE; induction rules as [ | rule rules IH]; intros err COMPILE; simpl in COMPILE; try congruence.
  destruct (compileRule rule) as [err' | rule'] eqn: COMPILE_RULE; cbn in COMPILE.
  - inv COMPILE. unfold compileRule in COMPILE_RULE. destruct (nullable rule.(Rule.regex)) eqn: NULLABLE; inv COMPILE_RULE. exists rule; ss!.
  - destruct (compileRules rules) as [err' | rules'] eqn: COMPILE_RULES; cbn in COMPILE; try congruence.
    inv COMPILE. pose proof (IH err eq_refl) as (bad_rule & IN_RULES & NULLABLE & ERR). exists bad_rule; ss!.
Qed.

Theorem compileRules_has_nullable_failure (rules : list Rule.t)
  (NULLABLE : exists rule, rule ∈ rules /\ nullable rule.(Rule.regex) = true)
  : exists idx, compileRules rules = inl (BuildError.NullableTokenRule idx).
Proof.
  induction rules as [ | rule rules IH].
  - destruct NULLABLE as (bad_rule & [] & _).
  - destruct NULLABLE as (bad_rule & [EQ | IN] & NULLABLE).
    + subst bad_rule. simpl. unfold compileRule at 1. rewrite NULLABLE. ss!.
    + simpl. destruct (compileRule rule) as [[idx] | compiled_rule] eqn: COMPILE_RULE; simpl; eauto.
      pose proof (IH (@ex_intro _ _ bad_rule (conj IN NULLABLE))) as (idx & FAILURE); simpl.
      now rewrite FAILURE; exists idx.
Qed.

End Rule.

Module TaggedENFA.

#[projections(primitive)]
Record t : Type :=
  mk
  { state : Set
  ; state_hasEqDec : hasEqDec@{Set} state
  ; states : list state
  ; start_state : state
  ; accept_states : list (state * Token.t)
  ; eps_step (q : state) : list state
  ; char_step (q : state) (c : ascii) : list state
  } as M.

#[global] Existing Instance state_hasEqDec.

Variant okay (M : TaggedENFA.t) : Prop :=
  | okay_intro
    (start_okay : M.(TaggedENFA.start_state) ∈ M.(TaggedENFA.states))
    (accept_states_okay : forall q, forall tag, (q, tag) ∈ M.(TaggedENFA.accept_states) -> q ∈ M.(TaggedENFA.states))
    (eps_step_okay : forall q, forall q', q ∈ M.(TaggedENFA.states) -> q' ∈ M.(TaggedENFA.eps_step) q -> q' ∈ M.(TaggedENFA.states))
    (char_step_okay : forall q, forall q', forall c, q ∈ M.(TaggedENFA.states) -> q' ∈ M.(TaggedENFA.char_step) q c -> q' ∈ M.(TaggedENFA.states)).

Section DELTA_STAR.

Context {Q : Type}.

Variable eps_step : Q -> list Q.

Inductive eclosure (q : Q) : ensemble Q :=
  | eclosure_refl
    : q \in eclosure q
  | eclosure_step q1 q2
    (STEP : q1 ∈ eps_step q)
    (REST : q2 \in eclosure q1)
    : q2 \in eclosure q.

#[local] Hint Constructors eclosure : core.

Lemma eclosure_trans (q1 : Q) (q2 : Q) (q3 : Q)
  (H1_eclosure : q2 \in eclosure q1)
  (H2_eclosure : q3 \in eclosure q2)
  : q3 \in eclosure q1.
Proof.
  induction H1_eclosure as [q | q q1' q2' STEP REST IH]; simpl; eauto with *.
Qed.

Variable char_step : Q -> ascii -> list Q.

Inductive delta_star (q : Q) : Input.t -> ensemble Q :=
  | delta_star_nil
    : q \in delta_star q []
  | delta_star_eps q1 q2 s
    (STEP : q1 ∈ eps_step q)
    (REST : q2 \in delta_star q1 s)
    : q2 \in delta_star q s
  | delta_star_char q1 q2 c s
    (STEP : q1 ∈ char_step q c)
    (REST : q2 \in delta_star q1 s)
    : q2 \in delta_star q (c :: s).

#[local] Hint Constructors delta_star : core.

Lemma delta_star_app (q1 : Q) (q2 : Q) (q3 : Q) (s1 : Input.t) (s2 : Input.t)
  (H1_delta_star : q2 \in delta_star q1 s1)
  (H2_delta_star : q3 \in delta_star q2 s2)
  : q3 \in delta_star q1 (s1 ++ s2).
Proof.
  induction H1_delta_star as [q | q q1' q2' s STEP REST IH | q q1' q2' c s STEP REST IH]; simpl; eauto with *.
Qed.

Lemma delta_star_iff_eclosure (q : Q) (q' : Q)
  : q' \in delta_star q [] <-> q' \in eclosure q.
Proof.
  split; [intros H_delta_star | intros H_eclosure].
  - remember (@nil ascii) as s eqn: EQ; induction H_delta_star as [q | q q1' q2' s STEP REST IH | q q1' q2' c s STEP REST IH]; inv EQ; simpl; eauto with *.
  - induction H_eclosure as [q | q q1' q2' STEP REST IH]; simpl; eauto with *.
Qed.

Lemma delta_star_elim (q1 : Q) (q3 : Q) (s : Input.t)
  (H_delta_star : q3 \in delta_star q1 s)
  : ⟪ DELTA_STAR_NIL : s = [] /\ q3 = q1 ⟫ \/ ⟪ DELTA_STAR_EPS : exists q2, q2 ∈ eps_step q1 /\ q3 \in delta_star q2 s ⟫ \/ ⟪ DELTA_STAR_CHAR : exists c, exists s', exists q2, s = c :: s' /\ q2 ∈ char_step q1 c /\ q3 \in delta_star q2 s' ⟫.
Proof.
  unnw; destruct H_delta_star as [ | q1' q2' s' STEP REST | q1' q2' c s' STEP REST]; [left | right; left | right; right]; done!.
Qed.

Lemma delta_star_stuck (q1 : Q) (q2 : Q) (s : Input.t)
  (NO_EPS : forall q, ~ (q ∈ eps_step q1))
  (NO_CHAR : forall c, forall q, ~ (q ∈ char_step q1 c))
  (H_delta_star : q2 \in delta_star q1 s)
  : s = [] /\ q2 = q1.
Proof.
  inv H_delta_star; ss!.
Qed.

End DELTA_STAR.

Section BASICS.

Variable M : TaggedENFA.t.

#[local] Abbreviation Q := M.(TaggedENFA.state).
#[local] Abbreviation M_delta_star := (delta_star M.(TaggedENFA.eps_step) M.(TaggedENFA.char_step)).
#[local] Abbreviation M_eclosure := (eclosure M.(TaggedENFA.eps_step)).

Lemma eclosure_okay (q1 : Q) (q2 : Q)
  (OKAY : TaggedENFA.okay M)
  (IN : q1 ∈ M.(TaggedENFA.states))
  (H_eclosure : q2 \in M_eclosure q1)
  : q2 ∈ M.(TaggedENFA.states).
Proof.
  destruct OKAY as [_ _ ? _]; induction H_eclosure as [q | q q1' q2' STEP REST IH]; simpl; eauto with *.
Qed.

Lemma delta_star_okay (q1 : Q) (q2 : Q) (s : Input.t)
  (OKAY : TaggedENFA.okay M)
  (IN : q1 ∈ M.(TaggedENFA.states))
  (H_delta_star : q2 \in M_delta_star q1 s)
  : q2 ∈ M.(TaggedENFA.states).
Proof.
  destruct OKAY as [_ _ ? ?]; induction H_delta_star as [q | q q1' q2' s STEP REST IH | q q1' q2' c s STEP REST IH]; simpl; eauto with *.
Qed.

Definition accepts (s : Input.t) (tag : Token.t) : Prop :=
  exists qf, qf \in M_delta_star M.(TaggedENFA.start_state) s /\ (qf, tag) ∈ M.(TaggedENFA.accept_states).

Definition accepted_tags (s : Input.t) : ensemble Token.t :=
  fun tag => accepts s tag.

End BASICS.

Section Thompson's_construction.

#[projections(primitive)]
Record char_edge : Set :=
  mkCharEdge
  { char_edge_src : nat
  ; char_edge_label : ascii
  ; char_edge_dst : nat
  } as char_edge.

#[projections(primitive)]
Record fragment : Set :=
  mkFragment
  { frag_start : nat
  ; frag_accept : nat
  ; frag_eps_edges : list (nat * nat)
  ; frag_char_edges : list char_edge
  } as frag.

Fixpoint regex2fragment (e : regex ascii) (qi : nat) {struct e} : nat * fragment :=
  match e with
  | Re.Null =>
    let qf := qi + 1 in
    (qf, mkFragment qi qf [] [])
  | Re.Empty =>
    let qf := qi + 1 in
    (qf, mkFragment qi qf [(qi, qf)] [])
  | Re.Char c =>
    let qf := qi + 1 in
    (qf, mkFragment qi qf [] [mkCharEdge qi c qf])
  | Re.Union e1 e2 =>
    let qi1 := qi + 1 in
    let '(qf1, frag1) := regex2fragment e1 qi1 in
    let qi2 := qf1 + 1 in
    let '(qf2, frag2) := regex2fragment e2 qi2 in
    let qf := qf2 + 1 in
    (qf, mkFragment qi qf ((qi, qi1) :: (qi, qi2) :: (qf1, qf) :: (qf2, qf) :: frag1.(frag_eps_edges) ++ frag2.(frag_eps_edges)) (frag1.(frag_char_edges) ++ frag2.(frag_char_edges)))
  | Re.Append e1 e2 =>
    let qi1 := qi + 1 in
    let '(qf1, frag1) := regex2fragment e1 qi1 in
    let qi2 := qf1 + 1 in
    let '(qf2, frag2) := regex2fragment e2 qi2 in
    let qf := qf2 + 1 in
    (qf, mkFragment qi qf ((qi, qi1) :: (qf1, qi2) :: (qf2, qf) :: frag1.(frag_eps_edges) ++ frag2.(frag_eps_edges)) (frag1.(frag_char_edges) ++ frag2.(frag_char_edges)))
  | Re.Star e1 =>
    let qi1 := qi + 1 in
    let '(qf1, frag1) := regex2fragment e1 qi1 in
    let qf := qf1 + 1 in
    (qf, mkFragment qi qf ((qi, qi1) :: (qf1, qi1) :: (qi1, qf) :: frag1.(frag_eps_edges)) frag1.(frag_char_edges))
  end.

Fixpoint rules2fragments (qi : nat) (rules : list Rule.t) {struct rules} : nat * list (Rule.t * fragment) :=
  match rules with
  | [] => (qi, [])
  | rule :: rules' =>
    let '(qf, frag) := regex2fragment rule.(Rule.regex) qi in
    let '(qmax, frags) := rules2fragments (qf + 1) rules' in
    (qmax, (rule, frag) :: frags)
  end.

Fixpoint eps_step_from_edges (q : nat) (edges : list (nat * nat)) {struct edges} : list nat :=
  match edges with
  | [] => []
  | (src, dst) :: edges' =>
    if eq_dec q src then
      dst :: eps_step_from_edges q edges'
    else
      eps_step_from_edges q edges'
  end.

Fixpoint char_step_from_edges (q : nat) (c : ascii) (edges : list char_edge) {struct edges} : list nat :=
  match edges with
  | [] => []
  | edge :: edges' =>
    if eq_dec q edge.(char_edge_src) then
      if eq_dec c edge.(char_edge_label) then
        edge.(char_edge_dst) :: char_step_from_edges q c edges'
      else
        char_step_from_edges q c edges'
    else
      char_step_from_edges q c edges'
  end.

Fixpoint fragment_eps_edges (frags : list (Rule.t * fragment)) {struct frags} : list (nat * nat) :=
  match frags with
  | [] => []
  | (_, frag) :: frags' => (0, frag.(frag_start)) :: frag.(frag_eps_edges) ++ fragment_eps_edges frags'
  end.

Fixpoint fragment_char_edges (frags : list (Rule.t * fragment)) {struct frags} : list char_edge :=
  match frags with
  | [] => []
  | (_, frag) :: frags' => frag.(frag_char_edges) ++ fragment_char_edges frags'
  end.

Definition fragment_accept_states (frags : list (Rule.t * fragment)) : list (nat * Token.t) :=
  map (fun '(rule, frag) => (frag.(frag_accept), rule.(Rule.token))) frags.

Definition fragments2TaggedENFA (qmax : nat) (frags : list (Rule.t * fragment)) : TaggedENFA.t :=
  let eps_edges := fragment_eps_edges frags in
  let char_edges := fragment_char_edges frags in
  {|
    state := nat;
    state_hasEqDec := nat_hasEqDec;
    states := seq 0 qmax;
    start_state := 0;
    accept_states := fragment_accept_states frags;
    eps_step := fun q => eps_step_from_edges q eps_edges;
    char_step := fun q => fun c => char_step_from_edges q c char_edges;
  |}.

Definition mkUnitedTaggedENFA (rules : list Rule.t) : TaggedENFA.t :=
  let '(qmax, frags) := rules2fragments 1 rules in
  fragments2TaggedENFA qmax frags.

Lemma eps_step_from_edges_complete (q : nat) (q' : nat) (edges : list (nat * nat))
  (IN : (q, q') ∈ edges)
  : q' ∈ eps_step_from_edges q edges.
Proof.
  induction edges as [ | [src dst] edges IH]; simpl in IN |- *; des; des_ifs; ss!.
Qed.

Lemma eps_step_from_edges_sound (q : nat) (q' : nat) (edges : list (nat * nat))
  (IN : q' ∈ eps_step_from_edges q edges)
  : (q, q') ∈ edges.
Proof.
  induction edges as [ | [src dst] edges IH]; simpl in IN |- *; des; des_ifs; ss!.
Qed.

Lemma char_step_from_edges_complete (edge : char_edge) (edges : list char_edge)
  (IN : edge ∈ edges)
  : edge.(char_edge_dst) ∈ char_step_from_edges edge.(char_edge_src) edge.(char_edge_label) edges.
Proof.
  induction edges as [ | edge' edges IH]; simpl in IN |- *; des; des_ifs; ss!.
Qed.

Lemma char_step_from_edges_sound (q : nat) (q' : nat) (c : ascii) (edges : list char_edge)
  (IN : q' ∈ char_step_from_edges q c edges)
  : exists edge, edge ∈ edges /\ edge.(char_edge_src) = q /\ edge.(char_edge_label) = c /\ edge.(char_edge_dst) = q'.
Proof.
  induction edges as [ | edge edges IH]; simpl in IN |- *; try tauto.
  destruct (eq_dec q edge.(char_edge_src)) as [SRC_EQ | SRC_NE].
  - destruct (eq_dec c edge.(char_edge_label)) as [LABEL_EQ | LABEL_NE]; simpl in IN.
    + destruct IN as [DST_EQ | IN].
      * exists edge; ss!.
      * pose proof (IH IN) as (edge' & IN_EDGE & SRC' & LABEL' & DST'). exists edge'; ss!.
    + pose proof (IH IN) as (edge' & IN_EDGE & SRC' & LABEL' & DST'). exists edge'; ss!.
  - pose proof (IH IN) as (edge' & IN_EDGE & SRC' & LABEL' & DST'). exists edge'; ss!.
Qed.

Lemma fragment_eps_edges_start_complete (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment)
  (IN : (rule, frag) ∈ frags)
  : (0, frag.(frag_start)) ∈ fragment_eps_edges frags.
Proof.
  induction frags as [ | [rule' frag'] frags IH]; simpl in IN |- *; ss!.
Qed.

Lemma fragment_eps_edges_complete (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment) (q : nat) (q' : nat)
  (IN_FRAG : (rule, frag) ∈ frags)
  (IN_EDGE : (q, q') ∈ frag.(frag_eps_edges))
  : (q, q') ∈ fragment_eps_edges frags.
Proof.
  induction frags as [ | [rule' frag'] frags IH]; simpl in IN_FRAG |- *; des; ss!.
Qed.

Lemma fragment_char_edges_complete (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment) (edge : char_edge)
  (IN_FRAG : (rule, frag) ∈ frags)
  (IN_EDGE : edge ∈ frag.(frag_char_edges))
  : edge ∈ fragment_char_edges frags.
Proof.
  induction frags as [ | [rule' frag'] frags IH]; simpl in IN_FRAG |- *; des; ss!.
Qed.

Lemma fragment_accept_states_complete (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment)
  (IN_FRAG : (rule, frag) ∈ frags)
  : (frag.(frag_accept), rule.(Rule.token)) ∈ fragment_accept_states frags.
Proof.
  unfold fragment_accept_states. ss!.
Qed.

Lemma fragment_accept_states_sound (frags : list (Rule.t * fragment)) q tag
  (IN : (q, tag) ∈ fragment_accept_states frags)
  : exists rule, exists frag, (rule, frag) ∈ frags /\ q = frag.(frag_accept) /\ tag = rule.(Rule.token).
Proof.
  unfold fragment_accept_states in IN. rewrite L.in_map_iff in IN.
  destruct IN as ([rule frag] & EQ & IN_FRAG). inv EQ. now exists rule, frag.
Qed.

Variant TaggedENFA_COMPILED (M : TaggedENFA.t) (rules : list Rule.t) (qmax : nat) (frags : list (Rule.t * fragment)) : Prop :=
  | TaggedENFA_COMPILED_intro 
    (COMPILED_RULES : Rule.compileds = inr rules)
    (COMPILED_ENFA : M = mkUnitedTaggedENFA rules)
    (COMPILED_FRAGS : rules2fragments 1 rules = (qmax, frags)).

Variant TaggedENFA_FRAGMENTS (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment) : Prop :=
  | TaggedENFA_FRAGMENTS_intro
    (start_in : frag.(frag_start) ∈ eps_step_from_edges 0 (fragment_eps_edges frags))
    (accept_in : (frag.(frag_accept), rule.(Rule.token)) ∈ fragment_accept_states frags)
    (eps_in : forall q, forall q', (q, q') ∈ frag.(frag_eps_edges) -> q' ∈ eps_step_from_edges q (fragment_eps_edges frags))
    (char_in : forall edge, edge ∈ frag.(frag_char_edges) -> edge.(char_edge_dst) ∈ char_step_from_edges edge.(char_edge_src) edge.(char_edge_label) (fragment_char_edges frags)).

Theorem mkUnitedTaggedENFA_spec (M : TaggedENFA.t)
  (COMPILE : fmap mkUnitedTaggedENFA Rule.compileds = inr M)
  : exists rules, exists qmax, exists frags, TaggedENFA_COMPILED M rules qmax frags /\ (forall rule, forall frag, (rule, frag) ∈ frags -> TaggedENFA_FRAGMENTS frags rule frag).
Proof.
  unfold fmap, mkFunctorFromMonad in COMPILE. simpl in COMPILE.
  destruct Rule.compileds as [err | rules] eqn: COMPILED; inv COMPILE.
  destruct (rules2fragments 1 rules) as [qmax frags] eqn: FRAGS.
  exists rules, qmax, frags. split.
  - split; eauto.
  - ii; split; i.
    + eapply eps_step_from_edges_complete. eapply fragment_eps_edges_start_complete; eauto.
    + eapply fragment_accept_states_complete; eauto.
    + eapply eps_step_from_edges_complete. eapply fragment_eps_edges_complete; eauto.
    + eapply char_step_from_edges_complete. eapply fragment_char_edges_complete; eauto.
Qed.

Definition fragments_delta_star (frags : list (Rule.t * fragment)) : nat -> Input.t -> ensemble nat :=
  delta_star (fun q => eps_step_from_edges q (fragment_eps_edges frags)) (fun q => fun c => char_step_from_edges q c (fragment_char_edges frags)).

Definition fragment_delta_star (frag : fragment) : nat -> Input.t -> ensemble nat :=
  delta_star (fun q => eps_step_from_edges q frag.(frag_eps_edges)) (fun q => fun c => char_step_from_edges q c frag.(frag_char_edges)).

Lemma mkUnitedTaggedENFA_unfold_fragments rules qmax frags
  (FRAGS : rules2fragments 1 rules = (qmax, frags))
  : mkUnitedTaggedENFA rules = fragments2TaggedENFA qmax frags.
Proof.
  unfold mkUnitedTaggedENFA, fragments2TaggedENFA. rewrite FRAGS. reflexivity.
Qed.

Lemma TaggedENFA_COMPILED_as_fragments M rules qmax frags
  (COMPILED : TaggedENFA_COMPILED M rules qmax frags)
  : M = fragments2TaggedENFA qmax frags.
Proof.
  inv COMPILED. eapply mkUnitedTaggedENFA_unfold_fragments. exact COMPILED_FRAGS.
Qed.

Lemma TaggedENFA_FRAGMENTS_delta_star_step frags rule frag
  (FRAGMENTS : TaggedENFA_FRAGMENTS frags rule frag)
  : ⟪ EPS : forall q, forall q', (q, q') ∈ frag.(frag_eps_edges) -> q' \in fragments_delta_star frags q [] ⟫ /\ ⟪ CHAR : forall edge, edge ∈ frag.(frag_char_edges) -> edge.(char_edge_dst) \in fragments_delta_star frags edge.(char_edge_src) [edge.(char_edge_label)] ⟫.
Proof.
  destruct FRAGMENTS as [_ _ EPS CHAR]. split.
  - intros q q' IN_EDGE. eapply delta_star_eps with (q1 := q').
    + exact (EPS q q' IN_EDGE).
    + econs.
  - intros edge IN_EDGE. eapply delta_star_char with (q1 := edge.(char_edge_dst)).
    + exact (CHAR edge IN_EDGE).
    + econs.
Qed.

Lemma regex2fragment_empty_delta_star frags rule qi qf frag
  (REGEX2FRAGMENT : regex2fragment Re.Empty qi = (qf, frag))
  (FRAGMENTS : TaggedENFA_FRAGMENTS frags rule frag)
  : frag.(frag_accept) \in fragments_delta_star frags frag.(frag_start) [].
Proof.
  pose proof (TaggedENFA_FRAGMENTS_delta_star_step frags rule frag FRAGMENTS) as [EPS _].
  simpl in REGEX2FRAGMENT. inv REGEX2FRAGMENT. eapply EPS. simpl. left. reflexivity.
Qed.

Lemma regex2fragment_start_accept e qi qf frag
  (REGEX2FRAGMENT : regex2fragment e qi = (qf, frag))
  : frag.(frag_start) = qi /\ frag.(frag_accept) = qf.
Proof.
  revert qi qf frag REGEX2FRAGMENT.
  induction e as [ | | c | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH]; intros qi qf frag REGEX2FRAGMENT; simpl in REGEX2FRAGMENT.
  - inv REGEX2FRAGMENT. eauto.
  - inv REGEX2FRAGMENT. eauto.
  - inv REGEX2FRAGMENT. eauto.
  - destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1].
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2].
    inv REGEX2FRAGMENT. eauto.
  - destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1].
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2].
    inv REGEX2FRAGMENT. eauto.
  - destruct (regex2fragment e (qi + 1)) as [qf1 frag1].
    inv REGEX2FRAGMENT. eauto.
Qed.

Lemma regex2fragment_same_fragment e qi1 qf1 qi2 qf2 frag
  (REGEX1 : regex2fragment e qi1 = (qf1, frag))
  (REGEX2 : regex2fragment e qi2 = (qf2, frag))
  : qi1 = qi2 /\ qf1 = qf2.
Proof.
  pose proof (regex2fragment_start_accept _ _ _ _ REGEX1) as [START1 ACCEPT1].
  pose proof (regex2fragment_start_accept _ _ _ _ REGEX2) as [START2 ACCEPT2].
  split; congruence.
Qed.

Definition eps_edge_in_range (lo : nat) (hi : nat) (edge : nat * nat) : Prop :=
  lo <= fst edge <= hi /\ lo <= snd edge <= hi.

Definition char_edge_in_range (lo : nat) (hi : nat) (edge : char_edge) : Prop :=
  lo <= edge.(char_edge_src) <= hi /\ lo <= edge.(char_edge_dst) <= hi.

Variant FRAGMENT_BOUNDS (lo : nat) (hi : nat) (frag : fragment) : Prop :=
  | FRAGMENT_BOUNDS_intro
    (BOUNDS_START : frag.(frag_start) = lo)
    (BOUNDS_ACCEPT : frag.(frag_accept) = hi)
    (BOUNDS_LT : lo < hi)
    (BOUNDS_EPS : forall edge, edge ∈ frag.(frag_eps_edges) -> eps_edge_in_range lo hi edge)
    (BOUNDS_CHAR : forall edge, edge ∈ frag.(frag_char_edges) -> char_edge_in_range lo hi edge).

Lemma regex2fragment_bounds e qi qf frag
  (REGEX2FRAGMENT : regex2fragment e qi = (qf, frag))
  : FRAGMENT_BOUNDS qi qf frag.
Proof.
  revert qi qf frag REGEX2FRAGMENT.
  induction e as [ | | c | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH]; intros qi qf frag REGEX2FRAGMENT; simpl in REGEX2FRAGMENT.
  - inv REGEX2FRAGMENT. econs; simpl; try lia; tauto.
  - inv REGEX2FRAGMENT. econs; simpl; try lia.
    intros [q q'] [EQ | IN]; s!; des; subst.
    + unfold eps_edge_in_range. simpl. lia.
    + contradiction.
  - inv REGEX2FRAGMENT. econs; simpl; try lia.
    intros edge [EQ | IN]; [subst edge; unfold char_edge_in_range; simpl; lia | contradiction].
  - destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    pose proof (IH1 _ _ _ REGEX1) as [START1 ACCEPT1 LT1 EPS1 CHAR1].
    pose proof (IH2 _ _ _ REGEX2) as [START2 ACCEPT2 LT2 EPS2 CHAR2].
    inv REGEX2FRAGMENT. econs; simpl; try lia.
    + intros [q q'] IN_EDGE. simpl in IN_EDGE.
      destruct IN_EDGE as [EQ | [EQ | [EQ | [EQ | IN_EDGE]]]]; s!; des; subst.
      * unfold eps_edge_in_range. simpl. lia.
      * unfold eps_edge_in_range. simpl. lia.
      * unfold eps_edge_in_range. simpl. lia.
      * unfold eps_edge_in_range. simpl. lia.
      * pose proof (EPS1 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. lia.
      * pose proof (EPS2 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. lia.
    + intros edge IN_EDGE. simpl in IN_EDGE. rewrite in_app_iff in IN_EDGE.
      destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (CHAR1 _ IN_EDGE). unfold char_edge_in_range in *. lia.
      * pose proof (CHAR2 _ IN_EDGE). unfold char_edge_in_range in *. lia.
  - destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    pose proof (IH1 _ _ _ REGEX1) as [START1 ACCEPT1 LT1 EPS1 CHAR1].
    pose proof (IH2 _ _ _ REGEX2) as [START2 ACCEPT2 LT2 EPS2 CHAR2].
    inv REGEX2FRAGMENT. econs; simpl; try lia.
    + intros [q q'] IN_EDGE. simpl in IN_EDGE.
      destruct IN_EDGE as [EQ | [EQ | [EQ | IN_EDGE]]]; s!; des; subst.
      * unfold eps_edge_in_range. simpl. lia.
      * unfold eps_edge_in_range. simpl. lia.
      * unfold eps_edge_in_range. simpl. lia.
      * pose proof (EPS1 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. lia.
      * pose proof (EPS2 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. lia.
    + intros edge IN_EDGE. simpl in IN_EDGE. s!; des.
      * pose proof (CHAR1 _ IN_EDGE). unfold char_edge_in_range in *. lia.
      * pose proof (CHAR2 _ IN_EDGE). unfold char_edge_in_range in *. lia.
  - destruct (regex2fragment e (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    pose proof (IH _ _ _ REGEX1) as [START1 ACCEPT1 LT1 EPS1 CHAR1].
    inv REGEX2FRAGMENT. econs; simpl; try lia.
    + intros [q q'] IN_EDGE. simpl in IN_EDGE.
      destruct IN_EDGE as [EQ | [EQ | [EQ | IN_EDGE]]]; s!; des; subst.
      * unfold eps_edge_in_range. simpl. lia.
      * unfold eps_edge_in_range. simpl. lia.
      * unfold eps_edge_in_range. simpl. lia.
      * pose proof (EPS1 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. lia.
    + intros edge IN_EDGE.
      pose proof (CHAR1 _ IN_EDGE). unfold char_edge_in_range in *. lia.
Qed.

Lemma regex2fragment_edge_src_lt e qi qf frag
  (REGEX2FRAGMENT : regex2fragment e qi = (qf, frag))
  : (forall q, forall q', (q, q') ∈ frag.(frag_eps_edges) -> q < qf) /\ (forall edge, edge ∈ frag.(frag_char_edges) -> edge.(char_edge_src) < qf).
Proof.
  revert qi qf frag REGEX2FRAGMENT.
  induction e as [ | | c | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH]; ii; simpl in REGEX2FRAGMENT.
  - inv REGEX2FRAGMENT. split; ii; contradiction.
  - inv REGEX2FRAGMENT. split; ii; simpl in *.
    + destruct H as [EQ | []]. inv EQ. lia.
    + contradiction.
  - inv REGEX2FRAGMENT. split; ii; simpl in *.
    + contradiction.
    + destruct H as [EQ | []]. subst edge. simpl. lia.
  - destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    pose proof (IH1 _ _ _ REGEX1) as [EPS1 CHAR1].
    pose proof (IH2 _ _ _ REGEX2) as [EPS2 CHAR2].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 _ _].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 _ _].
    inv REGEX2FRAGMENT. split; ii; simpl in *.
    + des; try (inv H; lia). rewrite in_app_iff in H. des; eauto; [pose proof (EPS1 _ _ H) | pose proof (EPS2 _ _ H)]; lia.
    + rewrite in_app_iff in H. des; eauto; [pose proof (CHAR1 _ H) | pose proof (CHAR2 _ H)]; lia.
  - destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    pose proof (IH1 _ _ _ REGEX1) as [EPS1 CHAR1].
    pose proof (IH2 _ _ _ REGEX2) as [EPS2 CHAR2].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 _ _].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 _ _].
    inv REGEX2FRAGMENT. split; ii; simpl in *.
    + des; try (inv H; lia). rewrite in_app_iff in H. des; eauto; [pose proof (EPS1 _ _ H) | pose proof (EPS2 _ _ H)]; lia.
    + rewrite in_app_iff in H. des; eauto; [pose proof (CHAR1 _ H) | pose proof (CHAR2 _ H)]; lia.
  - destruct (regex2fragment e (qi + 1)) as [qf1 frag1] eqn: REGEX.
    pose proof (IH _ _ _ REGEX) as [EPS1 CHAR1].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ LT1 _ _].
    inv REGEX2FRAGMENT. split; ii; simpl in *.
    + des; try (inv H; lia). pose proof (EPS1 _ _ H). lia.
    + pose proof (CHAR1 _ H). lia.
Qed.

Lemma regex2fragment_edge_dst_gt_start e qi qf frag
  (REGEX2FRAGMENT : regex2fragment e qi = (qf, frag))
  : (forall q, forall q', (q, q') ∈ frag.(frag_eps_edges) -> qi < q') /\ (forall edge, edge ∈ frag.(frag_char_edges) -> qi < edge.(char_edge_dst)).
Proof.
  revert qi qf frag REGEX2FRAGMENT.
  induction e as [ | | c | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH]; ii; simpl in REGEX2FRAGMENT.
  - inv REGEX2FRAGMENT. split; ii; contradiction.
  - inv REGEX2FRAGMENT. split; ii; simpl in *.
    + destruct H as [EQ | []]. inv EQ. lia.
    + contradiction.
  - inv REGEX2FRAGMENT. split; ii; simpl in *.
    + contradiction.
    + destruct H as [EQ | []]. subst edge. simpl. lia.
  - destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    pose proof (IH1 _ _ _ REGEX1) as [EPS1 CHAR1].
    pose proof (IH2 _ _ _ REGEX2) as [EPS2 CHAR2].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 _ _].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 _ _].
    inv REGEX2FRAGMENT. split; ii; simpl in *.
    + des; try (inv H; lia). rewrite in_app_iff in H. des; [pose proof (EPS1 _ _ H) | pose proof (EPS2 _ _ H)]; lia.
    + rewrite in_app_iff in H. des; [pose proof (CHAR1 _ H) | pose proof (CHAR2 _ H)]; lia.
  - destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    pose proof (IH1 _ _ _ REGEX1) as [EPS1 CHAR1].
    pose proof (IH2 _ _ _ REGEX2) as [EPS2 CHAR2].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 _ _].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 _ _].
    inv REGEX2FRAGMENT. split; ii; simpl in *.
    + des; try (inv H; lia). rewrite in_app_iff in H. des; [pose proof (EPS1 _ _ H) | pose proof (EPS2 _ _ H)]; lia.
    + rewrite in_app_iff in H. des; [pose proof (CHAR1 _ H) | pose proof (CHAR2 _ H)]; lia.
  - destruct (regex2fragment e (qi + 1)) as [qf1 frag1] eqn: REGEX.
    pose proof (IH _ _ _ REGEX) as [EPS1 CHAR1].
    pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ LT1 _ _].
    inv REGEX2FRAGMENT. split; ii; simpl in *.
    + des; try (inv H; lia). pose proof (EPS1 _ _ H). lia.
    + pose proof (CHAR1 _ H). lia.
Qed.

Lemma regex2fragment_complete_aux (e : regex ascii) (s : Input.t) (frags : list (Rule.t * fragment)) (rule : Rule.t) (qi : nat) (qf : nat) (frag : fragment) (topfrag : fragment)
  (IN_REGEX : s \in eval_regex e)
  (REGEX2FRAGMENT : regex2fragment e qi = (qf, frag))
  (FRAGMENTS : TaggedENFA_FRAGMENTS frags rule topfrag)
  (EPS_INCL : forall q, forall q', (q, q') ∈ frag.(frag_eps_edges) -> (q, q') ∈ topfrag.(frag_eps_edges))
  (CHAR_INCL : forall edge, edge ∈ frag.(frag_char_edges) -> edge ∈ topfrag.(frag_char_edges))
  : frag.(frag_accept) \in fragments_delta_star frags frag.(frag_start) s.
Proof.
  revert s IN_REGEX frags rule qi qf frag topfrag REGEX2FRAGMENT FRAGMENTS EPS_INCL CHAR_INCL.
  induction e as [ | | c | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH]; ii.
  - simpl in IN_REGEX. contradiction.
  - simpl in IN_REGEX. autorewrite with simplication_hints in IN_REGEX.
    subst s. simpl in REGEX2FRAGMENT. inv REGEX2FRAGMENT.
    pose proof (TaggedENFA_FRAGMENTS_delta_star_step frags rule topfrag FRAGMENTS) as [EPS _].
    eapply EPS. eapply EPS_INCL. simpl. left. reflexivity.
  - simpl in IN_REGEX. autorewrite with simplication_hints in IN_REGEX.
    subst s. simpl in REGEX2FRAGMENT. inv REGEX2FRAGMENT.
    pose proof (TaggedENFA_FRAGMENTS_delta_star_step frags rule topfrag FRAGMENTS) as [_ CHAR].
    eapply CHAR with (edge := mkCharEdge qi c (qi + 1)).
    eapply CHAR_INCL. simpl. left. reflexivity.
  - simpl in REGEX2FRAGMENT. cbn [eval_regex] in IN_REGEX.
    autorewrite with simplication_hints in IN_REGEX.
    destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    inv REGEX2FRAGMENT. destruct IN_REGEX as [IN1 | IN2].
    + pose proof (TaggedENFA_FRAGMENTS_delta_star_step frags rule topfrag FRAGMENTS) as [EPS _].
      pose proof (regex2fragment_start_accept _ _ _ _ REGEX1) as [START1 ACCEPT1].
      rewrite <- app_nil_r with (l := s). eapply delta_star_app with (q2 := qf1).
      * change s with ([] ++ s).
        eapply delta_star_app with (q2 := qi + 1).
        { eapply EPS. eapply EPS_INCL. simpl. left. reflexivity. }
        { rewrite <- START1. rewrite <- ACCEPT1.
          eapply IH1 with (s := s) (qi := qi + 1) (qf := qf1); eauto.
          - intros q q' IN_EDGE. eapply EPS_INCL. simpl. s!; tauto.
          - intros edge IN_EDGE. eapply CHAR_INCL. simpl. s!; tauto.
        }
      * eapply EPS. eapply EPS_INCL. simpl; s!; tauto.
    + pose proof (TaggedENFA_FRAGMENTS_delta_star_step frags rule topfrag FRAGMENTS) as [EPS _].
      pose proof (regex2fragment_start_accept _ _ _ _ REGEX2) as [START2 ACCEPT2].
      rewrite <- app_nil_r with (l := s). eapply delta_star_app with (q2 := qf2).
      * change s with ([] ++ s). eapply delta_star_app with (q2 := qf1 + 1).
        { eapply EPS. eapply EPS_INCL. simpl. right; left. reflexivity. }
        { rewrite <- START2. rewrite <- ACCEPT2.
          eapply IH2 with (s := s) (qi := qf1 + 1) (qf := qf2); eauto.
          - intros q q' IN_EDGE. eapply EPS_INCL. simpl. s!; tauto.
          - intros edge IN_EDGE. eapply CHAR_INCL. simpl. s!; tauto.
        }
      * eapply EPS. eapply EPS_INCL. simpl. s!; tauto.
  - simpl in REGEX2FRAGMENT. cbn [eval_regex] in IN_REGEX.
    rewrite E.liftM2_spec in IN_REGEX.
    destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    inv REGEX2FRAGMENT.
    destruct IN_REGEX as (s1 & IN1 & s2 & IN2 & EQ). subst s.
    pose proof (TaggedENFA_FRAGMENTS_delta_star_step frags rule topfrag FRAGMENTS) as [EPS _].
    pose proof (regex2fragment_start_accept _ _ _ _ REGEX1) as [START1 ACCEPT1].
    pose proof (regex2fragment_start_accept _ _ _ _ REGEX2) as [START2 ACCEPT2].
    eapply delta_star_app with (q2 := qf1) (s1 := s1) (s2 := s2).
    + change s1 with ([] ++ s1).
      eapply delta_star_app with (q2 := qi + 1).
      { eapply EPS. eapply EPS_INCL. simpl. left. reflexivity. }
      { rewrite <- START1. rewrite <- ACCEPT1.
        eapply IH1 with (s := s1) (qi := qi + 1) (qf := qf1); eauto.
        - intros q q' IN_EDGE. eapply EPS_INCL. simpl; s!; tauto.
        - intros edge IN_EDGE. eapply CHAR_INCL. simpl; s!; tauto.
      }
    + rewrite <- app_nil_r with (l := s2).
      eapply delta_star_app with (q2 := qf2).
      * change s2 with ([] ++ s2).
        eapply delta_star_app with (q2 := qf1 + 1).
        { eapply EPS. eapply EPS_INCL. simpl. right; left. reflexivity. }
        { rewrite <- START2. rewrite <- ACCEPT2.
          eapply IH2 with (s := s2) (qi := qf1 + 1) (qf := qf2); eauto.
          - intros q q' IN_EDGE. eapply EPS_INCL. simpl; s!; tauto.
          - intros edge IN_EDGE. eapply CHAR_INCL. simpl; s!; tauto.
        }
      * eapply EPS. eapply EPS_INCL. simpl. s!; tauto.
  - simpl in REGEX2FRAGMENT. simpl in IN_REGEX.
    destruct (regex2fragment e (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    inv REGEX2FRAGMENT.
    pose proof (TaggedENFA_FRAGMENTS_delta_star_step frags rule topfrag FRAGMENTS) as [EPS _].
    pose proof (regex2fragment_start_accept _ _ _ _ REGEX1) as [START1 ACCEPT1].
    assert (TAIL : forall t, t \in star (eval_regex e) -> qf1 + 1 \in fragments_delta_star frags (qi + 1) t).
    { intros t STAR_IN. induction STAR_IN as [ | s1 s2 IN1 IN2 IHSTAR].
      - eapply EPS. eapply EPS_INCL. simpl. right; right; left. reflexivity.
      - replace (s1 ++ s2) with ((s1 ++ []) ++ s2) by now rewrite app_nil_r.
        eapply delta_star_app with (q2 := qi + 1).
        + eapply delta_star_app with (q2 := qf1).
          * rewrite <- START1. rewrite <- ACCEPT1.
            eapply IH with (s := s1) (qi := qi + 1) (qf := qf1); eauto.
            { intros q q' IN_EDGE. eapply EPS_INCL. simpl. s!; tauto. }
          * eapply EPS. eapply EPS_INCL. simpl. s!; tauto.
        + exact IHSTAR.
    }
    change s with ([] ++ s).
    eapply delta_star_app with (q2 := qi + 1).
    + eapply EPS. eapply EPS_INCL. s!; tauto.
    + eapply TAIL. exact IN_REGEX.
Qed.

Theorem regex2fragment_complete frags rule qi qf frag s
  (REGEX2FRAGMENT : regex2fragment rule.(Rule.regex) qi = (qf, frag))
  (FRAGMENTS : TaggedENFA_FRAGMENTS frags rule frag)
  (IN_REGEX : s \in eval_regex rule.(Rule.regex))
  : frag.(frag_accept) \in fragments_delta_star frags frag.(frag_start) s.
Proof.
  eapply regex2fragment_complete_aux; eauto.
Qed.

Theorem TaggedENFA_FRAGMENTS_complete qmax frags rule qi qf frag s
  (REGEX2FRAGMENT : regex2fragment rule.(Rule.regex) qi = (qf, frag))
  (FRAGMENTS : TaggedENFA_FRAGMENTS frags rule frag)
  (IN_REGEX : s \in eval_regex rule.(Rule.regex))
  : accepts (fragments2TaggedENFA qmax frags) s rule.(Rule.token).
Proof.
  destruct FRAGMENTS as [START ACCEPT EPS CHAR].
  exists frag.(frag_accept). split; eauto.
  change s with ([] ++ s).
  eapply delta_star_app with (q2 := frag.(frag_start)).
  - eapply delta_star_eps with (q1 := frag.(frag_start)); eauto. econs.
  - eapply regex2fragment_complete; eauto. econs; eauto.
Qed.

Theorem rules2fragments_complete qi rules qmax frags rule
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_RULE : rule ∈ rules)
  : exists qi_rule, exists qf, exists frag, regex2fragment rule.(Rule.regex) qi_rule = (qf, frag) /\ (rule, frag) ∈ frags.
Proof.
  revert qi qmax frags FRAGS IN_RULE. induction rules as [ | rule' rules IH]; intros qi qmax frags FRAGS IN_RULE; simpl in IN_RULE; try tauto.
  simpl in FRAGS. destruct (regex2fragment rule'.(Rule.regex) qi) as [qf frag] eqn: REGEX2FRAGMENT.
  destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'. s!; des; subst.
  - exists qi, qf, frag. ss!.
  - pose proof (IH (qf + 1) qmax frags' FRAGS' IN_RULE) as (qi_rule & qf_rule & frag_rule & REGEX & IN_FRAGS).
    exists qi_rule, qf_rule, frag_rule. ss!.
Qed.

Lemma rules2fragments_sound qi rules qmax frags rule frag
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  : rule ∈ rules.
Proof.
  revert qi qmax frags FRAGS IN_FRAG. induction rules as [ | rule' rules IH]; ii; simpl in FRAGS.
  - now inv FRAGS.
  - destruct (regex2fragment rule'.(Rule.regex) qi) as [qf frag'] eqn: REGEX.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    s!; des; subst. destruct IN_FRAG as [EQ | IN_FRAG]; ss!.
Qed.

Lemma rules2fragments_bounds qi rules qmax frags
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  : qi <= qmax /\ ⟪ BOUND : forall rule, forall frag, (rule, frag) ∈ frags -> (exists qi_rule, exists qf, regex2fragment rule.(Rule.regex) qi_rule = (qf, frag) /\ FRAGMENT_BOUNDS qi_rule qf frag /\ qi <= qi_rule /\ qf < qmax) ⟫.
Proof.
  revert qi qmax frags FRAGS.
  induction rules as [ | rule' rules IH]; intros qi qmax frags FRAGS; simpl in FRAGS.
  - inv FRAGS. split; [lia | intros rule frag IN; contradiction].
  - destruct (regex2fragment rule'.(Rule.regex) qi) as [qf frag] eqn: REGEX2FRAGMENT.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    injection FRAGS as Hqmax Hfrags. subst qmax frags.
    pose proof (regex2fragment_bounds _ _ _ _ REGEX2FRAGMENT) as BOUNDS.
    assert (LT : qi < qf) by now destruct BOUNDS as [_ _ LT _ _].
    pose proof (IH (qf + 1) qmax' frags' FRAGS') as [QMAX TAIL].
    split; [done! | intros rule frag' IN]. destruct IN as [EQ | IN].
    + inv EQ. exists qi, qf. split; eauto. split; eauto. split; lia.
    + pose proof (TAIL rule frag' IN) as (qi_rule & qf_rule & REGEX & BOUNDS' & LE_START & LT_END).
      exists qi_rule, qf_rule; done!.
Qed.

Lemma rules2fragments_ranges_disjoint qi rules qmax frags rule1 frag1 qi1 qf1 rule2 frag2 qi2 qf2 q
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN1 : (rule1, frag1) ∈ frags)
  (IN2 : (rule2, frag2) ∈ frags)
  (REGEX1 : regex2fragment rule1.(Rule.regex) qi1 = (qf1, frag1))
  (REGEX2 : regex2fragment rule2.(Rule.regex) qi2 = (qf2, frag2))
  (RANGE1 : qi1 <= q <= qf1)
  (RANGE2 : qi2 <= q <= qf2)
  : (rule1, frag1) = (rule2, frag2).
Proof.
  revert qi qmax frags FRAGS rule1 frag1 qi1 qf1 rule2 frag2 qi2 qf2 q IN1 IN2 REGEX1 REGEX2 RANGE1 RANGE2. induction rules as [ | rule rules IH]; ii; simpl in FRAGS.
  - now inv FRAGS.
  - destruct (regex2fragment rule.(Rule.regex) qi) as [qf frag] eqn: REGEX.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    s!; des; subst. pose proof (rules2fragments_bounds _ _ _ _ FRAGS') as [_ TAIL_BOUNDS].
    destruct IN1 as [EQ1 | IN1]; destruct IN2 as [EQ2 | IN2]; rewrite <- inject_pair_eq.
    + inv EQ1. inv EQ2. reflexivity.
    + inv EQ1.
      pose proof (regex2fragment_same_fragment _ _ _ _ _ _ REGEX1 REGEX) as [EQ_QI EQ_QF]. subst qi1 qf1.
      pose proof (TAIL_BOUNDS _ _ IN2) as (qi2' & qf2' & REGEX2' & _ & LE2 & _).
      pose proof (regex2fragment_same_fragment _ _ _ _ _ _ REGEX2 REGEX2') as [EQ_QI EQ_QF]. subst qi2 qf2.
      lia.
    + inv EQ2.
      pose proof (regex2fragment_same_fragment _ _ _ _ _ _ REGEX2 REGEX) as [EQ_QI EQ_QF]. subst qi2 qf2.
      pose proof (TAIL_BOUNDS _ _ IN1) as (qi1' & qf1' & REGEX1' & _ & LE1 & _).
      pose proof (regex2fragment_same_fragment _ _ _ _ _ _ REGEX1 REGEX1') as [EQ_QI EQ_QF]. subst qi1 qf1.
      lia.
    + eapply IH; eauto.
Qed.

#[local] Hint Resolve regex2fragment_bounds : simplication_hints.

Lemma fragment_eps_edges_owner qi rules qmax frags q q'
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_EDGE : (q, q') ∈ fragment_eps_edges frags)
  (SRC_NONZERO : q ≠ 0)
  : exists rule, exists frag, exists qi_rule, exists qf, (rule, frag) ∈ frags /\ regex2fragment rule.(Rule.regex) qi_rule = (qf, frag) /\ FRAGMENT_BOUNDS qi_rule qf frag /\ qi <= qi_rule /\ qf < qmax /\ qi_rule <= q <= qf /\ (q, q') ∈ frag.(frag_eps_edges).
Proof.
  revert qi qmax frags FRAGS IN_EDGE; induction rules as [ | rule rules IH]; ii; simpl in FRAGS.
  - now inv FRAGS.
  - destruct (regex2fragment rule.(Rule.regex) qi) as [qf frag] eqn: REGEX.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    s!; des; subst. pose proof (rules2fragments_bounds _ _ _ _ FRAGS') as [QMAX _].
    simpl in IN_EDGE. destruct IN_EDGE as [EQ | IN_EDGE].
    + now inv EQ.
    + rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ LT EPS _].
        pose proof (EPS _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *.
        exists rule, frag, qi, qf. splits; lia || ss!.
      * pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ LT _ _].
        pose proof (IH (qf + 1) qmax frags' FRAGS' IN_EDGE) as (rule' & frag' & qi_rule & qf' & IN_FRAG & REGEX' & BOUNDS & LE & LT' & RANGE & IN_EDGE').
        exists rule', frag', qi_rule, qf'. splits; lia || ss!.
Qed.

Lemma fragment_eps_edges_start_sound qi rules qmax frags q'
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (qi_POS : 0 < qi)
  (IN_EDGE : (0, q') ∈ fragment_eps_edges frags)
  : exists rule, exists frag, exists qi_rule, exists qf, (rule, frag) ∈ frags /\ regex2fragment rule.(Rule.regex) qi_rule = (qf, frag) /\ q' = frag.(frag_start).
Proof.
  revert qi qmax frags q' FRAGS qi_POS IN_EDGE; induction rules as [ | rule rules IH]; ii; simpl in FRAGS.
  - now inv FRAGS.
  - destruct (regex2fragment rule.(Rule.regex) qi) as [qf frag] eqn: REGEX.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    s!; des; subst. simpl in IN_EDGE. destruct IN_EDGE as [EQ | IN_EDGE].
    + inv EQ. exists rule, frag, qi, qf. ss!.
    + s!. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ _ EPS _].
        pose proof (EPS _ IN_EDGE); done!.
      * pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ LT _ _].
        assert (qi_POS' : 0 < qf + 1) by lia.
        pose proof (IH (qf + 1) qmax frags' q' FRAGS' qi_POS' IN_EDGE) as (rule' & frag' & qi_rule & qf' & IN_FRAG & REGEX' & START).
        exists rule', frag', qi_rule, qf'. done!.
Qed.

Lemma fragment_char_edges_owner qi rules qmax frags edge
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_EDGE : edge ∈ fragment_char_edges frags)
  : exists rule, exists frag, exists qi_rule, exists qf, (rule, frag) ∈ frags /\ regex2fragment rule.(Rule.regex) qi_rule = (qf, frag) /\ FRAGMENT_BOUNDS qi_rule qf frag /\ qi <= qi_rule /\ qf < qmax /\ qi_rule <= edge.(char_edge_src) <= qf /\ edge ∈ frag.(frag_char_edges).
Proof.
  revert qi qmax frags FRAGS IN_EDGE; induction rules as [ | rule rules IH]; ii; simpl in FRAGS.
  - now inv FRAGS.
  - destruct (regex2fragment rule.(Rule.regex) qi) as [qf frag] eqn: REGEX.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    s!; des; subst. pose proof (rules2fragments_bounds _ _ _ _ FRAGS') as [QMAX _].
    simpl in IN_EDGE. rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
    + pose proof (regex2fragment_bounds _ _ _ _ REGEX) as BOUNDS.
      destruct BOUNDS as [_ _ LT _ CHAR].
      pose proof (CHAR _ IN_EDGE). unfold char_edge_in_range in *.
      exists rule, frag, qi, qf. splits; lia || ss!.
    + pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ LT _ _].
      pose proof (IH (qf + 1) qmax frags' FRAGS' IN_EDGE) as (rule' & frag' & qi_rule & qf' & IN_FRAG & REGEX' & BOUNDS & LE & LT' & RANGE & IN_EDGE').
      exists rule', frag', qi_rule, qf'. splits; lia || ss!.
Qed.

Lemma fragments2TaggedENFA_okay rules qmax frags
  (FRAGS : rules2fragments 1 rules = (qmax, frags))
  : TaggedENFA.okay (fragments2TaggedENFA qmax frags).
Proof.
  split; simpl.
  - rewrite in_seq. pose proof (rules2fragments_bounds _ _ _ _ FRAGS) as [LE _]. lia.
  - intros q tag ACCEPT.
    pose proof (fragment_accept_states_sound _ _ _ ACCEPT) as (rule & frag & IN_FRAG & ACCEPT_EQ & TOKEN_EQ); subst q tag.
    pose proof (rules2fragments_bounds _ _ _ _ FRAGS) as [_ BOUND].
    pose proof (BOUND _ _ IN_FRAG) as (qi_rule & qf & REGEX & [_ ACCEPT_EQ _ _ _] & LE_START & LT_END); subst qf.
    rewrite in_seq. lia.
  - intros q q' IN_STATES STEP.
    pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE.
    destruct (eq_dec q 0) as [EQ | NE].
    + subst q.
      assert (QI_POS : 0 < 1) by lia.
      pose proof (fragment_eps_edges_start_sound _ _ _ _ _ FRAGS QI_POS IN_EDGE) as (rule & frag & qi_rule & qf & IN_FRAG & REGEX & START_EQ); subst q'.
      pose proof (rules2fragments_bounds _ _ _ _ FRAGS) as [_ BOUND].
      pose proof (BOUND _ _ IN_FRAG) as (qi_rule' & qf' & REGEX' & [START_EQ _ LT _ _] & LE_START & LT_END).
      pose proof (regex2fragment_same_fragment _ _ _ _ _ _ REGEX REGEX') as [EQ_QI EQ_QF]; subst qi_rule' qf'.
      rewrite in_seq. lia.
    + pose proof (fragment_eps_edges_owner _ _ _ _ _ _ FRAGS IN_EDGE NE) as (rule & frag & qi_rule & qf & IN_FRAG & REGEX & [_ _ _ EPS _] & LE_START & LT_END & RANGE & IN_EDGE').
      pose proof (EPS _ IN_EDGE') as RANGE'.
      unfold eps_edge_in_range in RANGE'. simpl in RANGE'. rewrite in_seq. lia.
  - intros q q' c IN_STATES STEP.
    pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST); subst q q' c.
    pose proof (fragment_char_edges_owner _ _ _ _ _ FRAGS IN_EDGE) as (rule & frag & qi_rule & qf & IN_FRAG & REGEX & BOUNDS & LE_START & LT_END & RANGE & IN_EDGE').
    destruct BOUNDS as [_ _ _ _ CHAR].
    pose proof (CHAR _ IN_EDGE') as RANGE'.
    unfold char_edge_in_range in RANGE'. simpl in RANGE'. rewrite in_seq. lia.
Qed.

Theorem mkUnitedTaggedENFA_okay rules
  : TaggedENFA.okay (mkUnitedTaggedENFA rules).
Proof.
  unfold mkUnitedTaggedENFA. destruct (rules2fragments 1 rules) as [qmax frags] eqn: FRAGS.
  now eapply fragments2TaggedENFA_okay with (rules := rules).
Qed.

Lemma fragment_eps_edges_isolate qi rules qmax frags rule frag qi_rule qf q q'
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) qi_rule = (qf, frag))
  (SRC_NONZERO : q ≠ 0)
  (RANGE : qi_rule <= q <= qf)
  (IN_EDGE : (q, q') ∈ fragment_eps_edges frags)
  : (q, q') ∈ frag.(frag_eps_edges).
Proof.
  pose proof (fragment_eps_edges_owner _ _ _ _ _ _ FRAGS IN_EDGE SRC_NONZERO) as (rule' & frag' & qi_rule' & qf' & IN_FRAG' & REGEX' & _ & _ & _ & RANGE' & IN_EDGE').
  pose proof (rules2fragments_ranges_disjoint _ _ _ _ _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG IN_FRAG' REGEX REGEX' RANGE RANGE') as EQ.
  ss!.
Qed.

Lemma fragment_char_edges_isolate qi rules qmax frags rule frag qi_rule qf edge
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) qi_rule = (qf, frag))
  (RANGE : qi_rule <= edge.(char_edge_src) <= qf)
  (IN_EDGE : edge ∈ fragment_char_edges frags)
  : edge ∈ frag.(frag_char_edges).
Proof.
  pose proof (fragment_char_edges_owner _ _ _ _ _ FRAGS IN_EDGE) as (rule' & frag' & qi_rule' & qf' & IN_FRAG' & REGEX' & _ & _ & _ & RANGE' & IN_EDGE').
  pose proof (rules2fragments_ranges_disjoint _ _ _ _ _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG IN_FRAG' REGEX REGEX' RANGE RANGE') as EQ.
  ss!.
Qed.

Lemma rules2fragments_start_ge qi rules qmax frags rule frag qi_rule qf
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) qi_rule = (qf, frag))
  : qi <= qi_rule.
Proof.
  pose proof (rules2fragments_bounds _ _ _ _ FRAGS) as [_ BOUND].
  pose proof (BOUND _ _ IN_FRAG) as (qi_rule' & qf' & REGEX' & _ & LE & _).
  pose proof (regex2fragment_same_fragment _ _ _ _ _ _ REGEX REGEX') as [EQ _].
  ss!.
Qed.

Lemma delta_star_fragment_range qi rules qmax frags rule frag qi_rule qf q q' s
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) qi_rule = (qf, frag))
  (qi_POS : 0 < qi)
  (RANGE : qi_rule <= q <= qf)
  (DELTA : q' \in fragments_delta_star frags q s)
  : qi_rule <= q' <= qf.
Proof.
  revert qi rules rule frag qi_rule qf FRAGS IN_FRAG REGEX qi_POS RANGE; induction DELTA; ii.
  - exact RANGE.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE.
    assert (SRC_NONZERO : q ≠ 0) by (pose proof (rules2fragments_start_ge _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX); lia).
    pose proof (fragment_eps_edges_isolate _ _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX SRC_NONZERO RANGE IN_EDGE) as IN_FRAG_EDGE.
    pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ _ EPS _].
    pose proof (EPS _ IN_FRAG_EDGE). unfold eps_edge_in_range in *. simpl in *.
    eapply IHDELTA; eauto. lia.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    assert (RANGE_SRC : qi_rule <= edge.(char_edge_src) <= qf) by lia.
    pose proof (fragment_char_edges_isolate _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX RANGE_SRC IN_EDGE) as IN_FRAG_EDGE.
    pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ _ _ CHAR].
    pose proof (CHAR _ IN_FRAG_EDGE). unfold char_edge_in_range in *.
    eapply IHDELTA; eauto. lia.
Qed.

Lemma delta_star_global_to_fragment qi rules qmax frags rule frag qi_rule qf q q' s
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) qi_rule = (qf, frag))
  (qi_POS : 0 < qi)
  (RANGE : qi_rule <= q <= qf)
  (DELTA : q' \in fragments_delta_star frags q s)
  : q' \in fragment_delta_star frag q s.
Proof.
  revert qi rules rule frag qi_rule qf FRAGS IN_FRAG REGEX qi_POS RANGE. induction DELTA; ii.
  - econs.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE.
    assert (SRC_NONZERO : q ≠ 0) by (pose proof (rules2fragments_start_ge _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX); lia).
    pose proof (fragment_eps_edges_isolate _ _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX SRC_NONZERO RANGE IN_EDGE) as IN_FRAG_EDGE.
    pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ _ EPS _].
    pose proof (EPS _ IN_FRAG_EDGE). unfold eps_edge_in_range in *. simpl in *.
    eapply delta_star_eps.
    + eapply eps_step_from_edges_complete. exact IN_FRAG_EDGE.
    + eapply IHDELTA; eauto. lia.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    assert (RANGE_SRC : qi_rule <= edge.(char_edge_src) <= qf) by lia.
    pose proof (fragment_char_edges_isolate _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX RANGE_SRC IN_EDGE) as IN_FRAG_EDGE.
    pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ _ _ CHAR].
    pose proof (CHAR _ IN_FRAG_EDGE). unfold char_edge_in_range in *.
    eapply delta_star_char with (q1 := edge.(char_edge_dst)).
    + rewrite <- SRC. rewrite <- LABEL. eapply char_step_from_edges_complete. exact IN_FRAG_EDGE.
    + rewrite DST. eapply IHDELTA; eauto. lia.
Qed.

Lemma regex2fragment_global_to_local qi rules qmax frags rule qf frag s
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) frag.(frag_start) = (qf, frag))
  (qi_POS : 0 < qi)
  (DELTA : frag.(frag_accept) \in fragments_delta_star frags frag.(frag_start) s)
  : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s.
Proof.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [START ACCEPT LT _ _].
  eapply delta_star_global_to_fragment; eauto. lia.
Qed.

Lemma delta_star_fragment_elim qi rules qmax frags rule frag qi_rule qf q q' s
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) qi_rule = (qf, frag))
  (qi_POS : 0 < qi)
  (RANGE : qi_rule <= q <= qf)
  (DELTA : q' \in fragments_delta_star frags q s)
  : ⟪ DELTA_STAR_NIL : s = [] /\ q' = q ⟫ \/ ⟪ DELTA_STAR_EPS : exists q1, (q, q1) ∈ frag.(frag_eps_edges) /\ q' \in fragments_delta_star frags q1 s ⟫ \/ ⟪ DELTA_STAR_CHAR : exists edge, exists s', s = edge.(char_edge_label) :: s' /\ edge ∈ frag.(frag_char_edges) /\ q' \in fragments_delta_star frags edge.(char_edge_dst) s' ⟫.
Proof.
  pose proof (delta_star_elim _ _ q q' s DELTA) as [NIL | [EPS | CHAR]]; [left | right; left | right; right]; unnw; try tauto.
  - destruct EPS as (q1 & STEP & REST).
    pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE.
    assert (SRC_NONZERO : q ≠ 0) by now pose proof (rules2fragments_start_ge _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX); lia.
    pose proof (fragment_eps_edges_isolate _ _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX SRC_NONZERO RANGE IN_EDGE) as IN_FRAG_EDGE.
    exists q1. ss!.
  - destruct CHAR as (c & s' & q1 & EQ & STEP & REST).
    pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    assert (RANGE_SRC : qi_rule <= edge.(char_edge_src) <= qf) by lia.
    pose proof (fragment_char_edges_isolate _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX RANGE_SRC IN_EDGE) as IN_FRAG_EDGE.
    exists edge, s'. ss!.
Qed.

Lemma fragment_delta_star_elim frag q q' s
  (DELTA : q' \in fragment_delta_star frag q s)
  : ⟪ DELTA_STAR_NIL : s = [] /\ q' = q ⟫ \/ ⟪ DELTA_STAR_EPS : exists q1, (q, q1) ∈ frag.(frag_eps_edges) /\ q' \in fragment_delta_star frag q1 s ⟫ \/ ⟪ DELTA_STAR_CHAR : exists edge, exists s', s = edge.(char_edge_label) :: s' /\ edge ∈ frag.(frag_char_edges) /\ q' \in fragment_delta_star frag edge.(char_edge_dst) s' ⟫.
Proof.
  pose proof (delta_star_elim _ _ q q' s DELTA) as [NIL | [EPS | CHAR]]; [left | right; left | right; right]; unnw; try tauto.
  - destruct EPS as (q1 & STEP & REST). pose proof (eps_step_from_edges_sound _ _ _ STEP). exists q1; ss!.
  - destruct CHAR as (c & s' & q1 & EQ & STEP & REST). pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST). exists edge, s'; ss!.
Qed.

Lemma fragment_delta_star_elim_with_src frag q q' s
  (DELTA : q' \in fragment_delta_star frag q s)
  : ⟪ DELTA_STAR_NIL : s = [] /\ q' = q ⟫ \/ ⟪ DELTA_STAR_EPS : exists q1, (q, q1) ∈ frag.(frag_eps_edges) /\ q' \in fragment_delta_star frag q1 s ⟫ \/ ⟪ DELTA_STAR_CHAR : exists edge, exists s', s = edge.(char_edge_label) :: s' /\ edge.(char_edge_src) = q /\ edge ∈ frag.(frag_char_edges) /\ q' \in fragment_delta_star frag edge.(char_edge_dst) s' ⟫.
Proof.
  pose proof (delta_star_elim _ _ q q' s DELTA) as [NIL | [EPS | CHAR]]; [left | right; left | right; right]; unnw; try tauto.
  - destruct EPS as (q1 & STEP & REST). pose proof (eps_step_from_edges_sound _ _ _ STEP). exists q1; ss!.
  - destruct CHAR as (c & s' & q1 & EQ & STEP & REST). pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST). exists edge, s'. ss!.
Qed.

Lemma regex2fragment_Union_delta_star_start qi qf frag e1 e2 s
  (REGEX : regex2fragment (Re.Union e1 e2) qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : exists qf1, exists frag1, exists qf2, exists frag2, regex2fragment e1 (qi + 1) = (qf1, frag1) /\ regex2fragment e2 (qf1 + 1) = (qf2, frag2) /\ (frag.(frag_accept) \in fragment_delta_star frag (qi + 1) s \/ frag.(frag_accept) \in fragment_delta_star frag (qf1 + 1) s).
Proof.
  simpl in REGEX. destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1. destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2. inv REGEX.
  exists qf1, frag1, qf2, frag2. splits; simpl; eauto.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  pose proof (fragment_delta_star_elim_with_src _ _ _ _ DELTA) as [NIL | [EPS | CHAR]].
  - des; simpl in *; lia.
  - destruct EPS as (q1 & IN_EDGE & REST). simpl in IN_EDGE. s!; des; subst.
    + left. exact REST.
    + right. exact REST.
    + exfalso; lia.
    + exfalso; lia.
    + pose proof (EPS1 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. exfalso; lia.
    + pose proof (EPS2 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. exfalso; lia.
  - destruct CHAR as (edge & s' & EQ & SRC & IN_EDGE & REST). simpl in IN_EDGE. s!; des.
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. exfalso; lia.
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. exfalso; lia.
Qed.

#[local] Opaque eps_step_from_edges.
#[local] Opaque char_step_from_edges.

#[local] Hint Constructors eclosure : simplication_hints.
#[local] Hint Constructors delta_star : simplication_hints.

Lemma regex2fragment_Union_left_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 q q' s
  (REGEX : regex2fragment (Re.Union e1 e2) qi = (qf, frag))
  (REGEX1 : regex2fragment e1 (qi + 1) = (qf1, frag1))
  (REGEX2 : regex2fragment e2 (qf1 + 1) = (qf2, frag2))
  (RANGE : qi + 1 <= q <= qf1)
  (DELTA : q' \in fragment_delta_star frag q s)
  (ACCEPT : q' = frag.(frag_accept))
  : exists s1, exists s2, s = s1 ++ s2 /\ qf1 \in fragment_delta_star frag1 q s1 /\ frag.(frag_accept) \in fragment_delta_star frag frag.(frag_accept) s2.
Proof.
  revert q q' s RANGE DELTA ACCEPT; simpl in REGEX; rewrite -> REGEX1, -> REGEX2 in REGEX; inv REGEX.
  intros q q' s RANGE DELTA ACCEPT.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  induction DELTA.
  - simpl in *. exfalso; lia.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE. simpl in IN_EDGE; s!; des; subst.
    + exfalso; lia.
    + exfalso; lia.
    + exists [], s; ss!.
    + exfalso; lia.
    + pose proof (EPS1 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]]. simpl in SRC_LO, SRC_HI, DST_LO, DST_HI.
      assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
      pose proof (IHDELTA RANGE_STEP eq_refl) as (s1 & s2 & EQ & DELTA1 & DELTA2).
      exists s1, s2. splits; eauto. eapply delta_star_eps; eauto. eapply eps_step_from_edges_complete; eauto.
    + pose proof (EPS2 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in *. lia.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST); simpl in IN_EDGE; s!; des.
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
      assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
      pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
      exists (edge.(char_edge_label) :: s1), s2. splits; auto.
      * rewrite EQ. simpl. now rewrite LABEL.
      * eapply delta_star_char with (q1 := q1); auto.
        rewrite <- DST. rewrite <- SRC. eapply char_step_from_edges_complete; auto.
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in SRC. lia.
Qed.

Lemma regex2fragment_Union_right_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 q q' s
  (REGEX : regex2fragment (Re.Union e1 e2) qi = (qf, frag))
  (REGEX1 : regex2fragment e1 (qi + 1) = (qf1, frag1))
  (REGEX2 : regex2fragment e2 (qf1 + 1) = (qf2, frag2))
  (RANGE : qf1 + 1 <= q <= qf2)
  (DELTA : q' \in fragment_delta_star frag q s)
  (ACCEPT : q' = frag.(frag_accept))
  : exists s1, exists s2, s = s1 ++ s2 /\ qf2 \in fragment_delta_star frag2 q s1 /\ frag.(frag_accept) \in fragment_delta_star frag frag.(frag_accept) s2.
Proof.
  revert q q' s RANGE DELTA ACCEPT; simpl in REGEX. rewrite -> REGEX1, -> REGEX2 in REGEX. inv REGEX; ii.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  induction DELTA.
  - simpl in *. exfalso; lia.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE. simpl in IN_EDGE; s!; des; subst.
    + exfalso; lia.
    + exfalso; lia.
    + exfalso; lia.
    + exists [], s; ss!.
    + pose proof (EPS1 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in *. lia.
    + pose proof (EPS2 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
      simpl in SRC_LO, SRC_HI, DST_LO, DST_HI.
      assert (RANGE_STEP : qf1 + 1 <= q1 <= qf2) by lia.
      pose proof (IHDELTA RANGE_STEP eq_refl) as (s1 & s2 & EQ & DELTA1 & DELTA2).
      exists s1, s2. splits; eauto. eapply delta_star_eps; eauto. eapply eps_step_from_edges_complete; eauto.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST); simpl in IN_EDGE; s!; des.
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in SRC. lia.
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
      assert (RANGE_STEP : qf1 + 1 <= q1 <= qf2) by lia.
      pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
      exists (edge.(char_edge_label) :: s1), s2. splits; auto.
      * rewrite EQ. simpl. now rewrite LABEL.
      * eapply delta_star_char with (q1 := q1); auto.
        rewrite <- DST. rewrite <- SRC. eapply char_step_from_edges_complete. exact IN_EDGE.
Qed.

Lemma regex2fragment_Append_delta_star_start qi qf frag e1 e2 s
  (REGEX : regex2fragment (Re.Append e1 e2) qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : exists qf1, exists frag1, exists qf2, exists frag2, regex2fragment e1 (qi + 1) = (qf1, frag1) /\ regex2fragment e2 (qf1 + 1) = (qf2, frag2) /\ frag.(frag_accept) \in fragment_delta_star frag (qi + 1) s.
Proof.
  simpl in REGEX. destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1. destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2. inv REGEX.
  exists qf1, frag1, qf2, frag2. splits; eauto.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  pose proof (fragment_delta_star_elim_with_src _ _ _ _ DELTA) as [NIL | [EPS | CHAR]].
  - des; simpl in *; exfalso; lia.
  - destruct EPS as (q1 & IN_EDGE & REST). simpl in IN_EDGE; s!; des; subst.
    + exact REST.
    + exfalso; lia.
    + exfalso; lia.
    + pose proof (EPS1 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. exfalso; lia.
    + pose proof (EPS2 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. exfalso; lia.
  - destruct CHAR as (edge & s' & EQ & SRC & IN_EDGE & REST). simpl in IN_EDGE; s!; des.
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in SRC. exfalso; lia.
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in SRC. exfalso; lia.
Qed.

Lemma regex2fragment_Append_left_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 q q' s
  (REGEX : regex2fragment (Re.Append e1 e2) qi = (qf, frag))
  (REGEX1 : regex2fragment e1 (qi + 1) = (qf1, frag1))
  (REGEX2 : regex2fragment e2 (qf1 + 1) = (qf2, frag2))
  (RANGE : qi + 1 <= q <= qf1)
  (DELTA : q' \in fragment_delta_star frag q s)
  (ACCEPT : q' = frag.(frag_accept))
  : exists s1, exists s2, s = s1 ++ s2 /\ qf1 \in fragment_delta_star frag1 q s1 /\ frag.(frag_accept) \in fragment_delta_star frag (qf1 + 1) s2.
Proof.
  revert q q' s RANGE DELTA ACCEPT. simpl in REGEX. rewrite REGEX1 in REGEX. rewrite REGEX2 in REGEX. inv REGEX. intros q q' s RANGE DELTA ACCEPT.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  induction DELTA.
  - simpl in *. exfalso; lia.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE. s!; des; subst; try now exfalso; lia.
    + exists [], s. ss!.
    + pose proof (EPS1 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]]; simpl in SRC_LO, SRC_HI, DST_LO, DST_HI.
      assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
      pose proof (IHDELTA RANGE_STEP eq_refl) as (s1 & s2 & EQ & DELTA1 & DELTA2).
      exists s1, s2. splits; eauto. eapply delta_star_eps; eauto. eapply eps_step_from_edges_complete; eauto.
    + pose proof (EPS2 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in *. exfalso; lia.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST); simpl in IN_EDGE; s!; des.
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
      assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
      pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
      exists (edge.(char_edge_label) :: s1), s2. splits; eauto.
      * rewrite EQ. simpl. now rewrite LABEL.
      * eapply delta_star_char with (q1 := q1); eauto.
        rewrite <- DST. rewrite <- SRC. eapply char_step_from_edges_complete; eauto.
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in SRC. exfalso; lia.
Qed.

Lemma regex2fragment_Append_right_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 q q' s
  (REGEX : regex2fragment (Re.Append e1 e2) qi = (qf, frag))
  (REGEX1 : regex2fragment e1 (qi + 1) = (qf1, frag1))
  (REGEX2 : regex2fragment e2 (qf1 + 1) = (qf2, frag2))
  (RANGE : qf1 + 1 <= q <= qf2)
  (DELTA : q' \in fragment_delta_star frag q s)
  (ACCEPT : q' = frag.(frag_accept))
  : exists s1, exists s2, s = s1 ++ s2 /\ qf2 \in fragment_delta_star frag2 q s1 /\ frag.(frag_accept) \in fragment_delta_star frag frag.(frag_accept) s2.
Proof.
  revert q q' s RANGE DELTA ACCEPT; simpl in REGEX. rewrite -> REGEX1, -> REGEX2 in REGEX. inv REGEX; ii.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  induction DELTA.
  - simpl in *. exfalso; lia.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE. simpl in IN_EDGE. s!; des; subst.
    + exfalso; lia.
    + exfalso; lia.
    + exists [], s. ss!.
    + pose proof (EPS1 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in *. exfalso; lia.
    + pose proof (EPS2 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
      simpl in SRC_LO, SRC_HI, DST_LO, DST_HI.
      assert (RANGE_STEP : qf1 + 1 <= q1 <= qf2) by lia.
      pose proof (IHDELTA RANGE_STEP eq_refl) as (s1 & s2 & EQ & DELTA1 & DELTA2).
      exists s1, s2. splits; eauto. eapply delta_star_eps; eauto. eapply eps_step_from_edges_complete; eauto.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    simpl in IN_EDGE. rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in SRC. lia.
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
      assert (RANGE_STEP : qf1 + 1 <= q1 <= qf2) by lia.
      pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
      exists (edge.(char_edge_label) :: s1), s2. splits; eauto.
      * rewrite EQ. simpl. now rewrite LABEL.
      * eapply delta_star_char with (q1 := q1); eauto.
        rewrite <- DST. rewrite <- SRC. eapply char_step_from_edges_complete; eauto.
Qed.

Lemma regex2fragment_Star_delta_star_start qi qf frag e s
  (REGEX : regex2fragment (Re.Star e) qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : exists qf1, exists frag1, regex2fragment e (qi + 1) = (qf1, frag1) /\ frag.(frag_accept) \in fragment_delta_star frag (qi + 1) s.
Proof.
  simpl in REGEX. destruct (regex2fragment e (qi + 1)) as [qf1 frag1] eqn: REGEX1.
  inv REGEX. exists qf1, frag1. split; eauto.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (fragment_delta_star_elim_with_src _ _ _ _ DELTA) as [NIL | [EPS | CHAR]].
  - des; simpl in *; exfalso; lia.
  - destruct EPS as (q1 & IN_EDGE & REST). simpl in IN_EDGE; s!; des; subst.
    + exact REST.
    + exfalso; lia.
    + exfalso; lia.
    + pose proof (EPS1 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. exfalso; lia.
  - destruct CHAR as (edge & s' & EQ & SRC & IN_EDGE & REST).
    pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in SRC. exfalso; lia.
Qed.

Lemma regex2fragment_accept_delta_star_stuck e qi qf frag q' s
  (REGEX : regex2fragment e qi = (qf, frag))
  (DELTA : q' \in fragment_delta_star frag qf s)
  : s = [] /\ q' = qf.
Proof.
  eapply delta_star_stuck; eauto.
  - intros q IN. pose proof (eps_step_from_edges_sound _ _ _ IN) as IN_EDGE.
    pose proof (regex2fragment_edge_src_lt _ _ _ _ REGEX) as [EPS _]. done!.
  - intros c q IN. pose proof (char_step_from_edges_sound _ _ _ _ IN) as (edge & IN_EDGE & SRC & LABEL & DST).
    pose proof (regex2fragment_edge_src_lt _ _ _ _ REGEX) as [_ CHAR]. done!.
Qed.

Lemma regex2fragment_Star_delta_star_sound_aux e
  (SOUND : forall qi, forall qf, forall frag, forall s, regex2fragment e qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e)
  : forall qi, forall qf, forall frag, forall qf1, forall frag1, forall q, forall q', forall s, regex2fragment (Re.Star e) qi = (qf, frag) -> regex2fragment e (qi + 1) = (qf1, frag1) -> qi + 1 <= q <= qf1 -> q' \in fragment_delta_star frag q s -> q' = frag.(frag_accept) ->  ((s = [] /\ q = qi + 1) \/ (exists s1, exists s2, s = s1 ++ s2 /\ qf1 \in fragment_delta_star frag1 q s1 /\ s2 \in eval_regex (Re.Star e))).
Proof.
  ii. revert q q' s H1 H2 H3. simpl in H. rewrite H0 in H. inv H. intros q q' s RANGE DELTA ACCEPT.
  pose proof (regex2fragment_bounds _ _ _ _ H0) as [START1 ACCEPT1 LT1 EPS1 CHAR1].
  pose proof (regex2fragment_edge_dst_gt_start _ _ _ _ H0) as [EPS_DST CHAR_DST].
  induction DELTA.
  - simpl in *; exfalso; lia.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE. simpl in IN_EDGE; s!; des; subst.
    + exfalso; lia.
    + set (qf1 := frag_accept frag1).
      enough (STAR_IN : s \in eval_regex (Re.Star e)).
      { right. exists [], s. ss!. }
      assert (RANGE_STEP : qi + 1 <= qi + 1 <= qf1) by lia.
      pose proof (IHDELTA RANGE_STEP eq_refl) as [[EQ _] | (s1 & s2 & EQ & DELTA1 & STAR)]; subst; simpl; [econs 1 | econs 2]; eauto.
      eapply SOUND; eauto. rewrite START1; eauto.
    + set (qf1 := frag_accept frag1).
      assert (REGEX_STAR : regex2fragment (Re.Star e) qi = (frag_accept frag1 + 1, mkFragment qi (qf1 + 1) ((qi, qi + 1) :: (qf1, qi + 1) :: (qi + 1, qf1 + 1) :: frag1.(frag_eps_edges)) frag1.(frag_char_edges))) by now simpl; rewrite H0.
      pose proof (regex2fragment_accept_delta_star_stuck (Re.Star e) qi (qf1 + 1) (mkFragment qi (qf1 + 1) ((qi, qi + 1) :: (qf1, qi + 1) :: (qi + 1, qf1 + 1) :: frag1.(frag_eps_edges)) frag1.(frag_char_edges)) _ s REGEX_STAR REST) as [EQ _]; subst s.
      left; ss!.
    + set (qf1 := frag_accept frag1).
      pose proof (EPS1 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]]; simpl in SRC_LO, SRC_HI, DST_LO, DST_HI.
      assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
      pose proof (IHDELTA RANGE_STEP eq_refl) as [[EQ EQ'] | (s1 & s2 & EQ & DELTA1 & STAR)]; subst.
      * pose proof (EPS_DST _ _ IN_EDGE); done!.
      * right. exists s1, s2. splits; eauto.
        eapply delta_star_eps; eauto. eapply eps_step_from_edges_complete; eauto.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
    assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
    pose proof (IHDELTA RANGE_STEP ACCEPT) as [[EQ EQ'] | (s1 & s2 & EQ & DELTA1 & STAR)]; subst.
    + pose proof (CHAR_DST _ IN_EDGE); done!.
    + right. exists (edge.(char_edge_label) :: s1), s2. splits; eauto. econs 3; eauto.
Qed.

Theorem regex2fragment_sound_Null qi qf frag s
  (REGEX : regex2fragment Re.Null qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : s \in eval_regex Re.Null.
Proof.
  simpl in REGEX. inv REGEX. pose proof (fragment_delta_star_elim _ _ _ _ DELTA) as [NIL | [EPS | CHAR]].
  - des; simpl in *; exfalso; lia.
  - des; contradiction.
  - des; contradiction.
Qed.

Theorem regex2fragment_sound_Empty qi qf frag s
  (REGEX : regex2fragment Re.Empty qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : s \in eval_regex Re.Empty.
Proof.
  simpl in REGEX. inv REGEX. pose proof (fragment_delta_star_elim _ _ _ _ DELTA) as [NIL | [EPS | CHAR]].
  - des; simpl in *; exfalso; lia.
  - destruct EPS as (q1 & IN_EDGE & REST). simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | []]. inv EQ.
    pose proof (regex2fragment_accept_delta_star_stuck Re.Empty qi (qi + 1) (mkFragment qi (qi + 1) [(qi, qi + 1)] []) (qi + 1) s eq_refl REST) as [EQ ?]; subst s.
    ss!.
  - des; contradiction.
Qed.

Theorem regex2fragment_sound_Char c qi qf frag s
  (REGEX : regex2fragment (Re.Char c) qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : s \in eval_regex (Re.Char c).
Proof.
  simpl in REGEX. inv REGEX. pose proof (fragment_delta_star_elim _ _ _ _ DELTA) as [NIL | [EPS | CHAR]].
  - des; simpl in *; exfalso; lia.
  - des; contradiction.
  - destruct CHAR as (edge & s' & EQ & IN_EDGE & REST). simpl in IN_EDGE.
    destruct IN_EDGE as [EDGE_EQ | []]. subst edge. simpl in EQ. subst s.
    pose proof (regex2fragment_accept_delta_star_stuck (Re.Char c) qi (qi + 1) (mkFragment qi (qi + 1) [] [mkCharEdge qi c (qi + 1)]) (qi + 1) s' eq_refl REST) as [EQ ?]; subst s'.
    ss!.
Qed.

Theorem regex2fragment_sound_Union e1 e2
  (SOUND1 : forall qi, forall qf, forall frag, forall s, regex2fragment e1 qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e1)
  (SOUND2 : forall qi, forall qf, forall frag, forall s, regex2fragment e2 qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e2)
  : forall qi, forall qf, forall frag, forall s, regex2fragment (Re.Union e1 e2) qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex (Re.Union e1 e2).
Proof.
  ii. pose proof (regex2fragment_start_accept _ _ _ _ H) as [_ ACCEPT]. pose proof (regex2fragment_Union_delta_star_start qi qf frag e1 e2 s H H0) as (qf1 & frag1 & qf2 & frag2 & REGEX1 & REGEX2 & [DELTA1 | DELTA2]).
  - pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [START1 ACCEPT1 LT1 _ _].
    assert (RANGE1 : qi + 1 <= qi + 1 <= qf1) by lia.
    pose proof (regex2fragment_Union_left_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 (qi + 1) frag.(frag_accept) s H REGEX1 REGEX2 RANGE1 DELTA1 eq_refl) as (s1 & s2 & EQ & DELTA1' & DELTA2').
    rewrite ACCEPT in DELTA2'.
    pose proof (regex2fragment_accept_delta_star_stuck (Re.Union e1 e2) qi qf frag qf s2 H DELTA2') as [EQ2 _]; subst s2.
    rewrite app_nil_r in EQ; subst s. s!. left. eapply SOUND1; done!.
  - pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [START2 ACCEPT2 LT2 _ _].
    assert (RANGE2 : qf1 + 1 <= qf1 + 1 <= qf2) by lia.
    pose proof (regex2fragment_Union_right_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 (qf1 + 1) frag.(frag_accept) s H REGEX1 REGEX2 RANGE2 DELTA2 eq_refl) as (s1 & s2 & EQ & DELTA1' & DELTA2').
    rewrite ACCEPT in DELTA2'.
    pose proof (regex2fragment_accept_delta_star_stuck (Re.Union e1 e2) qi qf frag qf s2 H DELTA2') as [EQ2 _]; subst s2.
    rewrite app_nil_r in EQ; subst s. s!. right. eapply SOUND2; done!.
Qed.

Theorem regex2fragment_sound_Append e1 e2
  (SOUND1 : forall qi, forall qf, forall frag, forall s, regex2fragment e1 qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e1)
  (SOUND2 : forall qi, forall qf, forall frag, forall s, regex2fragment e2 qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e2)
  : forall qi, forall qf, forall frag, forall s, regex2fragment (Re.Append e1 e2) qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex (Re.Append e1 e2).
Proof.
  ii. pose proof (regex2fragment_start_accept _ _ _ _ H) as [_ ACCEPT].
  pose proof (regex2fragment_Append_delta_star_start qi qf frag e1 e2 s H H0) as (qf1 & frag1 & qf2 & frag2 & REGEX1 & REGEX2 & DELTA).
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [START1 ACCEPT1 LT1 _ _].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [START2 ACCEPT2 LT2 _ _].
  assert (RANGE1 : qi + 1 <= qi + 1 <= qf1) by lia.
  assert (RANGE2 : qf1 + 1 <= qf1 + 1 <= qf2) by lia.
  pose proof (regex2fragment_Append_left_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 (qi + 1) frag.(frag_accept) s H REGEX1 REGEX2 RANGE1 DELTA eq_refl) as (s1 & s2 & EQ & DELTA1 & DELTA2).
  pose proof (regex2fragment_Append_right_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 (qf1 + 1) frag.(frag_accept) s2 H REGEX1 REGEX2 RANGE2 DELTA2 eq_refl) as (s2' & s3 & EQ' & DELTA2' & DELTA3).
  rewrite ACCEPT in DELTA3.
  pose proof (regex2fragment_accept_delta_star_stuck (Re.Append e1 e2) qi qf frag qf s3 H DELTA3) as [EQ3 _]; subst s3.
  rewrite app_nil_r in EQ'; subst s2 s; simpl.
  exists s1; split.
  { eapply SOUND1; done!. }
  exists s2'. split.
  { eapply SOUND2; done!. }
  red; reflexivity.
Qed.

Theorem regex2fragment_sound_Star e1
  (SOUND : forall qi, forall qf, forall frag, forall s, regex2fragment e1 qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e1)
  : forall qi, forall qf, forall frag, forall s, regex2fragment (Re.Star e1) qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex (Re.Star e1).
Proof.
  ii. pose proof (regex2fragment_Star_delta_star_start qi qf frag e1 s H H0) as (qf1 & frag1 & REGEX & DELTA).
  pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [START ACCEPT LT _ _].
  assert (RANGE : qi + 1 <= qi + 1 <= qf1) by lia.
  pose proof (regex2fragment_Star_delta_star_sound_aux e1 SOUND qi qf frag qf1 frag1 (qi + 1) frag.(frag_accept) s H REGEX RANGE DELTA eq_refl) as [[EQ _] | (s1 & s2 & EQ & DELTA1 & STAR)]; subst s; simpl; [econs 1 | econs 2].
  - eapply SOUND; done!.
  - exact STAR.
Qed.

Corollary regex2fragment_sound (e : regex ascii)
  : forall qi, forall qf, forall frag, forall s, regex2fragment e qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e.
Proof.
  induction e.
  - now eapply regex2fragment_sound_Null.
  - now eapply regex2fragment_sound_Empty.
  - now eapply regex2fragment_sound_Char.
  - now eapply regex2fragment_sound_Union.
  - now eapply regex2fragment_sound_Append.
  - now eapply regex2fragment_sound_Star.
Qed.

Lemma fragments_delta_star_start_to_fragment qi rules qmax frags rule frag qi_rule qf s
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) qi_rule = (qf, frag))
  (qi_POS : 0 < qi)
  (DELTA : frag.(frag_accept) \in fragments_delta_star frags 0 s)
  : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s.
Proof.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [START ACCEPT LT _ _].
  pose proof (delta_star_elim _ _ 0 frag.(frag_accept) s DELTA) as [NIL | [EPS | CHAR]].
  - des; subst.
    pose proof (rules2fragments_start_ge _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX); done!.
  - destruct EPS as (q1 & STEP & REST).
    pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE.
    pose proof (fragment_eps_edges_start_sound _ _ _ _ _ FRAGS qi_POS IN_EDGE) as (rule' & frag' & qi_rule' & qf' & IN_FRAG' & REGEX' & START_EDGE); subst q1.
    pose proof (regex2fragment_bounds _ _ _ _ REGEX') as [START' ACCEPT' LT' _ _].
    assert (RANGE : qi_rule <= frag.(frag_accept) <= qf) by lia.
    assert (RANGE' : qi_rule' <= frag.(frag_accept) <= qf').
    { eapply delta_star_fragment_range with (qi := qi) (rules := rules) (qmax := qmax) (frags := frags) (rule := rule') (frag := frag') (q := frag'.(frag_start)) (s := s); done!. }
    pose proof (rules2fragments_ranges_disjoint _ _ _ _ _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG IN_FRAG' REGEX REGEX' RANGE RANGE') as EQ.
    eapply delta_star_global_to_fragment; done!.
  - destruct CHAR as (c & s' & q1 & EQ & STEP & REST).
    pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    pose proof (fragment_char_edges_owner _ _ _ _ _ FRAGS IN_EDGE) as (rule' & frag' & qi_rule' & qf' & IN_FRAG' & REGEX' & BOUNDS' & LE_START & LT_END & RANGE' & IN_EDGE').
    done!.
Qed.

Lemma TaggedENFA_FRAGMENTS_sound qi rules qmax frags s tag
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (qi_POS : 0 < qi)
  (ACCEPTS : accepts (fragments2TaggedENFA qmax frags) s tag)
  : exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex).
Proof.
  destruct ACCEPTS as (q & DELTA & ACCEPT). simpl in DELTA, ACCEPT.
  pose proof (fragment_accept_states_sound _ _ _ ACCEPT) as (rule & frag & IN_FRAG & ACCEPT_EQ & TOKEN_EQ); subst q tag.
  pose proof (rules2fragments_bounds _ _ _ _ FRAGS) as [_ BOUND].
  pose proof (BOUND _ _ IN_FRAG) as (qi_rule & qf & REGEX & _ & _ & _).
  exists rule. split.
  - eapply rules2fragments_sound; eauto.
  - split; eauto. eapply regex2fragment_sound; eauto. eapply fragments_delta_star_start_to_fragment; eauto.
Qed.

Theorem mkUnitedTaggedENFA_sound (M : TaggedENFA.t)
  (COMPILE : fmap mkUnitedTaggedENFA Rule.compileds = inr M)
  : exists rules, Rule.compileds = inr rules /\ ⟪ ACCEPT : forall s, forall tag, accepts M s tag -> (exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex)) ⟫.
Proof.
  pose proof (mkUnitedTaggedENFA_spec M COMPILE) as (rules & qmax & frags & COMPILED & FRAGMENTS_OF).
  destruct COMPILED as [COMPILED_RULES COMPILED_ENFA COMPILED_FRAGS].
  exists rules. split; [exact COMPILED_RULES | unnw]. intros s tag ACCEPTS.
  assert (ENFA_EQ : M = fragments2TaggedENFA qmax frags).
  { eapply TaggedENFA_COMPILED_as_fragments. econs; eauto. }
  rewrite ENFA_EQ in ACCEPTS. eapply TaggedENFA_FRAGMENTS_sound; eauto.
Qed.

Theorem mkUnitedTaggedENFA_complete (M : TaggedENFA.t)
  (COMPILE : fmap mkUnitedTaggedENFA Rule.compileds = inr M)
  : exists rules, Rule.compileds = inr rules /\ ⟪ ACCEPT : forall s, forall tag, (exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex)) -> accepts M s tag ⟫.
Proof.
  pose proof (mkUnitedTaggedENFA_spec M COMPILE) as (rules & qmax & frags & COMPILED & FRAGMENTS_OF).
  destruct COMPILED as [COMPILED_RULES COMPILED_ENFA COMPILED_FRAGS].
  exists rules. split; [exact COMPILED_RULES | unnw]. intros s tag (rule & IN_RULE & TOKEN & IN_REGEX); subst tag.
  pose proof (rules2fragments_complete 1 rules qmax frags rule COMPILED_FRAGS IN_RULE) as (qi & qf & frag & REGEX2FRAGMENT & IN_FRAGS).
  pose proof (FRAGMENTS_OF rule frag IN_FRAGS) as FRAGMENTS.
  pose proof (TaggedENFA_FRAGMENTS_complete qmax frags rule qi qf frag s REGEX2FRAGMENT FRAGMENTS IN_REGEX) as ACCEPTS.
  rewrite TaggedENFA_COMPILED_as_fragments with (M := M) (rules := rules) (qmax := qmax) (frags := frags); eauto.
  exact (TaggedENFA_COMPILED_intro M rules qmax frags COMPILED_RULES COMPILED_ENFA COMPILED_FRAGS).
Qed.

End Thompson's_construction.

Module Thompson.

Definition accepts_global (frags : list (Rule.t * fragment)) (frag : fragment) (s : Input.t) : Prop :=
  frag.(frag_accept) \in fragments_delta_star frags frag.(frag_start) s.

Definition accepts_local (frag : fragment) (s : Input.t) : Prop :=
  frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s.

Theorem regex2fragment_invariant (e : regex ascii) (qi : nat) (qf : nat) (frag : fragment)
  (REGEX : regex2fragment e qi = (qf, frag))
  : FRAGMENT_BOUNDS qi qf frag.
Proof.
  now eapply regex2fragment_bounds with (e := e).
Qed.

Theorem regex2fragment_start_accept (e : regex ascii) (qi : nat) (qf : nat) (frag : fragment)
  (REGEX : regex2fragment e qi = (qf, frag))
  : frag.(frag_start) = qi /\ frag.(frag_accept) = qf.
Proof.
  now eapply TaggedENFA.regex2fragment_start_accept with (e := e).
Qed.

Variant REGEX2FRAGMENT_CORRECT (frags : list (Rule.t * fragment)) (rule : Rule.t) (qi : nat) (qf : nat) (frag : fragment) : Prop :=
  | regex2fragment_correct_intro
    (regex2fragment_local_sound : forall s : Input.t, frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex rule.(Rule.regex))
    (regex2fragment_global_complete : forall s : Input.t, s \in eval_regex rule.(Rule.regex) -> frag.(frag_accept) \in fragments_delta_star frags frag.(frag_start) s).

Theorem regex2fragment_correct frags rule qi qf frag
  (REGEX : regex2fragment rule.(Rule.regex) qi = (qf, frag))
  (FRAGMENTS : TaggedENFA_FRAGMENTS frags rule frag)
  : REGEX2FRAGMENT_CORRECT frags rule qi qf frag.
Proof.
  constructor.
  - intros s ACCEPT. eapply regex2fragment_sound; eauto.
  - intros s ACCEPT. eapply regex2fragment_complete; eauto.
Qed.

Theorem mkUnitedTaggedENFA_correct (M : TaggedENFA.t)
  (COMPILE : fmap mkUnitedTaggedENFA Rule.compileds = inr M)
  : exists rules, Rule.compileds = inr rules /\ ⟪ CORRECT : forall s, forall tag, accepts M s tag <-> exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex) ⟫.
Proof.
  pose proof (TaggedENFA.mkUnitedTaggedENFA_sound M COMPILE) as (rules & COMPILED & SOUND); unnw.
  pose proof (TaggedENFA.mkUnitedTaggedENFA_complete M COMPILE) as (rules' & COMPILED' & COMPLETE); unnw.
  rewrite COMPILED in COMPILED'. inv COMPILED'. exists rules'; ss!.
Qed.

End Thompson.

End TaggedENFA.

End MkLGS.
