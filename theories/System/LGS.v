Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Strings.String.
Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Monad.
Require Import PnV.Data.FiniteSet.
Require Import PnV.System.Regex.

Import DoNotations.

#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "=~=" := (is_similar_to (Similarity := Re.in_regex eq)) : type_scope.
#[local] Infix "∈" := L.In.

Definition all_bools : list bool :=
  [false; true].

Definition all_asciis : list ascii := do
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

Lemma all_bools_complete (b : bool)
  : b ∈ all_bools.
Proof.
  destruct b; simpl; tauto.
Qed.

Lemma all_asciis_complete (c : ascii)
  : c ∈ all_asciis.
Proof.
  destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
  unfold all_asciis.
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

Module Type TOKEN_SPEC.

Parameter t : Set.

Parameter t_hasEqDec : hasEqDec@{Set} TOKEN_SPEC.t.

Parameter rules : list (TOKEN_SPEC.t * regex ascii).

End TOKEN_SPEC.

Module LGS (Token : TOKEN_SPEC).

#[local] Existing Instance Token.t_hasEqDec.

Module Error.

Inductive t : Set :=
  | EmptyTokenRule (idx : nat)
  | NoMatch (rest : list ascii)
  | InternalInvariantBroken.

End Error.

#[universes(polymorphic=yes)]
Definition ErrM@{u} (A : Type@{u}) : Type@{u} :=
  Error.t + A.

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
    + rewrite andb_true_iff in H. destruct H as (H1 & H2).
      change (@nil ascii) with ((@nil ascii) ++ (@nil ascii)).
      eauto with *.
    + econs.
  - enough (CLAIM : forall s, forall e0, s =~= e0 -> s = [] -> nullable e0 = true).
    { i. eapply CLAIM; eauto. }
    intros s e0 H_IN. induction H_IN; simpl; i; subst; try congruence; eauto.
    + rewrite orb_true_iff. left. eauto.
    + rewrite orb_true_iff. right. eauto.
    + pose proof (app_eq_nil _ _ H) as (EQ1 & EQ2). subst s1 s2. ss!.
Qed.

Theorem nullable_spec (e : regex ascii)
  : nullable e = true <-> [] \in eval_regex e.
Proof.
  rewrite eval_regex_good. eapply nullable_similar_spec.
Qed.

Corollary nullable_false_spec (e : regex ascii)
  : nullable e = false <-> (~ [] \in eval_regex e).
Proof.
  destruct (nullable e) eqn: EQ; split; intros H.
  - congruence.
  - contradiction H. rewrite <- nullable_spec. exact EQ.
  - intros IN. rewrite <- nullable_spec in IN. congruence.
  - reflexivity.
Qed.

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
  }.

#[global] Existing Instance state_hasEqDec.

Definition accept_state (M : TaggedENFA.t) : Set :=
  (M.(state) * Token.t).

Variant okay (M : TaggedENFA.t) : Prop :=
  | okay_intro
    (start_okay : M.(start_state) ∈ M.(states))
    (accept_states_okay : forall q, forall tag, (q, tag) ∈ M.(accept_states) -> q ∈ M.(states))
    (eps_step_okay : forall q, forall q', q ∈ M.(states) -> q' ∈ M.(eps_step) q -> q' ∈ M.(states))
    (char_step_okay : forall q, forall q', forall c, q ∈ M.(states) -> q' ∈ M.(char_step) q c -> q' ∈ M.(states)).

Section BASICS.

Variable M : TaggedENFA.t.

#[local] Notation Q := M.(state).

Inductive delta_star (q : Q) : Input.t -> ensemble Q :=
  | delta_star_nil
    : q \in delta_star q []
  | delta_star_eps q1 q2 s
    (STEP : q1 ∈ M.(eps_step) q)
    (REST : q2 \in delta_star q1 s)
    : q2 \in delta_star q s
  | delta_star_char q1 q2 c s
    (STEP : q1 ∈ M.(char_step) q c)
    (REST : q2 \in delta_star q1 s)
    : q2 \in delta_star q (c :: s).

#[local] Hint Constructors delta_star : core.

Inductive eclosure (q : Q) : ensemble Q :=
  | eclosure_refl
    : q \in eclosure q
  | eclosure_step q1 q2
    (STEP : q1 ∈ M.(eps_step) q)
    (REST : q2 \in eclosure q1)
    : q2 \in eclosure q.

#[local] Hint Constructors eclosure : core.

Definition accepts (s : Input.t) (tag : Token.t) : Prop :=
  exists q, q \in delta_star M.(start_state) s /\ (q, tag) ∈ M.(accept_states).

Definition accepted_tags (s : Input.t) : ensemble Token.t :=
  fun tag => accepts s tag.

Lemma delta_star_app (q1 : Q) (q2 : Q) (q3 : Q) (s1 : Input.t) (s2 : Input.t)
  (H1_delta_star : q2 \in delta_star q1 s1)
  (H2_delta_star : q3 \in delta_star q2 s2)
  : q3 \in delta_star q1 (s1 ++ s2).
Proof.
  induction H1_delta_star as [q | q q1' q2' s STEP REST IH | q q1' q2' c s STEP REST IH]; simpl; eauto with *.
Qed.

Lemma eclosure_trans (q1 : Q) (q2 : Q) (q3 : Q)
  (H1_eclosure : q2 \in eclosure q1)
  (H2_eclosure : q3 \in eclosure q2)
  : q3 \in eclosure q1.
Proof.
  induction H1_eclosure as [q | q q1' q2' STEP REST IH]; simpl; eauto with *.
Qed.

Lemma delta_star_iff_eclosure (q : Q) (q' : Q)
  : q' \in delta_star q [] <-> q' \in eclosure q.
Proof.
  split; [intros H_delta_star | intros H_eclosure].
  - remember (@nil ascii) as s eqn: EQ; induction H_delta_star as [q | q q1' q2' s STEP REST IH | q q1' q2' c s STEP REST IH]; inv EQ; simpl; eauto with *.
  - induction H_eclosure as [q | q q1' q2' STEP REST IH]; simpl; eauto with *.
Qed.

Lemma eclosure_okay (q1 : Q) (q2 : Q)
  (OKAY : TaggedENFA.okay M)
  (IN : q1 ∈ M.(states))
  (H_eclosure : q2 \in eclosure q1)
  : q2 ∈ M.(states).
Proof.
  destruct OKAY as [_ _ ? _]; induction H_eclosure as [q | q q1' q2' STEP REST IH]; simpl; eauto with *.
Qed.

Lemma delta_star_okay (q1 : Q) (q2 : Q) (s : Input.t)
  (OKAY : TaggedENFA.okay M)
  (IN : q1 ∈ M.(states))
  (H_delta_star : q2 \in delta_star q1 s)
  : q2 ∈ M.(states).
Proof.
  destruct OKAY as [_ _ ? ?]; induction H_delta_star as [q | q q1' q2' s STEP REST IH | q q1' q2' c s STEP REST IH]; simpl; eauto with *.
Qed.

Lemma delta_star_elim (q1 : Q) (q3 : Q) (s : Input.t)
  (H_delta_star : q3 \in delta_star q1 s)
  : ⟪ DELTA_STAR_NIL : s = [] /\ q3 = q1 ⟫ \/ ⟪ DELTA_STAR_EPS : exists q2, q2 ∈ M.(eps_step) q1 /\ q3 \in delta_star q2 s ⟫ \/ ⟪ DELTA_STAR_CHAR : exists c, exists s', exists q2, s = c :: s' /\ q2 ∈ M.(char_step) q1 c /\ q3 \in delta_star q2 s' ⟫.
Proof.
  unnw; destruct H_delta_star as [ | q1' q2' s' STEP REST | q1' q2' c s' STEP REST]; [left | right; left | right; right]; done!.
Qed.

Lemma delta_star_stuck (q1 : Q) (q2 : Q) (s : Input.t)
  (NO_EPS : forall q, q ∈ M.(eps_step) q1 -> False)
  (NO_CHAR : forall c, forall q, q ∈ M.(char_step) q1 c -> False)
  (H_delta_star : q2 \in delta_star q1 s)
  : s = [] /\ q2 = q1.
Proof.
  inv H_delta_star; ss!.
Qed.

End BASICS.

End TaggedENFA.

End LGS.
