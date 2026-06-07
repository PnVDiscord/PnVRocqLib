Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Strings.String.
Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Monad.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Data.Graph.
Require Import PnV.System.Regex.

Import DoNotations.
Import DigraphFixedpoint.

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
  unfold all_asciis. destruct c as [b0 b1 b2 b3 b4 b5 b6 b7].
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

Lemma list_bind_sound {A : Type} {B : Type} (xs : list A) (k : A -> list B) (y : B)
  (IN : y ∈ (xs >>= k))
  : exists x, x ∈ xs /\ y ∈ k x.
Proof.
  induction xs as [ | x xs IH]; simpl in IN; [contradiction | ].
  rewrite in_app_iff in IN. destruct IN as [IN | IN].
  - exists x. split; [left; reflexivity | exact IN].
  - pose proof (IH IN) as (x' & IN_XS & IN_K).
    exists x'. split; [right; exact IN_XS | exact IN_K].
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

Module BuildError.

Inductive t : Set :=
  | NullableTokenRule (idx : nat).

End BuildError.

#[universes(polymorphic=yes)]
Definition BuildErrorM@{u | } (A : Type@{u}) : Type@{u} :=
  BuildError.t + A.

#[universes(polymorphic=yes)]
Instance ErrM_isMonad@{u} : isMonad@{u u} BuildErrorM@{u} :=
  { pure {A : Type@{u}} (x : A) := inr x
  ; bind {A : Type@{u}} {B : Type@{u}} (m : BuildErrorM A) (k : A -> BuildErrorM B) := B.either (@inl _ _) k m
  }.

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

Corollary nullable_false_iff (e : regex ascii)
  : nullable e = false <-> (~ [] \in eval_regex e).
Proof.
  destruct (nullable e) eqn: EQ; split; intros H.
  - congruence.
  - contradiction H. rewrite <- nullable_true_iff. exact EQ.
  - intros IN. rewrite <- nullable_true_iff in IN. congruence.
  - reflexivity.
Qed.

Module Rule.

#[projections(primitive)]
Record t : Set :=
  mk
  { index : nat
  ; token : Token.t
  ; regex : Re.t ascii
  }.

#[global]
Instance Rule_hasEqDec
  : hasEqDec@{Set} Rule.t.
Proof.
  red. decide equality.
  - eapply eq_dec.
  - eapply eq_dec.
  - eapply eq_dec.
Defined.

Definition compile_rule (rule : Rule.t) : BuildErrorM Rule.t :=
  if nullable rule.(Rule.regex) then
    inl (BuildError.NullableTokenRule rule.(Rule.index))
  else
    pure rule.

Theorem compile_rule_spec (rule : Rule.t) (compiled_rule : Rule.t)
  (COMPILE : compile_rule rule = inr compiled_rule)
  : forall s, s \in eval_regex rule.(Rule.regex) <-> s \in eval_regex compiled_rule.(Rule.regex).
Proof.
  intros s; split; intros ACCEPTS; unfold compile_rule in COMPILE; now destruct (nullable rule.(Rule.regex)) eqn: NULLABLE; inv COMPILE.
Qed.

Lemma compile_rule_not_match_empty (rule : Rule.t) (compiled_rule : Rule.t)
  (COMPILE : compile_rule rule = inr compiled_rule)
  : ~ ([] \in eval_regex compiled_rule.(Rule.regex)).
Proof.
  unfold compile_rule in COMPILE; destruct (nullable rule.(Rule.regex)) eqn: NULLABLE; inv COMPILE; now rewrite <- nullable_false_iff.
Qed.

Fixpoint compile_rules (rules : list Rule.t) {struct rules} : BuildErrorM (list Rule.t) :=
  match rules with
  | [] => pure (@nil Rule.t)
  | rule :: rules => liftM2 (@cons Rule.t) (compile_rule rule) (compile_rules rules)
  end.

Definition raws : list Rule.t :=
  L.mapi_from 1 (fun index => fun '(token, regex) => Rule.mk index token regex) Token.rules.

Definition compileds : BuildErrorM (list Rule.t) :=
  compile_rules raws.

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
  }.

#[global] Existing Instance state_hasEqDec.

Definition accept_state (M : TaggedENFA.t) : Set :=
  M.(TaggedENFA.state) * Token.t.

Variant okay (M : TaggedENFA.t) : Prop :=
  | okay_intro
    (start_okay : M.(TaggedENFA.start_state) ∈ M.(TaggedENFA.states))
    (accept_states_okay : forall q, forall tag, (q, tag) ∈ M.(TaggedENFA.accept_states) -> q ∈ M.(TaggedENFA.states))
    (eps_step_okay : forall q, forall q', q ∈ M.(TaggedENFA.states) -> q' ∈ M.(TaggedENFA.eps_step) q -> q' ∈ M.(TaggedENFA.states))
    (char_step_okay : forall q, forall q', forall c, q ∈ M.(TaggedENFA.states) -> q' ∈ M.(TaggedENFA.char_step) q c -> q' ∈ M.(TaggedENFA.states)).

Section DELTA_STAR.

Context {Q : Type}.

Variable eps_step : Q -> list Q.

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

#[global] Arguments delta_star_app {Q} {eps_step} {char_step} q1 q2 q3 s1 s2 _ _.
#[global] Arguments eclosure_trans {Q} {eps_step} q1 q2 q3 _ _.
#[global] Arguments delta_star_iff_eclosure {Q} {eps_step} {char_step} q q'.
#[global] Arguments delta_star_elim {Q} {eps_step} {char_step} q1 q3 s _.
#[global] Arguments delta_star_stuck {Q} {eps_step} {char_step} q1 q2 s _ _ _.

Section BASICS.

Variable M : TaggedENFA.t.

#[local] Notation Q := M.(TaggedENFA.state).
#[local] Notation M_delta_star := (delta_star M.(TaggedENFA.eps_step) M.(TaggedENFA.char_step)).
#[local] Notation M_eclosure := (eclosure M.(TaggedENFA.eps_step)).

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
  induction edges as [ | [src dst] edges IH]; simpl in IN |- *.
  - contradiction.
  - destruct IN as [EQ | IN].
    + inv EQ. destruct (eq_dec q q) as [_ | NE]; [left; reflexivity | contradiction NE; reflexivity].
    + destruct (eq_dec q src) as [_ | _]; simpl; eauto.
Qed.

Lemma eps_step_from_edges_sound (q : nat) (q' : nat) (edges : list (nat * nat))
  (IN : q' ∈ eps_step_from_edges q edges)
  : (q, q') ∈ edges.
Proof.
  induction edges as [ | [src dst] edges IH]; simpl in IN |- *; ss!.
  destruct (eq_dec q src) as [EQ | NE]; simpl in IN; done!.
Qed.

Lemma char_step_from_edges_complete (edge : char_edge) (edges : list char_edge)
  (IN : edge ∈ edges)
  : edge.(char_edge_dst) ∈ char_step_from_edges edge.(char_edge_src) edge.(char_edge_label) edges.
Proof.
  induction edges as [ | edge' edges IH]; simpl in IN |- *.
  - contradiction.
  - destruct IN as [EQ | IN].
    + subst edge'. destruct (eq_dec edge.(char_edge_src) edge.(char_edge_src)) as [_ | NE]; [ | contradiction NE; reflexivity].
      destruct (eq_dec edge.(char_edge_label) edge.(char_edge_label)) as [_ | NE]; [left; reflexivity | contradiction NE; reflexivity].
    + destruct (eq_dec edge.(char_edge_src) edge'.(char_edge_src)) as [_ | _]; destruct (eq_dec edge.(char_edge_label) edge'.(char_edge_label)) as [_ | _]; simpl; eauto.
Qed.

Lemma char_step_from_edges_sound (q : nat) (q' : nat) (c : ascii) (edges : list char_edge)
  (IN : q' ∈ char_step_from_edges q c edges)
  : exists edge, edge ∈ edges /\ edge.(char_edge_src) = q /\ edge.(char_edge_label) = c /\ edge.(char_edge_dst) = q'.
Proof.
  induction edges as [ | edge edges IH]; simpl in IN |- *; try tauto.
  destruct (eq_dec q edge.(char_edge_src)) as [SRC | SRC_NE].
  - destruct (eq_dec c edge.(char_edge_label)) as [LABEL | LABEL_NE]; simpl in IN.
    + destruct IN as [DST | IN].
      * exists edge. subst q'. repeat split; eauto.
      * pose proof (IH IN) as (edge' & IN_EDGE & SRC' & LABEL' & DST').
        exists edge'. repeat split; eauto.
    + pose proof (IH IN) as (edge' & IN_EDGE & SRC' & LABEL' & DST').
      exists edge'. repeat split; eauto.
  - pose proof (IH IN) as (edge' & IN_EDGE & SRC' & LABEL' & DST').
    exists edge'. repeat split; eauto.
Qed.

Lemma fragment_eps_edges_start_complete (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment)
  (IN : (rule, frag) ∈ frags)
  : (0, frag.(frag_start)) ∈ fragment_eps_edges frags.
Proof.
  induction frags as [ | [rule' frag'] frags IH]; simpl in IN |- *; eauto.
  destruct IN as [EQ | IN]; [inv EQ; left; reflexivity | right; rewrite in_app_iff; right; eauto].
Qed.

Lemma fragment_eps_edges_complete (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment) (q : nat) (q' : nat)
  (IN_FRAG : (rule, frag) ∈ frags)
  (IN_EDGE : (q, q') ∈ frag.(frag_eps_edges))
  : (q, q') ∈ fragment_eps_edges frags.
Proof.
  induction frags as [ | [rule' frag'] frags IH]; simpl in IN_FRAG |- *; eauto.
  destruct IN_FRAG as [EQ | IN_FRAG].
  - inv EQ. right. rewrite in_app_iff. left. exact IN_EDGE.
  - right. rewrite in_app_iff. right. eauto.
Qed.

Lemma fragment_char_edges_complete (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment) (edge : char_edge)
  (IN_FRAG : (rule, frag) ∈ frags)
  (IN_EDGE : edge ∈ frag.(frag_char_edges))
  : edge ∈ fragment_char_edges frags.
Proof.
  induction frags as [ | [rule' frag'] frags IH]; simpl in IN_FRAG |- *; eauto.
  destruct IN_FRAG as [EQ | IN_FRAG].
  - inv EQ. rewrite in_app_iff. left. exact IN_EDGE.
  - rewrite in_app_iff. right. eauto.
Qed.

Lemma fragment_accept_states_complete (frags : list (Rule.t * fragment)) (rule : Rule.t) (frag : fragment)
  (IN_FRAG : (rule, frag) ∈ frags)
  : (frag.(frag_accept), rule.(Rule.token)) ∈ fragment_accept_states frags.
Proof.
  unfold fragment_accept_states. rewrite L.in_map_iff.
  exists (rule, frag). split; [reflexivity | exact IN_FRAG].
Qed.

Lemma fragment_accept_states_sound (frags : list (Rule.t * fragment)) q tag
  (IN : (q, tag) ∈ fragment_accept_states frags)
  : exists rule, exists frag, (rule, frag) ∈ frags /\ q = frag.(frag_accept) /\ tag = rule.(Rule.token).
Proof.
  unfold fragment_accept_states in IN. rewrite L.in_map_iff in IN.
  destruct IN as ([rule frag] & EQ & IN_FRAG). inv EQ.
  exists rule, frag. eauto.
Qed.

Variant TaggedENFA_COMPILED (M : TaggedENFA.t) rules qmax frags : Prop :=
  | TaggedENFA_COMPILED_intro 
    (COMPILED_RULES : Rule.compileds = inr rules)
    (COMPILED_ENFA : M = mkUnitedTaggedENFA rules)
    (COMPILED_FRAGS : rules2fragments 1 rules = (qmax, frags)).

Variant TaggedENFA_FRAGMENTS (frags : list (Rule.t * fragment)) rule frag : Prop :=
  | TaggedENFA_FRAGMENTS_intro
    (IN1 : frag.(frag_start) ∈ eps_step_from_edges 0 (fragment_eps_edges frags))
    (IN2 : (frag.(frag_accept), rule.(Rule.token)) ∈ fragment_accept_states frags)
    (EPS : forall q, forall q', (q, q') ∈ frag.(frag_eps_edges) -> q' ∈ eps_step_from_edges q (fragment_eps_edges frags))
    (CHAR : forall edge, edge ∈ frag.(frag_char_edges) -> edge.(char_edge_dst) ∈ char_step_from_edges edge.(char_edge_src) edge.(char_edge_label) (fragment_char_edges frags)).

Theorem mkUnitedTaggedENFA_spec (M : TaggedENFA.t)
  (COMPILE : fmap mkUnitedTaggedENFA Rule.compileds = inr M)
  : exists rules, exists qmax, exists frags, TaggedENFA_COMPILED M rules qmax frags /\ (forall rule, forall frag, (rule, frag) ∈ frags -> TaggedENFA_FRAGMENTS frags rule frag).
Proof.
  unfold fmap, mkFunctorFromMonad in COMPILE. simpl in COMPILE.
  destruct Rule.compileds as [err | rules] eqn: COMPILED; inv COMPILE.
  destruct (rules2fragments 1 rules) as [qmax frags] eqn: FRAGS.
  exists rules, qmax, frags. split.
  - econs; eauto.
  - ii; econs.
    + eapply eps_step_from_edges_complete. eapply fragment_eps_edges_start_complete. exact H.
    + eapply fragment_accept_states_complete. exact H.
    + intros q q' IN_EDGE. eapply eps_step_from_edges_complete. eapply fragment_eps_edges_complete; eauto.
    + intros edge IN_EDGE. eapply char_step_from_edges_complete. eapply fragment_char_edges_complete; eauto.
Qed.

Definition fragments_delta_star (frags : list (Rule.t * fragment)) : nat -> Input.t -> ensemble nat :=
  delta_star (fun q => eps_step_from_edges q (fragment_eps_edges frags)) (fun q c => char_step_from_edges q c (fragment_char_edges frags)).

Definition fragment_delta_star (frag : fragment) : nat -> Input.t -> ensemble nat :=
  delta_star (fun q => eps_step_from_edges q frag.(frag_eps_edges)) (fun q c => char_step_from_edges q c frag.(frag_char_edges)).

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
    intros [q q'] [EQ | IN].
    + injection EQ as EQ1 EQ2. subst. unfold eps_edge_in_range. simpl. lia.
    + contradiction.
  - inv REGEX2FRAGMENT. econs; simpl; try lia.
    intros edge [EQ | IN]; [subst edge; unfold char_edge_in_range; simpl; lia | contradiction].
  - destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    pose proof (IH1 _ _ _ REGEX1) as [START1 ACCEPT1 LT1 EPS1 CHAR1].
    pose proof (IH2 _ _ _ REGEX2) as [START2 ACCEPT2 LT2 EPS2 CHAR2].
    inv REGEX2FRAGMENT. econs; simpl; try lia.
    + intros [q q'] IN_EDGE. simpl in IN_EDGE.
      destruct IN_EDGE as [EQ | [EQ | [EQ | [EQ | IN_EDGE]]]].
      * injection EQ as EQ1 EQ2. subst. unfold eps_edge_in_range. simpl. lia.
      * injection EQ as EQ1 EQ2. subst. unfold eps_edge_in_range. simpl. lia.
      * injection EQ as EQ1 EQ2. subst. unfold eps_edge_in_range. simpl. lia.
      * injection EQ as EQ1 EQ2. subst. unfold eps_edge_in_range. simpl. lia.
      * rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
        { pose proof (EPS1 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. lia. }
        { pose proof (EPS2 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. lia. }
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
      destruct IN_EDGE as [EQ | [EQ | [EQ | IN_EDGE]]].
      * injection EQ as EQ1 EQ2. subst. unfold eps_edge_in_range. simpl. lia.
      * injection EQ as EQ1 EQ2. subst. unfold eps_edge_in_range. simpl. lia.
      * injection EQ as EQ1 EQ2. subst. unfold eps_edge_in_range. simpl. lia.
      * rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
        { pose proof (EPS1 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. lia. }
        { pose proof (EPS2 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. lia. }
    + intros edge IN_EDGE. simpl in IN_EDGE. rewrite in_app_iff in IN_EDGE.
      destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (CHAR1 _ IN_EDGE). unfold char_edge_in_range in *. lia.
      * pose proof (CHAR2 _ IN_EDGE). unfold char_edge_in_range in *. lia.
  - destruct (regex2fragment e (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    pose proof (IH _ _ _ REGEX1) as [START1 ACCEPT1 LT1 EPS1 CHAR1].
    inv REGEX2FRAGMENT. econs; simpl; try lia.
    + intros [q q'] IN_EDGE. simpl in IN_EDGE.
      destruct IN_EDGE as [EQ | [EQ | [EQ | IN_EDGE]]].
      * injection EQ as EQ1 EQ2. subst. unfold eps_edge_in_range. simpl. lia.
      * injection EQ as EQ1 EQ2. subst. unfold eps_edge_in_range. simpl. lia.
      * injection EQ as EQ1 EQ2. subst. unfold eps_edge_in_range. simpl. lia.
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

Lemma regex2fragment_complete_aux (e : regex ascii) (s : Input.t) (frags : list (Rule.t * fragment)) (rule : Rule.t) (qi : nat) (qf : nat) (frag topfrag : fragment)
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
    eapply (CHAR (mkCharEdge qi c (qi + 1))).
    eapply CHAR_INCL. simpl. left. reflexivity.
  - simpl in REGEX2FRAGMENT. cbn [eval_regex] in IN_REGEX.
    autorewrite with simplication_hints in IN_REGEX.
    destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
    destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2.
    inv REGEX2FRAGMENT. destruct IN_REGEX as [IN1 | IN2].
    + pose proof (TaggedENFA_FRAGMENTS_delta_star_step frags rule topfrag FRAGMENTS) as [EPS _].
      pose proof (regex2fragment_start_accept _ _ _ _ REGEX1) as [START1 ACCEPT1].
      rewrite <- app_nil_r with (l := s).
      eapply delta_star_app with (q2 := qf1).
      * change s with ([] ++ s).
        eapply delta_star_app with (q2 := qi + 1).
        { eapply EPS. eapply EPS_INCL. simpl. left. reflexivity. }
        { rewrite <- START1. rewrite <- ACCEPT1.
          eapply (IH1 s IN1 frags rule (qi + 1) qf1 frag1 topfrag REGEX1 FRAGMENTS).
          - intros q q' IN_EDGE. eapply EPS_INCL. simpl.
            right; right; right; right. rewrite in_app_iff. left. exact IN_EDGE.
          - intros edge IN_EDGE. eapply CHAR_INCL. simpl.
            rewrite in_app_iff. left. exact IN_EDGE.
        }
      * eapply EPS. eapply EPS_INCL. simpl. right; right; left. reflexivity.
    + pose proof (TaggedENFA_FRAGMENTS_delta_star_step frags rule topfrag FRAGMENTS) as [EPS _].
      pose proof (regex2fragment_start_accept _ _ _ _ REGEX2) as [START2 ACCEPT2].
      rewrite <- app_nil_r with (l := s).
      eapply delta_star_app with (q2 := qf2).
      * change s with ([] ++ s).
        eapply delta_star_app with (q2 := qf1 + 1).
        { eapply EPS. eapply EPS_INCL. simpl. right; left. reflexivity. }
        { rewrite <- START2. rewrite <- ACCEPT2.
          eapply (IH2 s IN2 frags rule (qf1 + 1) qf2 frag2 topfrag REGEX2 FRAGMENTS).
          - intros q q' IN_EDGE. eapply EPS_INCL. simpl.
            right; right; right; right. rewrite in_app_iff. right. exact IN_EDGE.
          - intros edge IN_EDGE. eapply CHAR_INCL. simpl.
            rewrite in_app_iff. right. exact IN_EDGE.
        }
      * eapply EPS. eapply EPS_INCL. simpl.
        right; right; right; left. reflexivity.
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
      * eapply EPS. eapply EPS_INCL. simpl. left. reflexivity.
      * rewrite <- START1. rewrite <- ACCEPT1.
        eapply (IH1 s1 IN1 frags rule (qi + 1) qf1 frag1 topfrag REGEX1 FRAGMENTS).
        { intros q q' IN_EDGE. eapply EPS_INCL. simpl.
          right; right; right. rewrite in_app_iff. left. exact IN_EDGE.
        }
        { intros edge IN_EDGE. eapply CHAR_INCL. simpl.
          rewrite in_app_iff. left. exact IN_EDGE.
        }
    + rewrite <- app_nil_r with (l := s2).
      eapply delta_star_app with (q2 := qf2).
      * change s2 with ([] ++ s2).
        eapply delta_star_app with (q2 := qf1 + 1).
        { eapply EPS. eapply EPS_INCL. simpl. right; left. reflexivity. }
        { rewrite <- START2. rewrite <- ACCEPT2.
          eapply (IH2 s2 IN2 frags rule (qf1 + 1) qf2 frag2 topfrag REGEX2 FRAGMENTS).
          - intros q q' IN_EDGE. eapply EPS_INCL. simpl.
            right; right; right. rewrite in_app_iff. right. exact IN_EDGE.
          - intros edge IN_EDGE. eapply CHAR_INCL. simpl.
            rewrite in_app_iff. right. exact IN_EDGE.
        }
      * eapply EPS. eapply EPS_INCL. simpl. right; right; left. reflexivity.
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
            eapply (IH s1 IN1 frags rule (qi + 1) qf1 frag1 topfrag REGEX1 FRAGMENTS).
            { intros q q' IN_EDGE. eapply EPS_INCL. simpl. right; right; right. exact IN_EDGE. }
            { intros edge IN_EDGE. eapply CHAR_INCL. simpl. exact IN_EDGE. }
          * eapply EPS. eapply EPS_INCL. simpl. right; left. reflexivity.
        + exact IHSTAR.
    }
    change s with ([] ++ s).
    eapply delta_star_app with (q2 := qi + 1).
    + eapply EPS. eapply EPS_INCL. simpl. left. reflexivity.
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
  exists frag.(frag_accept). split.
  - change s with ([] ++ s).
    eapply delta_star_app with (q2 := frag.(frag_start)).
    + eapply delta_star_eps with (q1 := frag.(frag_start)).
      * exact START.
      * econs.
    + eapply regex2fragment_complete; eauto.
      econs; eauto.
  - exact ACCEPT.
Qed.

Theorem rules2fragments_complete qi rules qmax frags rule
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_RULE : rule ∈ rules)
  : exists qi_rule, exists qf, exists frag, regex2fragment rule.(Rule.regex) qi_rule = (qf, frag) /\ (rule, frag) ∈ frags.
Proof.
  revert qi qmax frags FRAGS IN_RULE.
  induction rules as [ | rule' rules IH]; intros qi qmax frags FRAGS IN_RULE; simpl in IN_RULE; try tauto.
  simpl in FRAGS. destruct (regex2fragment rule'.(Rule.regex) qi) as [qf frag] eqn: REGEX2FRAGMENT.
  destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
  injection FRAGS as Hqmax Hfrags. subst qmax frags.
  destruct IN_RULE as [EQ | IN_RULE].
  - subst rule'. exists qi, qf, frag. split; [exact REGEX2FRAGMENT | left; reflexivity].
  - pose proof (IH (qf + 1) qmax' frags' FRAGS' IN_RULE) as (qi_rule & qf_rule & frag_rule & REGEX & IN_FRAGS).
    exists qi_rule, qf_rule, frag_rule. split; [exact REGEX | right; exact IN_FRAGS].
Qed.

Lemma rules2fragments_sound qi rules qmax frags rule frag
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  : rule ∈ rules.
Proof.
  revert qi qmax frags FRAGS IN_FRAG.
  induction rules as [ | rule' rules IH]; ii; simpl in FRAGS.
  - inv FRAGS. contradiction.
  - destruct (regex2fragment rule'.(Rule.regex) qi) as [qf frag'] eqn: REGEX.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    injection FRAGS as Hqmax Hfrags. subst qmax frags.
    simpl in IN_FRAG. destruct IN_FRAG as [EQ | IN_FRAG].
    + inv EQ. left. reflexivity.
    + right. eapply IH; eauto.
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
    assert (LT : qi < qf) by (destruct BOUNDS as [_ _ LT _ _]; exact LT).
    pose proof (IH (qf + 1) qmax' frags' FRAGS') as [QMAX TAIL].
    split; [lia | intros rule frag' IN]. destruct IN as [EQ | IN].
    + inv EQ. exists qi, qf. split; eauto. split; eauto. split; lia.
    + pose proof (TAIL rule frag' IN) as (qi_rule & qf_rule & REGEX & BOUNDS' & LE_START & LT_END).
      exists qi_rule, qf_rule. split; eauto. split; eauto. split; lia.
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
  revert qi qmax frags FRAGS rule1 frag1 qi1 qf1 rule2 frag2 qi2 qf2 q IN1 IN2 REGEX1 REGEX2 RANGE1 RANGE2.
  induction rules as [ | rule rules IH]; ii.
  - simpl in FRAGS. inv FRAGS. contradiction.
  - simpl in FRAGS.
    destruct (regex2fragment rule.(Rule.regex) qi) as [qf frag] eqn: REGEX.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    injection FRAGS as Hqmax Hfrags. subst qmax frags.
    pose proof (rules2fragments_bounds _ _ _ _ FRAGS') as [_ TAIL_BOUNDS].
    destruct IN1 as [EQ1 | IN1]; destruct IN2 as [EQ2 | IN2].
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

Lemma fragment_eps_edges_owner qi rules qmax frags q q'
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_EDGE : (q, q') ∈ fragment_eps_edges frags)
  (SRC_NONZERO : ~ q = 0)
  : exists rule, exists frag, exists qi_rule, exists qf, (rule, frag) ∈ frags /\ regex2fragment rule.(Rule.regex) qi_rule = (qf, frag) /\ FRAGMENT_BOUNDS qi_rule qf frag /\ qi <= qi_rule /\ qf < qmax /\ qi_rule <= q <= qf /\ (q, q') ∈ frag.(frag_eps_edges).
Proof.
  revert qi qmax frags FRAGS IN_EDGE.
  induction rules as [ | rule rules IH]; ii.
  - simpl in FRAGS. inv FRAGS. contradiction.
  - simpl in FRAGS.
    destruct (regex2fragment rule.(Rule.regex) qi) as [qf frag] eqn: REGEX.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    injection FRAGS as Hqmax Hfrags. subst qmax frags.
    pose proof (rules2fragments_bounds _ _ _ _ FRAGS') as [QMAX _].
    simpl in IN_EDGE. destruct IN_EDGE as [EQ | IN_EDGE].
    + inv EQ. contradiction.
    + rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (regex2fragment_bounds _ _ _ _ REGEX) as BOUNDS.
        destruct BOUNDS as [_ _ LT EPS _].
        pose proof (EPS _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *.
        exists rule, frag, qi, qf. split; [left; reflexivity | ].
        split; [exact REGEX | ]. split; [eapply regex2fragment_bounds; eauto | ].
        split; [lia | ]. split; [lia | ]. split; [lia | exact IN_EDGE].
      * pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ LT _ _].
        pose proof (IH (qf + 1) qmax' frags' FRAGS' IN_EDGE) as (rule' & frag' & qi_rule & qf' & IN_FRAG & REGEX' & BOUNDS & LE & LT' & RANGE & IN_EDGE').
        exists rule', frag', qi_rule, qf'. split; [right; exact IN_FRAG | ].
        split; [exact REGEX' | ]. split; [exact BOUNDS | ].
        split; [lia | ]. split; [exact LT' | ]. split; [exact RANGE | exact IN_EDGE'].
Qed.

Lemma fragment_eps_edges_start_sound qi rules qmax frags q'
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (qi_POS : 0 < qi)
  (IN_EDGE : (0, q') ∈ fragment_eps_edges frags)
  : exists rule, exists frag, exists qi_rule, exists qf, (rule, frag) ∈ frags /\ regex2fragment rule.(Rule.regex) qi_rule = (qf, frag) /\ q' = frag.(frag_start).
Proof.
  revert qi qmax frags q' FRAGS qi_POS IN_EDGE.
  induction rules as [ | rule rules IH]; ii; simpl in FRAGS.
  - inv FRAGS. contradiction.
  - destruct (regex2fragment rule.(Rule.regex) qi) as [qf frag] eqn: REGEX.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    injection FRAGS as Hqmax Hfrags. subst qmax frags.
    simpl in IN_EDGE. destruct IN_EDGE as [EQ | IN_EDGE].
    + inv EQ. exists rule, frag, qi, qf. repeat split; eauto.
      left. reflexivity.
    + rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ _ EPS _].
        pose proof (EPS _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. lia.
      * pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ LT _ _].
        assert (qi_POS' : 0 < qf + 1) by lia.
        pose proof (IH (qf + 1) qmax' frags' q' FRAGS' qi_POS' IN_EDGE) as (rule' & frag' & qi_rule & qf' & IN_FRAG & REGEX' & START).
        exists rule', frag', qi_rule, qf'. split; [right; exact IN_FRAG | ].
        split; [exact REGEX' | exact START].
Qed.

Lemma fragment_char_edges_owner qi rules qmax frags edge
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_EDGE : edge ∈ fragment_char_edges frags)
  : exists rule, exists frag, exists qi_rule, exists qf, (rule, frag) ∈ frags /\ regex2fragment rule.(Rule.regex) qi_rule = (qf, frag) /\ FRAGMENT_BOUNDS qi_rule qf frag /\ qi <= qi_rule /\ qf < qmax /\ qi_rule <= edge.(char_edge_src) <= qf /\ edge ∈ frag.(frag_char_edges).
Proof.
  revert qi qmax frags FRAGS IN_EDGE.
  induction rules as [ | rule rules IH]; ii; simpl in FRAGS.
  - inv FRAGS. contradiction.
  - destruct (regex2fragment rule.(Rule.regex) qi) as [qf frag] eqn: REGEX.
    destruct (rules2fragments (qf + 1) rules) as [qmax' frags'] eqn: FRAGS'.
    injection FRAGS as Hqmax Hfrags. subst qmax frags.
    pose proof (rules2fragments_bounds _ _ _ _ FRAGS') as [QMAX _].
    simpl in IN_EDGE. rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
    + pose proof (regex2fragment_bounds _ _ _ _ REGEX) as BOUNDS.
      destruct BOUNDS as [_ _ LT _ CHAR].
      pose proof (CHAR _ IN_EDGE). unfold char_edge_in_range in *.
      exists rule, frag, qi, qf. split; [left; reflexivity | ].
      split; [exact REGEX | ]. split; [eapply regex2fragment_bounds; eauto | ].
      repeat (split; [lia | eauto]).
    + pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [_ _ LT _ _].
      pose proof (IH (qf + 1) qmax' frags' FRAGS' IN_EDGE) as (rule' & frag' & qi_rule & qf' & IN_FRAG & REGEX' & BOUNDS & LE & LT' & RANGE & IN_EDGE').
      exists rule', frag', qi_rule, qf'. split; [right; exact IN_FRAG | ].
      split; [exact REGEX' | ]. split; [exact BOUNDS | ].
      repeat (split; [lia | eauto]).
Qed.

Lemma fragments2TaggedENFA_okay rules qmax frags
  (FRAGS : rules2fragments 1 rules = (qmax, frags))
  : TaggedENFA.okay (fragments2TaggedENFA qmax frags).
Proof.
  constructor; simpl.
  - rewrite in_seq. pose proof (rules2fragments_bounds _ _ _ _ FRAGS) as [LE _]. lia.
  - intros q tag ACCEPT.
    pose proof (fragment_accept_states_sound _ _ _ ACCEPT) as (rule & frag & IN_FRAG & ACCEPT_EQ & TOKEN_EQ).
    subst q tag.
    pose proof (rules2fragments_bounds _ _ _ _ FRAGS) as [_ BOUND].
    pose proof (BOUND _ _ IN_FRAG) as (qi_rule & qf & REGEX & BOUNDS & LE_START & LT_END).
    destruct BOUNDS as [_ ACCEPT_EQ _ _ _]. subst qf.
    rewrite in_seq. lia.
  - intros q q' IN_STATES STEP.
    pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE.
    destruct (eq_dec q 0) as [EQ | NE].
    + subst q.
      assert (QI_POS : 0 < 1) by lia.
      pose proof (fragment_eps_edges_start_sound _ _ _ _ _ FRAGS QI_POS IN_EDGE) as (rule & frag & qi_rule & qf & IN_FRAG & REGEX & START_EQ).
      subst q'.
      pose proof (rules2fragments_bounds _ _ _ _ FRAGS) as [_ BOUND].
      pose proof (BOUND _ _ IN_FRAG) as (qi_rule' & qf' & REGEX' & BOUNDS & LE_START & LT_END).
      pose proof (regex2fragment_same_fragment _ _ _ _ _ _ REGEX REGEX') as [EQ_QI EQ_QF].
      subst qi_rule' qf'.
      destruct BOUNDS as [START_EQ _ LT _ _]. subst.
      rewrite in_seq. lia.
    + pose proof (fragment_eps_edges_owner _ _ _ _ _ _ FRAGS IN_EDGE NE) as (rule & frag & qi_rule & qf & IN_FRAG & REGEX & BOUNDS & LE_START & LT_END & RANGE & IN_EDGE').
      destruct BOUNDS as [_ _ _ EPS _].
      pose proof (EPS _ IN_EDGE') as RANGE'.
      unfold eps_edge_in_range in RANGE'. simpl in RANGE'.
      rewrite in_seq. lia.
  - intros q q' c IN_STATES STEP.
    pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    subst q q' c.
    pose proof (fragment_char_edges_owner _ _ _ _ _ FRAGS IN_EDGE) as (rule & frag & qi_rule & qf & IN_FRAG & REGEX & BOUNDS & LE_START & LT_END & RANGE & IN_EDGE').
    destruct BOUNDS as [_ _ _ _ CHAR].
    pose proof (CHAR _ IN_EDGE') as RANGE'.
    unfold char_edge_in_range in RANGE'. simpl in RANGE'.
    rewrite in_seq. lia.
Qed.

Theorem mkUnitedTaggedENFA_okay rules
  : TaggedENFA.okay (mkUnitedTaggedENFA rules).
Proof.
  unfold mkUnitedTaggedENFA. destruct (rules2fragments 1 rules) as [qmax frags] eqn: FRAGS.
  eapply fragments2TaggedENFA_okay. exact FRAGS.
Qed.

Lemma fragment_eps_edges_isolate qi rules qmax frags rule frag qi_rule qf q q'
  (FRAGS : rules2fragments qi rules = (qmax, frags))
  (IN_FRAG : (rule, frag) ∈ frags)
  (REGEX : regex2fragment rule.(Rule.regex) qi_rule = (qf, frag))
  (SRC_NONZERO : ~ q = 0)
  (RANGE : qi_rule <= q <= qf)
  (IN_EDGE : (q, q') ∈ fragment_eps_edges frags)
  : (q, q') ∈ frag.(frag_eps_edges).
Proof.
  pose proof (fragment_eps_edges_owner _ _ _ _ _ _ FRAGS IN_EDGE SRC_NONZERO) as (rule' & frag' & qi_rule' & qf' & IN_FRAG' & REGEX' & _ & _ & _ & RANGE' & IN_EDGE').
  pose proof (rules2fragments_ranges_disjoint _ _ _ _ _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG IN_FRAG' REGEX REGEX' RANGE RANGE') as EQ.
  inv EQ. exact IN_EDGE'.
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
  inv EQ. exact IN_EDGE'.
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
  subst qi_rule'. exact LE.
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
  revert qi rules rule frag qi_rule qf FRAGS IN_FRAG REGEX qi_POS RANGE. induction DELTA; ii.
  - exact RANGE.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE.
    assert (SRC_NONZERO : ~ q = 0) by (pose proof (rules2fragments_start_ge _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX); lia).
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
    assert (SRC_NONZERO : ~ q = 0) by (pose proof (rules2fragments_start_ge _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX); lia).
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
  pose proof (delta_star_elim q q' s DELTA) as [NIL | [EPS | CHAR]].
  - left. exact NIL.
  - right. left. destruct EPS as (q1 & STEP & REST).
    pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE.
    assert (SRC_NONZERO : ~ q = 0) by (pose proof (rules2fragments_start_ge _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX); lia).
    pose proof (fragment_eps_edges_isolate _ _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX SRC_NONZERO RANGE IN_EDGE) as IN_FRAG_EDGE.
    exists q1. split; eauto.
  - right. right. destruct CHAR as (c & s' & q1 & EQ & STEP & REST).
    pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    assert (RANGE_SRC : qi_rule <= edge.(char_edge_src) <= qf) by lia.
    pose proof (fragment_char_edges_isolate _ _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX RANGE_SRC IN_EDGE) as IN_FRAG_EDGE.
    exists edge, s'. repeat split; eauto; try congruence.
    now rewrite DST.
Qed.

Lemma fragment_delta_star_elim frag q q' s
  (DELTA : q' \in fragment_delta_star frag q s)
  : ⟪ DELTA_STAR_NIL : s = [] /\ q' = q ⟫ \/ ⟪ DELTA_STAR_EPS : exists q1, (q, q1) ∈ frag.(frag_eps_edges) /\ q' \in fragment_delta_star frag q1 s ⟫ \/ ⟪ DELTA_STAR_CHAR : exists edge, exists s', s = edge.(char_edge_label) :: s' /\ edge ∈ frag.(frag_char_edges) /\ q' \in fragment_delta_star frag edge.(char_edge_dst) s' ⟫.
Proof.
  pose proof (delta_star_elim q q' s DELTA) as [NIL | [EPS | CHAR]].
  - left. exact NIL.
  - right. left. destruct EPS as (q1 & STEP & REST).
    pose proof (eps_step_from_edges_sound _ _ _ STEP). exists q1. eauto.
  - right. right. destruct CHAR as (c & s' & q1 & EQ & STEP & REST).
    pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    exists edge, s'. repeat split; eauto; try congruence.
    now rewrite DST.
Qed.

Lemma fragment_delta_star_elim_with_src frag q q' s
  (DELTA : q' \in fragment_delta_star frag q s)
  : ⟪ DELTA_STAR_NIL : s = [] /\ q' = q ⟫ \/ ⟪ DELTA_STAR_EPS : exists q1, (q, q1) ∈ frag.(frag_eps_edges) /\ q' \in fragment_delta_star frag q1 s ⟫ \/ ⟪ DELTA_STAR_CHAR : exists edge, exists s', s = edge.(char_edge_label) :: s' /\ edge.(char_edge_src) = q /\ edge ∈ frag.(frag_char_edges) /\ q' \in fragment_delta_star frag edge.(char_edge_dst) s' ⟫.
Proof.
  pose proof (delta_star_elim q q' s DELTA) as [NIL | [EPS | CHAR]].
  - left. exact NIL.
  - right. left. destruct EPS as (q1 & STEP & REST).
    pose proof (eps_step_from_edges_sound _ _ _ STEP). exists q1. eauto.
  - right. right. destruct CHAR as (c & s' & q1 & EQ & STEP & REST).
    pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    exists edge, s'. repeat split; eauto; try congruence.
    now rewrite DST.
Qed.

Lemma regex2fragment_Union_delta_star_start qi qf frag e1 e2 s
  (REGEX : regex2fragment (Re.Union e1 e2) qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : exists qf1, exists frag1, exists qf2, exists frag2, regex2fragment e1 (qi + 1) = (qf1, frag1) /\ regex2fragment e2 (qf1 + 1) = (qf2, frag2) /\ (frag.(frag_accept) \in fragment_delta_star frag (qi + 1) s \/ frag.(frag_accept) \in fragment_delta_star frag (qf1 + 1) s).
Proof.
  simpl in REGEX. destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
  destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2. inv REGEX.
  exists qf1, frag1, qf2, frag2. repeat split; eauto.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  pose proof (fragment_delta_star_elim_with_src _ _ _ _ DELTA) as [NIL | [EPS | CHAR]].
  - des; simpl in *; lia.
  - destruct EPS as (q1 & IN_EDGE & REST). simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | [EQ | [EQ | [EQ | IN_EDGE]]]].
    + inv EQ. left. exact REST.
    + inv EQ. right. exact REST.
    + inv EQ. lia.
    + inv EQ. lia.
    + rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (EPS1 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. lia.
      * pose proof (EPS2 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. lia.
  - destruct CHAR as (edge & s' & EQ & SRC & IN_EDGE & REST). simpl in IN_EDGE.
    rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] _].
      simpl in SRC. exfalso. lia.
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] _].
      simpl in SRC. exfalso. lia.
Qed.

Lemma regex2fragment_Union_left_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 q q' s
  (REGEX : regex2fragment (Re.Union e1 e2) qi = (qf, frag))
  (REGEX1 : regex2fragment e1 (qi + 1) = (qf1, frag1))
  (REGEX2 : regex2fragment e2 (qf1 + 1) = (qf2, frag2))
  (RANGE : qi + 1 <= q <= qf1)
  (DELTA : q' \in fragment_delta_star frag q s)
  (ACCEPT : q' = frag.(frag_accept))
  : exists s1, exists s2, s = s1 ++ s2 /\ qf1 \in fragment_delta_star frag1 q s1 /\ frag.(frag_accept) \in fragment_delta_star frag frag.(frag_accept) s2.
Proof.
  revert q q' s RANGE DELTA ACCEPT.
  simpl in REGEX. rewrite REGEX1 in REGEX. rewrite REGEX2 in REGEX. inv REGEX.
  intros q q' s RANGE DELTA ACCEPT.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  revert RANGE ACCEPT. induction DELTA; intros RANGE ACCEPT.
  - simpl in *. lia.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE. simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | [EQ | [EQ | [EQ | IN_EDGE]]]].
    + injection EQ as EQ1 EQ2. lia.
    + injection EQ as EQ1 EQ2. lia.
    + injection EQ as EQ1 EQ2. subst q q1. exists [], s. repeat split; eauto.
      * econs.
      * now rewrite ACCEPT in REST.
    + injection EQ as EQ1 EQ2. lia.
    + rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (EPS1 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
        simpl in SRC_LO, SRC_HI, DST_LO, DST_HI.
        assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
        pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
        exists s1, s2. repeat split; eauto.
        eapply delta_star_eps; eauto. eapply eps_step_from_edges_complete. exact IN_EDGE.
      * pose proof (EPS2 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in *. lia.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    simpl in IN_EDGE. rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
      assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
      pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
      exists (edge.(char_edge_label) :: s1), s2. split.
      * rewrite EQ. simpl. now rewrite LABEL.
      * split; eauto. eapply delta_star_char with (q1 := q1).
        { rewrite <- DST. rewrite <- SRC. eapply char_step_from_edges_complete. exact IN_EDGE. }
        { exact DELTA1. }
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
  revert q q' s RANGE DELTA ACCEPT.
  simpl in REGEX. rewrite REGEX1 in REGEX. rewrite REGEX2 in REGEX. inv REGEX.
  intros q q' s RANGE DELTA ACCEPT.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  revert RANGE ACCEPT. induction DELTA; intros RANGE ACCEPT.
  - simpl in *. lia.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE. simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | [EQ | [EQ | [EQ | IN_EDGE]]]].
    + injection EQ as EQ1 EQ2. lia.
    + injection EQ as EQ1 EQ2. lia.
    + injection EQ as EQ1 EQ2. lia.
    + injection EQ as EQ1 EQ2. subst q q1. exists [], s. repeat split; eauto.
      * econs.
      * now rewrite ACCEPT in REST.
    + rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (EPS1 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in *. lia.
      * pose proof (EPS2 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
        simpl in SRC_LO, SRC_HI, DST_LO, DST_HI.
        assert (RANGE_STEP : qf1 + 1 <= q1 <= qf2) by lia.
        pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
        exists s1, s2. repeat split; eauto.
        eapply delta_star_eps; eauto. eapply eps_step_from_edges_complete. exact IN_EDGE.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    simpl in IN_EDGE. rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in SRC. lia.
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
      assert (RANGE_STEP : qf1 + 1 <= q1 <= qf2) by lia.
      pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
      exists (edge.(char_edge_label) :: s1), s2. split.
      * rewrite EQ. simpl. now rewrite LABEL.
      * split; eauto. eapply delta_star_char with (q1 := q1).
        { rewrite <- DST. rewrite <- SRC. eapply char_step_from_edges_complete. exact IN_EDGE. }
        { exact DELTA1. }
Qed.

Lemma regex2fragment_Append_delta_star_start qi qf frag e1 e2 s
  (REGEX : regex2fragment (Re.Append e1 e2) qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : exists qf1, exists frag1, exists qf2, exists frag2, regex2fragment e1 (qi + 1) = (qf1, frag1) /\ regex2fragment e2 (qf1 + 1) = (qf2, frag2) /\ frag.(frag_accept) \in fragment_delta_star frag (qi + 1) s.
Proof.
  simpl in REGEX. destruct (regex2fragment e1 (qi + 1)) as [qf1 frag1] eqn: REGEX1.
  destruct (regex2fragment e2 (qf1 + 1)) as [qf2 frag2] eqn: REGEX2. inv REGEX.
  exists qf1, frag1, qf2, frag2. repeat split; eauto.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  pose proof (fragment_delta_star_elim_with_src _ _ _ _ DELTA) as [NIL | [EPS | CHAR]].
  - des; simpl in *; lia.
  - destruct EPS as (q1 & IN_EDGE & REST). simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | [EQ | [EQ | IN_EDGE]]].
    + inv EQ. exact REST.
    + inv EQ. lia.
    + inv EQ. lia.
    + rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (EPS1 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. lia.
      * pose proof (EPS2 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. lia.
  - destruct CHAR as (edge & s' & EQ & SRC & IN_EDGE & REST). simpl in IN_EDGE.
    rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] _].
      simpl in SRC. exfalso. lia.
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] _].
      simpl in SRC. exfalso. lia.
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
  revert q q' s RANGE DELTA ACCEPT.
  simpl in REGEX. rewrite REGEX1 in REGEX. rewrite REGEX2 in REGEX. inv REGEX.
  intros q q' s RANGE DELTA ACCEPT.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  revert RANGE ACCEPT. induction DELTA; intros RANGE ACCEPT.
  - simpl in *. lia.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE. simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | [EQ | [EQ | IN_EDGE]]].
    + injection EQ as EQ1 EQ2. lia.
    + injection EQ as EQ1 EQ2. subst q q1. exists [], s. repeat split; eauto.
      * econs.
      * now rewrite ACCEPT in REST.
    + injection EQ as EQ1 EQ2. lia.
    + rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (EPS1 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
        simpl in SRC_LO, SRC_HI, DST_LO, DST_HI.
        assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
        pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
        exists s1, s2. repeat split; eauto.
        eapply delta_star_eps; eauto. eapply eps_step_from_edges_complete. exact IN_EDGE.
      * pose proof (EPS2 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in *. lia.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    simpl in IN_EDGE. rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
      assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
      pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
      exists (edge.(char_edge_label) :: s1), s2. split.
      * rewrite EQ. simpl. now rewrite LABEL.
      * split; eauto. eapply delta_star_char with (q1 := q1).
        { rewrite <- DST. rewrite <- SRC. eapply char_step_from_edges_complete. exact IN_EDGE. }
        { exact DELTA1. }
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in SRC. lia.
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
  revert q q' s RANGE DELTA ACCEPT.
  simpl in REGEX. rewrite REGEX1 in REGEX. rewrite REGEX2 in REGEX. inv REGEX.
  intros q q' s RANGE DELTA ACCEPT.
  pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [_ _ LT1 EPS1 CHAR1].
  pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [_ _ LT2 EPS2 CHAR2].
  revert RANGE ACCEPT. induction DELTA; intros RANGE ACCEPT.
  - simpl in *. lia.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE. simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | [EQ | [EQ | IN_EDGE]]].
    + injection EQ as EQ1 EQ2. lia.
    + injection EQ as EQ1 EQ2. lia.
    + injection EQ as EQ1 EQ2. subst q q1. exists [], s. repeat split; eauto.
      * econs.
      * now rewrite ACCEPT in REST.
    + rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
      * pose proof (EPS1 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in *. lia.
      * pose proof (EPS2 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
        simpl in SRC_LO, SRC_HI, DST_LO, DST_HI.
        assert (RANGE_STEP : qf1 + 1 <= q1 <= qf2) by lia.
        pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
        exists s1, s2. repeat split; eauto.
        eapply delta_star_eps; eauto. eapply eps_step_from_edges_complete. exact IN_EDGE.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    simpl in IN_EDGE. rewrite in_app_iff in IN_EDGE. destruct IN_EDGE as [IN_EDGE | IN_EDGE].
    + pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] _]. simpl in SRC. lia.
    + pose proof (CHAR2 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
      assert (RANGE_STEP : qf1 + 1 <= q1 <= qf2) by lia.
      pose proof (IHDELTA RANGE_STEP ACCEPT) as (s1 & s2 & EQ & DELTA1 & DELTA2).
      exists (edge.(char_edge_label) :: s1), s2. split.
      * rewrite EQ. simpl. now rewrite LABEL.
      * split; eauto. eapply delta_star_char with (q1 := q1).
        { rewrite <- DST. rewrite <- SRC. eapply char_step_from_edges_complete. exact IN_EDGE. }
        { exact DELTA1. }
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
  - des; simpl in *; lia.
  - destruct EPS as (q1 & IN_EDGE & REST). simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | [EQ | [EQ | IN_EDGE]]].
    + inv EQ. exact REST.
    + inv EQ. lia.
    + inv EQ. lia.
    + pose proof (EPS1 _ IN_EDGE). unfold eps_edge_in_range in *. simpl in *. lia.
  - destruct CHAR as (edge & s' & EQ & SRC & IN_EDGE & REST).
    pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] _].
    simpl in SRC. exfalso. lia.
Qed.

Lemma regex2fragment_accept_delta_star_stuck e qi qf frag q' s
  (REGEX : regex2fragment e qi = (qf, frag))
  (DELTA : q' \in fragment_delta_star frag qf s)
  : s = [] /\ q' = qf.
Proof.
  eapply delta_star_stuck; eauto.
  - intros q IN. pose proof (eps_step_from_edges_sound _ _ _ IN) as IN_EDGE.
    pose proof (regex2fragment_edge_src_lt _ _ _ _ REGEX) as [EPS _].
    pose proof (EPS _ _ IN_EDGE). lia.
  - intros c q IN. pose proof (char_step_from_edges_sound _ _ _ _ IN) as (edge & IN_EDGE & SRC & LABEL & DST).
    pose proof (regex2fragment_edge_src_lt _ _ _ _ REGEX) as [_ CHAR].
    pose proof (CHAR _ IN_EDGE). lia.
Qed.

Lemma regex2fragment_Star_delta_star_sound_aux e
  (SOUND : forall qi, forall qf, forall frag, forall s, regex2fragment e qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e)
  : forall qi, forall qf, forall frag, forall qf1, forall frag1, forall q, forall q', forall s, regex2fragment (Re.Star e) qi = (qf, frag) -> regex2fragment e (qi + 1) = (qf1, frag1) -> qi + 1 <= q <= qf1 -> q' \in fragment_delta_star frag q s -> q' = frag.(frag_accept) ->  ((s = [] /\ q = qi + 1) \/ (exists s1, exists s2, s = s1 ++ s2 /\ qf1 \in fragment_delta_star frag1 q s1 /\ s2 \in eval_regex (Re.Star e))).
Proof.
  ii. revert q q' s H1 H2 H3.
  simpl in H. rewrite H0 in H. inv H.
  intros q q' s RANGE DELTA ACCEPT.
  pose proof (regex2fragment_bounds _ _ _ _ H0) as [START1 ACCEPT1 LT1 EPS1 CHAR1].
  pose proof (regex2fragment_edge_dst_gt_start _ _ _ _ H0) as [EPS_DST CHAR_DST].
  revert RANGE ACCEPT. induction DELTA; intros RANGE ACCEPT.
  - simpl in *. lia.
  - pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE. simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | [EQ | [EQ | IN_EDGE]]].
    + injection EQ as EQ1 EQ2. lia.
    + injection EQ as EQ1 EQ2. subst q q1.
      assert (STAR_IN : s \in eval_regex (Re.Star e)).
      { assert (RANGE_STEP : qi + 1 <= qi + 1 <= qf1) by lia.
        pose proof (IHDELTA RANGE_STEP ACCEPT) as [[EQ _] | (s1 & s2 & EQ & DELTA1 & STAR)].
        - subst s. simpl. econs.
        - subst s. simpl. eapply star_app.
          + eapply SOUND; eauto. rewrite START1. rewrite ACCEPT1. exact DELTA1.
          + exact STAR.
      }
      right. exists [], s. repeat split; eauto. econs.
    + injection EQ as EQ1 EQ2. subst q q1.
      assert (REGEX_STAR : regex2fragment (Re.Star e) qi = (qf1 + 1, mkFragment qi (qf1 + 1) ((qi, qi + 1) :: (qf1, qi + 1) :: (qi + 1, qf1 + 1) :: frag1.(frag_eps_edges)) frag1.(frag_char_edges))) by (simpl; rewrite H0; reflexivity).
      pose proof (regex2fragment_accept_delta_star_stuck (Re.Star e) qi (qf1 + 1) (mkFragment qi (qf1 + 1) ((qi, qi + 1) :: (qf1, qi + 1) :: (qi + 1, qf1 + 1) :: frag1.(frag_eps_edges)) frag1.(frag_char_edges)) q2 s REGEX_STAR REST) as [EQ _].
      subst s. left. split; eauto.
    + pose proof (EPS1 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
      simpl in SRC_LO, SRC_HI, DST_LO, DST_HI.
      assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
      pose proof (IHDELTA RANGE_STEP ACCEPT) as [[EQ EQ'] | (s1 & s2 & EQ & DELTA1 & STAR)].
      * subst s q1. pose proof (EPS_DST _ _ IN_EDGE). lia.
      * right. exists s1, s2. repeat split; eauto.
        eapply delta_star_eps; eauto. eapply eps_step_from_edges_complete. exact IN_EDGE.
  - pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    pose proof (CHAR1 _ IN_EDGE) as [[SRC_LO SRC_HI] [DST_LO DST_HI]].
    assert (RANGE_STEP : qi + 1 <= q1 <= qf1) by lia.
    pose proof (IHDELTA RANGE_STEP ACCEPT) as [[EQ EQ'] | (s1 & s2 & EQ & DELTA1 & STAR)].
    + subst s q1. pose proof (CHAR_DST _ IN_EDGE). lia.
    + right. exists (edge.(char_edge_label) :: s1), s2. split.
      * rewrite EQ. simpl. now rewrite LABEL.
      * split; eauto. eapply delta_star_char with (q1 := q1).
        { rewrite <- DST. rewrite <- SRC. eapply char_step_from_edges_complete. exact IN_EDGE. }
        { exact DELTA1. }
Qed.

Theorem regex2fragment_sound_Null qi qf frag s
  (REGEX : regex2fragment Re.Null qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : s \in eval_regex Re.Null.
Proof.
  simpl in REGEX. inv REGEX. pose proof (fragment_delta_star_elim _ _ _ _ DELTA) as [NIL | [EPS | CHAR]].
  - des; simpl in *; lia.
  - des; contradiction.
  - des; contradiction.
Qed.

Theorem regex2fragment_sound_Empty qi qf frag s
  (REGEX : regex2fragment Re.Empty qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : s \in eval_regex Re.Empty.
Proof.
  simpl in REGEX. inv REGEX. pose proof (fragment_delta_star_elim _ _ _ _ DELTA) as [NIL | [EPS | CHAR]].
  - des; simpl in *; lia.
  - destruct EPS as (q1 & IN_EDGE & REST). simpl in IN_EDGE.
    destruct IN_EDGE as [EQ | []]. inv EQ.
    pose proof (regex2fragment_accept_delta_star_stuck Re.Empty qi (qi + 1) (mkFragment qi (qi + 1) [(qi, qi + 1)] []) (qi + 1) s eq_refl REST) as [EQ ?].
    subst s. simpl. autorewrite with simplication_hints. reflexivity.
  - des; contradiction.
Qed.

Theorem regex2fragment_sound_Char c qi qf frag s
  (REGEX : regex2fragment (Re.Char c) qi = (qf, frag))
  (DELTA : frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s)
  : s \in eval_regex (Re.Char c).
Proof.
  simpl in REGEX. inv REGEX. pose proof (fragment_delta_star_elim _ _ _ _ DELTA) as [NIL | [EPS | CHAR]].
  - des; simpl in *; lia.
  - des; contradiction.
  - destruct CHAR as (edge & s' & EQ & IN_EDGE & REST). simpl in IN_EDGE.
    destruct IN_EDGE as [EDGE_EQ | []]. subst edge. simpl in EQ. subst s.
    pose proof (regex2fragment_accept_delta_star_stuck (Re.Char c) qi (qi + 1) (mkFragment qi (qi + 1) [] [mkCharEdge qi c (qi + 1)]) (qi + 1) s' eq_refl REST) as [EQ ?].
    subst s'. simpl. autorewrite with simplication_hints. reflexivity.
Qed.

Theorem regex2fragment_sound_Union e1 e2
  (SOUND1 : forall qi, forall qf, forall frag, forall s, regex2fragment e1 qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e1)
  (SOUND2 : forall qi, forall qf, forall frag, forall s, regex2fragment e2 qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e2)
  : forall qi, forall qf, forall frag, forall s, regex2fragment (Re.Union e1 e2) qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex (Re.Union e1 e2).
Proof.
  ii. pose proof (regex2fragment_start_accept _ _ _ _ H) as [_ ACCEPT].
  pose proof (regex2fragment_Union_delta_star_start qi qf frag e1 e2 s H H0) as (qf1 & frag1 & qf2 & frag2 & REGEX1 & REGEX2 & [DELTA1 | DELTA2]).
  - pose proof (regex2fragment_bounds _ _ _ _ REGEX1) as [START1 ACCEPT1 LT1 _ _].
    assert (RANGE1 : qi + 1 <= qi + 1 <= qf1) by lia.
    pose proof (regex2fragment_Union_left_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 (qi + 1) frag.(frag_accept) s H REGEX1 REGEX2 RANGE1 DELTA1 eq_refl) as (s1 & s2 & EQ & DELTA1' & DELTA2').
    rewrite ACCEPT in DELTA2'.
    pose proof (regex2fragment_accept_delta_star_stuck (Re.Union e1 e2) qi qf frag qf s2 H DELTA2') as [EQ2 _].
    subst s2. rewrite app_nil_r in EQ. subst s.
    simpl. rewrite E.in_union_iff. left. eapply SOUND1; eauto.
    rewrite START1. rewrite ACCEPT1. exact DELTA1'.
  - pose proof (regex2fragment_bounds _ _ _ _ REGEX2) as [START2 ACCEPT2 LT2 _ _].
    assert (RANGE2 : qf1 + 1 <= qf1 + 1 <= qf2) by lia.
    pose proof (regex2fragment_Union_right_delta_star_split qi qf frag e1 e2 qf1 frag1 qf2 frag2 (qf1 + 1) frag.(frag_accept) s H REGEX1 REGEX2 RANGE2 DELTA2 eq_refl) as (s1 & s2 & EQ & DELTA1' & DELTA2').
    rewrite ACCEPT in DELTA2'.
    pose proof (regex2fragment_accept_delta_star_stuck (Re.Union e1 e2) qi qf frag qf s2 H DELTA2') as [EQ2 _].
    subst s2. rewrite app_nil_r in EQ. subst s.
    simpl. rewrite E.in_union_iff. right. eapply SOUND2; eauto.
    rewrite START2. rewrite ACCEPT2. exact DELTA1'.
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
  pose proof (regex2fragment_accept_delta_star_stuck (Re.Append e1 e2) qi qf frag qf s3 H DELTA3) as [EQ3 _].
  subst s3. rewrite app_nil_r in EQ'. subst s2. subst s.
  simpl. exists s1. split.
  - eapply SOUND1; eauto. rewrite START1. rewrite ACCEPT1. exact DELTA1.
  - exists s2'. split.
    + eapply SOUND2; eauto. rewrite START2. rewrite ACCEPT2. exact DELTA2'.
    + reflexivity.
Qed.

Theorem regex2fragment_sound_Star e1
  (SOUND : forall qi, forall qf, forall frag, forall s, regex2fragment e1 qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex e1)
  : forall qi, forall qf, forall frag, forall s, regex2fragment (Re.Star e1) qi = (qf, frag) -> frag.(frag_accept) \in fragment_delta_star frag frag.(frag_start) s -> s \in eval_regex (Re.Star e1).
Proof.
  ii. pose proof (regex2fragment_Star_delta_star_start qi qf frag e1 s H H0) as (qf1 & frag1 & REGEX & DELTA).
  pose proof (regex2fragment_bounds _ _ _ _ REGEX) as [START ACCEPT LT _ _].
  assert (RANGE : qi + 1 <= qi + 1 <= qf1) by lia.
  pose proof (regex2fragment_Star_delta_star_sound_aux e1 SOUND qi qf frag qf1 frag1 (qi + 1) frag.(frag_accept) s H REGEX RANGE DELTA eq_refl) as [[EQ _] | (s1 & s2 & EQ & DELTA1 & STAR)].
  - subst s. simpl. econs.
  - subst s. simpl. eapply star_app.
    + eapply SOUND; eauto. rewrite START. rewrite ACCEPT. exact DELTA1.
    + exact STAR.
Qed.

Corollary regex2fragment_sound e
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
  pose proof (delta_star_elim 0 frag.(frag_accept) s DELTA) as [NIL | [EPS | CHAR]].
  - des; subst.
    pose proof (rules2fragments_start_ge _ _ _ _ _ _ _ _ FRAGS IN_FRAG REGEX).
    lia.
  - destruct EPS as (q1 & STEP & REST).
    pose proof (eps_step_from_edges_sound _ _ _ STEP) as IN_EDGE.
    pose proof (fragment_eps_edges_start_sound _ _ _ _ _ FRAGS qi_POS IN_EDGE) as (rule' & frag' & qi_rule' & qf' & IN_FRAG' & REGEX' & START_EDGE).
    subst q1.
    pose proof (regex2fragment_bounds _ _ _ _ REGEX') as [START' ACCEPT' LT' _ _].
    assert (RANGE : qi_rule <= frag.(frag_accept) <= qf) by lia.
    assert (RANGE' : qi_rule' <= frag.(frag_accept) <= qf').
    { eapply delta_star_fragment_range with (qi := qi) (rules := rules) (qmax := qmax) (frags := frags) (rule := rule') (frag := frag') (q := frag'.(frag_start)) (s := s); eauto. lia. }
    pose proof (rules2fragments_ranges_disjoint _ _ _ _ _ _ _ _ _ _ _ _ _
      FRAGS IN_FRAG IN_FRAG' REGEX REGEX' RANGE RANGE') as EQ.
    inv EQ. eapply delta_star_global_to_fragment; eauto. lia.
  - destruct CHAR as (c & s' & q1 & EQ & STEP & REST).
    pose proof (char_step_from_edges_sound _ _ _ _ STEP) as (edge & IN_EDGE & SRC & LABEL & DST).
    pose proof (fragment_char_edges_owner _ _ _ _ _ FRAGS IN_EDGE) as (rule' & frag' & qi_rule' & qf' & IN_FRAG' & REGEX' & BOUNDS' & LE_START & LT_END & RANGE' & IN_EDGE').
    lia.
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
  - split; [reflexivity | ].
    eapply regex2fragment_sound; eauto.
    eapply fragments_delta_star_start_to_fragment; eauto.
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

End TaggedENFA.

Module TaggedDFA.

#[projections(primitive)]
Record t : Type :=
  mk
  { state : Set
  ; state_hasEqDec : hasEqDec@{Set} state
  ; states : list state
  ; start_state : state
  ; accept_states : list (state * Token.t)
  ; transition (q : state) (c : ascii) : state
  }.

#[global] Existing Instance state_hasEqDec.

Fixpoint delta (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) (s : Input.t) {struct s} : M.(TaggedDFA.state) :=
  match s with
  | [] => q
  | c :: s' => delta M (M.(TaggedDFA.transition) q c) s'
  end.

Definition accepts (M : TaggedDFA.t) (s : Input.t) (tag : Token.t) : Prop :=
  (delta M M.(TaggedDFA.start_state) s, tag) ∈ M.(TaggedDFA.accept_states).

Definition accepted_tags (M : TaggedDFA.t) (s : Input.t) : ensemble Token.t :=
  fun tag => accepts M s tag.

Definition state_reachable (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) : Prop :=
  exists s, q = delta M M.(TaggedDFA.start_state) s.

Definition all_states_reachable (M : TaggedDFA.t) : Prop :=
  forall q, q ∈ M.(TaggedDFA.states) -> state_reachable M q.

Definition language_equiv (M1 : TaggedDFA.t) (M2 : TaggedDFA.t) : Prop :=
  forall s, forall tag, accepts M1 s tag <-> accepts M2 s tag.

Variant okay (M : TaggedDFA.t) : Prop :=
  | okay_intro
    (start_okay : M.(TaggedDFA.start_state) ∈ M.(TaggedDFA.states))
    (accept_states_okay : forall q, forall tag, (q, tag) ∈ M.(TaggedDFA.accept_states) -> q ∈ M.(TaggedDFA.states))
    (transition_okay : forall q, forall c, q ∈ M.(TaggedDFA.states) -> M.(TaggedDFA.transition) q c ∈ M.(TaggedDFA.states)).

Lemma delta_app (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) (s1 : Input.t) (s2 : Input.t)
  : delta M q (s1 ++ s2) = delta M (delta M q s1) s2.
Proof.
  revert q. induction s1 as [ | c s1 IH]; intros q; simpl; eauto.
Qed.

Lemma delta_okay (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) (s : Input.t)
  (OKAY : okay M)
  (IN : q ∈ M.(TaggedDFA.states))
  : delta M q s ∈ M.(TaggedDFA.states).
Proof.
  revert q IN. induction s as [ | c s IH]; intros q IN; simpl; [exact IN | ].
  eapply IH. destruct OKAY as [_ _ TRANS_OKAY]. eapply TRANS_OKAY. exact IN.
Qed.

Section NUMBER_STATES.

Variable M : TaggedDFA.t.

#[local] Notation Q := M.(TaggedDFA.state).

Definition state_number (q : Q) : nat :=
  index_of q M.(TaggedDFA.states).

Definition numbered_state_denote (n : nat) : Q :=
  lookup M.(TaggedDFA.start_state) n M.(TaggedDFA.states).

Definition numbered_states : list nat :=
  seq 0 (length M.(TaggedDFA.states)).

Lemma numbered_states_NoDup
  : NoDup numbered_states.
Proof.
  unfold numbered_states. eapply seq_NoDup.
Qed.

Definition numbered_start_state : nat :=
  state_number M.(TaggedDFA.start_state).

Definition numbered_transition (n : nat) (c : ascii) : nat :=
  state_number (M.(TaggedDFA.transition) (numbered_state_denote n) c).

Definition numbered_accept_states : list (nat * Token.t) :=
  M.(TaggedDFA.accept_states) >>= fun '(q, tag) => [(state_number q, tag)].

Definition number_states : TaggedDFA.t :=
  {|
    state := nat;
    state_hasEqDec := nat_hasEqDec;
    states := numbered_states;
    start_state := numbered_start_state;
    accept_states := numbered_accept_states;
    transition := numbered_transition;
  |}.

Theorem number_states_states_NoDup
  : NoDup number_states.(TaggedDFA.states).
Proof.
  simpl. eapply numbered_states_NoDup.
Qed.

Lemma numbered_state_denote_state_number (q : Q)
  (IN : q ∈ M.(TaggedDFA.states))
  : numbered_state_denote (state_number q) = q.
Proof.
  unfold numbered_state_denote, state_number.
  eapply lookup_index_of. exact IN.
Qed.

Lemma numbered_state_denote_in (n : nat)
  (IN : n ∈ numbered_states)
  : numbered_state_denote n ∈ M.(TaggedDFA.states).
Proof.
  unfold numbered_states, numbered_state_denote in *.
  rewrite in_seq in IN. eapply lookup_in. lia.
Qed.

Lemma numbered_accept_states_complete (q : Q) (tag : Token.t)
  (ACCEPT : (q, tag) ∈ M.(TaggedDFA.accept_states))
  : (state_number q, tag) ∈ numbered_accept_states.
Proof.
  unfold numbered_accept_states.
  eapply list_bind_complete with (x := (q, tag)); [exact ACCEPT | ].
  simpl. left. reflexivity.
Qed.

Lemma numbered_accept_states_sound (n : nat) (tag : Token.t)
  (ACCEPT : (n, tag) ∈ numbered_accept_states)
  : exists q, (q, tag) ∈ M.(TaggedDFA.accept_states) /\ n = state_number q.
Proof.
  unfold numbered_accept_states in ACCEPT.
  pose proof (list_bind_sound _ _ _ ACCEPT) as ([q tag'] & ACCEPT' & IN).
  simpl in IN. destruct IN as [EQ | []]. inv EQ.
  exists q. eauto.
Qed.

Lemma numbered_delta (q : Q) (s : Input.t)
  (OKAY : okay M)
  (IN : q ∈ M.(TaggedDFA.states))
  : delta number_states (state_number q) s = state_number (delta M q s).
Proof.
  revert q IN. induction s as [ | c s IH]; intros q IN; simpl; [reflexivity | ].
  unfold numbered_transition.
  rewrite numbered_state_denote_state_number; [ | exact IN].
  eapply IH. destruct OKAY as [_ _ TRANS_OKAY]. eapply TRANS_OKAY. exact IN.
Qed.

Theorem number_states_sound (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : accepts number_states s tag)
  : accepts M s tag.
Proof.
  unfold accepts in ACCEPT |- *. simpl in ACCEPT.
  destruct OKAY as [START_OKAY ACCEPT_OKAY TRANS_OKAY].
  unfold numbered_start_state in ACCEPT.
  assert (NUMBERED_DELTA : delta number_states (state_number M.(TaggedDFA.start_state)) s = state_number (delta M M.(TaggedDFA.start_state) s)).
  { eapply numbered_delta; [econs; eauto | exact START_OKAY]. }
  rewrite NUMBERED_DELTA in ACCEPT.
  pose proof (numbered_accept_states_sound _ _ ACCEPT) as (q & ACCEPT_Q & EQ).
  assert (DELTA_IN : delta M M.(TaggedDFA.start_state) s ∈ M.(TaggedDFA.states)).
  { eapply delta_okay; [econs; eauto | exact START_OKAY]. }
  assert (Q_IN : q ∈ M.(TaggedDFA.states)) by (eapply ACCEPT_OKAY; exact ACCEPT_Q).
  pose proof (index_of_inj _ _ M.(TaggedDFA.states) M.(TaggedDFA.start_state) DELTA_IN Q_IN EQ) as DELTA_EQ.
  subst q. exact ACCEPT_Q.
Qed.

Theorem number_states_complete (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : accepts M s tag)
  : accepts number_states s tag.
Proof.
  unfold accepts in ACCEPT |- *. simpl.
  destruct OKAY as [START_OKAY ACCEPT_OKAY TRANS_OKAY].
  unfold numbered_start_state.
  assert (NUMBERED_DELTA : delta number_states (state_number M.(TaggedDFA.start_state)) s = state_number (delta M M.(TaggedDFA.start_state) s)).
  { eapply numbered_delta; [econs; eauto | exact START_OKAY]. }
  rewrite NUMBERED_DELTA.
  eapply numbered_accept_states_complete. exact ACCEPT.
Qed.

Theorem number_states_okay
  (OKAY : okay M)
  : okay number_states.
Proof.
  destruct OKAY as [START_OKAY ACCEPT_OKAY TRANS_OKAY].
  constructor; simpl.
  - eapply index_of_in_seq. exact START_OKAY.
  - intros n tag ACCEPT.
    pose proof (numbered_accept_states_sound n tag ACCEPT) as (q & ACCEPT_Q & EQ).
    subst n. eapply index_of_in_seq. eapply ACCEPT_OKAY. exact ACCEPT_Q.
  - intros n c IN.
    unfold numbered_transition. eapply index_of_in_seq.
    eapply TRANS_OKAY. eapply numbered_state_denote_in. exact IN.
Qed.

End NUMBER_STATES.

Section SUBSET_CONSTRUCTION.

Variable M : TaggedENFA.t.

#[local] Notation Q := M.(TaggedENFA.state).
#[local] Notation M_eclosure := (TaggedENFA.eclosure M.(TaggedENFA.eps_step)).
#[local] Notation M_delta_star := (TaggedENFA.delta_star M.(TaggedENFA.eps_step) M.(TaggedENFA.char_step)).

Definition subset_state : Set :=
  list Q.

Fixpoint iter {A : Type} (fuel : nat) (step : A -> A) (x : A) {struct fuel} : A :=
  match fuel with
  | O => x
  | S fuel' => iter fuel' step (step x)
  end.

Definition normalize (qs : subset_state) : subset_state :=
  filter (fun q => mem q qs) M.(TaggedENFA.states).

Definition move (qs : subset_state) (c : ascii) : subset_state :=
  qs >>= fun q => M.(TaggedENFA.char_step) q c.

Definition eps_move (qs : subset_state) : subset_state :=
  qs >>= M.(TaggedENFA.eps_step).

Definition eclose_step (qs : subset_state) : subset_state :=
  normalize (union (eps_move qs) qs).

Definition eclose (qs : subset_state) : subset_state :=
  iter (length M.(TaggedENFA.states)) eclose_step (normalize qs).

Lemma normalize_complete (qs : subset_state) (q : Q)
  (STATES : q ∈ M.(TaggedENFA.states))
  (IN : q ∈ qs)
  : q ∈ normalize qs.
Proof.
  unfold normalize. rewrite filter_In. split; [exact STATES | ].
  now rewrite mem_true_iff.
Qed.

Lemma normalize_sound (qs : subset_state) (q : Q)
  (IN : q ∈ normalize qs)
  : q ∈ qs /\ q ∈ M.(TaggedENFA.states).
Proof.
  unfold normalize in IN. rewrite filter_In in IN.
  destruct IN as [STATES MEM]. split; [ | exact STATES].
  now rewrite mem_true_iff in MEM.
Qed.

Lemma move_complete (qs : subset_state) (c : ascii) (q : Q) (q' : Q)
  (IN : q ∈ qs)
  (STEP : q' ∈ M.(TaggedENFA.char_step) q c)
  : q' ∈ move qs c.
Proof.
  unfold move. eapply list_bind_complete; eauto.
Qed.

Lemma move_sound (qs : subset_state) (c : ascii) (q' : Q)
  (IN : q' ∈ move qs c)
  : exists q, q ∈ qs /\ q' ∈ M.(TaggedENFA.char_step) q c.
Proof.
  unfold move in IN. eapply list_bind_sound. exact IN.
Qed.

Lemma eps_move_complete (qs : subset_state) (q : Q) (q' : Q)
  (IN : q ∈ qs)
  (STEP : q' ∈ M.(TaggedENFA.eps_step) q)
  : q' ∈ eps_move qs.
Proof.
  unfold eps_move. eapply list_bind_complete; eauto.
Qed.

Lemma eps_move_sound (qs : subset_state) (q' : Q)
  (IN : q' ∈ eps_move qs)
  : exists q, q ∈ qs /\ q' ∈ M.(TaggedENFA.eps_step) q.
Proof.
  unfold eps_move in IN. eapply list_bind_sound. exact IN.
Qed.

Lemma eclose_step_sound (qs : subset_state) (q' : Q)
  (IN : q' ∈ eclose_step qs)
  : exists q, q ∈ qs /\ q' \in M_eclosure q.
Proof.
  unfold eclose_step in IN.
  pose proof (normalize_sound _ _ IN) as [IN_UNION _].
  pose proof (union_sound _ _ _ IN_UNION) as [IN_EPS | IN_QS].
  - pose proof (eps_move_sound _ _ IN_EPS) as (q & IN_QS & STEP).
    exists q. split; [exact IN_QS | ].
    eapply TaggedENFA.eclosure_step; [exact STEP | constructor].
  - exists q'. split; [exact IN_QS | constructor].
Qed.

Lemma iter_eclose_step_sound (fuel : nat) (qs : subset_state) (q' : Q)
  (IN : q' ∈ iter fuel eclose_step qs)
  : exists q, q ∈ qs /\ q' \in M_eclosure q.
Proof.
  revert qs q' IN. induction fuel as [ | fuel IH]; intros qs q' IN; simpl in IN.
  - exists q'. split; [exact IN | constructor].
  - pose proof (IH _ _ IN) as (q1 & STEP & REST).
    pose proof (eclose_step_sound _ _ STEP) as (q0 & IN_QS & CLOS).
    exists q0. split; [exact IN_QS | ].
    eapply TaggedENFA.eclosure_trans; eauto.
Qed.

Lemma eclose_sound (qs : subset_state) (q' : Q)
  (IN : q' ∈ eclose qs)
  : exists q, q ∈ qs /\ q' \in M_eclosure q.
Proof.
  unfold eclose in IN.
  pose proof (iter_eclose_step_sound _ _ _ IN) as (q & IN_NORM & CLOS).
  pose proof (normalize_sound _ _ IN_NORM) as [IN_QS _].
  exists q. split; [exact IN_QS | exact CLOS].
Qed.

Definition eps_graph : GRAPH.t :=
  {|
    GRAPH.vertices := Q;
    GRAPH.edges := fun '(q, q') => q' ∈ M.(TaggedENFA.eps_step) q;
  |}.

#[local] Notation " src ~~~[ w ]~~> tgt " := (@walk eps_graph tgt src w) : type_scope.

Lemma eclosure_walk (q : Q) (q' : Q)
  (CLOS : q' \in M_eclosure q)
  : exists w, q ~~~[ w ]~~> q'.
Proof.
  induction CLOS as [q | q q1 q2 STEP REST IH].
  - exists []. constructor.
  - destruct IH as [w WALK]. exists (q1 :: w). econstructor; eauto.
Qed.

Lemma eps_walk_states (q : Q) (q' : Q) (w : list Q)
  (OKAY : TaggedENFA.okay M)
  (STATE : q ∈ M.(TaggedENFA.states))
  (WALK : q ~~~[ w ]~~> q')
  : forall q0, q0 ∈ w -> q0 ∈ M.(TaggedENFA.states).
Proof.
  destruct OKAY as [_ _ EPS_OKAY _].
  induction WALK as [ | q q1 w STEP REST IH]; intros q0 IN; simpl in IN; [contradiction | ].
  destruct IN as [EQ | IN].
  - subst q0. eapply EPS_OKAY; eauto.
  - eapply IH; [eapply EPS_OKAY; eauto | exact IN].
Qed.

Lemma eclose_step_complete_keep (qs : subset_state) (q : Q)
  (STATE : q ∈ M.(TaggedENFA.states))
  (IN : q ∈ qs)
  : q ∈ eclose_step qs.
Proof.
  unfold eclose_step.
  eapply normalize_complete; [exact STATE | ].
  eapply union_complete. right. exact IN.
Qed.

Lemma eclose_step_complete_edge (qs : subset_state) (q : Q) (q' : Q)
  (STATE : q' ∈ M.(TaggedENFA.states))
  (IN : q ∈ qs)
  (STEP : q' ∈ M.(TaggedENFA.eps_step) q)
  : q' ∈ eclose_step qs.
Proof.
  unfold eclose_step.
  eapply normalize_complete; [exact STATE | ].
  eapply union_complete. left.
  eapply eps_move_complete; eauto.
Qed.

Lemma iter_eclose_step_keeps (fuel : nat) (qs : subset_state) (q : Q)
  (STATE : q ∈ M.(TaggedENFA.states))
  (IN : q ∈ qs)
  : q ∈ iter fuel eclose_step qs.
Proof.
  revert qs IN. induction fuel as [ | fuel IH]; intros qs IN; simpl.
  - exact IN.
  - eapply IH. eapply eclose_step_complete_keep; eauto.
Qed.

Lemma iter_eclose_step_walk_complete (fuel : nat) (qs : subset_state) (q : Q) (q' : Q) (w : list Q)
  (OKAY : TaggedENFA.okay M)
  (QS_STATES : forall q0, q0 ∈ qs -> q0 ∈ M.(TaggedENFA.states))
  (IN : q ∈ qs)
  (WALK : q ~~~[ w ]~~> q')
  (LENGTH : length w <= fuel)
  : q' ∈ iter fuel eclose_step qs.
Proof.
  revert fuel qs IN QS_STATES LENGTH.
  induction WALK as [ | q q1 w STEP REST IH]; intros fuel qs IN QS_STATES LENGTH.
  - eapply iter_eclose_step_keeps; eauto.
  - destruct fuel as [ | fuel]; simpl in LENGTH; [lia | ].
    simpl. eapply IH.
    + eapply eclose_step_complete_edge; eauto.
      destruct OKAY as [_ _ EPS_OKAY _]. eapply EPS_OKAY; eauto.
    + intros q0 IN0. pose proof (normalize_sound _ _ IN0) as [_ STATE]. exact STATE.
    + lia.
Qed.

Lemma eclose_complete (qs : subset_state) (q : Q) (q' : Q)
  (OKAY : TaggedENFA.okay M)
  (QS_STATES : forall q0, q0 ∈ qs -> q0 ∈ M.(TaggedENFA.states))
  (IN : q ∈ qs)
  (CLOS : q' \in M_eclosure q)
  : q' ∈ eclose qs.
Proof.
  unfold eclose.
  pose proof (eclosure_walk _ _ CLOS) as [w WALK].
  pose proof (@walk_finds_path eps_graph (fun q => fun qs => match L.in_dec (@eq_dec Q M.(TaggedENFA.state_hasEqDec)) q qs with left IN => or_introl IN | right NOT_IN => or_intror NOT_IN end) q q' w WALK) as [p PATH].
  rewrite path_iff_no_dup_walk in PATH. destruct PATH as [WALK' NO_DUP].
  eapply iter_eclose_step_walk_complete with (q := q) (w := p); eauto.
  - intros q0 IN_NORM. pose proof (normalize_sound _ _ IN_NORM) as [_ STATE]. exact STATE.
  - eapply normalize_complete; [eapply QS_STATES; exact IN | exact IN].
  - eapply L.NoDup_incl_length; [exact NO_DUP | ].
    intros q0 IN_P. eapply eps_walk_states; eauto.
Qed.

Definition subset_state_okay (qs : subset_state) : Prop :=
  (forall q, q ∈ qs -> q ∈ M.(TaggedENFA.states)) /\ (forall q, forall q', q ∈ qs -> q' \in M_eclosure q -> q' ∈ qs).

Lemma eclose_closed (qs : subset_state) (q : Q) (q' : Q)
  (OKAY : TaggedENFA.okay M)
  (QS_STATES : forall q0, q0 ∈ qs -> q0 ∈ M.(TaggedENFA.states))
  (IN : q ∈ eclose qs)
  (CLOS : q' \in M_eclosure q)
  : q' ∈ eclose qs.
Proof.
  pose proof (eclose_sound _ _ IN) as (q0 & IN0 & CLOS0).
  eapply eclose_complete with (q := q0); eauto.
  eapply TaggedENFA.eclosure_trans; eauto.
Qed.

Definition subset_states : list subset_state :=
  powerset M.(TaggedENFA.states).

Lemma normalize_in_subset_states (qs : subset_state)
  : normalize qs ∈ subset_states.
Proof.
  unfold subset_states, normalize. eapply filter_in_powerset.
Qed.

Lemma eclose_step_in_subset_states (qs : subset_state)
  : eclose_step qs ∈ subset_states.
Proof.
  unfold eclose_step. eapply normalize_in_subset_states.
Qed.

Lemma iter_eclose_step_in_subset_states (fuel : nat) (qs : subset_state)
  (QS : qs ∈ subset_states)
  : iter fuel eclose_step qs ∈ subset_states.
Proof.
  revert qs QS. induction fuel as [ | fuel IH]; intros qs QS; simpl.
  - exact QS.
  - eapply IH. eapply eclose_step_in_subset_states.
Qed.

Lemma eclose_in_subset_states (qs : subset_state)
  : eclose qs ∈ subset_states.
Proof.
  unfold eclose. eapply iter_eclose_step_in_subset_states.
  eapply normalize_in_subset_states.
Qed.

Definition subset_start_state : subset_state :=
  eclose [M.(TaggedENFA.start_state)].

Definition subset_transition (qs : subset_state) (c : ascii) : subset_state :=
  eclose (move qs c).

Lemma subset_start_state_complete
  (OKAY : TaggedENFA.okay M)
  : M.(TaggedENFA.start_state) ∈ subset_start_state.
Proof.
  unfold subset_start_state.
  eapply eclose_complete with (q := M.(TaggedENFA.start_state)); eauto.
  - intros q IN. destruct OKAY as [START_OKAY _ _ _]. destruct IN as [EQ | []]. now subst q.
  - left. reflexivity.
  - constructor.
Qed.

Lemma subset_start_state_sound (q : Q)
  (IN : q ∈ subset_start_state)
  : q \in M_eclosure M.(TaggedENFA.start_state).
Proof.
  unfold subset_start_state in IN.
  pose proof (eclose_sound _ _ IN) as (q0 & IN_START & CLOS).
  destruct IN_START as [EQ | []]. subst q0. exact CLOS.
Qed.

Lemma subset_start_state_okay
  (OKAY : TaggedENFA.okay M)
  : subset_state_okay subset_start_state.
Proof.
  split.
  - intros q IN. pose proof OKAY as [START_OKAY _ _ _].
    eapply (TaggedENFA.eclosure_okay M M.(TaggedENFA.start_state) q); eauto.
    eapply subset_start_state_sound. exact IN.
  - intros q q' IN CLOS.
    eapply eclose_closed with (q := q); eauto.
    intros q0 IN0. destruct OKAY as [START_OKAY _ _ _].
    destruct IN0 as [EQ | []]. now subst q0.
Qed.

Lemma subset_transition_sound (qs : subset_state) (c : ascii) (q' : Q)
  (IN : q' ∈ subset_transition qs c)
  : exists q, exists q1, q ∈ qs /\ q1 ∈ M.(TaggedENFA.char_step) q c /\ q' \in M_eclosure q1.
Proof.
  unfold subset_transition in IN.
  pose proof (eclose_sound _ _ IN) as (q1 & IN_MOVE & CLOS).
  pose proof (move_sound _ _ _ IN_MOVE) as (q & IN_QS & STEP).
  exists q, q1. eauto.
Qed.

Lemma subset_transition_complete (qs : subset_state) (c : ascii) (q : Q) (q1 : Q) (q' : Q)
  (OKAY : TaggedENFA.okay M)
  (QS_STATES : forall q0, q0 ∈ qs -> q0 ∈ M.(TaggedENFA.states))
  (IN : q ∈ qs)
  (STEP : q1 ∈ M.(TaggedENFA.char_step) q c)
  (CLOS : q' \in M_eclosure q1)
  : q' ∈ subset_transition qs c.
Proof.
  unfold subset_transition. eapply eclose_complete with (q := q1); eauto.
  - intros q0 IN_MOVE. pose proof (move_sound _ _ _ IN_MOVE) as (q2 & IN_QS & STEP2).
    destruct OKAY as [_ _ _ CHAR_OKAY]. eapply CHAR_OKAY; eauto.
  - eapply move_complete; eauto.
Qed.

Lemma subset_transition_okay (qs : subset_state) (c : ascii)
  (OKAY : TaggedENFA.okay M)
  (QS_OKAY : subset_state_okay qs)
  : subset_state_okay (subset_transition qs c).
Proof.
  destruct QS_OKAY as [QS_STATES QS_CLOSED]. split.
  - intros q' IN.
    pose proof (subset_transition_sound _ _ _ IN) as (q & q1 & IN_QS & STEP & CLOS).
    eapply (TaggedENFA.eclosure_okay M q1 q'); eauto.
    pose proof OKAY as [_ _ _ CHAR_OKAY]. eapply CHAR_OKAY; eauto.
  - intros q q' IN CLOS.
    unfold subset_transition in *.
    eapply eclose_closed with (q := q); eauto.
    intros q0 IN_MOVE. pose proof (move_sound _ _ _ IN_MOVE) as (q2 & IN_QS & STEP).
    destruct OKAY as [_ _ _ CHAR_OKAY]. eapply CHAR_OKAY; eauto.
Qed.

Lemma subset_transition_in_subset_states (qs : subset_state) (c : ascii)
  : subset_transition qs c ∈ subset_states.
Proof.
  unfold subset_transition. eapply eclose_in_subset_states.
Qed.

Definition subset_accept_states_of (qs : subset_state) : list (subset_state * Token.t) :=
  M.(TaggedENFA.accept_states) >>= fun '(q, tag) => if mem q qs then [(qs, tag)] else [].

Definition subset_accept_states : list (subset_state * Token.t) :=
  subset_states >>= subset_accept_states_of.

Lemma subset_accept_states_of_complete (qs : subset_state) (q : Q) (tag : Token.t)
  (ACCEPT : (q, tag) ∈ M.(TaggedENFA.accept_states))
  (IN : q ∈ qs)
  : (qs, tag) ∈ subset_accept_states_of qs.
Proof.
  unfold subset_accept_states_of.
  eapply list_bind_complete with (x := (q, tag)); [exact ACCEPT | ].
  assert (MEM : mem q qs = true) by (rewrite mem_true_iff; exact IN).
  rewrite MEM. simpl. left. reflexivity.
Qed.

Lemma subset_accept_states_of_sound (qs : subset_state) (qs0 : subset_state) (tag : Token.t)
  (ACCEPT : (qs0, tag) ∈ subset_accept_states_of qs)
  : qs0 = qs /\ (exists q, (q, tag) ∈ M.(TaggedENFA.accept_states) /\ q ∈ qs).
Proof.
  unfold subset_accept_states_of in ACCEPT.
  pose proof (list_bind_sound _ _ _ ACCEPT) as ([q tag'] & ACCEPT' & IN).
  destruct (mem q qs) eqn: MEM; simpl in IN; [ | contradiction].
  destruct IN as [EQ | []]. inv EQ.
  split; [reflexivity | ].
  exists q. split; [exact ACCEPT' | now rewrite mem_true_iff in MEM].
Qed.

Lemma subset_accept_states_complete (qs : subset_state) (q : Q) (tag : Token.t)
  (QS : qs ∈ subset_states)
  (ACCEPT : (q, tag) ∈ M.(TaggedENFA.accept_states))
  (IN : q ∈ qs)
  : (qs, tag) ∈ subset_accept_states.
Proof.
  unfold subset_accept_states.
  eapply list_bind_complete with (x := qs); [exact QS | ].
  eapply subset_accept_states_of_complete; eauto.
Qed.

Lemma subset_accept_states_sound (qs : subset_state) (tag : Token.t)
  (ACCEPT : (qs, tag) ∈ subset_accept_states)
  : qs ∈ subset_states /\ (exists q, (q, tag) ∈ M.(TaggedENFA.accept_states) /\ q ∈ qs).
Proof.
  unfold subset_accept_states in ACCEPT.
  pose proof (list_bind_sound _ _ _ ACCEPT) as (qs' & QS & ACCEPT').
  pose proof (subset_accept_states_of_sound qs' qs tag ACCEPT') as (EQ & q & ACCEPT_Q & IN).
  subst qs'. eauto.
Qed.

Definition subset_construct : TaggedDFA.t :=
  {|
    state := subset_state;
    state_hasEqDec := list_hasEqDec M.(TaggedENFA.state_hasEqDec);
    states := subset_states;
    start_state := subset_start_state;
    accept_states := subset_accept_states;
    transition := subset_transition;
  |}.

Lemma subset_delta_in_subset_states (qs : subset_state) (s : Input.t)
  (QS : qs ∈ subset_states)
  : TaggedDFA.delta subset_construct qs s ∈ subset_states.
Proof.
  revert qs QS. induction s as [ | c s IH]; intros qs QS; simpl.
  - exact QS.
  - eapply IH. eapply subset_transition_in_subset_states.
Qed.

Lemma subset_delta_sound_aux (qs : subset_state) (s : Input.t) (q' : Q)
  (IN : q' ∈ TaggedDFA.delta subset_construct qs s)
  : exists q, q ∈ qs /\ q' \in M_delta_star q s.
Proof.
  revert qs q' IN. induction s as [ | c s IH]; intros qs q' IN; simpl in IN.
  - exists q'. split; [exact IN | constructor].
  - pose proof (IH _ _ IN) as (q1 & IN_TRANS & REST).
    pose proof (subset_transition_sound _ _ _ IN_TRANS) as (q0 & qchar & IN_QS & STEP & CLOS).
    exists q0. split; [exact IN_QS | ].
    eapply TaggedENFA.delta_star_char; [exact STEP | ].
    eapply (TaggedENFA.delta_star_app qchar q1 q' [] s).
    + eapply (proj2 (TaggedENFA.delta_star_iff_eclosure qchar q1)). exact CLOS.
    + exact REST.
Qed.

Theorem subset_construct_sound (s : Input.t) (tag : Token.t)
  (ACCEPT : TaggedDFA.accepts subset_construct s tag)
  : TaggedENFA.accepts M s tag.
Proof.
  unfold TaggedDFA.accepts in ACCEPT.
  pose proof (subset_accept_states_sound _ _ ACCEPT) as (_ & qf & ACCEPT_Q & IN_QS).
  unfold TaggedENFA.accepts. exists qf. split; [ | exact ACCEPT_Q].
  pose proof (subset_delta_sound_aux _ _ _ IN_QS) as (q0 & IN_START & REST).
  pose proof (subset_start_state_sound _ IN_START) as CLOS.
  eapply (TaggedENFA.delta_star_app M.(TaggedENFA.start_state) q0 qf [] s).
  - eapply (proj2 (TaggedENFA.delta_star_iff_eclosure M.(TaggedENFA.start_state) q0)). exact CLOS.
  - exact REST.
Qed.

Lemma subset_delta_complete_aux (s : Input.t) (q : Q) (q' : Q)
  (OKAY : TaggedENFA.okay M)
  (DELTA : q' \in M_delta_star q s)
  : forall qs, subset_state_okay qs -> q ∈ qs -> q' ∈ TaggedDFA.delta subset_construct qs s.
Proof.
  induction DELTA as [q | q q1 q2 s STEP REST IH | q q1 q2 c s STEP REST IH]; intros qs QS_OKAY IN; simpl.
  - exact IN.
  - eapply IH; [exact QS_OKAY | ].
    destruct QS_OKAY as [_ QS_CLOSED].
    eapply QS_CLOSED; [exact IN | ].
    eapply TaggedENFA.eclosure_step; [exact STEP | constructor].
  - eapply IH.
    + eapply subset_transition_okay; eauto.
    + eapply subset_transition_complete with (q := q) (q1 := q1); eauto.
      * destruct QS_OKAY as [QS_STATES _]. exact QS_STATES.
      * constructor.
Qed.

Theorem subset_construct_complete
  (OKAY : TaggedENFA.okay M) (s : Input.t) (tag : Token.t)
  (ACCEPT : TaggedENFA.accepts M s tag)
  : TaggedDFA.accepts subset_construct s tag.
Proof.
  unfold TaggedENFA.accepts in ACCEPT. destruct ACCEPT as [qf [DELTA ACCEPT_Q]].
  unfold TaggedDFA.accepts. simpl.
  eapply subset_accept_states_complete with (q := qf).
  - eapply subset_delta_in_subset_states. eapply eclose_in_subset_states.
  - exact ACCEPT_Q.
  - eapply subset_delta_complete_aux with (q := M.(TaggedENFA.start_state)); eauto.
    + eapply subset_start_state_okay; eauto.
    + eapply subset_start_state_complete; eauto.
Qed.

Theorem subset_construct_okay
  (OKAY : TaggedENFA.okay M)
  : okay subset_construct.
Proof.
  constructor; simpl.
  - eapply eclose_in_subset_states.
  - intros qs tag ACCEPT.
    pose proof (subset_accept_states_sound qs tag ACCEPT) as [QS _].
    exact QS.
  - intros qs c QS. eapply subset_transition_in_subset_states.
Qed.

End SUBSET_CONSTRUCTION.

Section MINIMISATION.

Variable M : TaggedDFA.t.

#[local] Notation Q := M.(TaggedDFA.state).

Definition accepts_from (q : Q) (s : Input.t) (tag : Token.t) : Prop :=
  (delta M q s, tag) ∈ M.(TaggedDFA.accept_states).

Definition right_language_equiv (q1 : Q) (q2 : Q) : Prop :=
  forall s, forall tag, accepts_from q1 s tag <-> accepts_from q2 s tag.

Definition accepting_tags_from (q : Q) : list Token.t :=
  M.(TaggedDFA.accept_states) >>= fun '(q', tag) => if eq_dec q q' then [tag] else [].

Lemma accepting_tags_from_complete (q : Q) (tag : Token.t)
  (ACCEPT : (q, tag) ∈ M.(TaggedDFA.accept_states))
  : tag ∈ accepting_tags_from q.
Proof.
  unfold accepting_tags_from.
  eapply list_bind_complete with (x := (q, tag)); [exact ACCEPT | ].
  destruct (eq_dec q q) as [_ | NE]; [simpl; left; reflexivity | contradiction NE; reflexivity].
Qed.

Lemma accepting_tags_from_sound (q : Q) (tag : Token.t)
  (ACCEPT : tag ∈ accepting_tags_from q)
  : (q, tag) ∈ M.(TaggedDFA.accept_states).
Proof.
  unfold accepting_tags_from in ACCEPT.
  pose proof (list_bind_sound _ _ _ ACCEPT) as ([q' tag'] & ACCEPT' & IN).
  destruct (eq_dec q q') as [EQ | NE]; simpl in IN; [ | contradiction].
  subst q'. destruct IN as [EQ_TAG | []]. inv EQ_TAG. exact ACCEPT'.
Qed.

Definition same_accepting_tagsb (q1 : Q) (q2 : Q) : bool :=
  forallb (fun '(_, tag) => eqb (mem (q1, tag) M.(TaggedDFA.accept_states)) (mem (q2, tag) M.(TaggedDFA.accept_states))) M.(TaggedDFA.accept_states).

Lemma same_accepting_tagsb_refl (q : Q)
  : same_accepting_tagsb q q = true.
Proof.
  unfold same_accepting_tagsb. rewrite forallb_forall.
  intros [q' tag] IN. simpl. now rewrite eqb_eq.
Qed.

Lemma same_accepting_tagsb_sound (q1 : Q) (q2 : Q) (tag : Token.t)
  (SAME : same_accepting_tagsb q1 q2 = true)
  (ACCEPT : (q1, tag) ∈ M.(TaggedDFA.accept_states))
  : (q2, tag) ∈ M.(TaggedDFA.accept_states).
Proof.
  unfold same_accepting_tagsb in SAME. rewrite forallb_forall in SAME.
  pose proof (SAME (q1, tag) ACCEPT) as EQB. simpl in EQB.
  assert (MEM1 : mem (q1, tag) M.(TaggedDFA.accept_states) = true) by (now rewrite mem_true_iff).
  rewrite MEM1 in EQB. rewrite eqb_eq in EQB.
  rewrite <- mem_true_iff. now symmetry.
Qed.

Lemma same_accepting_tagsb_complete (q1 : Q) (q2 : Q) (tag : Token.t)
  (SAME : same_accepting_tagsb q1 q2 = true)
  (ACCEPT : (q2, tag) ∈ M.(TaggedDFA.accept_states))
  : (q1, tag) ∈ M.(TaggedDFA.accept_states).
Proof.
  unfold same_accepting_tagsb in SAME. rewrite forallb_forall in SAME.
  pose proof (SAME (q2, tag) ACCEPT) as EQB. simpl in EQB.
  assert (MEM2 : mem (q2, tag) M.(TaggedDFA.accept_states) = true) by (now rewrite mem_true_iff).
  rewrite MEM2 in EQB. rewrite eqb_eq in EQB.
  rewrite <- mem_true_iff. exact EQB.
Qed.

Lemma same_accepting_tagsb_false_distinguish (q1 : Q) (q2 : Q)
  (SAME : same_accepting_tagsb q1 q2 = false)
  : exists tag, (accepts_from q1 [] tag /\ ~ accepts_from q2 [] tag) \/ (accepts_from q2 [] tag /\ ~ accepts_from q1 [] tag).
Proof.
  unfold same_accepting_tagsb in SAME.
  pose proof (forallb_false_exists _ _ SAME) as ([q tag] & _ & EQB).
  simpl in EQB.
  destruct (mem (q1, tag) M.(TaggedDFA.accept_states)) eqn: MEM1, (mem (q2, tag) M.(TaggedDFA.accept_states)) eqn: MEM2; simpl in EQB; inv EQB.
  - exists tag. left. split.
    + unfold accepts_from. simpl. rewrite <- mem_true_iff. exact MEM1.
    + unfold accepts_from. simpl. rewrite <- mem_false_iff. exact MEM2.
  - exists tag. right. split.
    + unfold accepts_from. simpl. rewrite <- mem_true_iff. exact MEM2.
    + unfold accepts_from. simpl. rewrite <- mem_false_iff. exact MEM1.
Qed.

Fixpoint minimisation_equivb (fuel : nat) (q1 : Q) (q2 : Q) {struct fuel} : bool :=
  match fuel with
  | O => same_accepting_tagsb q1 q2
  | S fuel' => same_accepting_tagsb q1 q2 && forallb (fun c => minimisation_equivb fuel' (M.(TaggedDFA.transition) q1 c) (M.(TaggedDFA.transition) q2 c)) all_asciis
  end.

Definition minimisation_pair_states : list (Q * Q) :=
  M.(TaggedDFA.states) >>= fun q1 => map (fun q2 => (q1, q2)) M.(TaggedDFA.states).

Definition minimisation_fuel : nat :=
  length minimisation_pair_states.

Definition minimisation_equiv (q1 : Q) (q2 : Q) : Prop :=
  minimisation_equivb minimisation_fuel q1 q2 = true.

Lemma minimisation_equivb_refl (fuel : nat) (q : Q)
  : minimisation_equivb fuel q q = true.
Proof.
  revert q. induction fuel as [ | fuel IH]; intros q.
  - cbn [minimisation_equivb]. eapply same_accepting_tagsb_refl.
  - cbn [minimisation_equivb]. rewrite same_accepting_tagsb_refl.
    change (forallb (fun c => minimisation_equivb fuel (M.(TaggedDFA.transition) q c) (M.(TaggedDFA.transition) q c)) all_asciis = true).
    rewrite forallb_forall. intros c IN. eapply IH.
Qed.

Lemma minimisation_equivb_same_accepting_tagsb (fuel : nat) (q1 : Q) (q2 : Q)
  (EQUIV : minimisation_equivb fuel q1 q2 = true)
  : same_accepting_tagsb q1 q2 = true.
Proof.
  destruct fuel as [ | fuel]; simpl in EQUIV; [exact EQUIV | ].
  now rewrite andb_true_iff in EQUIV.
Qed.

Lemma minimisation_equivb_accepts_from_sound (fuel : nat) (q1 : Q) (q2 : Q) (s : Input.t) (tag : Token.t)
  (LENGTH : length s <= fuel)
  (EQUIV : minimisation_equivb fuel q1 q2 = true)
  (ACCEPT : accepts_from q1 s tag)
  : accepts_from q2 s tag.
Proof.
  revert fuel q1 q2 LENGTH EQUIV ACCEPT.
  induction s as [ | c s IH]; intros fuel q1 q2 LENGTH EQUIV ACCEPT.
  - eapply same_accepting_tagsb_sound; [ | exact ACCEPT].
    eapply minimisation_equivb_same_accepting_tagsb. exact EQUIV.
  - destruct fuel as [ | fuel]; simpl in LENGTH; [lia | ].
    cbn [minimisation_equivb] in EQUIV. rewrite andb_true_iff in EQUIV. destruct EQUIV as [_ EQUIV].
    simpl in ACCEPT |- *.
    eapply (IH fuel (M.(TaggedDFA.transition) q1 c) (M.(TaggedDFA.transition) q2 c)); [lia | | exact ACCEPT].
    rewrite forallb_forall in EQUIV. eapply EQUIV. eapply all_asciis_complete.
Qed.

Lemma minimisation_equivb_accepts_from_complete (fuel : nat) (q1 : Q) (q2 : Q) (s : Input.t) (tag : Token.t)
  (LENGTH : length s <= fuel)
  (EQUIV : minimisation_equivb fuel q1 q2 = true)
  (ACCEPT : accepts_from q2 s tag)
  : accepts_from q1 s tag.
Proof.
  revert fuel q1 q2 LENGTH EQUIV ACCEPT.
  induction s as [ | c s IH]; intros fuel q1 q2 LENGTH EQUIV ACCEPT.
  - eapply same_accepting_tagsb_complete; [ | exact ACCEPT].
    eapply minimisation_equivb_same_accepting_tagsb. exact EQUIV.
  - destruct fuel as [ | fuel]; simpl in LENGTH; [lia | ].
    cbn [minimisation_equivb] in EQUIV. rewrite andb_true_iff in EQUIV. destruct EQUIV as [_ EQUIV].
    simpl in ACCEPT |- *.
    eapply (IH fuel (M.(TaggedDFA.transition) q1 c) (M.(TaggedDFA.transition) q2 c)); [lia | | exact ACCEPT].
    rewrite forallb_forall in EQUIV. eapply EQUIV. eapply all_asciis_complete.
Qed.

Lemma minimisation_equivb_false_distinguish (fuel : nat) (q1 : Q) (q2 : Q)
  (EQUIV : minimisation_equivb fuel q1 q2 = false)
  : exists s, exists tag, length s <= fuel /\ ((accepts_from q1 s tag /\ ~ accepts_from q2 s tag) \/ (accepts_from q2 s tag /\ ~ accepts_from q1 s tag)).
Proof.
  revert q1 q2 EQUIV. induction fuel as [ | fuel IH]; intros q1 q2 EQUIV.
  - cbn [minimisation_equivb] in EQUIV.
    pose proof (same_accepting_tagsb_false_distinguish q1 q2 EQUIV) as (tag & DIFF).
    exists (@nil ascii). exists tag. simpl. split; [lia | exact DIFF].
  - cbn [minimisation_equivb] in EQUIV. rewrite andb_false_iff in EQUIV.
    destruct EQUIV as [SAME | TRANS].
    + pose proof (same_accepting_tagsb_false_distinguish q1 q2 SAME) as (tag & DIFF).
      exists (@nil ascii). exists tag. simpl. split; [lia | exact DIFF].
    + pose proof (forallb_false_exists _ _ TRANS) as (c & _ & EQUIV_C).
      pose proof (IH _ _ EQUIV_C) as (s & tag & LENGTH & DIFF).
      exists (c :: s). exists tag. simpl. split; [lia | exact DIFF].
Qed.

Definition minimisation_pair_transition (qq : Q * Q) (c : ascii) : Q * Q :=
  (M.(TaggedDFA.transition) (fst qq) c, M.(TaggedDFA.transition) (snd qq) c).

Fixpoint minimisation_pair_delta (qq : Q * Q) (s : Input.t) {struct s} : Q * Q :=
  match s with
  | [] => qq
  | c :: s' => minimisation_pair_delta (minimisation_pair_transition qq c) s'
  end.

Fixpoint minimisation_pair_trace (qq : Q * Q) (s : Input.t) {struct s} : list (Q * Q) :=
  match s with
  | [] => []
  | c :: s' =>
    let qq' := minimisation_pair_transition qq c in
    qq' :: minimisation_pair_trace qq' s'
  end.

Definition minimisation_pair_graph : GRAPH.t :=
  {|
    GRAPH.vertices := Q * Q;
    GRAPH.edges := fun '(qq, qq') => exists c, qq' = minimisation_pair_transition qq c;
  |}.

#[local] Notation " src ~~~[ w ]~~> tgt " := (@walk minimisation_pair_graph tgt src w) : type_scope.

Lemma minimisation_pair_delta_spec (q1 : Q) (q2 : Q) (s : Input.t)
  : minimisation_pair_delta (q1, q2) s = (delta M q1 s, delta M q2 s).
Proof.
  revert q1 q2. induction s as [ | c s IH]; intros q1 q2; simpl; eauto.
Qed.

Lemma minimisation_pair_trace_walk (qq : Q * Q) (s : Input.t)
  : qq ~~~[ minimisation_pair_trace qq s ]~~> minimisation_pair_delta qq s.
Proof.
  revert qq. induction s as [ | c s IH]; intros qq; simpl.
  - constructor.
  - econstructor; [exists c; reflexivity | eapply IH].
Qed.

Lemma minimisation_pair_states_complete (q1 : Q) (q2 : Q)
  (IN1 : q1 ∈ M.(TaggedDFA.states))
  (IN2 : q2 ∈ M.(TaggedDFA.states))
  : (q1, q2) ∈ minimisation_pair_states.
Proof.
  unfold minimisation_pair_states.
  eapply list_bind_complete with (x := q1); [exact IN1 | ].
  rewrite in_map_iff. exists q2. split; [reflexivity | exact IN2].
Qed.

Lemma minimisation_pair_walk_states (qq : Q * Q) (qq' : Q * Q) (w : list (Q * Q))
  (OKAY : okay M)
  (STATE1 : fst qq ∈ M.(TaggedDFA.states))
  (STATE2 : snd qq ∈ M.(TaggedDFA.states))
  (WALK : qq ~~~[ w ]~~> qq')
  : forall qq0, qq0 ∈ w -> (fst qq0 ∈ M.(TaggedDFA.states) /\ snd qq0 ∈ M.(TaggedDFA.states)).
Proof.
  destruct OKAY as [_ _ TRANS_OKAY].
  induction WALK as [ | qq qq1 w EDGE REST IH]; intros qq0 IN; simpl in IN; [contradiction | ].
  destruct IN as [EQ | IN].
  - subst qq0. destruct EDGE as [c EQ]. subst qq1. simpl.
    split; eapply TRANS_OKAY; eauto.
  - eapply IH; [ | | exact IN].
    + destruct EDGE as [c EQ]. subst qq1. simpl. eapply TRANS_OKAY. exact STATE1.
    + destruct EDGE as [c EQ]. subst qq1. simpl. eapply TRANS_OKAY. exact STATE2.
Qed.

Lemma minimisation_equivb_step (fuel : nat) (q1 : Q) (q2 : Q) (c : ascii)
  (EQUIV : minimisation_equivb (S fuel) q1 q2 = true)
  : minimisation_equivb fuel (M.(TaggedDFA.transition) q1 c) (M.(TaggedDFA.transition) q2 c) = true.
Proof.
  cbn [minimisation_equivb] in EQUIV. rewrite andb_true_iff in EQUIV.
  destruct EQUIV as [_ EQUIV]. rewrite forallb_forall in EQUIV.
  eapply EQUIV. eapply all_asciis_complete.
Qed.

Lemma minimisation_equivb_walk_same_accepting_tagsb (fuel : nat) (qq : Q * Q) (qq' : Q * Q) (w : list (Q * Q))
  (WALK : qq ~~~[ w ]~~> qq')
  (LENGTH : length w <= fuel)
  (EQUIV : minimisation_equivb fuel (fst qq) (snd qq) = true)
  : same_accepting_tagsb (fst qq') (snd qq') = true.
Proof.
  revert fuel LENGTH EQUIV.
  induction WALK as [ | qq qq1 w EDGE REST IH]; intros fuel LENGTH EQUIV.
  - eapply minimisation_equivb_same_accepting_tagsb. exact EQUIV.
  - destruct fuel as [ | fuel]; simpl in LENGTH; [lia | ].
    destruct qq as [q1 q2], qq1 as [q1' q2']; cbn [fst snd] in *.
    destruct EDGE as [c EQ]. inv EQ.
    eapply (IH fuel); [lia | ].
    eapply minimisation_equivb_step. exact EQUIV.
Qed.

Lemma minimisation_equivb_same_accepting_tagsb_unbounded (q1 : Q) (q2 : Q) (s : Input.t)
  (OKAY : okay M)
  (STATE1 : q1 ∈ M.(TaggedDFA.states))
  (STATE2 : q2 ∈ M.(TaggedDFA.states))
  (EQUIV : minimisation_equivb minimisation_fuel q1 q2 = true)
  : same_accepting_tagsb (delta M q1 s) (delta M q2 s) = true.
Proof.
  pose proof (minimisation_pair_trace_walk (q1, q2) s) as WALK.
  rewrite minimisation_pair_delta_spec in WALK.
  pose proof (@walk_finds_path minimisation_pair_graph (fun qq => fun qs => match L.in_dec (@eq_dec (Q * Q) _) qq qs with left IN => or_introl IN | right NOT_IN => or_intror NOT_IN end) (q1, q2) (delta M q1 s, delta M q2 s) _ WALK) as [p PATH].
  rewrite path_iff_no_dup_walk in PATH. destruct PATH as [WALK' NO_DUP].
  eapply (minimisation_equivb_walk_same_accepting_tagsb minimisation_fuel (q1, q2) (delta M q1 s, delta M q2 s) p); eauto.
  eapply L.NoDup_incl_length; [exact NO_DUP | intros qq IN].
  pose proof (minimisation_pair_walk_states (q1, q2) (delta M q1 s, delta M q2 s) p OKAY STATE1 STATE2 WALK' qq IN) as [IN1 IN2].
  destruct qq as [qq1 qq2]; simpl in *.
  eapply minimisation_pair_states_complete; eauto.
Qed.

Lemma minimisation_equivb_accepts_from_sound_unbounded (q1 : Q) (q2 : Q) (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (STATE1 : q1 ∈ M.(TaggedDFA.states))
  (STATE2 : q2 ∈ M.(TaggedDFA.states))
  (EQUIV : minimisation_equivb minimisation_fuel q1 q2 = true)
  (ACCEPT : accepts_from q1 s tag)
  : accepts_from q2 s tag.
Proof.
  eapply same_accepting_tagsb_sound; [ | exact ACCEPT].
  eapply minimisation_equivb_same_accepting_tagsb_unbounded; eauto.
Qed.

Lemma minimisation_equivb_accepts_from_complete_unbounded (q1 : Q) (q2 : Q) (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (STATE1 : q1 ∈ M.(TaggedDFA.states))
  (STATE2 : q2 ∈ M.(TaggedDFA.states))
  (EQUIV : minimisation_equivb minimisation_fuel q1 q2 = true)
  (ACCEPT : accepts_from q2 s tag)
  : accepts_from q1 s tag.
Proof.
  eapply same_accepting_tagsb_complete; [ | exact ACCEPT].
  eapply minimisation_equivb_same_accepting_tagsb_unbounded; eauto.
Qed.

Lemma minimisation_equivb_right_language_equiv (q1 : Q) (q2 : Q)
  (OKAY : okay M)
  (STATE1 : q1 ∈ M.(TaggedDFA.states))
  (STATE2 : q2 ∈ M.(TaggedDFA.states))
  (EQUIV : minimisation_equivb minimisation_fuel q1 q2 = true)
  : right_language_equiv q1 q2.
Proof.
  intros s tag. split; intro ACCEPT.
  - eapply minimisation_equivb_accepts_from_sound_unbounded with (q1 := q1) (q2 := q2); eauto.
  - eapply minimisation_equivb_accepts_from_complete_unbounded with (q1 := q1) (q2 := q2); eauto.
Qed.

Lemma right_language_equiv_minimisation_equivb (q1 : Q) (q2 : Q)
  (SAME : right_language_equiv q1 q2)
  : minimisation_equivb minimisation_fuel q1 q2 = true.
Proof.
  destruct (minimisation_equivb minimisation_fuel q1 q2) eqn: EQUIV; [reflexivity | ].
  pose proof (minimisation_equivb_false_distinguish _ _ _ EQUIV) as (s & tag & _ & [(ACCEPT & NOT_ACCEPT) | (ACCEPT & NOT_ACCEPT)]).
  - pose proof (proj1 (SAME s tag) ACCEPT). contradiction.
  - pose proof (proj2 (SAME s tag) ACCEPT). contradiction.
Qed.

Definition minimised_state : Set :=
  list Q.

#[local]
Instance minimised_state_hasEqDec : hasEqDec minimised_state :=
  list_hasEqDec M.(TaggedDFA.state_hasEqDec).

Definition minimisation_class (q : Q) : minimised_state :=
  filter (minimisation_equivb minimisation_fuel q) M.(TaggedDFA.states).

Lemma minimisation_class_contains (q : Q)
  (IN : q ∈ M.(TaggedDFA.states))
  : q ∈ minimisation_class q.
Proof.
  unfold minimisation_class. rewrite filter_In. split; [exact IN | ].
  eapply minimisation_equivb_refl.
Qed.

Lemma minimisation_class_eq_of_right_language (q1 : Q) (q2 : Q)
  (OKAY : okay M)
  (STATE1 : q1 ∈ M.(TaggedDFA.states))
  (STATE2 : q2 ∈ M.(TaggedDFA.states))
  (SAME : right_language_equiv q1 q2)
  : minimisation_class q1 = minimisation_class q2.
Proof.
  unfold minimisation_class. eapply L.filter_ext_in. intros q STATE.
  destruct (minimisation_equivb minimisation_fuel q1 q) eqn: EQUIV1, (minimisation_equivb minimisation_fuel q2 q) eqn: EQUIV2; try reflexivity.
  - assert (SAME2 : right_language_equiv q2 q).
    { pose proof (minimisation_equivb_right_language_equiv q1 q OKAY STATE1 STATE EQUIV1) as SAME1.
      intros s tag. split; intro ACCEPT.
      - eapply (proj1 (SAME1 s tag)). eapply (proj2 (SAME s tag)). exact ACCEPT.
      - eapply (proj1 (SAME s tag)). eapply (proj2 (SAME1 s tag)). exact ACCEPT.
    }
    exfalso. pose proof (right_language_equiv_minimisation_equivb q2 q SAME2) as EQUIV.
    rewrite EQUIV2 in EQUIV. inv EQUIV.
  - assert (SAME1 : right_language_equiv q1 q).
    { pose proof (minimisation_equivb_right_language_equiv q2 q OKAY STATE2 STATE EQUIV2) as SAME2.
      intros s tag. split; intro ACCEPT.
      - eapply (proj1 (SAME2 s tag)). eapply (proj1 (SAME s tag)). exact ACCEPT.
      - eapply (proj2 (SAME s tag)). eapply (proj2 (SAME2 s tag)). exact ACCEPT.
    }
    exfalso.
    pose proof (right_language_equiv_minimisation_equivb q1 q SAME1) as EQUIV.
    rewrite EQUIV1 in EQUIV. inv EQUIV.
Qed.

Definition minimised_states : list minimised_state :=
  L.nodup eq_dec (map minimisation_class M.(TaggedDFA.states)).

Definition representative (qs : minimised_state) : Q :=
  match qs with
  | [] => M.(TaggedDFA.start_state)
  | q :: _ => q
  end.

Definition minimised_start_state : minimised_state :=
  minimisation_class M.(TaggedDFA.start_state).

Lemma minimisation_class_representative_state (q : Q)
  (IN : q ∈ M.(TaggedDFA.states))
  : representative (minimisation_class q) ∈ M.(TaggedDFA.states).
Proof.
  destruct (minimisation_class q) as [ | q0 qs] eqn: CLASS.
  - pose proof (minimisation_class_contains q IN) as IN_CLASS.
    rewrite CLASS in IN_CLASS. contradiction.
  - simpl. assert (IN_CLASS : q0 ∈ minimisation_class q) by (rewrite CLASS; left; reflexivity).
    unfold minimisation_class in IN_CLASS. rewrite filter_In in IN_CLASS. tauto.
Qed.

Lemma representative_minimisation_class_equiv (q : Q)
  (IN : q ∈ M.(TaggedDFA.states))
  : minimisation_equivb minimisation_fuel q (representative (minimisation_class q)) = true.
Proof.
  destruct (minimisation_class q) as [ | q0 qs] eqn: CLASS.
  - pose proof (minimisation_class_contains q IN) as IN_CLASS.
    rewrite CLASS in IN_CLASS. contradiction.
  - simpl. assert (IN_CLASS : q0 ∈ minimisation_class q) by (rewrite CLASS; left; reflexivity).
    unfold minimisation_class in IN_CLASS. rewrite filter_In in IN_CLASS. tauto.
Qed.

Lemma minimisation_class_in_minimised_states (q : Q)
  (IN : q ∈ M.(TaggedDFA.states))
  : minimisation_class q ∈ minimised_states.
Proof.
  unfold minimised_states. rewrite L.nodup_In, in_map_iff.
  exists q. split; [reflexivity | exact IN].
Qed.

Lemma minimised_states_NoDup
  : NoDup minimised_states.
Proof.
  unfold minimised_states. eapply L.NoDup_nodup.
Qed.

Lemma minimised_states_representative_state (qs : minimised_state)
  (QS : qs ∈ minimised_states)
  : representative qs ∈ M.(TaggedDFA.states).
Proof.
  unfold minimised_states in QS. rewrite L.nodup_In in QS. rewrite in_map_iff in QS.
  destruct QS as (q & EQ & IN). subst qs.
  eapply minimisation_class_representative_state. exact IN.
Qed.

Lemma minimised_state_eq_minimisation_class_representative (qs : minimised_state)
  (OKAY : okay M)
  (QS : qs ∈ minimised_states)
  : qs = minimisation_class (representative qs).
Proof.
  unfold minimised_states in QS. rewrite L.nodup_In in QS. rewrite in_map_iff in QS.
  destruct QS as (q & EQ & IN). subst qs.
  eapply minimisation_class_eq_of_right_language.
  - exact OKAY.
  - exact IN.
  - eapply minimisation_class_representative_state. exact IN.
  - eapply minimisation_equivb_right_language_equiv.
    + exact OKAY.
    + exact IN.
    + eapply minimisation_class_representative_state. exact IN.
    + eapply representative_minimisation_class_equiv. exact IN.
Qed.

Lemma minimised_states_eq_of_representative_right_language (qs1 : minimised_state) (qs2 : minimised_state)
  (OKAY : okay M)
  (QS1 : qs1 ∈ minimised_states)
  (QS2 : qs2 ∈ minimised_states)
  (SAME : right_language_equiv (representative qs1) (representative qs2))
  : qs1 = qs2.
Proof.
  rewrite (minimised_state_eq_minimisation_class_representative qs1 OKAY QS1).
  rewrite (minimised_state_eq_minimisation_class_representative qs2 OKAY QS2).
  eapply minimisation_class_eq_of_right_language.
  - exact OKAY.
  - eapply minimised_states_representative_state. exact QS1.
  - eapply minimised_states_representative_state. exact QS2.
  - exact SAME.
Qed.

Lemma minimised_start_state_in_minimised_states
  (OKAY : okay M)
  : minimised_start_state ∈ minimised_states.
Proof.
  destruct OKAY as [START_OKAY _ _].
  unfold minimised_start_state. eapply minimisation_class_in_minimised_states. exact START_OKAY.
Qed.

Definition minimised_transition (qs : minimised_state) (c : ascii) : minimised_state :=
  minimisation_class (M.(TaggedDFA.transition) (representative qs) c).

Lemma minimised_transition_in_minimised_states (qs : minimised_state) (c : ascii)
  (OKAY : okay M)
  (QS : qs ∈ minimised_states)
  : minimised_transition qs c ∈ minimised_states.
Proof.
  unfold minimised_transition. eapply minimisation_class_in_minimised_states.
  destruct OKAY as [_ _ TRANS_OKAY]. eapply TRANS_OKAY.
  eapply minimised_states_representative_state. exact QS.
Qed.

Definition minimised_accept_states_of (qs : minimised_state) : list (minimised_state * Token.t) :=
  accepting_tags_from (representative qs) >>= fun tag => [(qs, tag)].

Definition minimised_accept_states : list (minimised_state * Token.t) :=
  minimised_states >>= minimised_accept_states_of.

Lemma minimised_accept_states_of_complete (qs : minimised_state) (tag : Token.t)
  (ACCEPT : (representative qs, tag) ∈ M.(TaggedDFA.accept_states))
  : (qs, tag) ∈ minimised_accept_states_of qs.
Proof.
  unfold minimised_accept_states_of.
  eapply list_bind_complete with (x := tag); [ | simpl; left; reflexivity].
  eapply accepting_tags_from_complete. exact ACCEPT.
Qed.

Lemma minimised_accept_states_of_sound (qs : minimised_state) (qs0 : minimised_state) (tag : Token.t)
  (ACCEPT : (qs0, tag) ∈ minimised_accept_states_of qs)
  : qs0 = qs /\ (representative qs, tag) ∈ M.(TaggedDFA.accept_states).
Proof.
  unfold minimised_accept_states_of in ACCEPT.
  pose proof (list_bind_sound _ _ _ ACCEPT) as (tag' & ACCEPT' & IN).
  simpl in IN. destruct IN as [EQ | []]. inv EQ.
  split; [reflexivity | ].
  eapply accepting_tags_from_sound. exact ACCEPT'.
Qed.

Lemma minimised_accept_states_complete (qs : minimised_state) (tag : Token.t)
  (QS : qs ∈ minimised_states)
  (ACCEPT : (representative qs, tag) ∈ M.(TaggedDFA.accept_states))
  : (qs, tag) ∈ minimised_accept_states.
Proof.
  unfold minimised_accept_states.
  eapply list_bind_complete with (x := qs); [exact QS | ].
  eapply minimised_accept_states_of_complete. exact ACCEPT.
Qed.

Lemma minimised_accept_states_sound (qs : minimised_state) (tag : Token.t)
  (ACCEPT : (qs, tag) ∈ minimised_accept_states)
  : qs ∈ minimised_states /\ (representative qs, tag) ∈ M.(TaggedDFA.accept_states).
Proof.
  unfold minimised_accept_states in ACCEPT.
  pose proof (list_bind_sound _ _ _ ACCEPT) as (qs' & QS & ACCEPT').
  pose proof (minimised_accept_states_of_sound qs' qs tag ACCEPT') as (EQ & ACCEPT_Q).
  subst qs'. eauto.
Qed.

Definition minimise : TaggedDFA.t :=
  {|
    state := minimised_state;
    state_hasEqDec := list_hasEqDec M.(TaggedDFA.state_hasEqDec);
    states := minimised_states;
    start_state := minimised_start_state;
    accept_states := minimised_accept_states;
    transition := minimised_transition;
  |}.

Lemma minimised_accept_sound_aux (qs : minimised_state) (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (QS : qs ∈ minimised_states)
  (ACCEPT : (TaggedDFA.delta minimise qs s, tag) ∈ minimised_accept_states)
  : accepts_from (representative qs) s tag.
Proof.
  revert qs QS ACCEPT.
  induction s as [ | c s IH]; intros qs QS ACCEPT; simpl in ACCEPT.
  - pose proof (minimised_accept_states_sound _ _ ACCEPT) as [_ ACCEPT'].
    exact ACCEPT'.
  - set (qs' := minimised_transition qs c) in *.
    assert (QS' : qs' ∈ minimised_states).
    { subst qs'. eapply minimised_transition_in_minimised_states; eauto. }
    pose proof (IH qs' QS' ACCEPT) as ACCEPT_REP.
    assert (STATE1 : M.(TaggedDFA.transition) (representative qs) c ∈ M.(TaggedDFA.states)).
    { destruct OKAY as [_ _ TRANS_OKAY]. eapply TRANS_OKAY. eapply minimised_states_representative_state. exact QS. }
    assert (STATE2 : representative qs' ∈ M.(TaggedDFA.states)).
    { eapply minimised_states_representative_state. exact QS'. }
    assert (EQUIV : minimisation_equivb minimisation_fuel (M.(TaggedDFA.transition) (representative qs) c) (representative qs') = true).
    { subst qs'. unfold minimised_transition. eapply representative_minimisation_class_equiv. exact STATE1. }
    eapply minimisation_equivb_accepts_from_complete_unbounded with (q1 := M.(TaggedDFA.transition) (representative qs) c) (q2 := representative qs'); eauto.
Qed.

Lemma minimised_accept_complete_aux (qs : minimised_state) (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (QS : qs ∈ minimised_states)
  (ACCEPT : accepts_from (representative qs) s tag)
  : (TaggedDFA.delta minimise qs s, tag) ∈ minimised_accept_states.
Proof.
  revert qs QS ACCEPT.
  induction s as [ | c s IH]; intros qs QS ACCEPT; simpl in ACCEPT |- *.
  - eapply minimised_accept_states_complete; eauto.
  - set (qs' := minimised_transition qs c) in *.
    assert (QS' : qs' ∈ minimised_states).
    { subst qs'. eapply minimised_transition_in_minimised_states; eauto. }
    eapply IH; [exact QS' | ].
    assert (STATE1 : M.(TaggedDFA.transition) (representative qs) c ∈ M.(TaggedDFA.states)).
    { destruct OKAY as [_ _ TRANS_OKAY]. eapply TRANS_OKAY. eapply minimised_states_representative_state. exact QS. }
    assert (STATE2 : representative qs' ∈ M.(TaggedDFA.states)).
    { eapply minimised_states_representative_state. exact QS'. }
    assert (EQUIV : minimisation_equivb minimisation_fuel (M.(TaggedDFA.transition) (representative qs) c) (representative qs') = true).
    { subst qs'. unfold minimised_transition. eapply representative_minimisation_class_equiv. exact STATE1. }
    eapply minimisation_equivb_accepts_from_sound_unbounded with (q1 := M.(TaggedDFA.transition) (representative qs) c) (q2 := representative qs'); eauto.
Qed.

Theorem minimise_sound (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : TaggedDFA.accepts minimise s tag)
  : TaggedDFA.accepts M s tag.
Proof.
  unfold TaggedDFA.accepts in ACCEPT |- *. simpl in ACCEPT.
  pose proof (minimised_start_state_in_minimised_states OKAY) as QS_START.
  pose proof (minimised_accept_sound_aux minimised_start_state s tag OKAY QS_START ACCEPT) as ACCEPT_REP.
  assert (STATE1 : M.(TaggedDFA.start_state) ∈ M.(TaggedDFA.states)).
  { destruct OKAY as [START_OKAY _ _]. exact START_OKAY. }
  assert (STATE2 : representative minimised_start_state ∈ M.(TaggedDFA.states)).
  { eapply minimised_states_representative_state. exact QS_START. }
  assert (EQUIV : minimisation_equivb minimisation_fuel M.(TaggedDFA.start_state) (representative minimised_start_state) = true).
  { unfold minimised_start_state. eapply representative_minimisation_class_equiv. exact STATE1. }
  eapply minimisation_equivb_accepts_from_complete_unbounded with (q1 := M.(TaggedDFA.start_state)) (q2 := representative minimised_start_state); eauto.
Qed.

Theorem minimise_complete (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : TaggedDFA.accepts M s tag)
  : TaggedDFA.accepts minimise s tag.
Proof.
  unfold TaggedDFA.accepts in ACCEPT |- *. simpl.
  pose proof (minimised_start_state_in_minimised_states OKAY) as QS_START.
  eapply minimised_accept_complete_aux; [exact OKAY | exact QS_START | ].
  assert (STATE1 : M.(TaggedDFA.start_state) ∈ M.(TaggedDFA.states)).
  { destruct OKAY as [START_OKAY _ _]. exact START_OKAY. }
  assert (STATE2 : representative minimised_start_state ∈ M.(TaggedDFA.states)).
  { eapply minimised_states_representative_state. exact QS_START. }
  assert (EQUIV : minimisation_equivb minimisation_fuel M.(TaggedDFA.start_state) (representative minimised_start_state) = true).
  { unfold minimised_start_state. eapply representative_minimisation_class_equiv. exact STATE1. }
  eapply minimisation_equivb_accepts_from_sound_unbounded with (q1 := M.(TaggedDFA.start_state)) (q2 := representative minimised_start_state); eauto.
Qed.

Theorem minimise_okay
  (OKAY : okay M)
  : okay minimise.
Proof.
  split; simpl.
  - eapply minimised_start_state_in_minimised_states. exact OKAY.
  - intros qs tag ACCEPT. pose proof (minimised_accept_states_sound qs tag ACCEPT) as [QS _]. exact QS.
  - intros qs c QS. eapply minimised_transition_in_minimised_states; eauto.
Qed.

Definition minimise_numbered : TaggedDFA.t :=
  number_states minimise.

Theorem minimise_numbered_sound (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : TaggedDFA.accepts minimise_numbered s tag)
  : TaggedDFA.accepts M s tag.
Proof.
  pose proof (minimise_okay OKAY) as OKAY_MIN.
  pose proof (number_states_sound minimise s tag OKAY_MIN ACCEPT) as ACCEPT_MIN.
  eapply minimise_sound; eauto.
Qed.

Theorem minimise_numbered_complete (s : Input.t) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : TaggedDFA.accepts M s tag)
  : TaggedDFA.accepts minimise_numbered s tag.
Proof.
  pose proof (minimise_okay OKAY) as OKAY_MIN.
  eapply number_states_complete; [exact OKAY_MIN | eapply minimise_complete; eauto].
Qed.

Theorem minimise_numbered_okay
  (OKAY : okay M)
  : okay minimise_numbered.
Proof.
  eapply number_states_okay. eapply minimise_okay. exact OKAY.
Qed.

Theorem minimise_states_minimal (N : TaggedDFA.t)
  (OKAY : okay M)
  (REACHABLE : all_states_reachable M)
  (OKAY_N : okay N)
  (NODUP_N : NoDup N.(TaggedDFA.states))
  (EQUIV : language_equiv M N)
  : length minimise.(TaggedDFA.states) <= length N.(TaggedDFA.states).
Proof.
  cbn [states minimise].
  eapply @NoDup_exists_injective_length with (R := fun qs => fun n => exists s, representative qs = delta M M.(TaggedDFA.start_state) s /\ n = delta N N.(TaggedDFA.start_state) s).
  - exact N.(TaggedDFA.state_hasEqDec).
  - eapply minimised_states_NoDup.
  - intros qs QS.
    pose proof (minimised_states_representative_state qs QS) as STATE.
    pose proof (REACHABLE _ STATE) as (s & EQ).
    exists (delta N N.(TaggedDFA.start_state) s). split.
    + eapply delta_okay.
      * exact OKAY_N.
      * destruct OKAY_N as [START_OKAY _ _]. exact START_OKAY.
    + exists s. split; [exact EQ | reflexivity].
  - intros qs1 qs2 n QS1 QS2 R1 R2.
    destruct R1 as (s1 & EQ1 & EQN1).
    destruct R2 as (s2 & EQ2 & EQN2).
    eapply minimised_states_eq_of_representative_right_language; eauto.
    intros s tag. split; intro ACCEPT.
    + assert (ACCEPT_M1 : accepts M (s1 ++ s) tag).
      { unfold accepts, accepts_from in *. rewrite delta_app. rewrite <- EQ1. exact ACCEPT. }
      pose proof (proj1 (EQUIV (s1 ++ s) tag) ACCEPT_M1) as ACCEPT_N1.
      assert (ACCEPT_N2 : accepts N (s2 ++ s) tag).
      { unfold accepts in ACCEPT_N1 |- *. rewrite !delta_app in *. rewrite <- EQN1 in ACCEPT_N1. rewrite <- EQN2. exact ACCEPT_N1. }
      pose proof (proj2 (EQUIV (s2 ++ s) tag) ACCEPT_N2) as ACCEPT_M2.
      unfold accepts, accepts_from in ACCEPT_M2 |- *. rewrite delta_app in ACCEPT_M2.
      rewrite <- EQ2 in ACCEPT_M2. exact ACCEPT_M2.
    + assert (ACCEPT_M2 : accepts M (s2 ++ s) tag).
      { unfold accepts, accepts_from in *. rewrite delta_app. rewrite <- EQ2. exact ACCEPT. }
      pose proof (proj1 (EQUIV (s2 ++ s) tag) ACCEPT_M2) as ACCEPT_N2.
      assert (ACCEPT_N1 : accepts N (s1 ++ s) tag).
      { unfold accepts in ACCEPT_N2 |- *. rewrite !delta_app in *. rewrite <- EQN2 in ACCEPT_N2. rewrite <- EQN1. exact ACCEPT_N2. }
      pose proof (proj2 (EQUIV (s1 ++ s) tag) ACCEPT_N1) as ACCEPT_M1.
      unfold accepts, accepts_from in ACCEPT_M1 |- *. rewrite delta_app in ACCEPT_M1.
      rewrite <- EQ1 in ACCEPT_M1. exact ACCEPT_M1.
Qed.

Theorem minimise_numbered_states_minimal (N : TaggedDFA.t)
  (OKAY_M : okay M)
  (REACHABLE : all_states_reachable M)
  (OKAY_N : okay N)
  (NODUP_N : NoDup N.(TaggedDFA.states))
  (EQUIV : language_equiv M N)
  : length minimise_numbered.(TaggedDFA.states) <= length N.(TaggedDFA.states).
Proof.
  unfold minimise_numbered. cbn [states number_states numbered_states].
  unfold numbered_states. rewrite length_seq. eapply minimise_states_minimal; eauto.
Qed.

End MINIMISATION.

Module Partial.

#[projections(primitive)]
Record TaggedDFA : Type :=
  mk
  { state : Set
  ; state_hasEqDec : hasEqDec@{Set} state
  ; states : list state
  ; start_state : state
  ; accept_states : list (state * Token.t)
  ; transition (q : state) (c : ascii) : state
  }.

End Partial.

Section DELETE_DEAD_STATE.

Variable M : TaggedDFA.t.

#[local] Notation Q := M.(TaggedDFA.state).

Definition delete_state_set : Set :=
  list Q.

Definition delete_normalize (qs : delete_state_set) : delete_state_set :=
  filter (fun q => mem q qs) M.(TaggedDFA.states).

Lemma delete_normalize_complete (qs : delete_state_set) (q : Q)
  (STATES : q ∈ M.(TaggedDFA.states))
  (IN : q ∈ qs)
  : q ∈ delete_normalize qs.
Proof.
  unfold delete_normalize. rewrite filter_In. split; [exact STATES | ].
  now rewrite mem_true_iff.
Qed.

Lemma delete_normalize_sound (qs : delete_state_set) (q : Q)
  (IN : q ∈ delete_normalize qs)
  : q ∈ qs /\ q ∈ M.(TaggedDFA.states).
Proof.
  unfold delete_normalize in IN. rewrite filter_In in IN.
  destruct IN as [STATES MEM]. split; [ | exact STATES].
  now rewrite mem_true_iff in MEM.
Qed.

Definition delete_successors (q : Q) : delete_state_set :=
  map (M.(TaggedDFA.transition) q) all_asciis.

Definition delete_reachable_move (qs : delete_state_set) : delete_state_set :=
  qs >>= delete_successors.

Definition delete_reachable_step (qs : delete_state_set) : delete_state_set :=
  delete_normalize (union (delete_reachable_move qs) qs).

Definition reachable_states : delete_state_set :=
  iter (length M.(TaggedDFA.states)) delete_reachable_step (delete_normalize [M.(TaggedDFA.start_state)]).

Definition accepting_stateb (q : Q) : bool :=
  existsb (fun '(q', _) => eqb q q') M.(TaggedDFA.accept_states).

Definition accepting_states : delete_state_set :=
  filter accepting_stateb M.(TaggedDFA.states).

Definition predecessorb (q : Q) (p : Q) : bool :=
  existsb (fun c => eqb (M.(TaggedDFA.transition) p c) q) all_asciis.

Definition predecessors (q : Q) : delete_state_set :=
  filter (predecessorb q) M.(TaggedDFA.states).

Definition live_move (qs : delete_state_set) : delete_state_set :=
  qs >>= predecessors.

Definition live_step (qs : delete_state_set) : delete_state_set :=
  delete_normalize (union (live_move qs) qs).

Definition live_states : delete_state_set :=
  iter (length M.(TaggedDFA.states)) live_step accepting_states.

Lemma accepting_stateb_complete (q : Q) (tag : Token.t)
  (ACCEPT : (q, tag) ∈ M.(TaggedDFA.accept_states))
  : accepting_stateb q = true.
Proof.
  unfold accepting_stateb. rewrite existsb_exists.
  exists (q, tag). split; [exact ACCEPT | simpl].
  now rewrite eqb_eq.
Qed.

Lemma accepting_states_complete (q : Q) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : (q, tag) ∈ M.(TaggedDFA.accept_states))
  : q ∈ accepting_states.
Proof.
  destruct OKAY as [_ ACCEPT_OKAY _].
  unfold accepting_states. rewrite filter_In. split.
  - eapply ACCEPT_OKAY. exact ACCEPT.
  - eapply accepting_stateb_complete. exact ACCEPT.
Qed.

Definition dead_states : delete_state_set :=
  filter (fun q => negb (mem q live_states)) M.(TaggedDFA.states).

Definition useful_states : delete_state_set :=
  filter (fun q => mem q reachable_states && mem q live_states) M.(TaggedDFA.states).

Definition delete_dead_accept_states : list (Q * Token.t) :=
  filter (fun '(q, _) => mem q live_states) M.(TaggedDFA.accept_states).

Lemma live_step_complete_keep (q : Q) (qs : delete_state_set)
  (STATE : q ∈ M.(TaggedDFA.states))
  (IN : q ∈ qs)
  : q ∈ live_step qs.
Proof.
  unfold live_step.
  eapply delete_normalize_complete; [exact STATE | ].
  eapply union_complete. right. exact IN.
Qed.

Lemma iter_live_step_keeps (fuel : nat) (q : Q) (qs : delete_state_set)
  (STATE : q ∈ M.(TaggedDFA.states))
  (IN : q ∈ qs)
  : q ∈ iter fuel live_step qs.
Proof.
  revert qs IN. induction fuel as [ | fuel IH]; intros qs IN; simpl.
  - exact IN.
  - eapply IH. eapply live_step_complete_keep; eauto.
Qed.

Lemma accepting_state_live (q : Q) (tag : Token.t)
  (OKAY : okay M)
  (ACCEPT : (q, tag) ∈ M.(TaggedDFA.accept_states))
  : q ∈ live_states.
Proof.
  unfold live_states.
  eapply iter_live_step_keeps.
  - destruct OKAY as [_ ACCEPT_OKAY _]. eapply ACCEPT_OKAY. exact ACCEPT.
  - eapply accepting_states_complete; eauto.
Qed.

Lemma delete_dead_accept_states_complete (q : Q) (tag : Token.t)
  (ACCEPT : (q, tag) ∈ M.(TaggedDFA.accept_states))
  (LIVE : q ∈ live_states)
  : (q, tag) ∈ delete_dead_accept_states.
Proof.
  unfold delete_dead_accept_states. rewrite filter_In. split; [exact ACCEPT | ].
  now rewrite mem_true_iff.
Qed.

Lemma delete_dead_accept_states_sound (q : Q) (tag : Token.t)
  (ACCEPT : (q, tag) ∈ delete_dead_accept_states)
  : (q, tag) ∈ M.(TaggedDFA.accept_states) /\ q ∈ live_states.
Proof.
  unfold delete_dead_accept_states in ACCEPT. rewrite filter_In in ACCEPT.
  destruct ACCEPT as [ACCEPT LIVE]. split; [exact ACCEPT | ].
  now rewrite mem_true_iff in LIVE.
Qed.

Definition delete_dead_state : Partial.TaggedDFA :=
  {|
    Partial.state := Q;
    Partial.state_hasEqDec := M.(TaggedDFA.state_hasEqDec);
    Partial.states := live_states;
    Partial.start_state := M.(TaggedDFA.start_state);
    Partial.accept_states := delete_dead_accept_states;
    Partial.transition := M.(TaggedDFA.transition);
  |}.

End DELETE_DEAD_STATE.

End TaggedDFA.

Definition t : Type :=
  TaggedDFA.Partial.TaggedDFA.

Fixpoint delta (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (s : Input.t) {struct s} : M.(TaggedDFA.Partial.state) :=
  match s with
  | [] => q
  | c :: s' => delta M (M.(TaggedDFA.Partial.transition) q c) s'
  end.

Definition accepts (M : LGS.t) (s : Input.t) (tag : Token.t) : Prop :=
  (delta M M.(TaggedDFA.Partial.start_state) s, tag) ∈ M.(TaggedDFA.Partial.accept_states).

Definition accepted_tags (M : LGS.t) (s : Input.t) : ensemble Token.t :=
  fun tag => accepts M s tag.

Lemma delta_app (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (s1 : Input.t) (s2 : Input.t)
  : delta M q (s1 ++ s2) = delta M (delta M q s1) s2.
Proof.
  revert q. induction s1 as [ | c s1 IH]; intros q; simpl; eauto.
Qed.

Lemma delete_dead_state_delta (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) (s : Input.t)
  : delta (TaggedDFA.delete_dead_state M) q s = TaggedDFA.delta M q s.
Proof.
  revert q. induction s as [ | c s IH]; intros q; simpl; eauto.
Qed.

Theorem delete_dead_state_sound (M : TaggedDFA.t) (s : Input.t) (tag : Token.t)
  (ACCEPT : accepts (TaggedDFA.delete_dead_state M) s tag)
  : TaggedDFA.accepts M s tag.
Proof.
  unfold accepts, TaggedDFA.accepts in *. rewrite delete_dead_state_delta in ACCEPT. cbn in ACCEPT.
  pose proof (TaggedDFA.delete_dead_accept_states_sound M _ _ ACCEPT) as [ACCEPT' _].
  exact ACCEPT'.
Qed.

Theorem delete_dead_state_complete (M : TaggedDFA.t) (s : Input.t) (tag : Token.t)
  (OKAY : TaggedDFA.okay M)
  (ACCEPT : TaggedDFA.accepts M s tag)
  : accepts (TaggedDFA.delete_dead_state M) s tag.
Proof.
  unfold accepts, TaggedDFA.accepts in *. rewrite delete_dead_state_delta. cbn.
  eapply TaggedDFA.delete_dead_accept_states_complete; [exact ACCEPT | ].
  eapply TaggedDFA.accepting_state_live; eauto.
Qed.

Fixpoint first_accepting_token_from {Q : Set} `{Q_hasEqDec : hasEqDec@{Set} Q} (q : Q) (accept_states : list (Q * Token.t)) {struct accept_states} : option Token.t :=
  match accept_states with
  | [] => None
  | (q', tag) :: accept_states' => if eq_dec q q' then Some tag else first_accepting_token_from q accept_states'
  end.

Lemma first_accepting_token_from_sound {Q : Set} `{Q_hasEqDec : hasEqDec@{Set} Q} (q : Q) (accept_states : list (Q * Token.t)) (tag : Token.t)
  (FIND : first_accepting_token_from q accept_states = Some tag)
  : (q, tag) ∈ accept_states.
Proof.
  induction accept_states as [ | [q' tag'] accept_states IH]; simpl in FIND; [inv FIND | ].
  destruct (eq_dec q q') as [EQ | NE].
  - subst q'. inv FIND. left. reflexivity.
  - right. eapply IH. exact FIND.
Qed.

Lemma first_accepting_token_from_complete_some {Q : Set} `{Q_hasEqDec : hasEqDec@{Set} Q} (q : Q) (accept_states : list (Q * Token.t))
  (ACCEPT : exists tag, (q, tag) ∈ accept_states)
  : exists tag, first_accepting_token_from q accept_states = Some tag.
Proof.
  induction accept_states as [ | [q' tag'] accept_states IH]; simpl in ACCEPT |- *.
  - destruct ACCEPT as (tag & ACCEPT). contradiction.
  - destruct (eq_dec q q') as [EQ | NE].
    + exists tag'. reflexivity.
    + destruct ACCEPT as (tag & [EQ | ACCEPT]).
      * inv EQ. contradiction.
      * eapply IH. exists tag. exact ACCEPT.
Qed.

Definition first_accepting_token (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) : option Token.t :=
  @first_accepting_token_from M.(TaggedDFA.Partial.state) M.(TaggedDFA.Partial.state_hasEqDec) q M.(TaggedDFA.Partial.accept_states).

Lemma first_accepting_token_sound (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (tag : Token.t)
  (FIND : first_accepting_token M q = Some tag)
  : (q, tag) ∈ M.(TaggedDFA.Partial.accept_states).
Proof.
  eapply first_accepting_token_from_sound. exact FIND.
Qed.

Lemma first_accepting_token_complete_some (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (tag : Token.t)
  (ACCEPT : (q, tag) ∈ M.(TaggedDFA.Partial.accept_states))
  : exists tag', first_accepting_token M q = Some tag'.
Proof.
  eapply first_accepting_token_from_complete_some. exists tag. exact ACCEPT.
Qed.

Fixpoint maximal_munch (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (s : list ascii) (best : option (list ascii * Token.t)) {struct s} : option (list ascii * Token.t) :=
  match s with
  | [] => best
  | c :: s' =>
    let q' := M.(TaggedDFA.Partial.transition) q c in
    let best' := B.maybe (A := _) (B := fun _ => _) best (fun tag => Some (s', tag)) (first_accepting_token M q') in
    maximal_munch M q' s' best'
  end.

Lemma maximal_munch_some_if_best_some (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (s : Input.t) (rest : Input.t) (tag : Token.t)
  : exists rest', exists tag', maximal_munch M q s (Some (rest, tag)) = Some (rest', tag').
Proof.
  revert q rest tag. induction s as [ | c s IH]; intros q rest tag; simpl.
  - exists rest, tag. reflexivity.
  - destruct (first_accepting_token M (M.(TaggedDFA.Partial.transition) q c)) as [tag' | ]; cbn; eauto.
Qed.

Lemma maximal_munch_some_accepted_prefix (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (consumed : Input.t) (rest : Input.t) (best : option (Input.t * Token.t)) (tag : Token.t)
  (NONEMPTY : ~ consumed = [])
  (ACCEPT : (delta M q consumed, tag) ∈ M.(TaggedDFA.Partial.accept_states))
  : exists rest', exists tag', maximal_munch M q (consumed ++ rest) best = Some (rest', tag').
Proof.
  revert q rest best tag NONEMPTY ACCEPT.
  induction consumed as [ | c consumed IH]; intros q rest best tag NONEMPTY ACCEPT; [contradiction | ].
  simpl in ACCEPT |- *.
  set (q' := M.(TaggedDFA.Partial.transition) q c) in *.
  destruct consumed as [ | c' consumed'].
  - simpl in ACCEPT. destruct (first_accepting_token M q') as [tag' | ] eqn: FIND; cbn.
    + eapply maximal_munch_some_if_best_some.
    + pose proof (first_accepting_token_complete_some M q' tag ACCEPT) as (tag' & FIND').
      rewrite FIND in FIND'. inv FIND'.
  - destruct (first_accepting_token M q') as [tag' | ] eqn: FIND; cbn.
    + eapply IH; [discriminate | exact ACCEPT].
    + eapply IH; [discriminate | exact ACCEPT].
Qed.

Definition munch_accepts (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (s : Input.t) (rest : Input.t) (tag : Token.t) : Prop :=
  exists consumed, s = consumed ++ rest /\ (delta M q consumed, tag) ∈ M.(TaggedDFA.Partial.accept_states).

Lemma maximal_munch_sound_aux (M : LGS.t) (q0 : M.(TaggedDFA.Partial.state)) (s0 : Input.t) (q : M.(TaggedDFA.Partial.state)) (s : Input.t) (best : option (Input.t * Token.t)) (rest : Input.t) (tag : Token.t)
  (CUR : exists consumed, s0 = consumed ++ s /\ q = delta M q0 consumed)
  (BEST : forall rest0, forall tag0, best = Some (rest0, tag0) -> munch_accepts M q0 s0 rest0 tag0)
  (SCAN : maximal_munch M q s best = Some (rest, tag))
  : munch_accepts M q0 s0 rest tag.
Proof.
  revert q best rest tag CUR BEST SCAN.
  induction s as [ | c s IH]; intros q best rest tag CUR BEST SCAN; simpl in SCAN.
  - eapply BEST. exact SCAN.
  - destruct CUR as (consumed & EQ_INPUT & EQ_STATE). subst q.
    set (q' := M.(TaggedDFA.Partial.transition) (delta M q0 consumed) c) in *.
    assert (NEXT_INPUT : s0 = (consumed ++ [c]) ++ s).
    { rewrite EQ_INPUT. rewrite <- app_assoc. reflexivity. }
    assert (NEXT_STATE : q' = delta M q0 (consumed ++ [c])).
    { subst q'. rewrite delta_app. reflexivity. }
    destruct (first_accepting_token M q') as [tag' | ] eqn: FIND; cbn in SCAN.
    + eapply IH with (q := q') (best := Some (s, tag')); [ | | exact SCAN].
      * exists (consumed ++ [c]). split.
        { exact NEXT_INPUT. }
        { exact NEXT_STATE. }
      * intros rest0 tag0 BEST'. inv BEST'.
        exists (consumed ++ [c]). split.
        { exact NEXT_INPUT. }
        { rewrite <- NEXT_STATE. eapply first_accepting_token_sound. exact FIND. }
    + eapply IH with (q := q') (best := best); [ | | exact SCAN].
      * exists (consumed ++ [c]). split.
        { exact NEXT_INPUT. }
        { exact NEXT_STATE. }
      * intros rest0 tag0 BEST'. eapply BEST. exact BEST'.
Qed.

Theorem maximal_munch_sound (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (s : Input.t) (best : option (Input.t * Token.t)) (rest : Input.t) (tag : Token.t)
  (BEST : forall rest0 tag0, best = Some (rest0, tag0) -> munch_accepts M q s rest0 tag0)
  (SCAN : maximal_munch M q s best = Some (rest, tag))
  : munch_accepts M q s rest tag.
Proof.
  eapply maximal_munch_sound_aux with (q := q) (s := s) (best := best); eauto.
  exists []. split; reflexivity.
Qed.

Definition scan_one (M : LGS.t) (s : list ascii) : option (list ascii * Token.t) :=
  maximal_munch M M.(TaggedDFA.Partial.start_state) s None.

Definition scan_candidate (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t) : Prop :=
  exists consumed, s = consumed ++ rest /\ (~ consumed = []) /\ accepts M consumed tag.

Lemma maximal_munch_length_le (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (s : list ascii) (best : option (list ascii * Token.t)) (rest : list ascii) (tag : Token.t) (n : nat)
  (BEST_LE : forall rest0 tag0, best = Some (rest0, tag0) -> length rest0 <= n)
  (INPUT_LE : length s <= n)
  (SCAN : maximal_munch M q s best = Some (rest, tag))
  : length rest <= n.
Proof.
  revert q best rest tag n BEST_LE INPUT_LE SCAN.
  induction s as [ | c s IH]; intros q best rest tag n BEST_LE INPUT_LE SCAN; simpl in SCAN.
  - eapply BEST_LE. exact SCAN.
  - destruct (first_accepting_token M (M.(TaggedDFA.Partial.transition) q c)) as [tag' | ] eqn: FIND; cbn in SCAN.
    + eapply (IH (M.(TaggedDFA.Partial.transition) q c) (Some (s, tag')) rest tag n).
      * intros rest0 tag0 BEST. injection BEST as EQ_REST EQ_TAG. subst rest0. simpl in INPUT_LE. lia.
      * simpl in INPUT_LE. lia.
      * exact SCAN.
    + eapply (IH (M.(TaggedDFA.Partial.transition) q c) best rest tag n).
      * intros rest0 tag0 BEST. pose proof (BEST_LE rest0 tag0 BEST). lia.
      * simpl in INPUT_LE. lia.
      * exact SCAN.
Qed.

Lemma maximal_munch_length_le_accepted_prefix (M : LGS.t) (q : M.(TaggedDFA.Partial.state)) (consumed : Input.t) (rest : Input.t) (best : option (Input.t * Token.t)) (rest' : Input.t) (tag' : Token.t) (tag : Token.t)
  (NONEMPTY : ~ consumed = [])
  (ACCEPT : (delta M q consumed, tag) ∈ M.(TaggedDFA.Partial.accept_states))
  (SCAN : maximal_munch M q (consumed ++ rest) best = Some (rest', tag'))
  : length rest' <= length rest.
Proof.
  revert q rest best rest' tag' tag NONEMPTY ACCEPT SCAN.
  induction consumed as [ | c consumed IH]; intros q rest best rest' tag' tag NONEMPTY ACCEPT SCAN; [contradiction | ].
  simpl in ACCEPT, SCAN.
  set (q' := M.(TaggedDFA.Partial.transition) q c) in *.
  destruct consumed as [ | c' consumed'].
  - simpl in ACCEPT.
    destruct (first_accepting_token M q') as [tag0 | ] eqn: FIND; cbn in SCAN.
    + eapply (maximal_munch_length_le M q' rest (Some (rest, tag0)) rest' tag' (length rest)); [ | lia | exact SCAN].
      intros rest0 tag1 BEST. inv BEST. lia.
    + pose proof (first_accepting_token_complete_some M q' tag ACCEPT) as (tag0 & FIND').
      rewrite FIND in FIND'. inv FIND'.
  - destruct (first_accepting_token M q') as [tag0 | ] eqn: FIND; cbn in SCAN.
    + eapply IH; [discriminate | exact ACCEPT | exact SCAN].
    + eapply IH; [discriminate | exact ACCEPT | exact SCAN].
Qed.

Lemma scan_one_length_lt (M : LGS.t) (s : list ascii) (rest : list ascii) (tag : Token.t)
  (SCAN : scan_one M s = Some (rest, tag))
  : length rest < length s.
Proof.
  destruct s as [ | c s]; simpl in SCAN; [inv SCAN | ].
  unfold scan_one in SCAN. simpl in SCAN.
  destruct (first_accepting_token M (M.(TaggedDFA.Partial.transition) M.(TaggedDFA.Partial.start_state) c)) as [tag' | ] eqn: FIND; cbn in SCAN.
  - pose proof (maximal_munch_length_le M (M.(TaggedDFA.Partial.transition) M.(TaggedDFA.Partial.start_state) c) s (Some (s, tag')) rest tag (length s)) as LENGTH.
    assert (LE : length rest <= length s).
    { eapply LENGTH; [ | lia | exact SCAN]. intros rest0 tag0 BEST. inversion BEST; subst. lia. }
    simpl. lia.
  - pose proof (maximal_munch_length_le M (M.(TaggedDFA.Partial.transition) M.(TaggedDFA.Partial.start_state) c) s None rest tag (length s)) as LENGTH.
    assert (LE : length rest <= length s).
    { eapply LENGTH; [intros rest0 tag0 BEST; inv BEST | lia | exact SCAN]. }
    simpl. lia.
Qed.

Theorem scan_one_sound (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t)
  (SCAN : scan_one M s = Some (rest, tag))
  : exists consumed, s = consumed ++ rest /\ accepts M consumed tag /\ length rest < length s.
Proof.
  pose proof SCAN as SCAN_LENGTH.
  unfold scan_one in SCAN.
  pose proof (maximal_munch_sound M M.(TaggedDFA.Partial.start_state) s None rest tag) as SOUND.
  assert (BEST : forall rest0, forall tag0, None = Some (rest0, tag0) -> munch_accepts M M.(TaggedDFA.Partial.start_state) s rest0 tag0).
  { intros rest0 tag0 BEST. inv BEST. }
  pose proof (SOUND BEST SCAN) as (consumed & EQ_INPUT & ACCEPT).
  exists consumed. repeat split; eauto.
  eapply scan_one_length_lt. exact SCAN_LENGTH.
Qed.

Theorem scan_one_maximal (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t)
  (SCAN : scan_one M s = Some (rest, tag))
  : scan_candidate M s rest tag /\ (forall rest', forall tag', scan_candidate M s rest' tag' -> length rest <= length rest').
Proof.
  split.
  - pose proof (scan_one_sound M s rest tag SCAN) as (consumed & EQ_INPUT & ACCEPT & LT).
    exists consumed. repeat split; eauto.
    intros EQ. subst consumed. simpl in EQ_INPUT. subst s. lia.
  - intros rest' tag' (consumed & EQ_INPUT & NONEMPTY & ACCEPT).
    unfold scan_one in SCAN. rewrite EQ_INPUT in SCAN.
    unfold accepts in ACCEPT.
    eapply maximal_munch_length_le_accepted_prefix; eauto.
Qed.

Theorem scan_one_complete (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t)
  (CANDIDATE : scan_candidate M s rest tag)
  : exists rest', exists tag', scan_one M s = Some (rest', tag') /\ length rest' <= length rest.
Proof.
  destruct CANDIDATE as (consumed & EQ_INPUT & NONEMPTY & ACCEPT).
  unfold scan_one. rewrite EQ_INPUT. unfold accepts in ACCEPT.
  pose proof (maximal_munch_some_accepted_prefix M M.(TaggedDFA.Partial.start_state) consumed rest None tag NONEMPTY ACCEPT) as (rest' & tag' & SCAN).
  exists rest', tag'. split; [exact SCAN | eapply maximal_munch_length_le_accepted_prefix; eauto].
Qed.

Corollary scan_one_some_iff (M : LGS.t) (s : Input.t)
  : (exists rest, exists tag, scan_one M s = Some (rest, tag)) <-> (exists rest, exists tag, scan_candidate M s rest tag).
Proof.
  split.
  - intros (rest & tag & SCAN).
    pose proof (scan_one_maximal M s rest tag SCAN) as [CANDIDATE _].
    exists rest, tag. exact CANDIDATE.
  - intros (rest & tag & CANDIDATE).
    pose proof (scan_one_complete M s rest tag CANDIDATE) as (rest' & tag' & SCAN & _).
    exists rest', tag'. exact SCAN.
Qed.

Inductive scan_all_spec (M : LGS.t) : Input.t -> list Token.t -> Prop :=
  | scan_all_spec_nil
    : scan_all_spec M [] []
  | scan_all_spec_cons s rest tag tags
    (SCAN : scan_one M s = Some (rest, tag))
    (REST : scan_all_spec M rest tags)
    : scan_all_spec M s (tag :: tags).

Inductive scan_all_accepts (M : LGS.t) : Input.t -> list Token.t -> Prop :=
  | scan_all_accepts_nil
    : scan_all_accepts M [] []
  | scan_all_accepts_cons consumed rest tag tags
    (ACCEPT : accepts M consumed tag)
    (REST : scan_all_accepts M rest tags)
    : scan_all_accepts M (consumed ++ rest) (tag :: tags).

Definition input_lt (s1 : Input.t) (s2 : Input.t) : Prop :=
  length s1 < length s2.

Fixpoint scan_all' (M : LGS.t) (s : list ascii) (H_Acc : Acc input_lt s) {struct H_Acc} : option (list Token.t) :=
  if L.null s then
    Some []
  else
    match scan_one M s with
    | None => None
    | Some (rest, tag) =>
      match lt_dec (length rest) (length s) with
      | left LT =>
        match scan_all' M rest (Acc_inv H_Acc rest LT) with
        | None => None
        | Some tags => Some (tag :: tags)
        end
      | right _ => None
      end
    end.

Definition scan_all (M : LGS.t) (s : list ascii) : option (list Token.t) :=
  scan_all' M s (L.length_lt_wf s).

Theorem scan_all'_sound (M : LGS.t) (s : Input.t) (H_Acc : Acc input_lt s) (tags : list Token.t)
  (SCAN : scan_all' M s H_Acc = Some tags)
  : scan_all_spec M s tags.
Proof.
  revert s H_Acc tags SCAN.
  refine (fix IH (s : Input.t) (H_Acc : Acc input_lt s) (tags : list Token.t) (SCAN : scan_all' M s H_Acc = Some tags) {struct H_Acc} : scan_all_spec M s tags := _).
  destruct H_Acc as [H_Acc_inv].
  destruct s as [ | c s]; simpl in SCAN.
  - inv SCAN. constructor.
  - destruct (scan_one M (c :: s)) as [[rest tag] | ] eqn: SCAN_ONE; [ | inv SCAN].
    destruct (lt_dec (length rest) (S (length s))) as [LT | NLT]; cbn in SCAN; [ | inv SCAN].
    destruct (scan_all' M rest (H_Acc_inv rest LT)) as [tags' | ] eqn: SCAN_REST; cbn in SCAN; inv SCAN.
    eapply scan_all_spec_cons with (rest := rest); [exact SCAN_ONE | ].
    eapply IH. exact SCAN_REST.
Qed.

Theorem scan_all_sound (M : LGS.t) (s : Input.t) (tags : list Token.t)
  (SCAN : scan_all M s = Some tags)
  : scan_all_spec M s tags.
Proof.
  unfold scan_all in SCAN. eapply scan_all'_sound. exact SCAN.
Qed.

Theorem scan_all'_complete (M : LGS.t) (s : Input.t) (H_Acc : Acc input_lt s) (tags : list Token.t)
  (SPEC : scan_all_spec M s tags)
  : scan_all' M s H_Acc = Some tags.
Proof.
  revert H_Acc.
  induction SPEC; intros H_Acc.
  - destruct H_Acc as [H_Acc_inv]. simpl. reflexivity.
  - destruct H_Acc as [H_Acc_inv].
    destruct s as [ | c s']; simpl in SCAN.
    + inv SCAN.
    + simpl. rewrite SCAN.
      destruct (lt_dec (length rest) (S (length s'))) as [LT | NLT].
      * rewrite IHSPEC. reflexivity.
      * exfalso. pose proof (scan_one_length_lt M (c :: s') rest tag SCAN). simpl in H. lia.
Qed.

Theorem scan_all_complete (M : LGS.t) (s : Input.t) (tags : list Token.t)
  (SPEC : scan_all_spec M s tags)
  : scan_all M s = Some tags.
Proof.
  unfold scan_all. eapply scan_all'_complete. exact SPEC.
Qed.

Corollary scan_all_spec_iff (M : LGS.t) (s : Input.t) (tags : list Token.t)
  : scan_all M s = Some tags <-> scan_all_spec M s tags.
Proof.
  split.
  - eapply scan_all_sound.
  - eapply scan_all_complete.
Qed.

Theorem scan_all_spec_accepts (M : LGS.t) (s : Input.t) (tags : list Token.t)
  (SCAN : scan_all_spec M s tags)
  : scan_all_accepts M s tags.
Proof.
  induction SCAN.
  - constructor.
  - pose proof (scan_one_sound M s rest tag SCAN) as (consumed & EQ_INPUT & ACCEPT & _).
    subst s. econstructor; eauto.
Qed.

Theorem scan_all_accepts_sound (M : LGS.t) (s : Input.t) (tags : list Token.t)
  (SCAN : scan_all M s = Some tags)
  : scan_all_accepts M s tags.
Proof.
  eapply scan_all_spec_accepts. eapply scan_all_sound. exact SCAN.
Qed.

Inductive scan_all_rules (rules : list Rule.t) : Input.t -> list Token.t -> Prop :=
  | scan_all_rules_nil
    : scan_all_rules rules [] []
  | scan_all_rules_cons consumed rest tag tags rule
    (NONEMPTY : ~ consumed = [])
    (IN_RULE : rule ∈ rules)
    (TOKEN : rule.(Rule.token) = tag)
    (REGEX : consumed \in eval_regex rule.(Rule.regex))
    (REST : scan_all_rules rules rest tags)
    : scan_all_rules rules (consumed ++ rest) (tag :: tags).

Definition build : BuildErrorM LGS.t := do
  'rules <- Rule.compileds;
  ret (TaggedDFA.delete_dead_state (TaggedDFA.minimise_numbered (TaggedDFA.subset_construct (TaggedENFA.mkUnitedTaggedENFA rules))))
  end.

Theorem build_sound (M : LGS.t)
  (BUILD : build = inr M)
  : exists rules, Rule.compileds = inr rules /\ M = TaggedDFA.delete_dead_state (TaggedDFA.minimise_numbered (TaggedDFA.subset_construct (TaggedENFA.mkUnitedTaggedENFA rules))).
Proof.
  unfold build in BUILD. destruct Rule.compileds as [err | rules] eqn: COMPILED; inv BUILD.
  exists rules. split; eauto.
Qed.

Theorem build_complete (rules : list Rule.t)
  (COMPILED : Rule.compileds = inr rules)
  : build = inr (TaggedDFA.delete_dead_state (TaggedDFA.minimise_numbered (TaggedDFA.subset_construct (TaggedENFA.mkUnitedTaggedENFA rules)))).
Proof.
  unfold build. rewrite COMPILED. reflexivity.
Qed.

Theorem build_accepts_sound (M : LGS.t) (s : Input.t) (tag : Token.t)
  (BUILD : build = inr M)
  (ACCEPT : accepts M s tag)
  : exists rules, Rule.compileds = inr rules /\ exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex).
Proof.
  pose proof (build_sound M BUILD) as (rules & COMPILED & EQ). subst M.
  exists rules. split; [exact COMPILED | ].
  pose proof (delete_dead_state_sound _ _ _ ACCEPT) as ACCEPT_DFA.
  pose proof (TaggedDFA.minimise_numbered_sound _ _ _ (TaggedDFA.subset_construct_okay _ (TaggedENFA.mkUnitedTaggedENFA_okay rules)) ACCEPT_DFA) as ACCEPT_SUBSET.
  pose proof (TaggedDFA.subset_construct_sound _ _ _ ACCEPT_SUBSET) as ACCEPT_ENFA.
  assert (COMPILE : fmap TaggedENFA.mkUnitedTaggedENFA Rule.compileds = inr (TaggedENFA.mkUnitedTaggedENFA rules)).
  { unfold fmap, mkFunctorFromMonad. simpl. rewrite COMPILED. reflexivity. }
  pose proof (TaggedENFA.mkUnitedTaggedENFA_sound _ COMPILE) as (rules' & COMPILED' & SOUND).
  rewrite COMPILED in COMPILED'. inv COMPILED'.
  eapply SOUND. exact ACCEPT_ENFA.
Qed.

Theorem build_accepts_sound_with_rules (M : LGS.t) (rules : list Rule.t) (s : Input.t) (tag : Token.t)
  (BUILD : build = inr M)
  (COMPILED : Rule.compileds = inr rules)
  (ACCEPT : accepts M s tag)
  : exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex).
Proof.
  pose proof (build_accepts_sound M s tag BUILD ACCEPT) as (rules' & COMPILED' & ACCEPT').
  rewrite COMPILED in COMPILED'. inv COMPILED'. exact ACCEPT'.
Qed.

Theorem build_scan_one_sound (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t)
  (BUILD : build = inr M)
  (SCAN : scan_one M s = Some (rest, tag))
  : exists rules, Rule.compileds = inr rules /\ (exists consumed, exists rule, s = consumed ++ rest /\ (~ consumed = []) /\ rule ∈ rules /\ rule.(Rule.token) = tag /\ consumed \in eval_regex rule.(Rule.regex) /\ length rest < length s).
Proof.
  pose proof (build_sound M BUILD) as (rules & COMPILED & _).
  pose proof (scan_one_sound M s rest tag SCAN) as (consumed & EQ_INPUT & ACCEPT & LT).
  pose proof (build_accepts_sound_with_rules M rules consumed tag BUILD COMPILED ACCEPT) as (rule & IN_RULE & TOKEN & REGEX).
  exists rules. split; [exact COMPILED | exists consumed, rule].
  repeat split; eauto. intros EQ. subst consumed. simpl in EQ_INPUT. subst s. lia.
Qed.

Theorem build_accepts_complete (M : LGS.t) (rules : list Rule.t) (s : Input.t) (tag : Token.t)
  (BUILD : build = inr M)
  (COMPILED : Rule.compileds = inr rules)
  (ACCEPT : exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex))
  : accepts M s tag.
Proof.
  rewrite (build_complete rules COMPILED) in BUILD. inv BUILD.
  assert (COMPILE : fmap TaggedENFA.mkUnitedTaggedENFA Rule.compileds = inr (TaggedENFA.mkUnitedTaggedENFA rules)).
  { unfold fmap, mkFunctorFromMonad. simpl. rewrite COMPILED. reflexivity. }
  pose proof (TaggedENFA.mkUnitedTaggedENFA_okay rules) as OKAY_ENFA.
  pose proof (TaggedENFA.mkUnitedTaggedENFA_complete _ COMPILE) as (rules' & COMPILED' & COMPLETE).
  rewrite COMPILED in COMPILED'. injection COMPILED' as EQ_RULES. subst rules'.
  pose proof (COMPLETE s tag ACCEPT) as ACCEPT_ENFA.
  pose proof (TaggedDFA.subset_construct_complete _ OKAY_ENFA _ _ ACCEPT_ENFA) as ACCEPT_SUBSET.
  pose proof (TaggedDFA.subset_construct_okay _ OKAY_ENFA) as OKAY_SUBSET.
  pose proof (TaggedDFA.minimise_numbered_complete _ _ _ OKAY_SUBSET ACCEPT_SUBSET) as ACCEPT_MIN.
  pose proof (TaggedDFA.minimise_numbered_okay _ OKAY_SUBSET) as OKAY_MIN.
  eapply delete_dead_state_complete; eauto.
Qed.

Theorem build_scan_all_spec_sound (M : LGS.t) (rules : list Rule.t) (s : Input.t) (tags : list Token.t)
  (BUILD : build = inr M)
  (COMPILED : Rule.compileds = inr rules)
  (SPEC : scan_all_spec M s tags)
  : scan_all_rules rules s tags.
Proof.
  induction SPEC.
  - constructor.
  - pose proof (scan_one_sound M s rest tag SCAN) as (consumed & EQ_INPUT & ACCEPT & LT).
    pose proof (build_accepts_sound_with_rules M rules consumed tag BUILD COMPILED ACCEPT) as (rule & IN_RULE & TOKEN & REGEX).
    subst s. econstructor; eauto.
    intros EQ. subst consumed. simpl in LT. lia.
Qed.

Theorem build_scan_all_sound (M : LGS.t) (s : Input.t) (tags : list Token.t)
  (BUILD : build = inr M)
  (SCAN : scan_all M s = Some tags)
  : exists rules, Rule.compileds = inr rules /\ scan_all_rules rules s tags.
Proof.
  pose proof (build_sound M BUILD) as (rules & COMPILED & _).
  exists rules. split; [exact COMPILED | ].
  eapply build_scan_all_spec_sound; [exact BUILD | exact COMPILED | ].
  eapply scan_all_sound. exact SCAN.
Qed.

Section MAIN_THEOREMS.

Theorem build_correct (M : LGS.t)
  : build = inr M <-> (exists rules, Rule.compileds = inr rules /\ M =TaggedDFA.delete_dead_state(TaggedDFA.minimise_numbered(TaggedDFA.subset_construct (TaggedENFA.mkUnitedTaggedENFA rules)))).
Proof.
  split.
  - exact (build_sound M).
  - intros (rules & COMPILED & EQ). subst M.
    eapply build_complete. exact COMPILED.
Qed.

Theorem build_accepts_correct (M : LGS.t)
  (BUILD : build = inr M)
  : exists rules, Rule.compileds = inr rules /\ (forall s, forall tag, accepts M s tag <-> (exists rule, rule ∈ rules /\ rule.(Rule.token) = tag /\ s \in eval_regex rule.(Rule.regex))).
Proof.
  pose proof (build_sound M BUILD) as (rules & COMPILED & _).
  exists rules. split; [exact COMPILED | ].
  intros s tag. split.
  - intro ACCEPT. eapply build_accepts_sound_with_rules; eauto.
  - intro ACCEPT. eapply build_accepts_complete; eauto.
Qed.

Theorem scan_one_correct (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t)
  (SCAN_ONE : scan_one M s = Some (rest, tag))
  : scan_candidate M s rest tag /\ (forall rest', forall tag', scan_candidate M s rest' tag' -> length rest <= length rest').
Proof.
  eapply scan_one_maximal; eauto.
Qed.

Theorem scan_one_success_correct (M : LGS.t) (s : Input.t)
  : (exists rest, exists tag, scan_one M s = Some (rest, tag)) <-> (exists rest, exists tag, scan_candidate M s rest tag).
Proof.
  eapply scan_one_some_iff.
Qed.

Theorem scan_all_correct (M : LGS.t) (s : Input.t) (tags : list Token.t)
  : scan_all M s = Some tags <-> scan_all_spec M s tags.
Proof.
  eapply scan_all_spec_iff.
Qed.

Variant build_scan_one_spec (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t) : Prop :=
  | build_scan_one_spec_intro rules consumed rule
    (COMPILED : Rule.compileds = inr rules)
    (EQ_INPUT : s = consumed ++ rest)
    (NONEMPTY : ~ consumed = [])
    (IN_RULE : rule ∈ rules)
    (TOKEN : rule.(Rule.token) = tag)
    (REGEX : consumed \in eval_regex rule.(Rule.regex))
    (LENGTH : length rest < length s)
    (MAXIMAL : forall rest', forall tag', scan_candidate M s rest' tag' -> length rest <= length rest')
    : build_scan_one_spec M s rest tag.

Theorem build_scan_one_correct (M : LGS.t) (s : Input.t) (rest : Input.t) (tag : Token.t)
  (BUILD : build = inr M)
  (SCAN : scan_one M s = Some (rest, tag))
  : build_scan_one_spec M s rest tag.
Proof.
  pose proof (build_scan_one_sound M s rest tag BUILD SCAN) as (rules & COMPILED & consumed & rule & EQ_INPUT & NONEMPTY & IN_RULE & TOKEN & REGEX & LT).
  pose proof (scan_one_maximal M s rest tag SCAN) as [_ MAXIMAL].
  econstructor; eauto.
Qed.

Theorem build_scan_one_complete_correct (M : LGS.t) (rules : list Rule.t) (s : Input.t) (consumed : Input.t) (rest : Input.t) (rule : Rule.t)
  (BUILD : build = inr M)
  (COMPILED : Rule.compileds = inr rules)
  (EQ_INPUT : s = consumed ++ rest)
  (NONEMPTY : ~ consumed = [])
  (IN_RULE : rule ∈ rules)
  (REGEX : consumed \in eval_regex rule.(Rule.regex))
  : exists rest', exists tag', scan_one M s = Some (rest', tag') /\ length rest' <= length rest.
Proof.
  eapply scan_one_complete.
  exists consumed. repeat split; eauto.
  eapply build_accepts_complete with (rules := rules); eauto.
Qed.

Theorem build_scan_all_correct (M : LGS.t) (s : Input.t) (tags : list Token.t)
  (BUILD : build = inr M)
  (SCAN : scan_all M s = Some tags)
  : exists rules, Rule.compileds = inr rules /\ scan_all_rules rules s tags.
Proof.
  eapply build_scan_all_sound; eauto.
Qed.

Theorem minimise_numbered_minimal_correct (M : TaggedDFA.t) (N : TaggedDFA.t)
  (OKAY_M : TaggedDFA.okay M)
  (REACHABLE : TaggedDFA.all_states_reachable M)
  (OKAY_N : TaggedDFA.okay N)
  (NODUP_N : NoDup N.(TaggedDFA.states))
  (EQUIV : TaggedDFA.language_equiv M N)
  : length (TaggedDFA.minimise_numbered M).(TaggedDFA.states) <= length N.(TaggedDFA.states).
Proof.
  eapply TaggedDFA.minimise_numbered_states_minimal; eauto.
Qed.

End MAIN_THEOREMS.

End LGS.
