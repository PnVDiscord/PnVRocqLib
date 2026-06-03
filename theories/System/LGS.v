Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Strings.String.
Require Import PnV.Control.Monad.
Require Import PnV.Data.FiniteSet.
Require Import PnV.System.Regex.
Require Import PnV.Prelude.Prelude.

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

Theorem Input_to_of_string (s : string)
  : Input.to_string (Input.of_string s) = s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Theorem Input_of_to_string (s : Input.t)
  : Input.of_string (Input.to_string s) = s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Theorem Input_length_of_string (s : string)
  : length (Input.of_string s) = String.length s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Theorem Input_to_string_app (s1 : Input.t) (s2 : Input.t)
  : Input.to_string (s1 ++ s2) = String.append (Input.to_string s1) (Input.to_string s2).
Proof.
  induction s1 as [ | c s1 IH]; simpl; congruence.
Qed.

Fixpoint nullable (e : regex ascii) {struct e} : bool :=
  match e with
  | Re.Null => false
  | Re.Empty => true
  | Re.Char _ => false
  | Re.Union e1 e2 => nullable e1 || nullable e2
  | Re.Append e1 e2 => nullable e1 && nullable e2
  | Re.Star _ => true
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
  - assert (CLAIM : forall s, forall e0, s =~= e0 -> s = [] -> nullable e0 = true).
    { intros s e0 H_IN. induction H_IN; simpl; i; subst; try congruence; eauto.
      - rewrite orb_true_iff. left. eauto.
      - rewrite orb_true_iff. right. eauto.
      - pose proof (app_eq_nil _ _ H) as (EQ1 & EQ2). subst.
        rewrite andb_true_iff. eauto.
    }
    i. eapply CLAIM; eauto.
Qed.

Theorem nullable_spec (e : regex ascii)
  : nullable e = true <-> [] \in eval_regex e.
Proof.
  rewrite eval_regex_good. eapply nullable_similar_spec.
Qed.

Corollary nullable_false_spec (e : regex ascii)
  : nullable e = false <-> (~ [] \in eval_regex e).
Proof.
  destruct (nullable e) eqn: EQ; split; i.
  - congruence.
  - exfalso. apply H. rewrite <- nullable_spec. exact EQ.
  - intros IN. rewrite <- nullable_spec in IN. congruence.
  - reflexivity.
Qed.

Module ENFA.

#[projections(primitive)]
Record t : Type :=
  mk
  { state : Set
  ; state_hasEqDec : hasEqDec@{Set} state
  ; states : list state
  ; start : state
  ; accept_states : list state
  ; eps_step : state -> list state
  ; char_step : state -> ascii -> list state
  }.

#[global] Existing Instance state_hasEqDec.

Inductive reachable (M : ENFA.t) : M.(state) -> list ascii -> M.(state) -> Prop :=
  | reachable_nil q
    : reachable M q [] q
  | reachable_eps q1 q2 q3 s
    (STEP : q2 ∈ M.(eps_step) q1)
    (REST : reachable M q2 s q3)
    : reachable M q1 s q3
  | reachable_char q1 q2 q3 a s
    (STEP : q2 ∈ M.(char_step) q1 a)
    (REST : reachable M q2 s q3)
    : reachable M q1 (a :: s) q3.

Inductive eclose (M : ENFA.t) : M.(state) -> M.(state) -> Prop :=
  | eclose_refl q
    : eclose M q q
  | eclose_step q1 q2 q3
    (STEP : q2 ∈ M.(eps_step) q1)
    (REST : eclose M q2 q3)
    : eclose M q1 q3.

Definition accepts (M : ENFA.t) (s : list ascii) : Prop :=
  exists q, reachable M M.(start) s q /\ q ∈ M.(accept_states).

Definition wf (M : ENFA.t) : Prop :=
  M.(start) ∈ M.(states) /\
  (forall q, q ∈ M.(accept_states) -> q ∈ M.(states)) /\
  (forall q, forall q',
      q ∈ M.(states) -> q' ∈ M.(eps_step) q -> q' ∈ M.(states)) /\
  (forall q, forall q', forall a,
      q ∈ M.(states) -> q' ∈ M.(char_step) q a -> q' ∈ M.(states)).

End ENFA.

#[local] Hint Constructors ENFA.reachable ENFA.eclose : core.

Theorem ENFA_reachable_app (M : ENFA.t) (q1 : M.(ENFA.state)) (q2 : M.(ENFA.state)) (q3 : M.(ENFA.state)) (s1 : list ascii) (s2 : list ascii)
  (R1 : ENFA.reachable M q1 s1 q2)
  (R2 : ENFA.reachable M q2 s2 q3)
  : ENFA.reachable M q1 (s1 ++ s2) q3.
Proof.
  induction R1 as [q | q1' q2' q3' s STEP REST IH | q1' q2' q3' a s STEP REST IH]; simpl; eauto with *.
Qed.

Theorem ENFA_eclose_trans (M : ENFA.t) (q1 : M.(ENFA.state)) (q2 : M.(ENFA.state)) (q3 : M.(ENFA.state))
  (CLOSE1 : ENFA.eclose M q1 q2)
  (CLOSE2 : ENFA.eclose M q2 q3)
  : ENFA.eclose M q1 q3.
Proof.
  induction CLOSE1 as [q | q1' q2' q3' STEP REST IH]; eauto with *.
Qed.

Theorem ENFA_eclose_reachable_nil (M : ENFA.t) (q1 : M.(ENFA.state)) (q2 : M.(ENFA.state))
  (CLOSE : ENFA.eclose M q1 q2)
  : ENFA.reachable M q1 [] q2.
Proof.
  induction CLOSE as [q | q1' q2' q3 STEP REST IH]; eauto with *.
Qed.

Theorem ENFA_reachable_nil_eclose (M : ENFA.t) (q1 : M.(ENFA.state)) (q2 : M.(ENFA.state))
  (REACH : ENFA.reachable M q1 [] q2)
  : ENFA.eclose M q1 q2.
Proof.
  remember (@nil ascii) as s eqn: EQ.
  induction REACH as [q | q1' q2' q3' s STEP REST IH | q1' q2' q3' a s STEP REST IH]; inv EQ; eauto with *.
Qed.

Theorem ENFA_eclose_reachable_nil_iff (M : ENFA.t) (q1 : M.(ENFA.state)) (q2 : M.(ENFA.state))
  : ENFA.eclose M q1 q2 <-> ENFA.reachable M q1 [] q2.
Proof.
  split; intros H.
  - eapply ENFA_eclose_reachable_nil; eauto.
  - eapply ENFA_reachable_nil_eclose; eauto.
Qed.

Theorem ENFA_eclose_wf (M : ENFA.t) (q1 : M.(ENFA.state)) (q2 : M.(ENFA.state))
  (WF : ENFA.wf M)
  (IN : q1 ∈ M.(ENFA.states))
  (CLOSE : ENFA.eclose M q1 q2)
  : q2 ∈ M.(ENFA.states).
Proof.
  destruct WF as (_ & _ & EPS_WF & _).
  induction CLOSE as [q | q1' q2' q3 STEP REST IH].
  - exact IN.
  - eapply IH. eapply EPS_WF; eauto.
Qed.

Theorem ENFA_reachable_wf (M : ENFA.t) (q1 : M.(ENFA.state)) (q2 : M.(ENFA.state)) (s : list ascii)
  (WF : ENFA.wf M)
  (IN : q1 ∈ M.(ENFA.states))
  (REACH : ENFA.reachable M q1 s q2)
  : q2 ∈ M.(ENFA.states).
Proof.
  destruct WF as (_ & _ & EPS_WF & CHAR_WF).
  induction REACH as [q | q1' q2' q3 s STEP REST IH | q1' q2' q3 a s STEP REST IH].
  - exact IN.
  - eapply IH. eapply EPS_WF; eauto.
  - eapply IH. eapply CHAR_WF; eauto.
Qed.

Theorem ENFA_reachable_inv (M : ENFA.t) (q1 : M.(ENFA.state)) (q3 : M.(ENFA.state)) (s : list ascii)
  (REACH : ENFA.reachable M q1 s q3)
  : ⟪ REACH_NIL : s = [] /\ q3 = q1 ⟫ \/ ⟪ REACH_EPS : exists q2, q2 ∈ M.(ENFA.eps_step) q1 /\ ENFA.reachable M q2 s q3 ⟫ \/ ⟪ REACH_CHAR : exists a, exists s', exists q2, s = a :: s' /\ q2 ∈ M.(ENFA.char_step) q1 a /\ ENFA.reachable M q2 s' q3 ⟫.
Proof.
  destruct REACH as [q | q1' q2' q3' s' STEP REST | q1' q2' q3' a s' STEP REST].
  - left. split; reflexivity.
  - right. left. exists q2'. split; eauto.
  - right. right. exists a. exists s'. exists q2'. splits; eauto.
Qed.

Theorem ENFA_reachable_stuck (M : ENFA.t) (q1 : M.(ENFA.state)) (q2 : M.(ENFA.state)) (s : list ascii)
  (NO_EPS : forall q, q ∈ M.(ENFA.eps_step) q1 -> False)
  (NO_CHAR : forall a, forall q, q ∈ M.(ENFA.char_step) q1 a -> False)
  (REACH : ENFA.reachable M q1 s q2)
  : s = [] /\ q2 = q1.
Proof.
  inv REACH; eauto.
  - exfalso. eapply NO_EPS; eauto.
  - exfalso. eapply NO_CHAR; eauto.
Qed.

Module DFA.

#[projections(primitive)]
Record t : Type :=
  mk
  { state : Set
  ; state_hasEqDec : hasEqDec@{Set} state
  ; states : list state
  ; start : state
  ; acceptb : state -> bool
  ; step : state -> ascii -> option state
  }.

#[global] Existing Instance state_hasEqDec.

Fixpoint run_from (M : DFA.t) (q : M.(state)) (s : list ascii) {struct s} : option M.(state) :=
  match s with
  | [] => Some q
  | c :: s' =>
    match M.(step) q c with
    | Some q' => run_from M q' s'
    | None => None
    end
  end.

Definition run (M : DFA.t) (s : list ascii) : option M.(state) :=
  run_from M M.(start) s.

Definition accepts (M : DFA.t) (s : list ascii) : Prop :=
  exists q, run M s = Some q /\ M.(acceptb) q = true.

Definition acceptsb (M : DFA.t) (s : list ascii) : bool :=
  match run M s with
  | Some q => M.(acceptb) q
  | None => false
  end.

Definition wf (M : DFA.t) : Prop :=
  M.(start) ∈ M.(states) /\
  (forall q, forall q', forall a,
      q ∈ M.(states) -> M.(step) q a = Some q' -> q' ∈ M.(states)).

Inductive step_rel (M : DFA.t) : M.(state) -> ascii -> M.(state) -> Prop :=
  | step_rel_intro q a q'
    (STEP : M.(step) q a = Some q')
    : step_rel M q a q'.

Inductive reachable (M : DFA.t) : M.(state) -> list ascii -> M.(state) -> Prop :=
  | reachable_nil q
    : reachable M q [] q
  | reachable_cons q1 q2 q3 a s
    (STEP : step_rel M q1 a q2)
    (REST : reachable M q2 s q3)
    : reachable M q1 (a :: s) q3.

Definition deterministic (M : DFA.t) : Prop :=
  forall q, forall a, forall q1, forall q2, step_rel M q a q1 -> step_rel M q a q2 -> q1 = q2.

End DFA.

#[local] Hint Constructors DFA.step_rel DFA.reachable : core.

Theorem DFA_step_rel_deterministic (M : DFA.t)
  : DFA.deterministic M.
Proof.
  ii. inv H. inv H0. congruence.
Qed.

Theorem DFA_run_from_reachable_sound (M : DFA.t) (q1 : M.(DFA.state)) (q2 : M.(DFA.state)) (s : list ascii)
  (RUN : DFA.run_from M q1 s = Some q2)
  : DFA.reachable M q1 s q2.
Proof.
  revert q1 q2 RUN. induction s as [ | a s IH]; simpl; i.
  - inv RUN. eauto with *.
  - destruct (M.(DFA.step) q1 a) as [q' | ] eqn: STEP; try congruence.
    eauto with *.
Qed.

Theorem DFA_run_from_reachable_complete (M : DFA.t) (q1 : M.(DFA.state)) (q2 : M.(DFA.state)) (s : list ascii)
  (REACH : DFA.reachable M q1 s q2)
  : DFA.run_from M q1 s = Some q2.
Proof.
  induction REACH as [q | q1' q2' q3 a s STEP REST IH]; simpl.
  - reflexivity.
  - inv STEP. rewrite STEP0. exact IH.
Qed.

Corollary DFA_reachable_unique (M : DFA.t) (q : M.(DFA.state)) (q1 : M.(DFA.state)) (q2 : M.(DFA.state)) (s : list ascii)
  (R1 : DFA.reachable M q s q1)
  (R2 : DFA.reachable M q s q2)
  : q1 = q2.
Proof.
  pose proof (DFA_run_from_reachable_complete M q q1 s R1) as RUN1.
  pose proof (DFA_run_from_reachable_complete M q q2 s R2) as RUN2.
  congruence.
Qed.

Theorem DFA_acceptsb_spec (M : DFA.t) (s : list ascii)
  : DFA.acceptsb M s = true <-> DFA.accepts M s.
Proof.
  unfold DFA.acceptsb, DFA.accepts.
  destruct (DFA.run M s) as [q | ] eqn: RUN; split; i; des; try congruence; eauto.
Qed.

Theorem DFA_run_from_app (M : DFA.t) (q1 : M.(DFA.state)) (q2 : M.(DFA.state)) (s1 : list ascii) (s2 : list ascii)
  (RUN1 : DFA.run_from M q1 s1 = Some q2)
  : DFA.run_from M q1 (s1 ++ s2) = DFA.run_from M q2 s2.
Proof.
  revert q1 q2 RUN1. induction s1 as [ | a s1 IH]; simpl; i.
  - inv RUN1. reflexivity.
  - destruct (M.(DFA.step) q1 a) as [q' | ] eqn: STEP; try congruence.
    eauto.
Qed.

Module Thompson.

#[projections(primitive)]
Record char_edge : Set :=
  mkCharEdge
  { char_edge_src : nat
  ; char_edge_label : ascii
  ; char_edge_dst : nat
  }.

#[projections(primitive)]
Record fragment : Set :=
  mkFragment
  { frag_size : nat
  ; frag_start : nat
  ; frag_accept : nat
  ; frag_eps_edges : list (nat * nat)
  ; frag_char_edges : list char_edge
  }.

Definition offset_eps_edge (offset : nat) (edge : nat * nat) : nat * nat :=
  (offset + fst edge, offset + snd edge).

Definition offset_char_edge (offset : nat) (edge : char_edge) : char_edge :=
  mkCharEdge (offset + edge.(char_edge_src)) edge.(char_edge_label) (offset + edge.(char_edge_dst)).

Definition offset_fragment (offset : nat) (f : fragment) : fragment :=
  mkFragment f.(frag_size) (offset + f.(frag_start)) (offset + f.(frag_accept)) (map (offset_eps_edge offset) f.(frag_eps_edges)) (map (offset_char_edge offset) f.(frag_char_edges)).

Definition eps_step_of (edges : list (nat * nat)) (q : nat) : list nat :=
  fold_right (fun edge => fun acc => if Nat.eq_dec (fst edge) q then snd edge :: acc else acc) [] edges.

Definition char_step_of (edges : list char_edge) (q : nat) (a : ascii) : list nat :=
  let go edge acc := if Nat.eq_dec edge.(char_edge_src) q then if Ascii.ascii_dec edge.(char_edge_label) a then edge.(char_edge_dst) :: acc else acc else acc in
  fold_right go [] edges.

Definition of_fragment (f : fragment) : ENFA.t :=
  ENFA.mk nat nat_hasEqDec (seq 0 f.(frag_size)) f.(frag_start) [f.(frag_accept)] (eps_step_of f.(frag_eps_edges)) (char_step_of f.(frag_char_edges)).

Definition fragment_accepts (f : fragment) (s : list ascii) : Prop :=
  ENFA.reachable (of_fragment f) f.(frag_start) s f.(frag_accept).

Lemma eps_step_of_spec (edges : list (nat * nat)) (q : nat) (q' : nat)
  : L.In q' (eps_step_of edges q) <-> L.In (q, q') edges.
Proof.
  induction edges as [ | [src dst] edges IH]; simpl.
  - split; i; contradiction.
  - destruct (Nat.eq_dec src q) as [EQ | NE]; simpl.
    + subst src. split; i.
      * destruct H as [EQ | IN].
        { subst dst. left. reflexivity. }
        { right. rewrite <- IH. exact IN. }
      * destruct H as [EQ | IN].
        { inv EQ. left. reflexivity. }
        { right. rewrite IH. exact IN. }
    + split; i.
      * right. rewrite <- IH. exact H.
      * destruct H as [EQ | IN].
        { inv EQ. contradiction. }
        { rewrite IH. exact IN. }
Qed.

Definition char_edge_matches (q : nat) (a : ascii) (q' : nat) (edge : char_edge) : Prop :=
  edge.(char_edge_src) = q /\ edge.(char_edge_label) = a /\ edge.(char_edge_dst) = q'.

Lemma char_step_of_spec (edges : list char_edge) (q : nat) (a : ascii) (q' : nat)
  : L.In q' (char_step_of edges q a) <-> (exists edge, L.In edge edges /\ char_edge_matches q a q' edge).
Proof.
  induction edges as [ | [src label dst] edges IH]; simpl.
  - split; i.
    + contradiction.
    + destruct H as (edge & [] & _).
  - destruct (Nat.eq_dec src q) as [SRC | SRC]; simpl.
    + destruct (Ascii.ascii_dec label a) as [LABEL | LABEL]; simpl.
      * subst src label. split; i.
        { destruct H as [EQ | IN].
          - subst q'. exists (mkCharEdge q a dst). split; [left; reflexivity | simpl; repeat split].
          - rewrite IH in IN. destruct IN as (edge & IN & MATCH). exists edge. split; [right; exact IN | exact MATCH].
        }
        { destruct H as (edge & [EQ | IN] & MATCH).
          - inv EQ. simpl in MATCH. destruct MATCH as (_ & _ & DST). subst q'. left. reflexivity.
          - right. rewrite IH. exists edge. split; [exact IN | exact MATCH].
        }
      * subst src. split; i.
        { rewrite IH in H. destruct H as (edge & IN & MATCH). exists edge. split; [right; exact IN | exact MATCH]. }
        { destruct H as (edge & [EQ | IN] & MATCH).
          - inv EQ. simpl in MATCH. destruct MATCH as (_ & LABEL_EQ & _). contradiction.
          - rewrite IH. exists edge. split; [exact IN | exact MATCH].
        }
    + split; i.
      * rewrite IH in H. destruct H as (edge & IN & MATCH). exists edge. split; [right; exact IN | exact MATCH].
      * destruct H as (edge & [EQ | IN] & MATCH).
        { inv EQ. simpl in MATCH. destruct MATCH as (SRC_EQ & _). contradiction. }
        { rewrite IH. exists edge. split; [exact IN | exact MATCH]. }
Qed.

Lemma eps_step_of_offset (offset : nat) (edges : list (nat * nat)) (q : nat) (q' : nat)
  : L.In (offset + q') (eps_step_of (map (offset_eps_edge offset) edges) (offset + q)) <-> L.In q' (eps_step_of edges q).
Proof.
  rewrite eps_step_of_spec. rewrite eps_step_of_spec. rewrite in_map_iff. split; i.
  - destruct H as ((src & dst) & EQ & IN). simpl in EQ. inv EQ.
    replace src with q in * by lia. replace dst with q' in * by lia. exact IN.
  - exists (q, q'). split; [reflexivity | exact H].
Qed.

Lemma char_step_of_offset (offset : nat) (edges : list char_edge) (q : nat) (a : ascii) (q' : nat)
  : L.In (offset + q') (char_step_of (map (offset_char_edge offset) edges) (offset + q) a) <-> L.In q' (char_step_of edges q a).
Proof.
  rewrite char_step_of_spec. rewrite char_step_of_spec. split; i.
  - destruct H as (edge & IN & MATCH). rewrite in_map_iff in IN. destruct IN as ([src label dst] & EQ & IN). subst edge.
    simpl in MATCH. destruct MATCH as (SRC_EQ & LABEL_EQ & DST_EQ).
    cbn in SRC_EQ, LABEL_EQ, DST_EQ.
    exists (mkCharEdge src label dst). split.
    + exact IN.
    + unfold char_edge_matches. simpl. repeat split; [lia | exact LABEL_EQ | lia].
  - destruct H as (edge & IN & MATCH). exists (offset_char_edge offset edge). split.
    + rewrite in_map_iff. exists edge. split; [reflexivity | exact IN].
    + unfold char_edge_matches in *. destruct edge as [src label dst]. simpl in *.
      destruct MATCH as (SRC_EQ & LABEL_EQ & DST_EQ). subst. repeat split; try lia.
Qed.

Lemma offset_eps_edge_in_inv (offset : nat) (edges : list (nat * nat)) (q : nat) (q' : nat)
  (IN : L.In (offset + q, q') (map (offset_eps_edge offset) edges))
  : exists q0, q' = offset + q0 /\ L.In (q, q0) edges.
Proof.
  rewrite in_map_iff in IN. destruct IN as ((src & dst) & EQ & IN). simpl in EQ. inv EQ.
  replace src with q in * by lia. exists dst. split; eauto.
Qed.

Lemma offset_char_edge_in_inv (offset : nat) (edges : list char_edge) (q : nat) (a : ascii) (q' : nat)
  (IN : exists edge, L.In edge (map (offset_char_edge offset) edges) /\ char_edge_matches (offset + q) a q' edge)
  : exists q0, q' = offset + q0 /\ L.In q0 (char_step_of edges q a).
Proof.
  destruct IN as (edge & IN & MATCH). rewrite in_map_iff in IN.
  destruct IN as ([src label dst] & EQ & IN). subst edge. unfold char_edge_matches in MATCH. simpl in MATCH.
  destruct MATCH as (SRC_EQ & LABEL_EQ & DST_EQ). subst label q'.
  replace src with q in * by lia. exists dst. split; [reflexivity | ].
  rewrite char_step_of_spec. exists (mkCharEdge q a dst). split; [exact IN | unfold char_edge_matches; simpl; repeat split; reflexivity].
Qed.

Definition eps_edges_in_bounds (f : fragment) : Prop :=
  forall src, forall dst, L.In (src, dst) f.(frag_eps_edges) -> (src < f.(frag_size) /\ dst < f.(frag_size)).

Definition char_edges_in_bounds (f : fragment) : Prop :=
  forall edge, L.In edge f.(frag_char_edges) -> (edge.(char_edge_src) < f.(frag_size) /\ edge.(char_edge_dst) < f.(frag_size)).

Lemma eps_step_of_bound (f : fragment) (q : nat) (q' : nat)
  (WF : eps_edges_in_bounds f)
  (STEP : L.In q' (eps_step_of f.(frag_eps_edges) q))
  : q' < f.(frag_size).
Proof.
  rewrite eps_step_of_spec in STEP. pose proof (WF q q' STEP) as (_ & DST). exact DST.
Qed.

Lemma char_step_of_bound (f : fragment) (q : nat) (a : ascii) (q' : nat)
  (WF : char_edges_in_bounds f)
  (STEP : L.In q' (char_step_of f.(frag_char_edges) q a))
  : q' < f.(frag_size).
Proof.
  rewrite char_step_of_spec in STEP. destruct STEP as (edge & IN & MATCH).
  pose proof (WF edge IN) as (_ & DST). unfold char_edge_matches in MATCH. destruct MATCH as (_ & _ & EQ). subst q'. exact DST.
Qed.

Lemma offset_fragment_eps_edges_in_bounds (offset : nat) (f : fragment)
  (WF : eps_edges_in_bounds f)
  : forall src, forall dst, L.In (src, dst) (frag_eps_edges (offset_fragment offset f)) -> (offset <= src /\ src < offset + f.(frag_size) /\ offset <= dst /\ dst < offset + f.(frag_size)).
Proof.
  intros src dst IN. simpl in IN. rewrite in_map_iff in IN.
  destruct IN as ((src0 & dst0) & EQ & IN). simpl in EQ. inv EQ.
  pose proof (WF src0 dst0 IN) as (SRC & DST). lia.
Qed.

Lemma offset_fragment_char_edges_in_bounds (offset : nat) (f : fragment)
  (WF : char_edges_in_bounds f)
  : forall edge, L.In edge (frag_char_edges (offset_fragment offset f)) -> (offset <= edge.(char_edge_src) /\ edge.(char_edge_src) < offset + f.(frag_size) /\ offset <= edge.(char_edge_dst) /\ edge.(char_edge_dst) < offset + f.(frag_size)).
Proof.
  intros edge IN. simpl in IN. rewrite in_map_iff in IN.
  destruct IN as ([src label dst] & EQ & IN). subst edge. simpl.
  pose proof (WF (mkCharEdge src label dst) IN) as (SRC & DST). simpl in *. lia.
Qed.

Lemma offset_fragment_reachable (offset : nat) (f : fragment) (q1 : nat) (q2 : nat) (s : list ascii)
  (REACH : ENFA.reachable (of_fragment f) q1 s q2)
  : ENFA.reachable (of_fragment (offset_fragment offset f)) (offset + q1) s (offset + q2).
Proof.
  induction REACH as [q | q1' q2' q3' s STEP REST IH | q1' q2' q3' a s STEP REST IH]; simpl in *.
  - eauto with *.
  - eapply ENFA.reachable_eps with (q2 := offset + q2'); eauto.
    simpl. rewrite eps_step_of_offset. exact STEP.
  - eapply ENFA.reachable_char with (q2 := offset + q2'); eauto.
    simpl. rewrite char_step_of_offset. exact STEP.
Qed.

Lemma offset_fragment_accepts (offset : nat) (f : fragment) (s : list ascii)
  (ACCEPTS : fragment_accepts f s)
  : ENFA.reachable (of_fragment (offset_fragment offset f)) (frag_start (offset_fragment offset f)) s (frag_accept (offset_fragment offset f)).
Proof.
  unfold fragment_accepts in ACCEPTS. simpl.
  eapply offset_fragment_reachable. exact ACCEPTS.
Qed.

Lemma eps_step_of_incl (edges1 : list (nat * nat)) (edges2 : list (nat * nat)) (q : nat) (q' : nat)
  (INCL : forall edge, L.In edge edges1 -> L.In edge edges2)
  (STEP : L.In q' (eps_step_of edges1 q))
  : L.In q' (eps_step_of edges2 q).
Proof.
  rewrite eps_step_of_spec in STEP. rewrite eps_step_of_spec.
  eapply INCL. exact STEP.
Qed.

Lemma char_step_of_incl (edges1 : list char_edge) (edges2 : list char_edge) (q : nat) (a : ascii) (q' : nat)
  (INCL : forall edge, L.In edge edges1 -> L.In edge edges2)
  (STEP : L.In q' (char_step_of edges1 q a))
  : L.In q' (char_step_of edges2 q a).
Proof.
  rewrite char_step_of_spec in STEP. rewrite char_step_of_spec.
  destruct STEP as (edge & IN & MATCH).
  exists edge. split; [eapply INCL; exact IN | exact MATCH].
Qed.

Lemma fragment_reachable_incl (f : fragment) (g : fragment) (q1 : nat) (q2 : nat) (s : list ascii)
  (EPS_INCL : forall edge, L.In edge f.(frag_eps_edges) -> L.In edge g.(frag_eps_edges))
  (CHAR_INCL : forall edge, L.In edge f.(frag_char_edges) -> L.In edge g.(frag_char_edges))
  (REACH : ENFA.reachable (of_fragment f) q1 s q2)
  : ENFA.reachable (of_fragment g) q1 s q2.
Proof.
  induction REACH as [q | q1' q2' q3' s STEP REST IH | q1' q2' q3' a s STEP REST IH]; simpl in *.
  - eauto with *.
  - eapply ENFA.reachable_eps with (q2 := q2'); eauto.
    eapply eps_step_of_incl; eauto.
  - eapply ENFA.reachable_char with (q2 := q2'); eauto.
    eapply char_step_of_incl; eauto.
Qed.

Lemma fragment_reachable_project (f : fragment) (g : fragment) (offset : nat) (q1 : nat) (q2 : nat) (s : list ascii)
  (EPS_CASE : forall q, forall q', q < f.(frag_size) -> L.In q' (eps_step_of g.(frag_eps_edges) (offset + q)) -> (exists q0, q' = offset + q0 /\ q0 < f.(frag_size) /\ L.In q0 (eps_step_of f.(frag_eps_edges) q)))
  (CHAR_CASE : forall q, forall a, forall q', q < f.(frag_size) -> L.In q' (char_step_of g.(frag_char_edges) (offset + q) a) -> (exists q0, q' = offset + q0 /\ q0 < f.(frag_size) /\ L.In q0 (char_step_of f.(frag_char_edges) q a)))
  (BOUND : q1 < f.(frag_size))
  (REACH : ENFA.reachable (of_fragment g) (offset + q1) s (offset + q2))
  : ENFA.reachable (of_fragment f) q1 s q2.
Proof.
  remember (offset + q1) as src eqn: SRC_EQ. remember (offset + q2) as dst eqn: DST_EQ.
  revert q1 q2 BOUND SRC_EQ DST_EQ. induction REACH as [q | q1' q2' q3' s STEP REST IH | q1' q2' q3' a s STEP REST IH]; intros q0 qT BOUND SRC_EQ DST_EQ; subst.
  - replace qT with q0 by lia. eauto with *.
  - pose proof (EPS_CASE q0 q2' BOUND STEP) as (q2'' & EQ & BOUND' & STEP'). subst q2'.
    eapply ENFA.reachable_eps with (q2 := q2''); eauto.
  - pose proof (CHAR_CASE q0 a q2' BOUND STEP) as (q2'' & EQ & BOUND' & STEP'). subst q2'.
    eapply ENFA.reachable_char with (q2 := q2''); eauto.
Qed.

Lemma fragment_reachable_split_at_exit (f : fragment) (g : fragment) (offset : nat) (exit : nat) (target : nat) (q : nat) (s : list ascii)
  (TARGET_OUTSIDE : forall q, q < f.(frag_size) -> offset + q <> target)
  (EPS_CASE : forall q, forall q', q < f.(frag_size) -> L.In q' (eps_step_of g.(frag_eps_edges) (offset + q)) -> (q = f.(frag_accept) /\ q' = exit) \/ (exists q0, q' = offset + q0 /\ q0 < f.(frag_size) /\ L.In q0 (eps_step_of f.(frag_eps_edges) q)))
  (CHAR_CASE : forall q, forall a, forall q', q < f.(frag_size) -> L.In q' (char_step_of g.(frag_char_edges) (offset + q) a) -> (exists q0, q' = offset + q0 /\ q0 < f.(frag_size) /\ L.In q0 (char_step_of f.(frag_char_edges) q a)))
  (BOUND : q < f.(frag_size))
  (REACH : ENFA.reachable (of_fragment g) (offset + q) s target)
  : exists s1, exists s2, s = s1 ++ s2 /\ ENFA.reachable (of_fragment f) q s1 f.(frag_accept) /\ ENFA.reachable (of_fragment g) exit s2 target.
Proof.
  remember (offset + q) as src eqn: SRC_EQ. remember target as dst eqn: DST_EQ.
  revert q BOUND SRC_EQ DST_EQ. induction REACH as [q0 | q1' q2' q3' s STEP REST IH | q1' q2' q3' a s STEP REST IH]; intros q0' BOUND SRC_EQ DST_EQ; subst.
  - exfalso. eapply TARGET_OUTSIDE; eauto.
  - pose proof (EPS_CASE q0' q2' BOUND STEP) as [(ACCEPT & EXIT) | (q2'' & EQ & BOUND' & STEP')].
    + subst q0' q2'. exists []. exists s. simpl. splits; eauto with *.
    + subst q2'. pose proof (IH TARGET_OUTSIDE q2'' BOUND' eq_refl eq_refl) as (s1 & s2 & EQ_s & REACH1 & REACH2). subst s.
      exists s1. exists s2. splits; eauto with *.
  - pose proof (CHAR_CASE q0' a q2' BOUND STEP) as (q2'' & EQ & BOUND' & STEP'). subst q2'.
    pose proof (IH TARGET_OUTSIDE q2'' BOUND' eq_refl eq_refl) as (s1 & s2 & EQ_s & REACH1 & REACH2). subst s.
    exists (a :: s1). exists s2. splits; simpl; eauto with *.
Qed.

Lemma fragment_reachable_split_at_two_exits (f : fragment) (g : fragment) (offset : nat) (exit1 : nat) (exit2 : nat) (target : nat) (q : nat) (s : list ascii)
  (TARGET_OUTSIDE : forall q, q < f.(frag_size) -> offset + q <> target)
  (EPS_CASE : forall q, forall q', q < f.(frag_size) -> L.In q' (eps_step_of g.(frag_eps_edges) (offset + q)) -> (q = f.(frag_accept) /\ (q' = exit1 \/ q' = exit2)) \/ (exists q0, q' = offset + q0 /\ q0 < f.(frag_size) /\ L.In q0 (eps_step_of f.(frag_eps_edges) q)))
  (CHAR_CASE : forall q, forall a, forall q', q < f.(frag_size) -> L.In q' (char_step_of g.(frag_char_edges) (offset + q) a) -> (exists q0, q' = offset + q0 /\ q0 < f.(frag_size) /\ L.In q0 (char_step_of f.(frag_char_edges) q a)))
  (BOUND : q < f.(frag_size))
  (REACH : ENFA.reachable (of_fragment g) (offset + q) s target)
  : exists exit, exists s1, exists s2, s = s1 ++ s2 /\ ENFA.reachable (of_fragment f) q s1 f.(frag_accept) /\ (exit = exit1 \/ exit = exit2) /\ ENFA.reachable (of_fragment g) exit s2 target.
Proof.
  remember (offset + q) as src eqn: SRC_EQ. remember target as dst eqn: DST_EQ.
  revert q BOUND SRC_EQ DST_EQ. induction REACH as [q0 | q1' q2' q3' s STEP REST IH | q1' q2' q3' a s STEP REST IH]; intros q0' BOUND SRC_EQ DST_EQ; subst.
  - exfalso. eapply TARGET_OUTSIDE; eauto.
  - pose proof (EPS_CASE q0' q2' BOUND STEP) as [(ACCEPT & [EXIT | EXIT]) | (q2'' & EQ & BOUND' & STEP')].
    + subst q0' q2'. exists exit1. exists []. exists s. simpl. splits; eauto with *.
    + subst q0' q2'. exists exit2. exists []. exists s. simpl. splits; eauto with *.
    + subst q2'. pose proof (IH TARGET_OUTSIDE q2'' BOUND' eq_refl eq_refl) as (exit & s1 & s2 & EQ_s & REACH1 & EXIT_CASE & REACH2). subst s.
      exists exit. exists s1. exists s2. splits; eauto with *.
  - pose proof (CHAR_CASE q0' a q2' BOUND STEP) as (q2'' & EQ & BOUND' & STEP'). subst q2'.
    pose proof (IH TARGET_OUTSIDE q2'' BOUND' eq_refl eq_refl) as (exit & s1 & s2 & EQ_s & REACH1 & EXIT_CASE & REACH2). subst s.
    exists exit. exists (a :: s1). exists s2. splits; simpl; eauto with *.
Qed.

Fixpoint compile (e : regex ascii) {struct e} : fragment :=
  match e with
  | Re.Null => mkFragment 2 0 1 [] []
  | Re.Empty => mkFragment 2 0 1 [(0, 1)] []
  | Re.Char c => mkFragment 2 0 1 [] [mkCharEdge 0 c 1]
  | Re.Union e1 e2 =>
    let f1 := compile e1 in
    let f2 := compile e2 in
    let f1' := offset_fragment 1 f1 in
    let f2' := offset_fragment (1 + f1.(frag_size)) f2 in
    let accept := 1 + f1.(frag_size) + f2.(frag_size) in
    mkFragment (S accept) 0 accept ([(0, f1'.(frag_start)); (0, f2'.(frag_start)); (f1'.(frag_accept), accept); (f2'.(frag_accept), accept)] ++ f1'.(frag_eps_edges) ++ f2'.(frag_eps_edges)) (f1'.(frag_char_edges) ++ f2'.(frag_char_edges))
  | Re.Append e1 e2 =>
    let f1 := compile e1 in
    let f2 := compile e2 in
    let f2' := offset_fragment f1.(frag_size) f2 in
    mkFragment (f1.(frag_size) + f2.(frag_size)) f1.(frag_start) f2'.(frag_accept) (f1.(frag_eps_edges) ++ [(f1.(frag_accept), f2'.(frag_start))] ++ f2'.(frag_eps_edges)) (f1.(frag_char_edges) ++ f2'.(frag_char_edges))
  | Re.Star e1 =>
    let f := compile e1 in
    let f' := offset_fragment 1 f in
    let accept := 1 + f.(frag_size) in
    mkFragment (S accept) 0 accept ([(0, accept); (0, f'.(frag_start)); (f'.(frag_accept), f'.(frag_start)); (f'.(frag_accept), accept)] ++ f'.(frag_eps_edges)) f'.(frag_char_edges)
  end.

Definition to_enfa (e : regex ascii) : ENFA.t :=
  of_fragment (compile e).

Lemma offset_fragment_size (offset : nat) (f : fragment)
  : frag_size (offset_fragment offset f) = frag_size f.
Proof.
  reflexivity.
Qed.

Lemma offset_fragment_start (offset : nat) (f : fragment)
  : frag_start (offset_fragment offset f) = offset + frag_start f.
Proof.
  reflexivity.
Qed.

Lemma offset_fragment_accept (offset : nat) (f : fragment)
  : frag_accept (offset_fragment offset f) = offset + frag_accept f.
Proof.
  reflexivity.
Qed.

Lemma compile_size_ge_2 (e : regex ascii)
  : 2 <= frag_size (compile e).
Proof.
  induction e; simpl; lia.
Qed.

Lemma compile_start_lt_size (e : regex ascii)
  : frag_start (compile e) < frag_size (compile e).
Proof.
  induction e; simpl; lia.
Qed.

Lemma compile_accept_lt_size (e : regex ascii)
  : frag_accept (compile e) < frag_size (compile e).
Proof.
  induction e; simpl; lia.
Qed.

Lemma compile_edges_in_bounds (e : regex ascii)
  : eps_edges_in_bounds (compile e) /\ char_edges_in_bounds (compile e).
Proof.
  induction e as [ | | c | e1 (EPS1 & CHAR1) e2 (EPS2 & CHAR2) | e1 (EPS1 & CHAR1) e2 (EPS2 & CHAR2) | e (EPS & CHAR)]; simpl.
  - split; [intros src dst IN; contradiction | intros edge IN; contradiction].
  - split.
    + intros src dst IN. destruct IN as [EQ | []]. inv EQ. simpl. lia.
    + intros edge IN. contradiction.
  - split.
    + intros src dst IN. contradiction.
    + intros edge IN. destruct IN as [EQ | []]. inv EQ. simpl. lia.
  - split.
    + intros src dst IN. repeat rewrite in_app_iff in IN.
      destruct IN as [EQ | IN].
      { inv EQ; simpl; pose proof (compile_start_lt_size e1); lia. }
      destruct IN as [EQ | IN].
      { inv EQ; simpl; pose proof (compile_start_lt_size e2); lia. }
      destruct IN as [EQ | IN].
      { inv EQ; simpl; pose proof (compile_accept_lt_size e1); lia. }
      destruct IN as [EQ | IN].
      { inv EQ; simpl; pose proof (compile_accept_lt_size e2); lia. }
      rewrite in_app_iff in IN. destruct IN as [IN | IN].
      * pose proof (offset_fragment_eps_edges_in_bounds 1 (compile e1) EPS1 src dst IN) as (_ & SRC & _ & DST).
        pose proof (compile_size_ge_2 e2). simpl in *. lia.
      * pose proof (offset_fragment_eps_edges_in_bounds (1 + frag_size (compile e1)) (compile e2) EPS2 src dst IN) as (_ & SRC & _ & DST). simpl in *. lia.
    + intros edge IN. simpl in IN. rewrite in_app_iff in IN.
      destruct IN as [IN | IN].
      * pose proof (offset_fragment_char_edges_in_bounds 1 (compile e1) CHAR1 edge IN) as (_ & SRC & _ & DST).
        pose proof (compile_size_ge_2 e2). simpl in *. lia.
      * pose proof (offset_fragment_char_edges_in_bounds (1 + frag_size (compile e1)) (compile e2) CHAR2 edge IN) as (_ & SRC & _ & DST). simpl in *. lia.
  - split.
    + intros src dst IN. simpl in IN. rewrite in_app_iff in IN.
      destruct IN as [IN | IN].
      * pose proof (EPS1 src dst IN) as (SRC & DST).
        pose proof (compile_size_ge_2 e2). simpl in *. lia.
      * destruct IN as [EQ | IN].
        { inv EQ. simpl. pose proof (compile_accept_lt_size e1). pose proof (compile_start_lt_size e2). lia. }
        pose proof (offset_fragment_eps_edges_in_bounds (frag_size (compile e1)) (compile e2) EPS2 src dst IN) as (_ & SRC & _ & DST). simpl in *. lia.
    + intros edge IN. simpl in IN. rewrite in_app_iff in IN.
      destruct IN as [IN | IN].
      * pose proof (CHAR1 edge IN) as (SRC & DST).
        pose proof (compile_size_ge_2 e2). simpl in *. lia.
      * pose proof (offset_fragment_char_edges_in_bounds (frag_size (compile e1)) (compile e2) CHAR2 edge IN) as (_ & SRC & _ & DST). simpl in *. lia.
  - split.
    + intros src dst IN. simpl in IN.
      destruct IN as [EQ | IN].
      { inv EQ; simpl; lia. }
      destruct IN as [EQ | IN].
      { inv EQ; simpl; pose proof (compile_start_lt_size e); lia. }
      destruct IN as [EQ | IN].
      { inv EQ; simpl; pose proof (compile_accept_lt_size e); pose proof (compile_start_lt_size e); lia. }
      destruct IN as [EQ | IN].
      { inv EQ; simpl; pose proof (compile_accept_lt_size e); lia. }
      pose proof (offset_fragment_eps_edges_in_bounds 1 (compile e) EPS src dst IN) as (_ & SRC & _ & DST). simpl in *. lia.
    + intros edge IN.
      pose proof (offset_fragment_char_edges_in_bounds 1 (compile e) CHAR edge IN) as (_ & SRC & _ & DST). simpl in *. lia.
Qed.

Lemma compile_accept_no_eps_step (e : regex ascii) (q : nat)
  (STEP : L.In q (eps_step_of (frag_eps_edges (compile e)) (frag_accept (compile e))))
  : False.
Proof.
  revert q STEP. induction e as [ | | c | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH]; intros q STEP.
  - simpl in STEP. contradiction.
  - simpl in STEP. destruct (Nat.eq_dec 0 1) as [EQ | NE]; simpl in STEP; [lia | contradiction].
  - simpl in STEP. contradiction.
  - rewrite eps_step_of_spec in STEP. simpl in STEP.
    destruct STEP as [EQ | STEP].
    { inv EQ. }
    destruct STEP as [EQ | STEP].
    { inv EQ. }
    destruct STEP as [EQ | STEP].
    { inv EQ. pose proof (compile_accept_lt_size e1). pose proof (compile_size_ge_2 e2). lia. }
    destruct STEP as [EQ | STEP].
    { inv EQ. pose proof (compile_accept_lt_size e2). lia. }
    rewrite in_app_iff in STEP. destruct STEP as [STEP | STEP].
    + pose proof (compile_edges_in_bounds e1) as (EPS1 & _).
      pose proof (offset_fragment_eps_edges_in_bounds 1 (compile e1) EPS1 (1 + frag_size (compile e1) + frag_size (compile e2)) q STEP) as (_ & SRC & _).
      lia.
    + pose proof (compile_edges_in_bounds e2) as (EPS2 & _).
      pose proof (offset_fragment_eps_edges_in_bounds (1 + frag_size (compile e1)) (compile e2) EPS2 (1 + frag_size (compile e1) + frag_size (compile e2)) q STEP) as (_ & SRC & _).
      lia.
  - rewrite eps_step_of_spec in STEP. simpl in STEP. rewrite in_app_iff in STEP.
    destruct STEP as [STEP | STEP].
    + pose proof (compile_edges_in_bounds e1) as (EPS1 & _).
      pose proof (EPS1 (frag_size (compile e1) + frag_accept (compile e2)) q STEP) as (SRC & _).
      pose proof (compile_accept_lt_size e2). lia.
    + destruct STEP as [EQ | STEP].
      { inv EQ. pose proof (compile_accept_lt_size e1). pose proof (compile_accept_lt_size e2). lia. }
      pose proof (offset_eps_edge_in_inv (frag_size (compile e1)) (frag_eps_edges (compile e2)) (frag_accept (compile e2)) q STEP) as (q0 & EQ & STEP').
      eapply IH2. rewrite eps_step_of_spec. exact STEP'.
  - rewrite eps_step_of_spec in STEP. simpl in STEP.
    destruct STEP as [EQ | STEP].
    { inv EQ. }
    destruct STEP as [EQ | STEP].
    { inv EQ. }
    destruct STEP as [EQ | STEP].
    { inv EQ. pose proof (compile_accept_lt_size e). lia. }
    destruct STEP as [EQ | STEP].
    { inv EQ. pose proof (compile_accept_lt_size e). lia. }
    pose proof (compile_edges_in_bounds e) as (EPS & _).
    pose proof (offset_fragment_eps_edges_in_bounds 1 (compile e) EPS (1 + frag_size (compile e)) q STEP) as (_ & SRC & _).
    lia.
Qed.

Lemma compile_accept_no_char_step (e : regex ascii) (a : ascii) (q : nat)
  (STEP : L.In q (char_step_of (frag_char_edges (compile e)) (frag_accept (compile e)) a))
  : False.
Proof.
  revert a q STEP. induction e as [ | | c | e1 IH1 e2 IH2 | e1 IH1 e2 IH2 | e IH]; intros a q STEP.
  - simpl in STEP. contradiction.
  - simpl in STEP. contradiction.
  - simpl in STEP. destruct (Nat.eq_dec 0 1) as [EQ | NE]; simpl in STEP; [lia | contradiction].
  - rewrite char_step_of_spec in STEP. destruct STEP as (edge & IN & MATCH). simpl in IN. rewrite in_app_iff in IN.
    destruct IN as [IN | IN].
    + pose proof (compile_edges_in_bounds e1) as (_ & CHAR1).
      pose proof (offset_fragment_char_edges_in_bounds 1 (compile e1) CHAR1 edge IN) as (_ & SRC & _).
      unfold char_edge_matches in MATCH. destruct MATCH as (SRC_EQ & _ & _). simpl in SRC_EQ, SRC. pose proof (compile_size_ge_2 e2). lia.
    + pose proof (compile_edges_in_bounds e2) as (_ & CHAR2).
      pose proof (offset_fragment_char_edges_in_bounds (1 + frag_size (compile e1)) (compile e2) CHAR2 edge IN) as (_ & SRC & _).
      unfold char_edge_matches in MATCH. destruct MATCH as (SRC_EQ & _ & _). simpl in SRC_EQ, SRC. lia.
  - rewrite char_step_of_spec in STEP. destruct STEP as (edge & IN & MATCH). simpl in IN. rewrite in_app_iff in IN.
    destruct IN as [IN | IN].
    + pose proof (compile_edges_in_bounds e1) as (_ & CHAR1).
      pose proof (CHAR1 edge IN) as (SRC & _). unfold char_edge_matches in MATCH. destruct MATCH as (SRC_EQ & _ & _). simpl in SRC_EQ. lia.
    + pose proof (offset_char_edge_in_inv (frag_size (compile e1)) (frag_char_edges (compile e2)) (frag_accept (compile e2)) a q) as INV.
      destruct INV as (q0 & EQ & STEP').
      { exists edge. split; [exact IN | exact MATCH]. }
      eapply IH2. exact STEP'.
  - rewrite char_step_of_spec in STEP. destruct STEP as (edge & IN & MATCH). simpl in IN.
    pose proof (compile_edges_in_bounds e) as (_ & CHAR).
    pose proof (offset_fragment_char_edges_in_bounds 1 (compile e) CHAR edge IN) as (_ & SRC & _).
    unfold char_edge_matches in MATCH. destruct MATCH as (SRC_EQ & _ & _). simpl in SRC_EQ, SRC. lia.
Qed.

Lemma compile_accept_reachable_stuck (e : regex ascii) (s : list ascii)
  (REACH : ENFA.reachable (of_fragment (compile e)) (frag_accept (compile e)) s (frag_accept (compile e)))
  : s = [].
Proof.
  pose proof (ENFA_reachable_stuck (of_fragment (compile e)) (frag_accept (compile e)) (frag_accept (compile e)) s) as STUCK.
  destruct STUCK as (EQ & _).
  - intros q STEP. simpl in STEP. eapply compile_accept_no_eps_step; eauto.
  - intros a q STEP. simpl in STEP. eapply compile_accept_no_char_step; eauto.
  - exact REACH.
  - exact EQ.
Qed.

Theorem to_enfa_start_in_states (e : regex ascii)
  : L.In (ENFA.start (to_enfa e)) (ENFA.states (to_enfa e)).
Proof.
  unfold to_enfa. simpl. rewrite L.in_seq. pose proof (compile_start_lt_size e). lia.
Qed.

Theorem to_enfa_accept_in_states (e : regex ascii) (q : ENFA.state (to_enfa e))
  (IN : L.In q (ENFA.accept_states (to_enfa e)))
  : L.In q (ENFA.states (to_enfa e)).
Proof.
  unfold to_enfa in *. simpl in *. destruct IN as [EQ | []]. subst q.
  rewrite L.in_seq. pose proof (compile_accept_lt_size e). lia.
Qed.

Theorem to_enfa_wf (e : regex ascii)
  : ENFA.wf (to_enfa e).
Proof.
  unfold ENFA.wf. splits.
  - eapply to_enfa_start_in_states.
  - intros q IN. eapply to_enfa_accept_in_states; eauto.
  - intros q q' IN STEP. unfold to_enfa in *. simpl in *.
    rewrite eps_step_of_spec in STEP.
    pose proof (compile_edges_in_bounds e) as (EPS & _).
    pose proof (EPS q q' STEP) as (_ & DST).
    rewrite L.in_seq. lia.
  - intros q q' a IN STEP. unfold to_enfa in *. simpl in *.
    rewrite char_step_of_spec in STEP.
    destruct STEP as (edge & EDGE & MATCH).
    pose proof (compile_edges_in_bounds e) as (_ & CHAR).
    pose proof (CHAR edge EDGE) as (_ & DST).
    unfold char_edge_matches in MATCH. destruct MATCH as (_ & _ & EQ). subst q'.
    rewrite L.in_seq. lia.
Qed.

Lemma compile_null_sound_similar (s : list ascii)
  (ACCEPTS : fragment_accepts (compile Re.Null) s)
  : s =~= Re.Null.
Proof.
  unfold fragment_accepts in ACCEPTS. simpl in ACCEPTS. inv ACCEPTS; simpl in *; try contradiction; lia.
Qed.

Lemma compile_empty_sound_similar (s : list ascii)
  (ACCEPTS : fragment_accepts (compile Re.Empty) s)
  : s =~= Re.Empty.
Proof.
  unfold fragment_accepts in ACCEPTS. simpl in ACCEPTS. inv ACCEPTS; simpl in *; try contradiction; try lia.
  destruct STEP as [EQ | []]. inv EQ.
  inv REST; simpl in *; try contradiction; eauto with *.
Qed.

Lemma compile_char_sound_similar (c : ascii) (s : list ascii)
  (ACCEPTS : fragment_accepts (compile (Re.Char c)) s)
  : s =~= Re.Char c.
Proof.
  unfold fragment_accepts in ACCEPTS. simpl in ACCEPTS. inv ACCEPTS; simpl in *; try contradiction; try lia.
  destruct (Ascii.ascii_dec c a) as [EQ | NE]; simpl in STEP; try contradiction. subst a.
  destruct STEP as [STEP | []]. inv STEP.
  inv REST; simpl in *; try contradiction.
  econs. reflexivity.
Qed.

Lemma compile_union_left_eps_case (e1 : regex ascii) (e2 : regex ascii) (q : nat) (q' : nat)
  (BOUND : q < frag_size (compile e1))
  (STEP : L.In q' (eps_step_of (frag_eps_edges (compile (Re.Union e1 e2))) (1 + q)))
  : (q = frag_accept (compile e1) /\ q' = 1 + frag_size (compile e1) + frag_size (compile e2)) \/ (exists q0, q' = 1 + q0 /\ q0 < frag_size (compile e1) /\ L.In q0 (eps_step_of (frag_eps_edges (compile e1)) q)).
Proof.
  rewrite eps_step_of_spec in STEP. simpl in STEP.
  destruct STEP as [EQ | STEP].
  { inv EQ. }
  destruct STEP as [EQ | STEP].
  { inv EQ. }
  destruct STEP as [EQ | STEP].
  { inv EQ. left. split; [lia | reflexivity]. }
  destruct STEP as [EQ | STEP].
  { inv EQ. pose proof (compile_accept_lt_size e2). lia. }
  rewrite in_app_iff in STEP. destruct STEP as [STEP | STEP].
  - pose proof (offset_eps_edge_in_inv 1 (frag_eps_edges (compile e1)) q q' STEP) as (q0 & EQ & IN).
    right. exists q0. split; [exact EQ | ]. split.
    + pose proof (compile_edges_in_bounds e1) as (EPS1 & _). pose proof (EPS1 q q0 IN) as (_ & DST). exact DST.
    + rewrite eps_step_of_spec. exact IN.
  - pose proof (compile_edges_in_bounds e2) as (EPS2 & _).
    pose proof (offset_fragment_eps_edges_in_bounds (1 + frag_size (compile e1)) (compile e2) EPS2 (1 + q) q' STEP) as (LOW & _).
    lia.
Qed.

Lemma compile_union_right_eps_case (e1 : regex ascii) (e2 : regex ascii) (q : nat) (q' : nat)
  (BOUND : q < frag_size (compile e2))
  (STEP : L.In q' (eps_step_of (frag_eps_edges (compile (Re.Union e1 e2))) (1 + frag_size (compile e1) + q)))
  : (q = frag_accept (compile e2) /\ q' = 1 + frag_size (compile e1) + frag_size (compile e2)) \/ (exists q0, q' = 1 + frag_size (compile e1) + q0 /\ q0 < frag_size (compile e2) /\ L.In q0 (eps_step_of (frag_eps_edges (compile e2)) q)).
Proof.
  rewrite eps_step_of_spec in STEP. simpl in STEP.
  destruct STEP as [EQ | STEP].
  { inv EQ. }
  destruct STEP as [EQ | STEP].
  { inv EQ. }
  destruct STEP as [EQ | STEP].
  { inv EQ. pose proof (compile_accept_lt_size e1). lia. }
  destruct STEP as [EQ | STEP].
  { inv EQ. left. split; [lia | reflexivity]. }
  rewrite in_app_iff in STEP. destruct STEP as [STEP | STEP].
  - pose proof (compile_edges_in_bounds e1) as (EPS1 & _).
    pose proof (offset_fragment_eps_edges_in_bounds 1 (compile e1) EPS1 (1 + frag_size (compile e1) + q) q' STEP) as (_ & SRC & _).
    lia.
  - pose proof (offset_eps_edge_in_inv (1 + frag_size (compile e1)) (frag_eps_edges (compile e2)) q q' STEP) as (q0 & EQ & IN).
    right. exists q0. split; [exact EQ | ]. split.
    + pose proof (compile_edges_in_bounds e2) as (EPS2 & _). pose proof (EPS2 q q0 IN) as (_ & DST). exact DST.
    + rewrite eps_step_of_spec. exact IN.
Qed.

Lemma compile_union_left_char_case (e1 : regex ascii) (e2 : regex ascii) (q : nat) (a : ascii) (q' : nat)
  (BOUND : q < frag_size (compile e1))
  (STEP : L.In q' (char_step_of (frag_char_edges (compile (Re.Union e1 e2))) (1 + q) a))
  : exists q0, q' = 1 + q0 /\ q0 < frag_size (compile e1) /\ L.In q0 (char_step_of (frag_char_edges (compile e1)) q a).
Proof.
  rewrite char_step_of_spec in STEP. destruct STEP as (edge & IN & MATCH). simpl in IN. rewrite in_app_iff in IN.
  destruct IN as [IN | IN].
  - pose proof (offset_char_edge_in_inv 1 (frag_char_edges (compile e1)) q a q') as INV.
    destruct INV as (q0 & EQ & STEP').
    { exists edge. split; [exact IN | exact MATCH]. }
    exists q0. split; [exact EQ | ]. split.
    + pose proof (compile_edges_in_bounds e1) as (_ & CHAR1). eapply char_step_of_bound; eauto.
    + exact STEP'.
  - pose proof (compile_edges_in_bounds e2) as (_ & CHAR2).
    pose proof (offset_fragment_char_edges_in_bounds (1 + frag_size (compile e1)) (compile e2) CHAR2 edge IN) as (LOW & _).
    unfold char_edge_matches in MATCH. destruct MATCH as (SRC_EQ & _ & _). simpl in SRC_EQ, LOW. lia.
Qed.

Lemma compile_union_right_char_case (e1 : regex ascii) (e2 : regex ascii) (q : nat) (a : ascii) (q' : nat)
  (BOUND : q < frag_size (compile e2))
  (STEP : L.In q' (char_step_of (frag_char_edges (compile (Re.Union e1 e2))) (1 + frag_size (compile e1) + q) a))
  : exists q0, q' = 1 + frag_size (compile e1) + q0 /\ q0 < frag_size (compile e2) /\ L.In q0 (char_step_of (frag_char_edges (compile e2)) q a).
Proof.
  rewrite char_step_of_spec in STEP. destruct STEP as (edge & IN & MATCH). simpl in IN. rewrite in_app_iff in IN.
  destruct IN as [IN | IN].
  - pose proof (compile_edges_in_bounds e1) as (_ & CHAR1).
    pose proof (offset_fragment_char_edges_in_bounds 1 (compile e1) CHAR1 edge IN) as (_ & SRC & _).
    unfold char_edge_matches in MATCH. destruct MATCH as (SRC_EQ & _ & _). simpl in SRC_EQ, SRC. lia.
  - pose proof (offset_char_edge_in_inv (1 + frag_size (compile e1)) (frag_char_edges (compile e2)) q a q') as INV.
    destruct INV as (q0 & EQ & STEP').
    { exists edge. split; [exact IN | exact MATCH]. }
    exists q0. split; [exact EQ | ]. split.
    + pose proof (compile_edges_in_bounds e2) as (_ & CHAR2). eapply char_step_of_bound; eauto.
    + exact STEP'.
Qed.

Lemma compile_union_left_sound_similar (e1 : regex ascii) (e2 : regex ascii) (s : list ascii)
  (SOUND1 : forall s0, fragment_accepts (compile e1) s0 -> s0 =~= e1)
  (REACH : ENFA.reachable (of_fragment (compile (Re.Union e1 e2))) (1 + frag_start (compile e1)) s (1 + frag_size (compile e1) + frag_size (compile e2)))
  : s =~= Re.Union e1 e2.
Proof.
  eapply fragment_reachable_split_at_exit with (f := compile e1) (offset := 1) (exit := 1 + frag_size (compile e1) + frag_size (compile e2)) (target := 1 + frag_size (compile e1) + frag_size (compile e2)) in REACH.
  - destruct REACH as (s1 & s2 & EQ & BODY & TAIL). pose proof (compile_accept_reachable_stuck (Re.Union e1 e2) s2 TAIL) as NIL. subst s2.
    rewrite app_nil_r in EQ. subst s. eapply Re.in_Union_l. eapply SOUND1. exact BODY.
  - intros q BOUND TARGET. lia.
  - intros q q' BOUND STEP. eapply compile_union_left_eps_case; eauto.
  - intros q a q' BOUND STEP. eapply compile_union_left_char_case; eauto.
  - eapply compile_start_lt_size.
Qed.

Lemma compile_union_right_sound_similar (e1 : regex ascii) (e2 : regex ascii) (s : list ascii)
  (SOUND2 : forall s0, fragment_accepts (compile e2) s0 -> s0 =~= e2)
  (REACH : ENFA.reachable (of_fragment (compile (Re.Union e1 e2))) (1 + frag_size (compile e1) + frag_start (compile e2)) s (1 + frag_size (compile e1) + frag_size (compile e2)))
  : s =~= Re.Union e1 e2.
Proof.
  eapply fragment_reachable_split_at_exit with (f := compile e2) (offset := 1 + frag_size (compile e1)) (exit := 1 + frag_size (compile e1) + frag_size (compile e2)) (target := 1 + frag_size (compile e1) + frag_size (compile e2)) in REACH.
  - destruct REACH as (s1 & s2 & EQ & BODY & TAIL). pose proof (compile_accept_reachable_stuck (Re.Union e1 e2) s2 TAIL) as NIL. subst s2.
    rewrite app_nil_r in EQ. subst s. eapply Re.in_Union_r. eapply SOUND2. exact BODY.
  - intros q BOUND TARGET. lia.
  - intros q q' BOUND STEP. eapply compile_union_right_eps_case; eauto.
  - intros q a q' BOUND STEP. eapply compile_union_right_char_case; eauto.
  - eapply compile_start_lt_size.
Qed.

Lemma compile_union_sound_similar (e1 : regex ascii) (e2 : regex ascii) (s : list ascii)
  (SOUND1 : forall s0, fragment_accepts (compile e1) s0 -> s0 =~= e1)
  (SOUND2 : forall s0, fragment_accepts (compile e2) s0 -> s0 =~= e2)
  (REACH : fragment_accepts (compile (Re.Union e1 e2)) s)
  : s =~= Re.Union e1 e2.
Proof.
  unfold fragment_accepts in REACH. simpl in REACH.
  pose proof (ENFA_reachable_inv _ _ _ _ REACH) as [(S_EQ & Q_EQ) | [(q2 & STEP & REST) | (a & s' & q2 & S_EQ & STEP & REST)]].
  - exfalso. lia.
  - change (L.In q2 (eps_step_of (frag_eps_edges (compile (Re.Union e1 e2))) 0)) in STEP.
    rewrite eps_step_of_spec in STEP. simpl in STEP.
    destruct STEP as [EQ | STEP].
    { inv EQ. eapply compile_union_left_sound_similar; eauto. }
    destruct STEP as [EQ | STEP].
    { inv EQ. eapply compile_union_right_sound_similar; eauto. }
    destruct STEP as [EQ | STEP].
    { inv EQ. }
    destruct STEP as [EQ | STEP].
    { inv EQ. }
    rewrite in_app_iff in STEP. destruct STEP as [STEP | STEP].
    + pose proof (compile_edges_in_bounds e1) as (EPS1 & _).
      pose proof (offset_fragment_eps_edges_in_bounds 1 (compile e1) EPS1 0 q2 STEP) as (LOW & _).
      lia.
    + pose proof (compile_edges_in_bounds e2) as (EPS2 & _).
      pose proof (offset_fragment_eps_edges_in_bounds (1 + frag_size (compile e1)) (compile e2) EPS2 0 q2 STEP) as (LOW & _).
      lia.
  - subst s. change (L.In q2 (char_step_of (frag_char_edges (compile (Re.Union e1 e2))) 0 a)) in STEP.
    rewrite char_step_of_spec in STEP. destruct STEP as (edge & IN & MATCH). simpl in IN. rewrite in_app_iff in IN.
    destruct IN as [IN | IN].
    + pose proof (compile_edges_in_bounds e1) as (_ & CHAR1).
      pose proof (offset_fragment_char_edges_in_bounds 1 (compile e1) CHAR1 edge IN) as (LOW & _).
      unfold char_edge_matches in MATCH. destruct MATCH as (SRC_EQ & _ & _). simpl in LOW, SRC_EQ. lia.
    + pose proof (compile_edges_in_bounds e2) as (_ & CHAR2).
      pose proof (offset_fragment_char_edges_in_bounds (1 + frag_size (compile e1)) (compile e2) CHAR2 edge IN) as (LOW & _).
      unfold char_edge_matches in MATCH. destruct MATCH as (SRC_EQ & _ & _). simpl in LOW, SRC_EQ. lia.
Qed.

Lemma compile_append_left_eps_case (e1 : regex ascii) (e2 : regex ascii) (q : nat) (q' : nat)
  (BOUND : q < frag_size (compile e1))
  (STEP : L.In q' (eps_step_of (frag_eps_edges (compile (Re.Append e1 e2))) q))
  : (q = frag_accept (compile e1) /\ q' = frag_size (compile e1) + frag_start (compile e2)) \/ (exists q0, q' = q0 /\ q0 < frag_size (compile e1) /\ L.In q0 (eps_step_of (frag_eps_edges (compile e1)) q)).
Proof.
  rewrite eps_step_of_spec in STEP. simpl in STEP. rewrite in_app_iff in STEP.
  destruct STEP as [STEP | STEP].
  - right. exists q'. split; [reflexivity | ]. split.
    + pose proof (compile_edges_in_bounds e1) as (EPS1 & _). pose proof (EPS1 q q' STEP) as (_ & DST). exact DST.
    + rewrite eps_step_of_spec. exact STEP.
  - destruct STEP as [EQ | STEP].
    + inv EQ. left. split; reflexivity.
    + pose proof (compile_edges_in_bounds e2) as (EPS2 & _).
      pose proof (offset_fragment_eps_edges_in_bounds (frag_size (compile e1)) (compile e2) EPS2 q q' STEP) as (LOW & _).
      lia.
Qed.

Lemma compile_append_left_char_case (e1 : regex ascii) (e2 : regex ascii) (q : nat) (a : ascii) (q' : nat)
  (BOUND : q < frag_size (compile e1))
  (STEP : L.In q' (char_step_of (frag_char_edges (compile (Re.Append e1 e2))) q a))
  : exists q0, q' = q0 /\ q0 < frag_size (compile e1) /\ L.In q0 (char_step_of (frag_char_edges (compile e1)) q a).
Proof.
  rewrite char_step_of_spec in STEP. destruct STEP as (edge & IN & MATCH). simpl in IN. rewrite in_app_iff in IN.
  destruct IN as [IN | IN].
  - exists q'. split; [reflexivity | ]. split.
    + pose proof (compile_edges_in_bounds e1) as (_ & CHAR1). pose proof (CHAR1 edge IN) as (_ & DST).
      unfold char_edge_matches in MATCH. destruct MATCH as (_ & _ & DST_EQ). subst q'. exact DST.
    + rewrite char_step_of_spec. exists edge. split; [exact IN | exact MATCH].
  - pose proof (compile_edges_in_bounds e2) as (_ & CHAR2).
    pose proof (offset_fragment_char_edges_in_bounds (frag_size (compile e1)) (compile e2) CHAR2 edge IN) as (LOW & _).
    unfold char_edge_matches in MATCH. destruct MATCH as (SRC_EQ & _ & _). simpl in LOW, SRC_EQ. lia.
Qed.

Lemma compile_append_right_eps_case (e1 : regex ascii) (e2 : regex ascii) (q : nat) (q' : nat)
  (BOUND : q < frag_size (compile e2))
  (STEP : L.In q' (eps_step_of (frag_eps_edges (compile (Re.Append e1 e2))) (frag_size (compile e1) + q)))
  : exists q0, q' = frag_size (compile e1) + q0 /\ q0 < frag_size (compile e2) /\ L.In q0 (eps_step_of (frag_eps_edges (compile e2)) q).
Proof.
  rewrite eps_step_of_spec in STEP. simpl in STEP. rewrite in_app_iff in STEP.
  destruct STEP as [STEP | STEP].
  - pose proof (compile_edges_in_bounds e1) as (EPS1 & _).
    pose proof (EPS1 (frag_size (compile e1) + q) q' STEP) as (SRC & _). lia.
  - destruct STEP as [EQ | STEP].
    + inv EQ. pose proof (compile_accept_lt_size e1). lia.
    + pose proof (offset_eps_edge_in_inv (frag_size (compile e1)) (frag_eps_edges (compile e2)) q q' STEP) as (q0 & EQ & IN).
      exists q0. split; [exact EQ | ]. split.
      * pose proof (compile_edges_in_bounds e2) as (EPS2 & _). pose proof (EPS2 q q0 IN) as (_ & DST). exact DST.
      * rewrite eps_step_of_spec. exact IN.
Qed.

Lemma compile_append_right_char_case (e1 : regex ascii) (e2 : regex ascii) (q : nat) (a : ascii) (q' : nat)
  (BOUND : q < frag_size (compile e2))
  (STEP : L.In q' (char_step_of (frag_char_edges (compile (Re.Append e1 e2))) (frag_size (compile e1) + q) a))
  : exists q0, q' = frag_size (compile e1) + q0 /\ q0 < frag_size (compile e2) /\ L.In q0 (char_step_of (frag_char_edges (compile e2)) q a).
Proof.
  rewrite char_step_of_spec in STEP. destruct STEP as (edge & IN & MATCH). simpl in IN. rewrite in_app_iff in IN.
  destruct IN as [IN | IN].
  - pose proof (compile_edges_in_bounds e1) as (_ & CHAR1).
    pose proof (CHAR1 edge IN) as (SRC & _). unfold char_edge_matches in MATCH. destruct MATCH as (SRC_EQ & _ & _). simpl in SRC_EQ. lia.
  - pose proof (offset_char_edge_in_inv (frag_size (compile e1)) (frag_char_edges (compile e2)) q a q') as INV.
    destruct INV as (q0 & EQ & STEP').
    { exists edge. split; [exact IN | exact MATCH]. }
    exists q0. split; [exact EQ | ]. split.
    + pose proof (compile_edges_in_bounds e2) as (_ & CHAR2). eapply char_step_of_bound; eauto.
    + exact STEP'.
Qed.

Lemma compile_append_sound_similar (e1 : regex ascii) (e2 : regex ascii) (s : list ascii)
  (SOUND1 : forall s0, fragment_accepts (compile e1) s0 -> s0 =~= e1)
  (SOUND2 : forall s0, fragment_accepts (compile e2) s0 -> s0 =~= e2)
  (REACH : fragment_accepts (compile (Re.Append e1 e2)) s)
  : s =~= Re.Append e1 e2.
Proof.
  unfold fragment_accepts in REACH. simpl in REACH.
  assert (TARGET_OUTSIDE : forall q, q < frag_size (compile e1) -> 0 + q <> frag_size (compile e1) + frag_accept (compile e2)).
  { intros q BOUND TARGET. pose proof (compile_accept_lt_size e2). lia. }
  assert (EPS_CASE1 : forall q, forall q', q < frag_size (compile e1) -> L.In q' (eps_step_of (frag_eps_edges (compile (Re.Append e1 e2))) (0 + q)) -> (q = frag_accept (compile e1) /\ q' = frag_size (compile e1) + frag_start (compile e2)) \/ (exists q0, q' = 0 + q0 /\ q0 < frag_size (compile e1) /\ L.In q0 (eps_step_of (frag_eps_edges (compile e1)) q))).
  { intros q q' BOUND STEP. simpl in *. pose proof (compile_append_left_eps_case e1 e2 q q' BOUND STEP) as STEP'. destruct STEP' as [STEP' | (q0 & EQ & BOUND' & STEP')].
    - left. exact STEP'.
    - right. exists q0. splits; eauto.
  }
  assert (CHAR_CASE1 : forall q, forall a, forall q', q < frag_size (compile e1) -> L.In q' (char_step_of (frag_char_edges (compile (Re.Append e1 e2))) (0 + q) a) -> (exists q0, q' = 0 + q0 /\ q0 < frag_size (compile e1) /\ L.In q0 (char_step_of (frag_char_edges (compile e1)) q a))).
  { intros q a q' BOUND STEP. simpl in *. pose proof (compile_append_left_char_case e1 e2 q a q' BOUND STEP) as (q0 & EQ & BOUND' & STEP'). exists q0. splits; eauto. }
  pose proof (fragment_reachable_split_at_exit (compile e1) (compile (Re.Append e1 e2)) 0 (frag_size (compile e1) + frag_start (compile e2)) (frag_size (compile e1) + frag_accept (compile e2)) (frag_start (compile e1)) s TARGET_OUTSIDE EPS_CASE1 CHAR_CASE1 (compile_start_lt_size e1) REACH) as (s1 & s2 & EQ & BODY1 & TAIL).
  subst s.
  assert (EPS_CASE2 : forall q, forall q', q < frag_size (compile e2) -> L.In q' (eps_step_of (frag_eps_edges (compile (Re.Append e1 e2))) (frag_size (compile e1) + q)) -> (exists q0, q' = frag_size (compile e1) + q0 /\ q0 < frag_size (compile e2) /\ L.In q0 (eps_step_of (frag_eps_edges (compile e2)) q))).
  { intros q q' BOUND STEP. eapply compile_append_right_eps_case; eauto. }
  assert (CHAR_CASE2 : forall q, forall a, forall q', q < frag_size (compile e2) -> L.In q' (char_step_of (frag_char_edges (compile (Re.Append e1 e2))) (frag_size (compile e1) + q) a) -> (exists q0, q' = frag_size (compile e1) + q0 /\ q0 < frag_size (compile e2) /\ L.In q0 (char_step_of (frag_char_edges (compile e2)) q a))).
  { intros q a q' BOUND STEP. eapply compile_append_right_char_case; eauto. }
  pose proof (fragment_reachable_project (compile e2) (compile (Re.Append e1 e2)) (frag_size (compile e1)) (frag_start (compile e2)) (frag_accept (compile e2)) s2 EPS_CASE2 CHAR_CASE2 (compile_start_lt_size e2) TAIL) as BODY2.
  eapply Re.in_Append.
  - eapply SOUND1. exact BODY1.
  - eapply SOUND2. exact BODY2.
Qed.

Lemma compile_star_inside_eps_case (e : regex ascii) (q : nat) (q' : nat)
  (BOUND : q < frag_size (compile e))
  (STEP : L.In q' (eps_step_of (frag_eps_edges (compile (Re.Star e))) (1 + q)))
  : (q = frag_accept (compile e) /\ (q' = 1 + frag_start (compile e) \/ q' = 1 + frag_size (compile e))) \/ (exists q0, q' = 1 + q0 /\ q0 < frag_size (compile e) /\ L.In q0 (eps_step_of (frag_eps_edges (compile e)) q)).
Proof.
  rewrite eps_step_of_spec in STEP. simpl in STEP.
  destruct STEP as [EQ | STEP].
  { inv EQ. }
  destruct STEP as [EQ | STEP].
  { inv EQ. }
  destruct STEP as [EQ | STEP].
  { inv EQ. left. split; [lia | left; reflexivity]. }
  destruct STEP as [EQ | STEP].
  { inv EQ. left. split; [lia | right; reflexivity]. }
  pose proof (offset_eps_edge_in_inv 1 (frag_eps_edges (compile e)) q q' STEP) as (q0 & EQ & IN).
  right. exists q0. split; [exact EQ | ]. split.
  - pose proof (compile_edges_in_bounds e) as (EPS & _). pose proof (EPS q q0 IN) as (_ & DST). exact DST.
  - rewrite eps_step_of_spec. exact IN.
Qed.

Lemma compile_star_inside_char_case (e : regex ascii) (q : nat) (a : ascii) (q' : nat)
  (BOUND : q < frag_size (compile e))
  (STEP : L.In q' (char_step_of (frag_char_edges (compile (Re.Star e))) (1 + q) a))
  : exists q0, q' = 1 + q0 /\ q0 < frag_size (compile e) /\ L.In q0 (char_step_of (frag_char_edges (compile e)) q a).
Proof.
  rewrite char_step_of_spec in STEP. destruct STEP as (edge & IN & MATCH). simpl in IN.
  pose proof (offset_char_edge_in_inv 1 (frag_char_edges (compile e)) q a q') as INV.
  destruct INV as (q0 & EQ & STEP').
  { exists edge. split; [exact IN | exact MATCH]. }
  exists q0. split; [exact EQ | ]. split.
  - pose proof (compile_edges_in_bounds e) as (_ & CHAR). eapply char_step_of_bound; eauto.
  - exact STEP'.
Qed.

Lemma compile_star_inside_sound_similar (e : regex ascii) (q : nat) (s : list ascii)
  (SOUND : forall s0, fragment_accepts (compile e) s0 -> s0 =~= e)
  (BOUND : q < frag_size (compile e))
  (REACH : ENFA.reachable (of_fragment (compile (Re.Star e))) (1 + q) s (1 + frag_size (compile e)))
  : exists s1, exists s2, s = s1 ++ s2 /\ ENFA.reachable (of_fragment (compile e)) q s1 (frag_accept (compile e)) /\ s2 =~= Re.Star e.
Proof.
  remember (1 + q) as src eqn: SRC_EQ. remember (1 + frag_size (compile e)) as dst eqn: DST_EQ.
  revert q BOUND SRC_EQ DST_EQ. induction REACH as [q0 | q1 q2 q3 s0 STEP REST IH | q1 q2 q3 a s0 STEP REST IH]; intros q0' BOUND SRC_EQ DST_EQ; subst.
  - exfalso. lia.
  - pose proof (compile_star_inside_eps_case e q0' q2 BOUND STEP) as [(ACCEPT & [LOOP | EXIT]) | (q2' & EQ & BOUND' & STEP')].
    + subst q0' q2. pose proof (IH (frag_start (compile e)) (compile_start_lt_size e) eq_refl eq_refl) as (s1 & s2 & EQ_s & BODY & STAR). subst s0.
      exists []. exists (s1 ++ s2). simpl. split.
      * reflexivity.
      * split.
        { eauto with *. }
        { eapply Re.in_Star_app.
          - eapply SOUND. exact BODY.
          - exact STAR.
        }
    + subst q0' q2. pose proof (compile_accept_reachable_stuck (Re.Star e) s0 REST) as NIL. subst s0.
      exists []. exists []. simpl. split.
      * reflexivity.
      * split; eauto with *.
    + subst q2. pose proof (IH q2' BOUND' eq_refl eq_refl) as (s1 & s2 & EQ_s & BODY & STAR). subst s0.
      exists s1. exists s2. split.
      * reflexivity.
      * split.
        { eapply ENFA.reachable_eps with (q2 := q2'); eauto. }
        { exact STAR. }
  - pose proof (compile_star_inside_char_case e q0' a q2 BOUND STEP) as (q2' & EQ & BOUND' & STEP'). subst q2.
    pose proof (IH q2' BOUND' eq_refl eq_refl) as (s1 & s2 & EQ_s & BODY & STAR). subst s0.
    exists (a :: s1). exists s2. simpl. split.
    + reflexivity.
    + split.
      * eapply ENFA.reachable_char with (q2 := q2'); eauto.
      * exact STAR.
Qed.

Lemma compile_star_sound_similar (e : regex ascii) (s : list ascii)
  (SOUND : forall s0, fragment_accepts (compile e) s0 -> s0 =~= e)
  (REACH : fragment_accepts (compile (Re.Star e)) s)
  : s =~= Re.Star e.
Proof.
  unfold fragment_accepts in REACH. simpl in REACH.
  pose proof (ENFA_reachable_inv _ _ _ _ REACH) as [(S_EQ & Q_EQ) | [(q2 & STEP & REST) | (a & s' & q2 & S_EQ & STEP & REST)]].
  - exfalso. lia.
  - change (L.In q2 (eps_step_of (frag_eps_edges (compile (Re.Star e))) 0)) in STEP.
    rewrite eps_step_of_spec in STEP. simpl in STEP.
    destruct STEP as [EQ | STEP].
    { inv EQ. pose proof (compile_accept_reachable_stuck (Re.Star e) s REST) as NIL. subst s. eauto with *. }
    destruct STEP as [EQ | STEP].
    { inv EQ. pose proof (compile_star_inside_sound_similar e (frag_start (compile e)) s SOUND (compile_start_lt_size e) REST) as (s1 & s2 & EQ_s & BODY & STAR). subst s.
      eapply Re.in_Star_app.
      - eapply SOUND. exact BODY.
      - exact STAR.
    }
    destruct STEP as [EQ | STEP].
    { inv EQ. }
    destruct STEP as [EQ | STEP].
    { inv EQ. }
    pose proof (compile_edges_in_bounds e) as (EPS & _).
    pose proof (offset_fragment_eps_edges_in_bounds 1 (compile e) EPS 0 q2 STEP) as (LOW & _).
    lia.
  - subst s. change (L.In q2 (char_step_of (frag_char_edges (compile (Re.Star e))) 0 a)) in STEP.
    rewrite char_step_of_spec in STEP. destruct STEP as (edge & IN & MATCH). simpl in IN.
    pose proof (compile_edges_in_bounds e) as (_ & CHAR).
    pose proof (offset_fragment_char_edges_in_bounds 1 (compile e) CHAR edge IN) as (LOW & _).
    unfold char_edge_matches in MATCH. destruct MATCH as (SRC_EQ & _ & _). simpl in LOW, SRC_EQ. lia.
Qed.

Lemma compile_star_tail_complete_similar (e : regex ascii) (s : list ascii)
  (BODY : forall s0, s0 =~= e -> fragment_accepts (compile e) s0)
  (IN : s =~= Re.Star e)
  : ENFA.reachable (of_fragment (compile (Re.Star e))) (1 + frag_accept (compile e)) s (1 + frag_size (compile e)).
Proof.
  remember (Re.Star e) as star_e eqn: STAR_EQ. induction IN as [ | c c' EQ | s0 e1 e2 IN IH | s0 e1 e2 IN IH | s1 s2 e1 e2 IN1 IH1 IN2 IH2 | e1 | e1 s1 s2 IN1 IH1 IN2 IH2]; inv STAR_EQ.
  - simpl. eapply ENFA.reachable_eps with (q2 := 1 + frag_size (compile e)).
    + change (L.In (1 + frag_size (compile e)) (eps_step_of (frag_eps_edges (compile (Re.Star e))) (1 + frag_accept (compile e)))).
      rewrite eps_step_of_spec. simpl. right. right. right. left. reflexivity.
    + eauto with *.
  - pose proof (BODY s1 IN1) as BODY_REACH.
    pose proof (offset_fragment_accepts 1 (compile e) s1 BODY_REACH) as BODY_OFF.
    pose proof (fragment_reachable_incl (offset_fragment 1 (compile e)) (compile (Re.Star e)) (1 + frag_start (compile e)) (1 + frag_accept (compile e)) s1) as BODY_INCL.
    assert (BODY_BIG : ENFA.reachable (of_fragment (compile (Re.Star e))) (1 + frag_start (compile e)) s1 (1 + frag_accept (compile e))).
    { eapply BODY_INCL.
      - intros edge EDGE. simpl in *. right. right. right. right. exact EDGE.
      - intros edge EDGE. simpl in *. exact EDGE.
      - exact BODY_OFF.
    }
    assert (LOOP : ENFA.reachable (of_fragment (compile (Re.Star e))) (1 + frag_accept (compile e)) s1 (1 + frag_accept (compile e))).
    { eapply ENFA.reachable_eps with (q2 := 1 + frag_start (compile e)).
      - change (L.In (1 + frag_start (compile e)) (eps_step_of (frag_eps_edges (compile (Re.Star e))) (1 + frag_accept (compile e)))).
        rewrite eps_step_of_spec. simpl. right. right. left. reflexivity.
      - exact BODY_BIG.
    }
    pose proof (IH2 eq_refl) as TAIL.
    eapply ENFA_reachable_app; eauto.
Qed.

Theorem compile_complete_similar (e : regex ascii) (s : list ascii)
  (IN : s =~= e)
  : fragment_accepts (compile e) s.
Proof.
  revert s IN. induction e as [ | | c | e1 COMPLETE1 e2 COMPLETE2 | e1 COMPLETE1 e2 COMPLETE2 | e COMPLETE]; intros s IN; inv IN; unfold fragment_accepts in *; simpl in *.
  - eapply ENFA.reachable_eps with (q2 := 1); simpl; eauto with *.
  - red in c_corres. subst c0. eapply ENFA.reachable_char with (q2 := 1); simpl; eauto with *.
    destruct (Ascii.ascii_dec c c) as [_ | NE]; [left; reflexivity | contradiction].
  - match goal with [ H : s =~= e1 |- _ ] => pose proof (COMPLETE1 s H) as IH end.
    pose proof (offset_fragment_accepts 1 (compile e1) s IH) as BODY_OFF.
    assert (BODY_BIG : ENFA.reachable (of_fragment (compile (Re.Union e1 e2))) (1 + frag_start (compile e1)) s (1 + frag_accept (compile e1))).
    { eapply fragment_reachable_incl with (f := offset_fragment 1 (compile e1)) (g := compile (Re.Union e1 e2)).
      - intros edge EDGE. simpl in *. right. right. right. right. rewrite in_app_iff. left. exact EDGE.
      - intros edge EDGE. simpl in *. rewrite in_app_iff. left. exact EDGE.
      - exact BODY_OFF.
    }
    assert (HEAD : ENFA.reachable (of_fragment (compile (Re.Union e1 e2))) 0 s (1 + frag_accept (compile e1))).
    { eapply ENFA.reachable_eps with (q2 := 1 + frag_start (compile e1)); simpl; eauto with *. }
    assert (TAIL : ENFA.reachable (of_fragment (compile (Re.Union e1 e2))) (1 + frag_accept (compile e1)) [] (1 + frag_size (compile e1) + frag_size (compile e2))).
    { eapply ENFA.reachable_eps with (q2 := 1 + frag_size (compile e1) + frag_size (compile e2)).
      - change (L.In (1 + frag_size (compile e1) + frag_size (compile e2)) (eps_step_of (frag_eps_edges (compile (Re.Union e1 e2))) (1 + frag_accept (compile e1)))).
        rewrite eps_step_of_spec. simpl. right. right. left. reflexivity.
      - eauto with *.
    }
    pose proof (ENFA_reachable_app (of_fragment (compile (Re.Union e1 e2))) 0 (1 + frag_accept (compile e1)) (1 + frag_size (compile e1) + frag_size (compile e2)) s [] HEAD TAIL) as REACH.
    rewrite app_nil_r in REACH. exact REACH.
  - match goal with [ H : s =~= e2 |- _ ] => pose proof (COMPLETE2 s H) as IH end.
    pose proof (offset_fragment_accepts (1 + frag_size (compile e1)) (compile e2) s IH) as BODY_OFF.
    assert (BODY_BIG : ENFA.reachable (of_fragment (compile (Re.Union e1 e2))) (1 + frag_size (compile e1) + frag_start (compile e2)) s (1 + frag_size (compile e1) + frag_accept (compile e2))).
    { eapply fragment_reachable_incl with (f := offset_fragment (1 + frag_size (compile e1)) (compile e2)) (g := compile (Re.Union e1 e2)).
      - intros edge EDGE. simpl in *. right. right. right. right. rewrite in_app_iff. right. exact EDGE.
      - intros edge EDGE. simpl in *. rewrite in_app_iff. right. exact EDGE.
      - exact BODY_OFF.
    }
    assert (HEAD : ENFA.reachable (of_fragment (compile (Re.Union e1 e2))) 0 s (1 + frag_size (compile e1) + frag_accept (compile e2))).
    { eapply ENFA.reachable_eps with (q2 := 1 + frag_size (compile e1) + frag_start (compile e2)).
      - change (L.In (1 + frag_size (compile e1) + frag_start (compile e2)) (eps_step_of (frag_eps_edges (compile (Re.Union e1 e2))) 0)).
        rewrite eps_step_of_spec. simpl. right. left. reflexivity.
      - exact BODY_BIG.
    }
    assert (TAIL : ENFA.reachable (of_fragment (compile (Re.Union e1 e2))) (1 + frag_size (compile e1) + frag_accept (compile e2)) [] (1 + frag_size (compile e1) + frag_size (compile e2))).
    { eapply ENFA.reachable_eps with (q2 := 1 + frag_size (compile e1) + frag_size (compile e2)).
      - change (L.In (1 + frag_size (compile e1) + frag_size (compile e2)) (eps_step_of (frag_eps_edges (compile (Re.Union e1 e2))) (1 + frag_size (compile e1) + frag_accept (compile e2)))).
        rewrite eps_step_of_spec. simpl. right. right. right. left. reflexivity.
      - eauto with *.
    }
    pose proof (ENFA_reachable_app (of_fragment (compile (Re.Union e1 e2))) 0 (1 + frag_size (compile e1) + frag_accept (compile e2)) (1 + frag_size (compile e1) + frag_size (compile e2)) s [] HEAD TAIL) as REACH.
    rewrite app_nil_r in REACH. exact REACH.
  - match goal with [ H : s1 =~= e1 |- _ ] => pose proof (COMPLETE1 s1 H) as IH1 end.
    match goal with [ H : s2 =~= e2 |- _ ] => pose proof (COMPLETE2 s2 H) as IH2 end.
    assert (BODY1_BIG : ENFA.reachable (of_fragment (compile (Re.Append e1 e2))) (frag_start (compile e1)) s1 (frag_accept (compile e1))).
    { eapply fragment_reachable_incl with (f := compile e1) (g := compile (Re.Append e1 e2)).
      - intros edge EDGE. simpl in *. rewrite in_app_iff. left. exact EDGE.
      - intros edge EDGE. simpl in *. rewrite in_app_iff. left. exact EDGE.
      - exact IH1.
    }
    pose proof (offset_fragment_accepts (frag_size (compile e1)) (compile e2) s2 IH2) as BODY2_OFF.
    assert (BODY2_BIG : ENFA.reachable (of_fragment (compile (Re.Append e1 e2))) (frag_size (compile e1) + frag_start (compile e2)) s2 (frag_size (compile e1) + frag_accept (compile e2))).
    { eapply fragment_reachable_incl with (f := offset_fragment (frag_size (compile e1)) (compile e2)) (g := compile (Re.Append e1 e2)).
      - intros edge EDGE. simpl in *. rewrite in_app_iff. right. right. exact EDGE.
      - intros edge EDGE. simpl in *. rewrite in_app_iff. right. exact EDGE.
      - exact BODY2_OFF.
    }
    assert (BRIDGE : ENFA.reachable (of_fragment (compile (Re.Append e1 e2))) (frag_accept (compile e1)) [] (frag_size (compile e1) + frag_start (compile e2))).
    { eapply ENFA.reachable_eps with (q2 := frag_size (compile e1) + frag_start (compile e2)).
      - change (L.In (frag_size (compile e1) + frag_start (compile e2)) (eps_step_of (frag_eps_edges (compile (Re.Append e1 e2))) (frag_accept (compile e1)))).
        rewrite eps_step_of_spec. simpl. rewrite in_app_iff. right. left. reflexivity.
      - eauto with *.
    }
    pose proof (ENFA_reachable_app (of_fragment (compile (Re.Append e1 e2))) (frag_start (compile e1)) (frag_accept (compile e1)) (frag_size (compile e1) + frag_start (compile e2)) s1 [] BODY1_BIG BRIDGE) as LEFT.
    rewrite app_nil_r in LEFT.
    eapply ENFA_reachable_app; eauto.
  - eapply ENFA.reachable_eps with (q2 := 1 + frag_size (compile e)).
    + change (L.In (1 + frag_size (compile e)) (eps_step_of (frag_eps_edges (compile (Re.Star e))) 0)).
      rewrite eps_step_of_spec. simpl. left. reflexivity.
    + eauto with *.
  - match goal with [ H : s1 =~= e |- _ ] => pose proof (COMPLETE s1 H) as IH1 end.
    match goal with [ H : s2 =~= Re.Star e |- _ ] => pose proof (compile_star_tail_complete_similar e s2 COMPLETE H) as TAIL end.
    pose proof (offset_fragment_accepts 1 (compile e) s1 IH1) as BODY_OFF.
    assert (BODY_BIG : ENFA.reachable (of_fragment (compile (Re.Star e))) (1 + frag_start (compile e)) s1 (1 + frag_accept (compile e))).
    { eapply fragment_reachable_incl with (f := offset_fragment 1 (compile e)) (g := compile (Re.Star e)).
      - intros edge EDGE. simpl in *. right. right. right. right. exact EDGE.
      - intros edge EDGE. simpl in *. exact EDGE.
      - exact BODY_OFF.
    }
    assert (HEAD : ENFA.reachable (of_fragment (compile (Re.Star e))) 0 s1 (1 + frag_accept (compile e))).
    { eapply ENFA.reachable_eps with (q2 := 1 + frag_start (compile e)).
      - change (L.In (1 + frag_start (compile e)) (eps_step_of (frag_eps_edges (compile (Re.Star e))) 0)).
        rewrite eps_step_of_spec. simpl. right. left. reflexivity.
      - exact BODY_BIG.
    }
    eapply ENFA_reachable_app; eauto.
Qed.

Theorem compile_sound_similar (e : regex ascii) (s : list ascii)
  (ACCEPTS : fragment_accepts (compile e) s)
  : s =~= e.
Proof.
  revert s ACCEPTS. induction e as [ | | c | e1 SOUND1 e2 SOUND2 | e1 SOUND1 e2 SOUND2 | e SOUND]; intros s ACCEPTS.
  - eapply compile_null_sound_similar; eauto.
  - eapply compile_empty_sound_similar; eauto.
  - eapply compile_char_sound_similar; eauto.
  - eapply compile_union_sound_similar; eauto.
  - eapply compile_append_sound_similar; eauto.
  - eapply compile_star_sound_similar; eauto.
Qed.

Theorem compile_sound (e : regex ascii) (s : list ascii)
  (ACCEPTS : fragment_accepts (compile e) s)
  : s \in eval_regex e.
Proof.
  rewrite eval_regex_good. eapply compile_sound_similar; eauto.
Qed.

Theorem compile_complete (e : regex ascii) (s : list ascii)
  (IN : s \in eval_regex e)
  : fragment_accepts (compile e) s.
Proof.
  rewrite eval_regex_good in IN. eapply compile_complete_similar; eauto.
Qed.

Theorem to_enfa_complete (e : regex ascii) (s : list ascii)
  (IN : s \in eval_regex e)
  : ENFA.accepts (to_enfa e) s.
Proof.
  unfold to_enfa, ENFA.accepts. exists (frag_accept (compile e)). split.
  - eapply compile_complete; eauto.
  - simpl. left. reflexivity.
Qed.

Theorem to_enfa_sound (e : regex ascii) (s : list ascii)
  (ACCEPTS : ENFA.accepts (to_enfa e) s)
  : s \in eval_regex e.
Proof.
  unfold to_enfa, ENFA.accepts in ACCEPTS. destruct ACCEPTS as (q & REACH & ACCEPT).
  simpl in ACCEPT. destruct ACCEPT as [EQ | []]. subst q.
  eapply compile_sound; eauto.
Qed.

End Thompson.

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
  (M.(state) * Token.t)%type.

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

Inductive eclosure (q : Q) : ensemble Q :=
  | eclosure_refl
    : q \in eclosure q
  | eclosure_step q1 q2
    (STEP : q1 ∈ M.(eps_step) q)
    (REST : q2 \in eclosure q1)
    : q2 \in eclosure q.

Definition accepts (s : Input.t) (tag : Token.t) : Prop :=
  exists q, q \in delta_star M.(start_state) s /\ (q, tag) ∈ M.(accept_states).

Definition accepted_tags (s : Input.t) : ensemble Token.t :=
  fun tag => accepts s tag.

#[local] Hint Constructors delta_star : core.
#[local] Hint Constructors eclosure : core.

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

#[projections(primitive)]
Record raw_rule : Set :=
  mkRawRule
  { raw_rule_index : nat
  ; raw_rule_token : Token.t
  ; raw_rule_regex : regex ascii
  }.

#[projections(primitive)]
Record compiled_rule : Set :=
  mkCompiledRule
  { compiled_rule_index : nat
  ; compiled_rule_token : Token.t
  ; compiled_rule_regex : regex ascii
  }.

Definition raw_rules : list raw_rule :=
  L.mapi_from 0 (fun idx => fun rule => mkRawRule idx (fst rule) (snd rule)) Token.rules.

Definition compile_rule (r : raw_rule) : ErrM compiled_rule :=
  if nullable r.(raw_rule_regex) then
    inl (Error.EmptyTokenRule r.(raw_rule_index))
  else
    inr (mkCompiledRule r.(raw_rule_index) r.(raw_rule_token) r.(raw_rule_regex)).

Fixpoint compile_rules_loop (rs : list raw_rule) {struct rs}
  : ErrM (list compiled_rule) :=
  match rs with
  | [] => inr []
  | r :: rs' =>
    match compile_rule r, compile_rules_loop rs' with
    | inr cr, inr crs => inr (cr :: crs)
    | inl err, _ => inl err
    | _, inl err => inl err
    end
  end.

Definition compile_rules : ErrM (list compiled_rule) :=
  compile_rules_loop raw_rules.

Definition compiled_rules_wf (crs : list compiled_rule) : Prop :=
  forall cr, cr ∈ crs -> (exists r, r ∈ raw_rules /\ compile_rule r = inr cr).

Definition raw_rule_accepts (r : raw_rule) (s : list ascii) : Prop :=
  s \in eval_regex r.(raw_rule_regex).

Definition compiled_rule_accepts (r : compiled_rule) (s : list ascii) : Prop :=
  s \in eval_regex r.(compiled_rule_regex).

Theorem compile_rule_sound (r : raw_rule) (cr : compiled_rule) (s : list ascii)
  (COMPILE : compile_rule r = inr cr)
  (ACCEPTS : compiled_rule_accepts cr s)
  : raw_rule_accepts r s.
Proof.
  unfold compile_rule in COMPILE.
  destruct (nullable r.(raw_rule_regex)) eqn: NULLABLE; inv COMPILE.
  exact ACCEPTS.
Qed.

Theorem compile_rule_complete (r : raw_rule) (cr : compiled_rule) (s : list ascii)
  (COMPILE : compile_rule r = inr cr)
  (ACCEPTS : raw_rule_accepts r s)
  : compiled_rule_accepts cr s.
Proof.
  unfold compile_rule in COMPILE.
  destruct (nullable r.(raw_rule_regex)) eqn: NULLABLE; inv COMPILE.
  exact ACCEPTS.
Qed.

Theorem compile_rule_nonempty (r : raw_rule) (cr : compiled_rule)
  (COMPILE : compile_rule r = inr cr)
  : ~ compiled_rule_accepts cr [].
Proof.
  unfold compile_rule in COMPILE.
  destruct (nullable r.(raw_rule_regex)) eqn: NULLABLE; inv COMPILE.
  unfold compiled_rule_accepts. simpl.
  rewrite <- nullable_false_spec. exact NULLABLE.
Qed.

Lemma compile_rule_not_no_match (r : raw_rule) (rest : Input.t)
  : compile_rule r <> inl (Error.NoMatch rest).
Proof.
  unfold compile_rule. destruct (nullable r.(raw_rule_regex)); discriminate.
Qed.

Lemma compile_rules_loop_not_no_match (rs : list raw_rule) (rest : Input.t)
  : compile_rules_loop rs <> inl (Error.NoMatch rest).
Proof.
  revert rest. induction rs as [ | r rs IH]; intros rest; simpl.
  - discriminate.
  - destruct (compile_rule r) as [err | cr] eqn: COMPILE1.
    + destruct err; try discriminate.
      exfalso. eapply compile_rule_not_no_match. exact COMPILE1.
    + pose (rec := compile_rules_loop rs).
      fold rec.
      destruct rec as [err | crs] eqn: REC.
      * destruct err; try discriminate.
        exfalso. eapply (IH rest0). unfold rec in REC. exact REC.
      * discriminate.
Qed.

Theorem compile_rules_not_no_match (rest : Input.t)
  : compile_rules <> inl (Error.NoMatch rest).
Proof.
  unfold compile_rules. eapply compile_rules_loop_not_no_match.
Qed.

Lemma compile_rules_loop_sound (rs : list raw_rule) (crs : list compiled_rule)
  (COMPILE : compile_rules_loop rs = inr crs)
  : forall cr, cr ∈ crs -> exists r, r ∈ rs /\ compile_rule r = inr cr.
Proof.
  revert crs COMPILE.
  induction rs as [ | r rs IH]; intros crs COMPILE cr IN; simpl in COMPILE.
  - inv COMPILE. contradiction.
  - destruct (compile_rule r) as [err | cr'] eqn: COMPILE1; try congruence.
    destruct (compile_rules_loop rs) as [err | crs'] eqn: COMPILE2; try congruence.
    inv COMPILE. destruct IN as [EQ | IN].
    + subst cr. exists r. split; [left; reflexivity | exact COMPILE1].
    + pose proof (IH crs' eq_refl cr IN) as (r' & IN' & COMPILE').
      exists r'. split; [right; exact IN' | exact COMPILE'].
Qed.

Theorem compile_rules_sound (crs : list compiled_rule)
  (COMPILE : compile_rules = inr crs)
  : compiled_rules_wf crs.
Proof.
  unfold compiled_rules_wf. unfold compile_rules in COMPILE.
  eapply compile_rules_loop_sound; eauto.
Qed.

Definition tagged_state : Set :=
  option (nat * nat).

#[global]
Instance tagged_state_hasEqDec
  : hasEqDec@{Set} tagged_state.
Proof.
  unfold tagged_state. red. decide equality. decide equality; eapply eq_dec.
Defined.

Definition compiled_rule_fragment (cr : compiled_rule) : Thompson.fragment :=
  Thompson.compile cr.(compiled_rule_regex).

Definition compiled_rule_table (crs : list compiled_rule) : list (nat * compiled_rule) :=
  L.mapi_from 0 (fun key => fun cr => (key, cr)) crs.

Definition lookup_compiled_rule (crs : list compiled_rule) (key : nat)
  : option compiled_rule :=
  nth_error crs key.

Definition compiled_rule_start_state (entry : nat * compiled_rule) : tagged_state :=
  let key := fst entry in
  let cr := snd entry in
  Some (key, (compiled_rule_fragment cr).(Thompson.frag_start)).

Definition compiled_rule_accept_state (entry : nat * compiled_rule)
  : tagged_state :=
  let key := fst entry in
  let cr := snd entry in
  Some (key, (compiled_rule_fragment cr).(Thompson.frag_accept)).

Definition compiled_rule_states (entry : nat * compiled_rule) : list tagged_state :=
  let key := fst entry in
  let cr := snd entry in
  map (fun q => Some (key, q)) (seq 0 (compiled_rule_fragment cr).(Thompson.frag_size)).

Definition tagged_states (crs : list compiled_rule) : list tagged_state :=
  None :: flat_map compiled_rule_states (compiled_rule_table crs).

Definition tagged_accept_states (crs : list compiled_rule) : list (tagged_state * Token.t) :=
  map (fun entry => (compiled_rule_accept_state entry, (snd entry).(compiled_rule_token))) (compiled_rule_table crs).

Definition tagged_eps_step (crs : list compiled_rule) (q : tagged_state) : list tagged_state :=
  match q with
  | None => map compiled_rule_start_state (compiled_rule_table crs)
  | Some (key, q0) =>
    match lookup_compiled_rule crs key with
    | None => []
    | Some cr => map (fun q1 => Some (key, q1)) (Thompson.eps_step_of (compiled_rule_fragment cr).(Thompson.frag_eps_edges) q0)
    end
  end.

Definition tagged_char_step (crs : list compiled_rule) (q : tagged_state) (a : ascii) : list tagged_state :=
  match q with
  | None => []
  | Some (key, q0) =>
    match lookup_compiled_rule crs key with
    | None => []
    | Some cr => map (fun q1 => Some (key, q1)) (Thompson.char_step_of (compiled_rule_fragment cr).(Thompson.frag_char_edges) q0 a)
    end
  end.

Definition build_tagged_enfa (crs : list compiled_rule) : TaggedENFA.t :=
  TaggedENFA.mk tagged_state tagged_state_hasEqDec (tagged_states crs) None (tagged_accept_states crs) (tagged_eps_step crs) (tagged_char_step crs).

Lemma lookup_compiled_rule_in (crs : list compiled_rule) (key : nat) (cr : compiled_rule)
  (LOOKUP : lookup_compiled_rule crs key = Some cr)
  : cr ∈ crs.
Proof.
  unfold lookup_compiled_rule in LOOKUP. eapply nth_error_In. exact LOOKUP.
Qed.

Lemma compiled_rule_table_lookup_in_from (base : nat) (crs : list compiled_rule) (key : nat) (cr : compiled_rule)
  (LOOKUP : nth_error crs key = Some cr)
  : (base + key, cr) ∈ L.mapi_from base (fun key => fun cr => (key, cr)) crs.
Proof.
  revert base key LOOKUP.
  induction crs as [ | cr0 crs IH]; intros base key LOOKUP.
  - destruct key; simpl in LOOKUP; congruence.
  - destruct key as [ | key]; simpl in LOOKUP.
    + inv LOOKUP. left. rewrite Nat.add_0_r. reflexivity.
    + right. replace (base + S key) with (S base + key) by lia.
      eapply IH. exact LOOKUP.
Qed.

Lemma compiled_rule_table_lookup_in (crs : list compiled_rule) (key : nat) (cr : compiled_rule)
  (LOOKUP : lookup_compiled_rule crs key = Some cr)
  : (key, cr) ∈ compiled_rule_table crs.
Proof.
  unfold lookup_compiled_rule in LOOKUP. unfold compiled_rule_table.
  replace key with (0 + key) by lia.
  eapply compiled_rule_table_lookup_in_from. exact LOOKUP.
Qed.

Lemma compiled_rule_table_in_lookup_from (base : nat) (crs : list compiled_rule) (key : nat) (cr : compiled_rule)
  (IN : (key, cr) ∈ L.mapi_from base (fun key => fun cr => (key, cr)) crs)
  : exists n, key = base + n /\ nth_error crs n = Some cr.
Proof.
  revert base key cr IN.
  induction crs as [ | cr0 crs IH]; intros base key cr IN; simpl in IN.
  - contradiction.
  - destruct IN as [EQ | IN].
    + inv EQ. exists 0. split; simpl; [lia | reflexivity].
    + pose proof (IH (S base) key cr IN) as (n & KEY & LOOKUP).
      exists (S n). split; simpl; [lia | exact LOOKUP].
Qed.

Lemma compiled_rule_table_in_lookup (crs : list compiled_rule) (key : nat) (cr : compiled_rule)
  (IN : (key, cr) ∈ compiled_rule_table crs)
  : lookup_compiled_rule crs key = Some cr.
Proof.
  unfold compiled_rule_table in IN. unfold lookup_compiled_rule.
  pose proof (compiled_rule_table_in_lookup_from 0 crs key cr IN) as (n & KEY & LOOKUP).
  replace key with n by lia. exact LOOKUP.
Qed.

Lemma compiled_rule_state_in (crs : list compiled_rule) (key : nat) (cr : compiled_rule) (q : nat)
  (IN : (key, cr) ∈ compiled_rule_table crs)
  (BOUND : q < (compiled_rule_fragment cr).(Thompson.frag_size))
  : Some (key, q) ∈ tagged_states crs.
Proof.
  unfold tagged_states. simpl. right. rewrite in_flat_map.
  exists (key, cr). split; [exact IN | ].
  unfold compiled_rule_states. simpl. rewrite in_map_iff.
  exists q. split; [reflexivity | ].
  rewrite L.in_seq. split; lia.
Qed.

Lemma compiled_rule_start_state_in (crs : list compiled_rule) (entry : nat * compiled_rule)
  (IN : entry ∈ compiled_rule_table crs)
  : compiled_rule_start_state entry ∈ tagged_states crs.
Proof.
  destruct entry as [key cr]. unfold compiled_rule_start_state.
  eapply compiled_rule_state_in; eauto.
  unfold compiled_rule_fragment. eapply Thompson.compile_start_lt_size.
Qed.

Lemma compiled_rule_accept_state_in (crs : list compiled_rule) (entry : nat * compiled_rule)
  (IN : entry ∈ compiled_rule_table crs)
  : compiled_rule_accept_state entry ∈ tagged_states crs.
Proof.
  destruct entry as [key cr]. unfold compiled_rule_accept_state.
  eapply compiled_rule_state_in; eauto.
  unfold compiled_rule_fragment. eapply Thompson.compile_accept_lt_size.
Qed.

Theorem build_tagged_enfa_okay (crs : list compiled_rule)
  : TaggedENFA.okay (build_tagged_enfa crs).
Proof.
  unfold build_tagged_enfa. econstructor.
  - simpl. left. reflexivity.
  - change (forall q, forall tag,
      (q, tag) ∈ tagged_accept_states crs -> q ∈ tagged_states crs).
    intros q tag IN. unfold tagged_accept_states in IN. rewrite in_map_iff in IN.
    destruct IN as (entry & EQ & IN). inv EQ.
    eapply compiled_rule_accept_state_in. exact IN.
  - change (forall q, forall q', q ∈ tagged_states crs -> q' ∈ tagged_eps_step crs q -> q' ∈ tagged_states crs).
    intros q q' IN_STATE STEP. destruct q as [[idx q0] | ].
    + unfold tagged_eps_step in STEP.
      destruct (lookup_compiled_rule crs idx) as [cr | ] eqn: LOOKUP; [ | contradiction].
      rewrite in_map_iff in STEP. destruct STEP as (q1 & EQ & STEP). inv EQ.
      eapply compiled_rule_state_in.
      * eapply compiled_rule_table_lookup_in. exact LOOKUP.
      * unfold compiled_rule_fragment.
        pose proof (Thompson.compile_edges_in_bounds (compiled_rule_regex cr)) as (EPS & _).
        eapply Thompson.eps_step_of_bound; eauto.
    + unfold tagged_eps_step in STEP. rewrite in_map_iff in STEP.
      destruct STEP as (entry & EQ & IN). subst q'.
      eapply compiled_rule_start_state_in. exact IN.
  - change (forall q, forall q', forall a, q ∈ tagged_states crs -> q' ∈ tagged_char_step crs q a -> q' ∈ tagged_states crs).
    intros q q' a IN_STATE STEP. destruct q as [[idx q0] | ].
    + unfold tagged_char_step in STEP.
      destruct (lookup_compiled_rule crs idx) as [cr | ] eqn: LOOKUP; [ | contradiction].
      rewrite in_map_iff in STEP. destruct STEP as (q1 & EQ & STEP). inv EQ.
      eapply compiled_rule_state_in.
      * eapply compiled_rule_table_lookup_in. exact LOOKUP.
      * unfold compiled_rule_fragment.
        pose proof (Thompson.compile_edges_in_bounds (compiled_rule_regex cr)) as (_ & CHAR).
        eapply Thompson.char_step_of_bound; eauto.
    + unfold tagged_char_step in STEP. contradiction.
Qed.

Lemma tagged_inside_delta_complete (crs : list compiled_rule) (key : nat) (cr : compiled_rule) (q0 : nat) (q : nat) (s : list ascii)
  (LOOKUP : lookup_compiled_rule crs key = Some cr)
  (REACH : ENFA.reachable (Thompson.of_fragment (compiled_rule_fragment cr)) q0 s q)
  : Some (key, q) \in TaggedENFA.delta_star (build_tagged_enfa crs) (Some (key, q0)) s.
Proof.
  induction REACH as [q | q1 q2 q3 s STEP REST IH | q1 q2 q3 a s STEP REST IH].
  - eapply TaggedENFA.delta_star_nil.
  - eapply TaggedENFA.delta_star_eps with (q1 := Some (key, q2)); eauto.
    simpl. unfold tagged_eps_step. rewrite LOOKUP. rewrite in_map_iff.
    exists q2. split; [reflexivity | exact STEP].
  - eapply TaggedENFA.delta_star_char with (q1 := Some (key, q2)); eauto.
    simpl. unfold tagged_char_step. rewrite LOOKUP. rewrite in_map_iff.
    exists q2. split; [reflexivity | exact STEP].
Qed.

Lemma tagged_inside_delta_sound (crs : list compiled_rule) (key : nat) (cr : compiled_rule) (q0 : nat) (qT : tagged_state) (s : list ascii)
  (LOOKUP : lookup_compiled_rule crs key = Some cr)
  (REACH : qT \in TaggedENFA.delta_star (build_tagged_enfa crs) (Some (key, q0)) s)
  : exists q, qT = Some (key, q) /\ ENFA.reachable (Thompson.of_fragment (compiled_rule_fragment cr)) q0 s q.
Proof.
  remember (Some (key, q0)) as src eqn: SRC.
  revert key cr q0 LOOKUP SRC.
  induction REACH as [q | q1 q2 q3 s STEP REST IH | q1 q2 q3 a s STEP REST IH]; intros key cr q0 LOOKUP SRC; subst.
  - exists q0. splits; eauto with *.
  - simpl in STEP. unfold tagged_eps_step in STEP. rewrite LOOKUP in STEP.
    rewrite in_map_iff in STEP. destruct STEP as (q2' & EQ & STEP). inv EQ.
    pose proof (IH key cr q2' LOOKUP eq_refl) as (q & TARGET & REST').
    subst q3. exists q. split; [reflexivity | ].
    eapply ENFA.reachable_eps with (q2 := q2'); eauto.
  - simpl in STEP. unfold tagged_char_step in STEP. rewrite LOOKUP in STEP.
    rewrite in_map_iff in STEP. destruct STEP as (q2' & EQ & STEP). inv EQ.
    pose proof (IH key cr q2' LOOKUP eq_refl) as (q & TARGET & REST').
    subst q3. exists q. split; [reflexivity | ].
    eapply ENFA.reachable_char with (q2 := q2'); eauto.
Qed.

Lemma tagged_start_delta_sound (crs : list compiled_rule) (qT : tagged_state) (s : list ascii)
  (REACH : qT \in TaggedENFA.delta_star (build_tagged_enfa crs) None s)
  : (qT = None /\ s = []) \/ (exists key, exists cr, exists q, lookup_compiled_rule crs key = Some cr /\ qT = Some (key, q) /\ ENFA.reachable (Thompson.of_fragment (compiled_rule_fragment cr)) (Thompson.frag_start (compiled_rule_fragment cr)) s q).
Proof.
  inv REACH.
  - left. split; reflexivity.
  - right. simpl in STEP. unfold tagged_eps_step in STEP. rewrite in_map_iff in STEP.
    destruct STEP as (entry & EQ & IN). destruct entry as [key cr]. simpl in EQ. inv EQ.
    pose proof (compiled_rule_table_in_lookup crs key cr IN) as LOOKUP.
    pose proof (tagged_inside_delta_sound crs key cr (Thompson.frag_start (compiled_rule_fragment cr)) qT s LOOKUP REST) as (q & TARGET & BODY).
    exists key. exists cr. exists q. splits; eauto.
  - simpl in STEP. unfold tagged_char_step in STEP. contradiction.
Qed.

Theorem build_tagged_enfa_complete (crs : list compiled_rule) (key : nat) (cr : compiled_rule) (s : list ascii)
  (LOOKUP : lookup_compiled_rule crs key = Some cr)
  (ACCEPTS : compiled_rule_accepts cr s)
  : TaggedENFA.accepts (build_tagged_enfa crs) s cr.(compiled_rule_token).
Proof.
  unfold compiled_rule_accepts in ACCEPTS.
  pose proof (Thompson.compile_complete cr.(compiled_rule_regex) s ACCEPTS) as REACH.
  unfold TaggedENFA.accepts.
  exists (Some (key, (compiled_rule_fragment cr).(Thompson.frag_accept))).
  split.
  - simpl. eapply TaggedENFA.delta_star_eps with (q1 := Some (key, (compiled_rule_fragment cr).(Thompson.frag_start))).
    + simpl. unfold tagged_eps_step. rewrite in_map_iff.
      exists (key, cr). split; [reflexivity | ].
      eapply compiled_rule_table_lookup_in. exact LOOKUP.
    + eapply tagged_inside_delta_complete; eauto.
  - simpl. unfold tagged_accept_states. rewrite in_map_iff.
    exists (key, cr). split.
    + simpl. reflexivity.
    + eapply compiled_rule_table_lookup_in. exact LOOKUP.
Qed.

Theorem build_tagged_enfa_sound (crs : list compiled_rule) (tag : Token.t) (s : list ascii)
  (ACCEPTS : TaggedENFA.accepts (build_tagged_enfa crs) s tag)
  : exists key, exists cr, lookup_compiled_rule crs key = Some cr /\ tag = cr.(compiled_rule_token) /\ compiled_rule_accepts cr s.
Proof.
  unfold TaggedENFA.accepts in ACCEPTS. destruct ACCEPTS as (q & REACH & ACCEPT).
  pose proof (tagged_start_delta_sound crs q s REACH) as [(Q_NONE & S_NIL) | (key & cr & q0 & LOOKUP & TARGET & BODY)].
  - subst q. simpl in ACCEPT. unfold tagged_accept_states in ACCEPT.
    rewrite in_map_iff in ACCEPT. destruct ACCEPT as ([key cr] & EQ & _).
    inv EQ.
  - subst q. simpl in ACCEPT. unfold tagged_accept_states in ACCEPT.
    rewrite in_map_iff in ACCEPT.
    destruct ACCEPT as ([key' cr'] & EQ & IN).
    inv EQ.
    pose proof (compiled_rule_table_in_lookup crs key cr' IN) as LOOKUP'.
    assert (CR_EQ : cr' = cr) by congruence. subst cr'.
    exists key. exists cr. splits; [exact LOOKUP | reflexivity | ].
    unfold compiled_rule_accepts. eapply Thompson.compile_sound.
    unfold Thompson.fragment_accepts.
    change (ENFA.reachable (Thompson.of_fragment (compiled_rule_fragment cr))(Thompson.frag_start (compiled_rule_fragment cr)) s (Thompson.frag_accept (compiled_rule_fragment cr))).
    exact BODY.
Qed.

Corollary build_tagged_enfa_accepts_iff (crs : list compiled_rule) (tag : Token.t) (s : list ascii)
  : TaggedENFA.accepts (build_tagged_enfa crs) s tag <-> (exists key, exists cr, lookup_compiled_rule crs key = Some cr /\ tag = cr.(compiled_rule_token) /\ compiled_rule_accepts cr s).
Proof.
  split; intros ACCEPTS.
  - eapply build_tagged_enfa_sound. exact ACCEPTS.
  - destruct ACCEPTS as (key & cr & LOOKUP & TAG & RULE_ACCEPTS).
    subst tag. eapply build_tagged_enfa_complete; eauto.
Qed.

Module Subset.

Definition dstate (M : ENFA.t) : Set :=
  list M.(ENFA.state).

Definition subset_of_states (M : ENFA.t) (qs : list M.(ENFA.state)) : Prop :=
  forall q, q ∈ qs -> q ∈ M.(ENFA.states).

Definition state_mem (M : ENFA.t) : M.(ENFA.state) -> list M.(ENFA.state) -> bool :=
  mem (EQ_DEC := M.(ENFA.state_hasEqDec)).

Lemma state_mem_true_iff (M : ENFA.t) (q : M.(ENFA.state)) (qs : list M.(ENFA.state))
  : state_mem M q qs = true <-> q ∈ qs.
Proof.
  unfold state_mem. eapply mem_true_iff.
Qed.

Lemma state_mem_false_iff (M : ENFA.t) (q : M.(ENFA.state)) (qs : list M.(ENFA.state))
  : state_mem M q qs = false <-> ~ q ∈ qs.
Proof.
  unfold state_mem. eapply mem_false_iff.
Qed.

Definition close_state (M : ENFA.t) : Type :=
  ((list M.(ENFA.state) * list M.(ENFA.state)) * list M.(ENFA.state))%type.

Definition close_unseen {M : ENFA.t} (st : close_state M) : list M.(ENFA.state) :=
  fst (fst st).

Definition close_pending {M : ENFA.t} (st : close_state M) : list M.(ENFA.state) :=
  snd (fst st).

Definition close_seen {M : ENFA.t} (st : close_state M) : list M.(ENFA.state) :=
  snd st.

Definition close_measure {M : ENFA.t} (st : close_state M) : { n : nat & nat } :=
  @existT nat (fun _ => nat) (length (close_unseen st)) (length (close_pending st)).

Definition close_lt (M : ENFA.t) : close_state M -> close_state M -> Prop :=
  fun st1 => fun st2 => B.lexprod nat (fun _ => nat) lt (fun _ => lt) (close_measure st1) (close_measure st2).

Lemma close_lt_wf (M : ENFA.t)
  : well_founded (close_lt M).
Proof.
  unfold close_lt.
  eapply B.wf_inverse_image.
  eapply B.wf_lexprod.
  - exact lt_wf.
  - intros _. exact lt_wf.
Qed.

Lemma close_lt_skip (M : ENFA.t) (unseen : list M.(ENFA.state)) (pending : list M.(ENFA.state)) (seen : list M.(ENFA.state)) (q : M.(ENFA.state))
  : close_lt M ((unseen, pending), seen) ((unseen, q :: pending), seen).
Proof.
  unfold close_lt, close_measure, close_unseen, close_pending. simpl.
  right. exists eq_refl. simpl. lia.
Qed.

Lemma close_lt_process (M : ENFA.t) (unseen : list M.(ENFA.state)) (pending : list M.(ENFA.state)) (seen : list M.(ENFA.state)) (q : M.(ENFA.state))
  (IN_UNSEEN : q ∈ unseen)
  : close_lt M ((remove eq_dec q unseen, M.(ENFA.eps_step) q ++ pending), q :: seen) ((unseen, q :: pending), seen).
Proof.
  unfold close_lt, close_measure, close_unseen, close_pending. simpl.
  left. eapply remove_length_lt. exact IN_UNSEEN.
Qed.

Fixpoint eclose_work_acc (M : ENFA.t) (st : close_state M) (ACC : Acc (close_lt M) st) {struct ACC} : list M.(ENFA.state) :=
  match st as st0 return Acc (close_lt M) st0 -> list M.(ENFA.state) with
  | ((unseen, []), seen) => fun _ => seen
  | ((unseen, q :: pending), seen) => fun ACC =>
    if state_mem M q seen then
      let st' := ((unseen, pending), seen) in
      eclose_work_acc M st' (Acc_inv ACC (close_lt_skip M unseen pending seen q))
    else
      match in_dec eq_dec q unseen with
      | left IN_UNSEEN =>
        let st' := ((remove eq_dec q unseen, M.(ENFA.eps_step) q ++ pending), q :: seen) in
        eclose_work_acc M st' (Acc_inv ACC (close_lt_process M unseen pending seen q IN_UNSEEN))
      | right _ =>
        let st' := ((unseen, pending), seen) in
        eclose_work_acc M st' (Acc_inv ACC (close_lt_skip M unseen pending seen q))
      end
  end ACC.

Definition eclose (M : ENFA.t) (qs : list M.(ENFA.state)) : list M.(ENFA.state) :=
  let st := ((M.(ENFA.states), qs), []) in
  eclose_work_acc M st (close_lt_wf M st).

Definition origins (M : ENFA.t) (seeds : list M.(ENFA.state)) (xs : list M.(ENFA.state)) : Prop :=
  forall q, q ∈ xs -> exists q0, q0 ∈ seeds /\ ENFA.reachable M q0 [] q.

Lemma eclose_work_acc_sound (M : ENFA.t)
  : forall (st : close_state M) (ACC : Acc (close_lt M) st) (seeds : list M.(ENFA.state)), origins M seeds (close_pending st) -> origins M seeds (close_seen st) -> origins M seeds (eclose_work_acc M st ACC).
Proof.
  refine (fix IH st ACC {struct ACC} := _).
  intros seeds PENDING SEEN.
  destruct ACC as [ACC_INV].
  destruct st as [[unseen pending] seen].
  destruct pending as [ | q pending]; simpl in *.
  all: unfold close_pending, close_seen in *; simpl in *.
  - exact SEEN.
  - destruct (state_mem M q seen) eqn: IN_SEEN.
    + eapply (IH ((unseen, pending), seen) (ACC_INV ((unseen, pending), seen) (close_lt_skip M unseen pending seen q))).
      * intros x IN. unfold close_pending in IN. simpl in IN.
        eapply PENDING. right. exact IN.
      * exact SEEN.
    + destruct (in_dec eq_dec q unseen) as [IN_UNSEEN | NOT_IN_UNSEEN].
      * eapply (IH ((remove eq_dec q unseen, M.(ENFA.eps_step) q ++ pending), q :: seen) (ACC_INV ((remove eq_dec q unseen, M.(ENFA.eps_step) q ++ pending), q :: seen) (close_lt_process M unseen pending seen q IN_UNSEEN))).
        { intros x IN. unfold close_pending in IN. simpl in IN.
          rewrite in_app_iff in IN. destruct IN as [STEP | IN].
          - pose proof (PENDING q (or_introl eq_refl)) as (q0 & IN0 & REACH0).
            exists q0. split; [exact IN0 | ].
            change (@nil ascii) with ((@nil ascii) ++ (@nil ascii)).
            eapply ENFA_reachable_app with (q2 := q).
            + exact REACH0.
            + eapply ENFA.reachable_eps with (q2 := x); eauto with *.
          - eapply PENDING. right. exact IN.
        }
        { intros x IN. unfold close_seen in IN. simpl in IN.
          destruct IN as [EQ | IN].
          - subst x. eapply PENDING. left. reflexivity.
          - eapply SEEN. exact IN.
        }
      * eapply (IH ((unseen, pending), seen) (ACC_INV ((unseen, pending), seen) (close_lt_skip M unseen pending seen q))).
        { intros x IN. unfold close_pending in IN. simpl in IN.
          eapply PENDING. right. exact IN. }
        { exact SEEN. }
Qed.

Theorem eclose_sound (M : ENFA.t) (qs : list M.(ENFA.state)) (q : M.(ENFA.state))
  (IN : q ∈ eclose M qs)
  : exists q0, q0 ∈ qs /\ ENFA.reachable M q0 [] q.
Proof.
  unfold eclose in IN.
  eapply eclose_work_acc_sound in IN.
  - exact IN.
  - intros q0 IN0. exists q0. split; eauto with *.
  - intros q0 IN0. contradiction.
Qed.

Definition unseen_complete (M : ENFA.t) (unseen : list M.(ENFA.state)) (seen : list M.(ENFA.state)) : Prop :=
  forall q, q ∈ M.(ENFA.states) -> ~ q ∈ seen -> q ∈ unseen.

Definition frontier_closed (M : ENFA.t) (pending : list M.(ENFA.state)) (seen : list M.(ENFA.state)) : Prop :=
  forall q, forall q', q ∈ seen -> q' ∈ M.(ENFA.eps_step) q -> q' ∈ pending \/ q' ∈ seen.

Lemma subset_of_states_tail (M : ENFA.t) (q : M.(ENFA.state)) (qs : list M.(ENFA.state))
  (SUBSET : subset_of_states M (q :: qs))
  : subset_of_states M qs.
Proof.
  intros x IN. eapply SUBSET. right. exact IN.
Qed.

Lemma subset_of_states_remove (M : ENFA.t) (q : M.(ENFA.state)) (qs : list M.(ENFA.state))
  (SUBSET : subset_of_states M qs)
  : subset_of_states M (remove eq_dec q qs).
Proof.
  intros x IN. rewrite L.in_remove_iff in IN. eapply SUBSET. exact (proj1 IN).
Qed.

Lemma subset_of_states_app (M : ENFA.t) (xs : list M.(ENFA.state)) (ys : list M.(ENFA.state))
  (SUBSET_XS : subset_of_states M xs)
  (SUBSET_YS : subset_of_states M ys)
  : subset_of_states M (xs ++ ys).
Proof.
  intros q IN. rewrite in_app_iff in IN. destruct IN as [IN | IN].
  - eapply SUBSET_XS. exact IN.
  - eapply SUBSET_YS. exact IN.
Qed.

Lemma subset_of_states_eps_step (M : ENFA.t) (q : M.(ENFA.state))
  (WF : ENFA.wf M)
  (IN : q ∈ M.(ENFA.states))
  : subset_of_states M (M.(ENFA.eps_step) q).
Proof.
  destruct WF as (_ & _ & EPS_WF & _).
  intros q' STEP. eapply EPS_WF; eauto.
Qed.

Lemma unseen_complete_process (M : ENFA.t) (unseen : list M.(ENFA.state)) (pending : list M.(ENFA.state)) (seen : list M.(ENFA.state)) (q : M.(ENFA.state))
  (COMPLETE : unseen_complete M unseen seen)
  : unseen_complete M (remove eq_dec q unseen) (q :: seen).
Proof.
  intros x IN_STATES NOT_SEEN.
  rewrite L.in_remove_iff. split.
  - eapply COMPLETE.
    + exact IN_STATES.
    + intros IN_SEEN. eapply NOT_SEEN. right. exact IN_SEEN.
  - intros EQ. subst x. eapply NOT_SEEN. left. reflexivity.
Qed.

Lemma frontier_closed_skip_seen (M : ENFA.t) (pending : list M.(ENFA.state)) (seen : list M.(ENFA.state)) (q : M.(ENFA.state))
  (IN_SEEN : q ∈ seen)
  (FRONTIER : frontier_closed M (q :: pending) seen)
  : frontier_closed M pending seen.
Proof.
  intros x y IN_X STEP.
  pose proof (FRONTIER x y IN_X STEP) as [[EQ | IN] | IN].
  - subst y. right. exact IN_SEEN.
  - left. exact IN.
  - right. exact IN.
Qed.

Lemma frontier_closed_process (M : ENFA.t) (pending : list M.(ENFA.state)) (seen : list M.(ENFA.state)) (q : M.(ENFA.state))
  (FRONTIER : frontier_closed M (q :: pending) seen)
  : frontier_closed M (M.(ENFA.eps_step) q ++ pending) (q :: seen).
Proof.
  intros x y IN_X STEP.
  destruct IN_X as [EQ | IN_X].
  - subst x. left. rewrite in_app_iff. left. exact STEP.
  - pose proof (FRONTIER x y IN_X STEP) as [[EQ | IN] | IN].
    + subst y. right. left. reflexivity.
    + left. rewrite in_app_iff. right. exact IN.
    + right. right. exact IN.
Qed.

Lemma frontier_closed_skip_unknown (M : ENFA.t) (unseen : list M.(ENFA.state)) (pending : list M.(ENFA.state)) (seen : list M.(ENFA.state)) (q : M.(ENFA.state))
  (WF : ENFA.wf M)
  (SEEN_STATES : subset_of_states M seen)
  (COMPLETE : unseen_complete M unseen seen)
  (NOT_UNSEEN : ~ q ∈ unseen)
  (NOT_SEEN : ~ q ∈ seen)
  (FRONTIER : frontier_closed M (q :: pending) seen)
  : frontier_closed M pending seen.
Proof.
  intros x y IN_X STEP.
  pose proof (FRONTIER x y IN_X STEP) as [[EQ | IN] | IN].
  - subst y.
    exfalso. eapply NOT_UNSEEN.
    eapply COMPLETE.
    + eapply (subset_of_states_eps_step M x WF (SEEN_STATES x IN_X)).
      exact STEP.
    + exact NOT_SEEN.
  - left. exact IN.
  - right. exact IN.
Qed.

Lemma eclose_work_acc_contains (M : ENFA.t)
  (WF : ENFA.wf M)
  : forall (st : close_state M) (ACC : Acc (close_lt M) st), subset_of_states M (close_unseen st) -> subset_of_states M (close_pending st) -> subset_of_states M (close_seen st) -> unseen_complete M (close_unseen st) (close_seen st) -> forall q, q ∈ close_pending st \/ q ∈ close_seen st -> q ∈ eclose_work_acc M st ACC.
Proof.
  refine (fix IH st ACC {struct ACC} := _).
  intros UNSEEN_STATES PENDING_STATES SEEN_STATES COMPLETE x IN_X.
  destruct ACC as [ACC_INV].
  destruct st as [[unseen pending] seen].
  destruct pending as [ | q pending]; simpl in *.
  all: unfold close_unseen, close_pending, close_seen in *; simpl in *.
  - destruct IN_X as [IN_X | IN_X]; [contradiction | exact IN_X].
  - destruct (state_mem M q seen) eqn: IN_SEENb.
    + eapply (IH ((unseen, pending), seen) (ACC_INV ((unseen, pending), seen) (close_lt_skip M unseen pending seen q))).
      * exact UNSEEN_STATES.
      * eapply subset_of_states_tail. exact PENDING_STATES.
      * exact SEEN_STATES.
      * exact COMPLETE.
      * destruct IN_X as [[EQ | IN_PENDING] | IN_SEEN].
        { subst x. right. rewrite <- state_mem_true_iff. exact IN_SEENb. }
        { left. exact IN_PENDING. }
        { right. exact IN_SEEN. }
    + destruct (in_dec eq_dec q unseen) as [IN_UNSEEN | NOT_UNSEEN].
      * eapply (IH ((remove eq_dec q unseen, M.(ENFA.eps_step) q ++ pending), q :: seen) (ACC_INV ((remove eq_dec q unseen, M.(ENFA.eps_step) q ++ pending), q :: seen) (close_lt_process M unseen pending seen q IN_UNSEEN))).
        { eapply subset_of_states_remove. exact UNSEEN_STATES. }
        { eapply subset_of_states_app.
          - eapply subset_of_states_eps_step; eauto.
          - eapply subset_of_states_tail. exact PENDING_STATES.
        }
        { intros y IN. destruct IN as [EQ | IN].
          - subst y. eapply UNSEEN_STATES. exact IN_UNSEEN.
          - eapply SEEN_STATES. exact IN.
        }
        { eapply (unseen_complete_process M unseen pending seen q).
          exact COMPLETE. }
        { destruct IN_X as [[EQ | IN_PENDING] | IN_SEEN].
          - subst x. right. left. reflexivity.
          - left. simpl. rewrite in_app_iff. right. exact IN_PENDING.
          - right. right. exact IN_SEEN.
        }
      * assert (NOT_SEEN : ~ q ∈ seen).
        { rewrite <- state_mem_false_iff. exact IN_SEENb. }
        eapply (IH ((unseen, pending), seen) (ACC_INV ((unseen, pending), seen) (close_lt_skip M unseen pending seen q))).
        { exact UNSEEN_STATES. }
        { eapply subset_of_states_tail. exact PENDING_STATES. }
        { exact SEEN_STATES. }
        { exact COMPLETE. }
        { destruct IN_X as [[EQ | IN_PENDING] | IN_SEEN].
          - subst x. exfalso. eapply NOT_UNSEEN.
            eapply COMPLETE.
            + eapply PENDING_STATES. left. reflexivity.
            + exact NOT_SEEN.
          - left. exact IN_PENDING.
          - right. exact IN_SEEN.
        }
Qed.

Lemma eclose_contains_seeds (M : ENFA.t) (qs : list M.(ENFA.state))
  (WF : ENFA.wf M)
  (QS : subset_of_states M qs)
  : forall q, q ∈ qs -> q ∈ eclose M qs.
Proof.
  intros q IN.
  unfold eclose.
  eapply eclose_work_acc_contains.
  - exact WF.
  - intros x IN_X. exact IN_X.
  - exact QS.
  - intros x IN_X. contradiction.
  - intros x IN_X _. exact IN_X.
  - left. exact IN.
Qed.

Lemma eclose_work_acc_frontier (M : ENFA.t)
  (WF : ENFA.wf M)
  : forall (st : close_state M) (ACC : Acc (close_lt M) st), subset_of_states M (close_unseen st) -> subset_of_states M (close_pending st) -> subset_of_states M (close_seen st) -> unseen_complete M (close_unseen st) (close_seen st) -> frontier_closed M (close_pending st) (close_seen st) -> forall q q', q ∈ eclose_work_acc M st ACC -> q' ∈ M.(ENFA.eps_step) q -> q' ∈ eclose_work_acc M st ACC.
Proof.
  refine (fix IH st ACC {struct ACC} := _).
  intros UNSEEN_STATES PENDING_STATES SEEN_STATES COMPLETE FRONTIER x y IN_X STEP.
  destruct ACC as [ACC_INV].
  destruct st as [[unseen pending] seen].
  destruct pending as [ | q pending]; simpl in *.
  all: unfold close_unseen, close_pending, close_seen in *; simpl in *.
  - pose proof (FRONTIER x y IN_X STEP) as [IN_PENDING | IN_SEEN].
    + contradiction.
    + exact IN_SEEN.
  - destruct (state_mem M q seen) eqn: IN_SEENb.
    + eapply (IH ((unseen, pending), seen)
          (ACC_INV ((unseen, pending), seen)
             (close_lt_skip M unseen pending seen q))); eauto.
      * eapply subset_of_states_tail. exact PENDING_STATES.
      * eapply frontier_closed_skip_seen.
        { rewrite <- state_mem_true_iff. exact IN_SEENb. }
        { exact FRONTIER. }
    + destruct (in_dec eq_dec q unseen) as [IN_UNSEEN | NOT_UNSEEN].
      * eapply (IH ((remove eq_dec q unseen, M.(ENFA.eps_step) q ++ pending), q :: seen) (ACC_INV ((remove eq_dec q unseen, M.(ENFA.eps_step) q ++ pending), q :: seen) (close_lt_process M unseen pending seen q IN_UNSEEN))); eauto.
        { eapply subset_of_states_remove. exact UNSEEN_STATES. }
        { eapply subset_of_states_app.
          - eapply subset_of_states_eps_step; eauto.
          - eapply subset_of_states_tail. exact PENDING_STATES.
        }
        { intros z IN. destruct IN as [EQ | IN].
          - subst z. eapply UNSEEN_STATES. exact IN_UNSEEN.
          - eapply SEEN_STATES. exact IN.
        }
        { eapply (unseen_complete_process M unseen pending seen q). exact COMPLETE. }
        { eapply frontier_closed_process. exact FRONTIER. }
      * assert (NOT_SEEN : ~ q ∈ seen).
        { rewrite <- state_mem_false_iff. exact IN_SEENb. }
        eapply (IH ((unseen, pending), seen) (ACC_INV ((unseen, pending), seen)  (close_lt_skip M unseen pending seen q))); eauto.
        { eapply subset_of_states_tail. exact PENDING_STATES. }
        { eapply frontier_closed_skip_unknown; eauto. }
Qed.

Lemma eclose_closed (M : ENFA.t) (qs : list M.(ENFA.state))
  (WF : ENFA.wf M)
  (QS : subset_of_states M qs)
  : forall q q', q ∈ eclose M qs -> q' ∈ M.(ENFA.eps_step) q -> q' ∈ eclose M qs.
Proof.
  intros q q' IN STEP.
  unfold eclose in *.
  eapply (eclose_work_acc_frontier M WF
    ((M.(ENFA.states), qs), [])
    (close_lt_wf M ((M.(ENFA.states), qs), []))).
  - intros x IN_X. exact IN_X.
  - exact QS.
  - intros x IN_X. contradiction.
  - intros x IN_X _. exact IN_X.
  - intros x y IN_X. contradiction.
  - exact IN.
  - exact STEP.
Qed.

Theorem eclose_complete (M : ENFA.t) (qs : list M.(ENFA.state)) (q0 : M.(ENFA.state)) (q : M.(ENFA.state))
  (WF : ENFA.wf M)
  (QS : subset_of_states M qs)
  (IN : q0 ∈ qs)
  (REACH : ENFA.reachable M q0 [] q)
  : q ∈ eclose M qs.
Proof.
  pose proof (ENFA_reachable_nil_eclose M q0 q REACH) as CLOSE.
  pose proof (eclose_contains_seeds M qs WF QS q0 IN) as IN_CLOSE.
  clear IN REACH.
  revert IN_CLOSE.
  induction CLOSE as [q | q1 q2 q3 STEP REST IH]; intros IN_CLOSE.
  - exact IN_CLOSE.
  - eapply IH. eapply eclose_closed; eauto.
Qed.

Lemma eclose_subset_states (M : ENFA.t) (qs : list M.(ENFA.state))
  (WF : ENFA.wf M)
  (QS : subset_of_states M qs)
  : subset_of_states M (eclose M qs).
Proof.
  intros q IN.
  pose proof (eclose_sound M qs q IN) as (q0 & IN0 & REACH).
  eapply ENFA_reachable_wf; eauto.
Qed.

Definition move (M : ENFA.t) (qs : list M.(ENFA.state)) (a : ascii)
  : list M.(ENFA.state) :=
  flat_map (fun q => M.(ENFA.char_step) q a) (eclose M qs).

Theorem move_sound (M : ENFA.t) (qs : list M.(ENFA.state)) (a : ascii) (q : M.(ENFA.state))
  (IN : q ∈ move M qs a)
  : exists q0, exists q1, q0 ∈ qs /\ ENFA.reachable M q0 [] q1 /\ q ∈ M.(ENFA.char_step) q1 a.
Proof.
  unfold move in IN. rewrite in_flat_map in IN.
  destruct IN as (q1 & IN_CLOSE & STEP).
  pose proof (eclose_sound M qs q1 IN_CLOSE) as (q0 & IN_QS & REACH).
  exists q0. exists q1. splits; eauto.
Qed.

Theorem move_complete (M : ENFA.t) (qs : list M.(ENFA.state)) (a : ascii) (q0 : M.(ENFA.state)) (q1 : M.(ENFA.state)) (q : M.(ENFA.state))
  (WF : ENFA.wf M)
  (QS : subset_of_states M qs)
  (IN : q0 ∈ qs)
  (EPS : ENFA.reachable M q0 [] q1)
  (STEP : q ∈ M.(ENFA.char_step) q1 a)
  : q ∈ move M qs a.
Proof.
  unfold move. rewrite in_flat_map.
  exists q1. split; [ | exact STEP].
  eapply eclose_complete; eauto.
Qed.

Lemma move_subset_states (M : ENFA.t) (qs : list M.(ENFA.state)) (a : ascii)
  (WF : ENFA.wf M)
  (QS : subset_of_states M qs)
  : subset_of_states M (move M qs a).
Proof.
  intros q IN.
  pose proof (move_sound M qs a q IN) as (q0 & q1 & IN0 & REACH & STEP).
  pose proof WF as WF_COPY.
  destruct WF as (_ & _ & _ & CHAR_WF).
  eapply CHAR_WF with (q := q1) (a := a); [ | exact STEP].
  eapply ENFA_reachable_wf; eauto.
Qed.

Definition start (M : ENFA.t) : dstate M :=
  eclose M [M.(ENFA.start)].

Definition step (M : ENFA.t) (S : dstate M) (a : ascii) : dstate M :=
  eclose M (move M S a).

Theorem step_sound (M : ENFA.t) (S : dstate M) (a : ascii) (q : M.(ENFA.state))
  (IN : q ∈ step M S a)
  : exists q0, exists q1, exists q2, q0 ∈ S /\ ENFA.reachable M q0 [] q1 /\ q2 ∈ M.(ENFA.char_step) q1 a /\ ENFA.reachable M q2 [] q.
Proof.
  unfold step in IN.
  pose proof (eclose_sound M (move M S a) q IN) as (q2 & IN_MOVE & REACH_AFTER).
  pose proof (move_sound M S a q2 IN_MOVE) as (q0 & q1 & IN_S & REACH_BEFORE & STEP).
  exists q0. exists q1. exists q2. splits; eauto.
Qed.

Theorem step_complete (M : ENFA.t) (S : dstate M) (a : ascii) (q0 : M.(ENFA.state)) (q1 : M.(ENFA.state)) (q2 : M.(ENFA.state)) (q : M.(ENFA.state))
  (WF : ENFA.wf M)
  (QS : subset_of_states M S)
  (IN : q0 ∈ S)
  (EPS : ENFA.reachable M q0 [] q1)
  (STEP : q2 ∈ M.(ENFA.char_step) q1 a)
  (EPS_AFTER : ENFA.reachable M q2 [] q)
  : q ∈ step M S a.
Proof.
  unfold step.
  eapply eclose_complete with (q0 := q2); eauto.
  - eapply move_subset_states; eauto.
  - eapply move_complete with (q0 := q0) (q1 := q1); eauto.
Qed.

Definition eclosed (M : ENFA.t) (S : dstate M) : Prop :=
  forall q0 q, q0 ∈ S -> ENFA.reachable M q0 [] q -> q ∈ S.

Lemma eclose_eclosed (M : ENFA.t) (qs : list M.(ENFA.state))
  (WF : ENFA.wf M)
  (QS : subset_of_states M qs)
  : eclosed M (eclose M qs).
Proof.
  intros q0 q IN REACH.
  pose proof (ENFA_reachable_nil_eclose M q0 q REACH) as CLOSE.
  clear REACH.
  revert IN.
  induction CLOSE as [q | q1 q2 q3 STEP REST IH]; intros IN.
  - exact IN.
  - eapply IH. eapply eclose_closed; eauto.
Qed.

Lemma start_subset_states (M : ENFA.t)
  (WF : ENFA.wf M)
  : subset_of_states M (start M).
Proof.
  unfold start. eapply eclose_subset_states; eauto.
  intros q IN. destruct WF as (START_OK & _).
  destruct IN as [EQ | []]. subst q. exact START_OK.
Qed.

Lemma start_eclosed (M : ENFA.t)
  (WF : ENFA.wf M)
  : eclosed M (start M).
Proof.
  unfold start. eapply eclose_eclosed; eauto.
  intros q IN. destruct WF as (START_OK & _).
  destruct IN as [EQ | []]. subst q. exact START_OK.
Qed.

Lemma step_subset_states (M : ENFA.t) (S : dstate M) (a : ascii)
  (WF : ENFA.wf M)
  (QS : subset_of_states M S)
  : subset_of_states M (step M S a).
Proof.
  unfold step. eapply eclose_subset_states; eauto.
  eapply move_subset_states; eauto.
Qed.

Lemma step_eclosed (M : ENFA.t) (S : dstate M) (a : ascii)
  (WF : ENFA.wf M)
  (QS : subset_of_states M S)
  : eclosed M (step M S a).
Proof.
  unfold step. eapply eclose_eclosed; eauto.
  eapply move_subset_states; eauto.
Qed.

End Subset.

Definition forget_tagged_enfa (M : TaggedENFA.t) : ENFA.t :=
  ENFA.mk M.(TaggedENFA.state) M.(TaggedENFA.state_hasEqDec) M.(TaggedENFA.states) M.(TaggedENFA.start_state) (map fst M.(TaggedENFA.accept_states)) M.(TaggedENFA.eps_step) M.(TaggedENFA.char_step).

Theorem forget_tagged_enfa_wf (M : TaggedENFA.t)
  (OKAY : TaggedENFA.okay M)
  : ENFA.wf (forget_tagged_enfa M).
Proof.
  destruct OKAY as [START_OK ACCEPT_OK EPS_OK CHAR_OK].
  simpl. repeat split.
  - exact START_OK.
  - intros q IN. unfold forget_tagged_enfa in IN |- *. simpl in IN |- *.
    rewrite in_map_iff in IN.
    destruct IN as ([q' tag] & EQ & IN). simpl in EQ. subst q'.
    eapply ACCEPT_OK. exact IN.
  - exact EPS_OK.
  - exact CHAR_OK.
Qed.

Theorem forget_tagged_reachable_sound (M : TaggedENFA.t) (q1 : M.(TaggedENFA.state)) (q2 : M.(TaggedENFA.state)) (s : list ascii)
  (REACH : ENFA.reachable (forget_tagged_enfa M) q1 s q2)
  : q2 \in TaggedENFA.delta_star M q1 s.
Proof.
  induction REACH as [q | q1' q2' q3' s STEP REST IH | q1' q2' q3' a s STEP REST IH]; simpl in *.
  - eapply TaggedENFA.delta_star_nil.
  - eapply TaggedENFA.delta_star_eps; eauto.
  - eapply TaggedENFA.delta_star_char; eauto.
Qed.

Theorem forget_tagged_reachable_complete (M : TaggedENFA.t) (q1 : M.(TaggedENFA.state)) (q2 : M.(TaggedENFA.state)) (s : list ascii)
  (DELTA : q2 \in TaggedENFA.delta_star M q1 s)
  : ENFA.reachable (forget_tagged_enfa M) q1 s q2.
Proof.
  induction DELTA as [q | q q1' q2' s STEP REST IH | q q1' q2' c s STEP REST IH]; simpl in *.
  - eapply ENFA.reachable_nil.
  - eapply ENFA.reachable_eps; eauto.
  - eapply ENFA.reachable_char; eauto.
Qed.

Theorem forget_tagged_reachable_iff (M : TaggedENFA.t) (q1 : M.(TaggedENFA.state)) (q2 : M.(TaggedENFA.state)) (s : list ascii)
  : ENFA.reachable (forget_tagged_enfa M) q1 s q2 <-> q2 \in TaggedENFA.delta_star M q1 s.
Proof.
  split.
  - eapply forget_tagged_reachable_sound.
  - eapply forget_tagged_reachable_complete.
Qed.

Module TaggedDFA.

#[projections(primitive)]
Record t : Type :=
  mk
  { state : Set
  ; state_hasEqDec : hasEqDec@{Set} state
  ; states : list state
  ; start_state : state
  ; step : state -> ascii -> state
  ; accept_tag : state -> option Token.t
  }.

#[global] Existing Instance state_hasEqDec.

Fixpoint run_from (M : t) (q : M.(state)) (s : Input.t) {struct s} : M.(state) :=
  match s with
  | [] => q
  | c :: s' => run_from M (M.(step) q c) s'
  end.

Definition run (M : t) (s : Input.t) : M.(state) :=
  run_from M M.(start_state) s.

Definition accepted_tag (M : t) (s : Input.t) : option Token.t :=
  M.(accept_tag) (run M s).

Definition accepts (M : t) (s : Input.t) (tag : Token.t) : Prop :=
  accepted_tag M s = Some tag.

Definition okay (M : t) : Prop :=
  M.(start_state) ∈ M.(states) /\
  forall q q' c, q ∈ M.(states) -> M.(step) q c = q' -> q' ∈ M.(states).

Inductive reachable (M : t) : M.(state) -> Input.t -> M.(state) -> Prop :=
  | reachable_nil q
    : reachable M q [] q
  | reachable_char q1 q2 q3 c s
    (STEP : M.(step) q1 c = q2)
    (REST : reachable M q2 s q3)
    : reachable M q1 (c :: s) q3.

#[local] Hint Constructors reachable : core.

Theorem run_from_spec (M : t) (q : M.(state)) (q' : M.(state)) (s : Input.t)
  : run_from M q s = q' <-> reachable M q s q'.
Proof.
  split.
  - revert q q'. induction s as [ | c s IH]; simpl; intros q q' RUN.
    + subst q'. eauto with *.
    + eapply reachable_char with (q2 := M.(step) q c); eauto.
  - intros REACH. induction REACH as [q | q1 q2 q3 c s STEP REST IH]; simpl.
    + reflexivity.
    + rewrite STEP. exact IH.
Qed.

Theorem run_from_app (M : t) (q : M.(state)) (s1 : Input.t) (s2 : Input.t)
  : run_from M q (s1 ++ s2) = run_from M (run_from M q s1) s2.
Proof.
  revert q. induction s1 as [ | c s1 IH]; simpl; intros q.
  - reflexivity.
  - eapply IH.
Qed.

Theorem run_from_okay (M : t) (q : M.(state)) (s : Input.t)
  (OKAY : okay M)
  (IN : q ∈ M.(states))
  : run_from M q s ∈ M.(states).
Proof.
  destruct OKAY as [_ STEP_OK].
  revert q IN. induction s as [ | c s IH]; simpl; intros q IN.
  - exact IN.
  - eapply IH. eapply STEP_OK; [exact IN | reflexivity].
Qed.

Theorem run_okay (M : t) (s : Input.t)
  (OKAY : okay M)
  : run M s ∈ M.(states).
Proof.
  destruct OKAY as [START_OK STEP_OK].
  unfold run.
  eapply run_from_okay; [split; eauto | exact START_OK].
Qed.

Theorem run_deterministic (M : t) (q : M.(state)) (q1 : M.(state)) (q2 : M.(state)) (s : Input.t)
  (REACH1 : reachable M q s q1)
  (REACH2 : reachable M q s q2)
  : q1 = q2.
Proof.
  rewrite <- run_from_spec in REACH1.
  rewrite <- run_from_spec in REACH2.
  congruence.
Qed.

Theorem accepted_tag_spec (M : t) (s : Input.t) (tag : Token.t)
  : accepts M s tag <-> accepted_tag M s = Some tag.
Proof.
  reflexivity.
Qed.

Theorem accepted_tag_priority (M : t) (s : Input.t) (tag : Token.t)
  (ACCEPT : accepted_tag M s = Some tag)
  : accepts M s tag.
Proof.
  exact ACCEPT.
Qed.

End TaggedDFA.

Module TaggedSubset.

Definition dstate (M : TaggedENFA.t) : Set :=
  list M.(TaggedENFA.state).

Definition state_mem (M : TaggedENFA.t) : M.(TaggedENFA.state) -> list M.(TaggedENFA.state) -> bool :=
  mem (EQ_DEC := M.(TaggedENFA.state_hasEqDec)).

Lemma state_mem_true_iff (M : TaggedENFA.t) (q : M.(TaggedENFA.state)) (qs : list M.(TaggedENFA.state))
  : state_mem M q qs = true <-> q ∈ qs.
Proof.
  unfold state_mem. eapply mem_true_iff.
Qed.

Lemma state_mem_false_iff (M : TaggedENFA.t) (q : M.(TaggedENFA.state)) (qs : list M.(TaggedENFA.state))
  : state_mem M q qs = false <-> ~ q ∈ qs.
Proof.
  unfold state_mem. eapply mem_false_iff.
Qed.

Definition normalize (M : TaggedENFA.t) (S : dstate M) : dstate M :=
  filter (fun q => state_mem M q S) M.(TaggedENFA.states).

Definition all_dstates (M : TaggedENFA.t) : list (dstate M) :=
  powerset M.(TaggedENFA.states).

Definition start (M : TaggedENFA.t) : dstate M :=
  normalize M (Subset.start (forget_tagged_enfa M)).

Definition step (M : TaggedENFA.t) (S : dstate M) (c : ascii) : dstate M :=
  normalize M (Subset.step (forget_tagged_enfa M) S c).

Definition successors (M : TaggedENFA.t) (S : dstate M) : list (dstate M) :=
  map (step M S) all_asciis.

Definition subset_graph_enfa (M : TaggedENFA.t) : ENFA.t :=
  ENFA.mk (dstate M) (list_hasEqDec M.(TaggedENFA.state_hasEqDec)) (all_dstates M) (start M) [] (successors M) (fun _ => fun _ => []).

Definition reachable_states (M : TaggedENFA.t) : list (dstate M) :=
  Subset.eclose (subset_graph_enfa M) [start M].

Definition states (M : TaggedENFA.t) : list (dstate M) :=
  reachable_states M.

Fixpoint first_accept_tag {Q : Set} `{EQ_DEC : hasEqDec@{Set} Q} (S : list Q) (accepts : list (Q * Token.t)) {struct accepts} : option Token.t :=
  match accepts with
  | [] => None
  | (q, tag) :: accepts' =>
    if mem (EQ_DEC := EQ_DEC) q S then
      Some tag
    else
      first_accept_tag (EQ_DEC := EQ_DEC) S accepts'
  end.

Definition tagged_first_accept_tag (M : TaggedENFA.t) (S : dstate M) (accepts : list (M.(TaggedENFA.state) * Token.t)) : option Token.t :=
  first_accept_tag (EQ_DEC := M.(TaggedENFA.state_hasEqDec)) S accepts.

Definition accept_tag (M : TaggedENFA.t) (S : dstate M) : option Token.t :=
  tagged_first_accept_tag M S M.(TaggedENFA.accept_states).

Definition compile (M : TaggedENFA.t) : TaggedDFA.t :=
  TaggedDFA.mk (dstate M) (list_hasEqDec M.(TaggedENFA.state_hasEqDec)) (states M) (start M) (step M) (accept_tag M).

Lemma normalize_sound (M : TaggedENFA.t) (S : dstate M) (q : M.(TaggedENFA.state))
  (IN : q ∈ normalize M S)
  : q ∈ M.(TaggedENFA.states) /\ q ∈ S.
Proof.
  unfold normalize in IN. rewrite filter_In in IN.
  destruct IN as [IN_STATES MEM].
  split; [exact IN_STATES | ].
  rewrite <- state_mem_true_iff. exact MEM.
Qed.

Lemma normalize_complete (M : TaggedENFA.t) (S : dstate M) (q : M.(TaggedENFA.state))
  (IN_STATES : q ∈ M.(TaggedENFA.states))
  (IN : q ∈ S)
  : q ∈ normalize M S.
Proof.
  unfold normalize. rewrite filter_In. split; [exact IN_STATES | ].
  rewrite state_mem_true_iff. exact IN.
Qed.

Lemma normalize_subset_states (M : TaggedENFA.t) (S : dstate M)
  : Subset.subset_of_states (forget_tagged_enfa M) (normalize M S).
Proof.
  intros q IN.
  pose proof (normalize_sound M S q IN) as [IN_STATES _].
  exact IN_STATES.
Qed.

Lemma start_in_all_dstates (M : TaggedENFA.t)
  : start M ∈ all_dstates M.
Proof.
  unfold start, all_dstates, normalize.
  eapply filter_in_powerset.
Qed.

Lemma step_in_all_dstates (M : TaggedENFA.t) (S : dstate M) (c : ascii)
  : step M S c ∈ all_dstates M.
Proof.
  unfold step, all_dstates, normalize.
  eapply filter_in_powerset.
Qed.

Lemma subset_graph_enfa_wf (M : TaggedENFA.t)
  : ENFA.wf (subset_graph_enfa M).
Proof.
  unfold subset_graph_enfa. simpl. repeat split.
  - eapply start_in_all_dstates.
  - intros q IN. contradiction.
  - intros S S' IN_STATES IN_SUCC.
    change (S' ∈ successors M S) in IN_SUCC.
    unfold successors in IN_SUCC. rewrite in_map_iff in IN_SUCC.
    destruct IN_SUCC as (c & EQ & _). subst S'.
    eapply step_in_all_dstates.
  - intros S S' c IN_STATES IN_STEP. contradiction.
Qed.

Lemma start_in_states (M : TaggedENFA.t)
  : start M ∈ states M.
Proof.
  unfold states, reachable_states.
  assert (QS : Subset.subset_of_states (subset_graph_enfa M) [start M]).
  { intros S IN. destruct IN as [EQ | []]. subst S.
    simpl. eapply start_in_all_dstates.
  }
  pose proof (Subset.eclose_contains_seeds (subset_graph_enfa M) [start M] (subset_graph_enfa_wf M) QS (start M) (or_introl eq_refl)) as IN_START.
  exact IN_START.
Qed.

Lemma step_in_states (M : TaggedENFA.t) (S : dstate M) (c : ascii)
  (IN : S ∈ states M)
  : step M S c ∈ states M.
Proof.
  unfold states, reachable_states in *.
  assert (QS : Subset.subset_of_states (subset_graph_enfa M) [start M]).
  { intros S0 IN0. destruct IN0 as [EQ | []]. subst S0.
    simpl. eapply start_in_all_dstates.
  }
  assert (STEP_EDGE : step M S c ∈ ENFA.eps_step (subset_graph_enfa M) S).
  { change (step M S c ∈ successors M S).
    unfold successors. rewrite in_map_iff.
    exists c. split; [reflexivity | eapply all_asciis_complete].
  }
  pose proof (Subset.eclose_closed (subset_graph_enfa M) [start M] (subset_graph_enfa_wf M) QS S (step M S c) IN STEP_EDGE) as IN_STEP.
  exact IN_STEP.
Qed.

Theorem subset_construction_okay (M : TaggedENFA.t)
  : TaggedDFA.okay (compile M).
Proof.
  unfold TaggedDFA.okay, compile. simpl.
  split.
  - eapply start_in_states.
  - intros q q' c IN STEP_EQ. subst q'. eapply step_in_states. exact IN.
Qed.

Theorem first_accept_tag_sound {Q : Set} `{EQ_DEC : hasEqDec@{Set} Q} (S : list Q) (accepts : list (Q * Token.t)) (tag : Token.t)
  (BEST : first_accept_tag (EQ_DEC := EQ_DEC) S accepts = Some tag)
  : exists q, q ∈ S /\ (q, tag) ∈ accepts.
Proof.
  induction accepts as [ | [q tag0] accepts IH]; simpl in BEST.
  - discriminate.
  - destruct (mem (EQ_DEC := EQ_DEC) q S) eqn: IN_Q.
    + inv BEST. exists q. split.
      * rewrite <- @mem_true_iff with (EQ_DEC := EQ_DEC). exact IN_Q.
      * left. reflexivity.
    + pose proof (IH BEST) as (q' & IN_S & IN_ACCEPTS).
      exists q'. split.
      * exact IN_S.
      * right. exact IN_ACCEPTS.
Qed.

Theorem dfa_accept_tag_correct (M : TaggedENFA.t) (S : dstate M) (tag : Token.t)
  (ACCEPT : TaggedDFA.accept_tag (compile M) S = Some tag)
  : exists q, q ∈ S /\ (q, tag) ∈ M.(TaggedENFA.accept_states).
Proof.
  simpl in ACCEPT. eapply first_accept_tag_sound. exact ACCEPT.
Qed.

Theorem dfa_accept_tag_complete (M : TaggedENFA.t) (S : dstate M) (tag : Token.t)
  (ACCEPT : TaggedDFA.accept_tag (compile M) S = Some tag)
  : accept_tag M S = Some tag.
Proof.
  exact ACCEPT.
Qed.

Theorem dfa_step_correct_sound (M : TaggedENFA.t) (S : dstate M) (c : ascii) (q : M.(TaggedENFA.state))
  (IN : q ∈ step M S c)
  : exists q0, exists q1, exists q2, q0 ∈ S /\ ENFA.reachable (forget_tagged_enfa M) q0 [] q1 /\ q2 ∈ M.(TaggedENFA.char_step) q1 c /\ ENFA.reachable (forget_tagged_enfa M) q2 [] q.
Proof.
  unfold step in IN.
  pose proof (normalize_sound M (Subset.step (forget_tagged_enfa M) S c) q IN) as [_ IN_STEP].
  pose proof (Subset.step_sound (forget_tagged_enfa M) S c q IN_STEP) as (q0 & q1 & q2 & IN_S & EPS_BEFORE & STEP & EPS_AFTER).
  simpl in STEP.
  exists q0. exists q1. exists q2. splits; eauto.
Qed.

Theorem dfa_step_correct_complete (M : TaggedENFA.t) (S : dstate M) (c : ascii) (q0 : M.(TaggedENFA.state)) (q1 : M.(TaggedENFA.state)) (q2 : M.(TaggedENFA.state)) (q : M.(TaggedENFA.state))
  (QS : Subset.subset_of_states (forget_tagged_enfa M) S)
  (OKAY : TaggedENFA.okay M)
  (IN : q0 ∈ S)
  (EPS : ENFA.reachable (forget_tagged_enfa M) q0 [] q1)
  (STEP : q2 ∈ M.(TaggedENFA.char_step) q1 c)
  (EPS_AFTER : ENFA.reachable (forget_tagged_enfa M) q2 [] q)
  : q ∈ step M S c.
Proof.
  pose proof (forget_tagged_enfa_wf M OKAY) as WF.
  assert (STEP' : q2 ∈ ENFA.char_step (forget_tagged_enfa M) q1 c).
  { simpl. exact STEP. }
  pose proof (Subset.step_complete (forget_tagged_enfa M) S c
    q0 q1 q2 q WF QS IN EPS STEP' EPS_AFTER) as IN_STEP.
  assert (IN_STATES : q ∈ M.(TaggedENFA.states)).
  { pose proof (Subset.step_subset_states (forget_tagged_enfa M) S c WF QS q IN_STEP) as IN_STATES.
    simpl in IN_STATES. exact IN_STATES.
  }
  unfold step.
  eapply normalize_complete.
  - exact IN_STATES.
  - exact IN_STEP.
Qed.

Lemma normalize_eclosed (M : TaggedENFA.t) (S : dstate M)
  (CLOSED : Subset.eclosed (forget_tagged_enfa M) S)
  (OKAY : TaggedENFA.okay M)
  : Subset.eclosed (forget_tagged_enfa M) (normalize M S).
Proof.
  intros q0 q IN REACH.
  pose proof (normalize_sound M S q0 IN) as [IN_STATES IN_S].
  eapply normalize_complete.
  - assert (IN_STATES' : q0 ∈ ENFA.states (forget_tagged_enfa M)).
    { simpl. exact IN_STATES. }
    pose proof (ENFA_reachable_wf (forget_tagged_enfa M) q0 q [] (forget_tagged_enfa_wf M OKAY) IN_STATES' REACH) as Q_STATES.
    simpl in Q_STATES. exact Q_STATES.
  - eapply CLOSED; eauto.
Qed.

Lemma step_subset_states (M : TaggedENFA.t) (S : dstate M) (c : ascii)
  : Subset.subset_of_states (forget_tagged_enfa M) (step M S c).
Proof.
  unfold step. eapply normalize_subset_states.
Qed.

Lemma step_eclosed (M : TaggedENFA.t) (S : dstate M) (c : ascii)
  (QS : Subset.subset_of_states (forget_tagged_enfa M) S)
  (OKAY : TaggedENFA.okay M)
  : Subset.eclosed (forget_tagged_enfa M) (step M S c).
Proof.
  unfold step. eapply normalize_eclosed; eauto.
  eapply Subset.step_eclosed; eauto.
  eapply forget_tagged_enfa_wf. exact OKAY.
Qed.

Lemma start_subset_states (M : TaggedENFA.t)
  : Subset.subset_of_states (forget_tagged_enfa M) (start M).
Proof.
  unfold start. eapply normalize_subset_states.
Qed.

Lemma start_eclosed (M : TaggedENFA.t)
  (OKAY : TaggedENFA.okay M)
  : Subset.eclosed (forget_tagged_enfa M) (start M).
Proof.
  unfold start. eapply normalize_eclosed; eauto.
  eapply Subset.start_eclosed.
  eapply forget_tagged_enfa_wf. exact OKAY.
Qed.

Theorem dfa_run_from_sound (M : TaggedENFA.t) (s : Input.t) (S : dstate M) (qD : dstate M) (qN : M.(TaggedENFA.state))
  (RUN : TaggedDFA.run_from (compile M) S s = qD)
  (IN : qN ∈ qD)
  : exists q0, q0 ∈ S /\ qN \in TaggedENFA.delta_star M q0 s.
Proof.
  revert S qD qN RUN IN.
  induction s as [ | c s IH]; simpl; intros S qD qN RUN IN.
  - subst qD. exists qN. split; eauto with *.
    eapply TaggedENFA.delta_star_nil.
  - pose proof (IH (step M S c) qD qN RUN IN) as (q_after & IN_STEP & DELTA_TAIL).
    pose proof (dfa_step_correct_sound M S c q_after IN_STEP) as (q0 & q1 & q2 & IN_S & EPS_BEFORE & STEP & EPS_AFTER).
    exists q0. split; [exact IN_S | ].
    eapply forget_tagged_reachable_sound.
    change (c :: s) with ((@nil ascii) ++ (c :: s)).
    eapply ENFA_reachable_app with (q2 := q1).
    + exact EPS_BEFORE.
    + eapply ENFA.reachable_char with (q2 := q2).
      * exact STEP.
      * change s with ((@nil ascii) ++ s).
        eapply ENFA_reachable_app with (q2 := q_after).
        { exact EPS_AFTER. }
        { eapply forget_tagged_reachable_complete. exact DELTA_TAIL. }
Qed.

Theorem dfa_run_from_complete (M : TaggedENFA.t) (s : Input.t) (S : dstate M) (q0 : M.(TaggedENFA.state)) (qN : M.(TaggedENFA.state))
  (QS : Subset.subset_of_states (forget_tagged_enfa M) S)
  (CLOSED : Subset.eclosed (forget_tagged_enfa M) S)
  (OKAY : TaggedENFA.okay M)
  (IN : q0 ∈ S)
  (DELTA : qN \in TaggedENFA.delta_star M q0 s)
  : exists qD, TaggedDFA.run_from (compile M) S s = qD /\ qN ∈ qD.
Proof.
  pose proof (forget_tagged_reachable_complete M q0 qN s DELTA) as REACH.
  clear DELTA.
  revert S QS CLOSED IN.
  induction REACH as [q | q1 q2 q3 s STEP REST IH | q1 q2 q3 c s STEP REST IH]; intros S QS CLOSED IN.
  - exists S. split; [reflexivity | exact IN].
  - assert (IN2 : q2 ∈ S).
    { eapply CLOSED; [exact IN | ]. eapply ENFA.reachable_eps; eauto with *. }
    eapply IH; eauto.
  - simpl.
    assert (IN_STEP : q2 ∈ step M S c).
    { eapply dfa_step_correct_complete with (q0 := q1) (q1 := q1) (q2 := q2); eauto with *. }
    pose proof (IH (step M S c) (step_subset_states M S c) (step_eclosed M S c QS OKAY) IN_STEP) as (qD & RUN & IN_D).
    exists qD. split; [exact RUN | exact IN_D].
Qed.

Theorem dfa_run_sound (M : TaggedENFA.t) (s : Input.t) (q : M.(TaggedENFA.state))
  (IN : q ∈ TaggedDFA.run (compile M) s)
  : q \in TaggedENFA.delta_star M M.(TaggedENFA.start_state) s.
Proof.
  unfold TaggedDFA.run in IN.
  pose proof (dfa_run_from_sound M s (start M) (TaggedDFA.run_from (compile M) (start M) s) q eq_refl IN) as (q0 & IN_START & DELTA).
  unfold start in IN_START.
  pose proof (normalize_sound M (Subset.start (forget_tagged_enfa M)) q0 IN_START) as [_ IN_RAW_START].
  unfold Subset.start in IN_RAW_START.
  pose proof (Subset.eclose_sound (forget_tagged_enfa M) [M.(TaggedENFA.start_state)] q0 IN_RAW_START) as (q_start & IN_SEED & EPS).
  destruct IN_SEED as [EQ | []]. subst q_start.
  eapply forget_tagged_reachable_sound.
  change s with ((@nil ascii) ++ s).
  eapply ENFA_reachable_app with (q2 := q0).
  - exact EPS.
  - eapply forget_tagged_reachable_complete. exact DELTA.
Qed.

Theorem dfa_run_complete (M : TaggedENFA.t) (s : Input.t) (q : M.(TaggedENFA.state))
  (OKAY : TaggedENFA.okay M)
  (DELTA : q \in TaggedENFA.delta_star M M.(TaggedENFA.start_state) s)
  : q ∈ TaggedDFA.run (compile M) s.
Proof.
  unfold TaggedDFA.run.
  pose proof (dfa_run_from_complete M s (start M) M.(TaggedENFA.start_state) q (start_subset_states M) (start_eclosed M OKAY) OKAY) as COMPLETE.
  assert (START_OK : M.(TaggedENFA.start_state) ∈ M.(TaggedENFA.states)).
  { destruct OKAY as [START_OK _ _ _]. exact START_OK. }
  assert (START_IN : M.(TaggedENFA.start_state) ∈ start M).
  { unfold start. eapply normalize_complete.
    - exact START_OK.
    - assert (RAW_START : M.(TaggedENFA.start_state) ∈ Subset.start (forget_tagged_enfa M)).
      { unfold Subset.start.
        pose proof (Subset.eclose_contains_seeds (forget_tagged_enfa M) [M.(TaggedENFA.start_state)] (forget_tagged_enfa_wf M OKAY) (fun q0 => fun IN => match IN with or_introl EQ => eq_ind _ (fun q' => q' ∈ M.(TaggedENFA.states)) START_OK _ EQ | or_intror NIL => False_rect _ NIL end) M.(TaggedENFA.start_state) (or_introl eq_refl)) as RAW_START.
        simpl in RAW_START. exact RAW_START.
      }
      exact RAW_START.
  }
  destruct (COMPLETE START_IN DELTA) as (qD & RUN & IN_Q).
  change (q ∈ TaggedDFA.run_from (compile M) (start M) s).
  rewrite RUN. exact IN_Q.
Qed.

Theorem subset_construction_sound (M : TaggedENFA.t) (s : Input.t) (tag : Token.t)
  (ACCEPT : TaggedDFA.accepted_tag (compile M) s = Some tag)
  : TaggedENFA.accepts M s tag.
Proof.
  unfold TaggedDFA.accepted_tag in ACCEPT.
  pose proof (dfa_accept_tag_correct M (TaggedDFA.run (compile M) s) tag ACCEPT) as (q & IN_RUN & IN_ACCEPT).
  exists q. split.
  - eapply dfa_run_sound. exact IN_RUN.
  - exact IN_ACCEPT.
Qed.

Fixpoint first_delta_accept_tag (M : TaggedENFA.t) (s : Input.t) (accepts : list (M.(TaggedENFA.state) * Token.t)) (tag : Token.t) {struct accepts} : Prop :=
  match accepts with
  | [] => False
  | (q, tag0) :: accepts' => (q \in TaggedENFA.delta_star M M.(TaggedENFA.start_state) s /\ tag0 = tag) \/ (~ q \in TaggedENFA.delta_star M M.(TaggedENFA.start_state) s /\ first_delta_accept_tag M s accepts' tag)
  end.

Definition enfa_priority_accepts (M : TaggedENFA.t) (s : Input.t) (tag : Token.t) : Prop :=
  first_delta_accept_tag M s M.(TaggedENFA.accept_states) tag.

Lemma first_accept_tag_run_priority_sound (M : TaggedENFA.t) (s : Input.t) (accepts : list (M.(TaggedENFA.state) * Token.t)) (tag : Token.t)
  (OKAY : TaggedENFA.okay M)
  (BEST : tagged_first_accept_tag M (TaggedDFA.run (compile M) s) accepts = Some tag)
  : first_delta_accept_tag M s accepts tag.
Proof.
  unfold tagged_first_accept_tag in BEST.
  induction accepts as [ | [q tag0] accepts IH]; simpl in BEST |- *.
  - discriminate.
  - change (mem (EQ_DEC := M.(TaggedENFA.state_hasEqDec)) q (TaggedDFA.run (compile M) s)) with (state_mem M q (TaggedDFA.run (compile M) s)) in BEST.
    destruct (state_mem M q (TaggedDFA.run (compile M) s)) eqn: IN_RUN.
    + inv BEST. left. split; [ | reflexivity].
      eapply dfa_run_sound. rewrite <- state_mem_true_iff. exact IN_RUN.
    + right. split.
      * intros DELTA.
        pose proof (dfa_run_complete M s q OKAY DELTA) as IN.
        rewrite state_mem_false_iff in IN_RUN. contradiction.
      * eapply IH. exact BEST.
Qed.

Lemma first_accept_tag_run_priority_complete (M : TaggedENFA.t) (s : Input.t) (accepts : list (M.(TaggedENFA.state) * Token.t)) (tag : Token.t)
  (OKAY : TaggedENFA.okay M)
  (PRIORITY : first_delta_accept_tag M s accepts tag)
  : tagged_first_accept_tag M (TaggedDFA.run (compile M) s) accepts = Some tag.
Proof.
  unfold tagged_first_accept_tag.
  induction accepts as [ | [q tag0] accepts IH]; simpl in PRIORITY |- *.
  - contradiction.
  - change (mem (EQ_DEC := M.(TaggedENFA.state_hasEqDec)) q (TaggedDFA.run (compile M) s)) with (state_mem M q (TaggedDFA.run (compile M) s)).
    destruct PRIORITY as [[DELTA EQ] | [NOT_DELTA PRIORITY]].
    + subst tag0.
      destruct (state_mem M q (TaggedDFA.run (compile M) s)) eqn: IN_RUN.
      * reflexivity.
      * rewrite state_mem_false_iff in IN_RUN.
        exfalso. eapply IN_RUN. eapply dfa_run_complete; eauto.
    + destruct (state_mem M q (TaggedDFA.run (compile M) s)) eqn: IN_RUN.
      * exfalso. eapply NOT_DELTA.
        eapply dfa_run_sound. rewrite <- state_mem_true_iff. exact IN_RUN.
      * eapply IH. exact PRIORITY.
Qed.

Theorem dfa_accept_tag_priority_correct (M : TaggedENFA.t) (s : Input.t) (tag : Token.t)
  (OKAY : TaggedENFA.okay M)
  : TaggedDFA.accepted_tag (compile M) s = Some tag <-> enfa_priority_accepts M s tag.
Proof.
  unfold TaggedDFA.accepted_tag, enfa_priority_accepts.
  simpl. split.
  - eapply first_accept_tag_run_priority_sound. exact OKAY.
  - eapply first_accept_tag_run_priority_complete. exact OKAY.
Qed.

Theorem subset_construction_exact (M : TaggedENFA.t) (s : Input.t) (tag : Token.t)
  (OKAY : TaggedENFA.okay M)
  : TaggedDFA.accepted_tag (compile M) s = Some tag <-> enfa_priority_accepts M s tag.
Proof.
  eapply dfa_accept_tag_priority_correct. exact OKAY.
Qed.

End TaggedSubset.

Fixpoint first_matching_entry (entries : list (nat * compiled_rule)) (s : Input.t) (cr : compiled_rule) {struct entries} : Prop :=
  match entries with
  | [] => False
  | (_, cr0) :: entries' => (compiled_rule_accepts cr0 s /\ cr = cr0) \/ (~ compiled_rule_accepts cr0 s /\ first_matching_entry entries' s cr)
  end.

Lemma tagged_entry_delta_accept_iff (crs : list compiled_rule) (key : nat) (cr : compiled_rule) (s : Input.t)
  (LOOKUP : lookup_compiled_rule crs key = Some cr)
  : Some (key, (compiled_rule_fragment cr).(Thompson.frag_accept)) \in TaggedENFA.delta_star (build_tagged_enfa crs) (TaggedENFA.start_state (build_tagged_enfa crs)) s <-> compiled_rule_accepts cr s.
Proof.
  split.
  - intros REACH.
    pose proof (tagged_start_delta_sound crs
      (Some (key, (compiled_rule_fragment cr).(Thompson.frag_accept)))
      s REACH) as [(EQ & _) | (key' & cr' & q & LOOKUP' & TARGET & BODY)].
    + discriminate.
    + inv TARGET.
      assert (cr' = cr) by congruence. subst cr'.
      unfold compiled_rule_accepts.
      eapply Thompson.compile_sound.
      unfold Thompson.fragment_accepts.
      exact BODY.
  - intros ACCEPTS.
    unfold compiled_rule_accepts in ACCEPTS.
    pose proof (Thompson.compile_complete cr.(compiled_rule_regex) s ACCEPTS) as BODY.
    eapply TaggedENFA.delta_star_eps
      with (q1 := Some (key, (compiled_rule_fragment cr).(Thompson.frag_start))).
    + simpl. unfold tagged_eps_step. rewrite in_map_iff.
      exists (key, cr). split; [reflexivity | ].
      eapply compiled_rule_table_lookup_in. exact LOOKUP.
    + eapply tagged_inside_delta_complete; eauto.
Qed.

Lemma first_matching_entry_priority_sound (crs : list compiled_rule) (entries : list (nat * compiled_rule)) (s : Input.t) (tag : Token.t)
  (INCL : forall entry, entry ∈ entries -> entry ∈ compiled_rule_table crs)
  (PRIORITY : TaggedSubset.first_delta_accept_tag (build_tagged_enfa crs) s (map (fun entry => (compiled_rule_accept_state entry, (snd entry).(compiled_rule_token))) entries) tag)
  : exists cr, first_matching_entry entries s cr /\ tag = cr.(compiled_rule_token).
Proof.
  induction entries as [ | [key cr0] entries IH]; simpl in PRIORITY |- *.
  - contradiction.
  - destruct PRIORITY as [[REACH TAG] | [NOT_REACH PRIORITY]].
    + exists cr0. split.
      * left. split; [ | reflexivity].
        eapply tagged_entry_delta_accept_iff.
        { eapply compiled_rule_table_in_lookup. eapply INCL. left. reflexivity. }
        { exact REACH. }
      * symmetry. exact TAG.
    + pose proof (IH (fun entry IN => INCL entry (or_intror IN)) PRIORITY)
        as (cr & FIRST & TAG).
      exists cr. split; [ | exact TAG].
      right. split; [ | exact FIRST].
      intros ACCEPTS. eapply NOT_REACH.
      eapply tagged_entry_delta_accept_iff.
      * eapply compiled_rule_table_in_lookup. eapply INCL. left. reflexivity.
      * exact ACCEPTS.
Qed.

Lemma first_matching_entry_priority_complete (crs : list compiled_rule) (entries : list (nat * compiled_rule)) (s : Input.t) (cr : compiled_rule)
  (INCL : forall entry, entry ∈ entries -> entry ∈ compiled_rule_table crs)
  (FIRST : first_matching_entry entries s cr)
  : TaggedSubset.first_delta_accept_tag (build_tagged_enfa crs) s (map (fun entry => (compiled_rule_accept_state entry, (snd entry).(compiled_rule_token))) entries) cr.(compiled_rule_token).
Proof.
  induction entries as [ | [key cr0] entries IH]; simpl in FIRST |- *.
  - contradiction.
  - destruct FIRST as [[ACCEPTS EQ] | [NOT_ACCEPTS FIRST]].
    + subst cr. left. split; [ | reflexivity].
      eapply tagged_entry_delta_accept_iff.
      * eapply compiled_rule_table_in_lookup. eapply INCL. left. reflexivity.
      * exact ACCEPTS.
    + right. split.
      * intros REACH. eapply NOT_ACCEPTS.
        eapply tagged_entry_delta_accept_iff.
        { eapply compiled_rule_table_in_lookup. eapply INCL. left. reflexivity. }
        { exact REACH. }
      * eapply IH.
        { intros entry IN. eapply INCL. right. exact IN. }
        { exact FIRST. }
Qed.

Theorem build_tagged_enfa_priority_iff (crs : list compiled_rule) (s : Input.t) (tag : Token.t)
  : TaggedSubset.enfa_priority_accepts (build_tagged_enfa crs) s tag <-> exists cr, first_matching_entry (compiled_rule_table crs) s cr /\ tag = cr.(compiled_rule_token).
Proof.
  unfold TaggedSubset.enfa_priority_accepts.
  unfold tagged_accept_states.
  split.
  - eapply first_matching_entry_priority_sound.
    intros entry IN. exact IN.
  - intros (cr & FIRST & TAG). subst tag.
    eapply first_matching_entry_priority_complete.
    + intros entry IN. exact IN.
    + exact FIRST.
Qed.

Module TaggedMinimize.

Definition accepted_from (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) (s : Input.t) : option Token.t :=
  M.(TaggedDFA.accept_tag) (TaggedDFA.run_from M q s).

Definition same_future_tag (M : TaggedDFA.t) (q1 : M.(TaggedDFA.state)) (q2 : M.(TaggedDFA.state)) : Prop :=
  forall s, accepted_from M q1 s = accepted_from M q2 s.

Definition distinguishable (M : TaggedDFA.t) (q1 : M.(TaggedDFA.state)) (q2 : M.(TaggedDFA.state)) : Prop :=
  exists s, accepted_from M q1 s <> accepted_from M q2 s.

Definition state_cardinality (M : TaggedDFA.t) : nat :=
  length (nodup eq_dec M.(TaggedDFA.states)).

Definition reachable_state (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) : Prop :=
  exists s, TaggedDFA.run M s = q.

Definition reachable_dfa (M : TaggedDFA.t) : Prop :=
  TaggedDFA.okay M /\ (forall q, q ∈ M.(TaggedDFA.states) -> reachable_state M q).

Definition candidate_for_same_language (M N : TaggedDFA.t) : Prop :=
  forall s, forall tag, TaggedDFA.accepts M s tag <-> TaggedDFA.accepts N s tag.

Definition pair_state (M : TaggedDFA.t) : Set :=
  (M.(TaggedDFA.state) * M.(TaggedDFA.state))%type.

Definition pair_states (M : TaggedDFA.t) : list (pair_state M) :=
  product M.(TaggedDFA.states) M.(TaggedDFA.states).

Definition pair_successors (M : TaggedDFA.t) (p : pair_state M) : list (pair_state M) :=
  map (fun c => (M.(TaggedDFA.step) (fst p) c, M.(TaggedDFA.step) (snd p) c)) all_asciis.

Definition pair_graph (M : TaggedDFA.t) : ENFA.t :=
  ENFA.mk (pair_state M) (pair_hasEqdec M.(TaggedDFA.state_hasEqDec) M.(TaggedDFA.state_hasEqDec)) (pair_states M) (M.(TaggedDFA.start_state), M.(TaggedDFA.start_state)) [] (pair_successors M) (fun _ _ => []).

Definition tag_diffb (M : TaggedDFA.t) (p : pair_state M) : bool :=
  if @eq_dec (option Token.t) (@option_hasEqDec Token.t Token.t_hasEqDec) (M.(TaggedDFA.accept_tag) (fst p)) (M.(TaggedDFA.accept_tag) (snd p)) then
    false
  else
    true.

Definition distinguishableb (M : TaggedDFA.t) (q1 : M.(TaggedDFA.state)) (q2 : M.(TaggedDFA.state)) : bool :=
  existsb (tag_diffb M) (Subset.eclose (pair_graph M) [(q1, q2)]).

Lemma tag_diffb_sound (M : TaggedDFA.t) (p : pair_state M)
  (DIFF : tag_diffb M p = true)
  : M.(TaggedDFA.accept_tag) (fst p) <> M.(TaggedDFA.accept_tag) (snd p).
Proof.
  unfold tag_diffb in DIFF.
  destruct (@eq_dec (option Token.t) (@option_hasEqDec Token.t Token.t_hasEqDec) (M.(TaggedDFA.accept_tag) (fst p)) (M.(TaggedDFA.accept_tag) (snd p))) as [EQ | NE].
  - discriminate.
  - exact NE.
Qed.

Lemma tag_diffb_complete (M : TaggedDFA.t) (p : pair_state M)
  (DIFF : M.(TaggedDFA.accept_tag) (fst p) <> M.(TaggedDFA.accept_tag) (snd p))
  : tag_diffb M p = true.
Proof.
  unfold tag_diffb.
  destruct (@eq_dec (option Token.t) (@option_hasEqDec Token.t Token.t_hasEqDec) (M.(TaggedDFA.accept_tag) (fst p)) (M.(TaggedDFA.accept_tag) (snd p))) as [EQ | NE].
  - contradiction.
  - reflexivity.
Qed.

Lemma pair_graph_wf (M : TaggedDFA.t)
  (OKAY : TaggedDFA.okay M)
  : ENFA.wf (pair_graph M).
Proof.
  destruct OKAY as [START_OK STEP_OK].
  unfold pair_graph. simpl. repeat split.
  - eapply product_complete; exact START_OK.
  - intros q IN. contradiction.
  - intros p p' IN_STATES IN_STEP.
    change (p ∈ pair_states M) in IN_STATES.
    destruct p as [p1 p2]. simpl in *.
    pose proof (product_sound M.(TaggedDFA.states) M.(TaggedDFA.states)
      p1 p2 IN_STATES) as [IN1 IN2].
    change (p' ∈ pair_successors M (p1, p2)) in IN_STEP.
    unfold pair_successors in IN_STEP. rewrite in_map_iff in IN_STEP.
    destruct IN_STEP as (c & EQ & _). subst p'.
    eapply product_complete.
    + eapply (STEP_OK p1 (M.(TaggedDFA.step) p1 c) c).
      * exact IN1.
      * reflexivity.
    + eapply (STEP_OK p2 (M.(TaggedDFA.step) p2 c) c).
      * exact IN2.
      * reflexivity.
  - intros p p' c IN_STATES IN_STEP. contradiction.
Qed.

Lemma pair_graph_reachable_sound_pair (M : TaggedDFA.t) (p1 : pair_state M) (p2 : pair_state M)
  (REACH : ENFA.reachable (pair_graph M) p1 [] p2)
  : exists s, TaggedDFA.run_from M (fst p1) s = fst p2 /\ TaggedDFA.run_from M (snd p1) s = snd p2.
Proof.
  remember (@nil ascii) as input eqn: EQ.
  induction REACH as [p | p1 p2 p3 s STEP REST IH | p1 p2 p3 c s STEP REST IH]; inv EQ.
  - exists []. split; reflexivity.
  - change (p2 ∈ pair_successors M p1) in STEP.
    unfold pair_successors in STEP. rewrite in_map_iff in STEP.
    destruct STEP as (c & EQ_PAIR & _). subst p2.
    destruct p1 as [r1 r2]. simpl in *.
    pose proof (IH eq_refl) as (s0 & RUN1 & RUN2).
    exists (c :: s0). simpl. split; [exact RUN1 | exact RUN2].
Qed.

Lemma pair_graph_reachable_sound (M : TaggedDFA.t) (q1 : M.(TaggedDFA.state)) (q2 : M.(TaggedDFA.state)) (q1' : M.(TaggedDFA.state)) (q2' : M.(TaggedDFA.state))
  (REACH : ENFA.reachable (pair_graph M) (q1, q2) [] (q1', q2'))
  : exists s, TaggedDFA.run_from M q1 s = q1' /\ TaggedDFA.run_from M q2 s = q2'.
Proof.
  pose proof (pair_graph_reachable_sound_pair M (q1, q2) (q1', q2') REACH) as (s & RUN1 & RUN2).
  exists s. simpl in RUN1, RUN2. split; assumption.
Qed.

Lemma pair_graph_reachable_complete (M : TaggedDFA.t) (q1 : M.(TaggedDFA.state)) (q2 : M.(TaggedDFA.state)) (s : Input.t)
  : ENFA.reachable (pair_graph M) (q1, q2) [] (TaggedDFA.run_from M q1 s, TaggedDFA.run_from M q2 s).
Proof.
  revert q1 q2. induction s as [ | c s IH]; simpl; intros q1 q2.
  - eapply ENFA.reachable_nil.
  - eapply ENFA.reachable_eps with (q2 := (M.(TaggedDFA.step) q1 c, M.(TaggedDFA.step) q2 c)).
    + change ((M.(TaggedDFA.step) q1 c, M.(TaggedDFA.step) q2 c) ∈ pair_successors M (q1, q2)).
      unfold pair_successors. rewrite in_map_iff.
      exists c. split; [reflexivity | eapply all_asciis_complete].
    + eapply IH.
Qed.

Theorem distinguishableb_sound (M : TaggedDFA.t) (q1 : M.(TaggedDFA.state)) (q2 : M.(TaggedDFA.state))
  (DIST : distinguishableb M q1 q2 = true)
  : distinguishable M q1 q2.
Proof.
  unfold distinguishableb in DIST.
  rewrite existsb_exists in DIST.
  destruct DIST as ([q1' q2'] & IN_CLOSE & DIFF).
  pose proof (Subset.eclose_sound (pair_graph M) [(q1, q2)] (q1', q2') IN_CLOSE) as (p0 & IN_SEED & REACH).
  destruct IN_SEED as [EQ | []]. inv EQ.
  pose proof (pair_graph_reachable_sound M q1 q2 q1' q2' REACH) as (s & RUN1 & RUN2).
  exists s. unfold accepted_from.
  rewrite RUN1, RUN2.
  pose proof (tag_diffb_sound M (q1', q2') DIFF) as NE.
  simpl in NE. exact NE.
Qed.

Theorem distinguishableb_complete (M : TaggedDFA.t) (q1 : M.(TaggedDFA.state)) (q2 : M.(TaggedDFA.state))
  (OKAY : TaggedDFA.okay M)
  (IN1 : q1 ∈ M.(TaggedDFA.states))
  (IN2 : q2 ∈ M.(TaggedDFA.states))
  (DIST : distinguishable M q1 q2)
  : distinguishableb M q1 q2 = true.
Proof.
  destruct DIST as (s & DIST).
  unfold distinguishableb.
  rewrite existsb_exists.
  exists (TaggedDFA.run_from M q1 s, TaggedDFA.run_from M q2 s).
  split.
  - assert (QS : Subset.subset_of_states (pair_graph M) [(q1, q2)]).
    { intros p IN. destruct IN as [EQ | []]. subst p.
      eapply product_complete; eauto.
    }
    pose proof (Subset.eclose_complete (pair_graph M) [(q1, q2)] (q1, q2) (TaggedDFA.run_from M q1 s, TaggedDFA.run_from M q2 s) (pair_graph_wf M OKAY) QS (or_introl eq_refl) (pair_graph_reachable_complete M q1 q2 s)) as IN_CLOSE.
    exact IN_CLOSE.
  - unfold accepted_from in DIST.
    eapply tag_diffb_complete.
    exact DIST.
Qed.

Theorem distinguishableb_iff (M : TaggedDFA.t) (q1 : M.(TaggedDFA.state)) (q2 : M.(TaggedDFA.state))
  (OKAY : TaggedDFA.okay M)
  (IN1 : q1 ∈ M.(TaggedDFA.states))
  (IN2 : q2 ∈ M.(TaggedDFA.states))
  : distinguishableb M q1 q2 = true <-> distinguishable M q1 q2.
Proof.
  split.
  - eapply distinguishableb_sound.
  - eapply distinguishableb_complete; eauto.
Qed.

Definition same_block (M : TaggedDFA.t) (q1 : M.(TaggedDFA.state)) (q2 : M.(TaggedDFA.state)) : Prop :=
  distinguishableb M q1 q2 = false.

Definition partition_stable (M : TaggedDFA.t) : Prop :=
  forall q1, forall q2, forall c, q1 ∈ M.(TaggedDFA.states) -> q2 ∈ M.(TaggedDFA.states) -> same_block M q1 q2 -> same_block M (M.(TaggedDFA.step) q1 c) (M.(TaggedDFA.step) q2 c).

Theorem same_block_language_equiv (M : TaggedDFA.t) (q1 : M.(TaggedDFA.state)) (q2 : M.(TaggedDFA.state))
  (SAME : same_block M q1 q2)
  (OKAY : TaggedDFA.okay M)
  (IN1 : q1 ∈ M.(TaggedDFA.states))
  (IN2 : q2 ∈ M.(TaggedDFA.states))
  : same_future_tag M q1 q2.
Proof.
  unfold same_future_tag. intros s.
  destruct (@eq_dec (option Token.t) (@option_hasEqDec Token.t Token.t_hasEqDec)
    (accepted_from M q1 s) (accepted_from M q2 s)) as [EQ | NE].
  - exact EQ.
  - exfalso.
    assert (DIST : distinguishable M q1 q2).
    { exists s. exact NE. }
    pose proof (distinguishableb_complete M q1 q2 OKAY IN1 IN2 DIST) as YES.
    unfold same_block in SAME. congruence.
Qed.

Theorem same_block_partition_stable (M : TaggedDFA.t)
  (OKAY : TaggedDFA.okay M)
  : partition_stable M.
Proof.
  intros q1 q2 c IN1 IN2 SAME.
  unfold same_block.
  destruct (distinguishableb M (M.(TaggedDFA.step) q1 c)
    (M.(TaggedDFA.step) q2 c)) eqn: DIST; [ | reflexivity].
  pose proof (distinguishableb_sound M (M.(TaggedDFA.step) q1 c)
    (M.(TaggedDFA.step) q2 c) DIST) as (s & NE).
  pose proof (same_block_language_equiv M q1 q2 SAME OKAY IN1 IN2 (c :: s)) as EQ.
  unfold accepted_from in EQ, NE. simpl in EQ. contradiction.
Qed.

Definition block_of (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) : list M.(TaggedDFA.state) :=
  filter (fun q' => negb (distinguishableb M q q')) M.(TaggedDFA.states).

Definition blocks (M : TaggedDFA.t) : list (list M.(TaggedDFA.state)) :=
  nodup (@eq_dec (list M.(TaggedDFA.state)) (list_hasEqDec M.(TaggedDFA.state_hasEqDec))) (map (block_of M) M.(TaggedDFA.states)).

Definition representative (M : TaggedDFA.t) (B : list M.(TaggedDFA.state)) : M.(TaggedDFA.state) :=
  match B with
  | [] => M.(TaggedDFA.start_state)
  | q :: _ => q
  end.

Definition minimize (M : TaggedDFA.t) : TaggedDFA.t :=
  TaggedDFA.mk (list M.(TaggedDFA.state)) (list_hasEqDec M.(TaggedDFA.state_hasEqDec)) (blocks M) (block_of M M.(TaggedDFA.start_state)) (fun B => fun c => block_of M (M.(TaggedDFA.step) (representative M B) c)) (fun B => M.(TaggedDFA.accept_tag) (representative M B)).

Lemma distinguishableb_refl_false (M : TaggedDFA.t) (q : M.(TaggedDFA.state))
  : distinguishableb M q q = false.
Proof.
  destruct (distinguishableb M q q) eqn: DIST; [ | reflexivity].
  pose proof (distinguishableb_sound M q q DIST) as (s & CONTRA).
  unfold accepted_from in CONTRA. contradiction.
Qed.

Lemma block_of_sound (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) (r : M.(TaggedDFA.state))
  (IN : r ∈ block_of M q)
  : r ∈ M.(TaggedDFA.states) /\ distinguishableb M q r = false.
Proof.
  unfold block_of in IN. rewrite filter_In in IN.
  destruct IN as [IN_STATES SAME].
  rewrite negb_true_iff in SAME.
  split; [exact IN_STATES | exact SAME].
Qed.

Lemma block_of_contains_self (M : TaggedDFA.t) (q : M.(TaggedDFA.state))
  (IN : q ∈ M.(TaggedDFA.states))
  : q ∈ block_of M q.
Proof.
  unfold block_of. rewrite filter_In. split; [exact IN | ].
  rewrite negb_true_iff. eapply distinguishableb_refl_false.
Qed.

Lemma block_of_in_blocks (M : TaggedDFA.t) (q : M.(TaggedDFA.state))
  (IN : q ∈ M.(TaggedDFA.states))
  : block_of M q ∈ blocks M.
Proof.
  unfold blocks. rewrite L.nodup_In. rewrite in_map_iff.
  exists q. split; [reflexivity | exact IN].
Qed.

Lemma representative_block_of_in_states (M : TaggedDFA.t) (q : M.(TaggedDFA.state))
  (IN : q ∈ M.(TaggedDFA.states))
  : representative M (block_of M q) ∈ M.(TaggedDFA.states).
Proof.
  pose proof (block_of_contains_self M q IN) as IN_BLOCK.
  destruct (block_of M q) as [ | r rs] eqn: BLOCK.
  - contradiction.
  - pose proof (block_of_sound M q r) as SOUND.
    simpl. eapply SOUND. rewrite BLOCK. left. reflexivity.
Qed.

Lemma representative_in_states (M : TaggedDFA.t) (B : list M.(TaggedDFA.state))
  (IN : B ∈ blocks M)
  : representative M B ∈ M.(TaggedDFA.states).
Proof.
  unfold blocks in IN. rewrite L.nodup_In in IN.
  rewrite in_map_iff in IN.
  destruct IN as (q & EQ & IN_Q). subst B.
  eapply representative_block_of_in_states. exact IN_Q.
Qed.

Lemma representative_block_of_in_block (M : TaggedDFA.t) (q : M.(TaggedDFA.state))
  (IN : q ∈ M.(TaggedDFA.states))
  : representative M (block_of M q) ∈ block_of M q.
Proof.
  pose proof (block_of_contains_self M q IN) as IN_BLOCK.
  destruct (block_of M q) as [ | r rs] eqn: BLOCK.
  - contradiction.
  - simpl. left. reflexivity.
Qed.

Lemma block_of_language_equiv (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) (r : M.(TaggedDFA.state))
  (OKAY : TaggedDFA.okay M)
  (IN_Q : q ∈ M.(TaggedDFA.states))
  (IN_BLOCK : r ∈ block_of M q)
  : same_future_tag M q r.
Proof.
  pose proof (block_of_sound M q r IN_BLOCK) as [IN_R SAME].
  unfold same_future_tag. intros s.
  destruct (@eq_dec (option Token.t) (@option_hasEqDec Token.t Token.t_hasEqDec) (accepted_from M q s) (accepted_from M r s)) as [EQ | NE].
  - exact EQ.
  - exfalso.
    assert (DIST : distinguishable M q r).
    { exists s. exact NE. }
    pose proof (distinguishableb_complete M q r OKAY IN_Q IN_R DIST) as YES.
    congruence.
Qed.

Lemma representative_block_of_language_equiv (M : TaggedDFA.t) (q : M.(TaggedDFA.state))
  (OKAY : TaggedDFA.okay M)
  (IN : q ∈ M.(TaggedDFA.states))
  : same_future_tag M q (representative M (block_of M q)).
Proof.
  eapply block_of_language_equiv; eauto.
  eapply representative_block_of_in_block. exact IN.
Qed.

Theorem minimize_okay (M : TaggedDFA.t)
  (OKAY : TaggedDFA.okay M)
  : TaggedDFA.okay (minimize M).
Proof.
  destruct OKAY as [START_OK STEP_OK].
  unfold TaggedDFA.okay, minimize. simpl.
  split.
  - eapply block_of_in_blocks. exact START_OK.
  - intros B B' c IN_B STEP_EQ. subst B'.
    eapply block_of_in_blocks.
    eapply STEP_OK.
    + eapply representative_in_states. exact IN_B.
    + reflexivity.
Qed.

Theorem minimize_accepted_from (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) (s : Input.t)
  (OKAY : TaggedDFA.okay M)
  (IN : q ∈ M.(TaggedDFA.states))
  : accepted_from (minimize M) (block_of M q) s = accepted_from M q s.
Proof.
  revert q IN. induction s as [ | c s IH]; intros q IN.
  - unfold accepted_from. simpl.
    pose proof (representative_block_of_language_equiv M q OKAY IN []) as EQ.
    unfold accepted_from in EQ. simpl in EQ. symmetry. exact EQ.
  - unfold accepted_from at 1. simpl.
    fold (accepted_from (minimize M) (block_of M (M.(TaggedDFA.step) (representative M (block_of M q)) c)) s).
    assert (IN_REP : representative M (block_of M q) ∈ M.(TaggedDFA.states)).
    { eapply representative_block_of_in_states. exact IN. }
    assert (IN_STEP : M.(TaggedDFA.step) (representative M (block_of M q)) c ∈ M.(TaggedDFA.states)).
    { destruct OKAY as [_ STEP_OK].
      eapply STEP_OK; [exact IN_REP | reflexivity].
    }
    change (accepted_from (minimize M) (block_of M (M.(TaggedDFA.step) (representative M (block_of M q)) c)) s = accepted_from M q (c :: s)).
    rewrite (IH (M.(TaggedDFA.step) (representative M (block_of M q)) c) IN_STEP).
    pose proof (representative_block_of_language_equiv M q OKAY IN (c :: s)) as EQ.
    unfold accepted_from in EQ. simpl in EQ. symmetry. exact EQ.
Qed.

Theorem minimize_tag_preserving (M : TaggedDFA.t) (s : Input.t)
  (OKAY : TaggedDFA.okay M)
  : TaggedDFA.accepted_tag (minimize M) s = TaggedDFA.accepted_tag M s.
Proof.
  unfold TaggedDFA.accepted_tag, TaggedDFA.run.
  destruct OKAY as [START_OK STEP_OK].
  eapply (minimize_accepted_from M M.(TaggedDFA.start_state) s (conj START_OK STEP_OK) START_OK).
Qed.

Theorem minimize_accepts_iff (M : TaggedDFA.t) (s : Input.t) (tag : Token.t)
  (OKAY : TaggedDFA.okay M)
  : TaggedDFA.accepts (minimize M) s tag <-> TaggedDFA.accepts M s tag.
Proof.
  unfold TaggedDFA.accepts.
  rewrite minimize_tag_preserving; [reflexivity | exact OKAY].
Qed.

Lemma distinguishable_respects_same_future_l (M : TaggedDFA.t) (q1 : M.(TaggedDFA.state)) (q2 : M.(TaggedDFA.state)) (r : M.(TaggedDFA.state))
  (EQUIV : same_future_tag M q1 q2)
  (DIST : distinguishable M q1 r)
  : distinguishable M q2 r.
Proof.
  destruct DIST as (s & NE).
  exists s. intros EQ.
  eapply NE. rewrite EQUIV. exact EQ.
Qed.

Lemma distinguishableb_eq_of_same_future (M : TaggedDFA.t) (q1 : M.(TaggedDFA.state)) (q2 : M.(TaggedDFA.state)) (r : M.(TaggedDFA.state))
  (OKAY : TaggedDFA.okay M)
  (IN1 : q1 ∈ M.(TaggedDFA.states))
  (IN2 : q2 ∈ M.(TaggedDFA.states))
  (IN_R : r ∈ M.(TaggedDFA.states))
  (EQUIV : same_future_tag M q1 q2)
  : distinguishableb M q1 r = distinguishableb M q2 r.
Proof.
  destruct (distinguishableb M q1 r) eqn: DIST1, (distinguishableb M q2 r) eqn: DIST2; try reflexivity.
  - pose proof (distinguishableb_sound M q1 r DIST1) as DIST.
    pose proof (distinguishable_respects_same_future_l M q1 q2 r EQUIV DIST) as DIST'.
    pose proof (distinguishableb_complete M q2 r OKAY IN2 IN_R DIST') as YES.
    congruence.
  - pose proof (distinguishableb_sound M q2 r DIST2) as DIST.
    assert (EQUIV_SYM : same_future_tag M q2 q1).
    { intros s. symmetry. eapply EQUIV. }
    pose proof (distinguishable_respects_same_future_l M q2 q1 r EQUIV_SYM DIST) as DIST'.
    pose proof (distinguishableb_complete M q1 r OKAY IN1 IN_R DIST') as YES.
    congruence.
Qed.

Lemma block_of_ext (M : TaggedDFA.t) (q1 : M.(TaggedDFA.state)) (q2 : M.(TaggedDFA.state))
  (OKAY : TaggedDFA.okay M)
  (IN1 : q1 ∈ M.(TaggedDFA.states))
  (IN2 : q2 ∈ M.(TaggedDFA.states))
  (EQUIV : same_future_tag M q1 q2)
  : block_of M q1 = block_of M q2.
Proof.
  unfold block_of.
  eapply L.filter_ext_in. intros r IN_R.
  rewrite (distinguishableb_eq_of_same_future M q1 q2 r OKAY IN1 IN2 IN_R EQUIV).
  reflexivity.
Qed.

Lemma block_of_representative (M : TaggedDFA.t) (B : list M.(TaggedDFA.state))
  (OKAY : TaggedDFA.okay M)
  (IN : B ∈ blocks M)
  : block_of M (representative M B) = B.
Proof.
  unfold blocks in IN. rewrite L.nodup_In in IN.
  rewrite in_map_iff in IN.
  destruct IN as (q & EQ & IN_Q). subst B.
  pose proof (representative_block_of_language_equiv M q OKAY IN_Q) as EQUIV.
  pose proof (representative_block_of_in_states M q IN_Q) as IN_REP.
  symmetry. eapply block_of_ext; eauto.
Qed.

Lemma minimized_block_accepted_from (M : TaggedDFA.t) (B : list M.(TaggedDFA.state)) (s : Input.t)
  (OKAY : TaggedDFA.okay M)
  (IN : B ∈ blocks M)
  : accepted_from (minimize M) B s = accepted_from M (representative M B) s.
Proof.
  unfold blocks in IN. rewrite L.nodup_In in IN.
  rewrite in_map_iff in IN.
  destruct IN as (q & EQ & IN_Q). subst B.
  rewrite minimize_accepted_from; eauto.
  pose proof (representative_block_of_language_equiv M q OKAY IN_Q s) as EQUIV.
  exact EQUIV.
Qed.

Theorem minimize_distinguishes_blocks (M : TaggedDFA.t) (B1 : list M.(TaggedDFA.state)) (B2 : list M.(TaggedDFA.state))
  (OKAY : TaggedDFA.okay M)
  (IN1 : B1 ∈ blocks M)
  (IN2 : B2 ∈ blocks M)
  (NE : ~ B1 = B2)
  : distinguishable (minimize M) B1 B2.
Proof.
  pose proof (representative_in_states M B1 IN1) as REP1_IN.
  pose proof (representative_in_states M B2 IN2) as REP2_IN.
  destruct (distinguishableb M (representative M B1) (representative M B2)) eqn: DIST.
  - pose proof (distinguishableb_sound M (representative M B1) (representative M B2) DIST) as (s & DIST_S).
    exists s.
    rewrite !minimized_block_accepted_from; eauto.
  - exfalso.
    assert (SAME : same_block M (representative M B1) (representative M B2)).
    { exact DIST. }
    pose proof (same_block_language_equiv M (representative M B1) (representative M B2) SAME OKAY REP1_IN REP2_IN) as EQUIV.
    pose proof (block_of_ext M (representative M B1) (representative M B2) OKAY REP1_IN REP2_IN EQUIV) as BLOCK_EQ.
    rewrite (block_of_representative M B1 OKAY IN1) in BLOCK_EQ.
    rewrite (block_of_representative M B2 OKAY IN2) in BLOCK_EQ.
    contradiction.
Qed.

Lemma candidate_accepted_tag_eq (M : TaggedDFA.t) (N : TaggedDFA.t) (s : Input.t)
  (SAME : candidate_for_same_language M N)
  : TaggedDFA.accepted_tag M s = TaggedDFA.accepted_tag N s.
Proof.
  unfold candidate_for_same_language in SAME.
  destruct (TaggedDFA.accepted_tag M s) as [tagM | ] eqn: ACCEPT_M; destruct (TaggedDFA.accepted_tag N s) as [tagN | ] eqn: ACCEPT_N; try reflexivity.
  - assert (ACCEPT_N_M : TaggedDFA.accepts N s tagM).
    { eapply (proj1 (SAME s tagM)). exact ACCEPT_M. }
    unfold TaggedDFA.accepts in ACCEPT_N_M.
    rewrite ACCEPT_N in ACCEPT_N_M. inv ACCEPT_N_M. reflexivity.
  - assert (ACCEPT_N_M : TaggedDFA.accepts N s tagM).
    { eapply (proj1 (SAME s tagM)). exact ACCEPT_M. }
    unfold TaggedDFA.accepts in ACCEPT_N_M.
    rewrite ACCEPT_N in ACCEPT_N_M. discriminate.
  - assert (ACCEPT_M_N : TaggedDFA.accepts M s tagN).
    { eapply (proj2 (SAME s tagN)). exact ACCEPT_N. }
    unfold TaggedDFA.accepts in ACCEPT_M_N.
    rewrite ACCEPT_M in ACCEPT_M_N. discriminate.
Qed.

Theorem minimize_minimal (M : TaggedDFA.t) (N : TaggedDFA.t) (reach_word : M.(TaggedDFA.state) -> Input.t)
  (M_OKAY : TaggedDFA.okay M)
  (N_OKAY : TaggedDFA.okay N)
  (REACH_WORD : forall q, q ∈ M.(TaggedDFA.states) -> TaggedDFA.run M (reach_word q) = q)
  (SAME : candidate_for_same_language M N)
  : state_cardinality (minimize M) <= state_cardinality N.
Proof.
  set (image := map (fun B => TaggedDFA.run N (reach_word (representative M B))) (blocks M)).
  assert (NO_DUP_BLOCKS : NoDup (blocks M)).
  { unfold blocks. eapply NoDup_nodup. }
  assert (NO_DUP_IMAGE : NoDup image).
  { subst image. eapply NoDup_map_injective_on.
    - intros B1 B2 IN1 IN2 RUN_EQ.
      destruct (@eq_dec (list M.(TaggedDFA.state)) (list_hasEqDec M.(TaggedDFA.state_hasEqDec)) B1 B2) as [EQ | NE]; [exact EQ | exfalso].
      pose proof (representative_in_states M B1 IN1) as REP1_IN.
      pose proof (representative_in_states M B2 IN2) as REP2_IN.
      pose proof (minimize_distinguishes_blocks M B1 B2 M_OKAY IN1 IN2 NE) as (s & DIST).
      assert (TAG_M1 : TaggedDFA.accepted_tag M (reach_word (representative M B1) ++ s) = accepted_from M (representative M B1) s).
      { unfold TaggedDFA.accepted_tag, TaggedDFA.run, accepted_from.
        rewrite TaggedDFA.run_from_app.
        fold (TaggedDFA.run M (reach_word (representative M B1))).
        rewrite REACH_WORD; [reflexivity | exact REP1_IN].
      }
      assert (TAG_M2 : TaggedDFA.accepted_tag M (reach_word (representative M B2) ++ s) = accepted_from M (representative M B2) s).
      { unfold TaggedDFA.accepted_tag, TaggedDFA.run, accepted_from.
        rewrite TaggedDFA.run_from_app.
        fold (TaggedDFA.run M (reach_word (representative M B2))).
        rewrite REACH_WORD; [reflexivity | exact REP2_IN].
      }
      assert (TAG_N : TaggedDFA.accepted_tag N (reach_word (representative M B1) ++ s) = TaggedDFA.accepted_tag N (reach_word (representative M B2) ++ s)).
      { unfold TaggedDFA.accepted_tag, TaggedDFA.run.
        rewrite !TaggedDFA.run_from_app.
        fold (TaggedDFA.run N (reach_word (representative M B1))).
        fold (TaggedDFA.run N (reach_word (representative M B2))).
        rewrite RUN_EQ. reflexivity.
      }
      eapply DIST.
      rewrite !minimized_block_accepted_from; eauto.
      rewrite <- TAG_M1. rewrite <- TAG_M2.
      rewrite (candidate_accepted_tag_eq M N (reach_word (representative M B1) ++ s) SAME).
      rewrite (candidate_accepted_tag_eq M N (reach_word (representative M B2) ++ s) SAME).
      exact TAG_N.
    - exact NO_DUP_BLOCKS.
  }
  assert (IMAGE_IN_STATES : forall q, q ∈ image -> q ∈ nodup eq_dec N.(TaggedDFA.states)).
  { intros q IN. subst image. rewrite in_map_iff in IN.
    destruct IN as (B & EQ & IN_B). subst q.
    rewrite nodup_In.
    eapply TaggedDFA.run_okay. exact N_OKAY.
  }
  unfold state_cardinality. simpl.
  set (block_eq_dec := @eq_dec (list M.(TaggedDFA.state)) (list_hasEqDec M.(TaggedDFA.state_hasEqDec))).
  change (length (nodup block_eq_dec (blocks M)) <= length (nodup eq_dec N.(TaggedDFA.states))).
  assert (BLOCKS_LEN : length (nodup block_eq_dec (blocks M)) = length (blocks M)).
  { apply Nat.le_antisymm.
    - eapply NoDup_incl_length.
      + eapply NoDup_nodup.
      + intros B IN. rewrite nodup_In in IN. exact IN.
    - eapply NoDup_incl_length.
      + exact NO_DUP_BLOCKS.
      + intros B IN. rewrite nodup_In. exact IN.
  }
  rewrite BLOCKS_LEN.
  rewrite <- (length_map (fun B =>
    TaggedDFA.run N (reach_word (representative M B))) (blocks M)).
  eapply NoDup_incl_length.
  - exact NO_DUP_IMAGE.
  - intros q IN. eapply IMAGE_IN_STATES. exact IN.
Qed.

End TaggedMinimize.

Module PartialTaggedDFA.

#[projections(primitive)]
Record t : Type :=
  mk
  { state : Set
  ; state_hasEqDec : hasEqDec@{Set} state
  ; states : list state
  ; start_state : state
  ; step : state -> ascii -> option state
  ; accept_tag : state -> option Token.t
  }.

#[global] Existing Instance state_hasEqDec.

Fixpoint run_from (M : t) (q : M.(state)) (s : Input.t) {struct s}: option M.(state) :=
  match s with
  | [] => Some q
  | c :: s' =>
    match M.(step) q c with
    | Some q' => run_from M q' s'
    | None => None
    end
  end.

Definition run (M : t) (s : Input.t) : option M.(state) :=
  run_from M M.(start_state) s.

Definition accepted_tag (M : t) (s : Input.t) : option Token.t :=
  match run M s with
  | Some q => M.(accept_tag) q
  | None => None
  end.

Definition accepts (M : t) (s : Input.t) (tag : Token.t) : Prop :=
  accepted_tag M s = Some tag.

Definition accepted_from (M : t) (q : M.(state)) (s : Input.t) : option Token.t :=
  match run_from M q s with
  | Some q' => M.(accept_tag) q'
  | None => None
  end.

Definition okay (M : t) : Prop :=
  M.(start_state) ∈ M.(states) /\ (forall q, forall q', forall c, q ∈ M.(states) -> M.(step) q c = Some q' -> q' ∈ M.(states)).

Theorem run_from_app (M : t) (q : M.(state)) (s1 : Input.t) (s2 : Input.t)
  : run_from M q (s1 ++ s2) = match run_from M q s1 with | Some q' => run_from M q' s2 | None => None end.
Proof.
  revert q. induction s1 as [ | c s1 IH]; simpl; intros q.
  - reflexivity.
  - destruct (M.(step) q c) as [q' | ]; [eapply IH | reflexivity].
Qed.

End PartialTaggedDFA.

Module DeadStateDeletion.

Definition is_dead_state (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) : Prop :=
  M.(TaggedDFA.accept_tag) q = None /\ (forall c, M.(TaggedDFA.step) q c = q).

Definition delete_dead_state_with (M : TaggedDFA.t) (dead : M.(TaggedDFA.state)) : PartialTaggedDFA.t :=
  PartialTaggedDFA.mk M.(TaggedDFA.state) M.(TaggedDFA.state_hasEqDec) (remove eq_dec dead M.(TaggedDFA.states)) M.(TaggedDFA.start_state) (fun q => fun c => let q' := M.(TaggedDFA.step) q c in if eq_dec q' dead then None else Some q') M.(TaggedDFA.accept_tag).

Definition of_total (M : TaggedDFA.t) : PartialTaggedDFA.t :=
  PartialTaggedDFA.mk M.(TaggedDFA.state) M.(TaggedDFA.state_hasEqDec) M.(TaggedDFA.states) M.(TaggedDFA.start_state) (fun q => fun c => Some (M.(TaggedDFA.step) q c)) M.(TaggedDFA.accept_tag).

Lemma dead_accepted_from_none (M : TaggedDFA.t) (dead : M.(TaggedDFA.state)) (s : Input.t)
  (DEAD : is_dead_state M dead)
  : TaggedMinimize.accepted_from M dead s = None.
Proof.
  destruct DEAD as [ACCEPT STEP].
  induction s as [ | c s IH]; simpl.
  - exact ACCEPT.
  - unfold TaggedMinimize.accepted_from in *. simpl.
    rewrite STEP. exact IH.
Qed.

Theorem delete_dead_state_run_none_iff_dead (M : TaggedDFA.t) (dead : M.(TaggedDFA.state)) (q : M.(TaggedDFA.state)) (c : ascii)
  (DEAD : is_dead_state M dead)
  : PartialTaggedDFA.step (delete_dead_state_with M dead) q c = None <-> M.(TaggedDFA.step) q c = dead.
Proof.
  simpl. destruct (eq_dec (TaggedDFA.step M q c) dead) as [EQ | NE].
  - split; intros _; [exact EQ | reflexivity].
  - split; intros H.
    + discriminate.
    + contradiction.
Qed.

Theorem delete_dead_state_okay (M : TaggedDFA.t) (dead : M.(TaggedDFA.state))
  (OKAY : TaggedDFA.okay M)
  (START_NOT_DEAD : ~ M.(TaggedDFA.start_state) = dead)
  : PartialTaggedDFA.okay (delete_dead_state_with M dead).
Proof.
  destruct OKAY as [START_OK STEP_OK].
  unfold PartialTaggedDFA.okay, delete_dead_state_with. simpl.
  split.
  - rewrite L.in_remove_iff. split; [exact START_OK | exact START_NOT_DEAD].
  - intros q q' c IN_Q STEP.
    rewrite L.in_remove_iff in IN_Q. destruct IN_Q as [IN_Q NE_Q].
    destruct (eq_dec (M.(TaggedDFA.step) q c) dead) as [EQ | NE].
    + discriminate.
    + inv STEP. rewrite L.in_remove_iff. split.
      * eapply STEP_OK; [exact IN_Q | reflexivity].
      * exact NE.
Qed.

Theorem delete_dead_state_preserves_accepted_from (M : TaggedDFA.t) (dead : M.(TaggedDFA.state)) (q : M.(TaggedDFA.state)) (s : Input.t)
  (DEAD : is_dead_state M dead)
  : match PartialTaggedDFA.run_from (delete_dead_state_with M dead) q s with | Some q' => M.(TaggedDFA.accept_tag) q' | None => None end = TaggedMinimize.accepted_from M q s.
Proof.
  revert q. induction s as [ | c s IH]; intros q; simpl.
  - reflexivity.
  - destruct (eq_dec (M.(TaggedDFA.step) q c) dead) as [EQ | NE].
    + change (None = TaggedMinimize.accepted_from M (M.(TaggedDFA.step) q c) s).
      rewrite EQ. symmetry. eapply dead_accepted_from_none. exact DEAD.
    + eapply IH.
Qed.

Theorem delete_dead_state_preserves_accepted_tag (M : TaggedDFA.t) (dead : M.(TaggedDFA.state)) (s : Input.t)
  (DEAD : is_dead_state M dead)
  : PartialTaggedDFA.accepted_tag (delete_dead_state_with M dead) s = TaggedDFA.accepted_tag M s.
Proof.
  unfold PartialTaggedDFA.accepted_tag, PartialTaggedDFA.run, TaggedDFA.accepted_tag, TaggedDFA.run.
  eapply delete_dead_state_preserves_accepted_from. exact DEAD.
Qed.

Theorem delete_dead_state_exact (M : TaggedDFA.t) (dead : M.(TaggedDFA.state)) (s : Input.t) (tag : Token.t)
  (DEAD : is_dead_state M dead)
  : PartialTaggedDFA.accepts (delete_dead_state_with M dead) s tag <-> TaggedDFA.accepts M s tag.
Proof.
  unfold PartialTaggedDFA.accepts, TaggedDFA.accepts.
  rewrite delete_dead_state_preserves_accepted_tag; [reflexivity | exact DEAD].
Qed.

Lemma of_total_preserves_accepted_from (M : TaggedDFA.t) (q : M.(TaggedDFA.state)) (s : Input.t)
  : match PartialTaggedDFA.run_from (of_total M) q s with | Some q' => M.(TaggedDFA.accept_tag) q' | None => None end = TaggedMinimize.accepted_from M q s.
Proof.
  revert q. induction s as [ | c s IH]; intros q; simpl.
  - reflexivity.
  - eapply IH.
Qed.

Theorem of_total_preserves_accepted_tag (M : TaggedDFA.t) (s : Input.t)
  : PartialTaggedDFA.accepted_tag (of_total M) s = TaggedDFA.accepted_tag M s.
Proof.
  unfold PartialTaggedDFA.accepted_tag, PartialTaggedDFA.run, TaggedDFA.accepted_tag, TaggedDFA.run.
  eapply of_total_preserves_accepted_from.
Qed.

Theorem of_total_okay (M : TaggedDFA.t)
  (OKAY : TaggedDFA.okay M)
  : PartialTaggedDFA.okay (of_total M).
Proof.
  destruct OKAY as [START_OK STEP_OK].
  unfold PartialTaggedDFA.okay, of_total. simpl.
  split; [exact START_OK | ].
  intros q q' c IN_Q STEP. inv STEP.
  eapply STEP_OK; [exact IN_Q | reflexivity].
Qed.

Theorem of_total_exact (M : TaggedDFA.t) (s : Input.t) (tag : Token.t)
  : PartialTaggedDFA.accepts (of_total M) s tag <-> TaggedDFA.accepts M s tag.
Proof.
  unfold PartialTaggedDFA.accepts, TaggedDFA.accepts.
  rewrite of_total_preserves_accepted_tag. reflexivity.
Qed.

End DeadStateDeletion.

Module Scanner.

#[projections(primitive)]
Record scan_result : Set :=
  mkScanResult
  { scan_lexeme : Input.t
  ; scan_token : Token.t
  ; scan_rest : Input.t
  }.

Definition scan_result_split (input : Input.t) (r : scan_result) : Prop :=
  input = r.(scan_lexeme) ++ r.(scan_rest).

Definition scan_result_sound (M : PartialTaggedDFA.t) (r : scan_result) : Prop :=
  PartialTaggedDFA.accepted_from M M.(PartialTaggedDFA.start_state)
    r.(scan_lexeme) = Some r.(scan_token).

Definition opt_scan_split (input : Input.t) (r : option scan_result) : Prop :=
  match r with
  | Some r' => scan_result_split input r'
  | None => True
  end.

Definition opt_scan_sound (M : PartialTaggedDFA.t) (r : option scan_result) : Prop :=
  match r with
  | Some r' => scan_result_sound M r'
  | None => True
  end.

Definition opt_scan_nonempty (r : option scan_result) : Prop :=
  match r with
  | Some r' => r'.(scan_lexeme) <> []
  | None => True
  end.

Definition scan_result_longest (M : PartialTaggedDFA.t) (input : Input.t) (r : scan_result) : Prop :=
  scan_result_split input r /\ (forall prefix, forall suffix, forall tag, input = prefix ++ suffix -> length r.(scan_lexeme) < length prefix -> ~ PartialTaggedDFA.accepted_tag M prefix = Some tag).

Definition opt_scan_seen_longest (M : PartialTaggedDFA.t) (input : Input.t) (consumed : Input.t) (last : option scan_result) : Prop :=
  match last with
  | None => True
  | Some r => scan_result_split input r /\ (forall prefix, forall suffix, forall tag, input = prefix ++ suffix -> length r.(scan_lexeme) < length prefix -> length prefix <= length consumed -> ~ PartialTaggedDFA.accepted_tag M prefix = Some tag)
  end.

Definition opt_scan_longest (M : PartialTaggedDFA.t) (input : Input.t) (r : option scan_result) : Prop :=
  match r with
  | Some r' => scan_result_longest M input r'
  | None => True
  end.

Definition no_accepted_nonempty_prefix (M : PartialTaggedDFA.t) (input : Input.t) : Prop :=
  forall prefix, forall suffix, forall tag, input = prefix ++ suffix -> (~ prefix = []) -> PartialTaggedDFA.accepted_tag M prefix <> Some tag.

Definition no_accepted_prefix_up_to (M : PartialTaggedDFA.t) (input consumed : Input.t) : Prop :=
  forall prefix, forall suffix, forall tag, input = prefix ++ suffix ->(~ prefix = []) ->length prefix <= length consumed ->PartialTaggedDFA.accepted_tag M prefix <> Some tag.

Inductive tokenizable (M : PartialTaggedDFA.t) : Input.t -> Prop :=
  | tokenizable_nil
    : tokenizable M []
  | tokenizable_cons input r
    (SPLIT : scan_result_split input r)
    (SOUND : scan_result_sound M r)
    (NONEMPTY : r.(scan_lexeme) <> [])
    (LONGEST : scan_result_longest M input r)
    (REST : tokenizable M r.(scan_rest))
    : tokenizable M input.

Fixpoint scan_one_loop (M : PartialTaggedDFA.t) (q : M.(PartialTaggedDFA.state)) (consumed : Input.t) (rest : Input.t) (last : option scan_result) {struct rest} : option scan_result :=
  match rest with
  | [] => last
  | c :: rest' =>
    match M.(PartialTaggedDFA.step) q c with
    | None => last
    | Some q' =>
      let consumed' := consumed ++ [c] in
      let last' := match M.(PartialTaggedDFA.accept_tag) q' with | Some tag => Some (mkScanResult consumed' tag rest') | None => last end in
      scan_one_loop M q' consumed' rest' last'
    end
  end.

Definition scan_one_raw (M : PartialTaggedDFA.t) (input : Input.t) : option scan_result :=
  scan_one_loop M M.(PartialTaggedDFA.start_state) [] input None.

Definition scan_one (M : PartialTaggedDFA.t) (input : Input.t) : ErrM scan_result :=
  match scan_one_raw M input with
  | Some r => inr r
  | None => inl (Error.NoMatch input)
  end.

Lemma scan_one_loop_split (M : PartialTaggedDFA.t) (q : M.(PartialTaggedDFA.state)) (input : Input.t) (consumed : Input.t) (rest : Input.t) (last : option scan_result)
  (WHOLE : input = consumed ++ rest)
  (LAST : opt_scan_split input last)
  : opt_scan_split input (scan_one_loop M q consumed rest last).
Proof.
  revert q consumed last WHOLE LAST.
  induction rest as [ | c rest IH]; simpl; intros q consumed last WHOLE LAST.
  - exact LAST.
  - destruct (M.(PartialTaggedDFA.step) q c) as [q' | ] eqn: STEP.
    + eapply IH.
      * rewrite WHOLE. rewrite <- app_assoc. reflexivity.
      * destruct (M.(PartialTaggedDFA.accept_tag) q') as [tag | ]; [ | exact LAST].
        unfold opt_scan_split, scan_result_split. simpl.
        rewrite WHOLE. rewrite <- app_assoc. reflexivity.
    + exact LAST.
Qed.

Theorem scan_one_raw_split (M : PartialTaggedDFA.t) (input : Input.t) (r : scan_result)
  (SCAN : scan_one_raw M input = Some r)
  : scan_result_split input r.
Proof.
  unfold scan_one_raw in SCAN.
  pose proof (scan_one_loop_split M M.(PartialTaggedDFA.start_state) input [] input None eq_refl I) as SPLIT.
  rewrite SCAN in SPLIT. exact SPLIT.
Qed.

Lemma scan_one_loop_sound (M : PartialTaggedDFA.t) (q : M.(PartialTaggedDFA.state)) (input : Input.t) (consumed : Input.t) (rest : Input.t) (last : option scan_result)
  (RUN : PartialTaggedDFA.run_from M M.(PartialTaggedDFA.start_state) consumed = Some q)
  (LAST : opt_scan_sound M last)
  : opt_scan_sound M (scan_one_loop M q consumed rest last).
Proof.
  revert q consumed last RUN LAST.
  induction rest as [ | c rest IH]; simpl; intros q consumed last RUN LAST.
  - exact LAST.
  - destruct (M.(PartialTaggedDFA.step) q c) as [q' | ] eqn: STEP.
    + eapply IH.
      * rewrite PartialTaggedDFA.run_from_app.
        rewrite RUN. simpl. rewrite STEP. reflexivity.
      * destruct (M.(PartialTaggedDFA.accept_tag) q') as [tag | ] eqn: ACCEPT; [ | exact LAST].
        unfold opt_scan_sound, scan_result_sound, PartialTaggedDFA.accepted_from.
        simpl. rewrite PartialTaggedDFA.run_from_app.
        rewrite RUN. simpl. rewrite STEP. simpl. exact ACCEPT.
    + exact LAST.
Qed.

Theorem scan_one_raw_sound (M : PartialTaggedDFA.t) (input : Input.t) (r : scan_result)
  (SCAN : scan_one_raw M input = Some r)
  : scan_result_sound M r.
Proof.
  unfold scan_one_raw in SCAN.
  pose proof (scan_one_loop_sound M M.(PartialTaggedDFA.start_state) input [] input None eq_refl I) as SOUND.
  rewrite SCAN in SOUND. exact SOUND.
Qed.

Theorem scan_one_sound (M : PartialTaggedDFA.t) (input : Input.t) (r : scan_result)
  (SCAN : scan_one M input = inr r)
  : scan_result_sound M r.
Proof.
  unfold scan_one in SCAN.
  destruct (scan_one_raw M input) as [r0 | ] eqn: RAW; try discriminate.
  inv SCAN. eapply scan_one_raw_sound. exact RAW.
Qed.

Lemma scan_one_loop_nonempty (M : PartialTaggedDFA.t) (q : M.(PartialTaggedDFA.state)) (consumed : Input.t) (rest : Input.t) (last : option scan_result)
  (LAST : opt_scan_nonempty last)
  : opt_scan_nonempty (scan_one_loop M q consumed rest last).
Proof.
  revert q consumed last LAST.
  induction rest as [ | c rest IH]; simpl; intros q consumed last LAST.
  - exact LAST.
  - destruct (M.(PartialTaggedDFA.step) q c) as [q' | ] eqn: STEP.
    + eapply IH.
      destruct (M.(PartialTaggedDFA.accept_tag) q') as [tag | ]; [ | exact LAST].
      unfold opt_scan_nonempty. simpl.
      destruct consumed as [ | c0 consumed]; discriminate.
    + exact LAST.
Qed.

Theorem scan_one_raw_progress (M : PartialTaggedDFA.t) (input : Input.t) (r : scan_result)
  (SCAN : scan_one_raw M input = Some r)
  : r.(scan_lexeme) <> [].
Proof.
  unfold scan_one_raw in SCAN.
  pose proof (scan_one_loop_nonempty M M.(PartialTaggedDFA.start_state) [] input None I) as NONEMPTY.
  rewrite SCAN in NONEMPTY. exact NONEMPTY.
Qed.

Lemma scan_one_loop_longest (M : PartialTaggedDFA.t) (q : M.(PartialTaggedDFA.state)) (input : Input.t) (consumed : Input.t) (rest : Input.t) (last : option scan_result)
  (WHOLE : input = consumed ++ rest)
  (RUN : PartialTaggedDFA.run_from M M.(PartialTaggedDFA.start_state) consumed = Some q)
  (LAST : opt_scan_seen_longest M input consumed last)
  : opt_scan_longest M input (scan_one_loop M q consumed rest last).
Proof.
  revert q consumed last WHOLE RUN LAST.
  induction rest as [ | c rest IH]; simpl; intros q consumed last WHOLE RUN LAST.
  - destruct last as [r | ]; [ | exact I].
    unfold opt_scan_longest, scan_result_longest.
    unfold opt_scan_seen_longest in LAST. destruct LAST as [SPLIT LAST].
    split; [exact SPLIT | ].
    intros prefix suffix tag PREFIX LONGER ACCEPTS.
    eapply LAST; [exact PREFIX | exact LONGER | | exact ACCEPTS].
    subst input. rewrite app_nil_r in PREFIX.
    rewrite PREFIX. rewrite length_app. lia.
  - destruct (M.(PartialTaggedDFA.step) q c) as [q' | ] eqn: STEP.
    + eapply IH.
      * rewrite WHOLE. rewrite <- app_assoc. reflexivity.
      * rewrite PartialTaggedDFA.run_from_app.
        rewrite RUN. simpl. rewrite STEP. reflexivity.
      * destruct (M.(PartialTaggedDFA.accept_tag) q') as [tag | ] eqn: ACCEPT.
        { unfold opt_scan_seen_longest, scan_result_split. simpl. split.
          - rewrite WHOLE. rewrite <- app_assoc. reflexivity.
          - intros prefix suffix tag0 PREFIX LONGER LE.
            intro ACCEPTS.
            rewrite length_app in LONGER, LE.
            simpl in LONGER, LE. lia.
        }
        { destruct last as [r | ]; [ | exact I].
          unfold opt_scan_seen_longest in *. destruct LAST as [SPLIT LAST].
          split; [exact SPLIT | ].
          intros prefix suffix tag LONGER_PREFIX LONGER LE.
          assert (LE_OLD_OR_EQ : length prefix <= length consumed \/ length prefix = length (consumed ++ [c])).
          { rewrite length_app in LE. rewrite length_app. simpl in LE |- *. lia. }
          destruct LE_OLD_OR_EQ as [LE_OLD | EQ_LEN].
          - eapply LAST; eauto.
          - intro ACCEPTS.
            assert (APP_EQ : (consumed ++ [c]) ++ rest = prefix ++ suffix).
            { rewrite <- app_assoc. simpl. rewrite <- WHOLE. exact LONGER_PREFIX. }
            pose proof (L.app_eq_length_inv (consumed ++ [c]) rest prefix suffix APP_EQ (eq_sym EQ_LEN)) as [PREFIX _].
            subst prefix.
            unfold PartialTaggedDFA.accepted_tag, PartialTaggedDFA.run in ACCEPTS.
            rewrite PartialTaggedDFA.run_from_app in ACCEPTS.
            rewrite RUN in ACCEPTS. simpl in ACCEPTS.
            rewrite STEP in ACCEPTS. simpl in ACCEPTS.
            rewrite ACCEPT in ACCEPTS. discriminate.
        }
    + destruct last as [r | ]; [ | exact I].
      unfold opt_scan_longest, scan_result_longest.
      unfold opt_scan_seen_longest in LAST. destruct LAST as [SPLIT LAST].
      split; [exact SPLIT | ].
      intros prefix suffix tag PREFIX LONGER.
      destruct (le_gt_dec (length prefix) (length consumed)) as [LE | GT].
      * eapply LAST; eauto.
      * intro ACCEPTS.
        subst input.
        pose proof (L.accepted_prefix_longer_cons consumed c rest
          prefix suffix PREFIX GT) as (prefix_tail & PREFIX_EQ).
        subst prefix.
        unfold PartialTaggedDFA.accepted_tag, PartialTaggedDFA.run
          in ACCEPTS.
        rewrite PartialTaggedDFA.run_from_app in ACCEPTS.
        rewrite RUN in ACCEPTS. simpl in ACCEPTS.
        rewrite STEP in ACCEPTS. discriminate.
Qed.

Theorem scan_one_raw_longest (M : PartialTaggedDFA.t) (input : Input.t) (r : scan_result)
  (SCAN : scan_one_raw M input = Some r)
  : scan_result_longest M input r.
Proof.
  unfold scan_one_raw in SCAN.
  pose proof (scan_one_loop_longest M M.(PartialTaggedDFA.start_state)
    input [] input None eq_refl eq_refl I) as LONGEST.
  rewrite SCAN in LONGEST. exact LONGEST.
Qed.

Lemma scan_one_loop_some_result (M : PartialTaggedDFA.t) (q : M.(PartialTaggedDFA.state)) (consumed : Input.t) (rest : Input.t) (r : scan_result)
  : exists r', scan_one_loop M q consumed rest (Some r) = Some r'.
Proof.
  revert q consumed r.
  induction rest as [ | c rest IH]; simpl; intros q consumed r.
  - exists r. reflexivity.
  - destruct (M.(PartialTaggedDFA.step) q c) as [q' | ] eqn: STEP.
    + destruct (M.(PartialTaggedDFA.accept_tag) q') as [tag | ].
      * eapply IH.
      * eapply IH.
    + exists r. reflexivity.
Qed.

Lemma scan_one_loop_none_no_accepted_prefix (M : PartialTaggedDFA.t) (q : M.(PartialTaggedDFA.state)) (input : Input.t) (consumed : Input.t) (rest : Input.t)
  (WHOLE : input = consumed ++ rest)
  (RUN : PartialTaggedDFA.run_from M M.(PartialTaggedDFA.start_state) consumed = Some q)
  (SEEN : no_accepted_prefix_up_to M input consumed)
  (SCAN : scan_one_loop M q consumed rest None = None)
  : no_accepted_nonempty_prefix M input.
Proof.
  revert q consumed WHOLE RUN SEEN SCAN.
  induction rest as [ | c rest IH]; simpl; intros q consumed WHOLE RUN SEEN SCAN.
  - intros prefix suffix tag PREFIX NONEMPTY ACCEPTS.
    eapply SEEN; [exact PREFIX | exact NONEMPTY | | exact ACCEPTS].
    subst input. rewrite app_nil_r in PREFIX.
    rewrite PREFIX. rewrite length_app. lia.
  - destruct (M.(PartialTaggedDFA.step) q c) as [q' | ] eqn: STEP.
    + destruct (M.(PartialTaggedDFA.accept_tag) q') as [tag0 | ] eqn: ACCEPT; [ | ].
      * pose proof (scan_one_loop_some_result M q' (consumed ++ [c])
          rest (mkScanResult (consumed ++ [c]) tag0 rest)) as (r & SOME).
        rewrite SCAN in SOME. discriminate.
      * eapply IH; [ | | | exact SCAN].
        { rewrite WHOLE. rewrite <- app_assoc. reflexivity. }
        { rewrite PartialTaggedDFA.run_from_app. rewrite RUN. simpl. rewrite STEP. reflexivity. }
        { intros prefix suffix tag PREFIX NONEMPTY LE.
          assert (LE_OLD_OR_EQ : length prefix <= length consumed \/ length prefix = length (consumed ++ [c])).
          { rewrite length_app in LE. rewrite length_app. simpl in LE |- *. lia. }
          destruct LE_OLD_OR_EQ as [LE_OLD | EQ_LEN].
          { eapply SEEN; eauto. }
          intro ACCEPTS.
          assert (APP_EQ : (consumed ++ [c]) ++ rest = prefix ++ suffix).
          { rewrite <- app_assoc. simpl. rewrite <- WHOLE. exact PREFIX. }
          pose proof (L.app_eq_length_inv (consumed ++ [c]) rest prefix suffix APP_EQ (eq_sym EQ_LEN)) as [PREFIX_EQ _].
          subst prefix.
          unfold PartialTaggedDFA.accepted_tag, PartialTaggedDFA.run in ACCEPTS.
          rewrite PartialTaggedDFA.run_from_app in ACCEPTS.
          rewrite RUN in ACCEPTS. simpl in ACCEPTS.
          rewrite STEP in ACCEPTS. simpl in ACCEPTS.
          rewrite ACCEPT in ACCEPTS. discriminate.
        }
    + intros prefix suffix tag PREFIX NONEMPTY ACCEPTS.
      destruct (le_gt_dec (length prefix) (length consumed)) as [LE | GT].
      * eapply SEEN; eauto.
      * subst input.
        pose proof (L.accepted_prefix_longer_cons consumed c rest prefix suffix PREFIX GT) as (prefix_tail & PREFIX_EQ).
        subst prefix.
        unfold PartialTaggedDFA.accepted_tag, PartialTaggedDFA.run in ACCEPTS.
        rewrite PartialTaggedDFA.run_from_app in ACCEPTS.
        rewrite RUN in ACCEPTS. simpl in ACCEPTS.
        rewrite STEP in ACCEPTS. discriminate.
Qed.

Theorem scan_one_raw_none_no_accepted_prefix (M : PartialTaggedDFA.t) (input : Input.t)
  (SCAN : scan_one_raw M input = None)
  : no_accepted_nonempty_prefix M input.
Proof.
  unfold scan_one_raw in SCAN.
  eapply (scan_one_loop_none_no_accepted_prefix
    M M.(PartialTaggedDFA.start_state) input [] input).
  - reflexivity.
  - reflexivity.
  - intros prefix suffix tag PREFIX NONEMPTY LE.
    destruct prefix as [ | c prefix]; [contradiction | simpl in LE; lia].
  - exact SCAN.
Qed.

Lemma scan_result_sound_accepted_tag (M : PartialTaggedDFA.t) (r : scan_result)
  (SOUND : scan_result_sound M r)
  : PartialTaggedDFA.accepted_tag M r.(scan_lexeme) = Some r.(scan_token).
Proof.
  unfold scan_result_sound, PartialTaggedDFA.accepted_tag, PartialTaggedDFA.accepted_from, PartialTaggedDFA.run in *.
  exact SOUND.
Qed.

Lemma scan_result_longest_same_rest (M : PartialTaggedDFA.t) (input : Input.t) (r1 : scan_result) (r2 : scan_result)
  (SPLIT1 : scan_result_split input r1)
  (SOUND1 : scan_result_sound M r1)
  (LONGEST1 : scan_result_longest M input r1)
  (SPLIT2 : scan_result_split input r2)
  (SOUND2 : scan_result_sound M r2)
  (LONGEST2 : scan_result_longest M input r2)
  : r1.(scan_lexeme) = r2.(scan_lexeme) /\ r1.(scan_rest) = r2.(scan_rest).
Proof.
  assert (NOT_LT12 : ~ length r1.(scan_lexeme) < length r2.(scan_lexeme)).
  { intros LT.
    destruct LONGEST1 as [_ LONGEST1].
    pose proof (scan_result_sound_accepted_tag M r2 SOUND2) as ACCEPT2.
    eapply (LONGEST1 r2.(scan_lexeme) r2.(scan_rest) r2.(scan_token)); [exact SPLIT2 | exact LT | exact ACCEPT2].
  }
  assert (NOT_LT21 : ~ length r2.(scan_lexeme) < length r1.(scan_lexeme)).
  { intros LT.
    destruct LONGEST2 as [_ LONGEST2].
    pose proof (scan_result_sound_accepted_tag M r1 SOUND1) as ACCEPT1.
    eapply (LONGEST2 r1.(scan_lexeme) r1.(scan_rest) r1.(scan_token)); [exact SPLIT1 | exact LT | exact ACCEPT1].
  }
  assert (LEN : length r1.(scan_lexeme) = length r2.(scan_lexeme)) by lia.
  unfold scan_result_split in SPLIT1, SPLIT2.
  rewrite SPLIT1 in SPLIT2.
  eapply L.app_eq_length_inv; eauto.
Qed.

Theorem scan_one_longest (M : PartialTaggedDFA.t) (input : Input.t) (r : scan_result)
  (SCAN : scan_one M input = inr r)
  : scan_result_longest M input r.
Proof.
  unfold scan_one in SCAN.
  destruct (scan_one_raw M input) as [r0 | ] eqn: RAW; try discriminate.
  inv SCAN. eapply scan_one_raw_longest. exact RAW.
Qed.

Lemma scan_result_rest_lt (input : Input.t) (r : scan_result)
  (SPLIT : scan_result_split input r)
  (NONEMPTY : r.(scan_lexeme) <> [])
  : length r.(scan_rest) < length input.
Proof.
  unfold scan_result_split in SPLIT. subst input.
  rewrite length_app.
  destruct r.(scan_lexeme) as [ | c lexeme].
  - contradiction.
  - simpl. lia.
Qed.

Definition input_lt (input1 input2 : Input.t) : Prop :=
  length input1 < length input2.

Lemma input_lt_wf
  : well_founded input_lt.
Proof.
  unfold input_lt. eapply B.wf_inverse_image. exact lt_wf.
Qed.

Fixpoint lex_loop_acc (M : PartialTaggedDFA.t) (input : Input.t) (ACC : Acc input_lt input) {struct ACC} : ErrM (list scan_result) :=
  match input as input0 return Acc input_lt input0 -> ErrM (list scan_result) with
  | [] => fun _ => inr []
  | c :: input' => fun ACC =>
    match scan_one_raw M (c :: input') as scan return scan_one_raw M (c :: input') = scan -> ErrM (list scan_result) with
    | None => fun _ => inl (Error.NoMatch (c :: input'))
    | Some r => fun SCAN =>
      let SPLIT := scan_one_raw_split M (c :: input') r SCAN in
      let NONEMPTY := scan_one_raw_progress M (c :: input') r SCAN in
      match lex_loop_acc M r.(scan_rest) (Acc_inv ACC (scan_result_rest_lt (c :: input') r SPLIT NONEMPTY)) with
      | inl err => inl err
      | inr rs => inr (r :: rs)
      end
    end eq_refl
  end ACC.

Definition lex_loop (M : PartialTaggedDFA.t) (input : Input.t) : ErrM (list scan_result) :=
  lex_loop_acc M input (input_lt_wf input).

Definition scan_one_cert (M : PartialTaggedDFA.t) (input : Input.t)
  : option { r : scan_result | scan_result_split input r /\ scan_result_sound M r /\ r.(scan_lexeme) <> [] /\ scan_result_longest M input r }.
Proof.
  destruct (scan_one_raw M input) as [r | ] eqn: SCAN.
  - refine (Some (exist _ r _)).
    split.
    + eapply scan_one_raw_split. exact SCAN.
    + split.
      * eapply scan_one_raw_sound. exact SCAN.
      * split.
        { eapply scan_one_raw_progress. exact SCAN. }
        { eapply scan_one_raw_longest. exact SCAN. }
  - exact None.
Defined.

Definition scan_one_dec (M : PartialTaggedDFA.t) (input : Input.t)
  : { r : scan_result | scan_result_split input r /\ scan_result_sound M r /\ r.(scan_lexeme) <> [] /\ scan_result_longest M input r } + { no_accepted_nonempty_prefix M input }.
Proof.
  destruct (scan_one_raw M input) as [r | ] eqn: SCAN.
  - left. exists r. split.
    + eapply scan_one_raw_split. exact SCAN.
    + split.
      * eapply scan_one_raw_sound. exact SCAN.
      * split.
        { eapply scan_one_raw_progress. exact SCAN. }
        { eapply scan_one_raw_longest. exact SCAN. }
  - right. eapply scan_one_raw_none_no_accepted_prefix. exact SCAN.
Defined.

Fixpoint lex_loop_cert_acc (M : PartialTaggedDFA.t) (input : Input.t) (ACC : Acc input_lt input) {struct ACC} : ErrM (list scan_result) :=
  match input as input0 return Acc input_lt input0 -> ErrM (list scan_result) with
  | [] => fun _ => inr []
  | c :: input' => fun ACC =>
    match scan_one_dec M (c :: input') with
    | inright _ => inl (Error.NoMatch (c :: input'))
    | inleft (@exist _ _ r CERT) =>
      match lex_loop_cert_acc M r.(scan_rest) (Acc_inv ACC (scan_result_rest_lt (c :: input') r (proj1 CERT) (proj1 (proj2 (proj2 CERT))))) with
      | inl err => inl err
      | inr rs => inr (r :: rs)
      end
    end
  end ACC.

Definition lex_loop_cert (M : PartialTaggedDFA.t) (input : Input.t) : ErrM (list scan_result) :=
  lex_loop_cert_acc M input (input_lt_wf input).

Fixpoint concat_lexemes (rs : list scan_result) : Input.t :=
  match rs with
  | [] => []
  | r :: rs' => r.(scan_lexeme) ++ concat_lexemes rs'
  end.

End Scanner.

Definition compiled_lexer_dfa (crs : list compiled_rule) : PartialTaggedDFA.t :=
  DeadStateDeletion.of_total (TaggedMinimize.minimize (TaggedSubset.compile (build_tagged_enfa crs))).

Definition lex_scan_results (input : Input.t) : ErrM (list Scanner.scan_result) :=
  match compile_rules with
  | inl err => inl err
  | inr crs => Scanner.lex_loop_cert (compiled_lexer_dfa crs) input
  end.

Definition lex_item_of_scan_result (r : Scanner.scan_result) : string * Token.t :=
  (Input.to_string r.(Scanner.scan_lexeme), r.(Scanner.scan_token)).

Fixpoint concat_lexeme_strings (items : list (string * Token.t)) : string :=
  match items with
  | [] => EmptyString
  | item :: items' => String.append (fst item) (concat_lexeme_strings items')
  end.

Definition lex (s : string) : ErrM (list (string * Token.t)) :=
  match lex_scan_results (Input.of_string s) with
  | inl err => inl err
  | inr rs => inr (map lex_item_of_scan_result rs)
  end.

Theorem lex_success_has_scan_results (s : string) (items : list (string * Token.t))
  (LEX : lex s = inr items)
  : exists rs, lex_scan_results (Input.of_string s) = inr rs /\ items = map lex_item_of_scan_result rs.
Proof.
  unfold lex in LEX.
  destruct (lex_scan_results (Input.of_string s)) as [err | rs] eqn: SCAN; try discriminate.
  inv LEX. exists rs. split; reflexivity.
Qed.

Theorem scan_result_compiled_rule_sound (crs : list compiled_rule) (r : Scanner.scan_result)
  (SOUND : Scanner.scan_result_sound (compiled_lexer_dfa crs) r)
  : exists key, exists cr, lookup_compiled_rule crs key = Some cr /\ r.(Scanner.scan_token) = cr.(compiled_rule_token) /\ compiled_rule_accepts cr r.(Scanner.scan_lexeme).
Proof.
  set (TM := build_tagged_enfa crs).
  set (D := TaggedSubset.compile TM).
  assert (D_OK : TaggedDFA.okay D).
  { subst D TM. eapply TaggedSubset.subset_construction_okay. }
  unfold Scanner.scan_result_sound in SOUND.
  unfold compiled_lexer_dfa in SOUND.
  fold TM in SOUND. fold D in SOUND.
  unfold PartialTaggedDFA.accepted_from in SOUND.
  rewrite DeadStateDeletion.of_total_preserves_accepted_from in SOUND.
  change (TaggedMinimize.accepted_from (TaggedMinimize.minimize D) (TaggedMinimize.block_of D D.(TaggedDFA.start_state)) r.(Scanner.scan_lexeme) = Some r.(Scanner.scan_token)) in SOUND.
  rewrite TaggedMinimize.minimize_accepted_from in SOUND.
  - fold D in SOUND.
    unfold TaggedMinimize.accepted_from in SOUND.
    change (TaggedDFA.accepted_tag D r.(Scanner.scan_lexeme) = Some r.(Scanner.scan_token)) in SOUND.
    pose proof (TaggedSubset.subset_construction_sound TM r.(Scanner.scan_lexeme) r.(Scanner.scan_token) SOUND) as ACCEPTS.
    subst TM.
    pose proof (build_tagged_enfa_sound crs r.(Scanner.scan_token) r.(Scanner.scan_lexeme) ACCEPTS) as (key & cr & LOOKUP & TOKEN & ACCEPTS_RULE).
    exists key. exists cr. splits; [exact LOOKUP | exact TOKEN | exact ACCEPTS_RULE].
  - exact D_OK.
  - destruct D_OK as [START_OK _]. exact START_OK.
Qed.

Theorem scan_result_compiled_rule_priority (crs : list compiled_rule) (r : Scanner.scan_result)
  (SOUND : Scanner.scan_result_sound (compiled_lexer_dfa crs) r)
  : exists cr, first_matching_entry (compiled_rule_table crs) r.(Scanner.scan_lexeme) cr /\ r.(Scanner.scan_token) = cr.(compiled_rule_token).
Proof.
  set (TM := build_tagged_enfa crs).
  set (D := TaggedSubset.compile TM).
  assert (D_OK : TaggedDFA.okay D).
  { subst D TM. eapply TaggedSubset.subset_construction_okay. }
  unfold Scanner.scan_result_sound in SOUND.
  unfold compiled_lexer_dfa in SOUND.
  fold TM in SOUND. fold D in SOUND.
  unfold PartialTaggedDFA.accepted_from in SOUND.
  rewrite DeadStateDeletion.of_total_preserves_accepted_from in SOUND.
  change (TaggedMinimize.accepted_from (TaggedMinimize.minimize D) (TaggedMinimize.block_of D D.(TaggedDFA.start_state)) r.(Scanner.scan_lexeme) = Some r.(Scanner.scan_token)) in SOUND.
  rewrite TaggedMinimize.minimize_accepted_from in SOUND.
  - fold D in SOUND.
    unfold TaggedMinimize.accepted_from in SOUND.
    change (TaggedDFA.accepted_tag D r.(Scanner.scan_lexeme) = Some r.(Scanner.scan_token)) in SOUND.
    pose proof (proj1 (TaggedSubset.subset_construction_exact TM r.(Scanner.scan_lexeme) r.(Scanner.scan_token) (build_tagged_enfa_okay _)) SOUND) as PRIORITY.
    subst TM.
    pose proof (proj1 (build_tagged_enfa_priority_iff crs r.(Scanner.scan_lexeme) r.(Scanner.scan_token)) PRIORITY) as (cr & FIRST & TOKEN).
    exists cr. split; [exact FIRST | exact TOKEN].
  - exact D_OK.
  - destruct D_OK as [START_OK _]. exact START_OK.
Qed.

Definition scan_results_priority (crs : list compiled_rule) (rs : list Scanner.scan_result) : Prop :=
  forall r, r ∈ rs -> (exists cr, first_matching_entry (compiled_rule_table crs) r.(Scanner.scan_lexeme) cr /\ r.(Scanner.scan_token) = cr.(compiled_rule_token)).

Theorem scan_result_raw_rule_sound (crs : list compiled_rule) (r : Scanner.scan_result)
  (COMPILE : compile_rules = inr crs)
  (SOUND : Scanner.scan_result_sound (compiled_lexer_dfa crs) r)
  : exists raw, raw ∈ raw_rules /\ r.(Scanner.scan_token) = raw.(raw_rule_token) /\ raw_rule_accepts raw r.(Scanner.scan_lexeme).
Proof.
  pose proof (scan_result_compiled_rule_sound crs r SOUND) as
    (key & cr & LOOKUP & TOKEN & ACCEPTS).
  pose proof (compile_rules_sound crs COMPILE cr
    (lookup_compiled_rule_in crs key cr LOOKUP)) as
    (raw & IN_RAW & COMPILE_RAW).
  exists raw. splits; [exact IN_RAW | | ].
  - unfold compile_rule in COMPILE_RAW.
    destruct (nullable (raw_rule_regex raw)) eqn: NULLABLE; inv COMPILE_RAW.
    exact TOKEN.
  - eapply compile_rule_sound; eauto.
Qed.

Theorem scan_one_raw_rule_sound (crs : list compiled_rule) (input : Input.t) (r : Scanner.scan_result)
  (COMPILE : compile_rules = inr crs)
  (SCAN : Scanner.scan_one (compiled_lexer_dfa crs) input = inr r)
  : exists raw, raw ∈ raw_rules /\ r.(Scanner.scan_token) = raw.(raw_rule_token) /\ raw_rule_accepts raw r.(Scanner.scan_lexeme).
Proof.
  eapply scan_result_raw_rule_sound; [exact COMPILE | ].
  eapply Scanner.scan_one_sound. exact SCAN.
Qed.

Theorem scan_one_compiled_rule_priority (crs : list compiled_rule) (input : Input.t) (r : Scanner.scan_result)
  (SCAN : Scanner.scan_one (compiled_lexer_dfa crs) input = inr r)
  : exists cr, first_matching_entry (compiled_rule_table crs) r.(Scanner.scan_lexeme) cr /\ r.(Scanner.scan_token) = cr.(compiled_rule_token).
Proof.
  eapply scan_result_compiled_rule_priority.
  eapply Scanner.scan_one_sound. exact SCAN.
Qed.

Definition scan_results_sound (M : PartialTaggedDFA.t) (rs : list Scanner.scan_result) : Prop :=
  forall r, r ∈ rs -> Scanner.scan_result_sound M r.

Theorem scan_results_compiled_rule_priority (crs : list compiled_rule) (rs : list Scanner.scan_result)
  (SOUNDS : scan_results_sound (compiled_lexer_dfa crs) rs)
  : scan_results_priority crs rs.
Proof.
  unfold scan_results_priority. intros r IN.
  eapply scan_result_compiled_rule_priority. eapply SOUNDS. exact IN.
Qed.

Fixpoint scan_results_longest (M : PartialTaggedDFA.t) (input : Input.t) (rs : list Scanner.scan_result) : Prop :=
  match rs with
  | [] => input = []
  | r :: rs' => Scanner.scan_result_longest M input r /\ scan_results_longest M r.(Scanner.scan_rest) rs'
  end.

Theorem lex_loop_cert_acc_concat_lexemes (M : PartialTaggedDFA.t)
  : forall (input : Input.t) (ACC : Acc Scanner.input_lt input) (rs : list Scanner.scan_result), Scanner.lex_loop_cert_acc M input ACC = inr rs -> input = Scanner.concat_lexemes rs.
Proof.
  refine (fix IH input ACC {struct ACC} := _).
  intros rs LEX.
  destruct ACC as [ACC_INV].
  destruct input as [ | c input']; simpl in LEX.
  - inv LEX. reflexivity.
  - destruct (Scanner.scan_one_dec M (c :: input')) as [[r0 CERT] | NO_MATCH]; try discriminate.
    destruct (Scanner.lex_loop_cert_acc M r0.(Scanner.scan_rest) (ACC_INV r0.(Scanner.scan_rest) (Scanner.scan_result_rest_lt (c :: input') r0 (proj1 CERT) (proj1 (proj2 (proj2 CERT)))))) as [err | rs'] eqn: REST; try discriminate.
    inv LEX.
    pose proof (proj1 CERT) as SPLIT.
    pose proof (IH r0.(Scanner.scan_rest) (ACC_INV r0.(Scanner.scan_rest) (Scanner.scan_result_rest_lt (c :: input') r0 (proj1 CERT) (proj1 (proj2 (proj2 CERT))))) rs' REST) as REST_CONCAT.
    simpl. unfold Scanner.scan_result_split in SPLIT.
    rewrite SPLIT.
    f_equal. exact REST_CONCAT.
Qed.

Theorem lex_loop_cert_concat_lexemes (M : PartialTaggedDFA.t) (input : Input.t) (rs : list Scanner.scan_result)
  (LEX : Scanner.lex_loop_cert M input = inr rs)
  : input = Scanner.concat_lexemes rs.
Proof.
  unfold Scanner.lex_loop_cert in LEX.
  eapply lex_loop_cert_acc_concat_lexemes. exact LEX.
Qed.

Theorem lex_loop_cert_acc_scan_results_sound (M : PartialTaggedDFA.t)
  : forall (input : Input.t) (ACC : Acc Scanner.input_lt input) (rs : list Scanner.scan_result), Scanner.lex_loop_cert_acc M input ACC = inr rs -> scan_results_sound M rs.
Proof.
  refine (fix IH input ACC {struct ACC} := _).
  intros rs LEX r IN_R.
  destruct ACC as [ACC_INV].
  destruct input as [ | c input']; simpl in LEX.
  - inv LEX. contradiction.
  - destruct (Scanner.scan_one_dec M (c :: input')) as [[r0 CERT] | NO_MATCH]; try discriminate.
    destruct (Scanner.lex_loop_cert_acc M r0.(Scanner.scan_rest) (ACC_INV r0.(Scanner.scan_rest) (Scanner.scan_result_rest_lt (c :: input') r0 (proj1 CERT) (proj1 (proj2 (proj2 CERT)))))) as [err | rs'] eqn: REST; try discriminate.
    inversion LEX. subst rs. clear LEX.
    pose proof (proj1 CERT) as SPLIT.
    pose proof (proj1 (proj2 CERT)) as SOUND.
    pose proof (proj1 (proj2 (proj2 CERT))) as NONEMPTY.
    cbn in REST.
    destruct IN_R as [EQ | IN_R].
    + subst r. exact SOUND.
    + eapply (IH r0.(Scanner.scan_rest) (ACC_INV r0.(Scanner.scan_rest) (Scanner.scan_result_rest_lt (c :: input') r0 (proj1 CERT) (proj1 (proj2 (proj2 CERT))))) rs' REST r IN_R).
Qed.

Theorem lex_loop_cert_scan_results_sound (M : PartialTaggedDFA.t) (input : Input.t) (rs : list Scanner.scan_result)
  (LEX : Scanner.lex_loop_cert M input = inr rs)
  : scan_results_sound M rs.
Proof.
  unfold Scanner.lex_loop_cert in LEX.
  eapply lex_loop_cert_acc_scan_results_sound. exact LEX.
Qed.

Theorem lex_loop_cert_scan_results_priority (crs : list compiled_rule) (input : Input.t) (rs : list Scanner.scan_result)
  (LEX : Scanner.lex_loop_cert (compiled_lexer_dfa crs) input = inr rs)
  : scan_results_priority crs rs.
Proof.
  eapply scan_results_compiled_rule_priority.
  eapply lex_loop_cert_scan_results_sound. exact LEX.
Qed.

Theorem lex_loop_cert_acc_scan_results_longest (M : PartialTaggedDFA.t)
  : forall (input : Input.t) (ACC : Acc Scanner.input_lt input) (rs : list Scanner.scan_result), Scanner.lex_loop_cert_acc M input ACC = inr rs -> scan_results_longest M input rs.
Proof.
  refine (fix IH input ACC {struct ACC} := _).
  intros rs LEX.
  destruct ACC as [ACC_INV].
  destruct input as [ | c input']; simpl in LEX.
  - inv LEX. reflexivity.
  - destruct (Scanner.scan_one_dec M (c :: input')) as [[r0 CERT] | NO_MATCH]; try discriminate.
    destruct (Scanner.lex_loop_cert_acc M r0.(Scanner.scan_rest) (ACC_INV r0.(Scanner.scan_rest) (Scanner.scan_result_rest_lt (c :: input') r0 (proj1 CERT) (proj1 (proj2 (proj2 CERT)))))) as [err | rs'] eqn: REST; try discriminate.
    inv LEX. split.
    + exact (proj2 (proj2 (proj2 CERT))).
    + eapply (IH r0.(Scanner.scan_rest) (ACC_INV r0.(Scanner.scan_rest) (Scanner.scan_result_rest_lt (c :: input') r0 (proj1 CERT) (proj1 (proj2 (proj2 CERT))))) rs' REST).
Qed.

Theorem lex_loop_cert_scan_results_longest (M : PartialTaggedDFA.t) (input : Input.t) (rs : list Scanner.scan_result)
  (LEX : Scanner.lex_loop_cert M input = inr rs)
  : scan_results_longest M input rs.
Proof.
  unfold Scanner.lex_loop_cert in LEX.
  eapply lex_loop_cert_acc_scan_results_longest. exact LEX.
Qed.

Theorem lex_loop_cert_acc_no_match_sound (M : PartialTaggedDFA.t)
  : forall (input : Input.t) (ACC : Acc Scanner.input_lt input) (rest : Input.t), Scanner.lex_loop_cert_acc M input ACC = inl (Error.NoMatch rest) -> Scanner.no_accepted_nonempty_prefix M rest.
Proof.
  refine (fix IH input ACC {struct ACC} := _).
  intros rest LEX.
  destruct ACC as [ACC_INV].
  destruct input as [ | c input']; simpl in LEX.
  - discriminate.
  - destruct (Scanner.scan_one_dec M (c :: input')) as [[r0 CERT] | NO_MATCH].
    + destruct (Scanner.lex_loop_cert_acc M r0.(Scanner.scan_rest) (ACC_INV r0.(Scanner.scan_rest) (Scanner.scan_result_rest_lt (c :: input') r0 (proj1 CERT) (proj1 (proj2 (proj2 CERT)))))) as [err | rs'] eqn: REST; try discriminate.
      inv LEX.
      eapply (IH r0.(Scanner.scan_rest) (ACC_INV r0.(Scanner.scan_rest) (Scanner.scan_result_rest_lt (c :: input') r0 (proj1 CERT) (proj1 (proj2 (proj2 CERT))))) rest REST).
    + inv LEX. exact NO_MATCH.
Qed.

Theorem lex_loop_cert_no_match_sound (M : PartialTaggedDFA.t) (input : Input.t) (rest : Input.t)
  (LEX : Scanner.lex_loop_cert M input = inl (Error.NoMatch rest))
  : Scanner.no_accepted_nonempty_prefix M rest.
Proof.
  unfold Scanner.lex_loop_cert in LEX.
  eapply lex_loop_cert_acc_no_match_sound. exact LEX.
Qed.

Theorem lex_loop_cert_acc_complete_for_tokenizable (M : PartialTaggedDFA.t)
  : forall (input : Input.t) (ACC : Acc Scanner.input_lt input), Scanner.tokenizable M input -> exists rs, Scanner.lex_loop_cert_acc M input ACC = inr rs.
Proof.
  refine (fix IH input ACC {struct ACC} := _).
  intros TOK.
  destruct ACC as [ACC_INV].
  destruct input as [ | c input']; simpl.
  - exists []. reflexivity.
  - inv TOK.
    destruct (Scanner.scan_one_dec M (c :: input')) as [[r0 CERT] | NO_MATCH].
    + pose proof (proj1 CERT) as SPLIT0.
      pose proof (proj1 (proj2 CERT)) as SOUND0.
      pose proof (proj1 (proj2 (proj2 CERT))) as NONEMPTY0.
      pose proof (proj2 (proj2 (proj2 CERT))) as LONGEST0.
      pose proof (Scanner.scan_result_longest_same_rest M (c :: input') r0 r SPLIT0 SOUND0 LONGEST0 SPLIT SOUND LONGEST) as (_ & REST_EQ).
      assert (TOK0 : Scanner.tokenizable M r0.(Scanner.scan_rest)).
      { rewrite REST_EQ. exact REST. }
      destruct (IH r0.(Scanner.scan_rest) (ACC_INV r0.(Scanner.scan_rest) (Scanner.scan_result_rest_lt (c :: input') r0 (proj1 CERT) (proj1 (proj2 (proj2 CERT))))) TOK0) as (rs & LOOP).
      rewrite LOOP. exists (r0 :: rs). reflexivity.
    + exfalso.
      pose proof (Scanner.scan_result_sound_accepted_tag M r SOUND) as ACCEPT.
      eapply (NO_MATCH r.(Scanner.scan_lexeme) r.(Scanner.scan_rest) r.(Scanner.scan_token)); eauto.
Qed.

Theorem lex_loop_cert_complete_for_tokenizable (M : PartialTaggedDFA.t) (input : Input.t)
  (TOK : Scanner.tokenizable M input)
  : exists rs, Scanner.lex_loop_cert M input = inr rs.
Proof.
  unfold Scanner.lex_loop_cert.
  eapply lex_loop_cert_acc_complete_for_tokenizable. exact TOK.
Qed.

Theorem lex_scan_results_longest (input : Input.t) (rs : list Scanner.scan_result)
  (SCAN : lex_scan_results input = inr rs)
  : exists crs, compile_rules = inr crs /\ scan_results_longest (compiled_lexer_dfa crs) input rs.
Proof.
  unfold lex_scan_results in SCAN.
  destruct compile_rules as [err | crs] eqn: COMPILE; try discriminate.
  exists crs. split; [reflexivity | ].
  eapply lex_loop_cert_scan_results_longest. exact SCAN.
Qed.

Theorem lex_scan_results_priority (input : Input.t) (rs : list Scanner.scan_result)
  (SCAN : lex_scan_results input = inr rs)
  : exists crs, compile_rules = inr crs /\ scan_results_priority crs rs.
Proof.
  unfold lex_scan_results in SCAN.
  destruct compile_rules as [err | crs] eqn: COMPILE; try discriminate.
  exists crs. split; [reflexivity | ].
  eapply lex_loop_cert_scan_results_priority. exact SCAN.
Qed.

Theorem lex_success_has_longest_scan_results (s : string) (items : list (string * Token.t))
  (LEX : lex s = inr items)
  : exists crs, exists rs, compile_rules = inr crs /\ lex_scan_results (Input.of_string s) = inr rs /\ items = map lex_item_of_scan_result rs /\ scan_results_longest (compiled_lexer_dfa crs) (Input.of_string s) rs.
Proof.
  pose proof (lex_success_has_scan_results s items LEX)as (rs & SCAN & ITEMS).
  pose proof (lex_scan_results_longest (Input.of_string s) rs SCAN)as (crs & COMPILE & LONGEST).
  exists crs. exists rs. splits; eauto.
Qed.

Theorem lex_success_has_longest_priority_scan_results (s : string) (items : list (string * Token.t))
  (LEX : lex s = inr items)
  : exists crs, exists rs, compile_rules = inr crs /\ lex_scan_results (Input.of_string s) = inr rs /\ items = map lex_item_of_scan_result rs /\ scan_results_longest (compiled_lexer_dfa crs) (Input.of_string s) rs /\ scan_results_priority crs rs.
Proof.
  pose proof (lex_success_has_scan_results s items LEX) as (rs & SCAN & ITEMS).
  unfold lex_scan_results in SCAN.
  destruct compile_rules as [err | crs] eqn: COMPILE; try discriminate.
  exists crs. exists rs. splits.
  - reflexivity.
  - unfold lex_scan_results. rewrite COMPILE. exact SCAN.
  - exact ITEMS.
  - eapply lex_loop_cert_scan_results_longest. exact SCAN.
  - eapply lex_loop_cert_scan_results_priority. exact SCAN.
Qed.

Theorem lex_scan_results_no_match_sound (input : Input.t) (rest : Input.t)
  (SCAN : lex_scan_results input = inl (Error.NoMatch rest))
  : exists crs, compile_rules = inr crs /\ Scanner.no_accepted_nonempty_prefix (compiled_lexer_dfa crs) rest.
Proof.
  unfold lex_scan_results in SCAN.
  destruct compile_rules as [err | crs] eqn: COMPILE.
  - inv SCAN. exfalso.
    eapply compile_rules_not_no_match. exact COMPILE.
  - exists crs. split; [reflexivity | ].
    eapply lex_loop_cert_no_match_sound. exact SCAN.
Qed.

Theorem lex_error_sound (s : string) (rest : Input.t)
  (LEX : lex s = inl (Error.NoMatch rest))
  : exists crs, compile_rules = inr crs /\ Scanner.no_accepted_nonempty_prefix (compiled_lexer_dfa crs) rest.
Proof.
  unfold lex in LEX.
  destruct (lex_scan_results (Input.of_string s)) as [err | rs] eqn: SCAN; try discriminate.
  inv LEX.
  eapply lex_scan_results_no_match_sound. exact SCAN.
Qed.

Definition lex_tokenizable (input : Input.t) : Prop :=
  exists crs, compile_rules = inr crs /\ Scanner.tokenizable (compiled_lexer_dfa crs) input.

Theorem lex_complete_for_tokenizable_input (s : string)
  (TOK : lex_tokenizable (Input.of_string s))
  : exists items, lex s = inr items.
Proof.
  destruct TOK as (crs & COMPILE & TOK).
  unfold lex, lex_scan_results.
  rewrite COMPILE.
  pose proof (lex_loop_cert_complete_for_tokenizable (compiled_lexer_dfa crs) (Input.of_string s) TOK) as (rs & LOOP).
  rewrite LOOP. exists (map lex_item_of_scan_result rs). reflexivity.
Qed.

Definition lex_items_sound (items : list (string * Token.t)) : Prop :=
  forall item, item ∈ items -> (exists raw, raw ∈ raw_rules /\ snd item = raw.(raw_rule_token) /\ raw_rule_accepts raw (Input.of_string (fst item))).

Theorem lex_items_of_scan_results_sound (crs : list compiled_rule) (rs : list Scanner.scan_result)
  (COMPILE : compile_rules = inr crs)
  (SOUNDS : scan_results_sound (compiled_lexer_dfa crs) rs)
  : lex_items_sound (map lex_item_of_scan_result rs).
Proof.
  unfold lex_items_sound. intros item IN.
  rewrite in_map_iff in IN.
  destruct IN as (r & EQ & IN_R). subst item.
  pose proof (scan_result_raw_rule_sound crs r COMPILE (SOUNDS r IN_R)) as (raw & IN_RAW & TOKEN & ACCEPTS).
  exists raw. split; [exact IN_RAW | ]. split.
  - simpl. exact TOKEN.
  - simpl. rewrite Input_of_to_string. exact ACCEPTS.
Qed.

Theorem concat_lexeme_strings_of_scan_results (rs : list Scanner.scan_result)
  : concat_lexeme_strings (map lex_item_of_scan_result rs) = Input.to_string (Scanner.concat_lexemes rs).
Proof.
  induction rs as [ | r rs IH]; simpl.
  - reflexivity.
  - rewrite Input_to_string_app. simpl. congruence.
Qed.

Theorem lex_sound_concat (s : string) (items : list (string * Token.t))
  (LEX : lex s = inr items)
  : concat_lexeme_strings items = s.
Proof.
  unfold lex in LEX.
  destruct (lex_scan_results (Input.of_string s)) as [err | rs] eqn: SCAN; try discriminate.
  inv LEX.
  unfold lex_scan_results in SCAN.
  destruct compile_rules as [err | crs] eqn: COMPILE; try discriminate.
  rewrite concat_lexeme_strings_of_scan_results.
  pose proof (lex_loop_cert_concat_lexemes (compiled_lexer_dfa crs) (Input.of_string s) rs SCAN) as CONCAT.
  rewrite <- CONCAT. eapply Input_to_of_string.
Qed.

Theorem lex_sound_tokens (s : string) (items : list (string * Token.t))
  (LEX : lex s = inr items)
  : lex_items_sound items.
Proof.
  unfold lex in LEX.
  destruct (lex_scan_results (Input.of_string s)) as [err | rs] eqn: SCAN; try discriminate.
  inv LEX.
  unfold lex_scan_results in SCAN.
  destruct compile_rules as [err | crs] eqn: COMPILE; try discriminate.
  pose proof (lex_loop_cert_scan_results_sound (compiled_lexer_dfa crs) (Input.of_string s) rs SCAN) as SOUNDS.
  eapply lex_items_of_scan_results_sound; eauto.
Qed.

End LGS.
