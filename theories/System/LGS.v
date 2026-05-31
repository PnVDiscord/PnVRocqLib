Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Strings.String.
Require Import PnV.Prelude.Prelude.
Require Import PnV.System.Regex.

#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "=~=" := (is_similar_to (Similarity := Re.in_regex eq)) : type_scope.

#[global]
Instance ascii_hasEqDec
  : hasEqDec@{Set} ascii.
Proof.
  exact Ascii.ascii_dec.
Defined.

Module Type TOKEN_SPEC.

Parameter t : Set.

#[global] Parameter t_hasEqDec : hasEqDec@{Set} t.

Parameter rules : list (t * regex ascii).

Parameter skips : list (regex ascii).

End TOKEN_SPEC.

Module LGS (Token : TOKEN_SPEC).

#[local] Existing Instance Token.t_hasEqDec.

Module Error.

Inductive t : Set :=
  | EmptyTokenRule (idx : nat)
  | EmptySkipRule (idx : nat)
  | BadRegex (idx : nat)
  | NoMatch (rest : list ascii)
  | FuelExhausted
  | InternalInvariantBroken.

End Error.

#[universes(polymorphic=yes)]
Definition ErrM@{u} (A : Type@{u}) : Type@{u} :=
  Error.t + A.

#[global, universes(polymorphic=yes)]
Instance result_isMonad@{u} : isMonad@{u u} ErrM@{u} :=
  { bind {A : Type@{u}} {B : Type@{u}} (m : ErrM@{u} A) (k : A -> ErrM@{u} B) := B.either (@inl _ _) k m
  ; pure {A : Type@{u}} (x : A) := inr x
  }.

Module Input.

Definition t : Set :=
  list ascii.

Fixpoint of_string (s : string) : t :=
  match s with
  | EmptyString => []
  | String c s' => c :: of_string s'
  end.

Fixpoint to_string (s : t) : string :=
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

Theorem Input_length_of_string (s : string)
  : length (Input.of_string s) = String.length s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
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

Inductive reachable (M : t) : state M -> list ascii -> state M -> Prop :=
  | reachable_nil q
    : reachable M q [] q
  | reachable_eps q1 q2 q3 s
    (STEP : L.In q2 (eps_step M q1))
    (REST : reachable M q2 s q3)
    : reachable M q1 s q3
  | reachable_char q1 q2 q3 a s
    (STEP : L.In q2 (char_step M q1 a))
    (REST : reachable M q2 s q3)
    : reachable M q1 (a :: s) q3.

Inductive eclose (M : t) : state M -> state M -> Prop :=
  | eclose_refl q
    : eclose M q q
  | eclose_step q1 q2 q3
    (STEP : L.In q2 (eps_step M q1))
    (REST : eclose M q2 q3)
    : eclose M q1 q3.

Definition accepts (M : t) (s : list ascii) : Prop :=
  exists q, reachable M (start M) s q /\ L.In q (accept_states M).

Definition wf (M : t) : Prop :=
  L.In (start M) (states M) /\ (forall q, L.In q (accept_states M) -> L.In q (states M)) /\ (forall q, forall q', L.In q (states M) -> L.In q' (eps_step M q) -> L.In q' (states M)) /\ (forall q, forall q', forall a, L.In q (states M) -> L.In q' (char_step M q a) -> L.In q' (states M)).

End ENFA.

#[local] Hint Constructors ENFA.reachable ENFA.eclose : core.

Theorem ENFA_accepts_ext (M : ENFA.t) (s1 : list ascii) (s2 : list ascii)
  (EQ : s1 = s2)
  : ENFA.accepts M s1 <-> ENFA.accepts M s2.
Proof.
  subst s2. done!.
Qed.

Theorem ENFA_reachable_app (M : ENFA.t) (q1 : ENFA.state M) (q2 : ENFA.state M) (q3 : ENFA.state M) (s1 : list ascii) (s2 : list ascii)
  (R1 : ENFA.reachable M q1 s1 q2)
  (R2 : ENFA.reachable M q2 s2 q3)
  : ENFA.reachable M q1 (s1 ++ s2) q3.
Proof.
  induction R1 as [q | q1' q2' q3' s STEP REST IH | q1' q2' q3' a s STEP REST IH]; simpl; eauto with *.
Qed.

Theorem ENFA_eclose_trans (M : ENFA.t) (q1 : ENFA.state M) (q2 : ENFA.state M) (q3 : ENFA.state M)
  (CLOSE1 : ENFA.eclose M q1 q2)
  (CLOSE2 : ENFA.eclose M q2 q3)
  : ENFA.eclose M q1 q3.
Proof.
  induction CLOSE1 as [q | q1' q2' q3' STEP REST IH]; eauto with *.
Qed.

Theorem ENFA_eclose_reachable_nil (M : ENFA.t) (q1 : ENFA.state M) (q2 : ENFA.state M)
  (CLOSE : ENFA.eclose M q1 q2)
  : ENFA.reachable M q1 [] q2.
Proof.
  induction CLOSE as [q | q1' q2' q3 STEP REST IH]; eauto with *.
Qed.

Theorem ENFA_reachable_nil_eclose (M : ENFA.t) (q1 : ENFA.state M) (q2 : ENFA.state M)
  (REACH : ENFA.reachable M q1 [] q2)
  : ENFA.eclose M q1 q2.
Proof.
  remember (@nil ascii) as s eqn: EQ. induction REACH as [q | q1' q2' q3' s STEP REST IH | q1' q2' q3' a s STEP REST IH]; inv EQ; eauto with *.
Qed.

Theorem ENFA_eclose_reachable_nil_iff (M : ENFA.t) (q1 : ENFA.state M) (q2 : ENFA.state M)
  : ENFA.eclose M q1 q2 <-> ENFA.reachable M q1 [] q2.
Proof.
  split; intros H.
  - eapply ENFA_eclose_reachable_nil; eauto.
  - eapply ENFA_reachable_nil_eclose; eauto.
Qed.

Theorem ENFA_eclose_wf (M : ENFA.t) (q1 : ENFA.state M) (q2 : ENFA.state M)
  (WF : ENFA.wf M)
  (IN : L.In q1 (ENFA.states M))
  (CLOSE : ENFA.eclose M q1 q2)
  : L.In q2 (ENFA.states M).
Proof.
  destruct WF as (_ & _ & EPS_WF & _).
  induction CLOSE as [q | q1' q2' q3 STEP REST IH].
  - exact IN.
  - eapply IH. eapply EPS_WF; eauto.
Qed.

Theorem ENFA_reachable_wf (M : ENFA.t) (q1 : ENFA.state M) (q2 : ENFA.state M) (s : list ascii)
  (WF : ENFA.wf M)
  (IN : L.In q1 (ENFA.states M))
  (REACH : ENFA.reachable M q1 s q2)
  : L.In q2 (ENFA.states M).
Proof.
  destruct WF as (_ & _ & EPS_WF & CHAR_WF).
  induction REACH as [q | q1' q2' q3 s STEP REST IH | q1' q2' q3 a s STEP REST IH].
  - exact IN.
  - eapply IH. eapply EPS_WF; eauto.
  - eapply IH. eapply CHAR_WF; eauto.
Qed.

Theorem ENFA_reachable_inv (M : ENFA.t) (q1 : ENFA.state M) (q3 : ENFA.state M) (s : list ascii)
  (REACH : ENFA.reachable M q1 s q3)
  : (s = [] /\ q3 = q1) \/ (exists q2, L.In q2 (ENFA.eps_step M q1) /\ ENFA.reachable M q2 s q3) \/ (exists a, exists s', exists q2, s = a :: s' /\ L.In q2 (ENFA.char_step M q1 a) /\ ENFA.reachable M q2 s' q3).
Proof.
  destruct REACH as [q | q1' q2' q3' s' STEP REST | q1' q2' q3' a s' STEP REST].
  - left. split; reflexivity.
  - right. left. exists q2'. split; eauto.
  - right. right. exists a. exists s'. exists q2'. splits; eauto.
Qed.

Theorem ENFA_reachable_stuck (M : ENFA.t) (q1 : ENFA.state M) (q2 : ENFA.state M) (s : list ascii)
  (NO_EPS : forall q, L.In q (ENFA.eps_step M q1) -> False)
  (NO_CHAR : forall a, forall q, L.In q (ENFA.char_step M q1 a) -> False)
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

Fixpoint run_from (M : t) (q : state M) (s : list ascii) {struct s} : option (state M) :=
  match s with
  | [] => Some q
  | c :: s' =>
    match step M q c with
    | Some q' => run_from M q' s'
    | None => None
    end
  end.

Definition run (M : t) (s : list ascii) : option (state M) :=
  run_from M (start M) s.

Definition accepts (M : t) (s : list ascii) : Prop :=
  exists q, run M s = Some q /\ acceptb M q = true.

Definition acceptsb (M : t) (s : list ascii) : bool :=
  match run M s with
  | Some q => acceptb M q
  | None => false
  end.

Definition wf (M : t) : Prop :=
  L.In (start M) (states M) /\ (forall q, forall q', forall a, L.In q (states M) -> step M q a = Some q' -> L.In q' (states M)).

Inductive step_rel (M : t) : state M -> ascii -> state M -> Prop :=
  | step_rel_intro q a q'
    (STEP : step M q a = Some q')
    : step_rel M q a q'.

Inductive reachable (M : t) : state M -> list ascii -> state M -> Prop :=
  | reachable_nil q
    : reachable M q [] q
  | reachable_cons q1 q2 q3 a s
    (STEP : step_rel M q1 a q2)
    (REST : reachable M q2 s q3)
    : reachable M q1 (a :: s) q3.

Definition language (M : t) : ensemble (list ascii) :=
  fun s => accepts M s.

Definition deterministic (M : t) : Prop :=
  forall q, forall a, forall q1, forall q2, step_rel M q a q1 -> step_rel M q a q2 -> q1 = q2.

Definition total (M : t) : Prop :=
  forall q, forall a, exists q', step M q a = Some q'.

End DFA.

#[local] Hint Constructors DFA.step_rel DFA.reachable : core.

Theorem DFA_step_rel_deterministic (M : DFA.t)
  : DFA.deterministic M.
Proof.
  ii. inv H. inv H0. congruence.
Qed.

Theorem DFA_run_from_reachable_sound (M : DFA.t) (q1 : DFA.state M) (q2 : DFA.state M) (s : list ascii)
  (RUN : DFA.run_from M q1 s = Some q2)
  : DFA.reachable M q1 s q2.
Proof.
  revert q1 q2 RUN. induction s as [ | a s IH]; simpl; i.
  - inv RUN. eauto with *.
  - destruct (DFA.step M q1 a) as [q' | ] eqn: STEP; try congruence. eauto with *.
Qed.

Theorem DFA_run_from_reachable_complete (M : DFA.t) (q1 : DFA.state M) (q2 : DFA.state M) (s : list ascii)
  (REACH : DFA.reachable M q1 s q2)
  : DFA.run_from M q1 s = Some q2.
Proof.
  induction REACH as [q | q1' q2' q3 a s STEP REST IH]; simpl.
  - reflexivity.
  - inv STEP. rewrite STEP0. exact IH.
Qed.

Corollary DFA_reachable_unique (M : DFA.t) (q : DFA.state M) (q1 : DFA.state M) (q2 : DFA.state M) (s : list ascii)
  (R1 : DFA.reachable M q s q1)
  (R2 : DFA.reachable M q s q2)
  : q1 = q2.
Proof.
  pose proof (DFA_run_from_reachable_complete M q q1 s R1) as RUN1.
  pose proof (DFA_run_from_reachable_complete M q q2 s R2) as RUN2.
  congruence.
Qed.

Theorem DFA_accepts_iff_run (M : DFA.t) (s : list ascii)
  : DFA.accepts M s <-> (exists q, DFA.run M s = Some q /\ DFA.acceptb M q = true).
Proof.
  reflexivity.
Qed.

Theorem DFA_acceptsb_spec (M : DFA.t) (s : list ascii)
  : DFA.acceptsb M s = true <-> DFA.accepts M s.
Proof.
  unfold DFA.acceptsb, DFA.accepts. destruct (DFA.run M s) as [q | ] eqn: RUN; split; i; des; try congruence; eauto.
Qed.

Theorem DFA_reachable_app (M : DFA.t) (q1 : DFA.state M) (q2 : DFA.state M) (q3 : DFA.state M) (s1 : list ascii) (s2 : list ascii)
  (R1 : DFA.reachable M q1 s1 q2)
  (R2 : DFA.reachable M q2 s2 q3)
  : DFA.reachable M q1 (s1 ++ s2) q3.
Proof.
  induction R1 as [q | q1' q2' q3' a s STEP REST IH]; simpl; eauto with *.
Qed.

Theorem DFA_run_from_app (M : DFA.t) (q1 : DFA.state M) (q2 : DFA.state M) (s1 : list ascii) (s2 : list ascii)
  (RUN1 : DFA.run_from M q1 s1 = Some q2)
  : DFA.run_from M q1 (s1 ++ s2) = DFA.run_from M q2 s2.
Proof.
  revert q1 q2 RUN1. induction s1 as [ | a s1 IH]; simpl; i.
  - inv RUN1. reflexivity.
  - destruct (DFA.step M q1 a) as [q' | ] eqn: STEP; try congruence. eauto.
Qed.

Corollary DFA_accepts_dec (M : DFA.t) (s : list ascii)
  : {DFA.accepts M s} + {~ DFA.accepts M s}.
Proof.
  destruct (DFA.acceptsb M s) eqn: ACCEPTS.
  - left. eapply DFA_acceptsb_spec. exact ACCEPTS.
  - right. intros CONTRA. rewrite <- DFA_acceptsb_spec in CONTRA. congruence.
Defined.

Definition dfa_lang_equiv (M1 : DFA.t) (M2 : DFA.t) : Prop :=
  forall s, DFA.accepts M1 s <-> DFA.accepts M2 s.

Theorem dfa_lang_equiv_refl (M : DFA.t)
  : dfa_lang_equiv M M.
Proof.
  ii. reflexivity.
Qed.

Theorem dfa_lang_equiv_sym (M1 : DFA.t) (M2 : DFA.t)
  (EQ : dfa_lang_equiv M1 M2)
  : dfa_lang_equiv M2 M1.
Proof.
  ii. symmetry. eapply EQ.
Qed.

Theorem dfa_lang_equiv_trans (M1 : DFA.t) (M2 : DFA.t) (M3 : DFA.t)
  (EQ12 : dfa_lang_equiv M1 M2)
  (EQ23 : dfa_lang_equiv M2 M3)
  : dfa_lang_equiv M1 M3.
Proof.
  ii. etransitivity; [eapply EQ12 | eapply EQ23].
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
    + rewrite andb_true_iff in H. destruct H as (H1 & H2). change (@nil ascii) with ((@nil ascii) ++ (@nil ascii)). eauto with *.
    + econs.
  - assert (CLAIM : forall s, forall e0, s =~= e0 -> s = [] -> nullable e0 = true).
    { intros s e0 H_IN. induction H_IN; simpl; i; subst; try congruence; eauto.
      - rewrite orb_true_iff. left. eauto.
      - rewrite orb_true_iff. right. eauto.
      - pose proof (app_eq_nil _ _ H) as (EQ1 & EQ2). subst. rewrite andb_true_iff. eauto.
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

Module Subset.

Definition dstate (M : ENFA.t) : Set :=
  list (ENFA.state M).

Definition subset_member (M : ENFA.t) (q : ENFA.state M) (S : dstate M) : Prop :=
  L.In q S.

Definition subset_of_states (M : ENFA.t) (qs : list (ENFA.state M)) : Prop :=
  forall q, L.In q qs -> L.In q (ENFA.states M).

Definition mem {A : Set} `{EQ_DEC : hasEqDec@{Set} A} (x : A) (xs : list A) : bool :=
  if in_dec eq_dec x xs then true else false.

Definition add {A : Set} `{EQ_DEC : hasEqDec@{Set} A} (x : A) (xs : list A) : list A :=
  if mem x xs then xs else x :: xs.

Fixpoint union {A : Set} `{EQ_DEC : hasEqDec@{Set} A} (xs : list A) (ys : list A) {struct xs} : list A :=
  match xs with
  | [] => ys
  | x :: xs' => union xs' (add x ys)
  end.

Fixpoint iter {A : Set} (n : nat) (f : A -> A) (x : A) {struct n} : A :=
  match n with
  | 0 => x
  | S n' => iter n' f (f x)
  end.

Definition eclose_once (M : ENFA.t) (seen : list (ENFA.state M)) : list (ENFA.state M) :=
  fold_right (fun q => fun acc => @union (ENFA.state M) (ENFA.state_hasEqDec M) (ENFA.eps_step M q) acc) seen seen.

Definition eclose (M : ENFA.t) (qs : list (ENFA.state M)) : list (ENFA.state M) :=
  iter (length (ENFA.states M)) (eclose_once M) (@union (ENFA.state M) (ENFA.state_hasEqDec M) qs []).

Definition move (M : ENFA.t) (qs : list (ENFA.state M)) (a : ascii) : list (ENFA.state M) :=
  flat_map (fun q => ENFA.char_step M q a) (eclose M qs).

Definition start (M : ENFA.t) : dstate M :=
  eclose M [ENFA.start M].

Definition step (M : ENFA.t) (S : dstate M) (a : ascii) : dstate M :=
  eclose M (move M S a).

Definition acceptb (M : ENFA.t) (S : dstate M) : bool :=
  existsb (fun q => @mem (ENFA.state M) (ENFA.state_hasEqDec M) q (ENFA.accept_states M)) S.

Definition alphabet : list ascii :=
  map ascii_of_nat (seq 0 256).

Definition successors (M : ENFA.t) (S : dstate M) : list (dstate M) :=
  map (step M S) alphabet.

Definition expand (M : ENFA.t) (seen : list (dstate M)) : list (dstate M) :=
  fold_right (fun S => fun acc => @union (dstate M) (list_hasEqDec (ENFA.state_hasEqDec M)) (successors M S) acc) seen seen.

Definition reachable_bound (M : ENFA.t) : nat :=
  Nat.pow 2 (length (ENFA.states M)).

Definition states (M : ENFA.t) : list (dstate M) :=
  iter (S (reachable_bound M)) (expand M) (@union (dstate M) (list_hasEqDec (ENFA.state_hasEqDec M)) [start M] []).

Definition compile (M : ENFA.t) : DFA.t :=
  DFA.mk (dstate M) (list_hasEqDec (ENFA.state_hasEqDec M)) (states M) (start M) (acceptb M) (fun S => fun a => Some (step M S a)).

Definition has_origin (M : ENFA.t) (qs : list (ENFA.state M)) (seen : list (ENFA.state M)) : Prop :=
  forall q, L.In q seen -> exists q0, L.In q0 qs /\ ENFA.reachable M q0 [] q.

Lemma add_sound {A : Set} `{EQ_DEC : hasEqDec@{Set} A} (x : A) (y : A) (xs : list A)
  (IN : L.In y (add x xs))
  : y = x \/ L.In y xs.
Proof.
  unfold add, mem in IN. destruct (in_dec eq_dec x xs) as [IN_x | NOT_IN_x].
  - right. exact IN.
  - simpl in IN. destruct IN as [EQ | IN].
    + left. symmetry. exact EQ.
    + right. exact IN.
Qed.

Lemma add_complete {A : Set} `{EQ_DEC : hasEqDec@{Set} A} (x : A) (y : A) (xs : list A)
  (IN : y = x \/ L.In y xs)
  : L.In y (add x xs).
Proof.
  unfold add, mem. destruct (in_dec eq_dec x xs) as [IN_x | NOT_IN_x].
  - destruct IN as [EQ | IN].
    + subst y. exact IN_x.
    + exact IN.
  - simpl. destruct IN as [EQ | IN].
    + left. symmetry. exact EQ.
    + right. exact IN.
Qed.

Lemma union_sound {A : Set} `{EQ_DEC : hasEqDec@{Set} A} (xs : list A) (ys : list A) (z : A)
  (IN : L.In z (union xs ys))
  : L.In z xs \/ L.In z ys.
Proof.
  revert ys IN. induction xs as [ | x xs IH]; simpl; intros ys IN.
  - right. exact IN.
  - pose proof (IH (add x ys) IN) as [IN_xs | IN_add].
    + left. right. exact IN_xs.
    + pose proof (add_sound x z ys IN_add) as [EQ | IN_ys].
      * left. left. symmetry. exact EQ.
      * right. exact IN_ys.
Qed.

Lemma union_complete {A : Set} `{EQ_DEC : hasEqDec@{Set} A} (xs : list A) (ys : list A) (z : A)
  (IN : L.In z xs \/ L.In z ys)
  : L.In z (union xs ys).
Proof.
  revert ys IN. induction xs as [ | x xs IH]; simpl; intros ys IN.
  - destruct IN as [IN | IN]; [contradiction | exact IN].
  - eapply IH. destruct IN as [[EQ | IN_xs] | IN_ys].
    + right. eapply add_complete. left. symmetry. exact EQ.
    + left. exact IN_xs.
    + right. eapply add_complete. right. exact IN_ys.
Qed.

Lemma eclose_fold_sound (M : ENFA.t) (seeds : list (ENFA.state M)) (base : list (ENFA.state M)) q
  (IN : L.In q (fold_right (fun q0 => fun acc => @union (ENFA.state M) (ENFA.state_hasEqDec M) (ENFA.eps_step M q0) acc) base seeds))
  : L.In q base \/ (exists q0, L.In q0 seeds /\ L.In q (ENFA.eps_step M q0)).
Proof.
  revert base IN. induction seeds as [ | q0 seeds IH]; simpl; intros base IN.
  - left. exact IN.
  - pose proof (union_sound (ENFA.eps_step M q0) _ q IN) as [STEP | IN_REST].
    + right. exists q0. split; [left; reflexivity | exact STEP].
    + pose proof (IH base IN_REST) as [IN_BASE | (q1 & IN_SEEDS & STEP)].
      * left. exact IN_BASE.
      * right. exists q1. split; [right; exact IN_SEEDS | exact STEP].
Qed.

Lemma union_initial_has_origin (M : ENFA.t) (qs : list (ENFA.state M))
  : has_origin M qs (@union (ENFA.state M) (ENFA.state_hasEqDec M) qs []).
Proof.
  unfold has_origin. intros q IN.
  pose proof (union_sound qs [] q IN) as [IN_QS | IN_NIL].
  - exists q. split; [exact IN_QS | eauto with *].
  - contradiction.
Qed.

Lemma eclose_once_preserves_origin (M : ENFA.t) (qs : list (ENFA.state M)) (seen : list (ENFA.state M))
  (ORIGIN : has_origin M qs seen)
  : has_origin M qs (eclose_once M seen).
Proof.
  unfold has_origin in *. intros q IN.
  unfold eclose_once in IN.
  pose proof (eclose_fold_sound M seen seen q IN) as [IN_SEEN | (q1 & IN_SEEN & STEP)].
  - eapply ORIGIN. exact IN_SEEN.
  - pose proof (ORIGIN q1 IN_SEEN) as (q0 & IN_QS & REACH).
    exists q0. split; [exact IN_QS | ].
    change (@nil ascii) with ((@nil ascii) ++ (@nil ascii)).
    eapply ENFA_reachable_app with (q2 := q1).
    + exact REACH.
    + eapply ENFA.reachable_eps with (q2 := q); eauto with *.
Qed.

Lemma eclose_iter_preserves_origin (M : ENFA.t) (qs : list (ENFA.state M)) n seen
  (ORIGIN : has_origin M qs seen)
  : has_origin M qs (iter n (eclose_once M) seen).
Proof.
  revert seen ORIGIN. induction n as [ | n IH]; simpl; intros seen ORIGIN.
  - exact ORIGIN.
  - eapply IH. eapply eclose_once_preserves_origin. exact ORIGIN.
Qed.

Theorem eclose_sound (M : ENFA.t) (qs : list (ENFA.state M)) q
  (IN : L.In q (eclose M qs))
  : exists q0, L.In q0 qs /\ ENFA.reachable M q0 [] q.
Proof.
  unfold eclose in IN.
  pose proof (eclose_iter_preserves_origin M qs (length (ENFA.states M)) _ (union_initial_has_origin M qs)) as ORIGIN.
  unfold has_origin in ORIGIN. eapply ORIGIN. exact IN.
Qed.

Theorem move_sound (M : ENFA.t) (qs : list (ENFA.state M)) (a : ascii) q
  (IN : L.In q (move M qs a))
  : exists q0, exists q1, L.In q0 qs /\ ENFA.reachable M q0 [] q1 /\ L.In q (ENFA.char_step M q1 a).
Proof.
  unfold move in IN. rewrite in_flat_map in IN.
  destruct IN as (q1 & IN_CLOSE & STEP).
  pose proof (eclose_sound M qs q1 IN_CLOSE) as (q0 & IN_QS & REACH).
  exists q0. exists q1. splits; eauto.
Qed.

Theorem subset_step_sound (M : ENFA.t) (S : dstate M) (a : ascii) q
  (IN : L.In q (step M S a))
  : exists q0, exists q1, exists q2, L.In q0 S /\ ENFA.reachable M q0 [] q1 /\ L.In q2 (ENFA.char_step M q1 a) /\ ENFA.reachable M q2 [] q.
Proof.
  unfold step in IN.
  pose proof (eclose_sound M (move M S a) q IN) as (q2 & IN_MOVE & REACH_AFTER).
  pose proof (move_sound M S a q2 IN_MOVE) as (q0 & q1 & IN_S & REACH_BEFORE & STEP).
  exists q0. exists q1. exists q2. splits; eauto.
Qed.

Lemma subset_run_from_sound (M : ENFA.t) (s : list ascii) (S : dstate M) (qD : dstate M) qN
  (RUN : DFA.run_from (compile M) S s = Some qD)
  (IN : L.In qN qD)
  : exists q0, L.In q0 S /\ ENFA.reachable M q0 s qN.
Proof.
  revert S qD qN RUN IN. induction s as [ | a s IH]; simpl; intros S qD qN RUN IN.
  - inv RUN. exists qN. split; eauto with *.
  - pose proof (IH (step M S a) qD qN RUN IN) as (q_after & IN_STEP & REACH_TAIL).
    pose proof (subset_step_sound M S a q_after IN_STEP) as (q0 & q1 & q2 & IN_S & REACH_BEFORE & STEP & REACH_AFTER).
    exists q0. split; [exact IN_S | ].
    change (a :: s) with ((@nil ascii) ++ (a :: s)).
    eapply ENFA_reachable_app with (q2 := q1).
    + exact REACH_BEFORE.
    + eapply ENFA.reachable_char with (q2 := q2).
      * exact STEP.
      * change s with ((@nil ascii) ++ s).
        eapply ENFA_reachable_app with (q2 := q_after).
        { exact REACH_AFTER. }
        { exact REACH_TAIL. }
Qed.

Theorem subset_run_sound (M : ENFA.t) (s : list ascii) (qD : dstate M) qN
  (RUN : DFA.run (compile M) s = Some qD)
  (IN : L.In qN qD)
  : ENFA.reachable M (ENFA.start M) s qN.
Proof.
  unfold DFA.run in RUN.
  pose proof (subset_run_from_sound M s (start M) qD qN RUN IN) as (q0 & IN_START & REACH).
  unfold start in IN_START.
  pose proof (eclose_sound M [ENFA.start M] q0 IN_START) as (q_start & IN_SEED & REACH_START).
  destruct IN_SEED as [EQ | []]. subst q_start.
  change s with ((@nil ascii) ++ s).
  eapply ENFA_reachable_app with (q2 := q0).
  - exact REACH_START.
  - exact REACH.
Qed.

Lemma acceptb_sound (M : ENFA.t) (S : dstate M)
  (ACCEPT : acceptb M S = true)
  : exists q, L.In q S /\ L.In q (ENFA.accept_states M).
Proof.
  unfold acceptb in ACCEPT. rewrite existsb_exists in ACCEPT.
  destruct ACCEPT as (q & IN_S & MEM).
  exists q. split; [exact IN_S | ].
  unfold mem in MEM. destruct (in_dec eq_dec q (ENFA.accept_states M)) as [IN_ACCEPT | NOT_ACCEPT].
  - exact IN_ACCEPT.
  - congruence.
Qed.

Theorem subset_accepts_sound (M : ENFA.t) (s : list ascii)
  (ACCEPTS : DFA.accepts (compile M) s)
  : ENFA.accepts M s.
Proof.
  unfold DFA.accepts in ACCEPTS. destruct ACCEPTS as (qD & RUN & ACCEPT).
  pose proof (acceptb_sound M qD ACCEPT) as (qN & IN_D & IN_ACCEPT).
  exists qN. split.
  - eapply subset_run_sound; eauto.
  - exact IN_ACCEPT.
Qed.

Inductive eps_path (M : ENFA.t) : ENFA.state M -> list (ENFA.state M) -> ENFA.state M -> Prop :=
  | eps_path_nil q
    : eps_path M q [] q
  | eps_path_cons q1 q2 q3 path
    (STEP : L.In q2 (ENFA.eps_step M q1))
    (REST : eps_path M q2 path q3)
    : eps_path M q1 (q2 :: path) q3.

Lemma eclose_fold_base_complete (M : ENFA.t) (seeds : list (ENFA.state M)) (base : list (ENFA.state M)) q
  (IN : L.In q base)
  : L.In q (fold_right (fun q0 => fun acc => @union (ENFA.state M) (ENFA.state_hasEqDec M) (ENFA.eps_step M q0) acc) base seeds).
Proof.
  induction seeds as [ | q0 seeds IH]; simpl.
  - exact IN.
  - eapply union_complete. right. exact IH.
Qed.

Lemma eclose_fold_step_complete (M : ENFA.t) (seeds : list (ENFA.state M)) (base : list (ENFA.state M)) q q'
  (IN : L.In q seeds)
  (STEP : L.In q' (ENFA.eps_step M q))
  : L.In q' (fold_right (fun q0 => fun acc => @union (ENFA.state M) (ENFA.state_hasEqDec M) (ENFA.eps_step M q0) acc) base seeds).
Proof.
  induction seeds as [ | q0 seeds IH]; simpl in IN |- *.
  - contradiction.
  - destruct IN as [EQ | IN].
    + subst q0. eapply union_complete. left. exact STEP.
    + eapply union_complete. right. eapply IH. exact IN.
Qed.

Lemma eclose_once_keeps (M : ENFA.t) (seen : list (ENFA.state M)) q
  (IN : L.In q seen)
  : L.In q (eclose_once M seen).
Proof.
  unfold eclose_once. eapply eclose_fold_base_complete. exact IN.
Qed.

Lemma eclose_once_step_complete (M : ENFA.t) (seen : list (ENFA.state M)) q q'
  (IN : L.In q seen)
  (STEP : L.In q' (ENFA.eps_step M q))
  : L.In q' (eclose_once M seen).
Proof.
  unfold eclose_once. eapply eclose_fold_step_complete; eauto.
Qed.

Lemma iter_succ_r {A : Set} (n : nat) (f : A -> A) (x : A)
  : iter (S n) f x = f (iter n f x).
Proof.
  revert x. induction n as [ | n IH]; intros x.
  - reflexivity.
  - change (iter (S n) f (f x) = f (iter n f (f x))). rewrite (IH (f x)). reflexivity.
Qed.

Lemma eclose_iter_keeps (M : ENFA.t) n seen q
  (IN : L.In q seen)
  : L.In q (iter n (eclose_once M) seen).
Proof.
  revert seen q IN. induction n as [ | n IH]; simpl; intros seen q IN.
  - exact IN.
  - eapply IH. eapply eclose_once_keeps. exact IN.
Qed.

Lemma eclose_iter_more (M : ENFA.t) n m seen q
  (LE : n <= m)
  (IN : L.In q (iter n (eclose_once M) seen))
  : L.In q (iter m (eclose_once M) seen).
Proof.
  revert n seen q LE IN. induction m as [ | m IH]; intros n seen q LE IN.
  - assert (EQ : n = 0) by lia. subst n. exact IN.
  - destruct n as [ | n].
    + eapply eclose_iter_keeps. exact IN.
    + simpl in IN |- *. eapply IH with (n := n); [lia | exact IN].
Qed.

Lemma eps_path_iter_complete (M : ENFA.t) q0 path q seen
  (IN : L.In q0 seen)
  (PATH : eps_path M q0 path q)
  : L.In q (iter (length path) (eclose_once M) seen).
Proof.
  revert seen IN. induction PATH as [q | q1 q2 q3 path STEP REST IH]; simpl; intros seen IN.
  - exact IN.
  - eapply IH. eapply eclose_once_step_complete; eauto.
Qed.

Lemma eps_path_of_reachable_nil (M : ENFA.t) q0 q
  (REACH : ENFA.reachable M q0 [] q)
  : exists path, eps_path M q0 path q.
Proof.
  remember (@nil ascii) as s eqn: EQ. revert EQ. induction REACH as [q | q1 q2 q3 s STEP REST IH | q1 q2 q3 a s STEP REST IH]; intros EQ; inv EQ.
  - exists []. eapply eps_path_nil.
  - pose proof (IH eq_refl) as (path & PATH). exists (q2 :: path). eapply eps_path_cons; eauto.
Qed.

Lemma eps_path_suffix (M : ENFA.t) q0 path q r
  (PATH : eps_path M q0 path q)
  (IN : L.In r (q0 :: path))
  (NODUP : NoDup (q0 :: path))
  : exists suffix, eps_path M r suffix q /\ NoDup (r :: suffix) /\ (forall x, L.In x (r :: suffix) -> L.In x (q0 :: path)).
Proof.
  induction PATH as [q0 | q0 q1 q2 path STEP REST IH].
  - simpl in IN. destruct IN as [EQ | []]. subst r. exists []. split.
    + eapply eps_path_nil.
    + split; [exact NODUP | intros x IN_x; exact IN_x].
  - simpl in IN. destruct IN as [EQ | IN].
    + subst r. exists (q1 :: path). split.
      * eapply eps_path_cons; eauto.
      * split; [exact NODUP | intros x IN_x; exact IN_x].
    + inversion NODUP as [ | ? ? NOT_IN NODUP_TAIL]; subst; clear NODUP.
      pose proof (IH IN NODUP_TAIL) as (suffix & PATH & NODUP & SUB).
      exists suffix. splits; eauto.
      intros x IN_x. right. eapply SUB. exact IN_x.
Qed.

Lemma eps_path_simple (M : ENFA.t) q0 path q
  (PATH : eps_path M q0 path q)
  : exists path', eps_path M q0 path' q /\ NoDup (q0 :: path') /\ (forall x, L.In x (q0 :: path') -> L.In x (q0 :: path)).
Proof.
  induction PATH as [q0 | q0 q1 q2 path STEP REST IH].
  - exists []. split.
    + eapply eps_path_nil.
    + split.
      * constructor; [intros [] | constructor].
      * intros x IN_x. exact IN_x.
  - pose proof IH as (path' & PATH' & NODUP & SUB).
    destruct (in_dec eq_dec q0 (q1 :: path')) as [IN | NOT_IN].
    + pose proof (eps_path_suffix M q1 path' q2 q0 PATH' IN NODUP) as (suffix & PATH_SUFFIX & NODUP_SUFFIX & SUB_SUFFIX).
      exists suffix. split.
      * exact PATH_SUFFIX.
      * split.
        { exact NODUP_SUFFIX. }
        { intros x IN_x. right. eapply SUB. eapply SUB_SUFFIX. exact IN_x. }
    + exists (q1 :: path'). split.
      * eapply eps_path_cons; eauto.
      * split.
        { constructor; [exact NOT_IN | exact NODUP]. }
        { intros x IN_x. simpl in IN_x. destruct IN_x as [EQ | IN_x].
          - subst x. left. reflexivity.
          - right. eapply SUB. exact IN_x.
        }
Qed.

Lemma eps_path_vertices_wf (M : ENFA.t) q0 path q
  (WF : ENFA.wf M)
  (IN0 : L.In q0 (ENFA.states M))
  (PATH : eps_path M q0 path q)
  : forall x, L.In x (q0 :: path) -> L.In x (ENFA.states M).
Proof.
  destruct WF as (_ & _ & EPS_WF & _).
  induction PATH as [q0 | q0 q1 q2 path STEP REST IH]; intros x IN_x.
  - simpl in IN_x. destruct IN_x as [EQ | []]. subst x. exact IN0.
  - simpl in IN_x. destruct IN_x as [EQ | IN_x].
    + subst x. exact IN0.
    + eapply IH.
      * eapply EPS_WF; eauto.
      * exact IN_x.
Qed.

Lemma eps_path_short_bound (M : ENFA.t) q0 path q
  (WF : ENFA.wf M)
  (IN0 : L.In q0 (ENFA.states M))
  (PATH : eps_path M q0 path q)
  : exists path', eps_path M q0 path' q /\ length path' <= length (ENFA.states M).
Proof.
  pose proof (eps_path_simple M q0 path q PATH) as (path' & PATH' & NODUP & SUB).
  assert (INCL : incl (q0 :: path') (ENFA.states M)).
  { intros x IN_x. eapply eps_path_vertices_wf; eauto. }
  pose proof (NoDup_incl_length NODUP INCL) as LENGTH.
  exists path'. split; [exact PATH' | simpl in LENGTH; lia].
Qed.

Theorem eclose_complete (M : ENFA.t) (qs : list (ENFA.state M)) q0 q
  (WF : ENFA.wf M)
  (QS : subset_of_states M qs)
  (IN : L.In q0 qs)
  (REACH : ENFA.reachable M q0 [] q)
  : L.In q (eclose M qs).
Proof.
  pose proof (eps_path_of_reachable_nil M q0 q REACH) as (path & PATH).
  pose proof (eps_path_short_bound M q0 path q WF (QS q0 IN) PATH) as (path' & PATH' & LENGTH).
  unfold eclose.
  eapply eclose_iter_more with (n := length path').
  - exact LENGTH.
  - eapply eps_path_iter_complete.
    + eapply union_complete. left. exact IN.
    + exact PATH'.
Qed.

Theorem eclose_idempotent (M : ENFA.t) (qs : list (ENFA.state M))
  (WF : ENFA.wf M)
  (QS : subset_of_states M qs)
  : forall q, L.In q (eclose M (eclose M qs)) <-> L.In q (eclose M qs).
Proof.
  intros q. split; intros IN.
  - pose proof (eclose_sound M (eclose M qs) q IN) as (q0 & IN0 & REACH).
    pose proof (eclose_sound M qs q0 IN0) as (q1 & IN1 & REACH1).
    assert (REACH' : ENFA.reachable M q1 [] q).
    { change (@nil ascii) with ((@nil ascii) ++ (@nil ascii)). eapply ENFA_reachable_app with (q2 := q0); eauto. }
    eapply eclose_complete with (q0 := q1); eauto.
  - eapply eclose_complete with (q0 := q); eauto with *.
    intros q0 IN0. pose proof (eclose_sound M qs q0 IN0) as (q1 & IN1 & REACH).
    eapply ENFA_reachable_wf; eauto.
Qed.

Lemma eclose_subset_of_states (M : ENFA.t) (qs : list (ENFA.state M))
  (WF : ENFA.wf M)
  (QS : subset_of_states M qs)
  : subset_of_states M (eclose M qs).
Proof.
  intros q IN.
  pose proof (eclose_sound M qs q IN) as (q0 & IN0 & REACH).
  eapply ENFA_reachable_wf; eauto.
Qed.

Theorem move_complete (M : ENFA.t) (qs : list (ENFA.state M)) (a : ascii) q0 q1 q
  (WF : ENFA.wf M)
  (QS : subset_of_states M qs)
  (IN : L.In q0 qs)
  (EPS : ENFA.reachable M q0 [] q1)
  (STEP : L.In q (ENFA.char_step M q1 a))
  : L.In q (move M qs a).
Proof.
  unfold move. rewrite in_flat_map.
  exists q1. split; [ | exact STEP].
  eapply eclose_complete; eauto.
Qed.

Lemma move_subset_of_states (M : ENFA.t) (qs : list (ENFA.state M)) (a : ascii)
  (WF : ENFA.wf M)
  (QS : subset_of_states M qs)
  : subset_of_states M (move M qs a).
Proof.
  intros q IN.
  pose proof (move_sound M qs a q IN) as (q0 & q1 & IN0 & REACH & STEP).
  pose proof WF as WF_COPY.
  destruct WF as (_ & _ & _ & CHAR_WF).
  eapply CHAR_WF with (q := q1) (a := a); [ | exact STEP].
  eapply ENFA_reachable_wf with (q1 := q0) (s := []); eauto.
Qed.

Theorem subset_step_complete (M : ENFA.t) (S : dstate M) (a : ascii) q0 q1 q2 q
  (WF : ENFA.wf M)
  (QS : subset_of_states M S)
  (IN : L.In q0 S)
  (EPS : ENFA.reachable M q0 [] q1)
  (STEP : L.In q2 (ENFA.char_step M q1 a))
  (EPS_AFTER : ENFA.reachable M q2 [] q)
  : L.In q (step M S a).
Proof.
  unfold step.
  eapply eclose_complete with (q0 := q2); eauto.
  - eapply move_subset_of_states; eauto.
  - eapply move_complete with (q0 := q0) (q1 := q1); eauto.
Qed.

Definition eclosed (M : ENFA.t) (S : dstate M) : Prop :=
  forall q0, forall q, L.In q0 S -> ENFA.reachable M q0 [] q -> L.In q S.

Lemma eclose_eclosed (M : ENFA.t) (qs : list (ENFA.state M))
  (WF : ENFA.wf M)
  (QS : subset_of_states M qs)
  : eclosed M (eclose M qs).
Proof.
  intros q0 q IN REACH.
  assert (IN_CLOSE : L.In q (eclose M (eclose M qs))).
  { eapply eclose_complete with (q0 := q0).
    - exact WF.
    - eapply eclose_subset_of_states; eauto.
    - exact IN.
    - exact REACH.
  }
  pose proof (eclose_idempotent M qs WF QS q) as (TO_ORIGINAL & _).
  eapply TO_ORIGINAL. exact IN_CLOSE.
Qed.

Lemma step_subset_of_states (M : ENFA.t) (S : dstate M) (a : ascii)
  (WF : ENFA.wf M)
  (QS : subset_of_states M S)
  : subset_of_states M (step M S a).
Proof.
  unfold step. eapply eclose_subset_of_states; eauto.
  eapply move_subset_of_states; eauto.
Qed.

Lemma step_eclosed (M : ENFA.t) (S : dstate M) (a : ascii)
  (WF : ENFA.wf M)
  (QS : subset_of_states M S)
  : eclosed M (step M S a).
Proof.
  unfold step. eapply eclose_eclosed; eauto.
  eapply move_subset_of_states; eauto.
Qed.

Lemma subset_run_from_complete (M : ENFA.t) (s : list ascii) (q0 : ENFA.state M) (qN : ENFA.state M) (S : dstate M)
  (WF : ENFA.wf M)
  (QS : subset_of_states M S)
  (CLOSED : eclosed M S)
  (IN : L.In q0 S)
  (REACH : ENFA.reachable M q0 s qN)
  : exists qD, DFA.run_from (compile M) S s = Some qD /\ L.In qN qD.
Proof.
  revert S QS CLOSED IN. induction REACH as [q | q1 q2 q3 s STEP REST IH | q1 q2 q3 a s STEP REST IH]; intros S QS CLOSED IN.
  - exists S. split; [reflexivity | exact IN].
  - assert (IN2 : L.In q2 S).
    { eapply CLOSED; [exact IN | ]. eapply ENFA.reachable_eps with (q2 := q2); eauto with *. }
    eapply IH; eauto.
  - simpl.
    pose proof (step_subset_of_states M S a WF QS) as QS_STEP.
    pose proof (step_eclosed M S a WF QS) as CLOSED_STEP.
    assert (IN_STEP : L.In q2 (step M S a)).
    { eapply subset_step_complete with (q0 := q1) (q1 := q1) (q2 := q2); eauto with *. }
    pose proof (IH (step M S a) QS_STEP CLOSED_STEP IN_STEP) as (qD & RUN & IN_D).
    exists qD. split; [exact RUN | exact IN_D].
Qed.

Theorem subset_run_complete (M : ENFA.t) (s : list ascii) qN
  (WF : ENFA.wf M)
  (REACH : ENFA.reachable M (ENFA.start M) s qN)
  : exists qD, DFA.run (compile M) s = Some qD /\ L.In qN qD.
Proof.
  assert (QS_START : subset_of_states M [ENFA.start M]).
  { intros q IN. destruct WF as (START_IN & _). destruct IN as [EQ | []]. subst q. exact START_IN. }
  assert (IN_START : L.In (ENFA.start M) (start M)).
  { unfold start. eapply eclose_complete with (q0 := ENFA.start M); eauto with *. }
  unfold DFA.run.
  eapply subset_run_from_complete with (q0 := ENFA.start M); eauto.
  - unfold start. eapply eclose_subset_of_states; eauto.
  - unfold start. eapply eclose_eclosed; eauto.
Qed.

Lemma acceptb_complete (M : ENFA.t) (S : dstate M) q
  (IN : L.In q S)
  (ACCEPT : L.In q (ENFA.accept_states M))
  : acceptb M S = true.
Proof.
  unfold acceptb. rewrite existsb_exists.
  exists q. split; [exact IN | ].
  unfold mem. destruct (in_dec eq_dec q (ENFA.accept_states M)) as [IN_ACCEPT | NOT_ACCEPT].
  - reflexivity.
  - contradiction.
Qed.

Theorem subset_accepts_complete (M : ENFA.t) (s : list ascii)
  (WF : ENFA.wf M)
  (ACCEPTS : ENFA.accepts M s)
  : DFA.accepts (compile M) s.
Proof.
  unfold ENFA.accepts in ACCEPTS. destruct ACCEPTS as (qN & REACH & ACCEPT).
  pose proof (subset_run_complete M s qN WF REACH) as (qD & RUN & IN_D).
  exists qD. split.
  - exact RUN.
  - eapply acceptb_complete; eauto.
Qed.

Corollary subset_language_equiv (M : ENFA.t) (s : list ascii)
  (WF : ENFA.wf M)
  : DFA.accepts (compile M) s <-> ENFA.accepts M s.
Proof.
  split; intros ACCEPTS.
  - eapply subset_accepts_sound; eauto.
  - eapply subset_accepts_complete; eauto.
Qed.

End Subset.

Module RegexCompiler.

Definition to_enfa (e : regex ascii) : ENFA.t :=
  Thompson.to_enfa e.

Theorem to_enfa_wf (e : regex ascii)
  : ENFA.wf (to_enfa e).
Proof.
  eapply Thompson.to_enfa_wf.
Qed.

Theorem to_enfa_sound (e : regex ascii) (s : list ascii)
  (ACCEPTS : ENFA.accepts (to_enfa e) s)
  : s \in eval_regex e.
Proof.
  eapply Thompson.to_enfa_sound; eauto.
Qed.

Theorem to_enfa_complete (e : regex ascii) (s : list ascii)
  (IN : s \in eval_regex e)
  : ENFA.accepts (to_enfa e) s.
Proof.
  eapply Thompson.to_enfa_complete; eauto.
Qed.

Definition enfa_to_dfa (M : ENFA.t) : Error.t + DFA.t :=
  inr (Subset.compile M).

Definition compile (e : regex ascii) : Error.t + DFA.t :=
  enfa_to_dfa (to_enfa e).

Definition recognize (e : regex ascii) (s : list ascii) : bool :=
  match compile e with
  | inl _ => false
  | inr D => DFA.acceptsb D s
  end.

Theorem to_enfa_empty_accepts_nil
  : ENFA.accepts (to_enfa Re.Empty) [].
Proof.
  exists 1. split.
  - eapply ENFA.reachable_eps with (q2 := 1); simpl; eauto with *.
  - simpl. eauto with *.
Qed.

Theorem to_enfa_char_accepts_single (c : ascii)
  : ENFA.accepts (to_enfa (Re.Char c)) [c].
Proof.
  exists 1. split.
  - eapply ENFA.reachable_char with (q2 := 1); simpl; eauto with *.
    destruct (Ascii.ascii_dec c c) as [_ | NE]; [eauto with * | contradiction].
  - simpl. eauto with *.
Qed.

End RegexCompiler.

Inductive rule_kind : Set :=
  | Emit (tok : Token.t)
  | Skip.

#[global]
Instance rule_kind_hasEqDec
  : hasEqDec@{Set} rule_kind.
Proof.
  red. decide equality. eapply eq_dec.
Defined.

#[projections(primitive)]
Record raw_rule : Set :=
  mkRawRule
  { raw_rule_index : nat
  ; raw_rule_kind : rule_kind
  ; raw_rule_regex : regex ascii
  }.

#[projections(primitive)]
Record accept_tag : Set :=
  mkAcceptTag
  { accept_rule_index : nat
  ; accept_kind : rule_kind
  }.

#[global]
Instance accept_tag_hasEqDec
  : hasEqDec@{Set} accept_tag.
Proof.
  red. decide equality; eapply eq_dec.
Defined.

#[projections(primitive)]
Record compiled_rule : Set :=
  mkCompiledRule
  { compiled_rule_index : nat
  ; compiled_rule_kind : rule_kind
  ; compiled_rule_regex : regex ascii
  }.

#[projections(primitive)]
Record lex_dfa : Type :=
  mkLexDFA
  { lex_core : DFA.t
  ; lex_accepts : DFA.state lex_core -> list accept_tag
  ; lex_best : DFA.state lex_core -> option accept_tag
  }.

Definition token_raw_rules : list raw_rule :=
  L.mapi_from 0 (fun idx => fun rule => mkRawRule idx (Emit (fst rule)) (snd rule)) Token.rules.

Definition skip_raw_rules : list raw_rule :=
  L.mapi_from (length Token.rules) (fun idx => fun e => mkRawRule idx Skip e) Token.skips.

Definition all_raw_rules : list raw_rule :=
  token_raw_rules ++ skip_raw_rules.

Definition empty_rule_error (r : raw_rule) : Error.t :=
  match r.(raw_rule_kind) with
  | Emit _ => Error.EmptyTokenRule r.(raw_rule_index)
  | Skip => Error.EmptySkipRule r.(raw_rule_index)
  end.

Definition compile_rule (r : raw_rule) : ErrM compiled_rule :=
  if nullable r.(raw_rule_regex) then
    inl (empty_rule_error r)
  else
    inr (mkCompiledRule r.(raw_rule_index) r.(raw_rule_kind) r.(raw_rule_regex)).

Fixpoint compile_rules_loop (rs : list raw_rule) {struct rs} : ErrM (list compiled_rule) :=
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
  compile_rules_loop all_raw_rules.

Definition compiled_rules_wf (crs : list compiled_rule) : Prop :=
  forall cr, L.In cr crs -> (exists r, L.In r all_raw_rules /\ compile_rule r = inr cr).

Definition rule_accepts (r : raw_rule) (s : list ascii) : Prop :=
  s \in eval_regex r.(raw_rule_regex).

Definition compiled_rule_accepts (r : compiled_rule) (s : list ascii) : Prop :=
  s \in eval_regex r.(compiled_rule_regex).

Theorem compile_rule_sound (r : raw_rule) (cr : compiled_rule) (s : list ascii)
  (COMPILE : compile_rule r = inr cr)
  (ACCEPTS : compiled_rule_accepts cr s)
  : rule_accepts r s.
Proof.
  unfold compile_rule in COMPILE. destruct (nullable r.(raw_rule_regex)) eqn: NULLABLE; inv COMPILE.
  exact ACCEPTS.
Qed.

Theorem compile_rule_complete (r : raw_rule) (cr : compiled_rule) (s : list ascii)
  (COMPILE : compile_rule r = inr cr)
  (ACCEPTS : rule_accepts r s)
  : compiled_rule_accepts cr s.
Proof.
  unfold compile_rule in COMPILE. destruct (nullable r.(raw_rule_regex)) eqn: NULLABLE; inv COMPILE.
  exact ACCEPTS.
Qed.

Theorem compile_rule_nonempty (r : raw_rule) (cr : compiled_rule)
  (COMPILE : compile_rule r = inr cr)
  : ~ compiled_rule_accepts cr [].
Proof.
  unfold compile_rule in COMPILE. destruct (nullable r.(raw_rule_regex)) eqn: NULLABLE; inv COMPILE.
  unfold compiled_rule_accepts. simpl. rewrite <- nullable_false_spec. exact NULLABLE.
Qed.

Lemma compile_rules_loop_sound (rs : list raw_rule) (crs : list compiled_rule)
  (COMPILE : compile_rules_loop rs = inr crs)
  : forall cr, L.In cr crs -> (exists r, L.In r rs /\ compile_rule r = inr cr).
Proof.
  revert crs COMPILE. induction rs as [ | r rs IH]; intros crs COMPILE cr IN; simpl in COMPILE.
  - inv COMPILE. contradiction.
  - destruct (compile_rule r) as [err | cr'] eqn: COMPILE1; try congruence.
    destruct (compile_rules_loop rs) as [err | crs'] eqn: COMPILE2; try congruence. inv COMPILE.
    destruct IN as [EQ | IN].
    + subst cr. exists r. split; [left; reflexivity | exact COMPILE1].
    + pose proof (IH crs' eq_refl cr IN) as (r' & IN' & COMPILE'). exists r'. split; [right; exact IN' | exact COMPILE'].
Qed.

Theorem compile_rules_sound (crs : list compiled_rule)
  (COMPILE : compile_rules = inr crs)
  : forall cr, L.In cr crs -> (exists r, L.In r all_raw_rules /\ compile_rule r = inr cr).
Proof.
  unfold compile_rules in COMPILE. eapply compile_rules_loop_sound; eauto.
Qed.

Theorem compile_rules_wf (crs : list compiled_rule)
  (COMPILE : compile_rules = inr crs)
  : compiled_rules_wf crs.
Proof.
  exact (compile_rules_sound crs COMPILE).
Qed.

Definition tag_of_compiled_rule (cr : compiled_rule) : accept_tag :=
  mkAcceptTag cr.(compiled_rule_index) cr.(compiled_rule_kind).

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

Definition lookup_compiled_rule (crs : list compiled_rule) (key : nat) : option compiled_rule :=
  nth_error crs key.

Definition compiled_rule_start_state (entry : nat * compiled_rule) : tagged_state :=
  let key := fst entry in
  let cr := snd entry in
  Some (key, (compiled_rule_fragment cr).(Thompson.frag_start)).

Definition compiled_rule_accept_state (entry : nat * compiled_rule) : tagged_state :=
  let key := fst entry in
  let cr := snd entry in
  Some (key, (compiled_rule_fragment cr).(Thompson.frag_accept)).

Definition compiled_rule_states (entry : nat * compiled_rule) : list tagged_state :=
  let key := fst entry in
  let cr := snd entry in
  map (fun q => Some (key, q)) (seq 0 (compiled_rule_fragment cr).(Thompson.frag_size)).

Definition tagged_states (crs : list compiled_rule) : list tagged_state :=
  None :: flat_map compiled_rule_states (compiled_rule_table crs).

Definition tagged_accept_states (crs : list compiled_rule) : list tagged_state :=
  map compiled_rule_accept_state (compiled_rule_table crs).

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

Definition tagged_state_tags (crs : list compiled_rule) (q : tagged_state) : list accept_tag :=
  match q with
  | None => []
  | Some (key, q0) =>
    match lookup_compiled_rule crs key with
    | None => []
    | Some cr =>
      if Nat.eq_dec q0 (compiled_rule_fragment cr).(Thompson.frag_accept) then
        [tag_of_compiled_rule cr]
      else
        []
    end
  end.

#[projections(primitive)]
Record tagged_enfa : Type :=
  mkTaggedENFA
  { tagged_core : ENFA.t
  ; tagged_tags : ENFA.state tagged_core -> list accept_tag
  }.

Definition build_tagged_enfa (crs : list compiled_rule) : tagged_enfa :=
  let M := ENFA.mk tagged_state tagged_state_hasEqDec (tagged_states crs) None (tagged_accept_states crs) (tagged_eps_step crs) (tagged_char_step crs) in
  mkTaggedENFA M (tagged_state_tags crs).

Definition tagged_accepts (TM : tagged_enfa) (tag : accept_tag) (s : list ascii) : Prop :=
  exists q, ENFA.reachable TM.(tagged_core) (ENFA.start TM.(tagged_core)) s q /\ L.In tag (tagged_tags TM q).

Lemma lookup_compiled_rule_in (crs : list compiled_rule) (key : nat) (cr : compiled_rule)
  (LOOKUP : lookup_compiled_rule crs key = Some cr)
  : L.In cr crs.
Proof.
  unfold lookup_compiled_rule in LOOKUP. eapply nth_error_In. exact LOOKUP.
Qed.

Lemma compiled_rule_table_lookup_in_from (base : nat) (crs : list compiled_rule) (key : nat) (cr : compiled_rule)
  (LOOKUP : nth_error crs key = Some cr)
  : L.In (base + key, cr) (L.mapi_from base (fun key => fun cr => (key, cr)) crs).
Proof.
  revert base key LOOKUP. induction crs as [ | cr0 crs IH]; intros base key LOOKUP.
  - destruct key; simpl in LOOKUP; congruence.
  - destruct key as [ | key]; simpl in LOOKUP.
    + inv LOOKUP. left. rewrite Nat.add_0_r. reflexivity.
    + right. replace (base + S key) with (S base + key) by lia.
      eapply IH. exact LOOKUP.
Qed.

Lemma compiled_rule_table_lookup_in (crs : list compiled_rule) (key : nat) (cr : compiled_rule)
  (LOOKUP : lookup_compiled_rule crs key = Some cr)
  : L.In (key, cr) (compiled_rule_table crs).
Proof.
  unfold lookup_compiled_rule in LOOKUP. unfold compiled_rule_table.
  replace key with (0 + key) by lia.
  eapply compiled_rule_table_lookup_in_from. exact LOOKUP.
Qed.

Lemma compiled_rule_table_in_lookup_from (base : nat) (crs : list compiled_rule) (key : nat) (cr : compiled_rule)
  (IN : L.In (key, cr) (L.mapi_from base (fun key => fun cr => (key, cr)) crs))
  : exists n, key = base + n /\ nth_error crs n = Some cr.
Proof.
  revert base key cr IN. induction crs as [ | cr0 crs IH]; intros base key cr IN; simpl in IN.
  - contradiction.
  - destruct IN as [EQ | IN].
    + inv EQ. exists 0. split; simpl; [lia | reflexivity].
    + pose proof (IH (S base) key cr IN) as (n & KEY & LOOKUP).
      exists (S n). split; simpl; [lia | exact LOOKUP].
Qed.

Lemma compiled_rule_table_in_lookup (crs : list compiled_rule) (key : nat) (cr : compiled_rule)
  (IN : L.In (key, cr) (compiled_rule_table crs))
  : lookup_compiled_rule crs key = Some cr.
Proof.
  unfold compiled_rule_table in IN. unfold lookup_compiled_rule.
  pose proof (compiled_rule_table_in_lookup_from 0 crs key cr IN) as (n & KEY & LOOKUP).
  replace key with n by lia. exact LOOKUP.
Qed.

Lemma compiled_rule_state_in (crs : list compiled_rule) (key : nat) (cr : compiled_rule) q
  (IN : L.In (key, cr) (compiled_rule_table crs))
  (BOUND : q < (compiled_rule_fragment cr).(Thompson.frag_size))
  : L.In (Some (key, q)) (tagged_states crs).
Proof.
  unfold tagged_states. simpl. right. rewrite in_flat_map.
  exists (key, cr). split; [exact IN | ].
  unfold compiled_rule_states. simpl. rewrite in_map_iff. exists q. split; [reflexivity | ].
  rewrite L.in_seq. split; lia.
Qed.

Lemma compiled_rule_start_state_in (crs : list compiled_rule) (entry : nat * compiled_rule)
  (IN : L.In entry (compiled_rule_table crs))
  : L.In (compiled_rule_start_state entry) (tagged_states crs).
Proof.
  destruct entry as [key cr]. unfold compiled_rule_start_state. eapply compiled_rule_state_in; eauto.
  unfold compiled_rule_fragment. eapply Thompson.compile_start_lt_size.
Qed.

Lemma compiled_rule_accept_state_in (crs : list compiled_rule) (entry : nat * compiled_rule)
  (IN : L.In entry (compiled_rule_table crs))
  : L.In (compiled_rule_accept_state entry) (tagged_states crs).
Proof.
  destruct entry as [key cr]. unfold compiled_rule_accept_state. eapply compiled_rule_state_in; eauto.
  unfold compiled_rule_fragment. eapply Thompson.compile_accept_lt_size.
Qed.

Theorem build_tagged_enfa_wf (crs : list compiled_rule)
  : ENFA.wf (tagged_core (build_tagged_enfa crs)).
Proof.
  unfold build_tagged_enfa. simpl. unfold ENFA.wf. splits.
  - simpl. left. reflexivity.
  - change (forall q, L.In q (tagged_accept_states crs) -> L.In q (tagged_states crs)).
    intros q IN. unfold tagged_accept_states in IN. rewrite in_map_iff in IN.
    destruct IN as (entry & EQ & IN). subst q. eapply compiled_rule_accept_state_in. exact IN.
  - change (forall q, forall q', L.In q (tagged_states crs) -> L.In q' (tagged_eps_step crs q) -> L.In q' (tagged_states crs)).
    intros q q' IN_STATE STEP. destruct q as [[idx q0] | ].
    + unfold tagged_eps_step in STEP. destruct (lookup_compiled_rule crs idx) as [cr | ] eqn: LOOKUP; [ | contradiction].
      rewrite in_map_iff in STEP. destruct STEP as (q1 & EQ & STEP). inv EQ.
      eapply compiled_rule_state_in.
      * eapply compiled_rule_table_lookup_in. exact LOOKUP.
      * unfold compiled_rule_fragment. pose proof (Thompson.compile_edges_in_bounds (compiled_rule_regex cr)) as (EPS & _).
        eapply Thompson.eps_step_of_bound; eauto.
    + unfold tagged_eps_step in STEP. rewrite in_map_iff in STEP.
      destruct STEP as (entry & EQ & IN). subst q'. eapply compiled_rule_start_state_in. exact IN.
  - change (forall q, forall q', forall a, L.In q (tagged_states crs) -> L.In q' (tagged_char_step crs q a) -> L.In q' (tagged_states crs)).
    intros q q' a IN_STATE STEP. destruct q as [[idx q0] | ].
    + unfold tagged_char_step in STEP. destruct (lookup_compiled_rule crs idx) as [cr | ] eqn: LOOKUP; [ | contradiction].
      rewrite in_map_iff in STEP. destruct STEP as (q1 & EQ & STEP). inv EQ.
      eapply compiled_rule_state_in.
      * eapply compiled_rule_table_lookup_in. exact LOOKUP.
      * unfold compiled_rule_fragment. pose proof (Thompson.compile_edges_in_bounds (compiled_rule_regex cr)) as (_ & CHAR).
        eapply Thompson.char_step_of_bound; eauto.
    + unfold tagged_char_step in STEP. contradiction.
Qed.

Lemma tagged_inside_reachable_complete (crs : list compiled_rule) (key : nat) (cr : compiled_rule) (q0 : nat) (q : nat) (s : list ascii)
  (LOOKUP : lookup_compiled_rule crs key = Some cr)
  (REACH : ENFA.reachable (Thompson.of_fragment (compiled_rule_fragment cr)) q0 s q)
  : ENFA.reachable (tagged_core (build_tagged_enfa crs)) (Some (key, q0)) s (Some (key, q)).
Proof.
  induction REACH as [q | q1 q2 q3 s STEP REST IH | q1 q2 q3 a s STEP REST IH].
  - eauto with *.
  - eapply ENFA.reachable_eps with (q2 := Some (key, q2)); eauto.
    simpl. unfold tagged_eps_step. rewrite LOOKUP. rewrite in_map_iff.
    exists q2. split; [reflexivity | exact STEP].
  - eapply ENFA.reachable_char with (q2 := Some (key, q2)); eauto.
    simpl. unfold tagged_char_step. rewrite LOOKUP. rewrite in_map_iff.
    exists q2. split; [reflexivity | exact STEP].
Qed.

Lemma tagged_inside_reachable_sound (crs : list compiled_rule) (key : nat) (cr : compiled_rule) (q0 : nat) (qT : tagged_state) (s : list ascii)
  (LOOKUP : lookup_compiled_rule crs key = Some cr)
  (REACH : ENFA.reachable (tagged_core (build_tagged_enfa crs)) (Some (key, q0)) s qT)
  : exists q, qT = Some (key, q) /\ ENFA.reachable (Thompson.of_fragment (compiled_rule_fragment cr)) q0 s q.
Proof.
  remember (Some (key, q0)) as src eqn: SRC. revert key cr q0 LOOKUP SRC.
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

Lemma tagged_start_reachable_sound (crs : list compiled_rule) (qT : tagged_state) (s : list ascii)
  (REACH : ENFA.reachable (tagged_core (build_tagged_enfa crs)) None s qT)
  : qT = None /\ s = [] \/ (exists key, exists cr, exists q, lookup_compiled_rule crs key = Some cr /\ qT = Some (key, q) /\ ENFA.reachable (Thompson.of_fragment (compiled_rule_fragment cr)) (Thompson.frag_start (compiled_rule_fragment cr)) s q).
Proof.
  inv REACH.
  - left. split; reflexivity.
  - right. simpl in STEP. unfold tagged_eps_step in STEP. rewrite in_map_iff in STEP.
    destruct STEP as (entry & EQ & IN). destruct entry as [key cr]. simpl in EQ. inv EQ.
    pose proof (compiled_rule_table_in_lookup crs key cr IN) as LOOKUP.
    pose proof (tagged_inside_reachable_sound crs key cr (Thompson.frag_start (compiled_rule_fragment cr)) qT s LOOKUP REST) as (q & TARGET & BODY).
    exists key. exists cr. exists q. splits; eauto.
  - simpl in STEP. unfold tagged_char_step in STEP. contradiction.
Qed.

Theorem build_tagged_enfa_complete (crs : list compiled_rule) (key : nat) (cr : compiled_rule) (s : list ascii)
  (LOOKUP : lookup_compiled_rule crs key = Some cr)
  (ACCEPTS : compiled_rule_accepts cr s)
  : tagged_accepts (build_tagged_enfa crs) (tag_of_compiled_rule cr) s.
Proof.
  unfold compiled_rule_accepts in ACCEPTS.
  pose proof (Thompson.compile_complete cr.(compiled_rule_regex) s ACCEPTS) as REACH.
  unfold tagged_accepts. exists (Some (key, (compiled_rule_fragment cr).(Thompson.frag_accept))).
  split.
  - simpl. eapply ENFA.reachable_eps with (q2 := Some (key, (compiled_rule_fragment cr).(Thompson.frag_start))).
    + simpl. unfold tagged_eps_step. rewrite in_map_iff.
      exists (key, cr). split; [reflexivity | ].
      eapply compiled_rule_table_lookup_in. exact LOOKUP.
    + eapply tagged_inside_reachable_complete; eauto.
  - simpl. unfold tagged_state_tags. rewrite LOOKUP.
    destruct (Nat.eq_dec (Thompson.frag_accept (compiled_rule_fragment cr)) (Thompson.frag_accept (compiled_rule_fragment cr))) as [_ | NE].
    + left. reflexivity.
    + contradiction.
Qed.

Theorem build_tagged_enfa_complete_in (crs : list compiled_rule) (cr : compiled_rule) (s : list ascii)
  (IN : L.In cr crs)
  (ACCEPTS : compiled_rule_accepts cr s)
  : exists key, tagged_accepts (build_tagged_enfa crs) (tag_of_compiled_rule cr) s /\ lookup_compiled_rule crs key = Some cr.
Proof.
  pose proof (L.In_nth_error_Some crs cr IN) as (key & LOOKUP & _).
  exists key. split; [ | exact LOOKUP].
  eapply build_tagged_enfa_complete; eauto.
Qed.

Theorem build_tagged_enfa_sound (crs : list compiled_rule) (tag : accept_tag) (s : list ascii)
  (ACCEPTS : tagged_accepts (build_tagged_enfa crs) tag s)
  : exists key, exists cr, lookup_compiled_rule crs key = Some cr /\ tag = tag_of_compiled_rule cr /\ compiled_rule_accepts cr s.
Proof.
  unfold tagged_accepts in ACCEPTS. destruct ACCEPTS as (q & REACH & TAG).
  pose proof (tagged_start_reachable_sound crs q s REACH) as [(Q_NONE & S_NIL) | (key & cr & q0 & LOOKUP & TARGET & BODY)].
  - subst q. simpl in TAG. contradiction.
  - subst q. simpl in TAG.
  unfold tagged_state_tags in TAG. rewrite LOOKUP in TAG.
  destruct (Nat.eq_dec q0 (Thompson.frag_accept (compiled_rule_fragment cr))) as [ACCEPT_EQ | NE].
  + simpl in TAG. destruct TAG as [TAG_EQ | []]. subst tag.
    exists key. exists cr. splits; [exact LOOKUP | reflexivity | ].
    unfold compiled_rule_accepts. eapply Thompson.compile_sound.
    unfold Thompson.fragment_accepts.
    change (ENFA.reachable (Thompson.of_fragment (compiled_rule_fragment cr)) (Thompson.frag_start (compiled_rule_fragment cr)) s (Thompson.frag_accept (compiled_rule_fragment cr))).
    rewrite <- ACCEPT_EQ. exact BODY.
  + simpl in TAG. contradiction.
Qed.

Corollary build_tagged_enfa_language_equiv (crs : list compiled_rule) (tag : accept_tag) (s : list ascii)
  : tagged_accepts (build_tagged_enfa crs) tag s <-> (exists key, exists cr, lookup_compiled_rule crs key = Some cr /\ tag = tag_of_compiled_rule cr /\ compiled_rule_accepts cr s).
Proof.
  split; intros ACCEPTS.
  - eapply build_tagged_enfa_sound. exact ACCEPTS.
  - destruct ACCEPTS as (key & cr & LOOKUP & TAG & RULE_ACCEPTS). subst tag.
    eapply build_tagged_enfa_complete; eauto.
Qed.

Definition choose_best_tag (tag : accept_tag) (best : option accept_tag) : option accept_tag :=
  match best with
  | None => Some tag
  | Some best_tag =>
    if Nat.leb tag.(accept_rule_index) best_tag.(accept_rule_index) then
      Some tag
    else
      Some best_tag
  end.

Definition best_tag (tags : list accept_tag) : option accept_tag :=
  fold_right choose_best_tag None tags.

Lemma best_tag_none_empty (tags : list accept_tag)
  (NONE : best_tag tags = None)
  : tags = [].
Proof.
  induction tags as [ | tag tags IH]; simpl in NONE.
  - reflexivity.
  - unfold choose_best_tag in NONE. destruct (best_tag tags) as [best | ] eqn: BEST.
    + destruct (Nat.leb (accept_rule_index tag) (accept_rule_index best)); congruence.
    + congruence.
Qed.

Lemma best_tag_sound (tags : list accept_tag) tag
  (BEST : best_tag tags = Some tag)
  : L.In tag tags.
Proof.
  revert tag BEST. induction tags as [ | tag0 tags IH]; intros tag BEST; simpl in BEST.
  - congruence.
  - unfold choose_best_tag in BEST. destruct (best_tag tags) as [best | ] eqn: BEST_TAIL.
    + destruct (Nat.leb (accept_rule_index tag0) (accept_rule_index best)) eqn: LE; inv BEST.
      * left. reflexivity.
      * right. eapply IH. reflexivity.
    + inv BEST. left. reflexivity.
Qed.

Lemma best_tag_priority (tags : list accept_tag) tag tag'
  (BEST : best_tag tags = Some tag)
  (IN : L.In tag' tags)
  : tag.(accept_rule_index) <= tag'.(accept_rule_index).
Proof.
  revert tag tag' BEST IN. induction tags as [ | tag0 tags IH]; intros tag tag' BEST IN; simpl in BEST, IN.
  - contradiction.
  - unfold choose_best_tag in BEST. destruct (best_tag tags) as [best | ] eqn: BEST_TAIL.
    + destruct (Nat.leb (accept_rule_index tag0) (accept_rule_index best)) eqn: LE; inv BEST.
      * eapply Nat.leb_le in LE. destruct IN as [EQ | IN].
        { subst tag'. lia. }
        { pose proof (IH best tag' eq_refl IN) as PRIORITY. lia. }
      * eapply Nat.leb_gt in LE. destruct IN as [EQ | IN].
        { subst tag'. lia. }
        { pose proof (IH tag tag' eq_refl IN) as PRIORITY. exact PRIORITY. }
    + inv BEST. pose proof (best_tag_none_empty tags BEST_TAIL) as EMPTY. subst tags.
      destruct IN as [EQ | []]. subst tag'. lia.
Qed.

Definition lex_dfa_of_tagged (TM : tagged_enfa) : lex_dfa :=
  let D := Subset.compile TM.(tagged_core) in
  mkLexDFA D (fun q => flat_map TM.(tagged_tags) q) (fun q => best_tag (flat_map TM.(tagged_tags) q)).

Definition determinize_tagged (TM : tagged_enfa) : ErrM lex_dfa :=
  inr (lex_dfa_of_tagged TM).

Theorem lex_best_sound (TM : tagged_enfa) (q : DFA.state (lex_core (lex_dfa_of_tagged TM))) tag
  (BEST : lex_best (lex_dfa_of_tagged TM) q = Some tag)
  : L.In tag (lex_accepts (lex_dfa_of_tagged TM) q).
Proof.
  simpl in *. eapply best_tag_sound. exact BEST.
Qed.

Theorem lex_best_priority (TM : tagged_enfa) (q : DFA.state (lex_core (lex_dfa_of_tagged TM))) tag tag'
  (BEST : lex_best (lex_dfa_of_tagged TM) q = Some tag)
  (IN : L.In tag' (lex_accepts (lex_dfa_of_tagged TM) q))
  : tag.(accept_rule_index) <= tag'.(accept_rule_index).
Proof.
  simpl in *. eapply best_tag_priority; eauto.
Qed.

Theorem lex_accepts_sound (TM : tagged_enfa) (q : DFA.state (lex_core (lex_dfa_of_tagged TM))) tag
  (TAG : L.In tag (lex_accepts (lex_dfa_of_tagged TM) q))
  : exists qN, L.In qN q /\ L.In tag (tagged_tags TM qN).
Proof.
  simpl in TAG. rewrite in_flat_map in TAG.
  destruct TAG as (qN & IN_Q & IN_TAG). exists qN. split; eauto.
Qed.

Theorem lex_accepts_complete (TM : tagged_enfa) (q : DFA.state (lex_core (lex_dfa_of_tagged TM))) qN tag
  (IN : L.In qN q)
  (TAG : L.In tag (tagged_tags TM qN))
  : L.In tag (lex_accepts (lex_dfa_of_tagged TM) q).
Proof.
  simpl. rewrite in_flat_map. exists qN. split; eauto.
Qed.

Theorem lex_accepts_run_sound (TM : tagged_enfa) input q tag
  (RUN : DFA.run (lex_core (lex_dfa_of_tagged TM)) input = Some q)
  (TAG : L.In tag (lex_accepts (lex_dfa_of_tagged TM) q))
  : exists qN, ENFA.reachable TM.(tagged_core) (ENFA.start TM.(tagged_core)) input qN /\ L.In tag (tagged_tags TM qN).
Proof.
  pose proof (lex_accepts_sound TM q tag TAG) as (qN & IN_Q & IN_TAG).
  exists qN. split; [ | exact IN_TAG].
  eapply Subset.subset_run_sound; eauto.
Qed.

Theorem lex_accepts_run_complete (TM : tagged_enfa) input qN tag
  (WF : ENFA.wf TM.(tagged_core))
  (REACH : ENFA.reachable TM.(tagged_core) (ENFA.start TM.(tagged_core)) input qN)
  (TAG : L.In tag (tagged_tags TM qN))
  : exists q, DFA.run (lex_core (lex_dfa_of_tagged TM)) input = Some q /\ L.In tag (lex_accepts (lex_dfa_of_tagged TM) q).
Proof.
  pose proof (Subset.subset_run_complete TM.(tagged_core) input qN WF REACH) as (q & RUN & IN_Q).
  exists q. split; [exact RUN | ].
  eapply lex_accepts_complete; eauto.
Qed.

#[projections(primitive)]
Record match_result : Set :=
  mkMatchResult
  { matched_rule_index : nat
  ; matched_kind : rule_kind
  ; matched_lexeme : list ascii
  ; matched_rest : list ascii
  }.

#[projections(primitive)]
Record t : Type :=
  mk
  { lexer_rules : list compiled_rule
  ; lexer_rules_wf : compiled_rules_wf lexer_rules
  ; lexer_dfa : lex_dfa
  ; lexer_dfa_sound : forall input, forall q, forall tag, DFA.run lexer_dfa.(lex_core) input = Some q -> lexer_dfa.(lex_best) q = Some tag -> (exists key, exists cr, lookup_compiled_rule lexer_rules key = Some cr /\ tag = tag_of_compiled_rule cr /\ compiled_rule_accepts cr input)
  }.

Inductive accepted_prefix (lexer : lex_dfa) (input : list ascii) : list ascii -> list ascii -> accept_tag -> Prop :=
  | accepted_prefix_intro prefix rest tag q
    (SPLIT : input = prefix ++ rest)
    (NONEMPTY : prefix <> [])
    (RUN : DFA.run lexer.(lex_core) prefix = Some q)
    (BEST : lexer.(lex_best) q = Some tag)
    : accepted_prefix lexer input prefix rest tag.

Inductive first_dfa_match (lexer : lex_dfa) (input : list ascii) : list ascii -> list ascii -> accept_tag -> Prop :=
  | first_dfa_match_intro prefix rest tag
    (ACCEPTED : accepted_prefix lexer input prefix rest tag)
    (LONGEST : forall prefix' rest' tag', accepted_prefix lexer input prefix' rest' tag' -> length prefix' <= length prefix)
    (PRIORITY : forall prefix' rest' tag', accepted_prefix lexer input prefix' rest' tag' -> length prefix' = length prefix -> tag.(accept_rule_index) <= tag'.(accept_rule_index))
    : first_dfa_match lexer input prefix rest tag.

Definition match_of_tag (prefix : list ascii) (rest : list ascii) (tag : accept_tag) : match_result :=
  mkMatchResult tag.(accept_rule_index) tag.(accept_kind) prefix rest.

Definition tag_of_match (m : match_result) : accept_tag :=
  mkAcceptTag m.(matched_rule_index) m.(matched_kind).

Definition input_lt (input1 : list ascii) (input2 : list ascii) : Prop :=
  length input1 < length input2.

Lemma tag_of_match_of_tag (prefix : list ascii) (rest : list ascii) (tag : accept_tag)
  : tag_of_match (match_of_tag prefix rest tag) = tag.
Proof.
  destruct tag as [idx kind]. reflexivity.
Qed.

Lemma match_of_tag_of_match (m : match_result)
  : match_of_tag m.(matched_lexeme) m.(matched_rest) (tag_of_match m) = m.
Proof.
  destruct m as [idx kind lexeme rest]. reflexivity.
Qed.

Lemma accepted_prefix_same_length (lexer : lex_dfa) (input : list ascii) (prefix1 : list ascii) (rest1 : list ascii) (tag1 : accept_tag) (prefix2 : list ascii) (rest2 : list ascii) (tag2 : accept_tag)
  (ACCEPTED1 : accepted_prefix lexer input prefix1 rest1 tag1)
  (ACCEPTED2 : accepted_prefix lexer input prefix2 rest2 tag2)
  (LEN : length prefix1 = length prefix2)
  : prefix1 = prefix2 /\ rest1 = rest2 /\ tag1 = tag2.
Proof.
  inv ACCEPTED1. inv ACCEPTED2.
  assert (APP : prefix1 ++ rest1 = prefix2 ++ rest2).
  { congruence. }
  pose proof (L.app_eq_length_inv prefix1 rest1 prefix2 rest2 APP LEN) as (PREFIX & REST).
  subst prefix2 rest2. rewrite RUN in RUN0. inv RUN0. rewrite BEST in BEST0. inv BEST0. eauto.
Qed.

Lemma first_dfa_match_unique (lexer : lex_dfa) (input : list ascii) (prefix1 : list ascii) (rest1 : list ascii) (tag1 : accept_tag) (prefix2 : list ascii) (rest2 : list ascii) (tag2 : accept_tag)
  (MATCH1 : first_dfa_match lexer input prefix1 rest1 tag1)
  (MATCH2 : first_dfa_match lexer input prefix2 rest2 tag2)
  : prefix1 = prefix2 /\ rest1 = rest2 /\ tag1 = tag2.
Proof.
  inv MATCH1. inv MATCH2.
  pose proof (LONGEST prefix2 rest2 tag2 ACCEPTED0) as LE12.
  pose proof (LONGEST0 prefix1 rest1 tag1 ACCEPTED) as LE21.
  eapply accepted_prefix_same_length; eauto. lia.
Qed.

Lemma DFA_run_snoc (M : DFA.t) (q : DFA.state M) (q' : DFA.state M) (prefix : list ascii) (c : ascii)
  (RUN : DFA.run M prefix = Some q)
  (STEP : DFA.step M q c = Some q')
  : DFA.run M (prefix ++ [c]) = Some q'.
Proof.
  unfold DFA.run in *. rewrite DFA_run_from_app with (q2 := q); eauto. simpl. rewrite STEP. reflexivity.
Qed.

Lemma accepted_prefix_no_step_bound (lexer : lex_dfa) (input : list ascii) (prefix_rev : list ascii) (c : ascii) (rest : list ascii) (q : DFA.state lexer.(lex_core)) (prefix : list ascii) (rest' : list ascii) (tag : accept_tag)
  (SPLIT : input = rev prefix_rev ++ c :: rest)
  (RUN : DFA.run lexer.(lex_core) (rev prefix_rev) = Some q)
  (STEP : DFA.step lexer.(lex_core) q c = None)
  (ACCEPTED : accepted_prefix lexer input prefix rest' tag)
  : length prefix <= length (rev prefix_rev).
Proof.
  destruct (le_lt_dec (length prefix) (length (rev prefix_rev))) as [LE | LT]; [exact LE | exfalso].
  inv ACCEPTED.
  pose proof (L.accepted_prefix_longer_cons (rev prefix_rev) c rest prefix rest' SPLIT0 LT) as (prefix_tail & PREFIX).
  subst prefix. unfold DFA.run in RUN0. rewrite DFA_run_from_app with (q2 := q) in RUN0; eauto.
  simpl in RUN0. rewrite STEP in RUN0. congruence.
Qed.

Lemma accepted_prefix_at_current (lexer : lex_dfa) (input : list ascii) (current : list ascii) (rest : list ascii) (q : DFA.state lexer.(lex_core)) (prefix : list ascii) (rest' : list ascii) (tag : accept_tag)
  (SPLIT : input = current ++ rest)
  (RUN : DFA.run lexer.(lex_core) current = Some q)
  (ACCEPTED : accepted_prefix lexer input prefix rest' tag)
  (LEN : length prefix = length current)
  : prefix = current /\ rest' = rest /\ lexer.(lex_best) q = Some tag.
Proof.
  inv ACCEPTED.
  assert (APP : prefix ++ rest' = current ++ rest).
  { congruence. }
  pose proof (L.app_eq_length_inv prefix rest' current rest APP LEN) as (PREFIX & REST).
  subst prefix rest'. rewrite RUN in RUN0. inv RUN0. eauto.
Qed.

Definition best_so_far (lexer : lex_dfa) (input : list ascii) (prefix_rev : list ascii) (best : option match_result) : Prop :=
  match best with
  | None => forall prefix, forall rest, forall tag, accepted_prefix lexer input prefix rest tag -> length prefix <= length (rev prefix_rev) -> False
  | Some m => accepted_prefix lexer input m.(matched_lexeme) m.(matched_rest) (tag_of_match m) /\ length m.(matched_lexeme) <= length (rev prefix_rev) /\ (forall prefix, forall rest, forall tag, accepted_prefix lexer input prefix rest tag -> length prefix <= length (rev prefix_rev) -> length prefix <= length m.(matched_lexeme)) /\ (forall prefix, forall rest, forall tag, accepted_prefix lexer input prefix rest tag -> length prefix = length m.(matched_lexeme) -> (tag_of_match m).(accept_rule_index) <= tag.(accept_rule_index))
  end.

Lemma best_so_far_to_first_dfa_match (lexer : lex_dfa) (input : list ascii) (prefix_rev : list ascii) (m : match_result)
  (BEST : best_so_far lexer input prefix_rev (Some m))
  (BOUND : forall prefix, forall rest, forall tag, accepted_prefix lexer input prefix rest tag -> length prefix <= length (rev prefix_rev))
  : first_dfa_match lexer input m.(matched_lexeme) m.(matched_rest) (tag_of_match m).
Proof.
  simpl in BEST. destruct BEST as (ACCEPTED & LEN & LONGEST & PRIORITY).
  econs; eauto.
Qed.

Lemma best_so_far_initial (lexer : lex_dfa) (input : list ascii)
  : best_so_far lexer input [] None.
Proof.
  simpl. intros prefix rest tag ACCEPTED LEN. inv ACCEPTED.
  destruct prefix as [ | c prefix]; [contradiction | simpl in LEN; lia].
Qed.

Lemma best_so_far_step (lexer : lex_dfa) (input : list ascii) (prefix_rev : list ascii) (c : ascii) (rest : list ascii) (q : DFA.state lexer.(lex_core)) (q' : DFA.state lexer.(lex_core)) (best : option match_result)
  (SPLIT : input = rev prefix_rev ++ c :: rest)
  (RUN : DFA.run lexer.(lex_core) (rev prefix_rev) = Some q)
  (STEP : DFA.step lexer.(lex_core) q c = Some q')
  (BEST : best_so_far lexer input prefix_rev best)
  : best_so_far lexer input (c :: prefix_rev) (B.maybe (A := accept_tag) (B := fun _ => option match_result) best (fun tag => Some (match_of_tag (rev (c :: prefix_rev)) rest tag)) (lexer.(lex_best) q')).
Proof.
  assert (SPLIT' : input = rev (c :: prefix_rev) ++ rest).
  { rewrite SPLIT. simpl. rewrite <- app_assoc. reflexivity. }
  assert (RUN' : DFA.run lexer.(lex_core) (rev (c :: prefix_rev)) = Some q').
  { simpl. eapply DFA_run_snoc; eauto. }
  unfold B.maybe. destruct (lex_best lexer q') as [tag | ] eqn: BEST_TAG; simpl.
  - set (m := match_of_tag (rev (c :: prefix_rev)) rest tag). simpl.
    assert (ACCEPTED : accepted_prefix lexer input (matched_lexeme m) (matched_rest m) (tag_of_match m)).
    { subst m. rewrite tag_of_match_of_tag. unfold match_of_tag. simpl. econs; eauto.
      intros EQ. apply f_equal with (f := @length ascii) in EQ. rewrite length_app, length_rev in EQ. simpl in EQ. lia.
    }
    splits.
    + exact ACCEPTED.
    + subst m. unfold match_of_tag. simpl. reflexivity.
    + intros prefix rest' tag' ACCEPTED' LEN. subst m. unfold match_of_tag in *. simpl in *. exact LEN.
    + intros prefix rest' tag' ACCEPTED' LEN.
      assert (LEN' : length (matched_lexeme m) = length prefix).
      { subst m. unfold match_of_tag. simpl. symmetry. exact LEN. }
      pose proof (accepted_prefix_same_length lexer input (matched_lexeme m) (matched_rest m) (tag_of_match m) prefix rest' tag' ACCEPTED ACCEPTED' LEN') as (_ & _ & TAG_EQ).
      assert (TAG_M : tag_of_match m = tag) by (subst m; apply tag_of_match_of_tag).
      rewrite TAG_M in TAG_EQ. subst tag'. lia.
  - destruct best as [m | ]; simpl in *.
    + destruct BEST as (ACCEPTED & LEN & LONGEST & PRIORITY).
      splits.
      * exact ACCEPTED.
      * rewrite length_app, length_rev in *. simpl in *. lia.
      * intros prefix rest' tag' ACCEPTED' LEN'.
        destruct (le_lt_dec (length prefix) (length (rev prefix_rev))) as [LE | LT].
        { eapply LONGEST; eauto. }
        exfalso. assert (LEN_CURRENT : length prefix = length (rev (c :: prefix_rev))) by (rewrite length_app, length_rev in *; simpl in *; lia).
        pose proof (accepted_prefix_at_current lexer input (rev (c :: prefix_rev)) rest q' prefix rest' tag' SPLIT' RUN' ACCEPTED' LEN_CURRENT) as (_ & _ & CONTRA).
        congruence.
      * eauto.
    + intros prefix rest' tag' ACCEPTED' LEN'.
      destruct (le_lt_dec (length prefix) (length (rev prefix_rev))) as [LE | LT].
      { eapply BEST; eauto. }
      assert (LEN_CURRENT : length prefix = length (rev (c :: prefix_rev))) by (rewrite length_app, length_rev in *; simpl in *; lia).
      pose proof (accepted_prefix_at_current lexer input (rev (c :: prefix_rev)) rest q' prefix rest' tag' SPLIT' RUN' ACCEPTED' LEN_CURRENT) as (_ & _ & CONTRA).
      congruence.
Qed.

Fixpoint scan_one_loop (lexer : lex_dfa) (q : DFA.state lexer.(lex_core)) (prefix_rev : list ascii) (rest : list ascii) (best : option match_result) {struct rest} : option match_result :=
  match rest with
  | [] => best
  | c :: rest' =>
    match DFA.step lexer.(lex_core) q c with
    | None => best
    | Some q' =>
      let prefix_rev' := c :: prefix_rev in
      let prefix := rev prefix_rev' in
      let best' := B.maybe (A := accept_tag) (B := fun _ => option match_result) best (fun tag => Some (match_of_tag prefix rest' tag)) (lexer.(lex_best) q') in
      scan_one_loop lexer q' prefix_rev' rest' best'
    end
  end.

Definition scan_one (lexer : t) (input : list ascii) : ErrM match_result :=
  match scan_one_loop lexer.(lexer_dfa) (DFA.start lexer.(lexer_dfa).(lex_core)) [] input None with
  | None => inl (Error.NoMatch input)
  | Some m => inr m
  end.

Lemma scan_one_loop_length_step (prefix_rev : list ascii) (c : ascii) (rest : list ascii)
  : length (rev prefix_rev ++ c :: rest) = length (rev (c :: prefix_rev) ++ rest).
Proof.
  repeat rewrite length_app. repeat rewrite length_rev. simpl. lia.
Qed.

Lemma scan_one_loop_progress (lexer : lex_dfa) (q : DFA.state lexer.(lex_core)) (prefix_rev : list ascii) (rest : list ascii) (best : option match_result) (m : match_result)
  (BEST : forall m0, best = Some m0 -> length m0.(matched_rest) < length (rev prefix_rev ++ rest))
  (LOOP : scan_one_loop lexer q prefix_rev rest best = Some m)
  : length m.(matched_rest) < length (rev prefix_rev ++ rest).
Proof.
  revert q prefix_rev best m BEST LOOP. induction rest as [ | c rest IH]; i; simpl in LOOP.
  - eauto.
  - destruct (DFA.step (lex_core lexer) q c) as [q' | ] eqn: STEP; eauto.
    replace (length (rev prefix_rev ++ c :: rest)) with (length (rev (c :: prefix_rev) ++ rest)).
    + eapply IH; [ | exact LOOP]. intros m0 BEST0.
      unfold B.maybe in BEST0. destruct (lex_best lexer q') as [tag | ] eqn: BEST_TAG.
      * inv BEST0. unfold match_of_tag. simpl. repeat rewrite length_app. repeat rewrite length_rev. simpl. lia.
      * pose proof (BEST m0 BEST0) as PROGRESS. rewrite <- scan_one_loop_length_step. exact PROGRESS.
    + symmetry. eapply scan_one_loop_length_step.
Qed.

Lemma scan_one_loop_dfa_sound (lexer : lex_dfa) (q : DFA.state lexer.(lex_core)) (prefix_rev : list ascii) (rest : list ascii) (best : option match_result) (input : list ascii) (m : match_result)
  (SPLIT : input = rev prefix_rev ++ rest)
  (RUN : DFA.run lexer.(lex_core) (rev prefix_rev) = Some q)
  (BEST : best_so_far lexer input prefix_rev best)
  (LOOP : scan_one_loop lexer q prefix_rev rest best = Some m)
  : first_dfa_match lexer input m.(matched_lexeme) m.(matched_rest) (tag_of_match m).
Proof.
  revert q prefix_rev best input m SPLIT RUN BEST LOOP. induction rest as [ | c rest IH]; i; simpl in LOOP.
  - destruct best as [m0 | ]; inv LOOP. eapply best_so_far_to_first_dfa_match; eauto.
    intros prefix rest' tag ACCEPTED. inv ACCEPTED.
    assert (EQ : rev prefix_rev ++ [] = prefix ++ rest') by congruence.
    apply f_equal with (f := @length ascii) in EQ. rewrite app_nil_r, length_app in EQ. lia.
  - destruct (DFA.step (lex_core lexer) q c) as [q' | ] eqn: STEP.
    + eapply IH with (q := q') (prefix_rev := c :: prefix_rev).
      * rewrite SPLIT. simpl. rewrite <- app_assoc. reflexivity.
      * simpl. eapply DFA_run_snoc; eauto.
      * eapply best_so_far_step; eauto.
      * exact LOOP.
    + destruct best as [m0 | ]; inv LOOP. eapply best_so_far_to_first_dfa_match; eauto.
      intros prefix rest' tag ACCEPTED. eapply accepted_prefix_no_step_bound; eauto.
Qed.

Lemma scan_one_loop_no_accepted_prefix (lexer : lex_dfa) (q : DFA.state lexer.(lex_core)) (prefix_rev : list ascii) (rest : list ascii) (best : option match_result) (input : list ascii)
  (SPLIT : input = rev prefix_rev ++ rest)
  (RUN : DFA.run lexer.(lex_core) (rev prefix_rev) = Some q)
  (BEST : best_so_far lexer input prefix_rev best)
  (LOOP : scan_one_loop lexer q prefix_rev rest best = None)
  : forall prefix, forall rest', forall tag, accepted_prefix lexer input prefix rest' tag -> False.
Proof.
  revert q prefix_rev best input SPLIT RUN BEST LOOP. induction rest as [ | c rest IH]; i; simpl in LOOP.
  - destruct best as [m0 | ]; inv LOOP.
    simpl in BEST. eapply BEST; eauto. inv H.
    assert (EQ : rev prefix_rev ++ [] = prefix ++ rest') by congruence.
    apply f_equal with (f := @length ascii) in EQ. rewrite app_nil_r, length_app in EQ. lia.
  - destruct (DFA.step (lex_core lexer) q c) as [q' | ] eqn: STEP.
    + eapply IH with (q := q') (prefix_rev := c :: prefix_rev) (best := B.maybe (A := accept_tag) (B := fun _ => option match_result) best (fun tag => Some (match_of_tag (rev (c :: prefix_rev)) rest tag)) (lex_best lexer q')) (input := input).
      * rewrite SPLIT. simpl. rewrite <- app_assoc. reflexivity.
      * simpl. eapply DFA_run_snoc; eauto.
      * eapply best_so_far_step; eauto.
      * exact LOOP.
      * exact H.
    + destruct best as [m0 | ]; inv LOOP.
      simpl in BEST. eapply BEST; eauto. eapply accepted_prefix_no_step_bound; eauto.
Qed.

Theorem scan_one_progress (lexer : t) (input : list ascii) (m : match_result)
  (SCAN : scan_one lexer input = inr m)
  : length m.(matched_rest) < length input.
Proof.
  unfold scan_one in SCAN. destruct (scan_one_loop (lexer_dfa lexer) (DFA.start (lex_core (lexer_dfa lexer))) [] input None) as [m0 | ] eqn: LOOP; inv SCAN.
  eapply scan_one_loop_progress with (best := None) in LOOP; [simpl in LOOP; exact LOOP | intros m1 CONTRA; congruence].
Qed.

Theorem scan_one_dfa_sound (lexer : t) (input : list ascii) (m : match_result)
  (SCAN : scan_one lexer input = inr m)
  : first_dfa_match lexer.(lexer_dfa) input m.(matched_lexeme) m.(matched_rest) (tag_of_match m).
Proof.
  unfold scan_one in SCAN. destruct (scan_one_loop (lexer_dfa lexer) (DFA.start (lex_core (lexer_dfa lexer))) [] input None) as [m0 | ] eqn: LOOP; inv SCAN.
  eapply scan_one_loop_dfa_sound with (q := DFA.start (lex_core (lexer_dfa lexer))) (prefix_rev := []) (rest := input) (best := None); eauto.
  eapply best_so_far_initial.
Qed.

Theorem accepted_prefix_rule_sound (lexer : t) (input : list ascii) (prefix : list ascii) (rest : list ascii) (tag : accept_tag)
  (ACCEPTED : accepted_prefix lexer.(lexer_dfa) input prefix rest tag)
  : exists key, exists cr, lookup_compiled_rule lexer.(lexer_rules) key = Some cr /\ tag = tag_of_compiled_rule cr /\ compiled_rule_accepts cr prefix.
Proof.
  inv ACCEPTED.
  eapply lexer_dfa_sound; eauto.
Qed.

Theorem scan_one_regex_sound (lexer : t) (input : list ascii) (m : match_result)
  (SCAN : scan_one lexer input = inr m)
  : exists key, exists cr, lookup_compiled_rule lexer.(lexer_rules) key = Some cr /\ tag_of_match m = tag_of_compiled_rule cr /\ compiled_rule_accepts cr m.(matched_lexeme).
Proof.
  pose proof (scan_one_dfa_sound lexer input m SCAN) as FIRST. inv FIRST.
  eapply accepted_prefix_rule_sound. exact ACCEPTED.
Qed.

Theorem scan_one_rule_sound (lexer : t) (input : list ascii) (m : match_result)
  (SCAN : scan_one lexer input = inr m)
  : exists cr, L.In cr lexer.(lexer_rules) /\ m.(matched_rule_index) = cr.(compiled_rule_index) /\ m.(matched_kind) = cr.(compiled_rule_kind) /\ compiled_rule_accepts cr m.(matched_lexeme).
Proof.
  pose proof (scan_one_regex_sound lexer input m SCAN) as (key & cr & LOOKUP & TAG & ACCEPTS).
  exists cr. splits.
  - eapply lookup_compiled_rule_in. exact LOOKUP.
  - destruct m as [idx kind lexeme rest]. destruct cr as [cr_idx cr_kind cr_regex]. simpl in *. inv TAG. reflexivity.
  - destruct m as [idx kind lexeme rest]. destruct cr as [cr_idx cr_kind cr_regex]. simpl in *. inv TAG. reflexivity.
  - exact ACCEPTS.
Qed.

Theorem scan_one_raw_rule_sound (lexer : t) (input : list ascii) (m : match_result)
  (SCAN : scan_one lexer input = inr m)
  : exists r, L.In r all_raw_rules /\ m.(matched_rule_index) = r.(raw_rule_index) /\ m.(matched_kind) = r.(raw_rule_kind) /\ rule_accepts r m.(matched_lexeme).
Proof.
  pose proof (scan_one_rule_sound lexer input m SCAN) as (cr & IN & INDEX & KIND & ACCEPTS).
  pose proof (lexer_rules_wf lexer cr IN) as (r & RAW_IN & COMPILE).
  assert (CR_INDEX : cr.(compiled_rule_index) = r.(raw_rule_index)).
  { unfold compile_rule in COMPILE. destruct (nullable (raw_rule_regex r)); inv COMPILE. reflexivity. }
  assert (CR_KIND : cr.(compiled_rule_kind) = r.(raw_rule_kind)).
  { unfold compile_rule in COMPILE. destruct (nullable (raw_rule_regex r)); inv COMPILE. reflexivity. }
  exists r. splits.
  - exact RAW_IN.
  - congruence.
  - congruence.
  - eapply compile_rule_sound; eauto.
Qed.

Corollary scan_one_dfa_longest (lexer : t) (input : list ascii) (m : match_result)
  (SCAN : scan_one lexer input = inr m)
  : forall prefix, forall rest, forall tag, accepted_prefix lexer.(lexer_dfa) input prefix rest tag -> length prefix <= length m.(matched_lexeme).
Proof.
  pose proof (scan_one_dfa_sound lexer input m SCAN) as FIRST. inv FIRST. eauto.
Qed.

Corollary scan_one_dfa_priority (lexer : t) (input : list ascii) (m : match_result)
  (SCAN : scan_one lexer input = inr m)
  : forall prefix, forall rest, forall tag, accepted_prefix lexer.(lexer_dfa) input prefix rest tag -> length prefix = length m.(matched_lexeme) -> m.(matched_rule_index) <= tag.(accept_rule_index).
Proof.
  pose proof (scan_one_dfa_sound lexer input m SCAN) as FIRST. inv FIRST. simpl in PRIORITY. eauto.
Qed.

Theorem scan_one_dfa_no_match (lexer : t) (input : list ascii)
  (SCAN : scan_one lexer input = inl (Error.NoMatch input))
  : forall prefix, forall rest, forall tag, accepted_prefix lexer.(lexer_dfa) input prefix rest tag -> False.
Proof.
  unfold scan_one in SCAN. destruct (scan_one_loop (lexer_dfa lexer) (DFA.start (lex_core (lexer_dfa lexer))) [] input None) as [m | ] eqn: LOOP; inv SCAN.
  intros prefix rest tag ACCEPTED.
  eapply scan_one_loop_no_accepted_prefix with (q := DFA.start (lex_core (lexer_dfa lexer))) (prefix_rev := []) (rest := input) (best := None); eauto.
  eapply best_so_far_initial.
Qed.

Theorem scan_one_dfa_complete (lexer : t) (input : list ascii) (prefix : list ascii) (rest : list ascii) (tag : accept_tag)
  (MATCH : first_dfa_match lexer.(lexer_dfa) input prefix rest tag)
  : scan_one lexer input = inr (match_of_tag prefix rest tag).
Proof.
  unfold scan_one.
  destruct (scan_one_loop (lexer_dfa lexer) (DFA.start (lex_core (lexer_dfa lexer))) [] input None) as [m | ] eqn: LOOP.
  - assert (SCAN : scan_one lexer input = inr m).
    { unfold scan_one. rewrite LOOP. reflexivity. }
    pose proof (scan_one_dfa_sound lexer input m SCAN) as SOUND.
    pose proof (first_dfa_match_unique lexer.(lexer_dfa) input m.(matched_lexeme) m.(matched_rest) (tag_of_match m) prefix rest tag SOUND MATCH) as (PREFIX & REST & TAG).
    subst prefix rest tag. rewrite match_of_tag_of_match. reflexivity.
  - exfalso. assert (SCAN : scan_one lexer input = inl (Error.NoMatch input)).
    { unfold scan_one. rewrite LOOP. reflexivity. }
    inv MATCH. inv ACCEPTED.
    pose proof (scan_one_dfa_no_match lexer (prefix ++ rest) SCAN prefix rest tag) as NO_MATCH.
    eapply NO_MATCH. econs; eauto.
Qed.

Inductive maximal_tokenizes (lexer : t) : list ascii -> list Token.t -> list ascii -> Prop :=
  | maximal_tokenizes_stop input
    (NO_MATCH : forall prefix, forall rest, forall tag, accepted_prefix lexer.(lexer_dfa) input prefix rest tag -> False)
    : maximal_tokenizes lexer input [] input
  | maximal_tokenizes_emit input tag tok lexeme rest toks unprocessed
    (FIRST : first_dfa_match lexer.(lexer_dfa) input lexeme rest tag)
    (KIND : tag.(accept_kind) = Emit tok)
    (REST : maximal_tokenizes lexer rest toks unprocessed)
    : maximal_tokenizes lexer input (tok :: toks) unprocessed
  | maximal_tokenizes_skip input tag lexeme rest toks unprocessed
    (FIRST : first_dfa_match lexer.(lexer_dfa) input lexeme rest tag)
    (KIND : tag.(accept_kind) = Skip)
    (REST : maximal_tokenizes lexer rest toks unprocessed)
    : maximal_tokenizes lexer input toks unprocessed.

Definition fully_tokenizes (lexer : t) (input : list ascii) (toks : list Token.t) : Prop :=
  maximal_tokenizes lexer input toks [].

Lemma maximal_tokenizes_nil (lexer : t)
  : maximal_tokenizes lexer [] [] [].
Proof.
  econs. intros prefix rest tag ACCEPTED. inv ACCEPTED.
  apply f_equal with (f := @length ascii) in SPLIT. rewrite length_app in SPLIT.
  destruct prefix as [ | c prefix]; [contradiction | simpl in SPLIT; lia].
Qed.

Theorem maximal_tokenizes_unique (lexer : t) (input : list ascii) (toks1 : list Token.t) (rest1 : list ascii) (toks2 : list Token.t) (rest2 : list ascii)
  (TOKENS1 : maximal_tokenizes lexer input toks1 rest1)
  (TOKENS2 : maximal_tokenizes lexer input toks2 rest2)
  : toks1 = toks2 /\ rest1 = rest2.
Proof.
  revert toks2 rest2 TOKENS2. induction TOKENS1; intros toks2 rest2 TOKENS2; inv TOKENS2.
  - eauto.
  - inv FIRST. exfalso. eapply NO_MATCH. exact ACCEPTED.
  - inv FIRST. exfalso. eapply NO_MATCH. exact ACCEPTED.
  - inv FIRST. exfalso. eapply NO_MATCH. exact ACCEPTED.
  - pose proof (first_dfa_match_unique lexer.(lexer_dfa) input lexeme rest tag lexeme0 rest0 tag0 FIRST FIRST0) as (LEXEME & REST_EQ & TAG_EQ).
    subst lexeme0 rest0 tag0. rewrite KIND in KIND0. inv KIND0.
    pose proof (IHTOKENS1 toks0 rest2 REST) as (TOKS & REST_FINAL). subst toks0 rest2. eauto.
  - pose proof (first_dfa_match_unique lexer.(lexer_dfa) input lexeme rest tag lexeme0 rest0 tag0 FIRST FIRST0) as (LEXEME & REST_EQ & TAG_EQ).
    subst lexeme0 rest0 tag0. rewrite KIND in KIND0. congruence.
  - inv FIRST. exfalso. eapply NO_MATCH. exact ACCEPTED.
  - pose proof (first_dfa_match_unique lexer.(lexer_dfa) input lexeme rest tag lexeme0 rest0 tag0 FIRST FIRST0) as (LEXEME & REST_EQ & TAG_EQ).
    subst lexeme0 rest0 tag0. rewrite KIND in KIND0. congruence.
  - pose proof (first_dfa_match_unique lexer.(lexer_dfa) input lexeme rest tag lexeme0 rest0 tag0 FIRST FIRST0) as (LEXEME & REST_EQ & TAG_EQ).
    subst lexeme0 rest0 tag0.
    pose proof (IHTOKENS1 toks2 rest2 REST) as (TOKS & REST_FINAL). subst toks2 rest2. eauto.
Qed.

Inductive scan_one_result (lexer : t) (input : list ascii) : Set :=
  | scan_one_error err
    (scan_one_error_eq : scan_one lexer input = inl err)
    : scan_one_result lexer input
  | scan_one_success m
    (scan_one_success_eq : scan_one lexer input = inr m)
    (scan_one_success_progress : input_lt m.(matched_rest) input)
    : scan_one_result lexer input.

Definition scan_one_with_progress (lexer : t) (input : list ascii) : scan_one_result lexer input.
Proof.
  destruct (scan_one lexer input) as [err | m] eqn: SCAN.
  - exact (scan_one_error lexer input err SCAN).
  - exact (scan_one_success lexer input m SCAN (scan_one_progress lexer input m SCAN)).
Defined.

Fixpoint scan_all_acc (lexer : t) (input : list ascii) (ACC : Acc input_lt input) {struct ACC} : ErrM (list Token.t) :=
  match input with
  | [] => inr []
  | _ =>
    match scan_one_with_progress lexer input with
    | scan_one_error _ _ err _ => inl err
    | scan_one_success _ _ m _ PROGRESS =>
      match scan_all_acc lexer m.(matched_rest) (Acc_inv ACC PROGRESS) with
      | inl err => inl err
      | inr toks =>
        match m.(matched_kind) with
        | Emit tok => inr (tok :: toks)
        | Skip => inr toks
        end
      end
    end
  end.

Definition scan_all (lexer : t) (input : list ascii) : ErrM (list Token.t) :=
  scan_all_acc lexer input (L.length_lt_wf input).

Theorem scan_all_acc_sound_maximal (lexer : t) (input : list ascii) (ACC : Acc input_lt input) (toks : list Token.t)
  (SCAN : scan_all_acc lexer input ACC = inr toks)
  : fully_tokenizes lexer input toks.
Proof.
  revert input ACC toks SCAN. fix IH 2. intros input ACC toks SCAN.
  destruct ACC as [ACC_INV].
  destruct input as [ | c input']; simpl in SCAN.
  - inv SCAN. unfold fully_tokenizes. eapply maximal_tokenizes_nil.
  - destruct (scan_one_with_progress lexer (c :: input')) as [err SCAN_ERR | m SCAN_M PROGRESS] eqn: SCAN_ONE; try congruence.
    destruct (scan_all_acc lexer (matched_rest m) (ACC_INV (matched_rest m) PROGRESS)) as [err | toks'] eqn: SCAN_REST; try congruence.
    pose proof (scan_one_dfa_sound lexer (c :: input') m SCAN_M) as FIRST.
    pose proof (IH (matched_rest m) (ACC_INV (matched_rest m) PROGRESS) toks' SCAN_REST) as REST.
    destruct (matched_kind m) as [tok | ] eqn: KIND; inv SCAN.
    + eapply maximal_tokenizes_emit with (tag := tag_of_match m) (lexeme := matched_lexeme m) (rest := matched_rest m); eauto.
    + eapply maximal_tokenizes_skip with (tag := tag_of_match m) (lexeme := matched_lexeme m) (rest := matched_rest m); eauto.
Qed.

Theorem scan_all_sound_maximal (lexer : t) (input : list ascii) (toks : list Token.t)
  (SCAN : scan_all lexer input = inr toks)
  : fully_tokenizes lexer input toks.
Proof.
  unfold scan_all in SCAN. eapply scan_all_acc_sound_maximal; eauto.
Qed.

Theorem maximal_tokenizes_complete_scan_all_acc (lexer : t) (input : list ascii) (toks : list Token.t) (unprocessed : list ascii)
  (TOKENS : maximal_tokenizes lexer input toks unprocessed)
  (DONE : unprocessed = [])
  : forall ACC, scan_all_acc lexer input ACC = inr toks.
Proof.
  induction TOKENS as [input NO_MATCH | input tag tok lexeme rest toks unprocessed FIRST KIND REST IH | input tag lexeme rest toks unprocessed FIRST KIND REST IH]; intros ACC.
  - subst input. destruct ACC as [ACC_INV]. reflexivity.
  - pose proof (scan_one_dfa_complete lexer input lexeme rest tag FIRST) as SCAN.
    inv FIRST. inv ACCEPTED.
    destruct lexeme as [ | c lexeme]; [contradiction | ].
    simpl in SCAN. destruct ACC as [ACC_INV]. simpl.
    destruct (scan_one_with_progress lexer (c :: lexeme ++ rest)) as [err SCAN_ERR | m SCAN_M PROGRESS].
    + rewrite SCAN in SCAN_ERR. congruence.
    + rewrite SCAN in SCAN_M. inv SCAN_M. simpl. rewrite KIND.
      rewrite (IH eq_refl (ACC_INV rest PROGRESS)). reflexivity.
  - pose proof (scan_one_dfa_complete lexer input lexeme rest tag FIRST) as SCAN.
    inv FIRST. inv ACCEPTED.
    destruct lexeme as [ | c lexeme]; [contradiction | ].
    simpl in SCAN. destruct ACC as [ACC_INV]. simpl.
    destruct (scan_one_with_progress lexer (c :: lexeme ++ rest)) as [err SCAN_ERR | m SCAN_M PROGRESS].
    + rewrite SCAN in SCAN_ERR. congruence.
    + rewrite SCAN in SCAN_M. inv SCAN_M. simpl. rewrite KIND.
      rewrite (IH eq_refl (ACC_INV rest PROGRESS)). reflexivity.
Qed.

Theorem scan_all_acc_complete_maximal (lexer : t) (input : list ascii) (toks : list Token.t)
  (TOKENS : fully_tokenizes lexer input toks)
  : forall ACC, scan_all_acc lexer input ACC = inr toks.
Proof.
  unfold fully_tokenizes in TOKENS. intros ACC.
  eapply maximal_tokenizes_complete_scan_all_acc; eauto.
Qed.

Theorem scan_all_complete_maximal (lexer : t) (input : list ascii) (toks : list Token.t)
  (TOKENS : fully_tokenizes lexer input toks)
  : scan_all lexer input = inr toks.
Proof.
  unfold scan_all. eapply scan_all_acc_complete_maximal; eauto.
Qed.

Definition run_with_error (lexer : t) (s : string) : ErrM (list Token.t) :=
  scan_all lexer (Input.of_string s).

Corollary run_with_error_sound_maximal (lexer : t) (s : string) (toks : list Token.t)
  (RUN : run_with_error lexer s = inr toks)
  : fully_tokenizes lexer (Input.of_string s) toks.
Proof.
  unfold run_with_error in RUN. eapply scan_all_sound_maximal; eauto.
Qed.

Definition run (lexer : t) (s : string) : option (list Token.t) :=
  match run_with_error lexer s with
  | inl _ => None
  | inr toks => Some toks
  end.

Corollary run_sound_maximal (lexer : t) (s : string) (toks : list Token.t)
  (RUN : run lexer s = Some toks)
  : fully_tokenizes lexer (Input.of_string s) toks.
Proof.
  unfold run in RUN. destruct (run_with_error lexer s) as [err | toks'] eqn: RUN_ERR; inv RUN.
  eapply run_with_error_sound_maximal; eauto.
Qed.

Corollary run_complete_maximal (lexer : t) (s : string) (toks : list Token.t)
  (TOKENS : fully_tokenizes lexer (Input.of_string s) toks)
  : run lexer s = Some toks.
Proof.
  unfold run, run_with_error.
  pose proof (scan_all_complete_maximal lexer (Input.of_string s) toks TOKENS) as SCAN.
  rewrite SCAN. reflexivity.
Qed.

Definition build : ErrM t.
Proof.
  destruct compile_rules as [err | crs] eqn: COMPILE.
  - exact (inl err).
  - destruct (determinize_tagged (build_tagged_enfa crs)) as [err | lexer] eqn: DETERMINIZE.
    + exact (inl err).
    + unfold determinize_tagged in DETERMINIZE. inv DETERMINIZE.
      refine (inr (mk crs (compile_rules_wf crs COMPILE) (lex_dfa_of_tagged (build_tagged_enfa crs)) _)).
      intros input q tag RUN BEST.
      pose proof (lex_best_sound (build_tagged_enfa crs) q tag BEST) as TAG.
      pose proof (lex_accepts_run_sound (build_tagged_enfa crs) input q tag RUN TAG) as (qN & REACH & TAGGED).
      eapply build_tagged_enfa_sound. unfold tagged_accepts. exists qN. split; eauto.
Defined.

Definition entry_point : ErrM (t -> string -> option (list Token.t)) :=
  inr run.

End LGS.
