Require Import PnV.Prelude.Prelude.

Notation "lhs ≠ rhs" := (~ (lhs = rhs)) : type_scope.

Tactic Notation "rewrite*" uconstr( t ) "by" ident ( H_EQ ) :=
  let lhs := fresh "lhs" in
  set (lhs := t) in |- *;
  match type of H_EQ with
  | ?X = ?Y => change (lhs = Y) in H_EQ; rewrite -> H_EQ; subst lhs
  end.

Tactic Notation "find" simple_intropattern( p ) "by" uconstr( H ) :=
  unshelve hexploit H; [eauto .. | intros p].

Tactic Notation "find*" simple_intropattern( p ) "by" uconstr( H ) :=
  hexploit H; [eauto .. | intros p].

Ltac done :=
  des; subst; done!.

Lemma S_lt_S_intro (n : nat) (m : nat)
  (H_lt : n < m)
  : S n < S m.
Proof.
  lia.
Qed.

Lemma inject_pair_eq (A : Type) (B : Type) (x : A) (x' : A) (y : B) (y' : B)
  : (x, y) = (x', y') <-> (x = x' /\ y = y').
Proof.
  split; [intros EQ; split | intros [EQ1 EQ2]]; congruence.
Qed.

#[global] Hint Rewrite inject_pair_eq : simplication_hints.

Fixpoint iter {A : Type} (fuel : nat) (step : A -> A) (x : A) {struct fuel} : A :=
  match fuel with
  | O => x
  | S fuel' => iter fuel' step (step x)
  end.

Lemma iter_succ (A : Type) (fuel : nat) (step : A -> A) (x : A)
  : iter (S fuel) step x = step (iter fuel step x).
Proof.
  revert x; induction fuel as [ | fuel IH]; intros x; simpl.
  - reflexivity.
  - eapply IH.
Qed.

#[global] Hint Rewrite iter_succ : simplication_hints.

Definition nonempty {A : Type} (xs : list A) : bool :=
  negb (L.null xs).

Lemma nonempty_exists {A : Type} (xs : list A)
  (NONEMPTY : nonempty xs = true)
  : exists x, L.In x xs.
Proof.
  unfold nonempty in NONEMPTY. destruct xs; done.
Qed.

Lemma nonempty_of_exists {A : Type} (xs : list A) (x : A)
  (IN : L.In x xs)
  : nonempty xs = true.
Proof.
  unfold nonempty. destruct xs; done.
Qed.

#[global]
Instance lnot_dec {P1 : Prop}
  `(P1_dec : B.Decision P1)
  : B.Decision (~ P1).
Proof.
  destruct P1_dec as [P1_yes | P1_no].
  - right. intros H. eapply H. exact P1_yes.
  - left. exact P1_no.
Defined.

#[global]
Instance land_dec {P1 : Prop} {P2 : Prop}
  `(P1_dec : B.Decision P1)
  `(P2_dec : B.Decision P2)
  : B.Decision (P1 /\ P2).
Proof.
  destruct P1_dec as [P1_yes | P1_no].
  - destruct P2_dec as [P2_yes | P2_no].
    + left. exact (conj P1_yes P2_yes).
    + right. intros H. contradiction (P2_no (proj2 H)).
  - right. intros H. contradiction (P1_no (proj1 H)).
Defined.

#[global]
Instance lor_dec {P1 : Prop} {P2 : Prop}
  `(P1_dec : B.Decision P1)
  `(P2_dec : B.Decision P2)
  : B.Decision (P1 \/ P2).
Proof.
  destruct P1_dec as [P1_yes | P1_no].
  - left. exact (or_introl P1_yes).
  - destruct P2_dec as [P2_yes | P2_no].
    + left. exact (or_intror P2_yes).
    + right. intros [H | H]; contradiction.
Defined.

#[global]
Instance falsum_dec
  : B.Decision False.
Proof.
  right. intros H. exact H.
Defined.

Lemma remove_length_lt {A : Type} `{EQ_DEC : hasEqDec A} (x : A) (xs : list A)
  (IN : L.In x xs)
  : length (remove EQ_DEC x xs) < length xs.
Proof.
  revert x IN; induction xs as [ | y ys IH]; simpl; ii.
  - ss!.
  - des_ifs.
    + find ? by remove_length_le; ss!.
    + des; ss!.
Qed.

Theorem NoDup_exists_injective_length {A : Type} {B : Type} `{B_hasEqDec : hasEqDec B} (xs : list A) (ys : list B) (R : A -> B -> Prop)
  (xs_NoDup : NoDup xs)
  (R_total : forall x, L.In x xs -> (exists y, L.In y ys /\ R x y))
  (R_functional : forall x1, forall x2, forall y, L.In x1 xs -> L.In x2 xs -> R x1 y -> R x2 y -> x1 = x2)
  : length xs <= length ys.
Proof.
  revert ys R_total R_functional; induction xs_NoDup as [ | x xs NOT_IN NO_DUP IH]; intros ys TOTAL INJ; simpl; [lia | ].
  pose proof (TOTAL x (or_introl eq_refl)) as (y & IN_Y & R_XY).
  enough (LE : length xs <= length (remove B_hasEqDec y ys)).
  { pose proof (remove_length_lt y ys IN_Y). lia. }
  eapply IH.
  - intros x' IN_XS.
    pose proof (TOTAL x' (or_intror IN_XS)) as (y' & IN_Y' & R_XY').
    exists y'. split; eauto. rewrite L.in_remove_iff. split; eauto; ii.
    enough (x' = x) by done!.
    eapply INJ; ss!.
  - ii; eapply INJ; ss!.
Qed.

Lemma NoDup_map_inj {X : Type} {Y : Type} (f : X -> Y) (l : list X)
  (NO_DUP : L.NoDup l)
  (INJ : forall a : X, forall b : X, L.In a l -> L.In b l -> f a = f b -> a = b)
  : L.NoDup (L.map f l).
Proof.
  revert INJ. induction NO_DUP as [ | a l NOT_IN NO_DUP IH]; intros ?; simpl; econs.
  - intros H_in. rewrite L.in_map_iff in H_in. destruct H_in as (b & f_eq & b_in).
    contradiction NOT_IN. erewrite INJ with (a := a) (b := b); simpl; eauto with *.
  - eapply IH. intros a1 b1 a1_in b1_in H_eq.  exact (INJ a1 b1 (or_intror a1_in) (or_intror b1_in) H_eq).
Qed.

Module SN.

Section Strong_Normalisation.

Context {A : Type}.

Inductive sn (R : A -> A -> Prop) (x : A) : Prop :=
  | sn_intro
    (sn_inv : forall x' : A, R x x' -> sn R x').

Context {R : A -> A -> Prop}.

Definition sn_inv (x : A) (H_sn : sn R x) : forall x' : A, R x x' -> sn R x' :=
  match H_sn with
  | @sn_intro _ _ sn_inv => sn_inv
  end.

Fixpoint sn_guard {x : A} (n : nat) (H_sn : sn R x) {struct n} : sn R x :=
  match n with
  | O => H_sn
  | S n' => sn_intro R x (fun x' : A => fun H_R : R x x' => sn_guard n' (sn_inv x H_sn x' H_R))
  end.

End Strong_Normalisation.

Strategy 100 [sn_guard].

Section Strict_Progress_on_Prosets.

Context {A : Type} {PROSET : isProset A}.

Inductive betaProgressive (x : A) (x' : A) : Prop :=
  | betaProgressive_intro
    (LE : x =< x')
    (NE : ~ (x == x')).

Theorem finite_upper_cone_implies_sn (x0 : A)
  (finite_upper_cone : exists cone : list A, forall x : A, x0 =< x -> L.In x cone)
  : sn betaProgressive x0.
Proof.
  destruct finite_upper_cone as [cone IN].
  enough (INV : forall bound : nat, forall cone : list A, forall x : A, length cone <= bound -> (forall y : A, x =< y -> L.In y cone) -> sn betaProgressive x).
  { eapply INV with (bound := length cone) (cone := cone); eauto. }
  induction bound as [ | bound IH]; intros cone' x LENGTH UPPER.
  - destruct cone' as [ | a cone']; simpl in LENGTH.
    + exfalso. eapply UPPER. reflexivity.
    + lia.
  - pose proof (UPPER x (leProp_refl x)) as IN_X.
    apply L.in_split in IN_X. destruct IN_X as (prefix & suffix & CONE_EQ).
    subst cone'. econs. intros x' [LE NE].
    eapply IH with (cone := prefix ++ suffix).
    + rewrite !length_app in LENGTH |- *. simpl in LENGTH. lia.
    + intros y LE'.
      pose proof (UPPER y (leProp_trans x x' y LE LE')) as IN_Y.
      rewrite L.in_app_iff in IN_Y. simpl in IN_Y.
      rewrite L.in_app_iff. destruct IN_Y as [IN_Y | [Y_EQ | IN_Y]]; eauto.
      subst y. contradiction NE. eapply leProp_antisymmetry; eauto.
Qed.

Corollary finite_domain_guarantees_sn
  (FINITE : exists enum : list A, forall x : A, L.In x enum)
  : forall x0 : A, sn betaProgressive x0.
Proof.
  destruct FINITE as [enum IN]. i.
  eapply finite_upper_cone_implies_sn; ss!.
Qed.

Section Progressive_Fixed_Point_Iteration.

Context {eqProp_dec : forall x : A, forall x' : A, B.Decision (x == x')}.

Variable step : A -> A.

Hypothesis step_isProgressive : forall x : A, x =< step x.

Fixpoint prog_iter (x : A) (sn_x : sn betaProgressive x) {struct sn_x} : A :=
  let x' : A := step x in
  match B.decide (x == x') with
  | left H_EQ => x
  | right H_NE => prog_iter x' (sn_inv x sn_x x' (betaProgressive_intro x x' (step_isProgressive x) H_NE))
  end.

Fixpoint prog_iter_pirrel (x : A) (H_sn : sn betaProgressive x) (H_sn' : sn betaProgressive x) {struct H_sn} : prog_iter x H_sn = prog_iter x H_sn'.
Proof.
  destruct H_sn as [H_sn_inv], H_sn' as [H_sn_inv']; simpl.
  destruct (B.decide _) as [H_EQ | H_NE]; [reflexivity | eapply prog_iter_pirrel].
Qed.

Fixpoint prog_iter_isProgressive (x : A) (sn_x : sn betaProgressive x) {struct sn_x} : x =< prog_iter x sn_x.
Proof.
  destruct sn_x as [H_sn_inv]. simpl.
  destruct (B.decide _) as [H_EQ | H_NE].
  - reflexivity.
  - etransitivity.
    + eapply step_isProgressive.
    + eapply prog_iter_isProgressive.
Qed.

Fixpoint prog_iter_isFixedpoint (x : A) (sn_x : sn betaProgressive x) {struct sn_x} : step (prog_iter x sn_x) == prog_iter x sn_x.
Proof.
 destruct sn_x as [H_sn_inv]. simpl.
  destruct (B.decide _) as [H_EQ | H_NE].
  - symmetry. exact H_EQ.
  - eapply prog_iter_isFixedpoint.
Qed.

Hypothesis step_isMonotonic : isMonotonic1 step.

Fixpoint prog_iter_le (x : A) (x' : A) (sn_x : sn betaProgressive x) (FIXEDPOINT : step x' == x') (LE : x =< x') {struct sn_x} : prog_iter x sn_x =< x'.
Proof.
  destruct sn_x as [H_sn_inv]; simpl.
  destruct (B.decide _) as [H_EQ | H_NE].
  - exact LE.
  - eapply prog_iter_le.
    + exact FIXEDPOINT.
    + etransitivity.
      * eapply step_isMonotonic. exact LE.
      * eapply eqProp_implies_leProp. exact FIXEDPOINT.
Qed.

End Progressive_Fixed_Point_Iteration.

End Strict_Progress_on_Prosets.

Section STRONG_SEARCH.

Fixpoint add' (n : nat) (m : nat) {struct n} : nat :=
  match n with
  | O => m
  | S n' => add' n' (S m)
  end.

Context {State : Type} (isDone : nat -> State -> Prop) {isDone_dec : forall n : nat, forall s : State, B.Decision (isDone n s)}.

Variable step : nat -> State -> State.

Definition advance (n : nat) (s : State) : State :=
  if B.decide (isDone n s) then s else step n s.

Variable s0 : State.

Fixpoint trace (n : nat) : State :=
  match n with
  | O => s0
  | S n' => advance n' (trace n')
  end.

Let P (n : nat) : Prop :=
  isDone n (trace n).

Inductive search (n : nat) : nat -> Prop :=
  | search_next
    (NOT_P : ~ (P n))
    : search n (S n).

Fixpoint strong_search_go (n : nat) (s : State) (Hs : s = trace n) (sn_n : sn search n) {struct sn_n} : nat * State.
Proof.
  destruct (B.decide (isDone n s)) as [H_YES | H_NO].
  - exact (n, s).
  - set (s' := step n s).
    assert (NOT_P : ~ (P n)).
    { unfold P. rewrite <- Hs. exact H_NO. }
    assert (Hs' : s' = trace (S n)).
    { unfold s'. simpl. unfold advance.
      destruct (B.decide _) as [H_YES' | H_NO'].
      - contradiction H_NO. congruence.
      - congruence.
    }
    exact (strong_search_go (S n) s' Hs' (sn_inv n sn_n (S n) (search_next n NOT_P))).
Defined.

Lemma add'_zero_r n
  : add' n 0 = n.
Proof.
  enough (AUX : forall p, forall q, add' p q = p + q).
  { rewrite AUX. lia. }
  intros p. induction p as [ | p IH]; intros q; simpl.
  - reflexivity.
  - rewrite IH. lia.
Qed.

Lemma sn_search n k
  (WITNESS : P (add' n k))
  : sn search n.
Proof.
  revert n WITNESS. induction k as [ | k IH]; intros n WITNESS.
  - constructor. intros n' SEARCH. destruct SEARCH as [NOT_P].
    contradiction NOT_P. rewrite <- add'_zero_r. exact WITNESS.
  - constructor. intros n' SEARCH. destruct SEARCH as [NOT_P].
    eapply IH. simpl. exact WITNESS.
Qed.

Hypothesis eventually_stops : exists k : nat, P k.

Corollary sn_search_0
  : sn search 0.
Proof.
  destruct eventually_stops as [k WITNESS].
  exact (sn_search O k WITNESS).
Qed.

Definition strong_search : nat * State :=
  strong_search_go 0 s0 eq_refl sn_search_0.

Fixpoint strong_search_go_pirrel (n : nat) (s : State) (Hs : s = trace n) (Hs' : s = trace n) (sn_n : sn search n) (sn_n' : sn search n) {struct sn_n} : strong_search_go n s Hs sn_n = strong_search_go n s Hs' sn_n'.
Proof.
  destruct sn_n as [H_sn_inv], sn_n' as [H_sn_inv']; simpl.
  destruct (B.decide _) as [H_YES | H_NO].
  - reflexivity.
  - eapply strong_search_go_pirrel.
Qed.

Lemma strong_search_go_correct_from (n : nat) (s : State) (n' : nat) (s' : State)
  (Hs : s = trace n)
  (sn_n : sn search n)
  (RESULT : (n', s') = strong_search_go n s Hs sn_n)
  : trace n' = s' /\ isDone n' s' /\ (forall m : nat, n <= m -> m < n' -> ~ (isDone m (trace m))).
Proof.
  revert n s Hs sn_n n' s' RESULT. fix IH 4. intros n s Hs [H_sn_inv] n' s' RESULT. simpl in RESULT.
  destruct (B.decide (isDone n s)) as [H_YES | H_NO].
  - inversion RESULT; subst n' s'. split.
    + symmetry. exact Hs.
    + split; [exact H_YES | lia].
  - find* (TRACE & DONE & FIRST) by IH.
    split; [exact TRACE | split; [exact DONE | intros m N_LE_M M_LT]].
    pose proof (Nat.eq_dec m n) as [EQ | NE].
    + subst m. unfold P. rewrite <- Hs. exact H_NO.
    + eapply FIRST; lia.
Qed.

Theorem strong_search_correct (n : nat) (s : State)
  (H_strong_search : (n, s) = strong_search)
  : trace n = s /\ isDone n s /\ (forall m : nat, m < n -> ~ (isDone m (trace m))).
Proof.
  find* (TRACE & DONE & FIRST) by strong_search_go_correct_from.
  split; [exact TRACE | split; [exact DONE | intros m LT]].
  eapply FIRST; lia.
Qed.

Definition strong_search_with_budget (budget : nat) : nat * State :=
  strong_search_go 0 s0 eq_refl (sn_guard (S budget) sn_search_0).

Theorem strong_search_with_budget_eq (budget : nat)
  : strong_search_with_budget budget = strong_search.
Proof.
  eapply strong_search_go_pirrel.
Qed.

End STRONG_SEARCH.

End SN.
