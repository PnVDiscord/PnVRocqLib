Require Import PnV.Prelude.Prelude.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.EqdepFacts.
Require Import Coq.Arith.Wf_nat.

Lemma eq_pirrel_fromEqDec {A : Type} {hasEqDec : hasEqDec A} (lhs : A) (rhs : A)
  (EQ1 : lhs = rhs)
  (EQ2 : lhs = rhs)
  : EQ1 = EQ2.
Proof.
  eapply UIP_dec. exact hasEqDec.
Defined.

Lemma exist_eq_fromEqDec {A : Type} (P : A -> bool) (x : A) (x' : A) (H : P x = true) (H' : P x' = true)
  : @exist A P x H = @exist A P x' H' <-> x = x'.
Proof.
  split.
  - intros EQ. inv EQ. reflexivity.
  - intros EQ. subst x'. f_equal.
    eapply UIP_dec. decide equality.
Qed.

Lemma projT2_eq_fromEqDec {A : Type} {B : A -> Type} {hasEqDec : hasEqDec A} (x : A) (y1 : B x) (y2 : B x)
  (EQ : @existT A B x y1 = @existT A B x y2)
  : y1 = y2.
Proof.
  erewrite eq_sigT_iff_eq_dep in EQ. eapply eq_rect_eq__eq_dep1_eq.
  - ii. eapply eq_rect_eq_dec. exact hasEqDec.
  - eapply eq_dep_dep1. exact EQ.
Defined.

Section SEARCH. (* Reference: "https://plv.mpi-sws.org/coqdoc/stdpp/stdpp.countable.html" *)

Context {A : Type} `{COUNTABLE : isCountable A}.

Inductive search_step (P : A -> Prop) (n : nat) : nat -> Prop :=
  | search_step_None
    (NONE : decode n = None)
    : search_step P n (S n)
  | search_step_Some (x : A)
    (NOT : ~ P x)
    (SOME : decode n = Some x)
    : search_step P n (S n).

Lemma initial_step (P : A -> Prop)
  (BOUND : exists x, P x)
  : Acc (flip (search_step P)) 0.
Proof.
  destruct BOUND as [x P_x]. enough (WTS : forall i, forall p, i <= encode x -> encode x = p + i -> Acc (flip (search_step P)) p) by now ii; eapply WTS with (i := encode x); lia.
  induction i as [ | i IH]; simpl; intros p LE EQ.
  - econs. intros j SEARCH. red in SEARCH. rewrite Nat.add_0_r in EQ. subst p. inv SEARCH.
    + rewrite decode_encode in NONE. congruence.
    + rewrite decode_encode in SOME. congruence.
  - econs. intros j SEARCH. red in SEARCH. eapply IH.
    + lia.
    + inv SEARCH; lia.
Defined.

Fixpoint search_go (P : A -> Prop) (P_dec : forall x, {P x} + {~ P x}) (n : nat) (acc : Acc (flip (search_step P)) n) {struct acc} : A.
Proof.
  destruct (B.Some_dec (decode n)) as [[y SOME] | NONE].
  - destruct (P_dec y) as [EQ | NE].
    + exact y.
    + exact (search_go P P_dec (S n) (Acc_inv acc (search_step_Some P n y NE SOME))).
  - exact (search_go P P_dec (S n) (Acc_inv acc (search_step_None P n NONE))).
Defined.

Fixpoint search_go_correct (P : A -> Prop) (P_dec : forall x, {P x} + {~ P x}) (n : nat) (acc : Acc (flip (search_step P)) n) {struct acc}
  : P (search_go P P_dec n acc).
Proof.
  destruct acc; simpl. destruct (B.Some_dec (decode n)) as [[? ?] | ?] eqn: ?.
  - destruct (P_dec x).
    + assumption.
    + eapply search_go_correct.
  - eapply search_go_correct.
Qed.

Lemma search_go_pirrel (P : A -> Prop) (P_dec : forall x, {P x} + {~ P x}) (n : nat) (acc : Acc (flip (search_step P)) n) (acc' : Acc (flip (search_step P)) n)
  : search_go P P_dec n acc = search_go P P_dec n acc'.
Proof.
  revert acc acc acc'. intros acc''. induction acc'' as [? _ IH]; intros [?] [?]. simpl.
  destruct (B.Some_dec (decode x)) as [[? ?] | ?] eqn: ?.
  - destruct (P_dec x0) as [? | ?].
    + reflexivity.
    + eapply IH. eapply search_step_Some with (x := x0); trivial.
  - eapply IH. eapply search_step_None; trivial.
Qed.

Definition search (n : nat) (BOUND : exists x, encode x = n) : A.
Proof.
  eapply search_go with (n := 0) (P := fun x : A => encode x = n).
  - exact (fun x : A => Nat.eq_dec (encode x) n).
  - eapply initial_step. exact BOUND.
Defined.

Theorem enumeration_lemma
  (encode_surjective : forall n : nat, exists x : A, encode x = n)
  : { enum : nat -> A & ⟪ enumerable : forall x, { n : nat | enum n = x } ⟫ }.
Proof.
  exists (fun n : nat => search n (encode_surjective n)). unnw. intros x. exists (encode x).
  assert (claim : encode (search (encode x) (encode_surjective (encode x))) = encode x).
  { eapply search_go_correct with (P := fun y : A => encode y = encode x) (P_dec := fun y : A => Nat.eq_dec (encode y) (encode x)). }
  apply f_equal with (f := decode) in claim. do 2 rewrite decode_encode in claim. congruence.
Defined.

End SEARCH.

Theorem LEM_implies_MarkovPrinciple (LEM : forall P : Prop, P \/ ~ P) (f : nat -> bool) 
  (NOT_ALL_TRUE : ~ (forall x, f x = true))
  : { n : nat | f n = false }.
Proof.
  enough (EXISTENCE : exists n : nat, f n = false).
  - assert (COUNTABLE : isCountable nat).
    { exists id Some. reflexivity. }
    assert (P_dec : forall x : nat, {f x = false} + {f x <> false}).
    { intros x. now destruct (f x) as [ | ]; [right | left]. }
    pose proof (FUEL := @initial_step nat COUNTABLE (fun x : nat => f x = false) EXISTENCE).
    exists (@search_go nat COUNTABLE (fun x : nat => f x = false) P_dec 0 FUEL). eapply search_go_correct.
  - pose proof (LEM (exists n : nat, f n = false)) as [YES | NO].
    + exact YES.
    + contradiction NOT_ALL_TRUE. intros x. destruct (f x) as [ | ] eqn: H_OBS; now firstorder.
Defined.

Lemma dec_finds_result_if_exists (P : nat -> Prop)
  (DEC : forall n, {P n} + {~ P n})
  (EXISTENCE : exists x, P x)
  : { x : nat | P x }.
Proof.
  pose (COUNTABLE := {| encode := id; decode := @Some nat; decode_encode (x : nat) := @eq_refl (option nat) (Some x) |}).
  exists (@search_go nat COUNTABLE P DEC 0 (@initial_step nat COUNTABLE P EXISTENCE)).
  eapply search_go_correct.
Defined.

Fixpoint first_nat (p : nat -> bool) (n : nat) : nat :=
  match n with
  | O => 0
  | S n' => if p (first_nat p n') then first_nat p n' else n
  end.

Theorem first_nat_spec (p : nat -> bool) (n : nat)
  (WITNESS : p n = true)
  (m := first_nat p n)
  : p m = true /\ ⟪ MIN : forall i, p i = true -> i >= m ⟫.
Proof with eauto.
  assert (claim1 : forall x, p x = true -> p (first_nat p x) = true).
  { induction x as [ | x IH]... simpl. destruct (p (first_nat p x)) as [ | ] eqn: ?... }
  unnw. split... intros i p_i_eq_true.
  enough (claim2 : forall x, first_nat p x <= x).
  enough (claim3 : forall x, p (first_nat p x) = true -> (forall y, x < y -> first_nat p x = first_nat p y)).
  enough (claim4 : forall x, forall y, p y = true -> first_nat p x <= y)...
  - intros x y p_y_eq_true. destruct (le_gt_dec x y) as [x_le_y | x_gt_y].
    + eapply Nat.le_trans...
    + replace (first_nat p x) with (first_nat p y)...
  - intros x p_first_nat_p_x_eq_true y x_gt_y. induction x_gt_y as [ | y x_gt_y IH]; simpl.
    + rewrite p_first_nat_p_x_eq_true...
    + rewrite <- IH, p_first_nat_p_x_eq_true...
  - induction x as [ | x IH]... simpl.
    destruct (p (first_nat p x)) as [ | ]...
Qed.

Theorem nat_search_lemma (p : nat -> bool)
  (EXISTENCE : exists n : nat, p n = true)
  : { n : nat | p n = true }.
Proof.
  assert (COUNTABLE : isCountable nat).
  { exists id Some. reflexivity. }
  assert (P_dec : forall x : nat, {p x = true} + {p x <> true}).
  { intros x. now destruct (p x) as [ | ]; [left | right]. }
  pose proof (FUEL := @initial_step nat COUNTABLE (fun x : nat => p x = true) EXISTENCE).
  exists (@search_go nat COUNTABLE (fun x : nat => p x = true) P_dec 0 FUEL). eapply search_go_correct.
Defined.

Definition nullary_mu (f : nat -> nat)
  (EXISTENCE : exists n : nat, f n = 0)
  : { n : nat | (forall i, i < n -> exists y, y > 0 /\ f i = y) /\ f n = 0 }.
Proof.
  pose (p := fun n : nat => Nat.eqb (f n) 0).
  assert (EXISTENCE' : exists n : nat, p n = true).
  { destruct EXISTENCE as [n f_n_eq_0]. exists n. unfold p. rewrite Nat.eqb_eq. exact f_n_eq_0. }
  pose proof (nat_search_lemma p EXISTENCE') as [n WITNESS].
  exists (first_nat p n). unnw. pose proof (first_nat_spec p n WITNESS) as claim.
  simpl in claim. unnw. destruct claim as [claim1 claim2]. split.
  - intros i H_lt. specialize claim2 with (i := i). unfold p in claim2. rewrite Nat.eqb_eq in claim2. fold p in claim2. destruct (f i) as [ | y'].
    + lia.
    + exists (S y'). lia.
  - rewrite <- Nat.eqb_eq with (n := f (first_nat p n)) (m := 0). exact claim1.
Defined.

Theorem infinite_descent (P : nat -> Prop)
  (DESCENT : forall n, P n -> exists m, m < n /\ P m)
  : forall n, ~ P n.
Proof.
  intros n. induction (lt_wf n) as [n _ IH]. intros P_n.
  pose proof (DESCENT n P_n) as [m [LT P_m]].
  contradiction (IH m LT P_m).
Qed.

Lemma dec_finds_minimum_if_exists (P : nat -> Prop)
  (DEC : forall n : nat, {P n} + {~ P n})
  (EXISTENCE : exists x, P x)
  : { x : nat | P x /\ ⟪ MIN : forall y, P y -> y >= x ⟫ }.
Proof.
  pose proof (dec_finds_result_if_exists P DEC EXISTENCE) as [n P_n].
  set (p := fun n : nat => if DEC n then true else false).
  assert (claim : forall x, P x <-> p x = true).
  { intros x. unfold p. destruct (DEC x) as [H_yes | H_no]; ss!. }
  exists (first_nat p n). pose proof (first_nat_spec p n) as SPEC.
  rewrite <- claim in SPEC. specialize (SPEC P_n). simpl in SPEC.
  destruct SPEC as [SPEC SPEC']. split; ii; rewrite claim in *; ss!.
Qed.
