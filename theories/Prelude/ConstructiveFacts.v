Require Import PnV.Prelude.Prelude.
Require Import Coq.Logic.Eqdep_dec.
Require Import Coq.Logic.EqdepFacts.

Lemma eq_pirrel_fromEqDec {A : Type} {hasEqDec: hasEqDec A} (lhs : A) (rhs : A)
  (EQ1 : lhs = rhs)
  (EQ2 : lhs = rhs)
  : EQ1 = EQ2.
Proof.
  eapply UIP_dec. exact hasEqDec.
Defined.

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

Lemma Acc_flip_search_step_P_0 (P : A -> Prop)
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
  - eapply Acc_flip_search_step_P_0. exact BOUND.
Defined.

Theorem enumeration_lemma
  (encode_surjective : forall n : nat, exists x, encode x = n)
  : { enum : nat -> A & ⟪ enumerable : forall x, { n : nat | enum n = x } ⟫ }.
Proof.
  exists (fun n : nat => search n (encode_surjective n)). unnw. intros x. exists (encode x).
  assert (claim : encode (search (encode x) (encode_surjective (encode x))) = encode x).
  { eapply search_go_correct with (P := fun y : A => encode y = encode x) (P_dec := fun y : A => Nat.eq_dec (encode y) (encode x)). }
  apply f_equal with (f := decode) in claim. do 2 rewrite decode_encode in claim. congruence.
Defined.

End SEARCH.

Theorem LEM_implies_MarkovPrinciple (LEM : forall P : Prop, P \/ ~ P) (f : nat -> bool) 
  (NOT_ALL_TRUE : ~ forall x, f x = true)
  : { n : nat | f n = false }.
Proof.
  enough (EXISTENCE : exists n : nat, f n = false).
  - assert (COUNTABLE : isCountable nat).
    { exists id Some. reflexivity. }
    assert (P_dec : forall x : nat, {f x = false} + {f x <> false}).
    { intros x. now destruct (f x) as [ | ]; [right | left]. }
    pose proof (FUEL := @Acc_flip_search_step_P_0 nat COUNTABLE (fun x : nat => f x = false) EXISTENCE).
    exists (@search_go nat COUNTABLE (fun x : nat => f x = false) P_dec 0 FUEL). eapply search_go_correct.
  - pose proof (LEM (exists n : nat, f n = false)) as [YES | NO].
    + exact YES.
    + contradiction NOT_ALL_TRUE. intros x. destruct (f x) as [ | ] eqn: H_OBS; now firstorder.
Defined.

Lemma dec_find_result_if_exists (P : nat -> Prop)
  (DEC : forall n, {P n} + {~ P n})
  (EXISTENCE : exists x, P x)
  : { x : nat | P x }.
Proof.
  pose (COUNTABLE := {| encode := id; decode := @Some nat; decode_encode (x : nat) := @eq_refl (option nat) (Some x) |}).
  exists (@search_go nat COUNTABLE P DEC 0 (@Acc_flip_search_step_P_0 nat COUNTABLE P EXISTENCE)).
  eapply search_go_correct.
Defined.
