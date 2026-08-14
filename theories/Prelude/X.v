Require Import PnV.Prelude.Prelude.

Notation "lhs ≠ rhs" := (~ (lhs = rhs)) : type_scope.

Tactic Notation "rewrite*" uconstr( t ) "by" ident ( H_EQ ) :=
  let lhs := fresh "lhs" in
  set (lhs := t) in |- *;
  match type of H_EQ with
  | ?X = ?Y => change (lhs = Y) in H_EQ; rewrite -> H_EQ; subst lhs
  end.

Tactic Notation "use" uconstr( H ) :=
  unshelve hexploit H; [eauto .. | intros p].

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) :=
  hexploit H; cycle -1; [intros p | try eassumption ..]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) :=
  hexploit H; cycle -1; [intros p | exact H1]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) :=
  hexploit H; cycle -1; [intros p | exact H1 | exact H2]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) :=
  hexploit H; cycle -1; [intros p | exact H1 | exact H2 | exact H3]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) :=
  hexploit H; cycle -1; [intros p | exact H1 | exact H2 | exact H3 | exact H4]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) :=
  hexploit H; cycle -1; [intros p | exact H1 | exact H2 | exact H3 | exact H4 | exact H5]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) ident( H6 ) :=
  hexploit H; cycle -1; [intros p | exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H6]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) ident( H6 ) ident( H7 ) :=
  hexploit H; cycle -1; [intros p | exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H6 | exact H7]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) ident( H6 ) ident( H7 ) ident( H8 ) :=
  hexploit H; cycle -1; [intros p | exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H6 | exact H7 | exact H8]; cycle 1.

Tactic Notation "use" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) ident( H6 ) ident( H7 ) ident( H8 ) ident( H9 ) :=
  hexploit H; cycle -1; [intros p | exact H1 | exact H2 | exact H3 | exact H4 | exact H5 | exact H6 | exact H7 | exact H8 | exact H9]; cycle 1.

Tactic Notation "use!" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) :=
  hexploit H; [try (revert H1; clear; i; eauto) .. | intros p].

Tactic Notation "use!" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) :=
  hexploit H; [try (revert H1 H2; clear; i; eauto) .. | intros p].

Tactic Notation "use!" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) :=
  hexploit H; [try (revert H1 H2 H3; clear; i; eauto) .. | intros p].

Tactic Notation "use!" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) :=
  hexploit H; [try (revert H1 H2 H3 H4; clear; i; eauto) .. | intros p].

Tactic Notation "use!" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) :=
  hexploit H; [try (revert H1 H2 H3 H4 H5; clear; i; eauto) .. | intros p].

Tactic Notation "use!" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) ident( H6 ) :=
  hexploit H; [try (revert H1 H2 H3 H4 H5 H6; clear; i; eauto) .. | intros p].

Tactic Notation "use!" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) ident( H6 ) ident( H7 ) :=
  hexploit H; [try (revert H1 H2 H3 H4 H5 H6 H7; clear; i; eauto) .. | intros p].

Tactic Notation "use!" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) ident( H6 ) ident( H7 ) ident( H8 ) :=
  hexploit H; [try (revert H1 H2 H3 H4 H5 H6 H7 H8; clear; i; eauto) .. | intros p].

Tactic Notation "use!" uconstr( H ) "as" simple_intropattern( p ) "with" ident( H1 ) ident( H2 ) ident( H3 ) ident( H4 ) ident( H5 ) ident( H6 ) ident( H7 ) ident( H8 ) ident( H9 ) :=
  hexploit H; [try (revert H1 H2 H3 H4 H5 H6 H7 H8 H9; clear; i; eauto) .. | intros p].

Tactic Notation "use!" uconstr( H ) "as" simple_intropattern( p ) "with" "*" :=
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
