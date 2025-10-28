Require Import PnV.Prelude.Prelude.
Require Import Stdlib.Logic.Eqdep_dec.
Require Import Stdlib.Logic.EqdepFacts.
Require Import Stdlib.Arith.Wf_nat.

Lemma eq_pirrel_fromEqDec {A : Type} {hasEqDec : hasEqDec A} (lhs : A) (rhs : A)
  (EQ1 : lhs = rhs)
  (EQ2 : lhs = rhs)
  : EQ1 = EQ2.
Proof.
  eapply UIP_dec. exact hasEqDec.
Defined.

Lemma exist_eq_bool {A : Type} (P : A -> bool) (x : A) (x' : A) (H : P x = true) (H' : P x' = true)
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
  - destruct (P_dec y) as [YES | NO].
    + exact y.
    + exact (search_go P P_dec (S n) (Acc_inv acc (search_step_Some P n y NO SOME))).
  - exact (search_go P P_dec (S n) (Acc_inv acc (search_step_None P n NONE))).
Defined.

Fixpoint search_go_correct (P : A -> Prop) (P_dec : forall x, {P x} + {~ P x}) (n : nat) (acc : Acc (flip (search_step P)) n) {struct acc} : P (search_go P P_dec n acc).
Proof.
  destruct acc; simpl. destruct (B.Some_dec (decode n)) as [[? ?] | ?].
  - destruct (P_dec x) as [YES | NO].
    + exact YES.
    + eapply search_go_correct.
  - eapply search_go_correct.
Qed.

Fixpoint search_go_pirrel (P : A -> Prop) (P_dec : forall x, {P x} + {~ P x}) (n : nat) (acc : Acc (flip (search_step P)) n) (acc' : Acc (flip (search_step P)) n) {struct acc} : search_go P P_dec n acc = search_go P P_dec n acc'.
Proof.
  destruct acc, acc'; simpl in *.
  destruct (B.Some_dec (decode n)) as [[? ?] | ?] eqn: ?.
  - destruct (P_dec x) as [? | ?].
    + reflexivity.
    + eapply search_go_pirrel.
  - eapply search_go_pirrel.
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
  | S n' => let m := first_nat p n' in if p m then m else n
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
  - intros i H_lt. specialize claim2 with (i := i). unfold p in claim2.
    rewrite Nat.eqb_eq in claim2. fold p in claim2. destruct (f i) as [ | y'].
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
Defined.

#[global] Opaque dec_finds_minimum_if_exists.

Module EQ_FACTS.

Section EQ_CONSTRUCTORS.

Context {A : Type}.

Definition eq_reflexivity (x1 : A) : x1 = x1 :=
  @eq_refl A x1.

Definition eq_symmetry (x1 : A) (x2 : A) (hyp_1EQ2 : x1 = x2) : x2 = x1 :=
  @eq_ind A x1 (fun x : A => x = x1) (@eq_refl A x1) x2 hyp_1EQ2.

Definition eq_transitivity (x1 : A) (x2 : A) (x3 : A) (hyp_1EQ2 : x1 = x2) (hyp_2EQ3 : x2 = x3) : x1 = x3 :=
  @eq_ind A x2 (fun x : A => x1 = x) hyp_1EQ2 x3 hyp_2EQ3.

Context {B : Type}.

Definition eq_congruence (f : A -> B) (x1 : A) (x2 : A) (hyp_1EQ2 : x1 = x2) : f x1 = f x2 :=
  @eq_ind A x1 (fun x : A => f x1 = f x) (@eq_refl B (f x1)) x2 hyp_1EQ2.

Context {C : Type}.

Definition eq_congruence2 (f : A -> B -> C) (x1 : A) (x2 : A) (hyp_x_EQ : x1 = x2) (y1 : B) (y2 : B) (hyp_y_EQ : y1 = y2) : f x1 y1 = f x2 y2 :=
  @eq_ind B y1 (fun y : B => f x1 y1 = f x2 y) (@eq_ind A x1 (fun x : A => f x1 y1 = f x y1) (@eq_refl C (f x1 y1)) x2 hyp_x_EQ) y2 hyp_y_EQ.

End EQ_CONSTRUCTORS.

Section EQ_DESTRUCTORS.

Context {A : Type}.

Definition rect_eq_l (lhs : A) (phi : forall rhs : A, lhs = rhs -> Type) (phi_pf : phi lhs (eq_reflexivity lhs)) (rhs : A) (hyp_eq : lhs = rhs) : phi rhs hyp_eq :=
  match hyp_eq as hyp_eq' in eq _ lhs' return phi lhs' hyp_eq' with
  | eq_refl => phi_pf
  end.

Definition rect_eq_r_aux (rhs : A) (lhs : A) (hyp_eq : lhs = rhs) : forall phi : forall lhs : A, lhs = rhs -> Type, phi rhs (eq_reflexivity rhs) -> phi lhs hyp_eq :=
  match hyp_eq as hyp_eq' in eq _ rhs' return forall phi' : forall lhs' : A, lhs' = rhs' -> Type, phi' rhs' (eq_reflexivity rhs') -> phi' lhs hyp_eq' with
  | eq_refl => fun phi' : forall lhs' : A, lhs' = lhs -> Type => fun phi_pf' : phi' lhs (eq_reflexivity lhs) => phi_pf'
  end.

Definition rect_eq_r (rhs : A) (phi : forall lhs : A, lhs = rhs -> Type) (phi_pf : phi rhs (eq_reflexivity rhs)) (lhs : A) (hyp_eq : lhs = rhs) : phi lhs hyp_eq :=
  rect_eq_r_aux rhs lhs hyp_eq phi phi_pf.

Context {B : A -> Type}.

Definition elim_eq_l (x1 : A) (x2 : A) (hyp_eq : x1 = x2) (pf : B x1) : B x2 :=
  eq_rect x1 B pf x2 hyp_eq.

Definition elim_eq_r (x1 : A) (x2 : A) (hyp_eq : x1 = x2) (pf : B x2) : B x1 :=
  eq_rect x2 B pf x1 (eq_symmetry x1 x2 hyp_eq).

#[local] Notation pi_A_B := (forall x : A, B x).

Lemma elim_eq_l_spec (x1 : A) (x2 : A) (f : pi_A_B) (hyp_eq : x1 = x2)
  : elim_eq_l x1 x2 hyp_eq (f x1) = elim_eq_l x2 x2 (eq_reflexivity x2) (f x2).
Proof.
  destruct hyp_eq; reflexivity.
Defined.

Lemma elim_eq_r_spec (x1 : A) (x2 : A) (f : pi_A_B) (hyp_eq : x1 = x2)
  : elim_eq_r x1 x2 hyp_eq (f x2) = elim_eq_r x1 x1 (eq_reflexivity x1) (f x1).
Proof.
  destruct hyp_eq; reflexivity.
Defined.

Definition transport {x1 : A} {x2 : A} (hyp_eq : x1 = x2) : B x1 -> B x2 :=
  elim_eq_l x1 x2 hyp_eq.

End EQ_DESTRUCTORS.

Section EQ_EM_implies_EQ_PIRREL. (* Reference: "https://coq.inria.fr/library/Coq.Logic.Eqdep_dec.html" *)

Context {A : Type}.

Definition eq_round_trip (x : A) : forall y : A, forall hyp_eq : x = y, eq_transitivity y x y (eq_symmetry x y hyp_eq) hyp_eq = eq_reflexivity y :=
  rect_eq_l x (fun y : A => fun hyp_eq : x = y => eq_transitivity y x y (eq_symmetry x y hyp_eq) hyp_eq = eq_reflexivity y) (eq_reflexivity (eq_reflexivity x)).

Variable x : A.

Section ABSTRACT_FORM.

Variable eq_encoder : forall y : A, x = y -> x = y.

Let eq_decoder (y : A) : x = y -> x = y :=
  eq_transitivity x x y (eq_symmetry x x (eq_encoder x (eq_reflexivity x))).

Let eq_decoder_decodes_properly : forall y : A, forall hyp_eq : x = y, eq_decoder y (eq_encoder y hyp_eq) = hyp_eq :=
  rect_eq_l x (fun y : A => fun hyp_eq : x = y => eq_decoder y (eq_encoder y hyp_eq) = hyp_eq) (eq_round_trip x x (eq_encoder x (eq_reflexivity x))).

Hypothesis all_eq_codes_are_indistinguishable_from_each_other : forall y : A, forall hyp_eq1 : x = y, forall hyp_eq2 : x = y, eq_encoder y hyp_eq1 = eq_encoder y hyp_eq2.

Definition eq_pirrel_holds_if_we_have_an_eq_encoder_which_returns_the_same_code (y : A) (hyp_eq1 : x = y) (hyp_eq2 : x = y) : hyp_eq1 = hyp_eq2 :=
  let claim1 : eq_decoder y (eq_encoder y hyp_eq1) = eq_decoder y (eq_encoder y hyp_eq2) := eq_congruence (eq_decoder y) (eq_encoder y hyp_eq1) (eq_encoder y hyp_eq2) (all_eq_codes_are_indistinguishable_from_each_other y hyp_eq1 hyp_eq2) in
  eq_ind (eq_decoder y (eq_encoder y hyp_eq2)) (fun hyp_eq : x = y => hyp_eq1 = hyp_eq) (eq_ind (eq_decoder y (eq_encoder y hyp_eq1)) (fun hyp_eq : x = y => hyp_eq = eq_decoder y (eq_encoder y hyp_eq2)) claim1 hyp_eq1 (eq_decoder_decodes_properly y hyp_eq1)) hyp_eq2 (eq_decoder_decodes_properly y hyp_eq2).

End ABSTRACT_FORM.

Hypothesis eq_em : forall y : A, x = y \/ x <> y.

Let my_eq_encoder (y : A) (hyp_eq : x = y) : x = y :=
  match eq_em y return x = y with
  | or_introl h_eq => h_eq
  | or_intror h_ne => False_ind (x = y) (h_ne hyp_eq)
  end.

Lemma my_eq_encoder_x_eq_reflexivity_x_is
  (hyp_eq : x = x)
  : my_eq_encoder x (eq_reflexivity x) = my_eq_encoder x hyp_eq.
Proof.
  refine (
    let ret (eq_em_x : x = x \/ x <> x) (h_eq : x = x) :=
    match eq_em_x return x = x with
    | or_introl Heq => Heq
    | or_intror Hne => False_ind (x = x) (Hne h_eq)
    end in _
  ).
  exact (
    match eq_em x as eq_em_x return ret eq_em_x (eq_reflexivity x) = ret eq_em_x hyp_eq with
    | or_introl h_eq => eq_reflexivity h_eq
    | or_intror h_ne => False_ind (False_ind (x = x) (h_ne (eq_reflexivity x)) = False_ind (x = x) (h_ne hyp_eq)) (h_ne hyp_eq)
    end
  ).
Defined.

Definition eq_em_implies_eq_pirrel : forall y : A, forall hyp_eq1 : x = y, forall hyp_eq2 : x = y, hyp_eq1 = hyp_eq2 :=
  eq_pirrel_holds_if_we_have_an_eq_encoder_which_returns_the_same_code my_eq_encoder (rect_eq_l x (fun y : A => fun hyp_eq1 : x = y => forall hyp_eq2 : x = y, my_eq_encoder y hyp_eq1 = my_eq_encoder y hyp_eq2) my_eq_encoder_x_eq_reflexivity_x_is).

End EQ_EM_implies_EQ_PIRREL.

Lemma eq_pirrel_fromEqDec {A : Type} {requiresEqDec : hasEqDec A}
  : forall x : A, forall y : A, forall hyp_eq1 : x = y, forall hyp_eq2 : x = y, hyp_eq1 = hyp_eq2.
Proof.
  intros x.
  refine (
    let eq_em (y : A) :=
    match eq_dec x y with
    | left hyp_yes => or_introl hyp_yes
    | right hyp_no => or_intror hyp_no
    end in _
  ).
  exact (fun y : A => fun hyp_eq1 : x = y =>
    match hyp_eq1 as hyp_eq1' in eq _ y' return forall hyp_eq : x = y', hyp_eq1' = hyp_eq with
    | eq_refl => eq_em_implies_eq_pirrel x eq_em x (eq_reflexivity x)
    end
  ).
Defined.

End EQ_FACTS.

Module FUN_FACTS.

Import EQ_FACTS.

Definition projT2_eq_STMT (A : Type) (B : A -> Type) (x : A) : Prop :=
  forall y1 : B x, forall y2 : B x, << PAIR_EQ : @existT A B x y1 = @existT A B x y2 >> -> y1 = y2.

Definition axiomK_STMT (A : Type) (x : A) : Prop :=
  forall phi : x = x -> Prop, << phi_refl : phi (eq_reflexivity x) >> -> forall hyp_eq : x = x, phi hyp_eq.

Definition eq_rect_eq_STMT (A : Type) (phi : A -> Type) (x : A) : Prop :=
  forall phi_x : phi x, forall hyp_eq : x = x, @eq_rect A x phi phi_x x hyp_eq = phi_x.

Definition pirrel_STMT (phi : Prop) : Prop :=
  forall pf1 : phi, forall pf2 : phi, pf1 = pf2.

Inductive BB : Prop :=
  | TrueBB
  | FalseBB.

Record RETRACT (A : Prop) (B : Prop) : Prop :=
  { _i : A -> B
  ; _j : B -> A
  ; _inv : forall x : A, _j (_i x) = x
  }.

#[global] Arguments _i {A} {B}.
#[global] Arguments _j {A} {B}.
#[global] Arguments _inv {A} {B}.

Record RETRACT2 (A : Prop) (B : Prop) : Prop :=
  { _i2 : A -> B
  ; _j2 : B -> A
  ; _inv2 : RETRACT A B -> forall x : A, _j2 (_i2 x) = x
  }.

#[global] Arguments _i2 {A} {B}.
#[global] Arguments _j2 {A} {B}.
#[global] Arguments _inv2 {A} {B}.

Definition RETRACT_REFL (A : Prop) : RETRACT A A :=
  {| _i := fun x : A => x; _j := fun x : A => x; _inv := @eq_refl A |}.

#[local] Hint Resolve _inv _inv2 RETRACT_REFL : core.

Lemma derive_fixedpoint_combinator (D : Prop)
  (RETRACT_DtoD_D : RETRACT (D -> D) D)
  : {Y : (D -> D) -> D | forall f : D -> D, Y f = f (Y f)}.
Proof.
  destruct RETRACT_DtoD_D as [lam_D app_D beta_D].
  pose (Y_combinator_of_Curry := fun f : D -> D => app_D (lam_D (fun x : D => f (app_D x x))) (lam_D (fun x : D => f (app_D x x)))).
  exists (Y_combinator_of_Curry). intros f.
  change (app_D (lam_D (fun x : D => f (app_D x x))) (lam_D (fun x : D => f (app_D x x))) = f (Y_combinator_of_Curry f)).
  now replace (app_D (lam_D (fun x : D => f (app_D x x)))) with (fun x : D => f (app_D x x)).
Qed.

Lemma TrueBB_eq_FalseBB_iff_pirrel
  : TrueBB = FalseBB <-> ⟪ PROOF_IRRELEVANCE : forall phi : Prop, pirrel_STMT phi ⟫.
Proof.
  unnw. split.
  - intros hyp_eq phi pf1 pf2. exact (eq_congruence (fun b : BB => if b then pf1 else pf2) TrueBB FalseBB hyp_eq).
  - intros h_pirrel. exact (h_pirrel BB TrueBB FalseBB).
Qed.

Lemma pirrel_iff_eq_rect_eq (A : Type) (x : A)
  : ⟪ PROOF_IRRELEVANCE : pirrel_STMT (x = x) ⟫ <-> ⟪ EQ_RECT_EQ : forall B : A -> Type, eq_rect_eq_STMT A B x ⟫.
Proof.
  ii; split; ii; des.
  - now rewrite H with (pf1 := hyp_eq) (pf2 := eq_reflexivity x).
  - now do 2 (match goal with [ pf : x = x |- _ ] => rewrite <- H with (B := eq x) (phi_x := pf) (hyp_eq := eq_symmetry x x pf); destruct pf end).
Qed.

Lemma pirrel_iff_axiomK (A : Type) (x : A)
  : ⟪ PROOF_IRRELEVANCE : pirrel_STMT (x = x) ⟫ <-> ⟪ AXIOM_K : axiomK_STMT A x ⟫.
Proof.
  ii; split; ii; des.
  - now rewrite H with (pf1 := hyp_eq) (pf2 := eq_reflexivity x).
  - now do 2 (match goal with [ pf : x = x |- _ ] => pattern pf; revert pf; eapply H end).
Qed.

Lemma eq_rect_eq_iff_projT2_eq (A : Type) (B : A -> Type) (x : A)
  : ⟪ EQ_RECT_EQ : eq_rect_eq_STMT A B x ⟫ <-> ⟪ projT2_eq : projT2_eq_STMT A B x ⟫.
Proof.
  ii; split; ii; des.
  - set (phi := fun pr1 : @sigT A B => fun pr2 : @sigT A B => fun projT1_eq : projT1 pr1 = projT1 pr2 => @eq_rect A (projT1 pr1) B (projT2 pr1) (projT1 pr2) projT1_eq = projT2 pr2).
    assert (claim1 : phi (@existT A B x y1) (@existT A B x y2) (eq_congruence (@projT1 A B) (@existT A B x y1) (@existT A B x y2) H0)) by now rewrite <- H0.
    unfold phi in claim1. rewrite H in claim1. exact (claim1).
  - eapply H. now destruct hyp_eq.
Qed.

Section EXCLUSIVE_MIDDLE_implies_PROOF_IRRELEVANCE. (* Reference: "https://coq.inria.fr/library/Coq.Logic.Berardi.html" *)

Hypothesis exclusive_middle : forall P : Prop, P \/ ~ P.

Let POW (P : Prop) : Prop :=
  P -> BB.

Let RETRACT2_POW_A_POW_B (A : Prop) (B : Prop)
  : RETRACT2 (POW A) (POW B).
Proof.
  destruct (exclusive_middle (RETRACT (POW A) (POW B))) as [hyp_yes | hyp_no].
  - exact ({| _i2 := _i hyp_yes; _j2 := _j hyp_yes; _inv2 := fun _ : RETRACT (POW A) (POW B) => _inv hyp_yes |}).
  - exact ({| _i2 := fun _ : POW A => fun _ : B => FalseBB; _j2 := fun _ : POW B => fun _ : A => FalseBB; _inv2 := fun r : RETRACT (POW A) (POW B) => False_ind (forall pa : POW A, (fun _ : A => FalseBB) = pa) (hyp_no r) |}).
Qed.

Let UNIV : Prop :=
  forall P : Prop, POW P.

Let SET_BUILDER_NOTATION (phi : UNIV -> BB) : UNIV :=
  fun P : Prop =>
  let LEFT : POW UNIV -> POW P := _j2 (RETRACT2_POW_A_POW_B P UNIV) in
  let RIGHT : POW UNIV -> POW UNIV := _i2 (RETRACT2_POW_A_POW_B UNIV UNIV) in
  LEFT (RIGHT phi).

#[local] Notation " ⦃ x | P ⦄ " := (SET_BUILDER_NOTATION (fun x : UNIV => P)) (x binder, at level 0, no associativity) : type_scope.

Let HAS_AS_AN_ELEMENT (x : UNIV) : UNIV -> BB :=
  x UNIV.

#[local] Notation " z ∈ x " := (HAS_AS_AN_ELEMENT x z) : type_scope.

Let SET_BUILDER_NOTATION_SPEC (phi : UNIV -> BB)
  : (fun z : UNIV => z ∈ ⦃ x | phi x ⦄) = phi.
Proof.
  unfold SET_BUILDER_NOTATION, HAS_AS_AN_ELEMENT.
  destruct (RETRACT2_POW_A_POW_B UNIV UNIV); cbn in *; eauto.
Qed.

Let NAIVE_SET_THEORY : RETRACT (POW UNIV) UNIV :=
  {| _i := SET_BUILDER_NOTATION; _j := HAS_AS_AN_ELEMENT; _inv := SET_BUILDER_NOTATION_SPEC |}.

Let NotBB (b : BB) : BB :=
  match exclusive_middle (b = TrueBB) return BB with
  | or_introl if_b_eq_TRUE_BB => FalseBB
  | or_intror if_b_ne_TRUE_BB => TrueBB
  end.

#[local] Notation " ¬ b " := (NotBB b) (at level 55, right associativity) : type_scope.

Let NOT_BB_SPEC1 (b : BB)
  (if_b_eq_TrueBB : b = TrueBB)
  : (¬ b) = FalseBB.
Proof.
  cbv; destruct (exclusive_middle (b = TrueBB)); tauto.
Qed.

Let NOT_BB_SPEC2 (b : BB)
  (if_b_ne_TrueBB : b <> TrueBB)
  : (¬ b) = TrueBB.
Proof.
  cbv; destruct (exclusive_middle (b = TrueBB)); tauto.
Qed.

Let russell (r : UNIV) : BB :=
  ¬ (r ∈ r).

Let R : UNIV :=
  ⦃ r | russell r ⦄.

Let RUSSELL : BB :=
  R ∈ R.

Let PARADOX_OF_BERARDI
  : RUSSELL = ¬ RUSSELL.
Proof with eauto.
  enough (it_is_sufficient_to_show : RUSSELL = russell R)...
  replace (russell) with (fun r : UNIV => r ∈ R)...
Qed.

Theorem exclusive_middle_implies_proof_irrelevance (P : Prop)
  : pirrel_STMT P.
Proof.
  eapply TrueBB_eq_FalseBB_iff_pirrel.
  destruct (exclusive_middle (RUSSELL = TrueBB)) as [RUSSELL_eq_TrueBB | RUSSELL_ne_TrueBB].
  - rewrite <- RUSSELL_eq_TrueBB. rewrite PARADOX_OF_BERARDI. now eapply NOT_BB_SPEC1.
  - contradiction (RUSSELL_ne_TrueBB). rewrite PARADOX_OF_BERARDI. now eapply NOT_BB_SPEC2.
Qed.

End EXCLUSIVE_MIDDLE_implies_PROOF_IRRELEVANCE.

Section UNTYPED_LAMBDA_CALCULUS_FOR_BB_implies_PARADOX_OF_RUSSELL.

Hypothesis untyped_lambda_calculus_for_BB : RETRACT (BB -> BB) BB.

Let NotBB (b : BB) : BB :=
  match b return BB with
  | TrueBB => FalseBB
  | FalseBB => TrueBB
  end.

Theorem untyped_lambda_calculus_for_BB_implies_paradox_of_russell
  : TrueBB = FalseBB.
Proof.
  pose proof (derive_fixedpoint_combinator BB untyped_lambda_calculus_for_BB) as [Y Y_spec]. set (RUSSELL := Y NotBB).
  assert (PARADOX_OF_RUSSELL : RUSSELL = NotBB RUSSELL) by exact (Y_spec NotBB). now destruct RUSSELL.
Qed.

End UNTYPED_LAMBDA_CALCULUS_FOR_BB_implies_PARADOX_OF_RUSSELL.

Section PROPOSITIONAL_EXTENSIONALITY_implies_PROOF_IRRELEVANCE. (* Reference: "https://coq.inria.fr/library/Coq.Logic.ClassicalFacts.html" *)

Hypothesis propositional_extensionality : forall P1 : Prop, forall P2 : Prop, (P1 <-> P2) -> (P1 = P2).

Let D_coerce_D_ARROW_D_for_any_inhabited_Prop_D (D : Prop)
  (D_inhabited : inhabited D)
  : D = (D -> D).
Proof.
  destruct D_inhabited as [D_holds].
  eapply propositional_extensionality; tauto.
Qed.

Let UNTYPED_LAMBDA_CALCULUS_for_any_inhabited_Prop (D : Prop)
  (D_inhabited : inhabited D)
  : RETRACT (D -> D) D.
Proof.
  replace (D -> D) with (D); eauto.
Qed.

Theorem propositional_extensionality_implies_proof_irrelevance (P : Prop)
  : pirrel_STMT P.
Proof.
  assert (BB_inhabited : inhabited BB) by now constructor; exact (FalseBB).
  eapply TrueBB_eq_FalseBB_iff_pirrel, untyped_lambda_calculus_for_BB_implies_paradox_of_russell; eauto.
Qed.

End PROPOSITIONAL_EXTENSIONALITY_implies_PROOF_IRRELEVANCE.

Lemma propositional_extensionality_implies_proof_irrelevance_variant1
  (PROPOSITIONAL_EXTENSIONALITY : forall P1 : Prop, forall P2 : Prop, (P1 <-> P2) -> (P1 = P2))
  : forall P : Prop, pirrel_STMT P.
Proof. (* Thanks to Minki Cho *)
  intros P p. assert (P_is_True : P = True) by now eapply PROPOSITIONAL_EXTENSIONALITY; tauto.
  revert p. subst P. now intros [] [].
Qed.

Section GIRARD'S_PARADOX. (* Reference: "https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Bug.20in.20kernel.20level.20normalization/near/306169266" *)

Universe u.

#[local] Notation star := Type@{u}.

Theorem GIRARD'S_PARADOX
  (PI : (star -> star) -> star)
  (LAM : forall A : star -> star, (forall x, A x) -> PI A)
  (APP : forall A : star -> star, PI A -> (forall x, A x))
  (BETA: forall A : star -> star, forall f, forall x, APP A (LAM A f) x = f x)
  : forall X : Prop, X.
Proof.
  set (F X := (ensemble (ensemble X) -> X) -> ensemble (ensemble X)).
  set (U := PI F).
  refine (let G (T : ensemble (ensemble U)) (X : Type) : F X := fun f => fun p => T (fun x => p (f (APP F x X f))) in _).
  refine (let tau (T : ensemble (ensemble U)) : U := LAM F (G T) in _).
  refine (let sigma (S : U) : ensemble (ensemble U) := APP F S U tau in _).
  assert (sigma_tau : forall s, forall S, sigma (tau S) s <-> S (fun x => s (tau (sigma x)))).
  { intros s S. enough (WTS : sigma (tau S) s = S (fun x => s (tau (sigma x)))) by now rewrite WTS.
    specialize BETA with (f := G S) (x := U). apply f_equal with (f := fun phi => phi tau s) in BETA. exact BETA.
  }
  refine (let omega : ensemble (ensemble U) := fun p => forall x, sigma x p -> p x in _).
  refine (let delta (S : ensemble (ensemble U)) := forall p, S p -> p (tau S) in _).
  assert (delta_omega : delta omega).
  { intros p d. eapply d. rewrite -> sigma_tau. intros x h. eapply d. rewrite -> sigma_tau. exact h. }
  exact (fun X : Prop => delta_omega (fun y => delta (sigma y) -> X) (fun x => fun e => fun f => f _ e (fun p => fun h => f _ (proj1 (sigma_tau _ _) h))) (fun p => fun h => delta_omega _ (proj1 (sigma_tau _ _) h))).
Qed.

End GIRARD'S_PARADOX.

Section option_injective. (* Reference: https://proofassistants.stackexchange.com/a/5248/3232 *)

#[local] Obligation Tactic := intros; simpl.

#[local] Existing Instance Equipotent_Symmetric.

Section option_injective_aux.

Context {A : Type} {B : Type} (option_A_eq_option_B : Equipotent (option A) (option B)).

Lemma option_injective_aux_lemma (x : A)
  (EQ : _rarr (Some x) = _rarr None)
  : False.
Proof.
  apply f_equal with (f := _larr) in EQ.
  now do 2 rewrite _larr_rarr in EQ.
Qed.

Definition option_injective_aux (x : A) (o1 : option B) (o2 : option B) : _rarr (Some x) = o1 -> _rarr None = o2 -> B :=
  match o1, o2 with
  | Some y1, Some y2 => fun _ => fun _ => y1
  | Some y1, None => fun _ => fun _ => y1
  | None, Some y2 => fun _ => fun _ => y2
  | None, None => fun EQ1 : _rarr (Some x) = None => fun EQ2 : _rarr None = None =>
    let EQ3 : _rarr (Some x) = _rarr None := eq_transitivity _ _ _ EQ1 (eq_symmetry _ _ EQ2) in
    @False_rect B (option_injective_aux_lemma x EQ3)
  end.

End option_injective_aux.

#[local]
Tactic Notation "safedestruct2" uconstr( X ) uconstr( Y ) :=
  let ea := fresh "ea" in let eb := fresh "eb" in
  gen (@eq_refl _ X) as ea; gen (@eq_refl _ Y) as eb;
  let oa := fresh "oa" in let ob := fresh "ob" in
  generalize X at -1 as oa; generalize Y at -1 as ob;
  intros; destruct oa, ob; subst; cbn.

#[local]
Ltac Tac.lightening_hook ::=
  match goal with
  | [ H1 : _ = ?X, H2 : context [?X] |- _ ] => rewrite <- H1 in H2; done!
  end.

Context {A : Type} {B : Type} (option_A_eq_option_B : Equipotent (option A) (option B)).

#[local, program]
Instance option_injective : Equipotent A B :=
  { _rarr (x : A) := option_injective_aux option_A_eq_option_B x (_rarr (Some x)) (_rarr None) eq_refl eq_refl
  ; _larr (y : B) := option_injective_aux (Equipotent_Symmetric option_A_eq_option_B) y (_rarr (Some y)) (_rarr None) eq_refl eq_refl
  }.
Next Obligation.
  safedestruct2 (_larr (Some y)) (_larr None); first [safedestruct2 (_rarr (Some a)) (_rarr None); Tac.lightening_hook | Tac.lightening].
Qed.
Next Obligation.
  safedestruct2 (_rarr (Some x)) (_rarr None); first [safedestruct2 (_larr (Some b)) (_larr None); Tac.lightening_hook | Tac.lightening].
Qed.

End option_injective.

Lemma existT_eq_existT_elim {A : Type} {B : A -> Type} (x1 : A) (x2 : A) (y1 : B x1) (y2 : B x2)
  (existT_eq_existT : @existT A B x1 y1 = @existT A B x2 y2)
  : { H : x1 = x2 | @eq_rect A x1 B y1 x2 H = y2 }.
Proof.
  change x2 with (projT1 (@existT A B x2 y2)).
  change y2 with (projT2 (@existT A B x2 y2)) at 5.
  destruct existT_eq_existT; simpl. exists eq_refl. reflexivity.
Qed.

End FUN_FACTS.
