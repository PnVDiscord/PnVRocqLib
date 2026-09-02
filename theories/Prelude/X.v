Require Import Stdlib.NArith.BinNat.
Require Export PnV.Prelude.Prelude.
Require Export PnV.Prelude.PnVTacs.

#[universes(polymorphic=yes)]
Definition mp@{u v | } {A : Type@{u}} {B : Type@{v}} (x : A) (f : A -> B) : B :=
  f x.

#[global] Arguments mp {A} {B} /.

Infix "&" := mp (at level 90, left associativity).

Notation "lhs ≠ rhs" := (~ (lhs = rhs)) : type_scope.

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

Section ITERATE_UNTIL.

Context {A : Type}.

Fixpoint iter (fuel : nat) (step : A -> A) (x : A) {struct fuel} : A :=
  match fuel with
  | O => x
  | S fuel' => iter fuel' step (step x)
  end.

Lemma iter_succ (fuel : nat) (step : A -> A) (x : A)
  : iter (S fuel) step x = step (iter fuel step x).
Proof.
  revert x; induction fuel as [ | fuel IH]; intros x; simpl.
  - reflexivity.
  - eapply IH.
Qed.

Lemma iter_invariant (P : A -> Prop) (F : A -> A) (n : nat) (x : A)
  (STEP : forall y : A, P y -> P (F y))
  (BASE : P x)
  : P (iter n F x).
Proof.
  revert x BASE. induction n as [ | n IH]; intros x BASE.
  - exact BASE.
  - simpl. eapply IH. eapply STEP. exact BASE.
Qed.

Lemma iter_fixed (n : nat) (F : A -> A) (x : A)
  (FIXED : F x = x)
  : iter n F x = x.
Proof.
  revert x FIXED. induction n as [ | n IH]; intros x FIXED.
  - reflexivity.
  - simpl. rewrite FIXED. eapply IH. exact FIXED.
Qed.

Context {A_hasEqDec : hasEqDec A}.

Fixpoint iterun (n : nat) (F : A -> A) (x : A) {struct n} : A :=
  match n with
  | O => x
  | S n' =>
    let y := F x in
    if eqb y x then x else iterun n' F y
  end.

Theorem iterun_eq_iter (n : nat) (F : A -> A) (x : A)
  : iterun n F x = iter n F x.
Proof.
  revert x. induction n as [ | n IH]; intros x.
  - reflexivity.
  - simpl. destruct (eqb (F x) x) as [ | ] eqn: H_OBS.
    + rewrite eqb_eq in H_OBS. rewrite H_OBS. symmetry. eapply iter_fixed. exact H_OBS.
    + eapply IH.
Qed.

End ITERATE_UNTIL.

#[global] Hint Rewrite @iter_succ : simplication_hints.

Section splits.

Context {X : Type}.

Fixpoint splits (xs : list X) {struct xs} : list (list X * list X) :=
  match xs with
  | [] => [([], [])]
  | x :: xs' => ([], x :: xs') :: L.map (fun '(ys, zs) => (x :: ys, zs)) (splits xs')
  end.

Lemma splits_nil_head (xs : list X)
  : L.In ([], xs) (splits xs).
Proof.
  destruct xs as [ | x xs]; simpl; now left.
Qed.

Lemma splits_shift (omega : list X) (alpha : list X) (x : X) (beta : list X)
  (IN : L.In (alpha, x :: beta) (splits omega))
  : L.In (alpha ++ [x], beta) (splits omega).
Proof.
  revert alpha beta IN. induction omega as [ | y omega IH]; intros alpha beta IN.
  - simpl in IN. destruct IN as [EQ | []]. congruence.
  - simpl in IN. destruct IN as [EQ | IN].
    + inversion EQ; subst. simpl.
      right. rewrite L.in_map_iff. exists ([], beta). split.
      * reflexivity.
      * eapply splits_nil_head.
    + rewrite L.in_map_iff in IN. destruct IN as ([alpha' beta'] & EQ & IN').
      simpl in EQ. inversion EQ; subst. simpl.
      right. rewrite L.in_map_iff. exists (alpha' ++ [x], beta). split.
      * reflexivity.
      * eapply IH. exact IN'.
Qed.

End splits.

Definition mfail_if (b : bool) : option unit :=
  if b then None else Some tt.

Definition mfail_unless (b : bool) : option unit :=
  mfail_if (negb b).

Lemma bind_Some_inv {A : Type} {B : Type} (o : option A) (f : A -> option B) (b : B)
  (EQ : (o >>= f) = Some b)
  : exists a : A, o = Some a /\ f a = Some b.
Proof.
  destruct o as [a | ]; [exists a; split; [reflexivity | exact EQ] | discriminate EQ].
Qed.

Lemma mfail_if_Some_inv {A : Type} (b : bool) (f : unit -> option A) (a : A)
  (EQ : (mfail_if b >>= f) = Some a)
  : b = false /\ f tt = Some a.
Proof.
  pose proof (bind_Some_inv (mfail_if b) f a EQ) as (u & EQ1 & EQ2).
  destruct b as [ | ]; [discriminate EQ1 | ].
  destruct u. split; [reflexivity | exact EQ2].
Qed.

Lemma mfail_unless_Some_inv {A : Type} (b : bool) (f : unit -> option A) (a : A)
  (EQ : (mfail_unless b >>= f) = Some a)
  : b = true /\ f tt = Some a.
Proof.
  pose proof (mfail_if_Some_inv (negb b) f a EQ) as [NEG EQ'].
  destruct b as [ | ]; [split; [reflexivity | exact EQ'] | discriminate NEG].
Qed.

Inductive rtc {A : Type} (R : A -> A -> Prop) (x : A) : A -> Prop :=
  | rtc_refl
    : rtc R x x
  | rtc_step (y : A) (z : A)
    (STEP : R x y)
    (REST : rtc R y z)
    : rtc R x z.

Inductive rtcn {A : Type} (R : A -> A -> Prop) : nat -> A -> A -> Prop :=
  | rtcn_O (x : A)
    : rtcn R O x x
  | rtcn_S (n : nat) (x : A) (y : A) (z : A)
    (STEP : R x y)
    (REST : rtcn R n y z)
    : rtcn R (S n) x z.

Inductive lexlt (p : nat * nat) (p' : nat * nat) : Prop :=
  | lexlt_fst
    (LT : fst p < fst p')
    : lexlt p p'
  | lexlt_snd
    (EQ : fst p = fst p')
    (LT : snd p < snd p')
    : lexlt p p'.

Lemma lexlt_aux_fst (a' : nat) (a0 : nat) (a : nat)
  (C : Nat.ltb a' a0 = true)
  (E : a0 = a)
  : a' < a.
Proof.
  rewrite Nat.ltb_lt in C. lia.
Qed.

Lemma lexlt_aux_snd (a' : nat) (b' : nat) (a0 : nat) (b : nat)
  (H : lexlt (a', b') (a0, b))
  (C : Nat.ltb a' a0 = false)
  : b' < b.
Proof.
  inversion H; simpl in *; [rewrite Nat.ltb_ge in C; lia | lia].
Qed.

Lemma lexlt_aux_eq (a' : nat) (b' : nat) (a0 : nat) (b : nat) (a : nat)
  (H : lexlt (a', b') (a0, b))
  (C : Nat.ltb a' a0 = false)
  (E : a0 = a)
  : a' = a.
Proof.
  inversion H; simpl in *; [rewrite Nat.ltb_ge in C; lia | lia].
Qed.

Definition lexAccB (a : nat) (rec : forall a' : nat, a' < a -> forall b' : nat, Acc lexlt (a', b')) : forall b : nat, Acc Nat.lt b -> forall a0 : nat, a0 = a -> Acc lexlt (a0, b).
Proof.
  refine (fix goB (b : nat) (H_Acc : Acc Nat.lt b) {struct H_Acc} : forall a0 : nat, a0 = a -> Acc lexlt (a0, b) := _).
  intros a0 E0. econs. intros p H. destruct p as [a' b'].
  destruct (Nat.ltb a' a0) as [ | ] eqn: C.
  - exact (rec a' (lexlt_aux_fst a' a0 a C E0) b').
  - exact (goB b' (Acc_inv H_Acc (lexlt_aux_snd a' b' a0 b H C)) a' (lexlt_aux_eq a' b' a0 b a H C E0)).
Defined.

Definition lexAcc : forall a : nat, Acc Nat.lt a -> forall b : nat, Acc lexlt (a, b).
Proof.
  refine (fix goA (a : nat) (H_Acc : Acc Nat.lt a) {struct H_Acc} : forall b : nat, Acc lexlt (a, b) := _).
  exact (fun b => lexAccB a (fun a' : nat => fun LT : a' < a => goA a' (Acc_inv H_Acc LT)) b (lt_wf b) a eq_refl).
Defined.

Definition lexlt_wf : well_founded lexlt.
Proof.
  intros [a b]. exact (lexAcc a (lt_wf a) b).
Defined.

Definition lexltb (p : nat * nat) (p' : nat * nat) : bool :=
  Nat.ltb (fst p) (fst p') || (Nat.eqb (fst p) (fst p') && Nat.ltb (snd p) (snd p')).

Lemma lexltb_lexlt (p : nat * nat) (p' : nat * nat)
  (TEST : lexltb p p' = true)
  : lexlt p p'.
Proof.
  unfold lexltb in TEST. destruct (Nat.ltb (fst p) (fst p')) as [ | ] eqn: C; simpl in TEST.
  - eapply lexlt_fst. rewrite Nat.ltb_lt in C. exact C.
  - rewrite andb_true_iff in TEST. destruct TEST as [EQ LT].
    rewrite Nat.eqb_eq in EQ. rewrite Nat.ltb_lt in LT.
    eapply lexlt_snd; [exact EQ | exact LT].
Qed.

Lemma lexlt_lexltb (p : nat * nat) (p' : nat * nat)
  (LT : lexlt p p')
  : lexltb p p' = true.
Proof.
  unfold lexltb. destruct (Nat.ltb (fst p) (fst p')) as [ | ] eqn: C; [reflexivity | simpl].
  rewrite Nat.ltb_ge in C. rewrite andb_true_iff, Nat.eqb_eq, Nat.ltb_lt.
  inversion LT; [lia | split; assumption].
Qed.

Fixpoint accLtGen (n : nat) (m : nat) {struct n} : Acc Nat.lt m :=
  match n with
  | O => lt_wf m
  | S n' => Acc_intro m (fun p : nat => fun _ : (p < m)%nat => accLtGen n' p)
  end.

Fixpoint accNGen (n : nat) (m : N) {struct n} : Acc N.lt m :=
  match n with
  | O => N.lt_wf_0 m
  | S n' => Acc_intro m (fun p : N => fun _ : (p < m)%N => accNGen n' p)
  end.

Definition accLt (m : nat) : Acc Nat.lt m :=
  accLtGen (S m) m.

Definition accNlt (m : N) : Acc N.lt m :=
  accNGen (S (N.to_nat m)) m.

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

Definition Acc_to_sn {x0 : A}
  (H_Acc : Acc (fun x' => fun x => R x x') x0)
  : sn R x0.
Proof.
  induction H_Acc as [x _ IH].
  econs. exact IH.
Defined.

End Strong_Normalisation.

#[global] Strategy 100 [sn_guard].

Definition sn_of_wf {A : Type} {R : A -> A -> Prop}
  (H_wf : well_founded R)
  : forall x0 : A, @sn A (fun x : A => fun x' : A => R x' x) x0.
Proof.
  exact (fun x0 => Acc_to_sn (H_wf x0)).
Defined.

Section Strict_Progress_on_Prosets.

Context {A : Type} {PROSET : isProset A}.

Inductive betaProgressive (x : A) (x' : A) : Prop :=
  | betaProgressive_intro
    (LE : x =< x')
    (NE : ~ (x == x'))
    : x ~>β x'
  where "x ~>β x'" := (betaProgressive x x').

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
  - pose proof (UPPER x (leProp_refl x)) as IN'.
    apply L.in_split in IN'. destruct IN' as (prefix & suffix & CONE_EQ).
    subst cone'. econs. intros x' [LE NE].
    eapply IH with (cone := prefix ++ suffix).
    + rewrite !length_app in LENGTH |- *. simpl in LENGTH. lia.
    + intros y LE'.
      pose proof (UPPER y (leProp_trans x x' y LE LE')) as IN'.
      rewrite L.in_app_iff in IN'. simpl in IN'.
      rewrite L.in_app_iff. destruct IN' as [IN' | [EQ' | IN']]; eauto.
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

Theorem add'_spec n m
  : add' n m = n + m.
Proof.
  revert m; induction n as [ | n IH]; simpl; i.
  - reflexivity.
  - rewrite IH. lia.
Qed.

Corollary add'_zero_r n
  : add' n 0 = n.
Proof.
  rewrite add'_spec. now rewrite Nat.add_0_r.
Qed.

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

Lemma strong_search_go_correct_from n s n' s'
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

Theorem strong_search_correct n s
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
