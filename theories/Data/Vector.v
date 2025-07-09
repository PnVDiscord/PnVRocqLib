Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.

Module Fin.

Inductive t : nat -> Set :=
  | FZ (n : nat) : t (S n)
  | FS (n : nat) (i : t n) : t (S n).

#[global] Arguments FZ {n}%_nat.
#[global] Arguments FS {n}%_nat (i).

Lemma case0 {phi : Fin.t O -> Type}
  : forall i, phi i.
Proof.
  intros i.
  exact (
    match i as i in Fin.t n return (match n as m return Fin.t m -> Type with O => phi | S m' => fun _ => unit end) i with
    | @FZ n' => tt
    | @FS n' i' => tt
    end
  ).
Defined.

Lemma caseS {n' : nat} {phi : Fin.t (S n') -> Type}
  (phiFZ : phi (@FZ n'))
  (phiFS : forall i' : Fin.t n', phi (@FS n' i'))
  : forall i, phi i.
Proof.
  intros i; revert phi phiFZ phiFS.
  exact (
    match i as i in Fin.t n return (match n as m return Fin.t m -> Type with O => fun _ => unit | S m' => fun i => forall phi' : Fin.t (S m') -> Type, phi' (@FZ m') -> (forall i' : Fin.t m', phi' (@FS m' i')) -> phi' i end) i with
    | @FZ n' => fun phi : Fin.t (S n') -> Type => fun phiFZ : phi (@FZ n') => fun phiFS : forall i' : Fin.t n', phi (@FS n' i') => phiFZ
    | @FS n' i' => fun phi : Fin.t (S n') -> Type => fun phiFS : phi (@FZ n') => fun phiFS : forall i' : Fin.t n', phi (@FS n' i') => phiFS i'
    end
  ).
Defined.

Lemma rectS (phi : forall n, Fin.t (S n) -> Type)
  (phiFZ : forall n : nat, phi n (@FZ n))
  (phiFS : forall n : nat, forall i : Fin.t (S n), phi n i -> phi (S n) (@FS (S n) i))
  : forall n, forall i, phi n i.
Proof.
  exact (
    fix rectS_fix (n : nat) (i : Fin.t (S n)) {struct i} : phi n i :=
    match i as i in Fin.t n return (match n return Fin.t n -> Type with O => fun _ => unit | S n' => phi n' end) i with
    | @FZ m => phiFZ m
    | @FS m i' => (match m as m return forall i : Fin.t m, phi m (@FS m i) with O => Fin.case0 | S m' => fun i => phiFS m' i (rectS_fix m' i) end) i'
    end
  ).
Defined.

Ltac case0 :=
  let i := fresh "i" in
  intro i; pattern i; revert i;
  apply case0.

Ltac caseS i' :=
  let i := fresh "i" in
  intro i; pattern i; revert i;
  apply caseS; [ | intros i'].

#[global]
Instance Fin_hasEqDec {n : nat}
  : hasEqDec (Fin.t n).
Proof.
  red. induction n as [ | n IH]; [Fin.case0 | Fin.caseS i1'; Fin.caseS i2'].
  - left; reflexivity.
  - right; congruence.
  - right; congruence.
  - pose proof (IH i1' i2') as [H_eq | H_ne]; [left | right].
    + f_equal. exact (H_eq). 
    + intros H_eq. contradiction H_ne.
      set (f := fun i : Fin.t (S n) =>
        match i in Fin.t m return Fin.t (pred m) -> Fin.t (pred m) with
        | @FZ n' => fun d : Fin.t n' => d
        | @FS n' i' => fun d : Fin.t n' => i'
        end
      ).
      apply f_equal2 with (f := f) (x1 := FS i1') (y1 := FS i2') (x2 := i1') (y2 := i1') in H_eq.
      { exact H_eq. }
      { reflexivity. }
Defined.

Definition fin (n : nat) : Set :=
  @sig nat (gt n).

Fixpoint runFin {n : nat} (i : Fin.t n) {struct i} : fin n :=
  match i in Fin.t x return @sig nat (gt x) with
  | @FZ n' => @exist nat (gt (S n')) O (le_intro_S_n_le_S_m le_intro_0_le_n)
  | @FS n' i' => @exist nat (gt (S n')) (S (proj1_sig (runFin i'))) (le_intro_S_n_le_S_m (proj2_sig (runFin i')))
  end.

Fixpoint getFin {n : nat} (m : nat) {struct n} : m < n -> Fin.t n :=
  match n as x return S m <= x -> Fin.t x with
  | O => lt_elim_n_lt_0
  | S n' =>
    match m as y return S y <= S n' -> Fin.t (S n') with
    | O => fun hyp_lt : O < S n' => FZ
    | S m' => fun hyp_lt : S m' < S n' => FS (getFin m' (lt_elim_n_lt_S_m hyp_lt))
    end
  end.

Lemma runFin_getFin_id {m : nat} {n : nat} (hyp_lt : m < n)
  : runFin (getFin m hyp_lt) = @exist nat (gt n) m hyp_lt.
Proof.
  revert n hyp_lt. induction m as [ | m IH]; intros [ | n'] hyp_lt; cbn in *.
  - exact (lt_elim_n_lt_0 hyp_lt).
  - f_equal; eapply le_pirrel.
  - exact (lt_elim_n_lt_0 hyp_lt).
  - rewrite IH; cbn. eapply f_equal, le_pirrel.
Qed.

Lemma getFin_runFin_id {n : nat} (i : Fin.t n)
  : getFin (proj1_sig (runFin i)) (proj2_sig (runFin i)) = i.
Proof.
  induction i as [n' | n' i' IH].
  - reflexivity.
  - cbn. f_equal. etransitivity; cycle 1; [exact IH | f_equal; eapply le_pirrel].
Qed.

Definition evalFin {n : nat} (i : Fin.t n) : nat :=
  proj1_sig (runFin i).

Lemma evalFin_unfold {n : nat} (i : Fin.t n) :
  evalFin i =
  match i with
  | FZ => O
  | FS i' => S (evalFin i')
  end.
Proof.
  destruct i; reflexivity.
Defined.

Lemma evalFin_inj {n : nat} (i1 : Fin.t n) (i2 : Fin.t n)
  (hyp_eq : evalFin i1 = evalFin i2)
  : i1 = i2.
Proof.
  unfold evalFin in hyp_eq.
  rewrite <- getFin_runFin_id with (i := i1).
  rewrite <- getFin_runFin_id with (i := i2).
  destruct (runFin i1) as [m1 hyp_lt1].
  destruct (runFin i2) as [m2 hyp_lt2].
  cbn in *. subst m1. f_equal. eapply le_pirrel.
Qed.

Fixpoint incrFin {m : nat} (n : nat) (i : Fin.t m) {struct n} : Fin.t (n + m) :=
  match n as x return Fin.t (x + m) with
  | O => i
  | S n' => FS (incrFin n' i)
  end.

Lemma incrFin_spec {m : nat} (n : nat) (i : Fin.t m)
  : evalFin (incrFin n i) = n + evalFin i.
Proof with eauto.
  induction n as [ | n IH]; simpl...
  rewrite evalFin_unfold. f_equal...
Qed.

#[global, program]
Instance Fin_isCountable {n : nat} : isCountable (Fin.t n) :=
  { encode := evalFin
  ; decode i :=
    match le_lt_dec n i with
    | left _ => None
    | right H_lt => Some (getFin i H_lt)
    end
  }.
Next Obligation.
  destruct (le_lt_dec n (evalFin x)) as [H_ge | H_lt].
  - unfold evalFin in H_ge. destruct (runFin x) as [i H_i]; simpl in *. lia.
  - f_equal. erewrite le_pirrel with (LE1 := H_lt). eapply getFin_runFin_id.
Qed.

End Fin.

Notation FZ := Fin.FZ.
Notation FS := Fin.FS.

#[global] Declare Scope vec_scope.

Module Vector.

#[universes(template)]
Inductive t (A : Type) : nat -> Type :=
  | VNil : t A O
  | VCons (n : nat) (x : A) (xs : t A n) : t A (S n).

#[global] Arguments VNil {A}.
#[global] Arguments VCons {A} (n) (x) (xs).

#[global] Delimit Scope vec_scope with t.

End Vector.

#[global] Bind Scope vec_scope with Vector.t.

Notation " [ ] " := (@Vector.VNil _) : vec_scope.
Notation " x :: xs " := (@Vector.VCons _ _ x xs) : vec_scope.
Notation " [ x ] " := (@Vector.VCons _ _ x (@Vector.VNil _)) : vec_scope.

Notation VNil := Vector.VNil.
Notation VCons := Vector.VCons.

Module V.

#[local] Open Scope vec_scope.

Section Accessories.

Context {A : Type}.

#[local] Notation vec := (Vector.t A).

Lemma case0 (phi : Vector.t A O -> Type)
  (phi_nil : phi (@VNil A))
  : forall ts, phi ts.
Proof.
  intros ts. revert phi phi_nil.
  exact (
    match ts as ts in Vector.t _ n return (match n as n return Vector.t A n -> Type with O => fun ts => forall phi : Vector.t A O -> Type, phi VNil -> phi ts | S n' => fun ts => unit end) ts with
    | @VNil _ => fun phi => fun phi_O => phi_O
    | @VCons _ n' t' ts' => tt
    end
  ).
Defined.

Lemma caseS {n' : nat} (phi : Vector.t A (S n') -> Type)
  (phi_cons : forall t', forall ts', phi (@VCons A n' t' ts'))
  : forall ts, phi ts.
Proof.
  intros ts. revert phi phi_cons.
  exact (
    match ts as ts in Vector.t _ n return (match n as n return Vector.t A n -> Type with O => fun _ => unit | S n' => fun ts => forall phi : Vector.t A (S n') -> Type, (forall t' : A, forall ts' : Vector.t A n', phi (VCons n' t' ts')) -> phi ts end) ts with
    | @VNil _ => tt
    | @VCons _ n' t' ts' => fun phi => fun phi_S => phi_S t' ts'
    end
  ).
Defined.

Lemma rectS (phi : forall n, vec (S n) -> Type)
  (phiOnce : forall x, phi 0 [x])
  (phiCons : forall n, forall x, forall xs, phi n xs -> phi (S n) (x :: xs))
  : forall n, forall xs, phi n xs.
Proof.
  exact (
    fix rectS_fix (n : nat) (xs : vec (S n)) {struct xs} : phi n xs :=
    match xs as xs in Vector.t _ n return (match n as n return vec n -> Type with O => fun _ => unit | S n' => phi n' end) xs with
    | VNil => tt
    | VCons n' x' xs' => (match n' as m return forall x : A, forall xs : vec m, phi m (VCons m x xs) with O => fun x => case0 (fun xs => phi 0 (VCons 0 x xs)) (phiOnce x) | S m' => fun x => fun xs => phiCons m' x xs (rectS_fix m' xs) end) x' xs'
    end
  ).
Defined.

Definition head {n : nat} (xs : vec (S n)) : A :=
  match xs in Vector.t _ n' return (match n' as n' return Type with O => unit | S n => A end) with
  | VNil => tt
  | VCons _ x _ => x
  end.

Definition tail {n : nat} (xs : vec (S n)) : vec n :=
  match xs in Vector.t _ n' return (match n' as n' return Type with O => unit | S n => vec n end) with
  | VNil => tt
  | VCons _ _ xs => xs
  end.

Fixpoint nth {n : nat} (xs : vec n) {struct xs} : Fin.t n -> A :=
  match xs with
  | [] => Fin.case0
  | x :: xs => Fin.caseS x (nth xs)
  end.

End Accessories.

#[local] Infix "!!" := nth.

#[local]
Tactic Notation "introVNil" :=
  let xs := fresh "xs" in
  intro xs; pattern xs; revert xs;
  apply V.case0.

#[local]
Tactic Notation "introVCons" ident( x' ) ident( xs' ) :=
  let xs := fresh "xs" in
  intro xs; pattern xs; revert xs;
  apply V.caseS; intros x' xs'.

Lemma nth_unfold {A : Type} {n : nat} (xs : Vector.t A n) (i : Fin.t n)
  : xs !! i = (match i in Fin.t m return Vector.t A m -> A with FZ => fun v => head v | FS i' => fun v => tail v !! i' end) xs.
Proof.
  revert i; destruct xs as [ | n' x' xs']; [Fin.case0 | Fin.caseS i']; reflexivity.
Qed.

Theorem vec_ext_eq {A : Type} {n : nat} (lhs : Vector.t A n) (rhs : Vector.t A n)
  : lhs = rhs <-> (forall i, lhs !! i = rhs !! i).
Proof.
  split.
  - now intros ?; subst.
  - revert lhs rhs. induction n as [ | n IH].
    + introVNil; introVNil. intros H_eq.
      reflexivity.
    + introVCons x xs; introVCons y ys. intros H_eq.
      assert (x = y) as x_eq_y by exact (H_eq FZ).
      enough (xs = ys) as xs_eq_ys by congruence.
      eapply IH. intros i. eapply H_eq with (i := FS i).
Qed.

Fixpoint map {A : Type} {B : Type} {n : nat} (f : A -> B) (xs : Vector.t A n) {struct xs} : Vector.t B n :=
  match xs with
  | [] => []
  | x :: xs' => f x :: map f xs'
  end.

Lemma map_spec {A : Type} {B : Type} {n : nat} (f : A -> B) (xs : Vector.t A n)
  : forall i : Fin.t n, f (xs !! i) = map f xs !! i.
Proof.
  induction xs as [ | n x xs IH].
  - Fin.case0.
  - Fin.caseS i.
    + reflexivity.
    + exact (IH i).
Qed.

Fixpoint replicate {A : Type} {n : nat} {struct n} : A -> Vector.t A n :=
  match n with
  | O => fun x => []
  | S n' => fun x => x :: replicate (n := n') x
  end.

Lemma replicate_spec {A : Type} {n : nat} (x : A)
  : forall i : Fin.t n, x = replicate x !! i.
Proof.
  induction n; [Fin.case0 | Fin.caseS i]; simpl; eauto.
Qed.

Fixpoint diagonal {A : Type} {n : nat} {struct n} : Vector.t (Vector.t A n) n -> Vector.t A n :=
  match n with
  | O => fun xss => []
  | S n' => fun xss => head (head xss) :: diagonal (n := n') (map tail (tail xss))
  end.

Lemma diagonal_spec {A : Type} {n : nat} (xss : Vector.t (Vector.t A n) n)
  : forall i : Fin.t n, xss !! i !! i = diagonal xss !! i.
Proof.
  revert xss; induction n as [ | n IH].
  - introVNil; Fin.case0.
  - introVCons xs xss; Fin.caseS i; simpl.
    + now rewrite nth_unfold.
    + now rewrite nth_unfold; rewrite <- IH with (i := i); rewrite map_spec with (f := tail) (xs := xss) (i := i).
Qed.

Ltac red_vec :=
  first [rewrite <- diagonal_spec | rewrite <- map_spec | rewrite <- replicate_spec].

Section INSTANCES.

#[global]
Instance vector_hasEqDec {A : Type} {n : nat}
  (A_hasEqDec : hasEqDec A)
  : hasEqDec (Vector.t A n).
Proof.
  red. induction n as [ | n IH]; intros lhs rhs.
  - left. revert lhs rhs. introVNil; introVNil; reflexivity.
  - pose proof (IH (tail lhs) (tail rhs)) as [H_EQ2 | H_NE2]; [pose proof (A_hasEqDec (head lhs) (head rhs)) as [H_EQ1 | H_NE1] | ].
    + left. revert lhs rhs H_EQ1 H_EQ2.
      introVCons x xs; introVCons y ys; intros H_head H_tail.
      cbv in *. congruence.
    + right. revert lhs rhs H_NE1 H_EQ2.
      introVCons x xs; introVCons y ys; intros H_head _ H_contradiction.
      now apply f_equal with (f := head) in H_contradiction.
    + right. revert lhs rhs H_NE2.
      introVCons x xs; introVCons y ys. intros H_tail H_contradiction.
      now apply f_equal with (f := tail) in H_contradiction.
Defined.

Definition vec (n : nat) (A : Type) : Type :=
  Vector.t A n.

#[local]
Instance vec_isMonad {n : nat} : isMonad (vec n) :=
  { bind {A : Type} {B : Type} (m : vec n A) (k : A -> vec n B) := diagonal (map k m)
  ; pure {A : Type} (x : A) := replicate x
  }.

Definition zipWith {n : nat} {A : Type} {B : Type} {C : Type} (f : A -> B -> C) (xs : Vector.t A n) (ys : Vector.t B n) : Vector.t C n :=
  liftM2 (MONAD := vec_isMonad) (A := A) (B := B) (C := C) f xs ys.

Lemma zipWith_spec {n : nat} {A : Type} {B : Type} {C : Type} (f : A -> B -> C) (xs : Vector.t A n) (ys : Vector.t B n)
  : forall i, f (xs !! i) (ys !! i) = zipWith f xs ys !! i.
Proof.
  cbn; ii. repeat red_vec. reflexivity.
Qed.

#[local]
Instance vec_isSetoid (n : nat) (A : Type) `(SETOID : isSetoid A) : isSetoid (vec n A) :=
  { eqProp (lhs : vec n A) (rhs : vec n A) := forall i : Fin.t n, lhs !! i == rhs !! i
  ; eqProp_Equivalence := relation_on_image_liftsEquivalence (pi_isSetoid (fun _ => SETOID)).(eqProp_Equivalence) nth
  }.

#[local]
Instance vec_isSetoid1 {n : nat} : isSetoid1 (vec n) :=
  vec_isSetoid n.

#[global]
Instance vec_satisfiesMonadLaws {n : nat}
  : @MonadLaws (vec n) vec_isSetoid1 vec_isMonad.
Proof.
  split; cbn; ii; (repeat red_vec); congruence.
Qed.

End INSTANCES.

Fixpoint foldr {A : Type} {B : Type} {n : nat} (f : A -> B -> B) (z : B) (xs : Vector.t A n) : B :=
  match xs with
  | [] => z
  | x :: xs => f x (foldr f z xs)
  end.

Lemma head_unfold {A : Type} (n : nat) (x : A) (xs : Vector.t A n)
  : head (x :: xs) = x.
Proof.
  reflexivity.
  Defined.

Lemma tail_unfold {A : Type} (n : nat) (x : A) (xs : Vector.t A n)
  : tail (x :: xs) = xs.
Proof.
  reflexivity.
Defined.

Section HEQ.

Context {A : Type}.

Fixpoint to_list {n : nat} (xs : Vector.t A n) {struct xs} : list A :=
  match xs with
  | [] => L.nil
  | x :: xs => L.cons x (to_list xs)
  end.

Lemma to_list_inj {n : nat} (xs1 : Vector.t A n) (xs2 : Vector.t A n)
  (EXT_EQ : to_list xs1 = to_list xs2)
  : xs1 = xs2.
Proof.
  revert xs1 xs2 EXT_EQ. induction xs1 as [ | n x1 xs1 IH].
  - introVNil; simpl. i. reflexivity.
  - introVCons x2 xs2; simpl. i. f_equal.
    + apply f_equal with (f := L.hd x1) in EXT_EQ. exact EXT_EQ.
    + apply f_equal with (f := @L.tl A) in EXT_EQ. eapply IH. exact EXT_EQ. 
Qed.

Fixpoint from_list (xs : list A) {struct xs} : Vector.t A (L.length xs) :=
  match xs with
  | L.nil => []
  | L.cons x xs => x :: from_list xs
  end.

Lemma to_list_from_list (xs : list A)
  : to_list (from_list xs) = xs.
Proof.
  induction xs as [ | x xs IH]; simpl.
  - reflexivity.
  - f_equal. exact IH.
Qed.

Lemma to_list_In (n : nat) (xs : Vector.t A n) (i : Fin.t n)
  : L.In (xs !! i) (to_list xs).
Proof.
  revert i. induction xs as [ | n x xs IH].
  - Fin.case0.
  - Fin.caseS i; [left | right]; eauto.
Qed.

Lemma in_to_list_iff (n : nat) (xs : Vector.t A n)
  : forall x, In x (to_list xs) <-> (exists i, xs !! i = x).
Proof.
  intros x. split.
  - revert x. induction xs as [ | n x' xs' IH]; simpl; intros x IN.
    + tauto.
    + destruct IN as [<- | IN].
      * exists (@FZ n). simpl. reflexivity.
      * pose proof (IH x IN) as [i EQ]. exists (@FS n i). simpl. exact EQ.
  - intros [i <-]. eapply to_list_In.
Qed.

Inductive vec_heq (n : nat) (xs : Vector.t A n) : forall m : nat, Vector.t A m -> Prop :=
  | vec_ext_heq_refl
    : vec_heq n xs n xs.

#[local] Notation " xs =~= xs' " := (vec_heq _ xs _ xs') : type_scope.

Lemma len_eq_from_vec_heq (n : nat) (m : nat) (xs : Vector.t A n) (xs' : Vector.t A m)
  (HEQ : xs =~= xs')
  : n = m.
Proof.
  exact (
    match HEQ in vec_heq _ _ m xs' return n = m with
    | vec_ext_heq_refl _ _ => @eq_refl nat n
    end
  ).
Defined.

Lemma eq_from_vec_heq (n : nat) (xs : Vector.t A n) (xs' : Vector.t A n)
  (HEQ : xs =~= xs')
  : xs = xs'.
Proof.
  pose proof (
    match HEQ in vec_heq _ _ m xs' return @existT nat (Vector.t A) n xs = @existT nat (Vector.t A) m xs' with
    | vec_ext_heq_refl _ _ => @eq_refl (@sigT nat (Vector.t A)) (@existT nat (Vector.t A) n xs)
    end
  ) as EQ.
  apply projT2_eq_fromEqDec in EQ. exact EQ.
Defined.

Lemma from_list_to_list (n : nat) (xs : Vector.t A n)
  : from_list (to_list xs) =~= xs.
Proof.
  induction xs as [ | n x xs IH]; simpl.
  - econs.
  - destruct IH. rewrite to_list_from_list. econs.
Qed.

#[local] Hint Constructors vec_heq : core.

Lemma nth_error_to_list (n : nat) (xs : Vector.t A n) (i : nat)
  (LT : i < n)
  : nth_error (to_list xs) i = Some (xs !! Fin.getFin i LT).
Proof.
  assert (claim : exists zs : list A, from_list zs =~= xs).
  { exists (to_list xs). eapply from_list_to_list. }
  destruct claim as [zs EQ]. destruct EQ. rename i into k.
  remember (Fin.getFin k LT) as i eqn: H_i. apply f_equal with (f := Fin.runFin) in H_i.
  rewrite Fin.runFin_getFin_id in H_i. revert k i LT H_i. induction zs as [ | z zs IH]; i.
  - simpl in *. inv LT.
  - simpl from_list. simpl to_list. simpl length in *. revert i H_i. Fin.caseS i'; i.
    + assert (EQ : k = O).
      { pose proof (@Fin.getFin_runFin_id (S (length zs)) FZ) as claim. rewrite H_i in claim. simpl proj1_sig in claim.
        apply f_equal with (f := Fin.runFin) in claim. rewrite Fin.runFin_getFin_id in claim. simpl in claim.
        apply f_equal with (f := @proj1_sig _ _) in claim. simpl in claim. trivial. 
      }
      subst k. simpl. reflexivity.
    + assert (EQ : k = S (proj1_sig (Fin.runFin i'))).
      { pose proof (@Fin.getFin_runFin_id (S (length zs)) (FS i')) as claim. rewrite H_i in claim. simpl proj1_sig in claim.
        apply f_equal with (f := Fin.runFin) in claim. rewrite Fin.runFin_getFin_id in claim. simpl in claim.
        apply f_equal with (f := @proj1_sig _ _) in claim. simpl in claim. trivial.
      }
      subst k. simpl. eapply IH. simpl in H_i. rewrite <- Fin.runFin_getFin_id. rewrite Fin.getFin_runFin_id. reflexivity.
Qed.

Lemma nth_error_to_list_eq (n : nat) (xs : Vector.t A n) (i : nat)
  : nth_error (to_list xs) i = (match le_lt_dec n i with right LT => Some (xs !! Fin.getFin i LT) | left GE => None end).
Proof.
  destruct (le_lt_dec n i) as [GE | LT].
  - revert i GE. induction xs as [ | n x xs IH]; simpl; i.
    + destruct i as [ | i']; trivial.
    + destruct i as [ | i']; [lia | simpl; eapply IH; lia].
  - eapply nth_error_to_list.
Qed.

Lemma heq_refl (n1 : nat) (xs1 : Vector.t A n1)
  : xs1 =~= xs1.
Proof.
  econs.
Qed.

Lemma heq_sym (n1 : nat) (n2 : nat) (xs1 : Vector.t A n1) (xs2 : Vector.t A n2)
  (EQ : xs1 =~= xs2)
  : xs2 =~= xs1.
Proof.
  destruct EQ. econs.
Qed.

Lemma heq_trans (n1 : nat) (n2 : nat) (n3 : nat) (xs1 : Vector.t A n1) (xs2 : Vector.t A n2) (xs3 : Vector.t A n3)
  (EQ : xs1 =~= xs2)
  (EQ' : xs2 =~= xs3)
  : xs1 =~= xs3.
Proof.
  destruct EQ. exact EQ'.
Qed.

Lemma heq_iff (n : nat) (m : nat) (xs : Vector.t A n) (xs' : Vector.t A m)
  : xs =~= xs' <-> to_list xs = to_list xs'.
Proof.
  split.
  - intros HEQ. destruct HEQ. reflexivity.
  - intros EQ. eapply heq_trans. 2: eapply from_list_to_list.
    rewrite <- EQ. eapply heq_sym. eapply from_list_to_list.
Qed.

Theorem heq_congruence (P : forall n : nat, Vector.t A n -> Prop) (n : nat) (n' : nat) (xs : Vector.t A n) (xs' : Vector.t A n')
  (HEQ : xs =~= xs')
  : P n xs <-> P n' xs'.
Proof.
  destruct HEQ. reflexivity.
Qed.

End HEQ.

Fixpoint snoc {A : Type} {n : nat} (xs : Vector.t A n) (x : A) {struct xs} : Vector.t A (S n) :=
  match xs with
  | [] => [x]
  | x' :: xs' => x' :: snoc xs' x
  end.

Lemma to_list_snoc {A : Type} {n : nat} (xs : Vector.t A n) (x : A)
  : to_list (snoc xs x) = L.app (to_list xs) (L.cons x L.nil).
Proof.
  revert x. induction xs as [ | n x' xs' IH]; simpl; i.
  - reflexivity.
  - f_equal. eapply IH.
Qed.

Fixpoint rev {A : Type} {n : nat} (xs : Vector.t A n) {struct xs} : Vector.t A n :=
  match xs with
  | [] => []
  | x :: xs => snoc (rev xs) x
  end.

Lemma to_list_rev {A : Type} {n : nat} (xs : Vector.t A n)
  : to_list (rev xs) = L.rev (to_list xs).
Proof.
  induction xs as [ | n x xs IH]; simpl.
  - reflexivity.
  - rewrite to_list_snoc. f_equal. exact IH.
Qed.

Fixpoint forallb {A : Type} {n : nat} (p : A -> bool) (xs : Vector.t A n) : bool :=
  match xs with
  | [] => true
  | x :: xs => p x && forallb p xs
  end.

Lemma forallb_forall {A : Type} {n : nat} (p : A -> bool) (xs : Vector.t A n)
  : forallb p xs = true <-> (forall i, p (xs !! i) = true).
Proof.
  induction xs as [ | n x xs IH]; simpl.
  - split; trivial. intros _. Fin.case0.
  - rewrite andb_true_iff. rewrite IH. split.
    + intros [p_x p_xs]. Fin.caseS i; eauto.
    + intros H_p. split.
      * eapply H_p with (i := FZ).
      * intros i. eapply H_p with (i := FS i).
Qed.

Inductive Similarity_vec_list (A : Type) : forall n : nat, Similarity (Vector.t A n) (list A) :=
  | Similarity_vec_list_nil
    : is_similar_to (VNil) (@L.nil A)
  | Similarity_vec_list_cons n x x' xs xs'
    (x_corres : x = x')
    (xs_corres : is_similar_to xs xs')
    : is_similar_to (VCons n x xs) (@L.cons A x' xs').

Lemma Similarity_vec_list_iff {A : Type} {n : nat} (xs : Vector.t A n) (xs' : list A)
  : is_similar_to (Similarity := Similarity_vec_list A n) xs xs' <-> V.to_list xs = xs'.
Proof.
  split.
  - intros H_sim. induction H_sim; simpl; f_equal; eauto.
  - intros <-. induction xs as [ | n x xs IH]; simpl; econs; eauto.
Qed.

End V.

Ltac introVNil :=
  let xs := fresh "xs" in
  intro xs; pattern xs; revert xs;
  apply V.case0.

Ltac introVCons x' xs' :=
  let xs := fresh "xs" in
  intro xs; pattern xs; revert xs;
  apply V.caseS; intros x' xs'.

Infix "!!" := V.nth.

Inductive Similarity_vec {A : Type} {A' : Type} {SIM : Similarity A A'} : forall n : nat, Similarity (Vector.t A n) (Vector.t A' n) :=
  | VNil_corres
    : is_similar_to VNil VNil
  | VCons_corres (n : nat) x x' xs xs'
    (x_corres : is_similar_to x x')
    (xs_corres : is_similar_to xs xs')
    : is_similar_to (VCons n x xs) (VCons n x' xs').

#[global] Existing Instance Similarity_vec.

Fixpoint nth_list {A : Type} (xs : list A) {struct xs} : Fin.t (length xs) -> A :=
  match xs with
  | [] => Fin.case0
  | x :: xs => Fin.caseS x (nth_list xs)
  end.
