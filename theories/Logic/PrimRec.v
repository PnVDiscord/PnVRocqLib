Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Data.Vector.

Section PRIMITIVE_RECURSION. (* Reference: "https://github.com/princeton-vl/CoqGym/blob/master/coq_projects/goedel/primRec.v" *)

#[local] Open Scope program_scope.

Let arity : Set := nat.

Fixpoint naryFun (n : arity) :=
  match n with
  | O => nat
  | S n' => nat -> naryFun n'
  end.

Fixpoint naryRel (n : arity) :=
  match n with
  | O => Prop
  | S n' => nat -> naryRel n'
  end.

Fixpoint eval_vec {n : arity} (xs : Vector.t nat n) : naryFun n -> nat :=
  match xs with
  | VNil => id
  | VCons n' x xs' => fun f => eval_vec xs' (f x)
  end.

Fixpoint eval_const {n : arity} (m : nat) : naryFun n :=
  match n with
  | O => m
  | S n' => const (eval_const m)
  end.

Fixpoint eval_proj {n : arity} (i : Fin.t n) : naryFun n :=
  match i with
  | FZ => eval_const
  | FS i' => const (eval_proj i')
  end.

Lemma eval_proj_spec (n : arity) (i : Fin.t n) (xs : Vector.t nat n)
  : eval_vec xs (eval_proj i) = xs !! i.
Proof.
  revert i. induction xs as [ | n x xs IH]; simpl.
  - Fin.case0.
  - Fin.caseS i.
    + simpl. clear IH. revert x xs. induction n as [ | n IH]; simpl.
      * intros x. introVNil. reflexivity.
      * intros x. introVCons x' xs'. simpl. unfold const. eapply IH.
    + eapply IH.
Qed.

Fixpoint eval_vec_1 {n : arity} {m : arity} (x : nat) (xs : Vector.t (naryFun (S n)) m) : Vector.t (naryFun n) m :=
  match xs with
  | VNil => VNil
  | VCons m' f xs' => VCons m' (f x) (eval_vec_1 x xs')
  end.

Fixpoint eval_compose {n : arity} {m : arity} : Vector.t (naryFun n) m -> naryFun m -> naryFun n :=
  match n with
  | O => fun xs => eval_vec xs
  | S n' => fun xs => fun f => fun x => eval_compose (eval_vec_1 x xs) f
  end.

Lemma eval_compose_spec (n : arity) (m : arity) (gs : Vector.t (naryFun n) m) (h : naryFun m) (xs : Vector.t nat n) (ys : Vector.t nat m) (z : nat)
  (gs_spec : V.map (eval_vec xs) gs = ys)
  (h_spec : eval_vec ys h = z)
  : eval_vec xs (eval_compose gs h) = z.
Proof.
  revert m gs h xs ys z gs_spec h_spec. induction n as [ | n IH]; simpl.
  - intros m gs h. introVNil. simpl. i.
    assert (claim1 : ys = gs).
    { rewrite <- gs_spec. clear ys z h gs_spec h_spec. induction gs as [ | n g gs IH]; simpl; trivial; f_equal; eauto. }
    subst gs. clear gs_spec. exact h_spec.
  - intros m gs h. introVCons x xs. simpl. i.
    assert (claim2 : V.map (eval_vec xs) (eval_vec_1 x gs) = ys).
    { rewrite <- gs_spec. clear ys gs_spec h_spec. clear z h IH. revert x xs. induction gs as [ | m g gs IH]; simpl.
      - reflexivity.
      - intros x xs. f_equal. eapply IH.
    }
    pose proof (claim3 := IH m (eval_vec_1 x gs) h xs ys z claim2 h_spec). congruence.
Qed.

Fixpoint eval_compose_2 {n : arity} : naryFun n -> naryFun (S n) -> naryFun n :=
  match n with
  | O => fun x => fun f => f x
  | S n' => fun f => fun g => fun a => eval_compose_2 (f a) (fun x => g x a)
  end.

Lemma eval_compose_2_spec (n : arity) (g : naryFun n) (h : naryFun (S n)) (xs : Vector.t nat n) (a : nat) (z : nat)
  (g_spec : eval_vec xs g = a)
  (h_spec : eval_vec (a :: xs) h = z)
  : eval_vec xs (eval_compose_2 g h) = z.
Proof.
  revert g h xs a z g_spec h_spec. induction n as [ | n IH]; simpl.
  - intros g h. introVNil. simpl. i. cbv in *. congruence.
  - intros g h. introVCons x xs. simpl. i.
    exact (IH (g x) (fun a => h a x) xs a z g_spec h_spec).
Qed.

Fixpoint eval_primRec {n : arity} (g : naryFun n) (h : naryFun (S (S n))) (a : nat) : naryFun n :=
  match a with
  | O => g
  | S a' => eval_compose_2 (eval_primRec g h a') (h a')
  end.

Inductive PrimRec : arity -> Set :=
  | PR_succ : PrimRec 1
  | PR_zero : PrimRec 0
  | PR_proj (n : arity) (i : Fin.t n) : PrimRec n
  | PR_compose (n : arity) (m : arity) (g : PrimRecs n m) (h : PrimRec m) : PrimRec n
  | PR_primRec (n : arity) (g : PrimRec n) (h : PrimRec (S (S n))) : PrimRec (S n)
with PrimRecs : arity -> arity -> Set :=
  | PRs_nil (n : arity) : PrimRecs n 0
  | PRs_cons (n : arity) (m : arity) (f : PrimRec n) (fs : PrimRecs n m) : PrimRecs n (S m).

Section PrimRecs_case.

Let cast (x : nat) (n : nat) (m : nat) (EQ : n = m) : PrimRecs x n -> PrimRecs x m :=
  match EQ with
  | eq_refl => fun xs => xs
  end.

Lemma PrimRecs_case0 (phi : forall x, PrimRecs x O -> Type)
  (phi_nil : forall n, phi n (PRs_nil n))
  : forall x, forall fs, phi x fs.
Proof.
  refine (fun x : nat =>
    let claim1 (fs : PrimRecs x O) : forall H_eq : O = O, phi x (cast x O O H_eq fs) :=
      match fs in PrimRecs x m return forall H_eq : m = O, phi x (cast x m O H_eq fs) with
      | PRs_nil x => fun H_eq : O = O => _
      | PRs_cons x n f' fs' => fun H_eq : S n = O => _
      end
    in _
  ).
  { intros fs. exact (claim1 fs eq_refl). }
Unshelve.
  - rewrite eq_pirrel_fromEqDec with (EQ1 := H_eq) (EQ2 := eq_refl).
    exact (phi_nil x).
  - inversion H_eq.
Qed.

Lemma PrimRecs_caseS {n' : nat} (phi : forall x, PrimRecs x (S n') -> Type)
  (phi_cons: forall n, forall f', forall fs', phi n (PRs_cons n n' f' fs'))
  : forall x, forall fs, phi x fs.
Proof.
  refine (fun x : nat =>
    let claim1 (fs : PrimRecs x (S n')) : forall H_eq : S n' = S n', phi x (cast x (S n') (S n') H_eq fs) :=
      match fs in PrimRecs x m return forall H_eq : m = S n', phi x (cast x m (S n') H_eq fs) with
      | PRs_nil x => fun H_eq: O = S n' => _
      | PRs_cons x n x' xs' => fun H_eq: S n = S n' => _
      end
    in _
  ).
  { intros fs. exact (claim1 fs eq_refl). }
Unshelve.
  - inversion H_eq.
  - pose proof (f_equal Nat.pred H_eq) as n_eq_n'. simpl in n_eq_n'. subst n'.
    rewrite eq_pirrel_fromEqDec with (EQ1 := H_eq) (EQ2 := eq_refl).
    exact (phi_cons x x' xs').
Qed.

End PrimRecs_case.

Fixpoint runPrimRec {n : arity} (f : PrimRec n) {struct f} : naryFun n :=
  match f with
  | PR_succ => S
  | PR_zero => O
  | PR_proj n i => eval_proj (n := n) i
  | PR_compose n m g h => eval_compose (n := n) (m := m) (runPrimRecs g) (runPrimRec h)
  | PR_primRec n g h => eval_primRec (n := n) (runPrimRec g) (runPrimRec h)
  end
with runPrimRecs {n : arity} {m : arity} (fs : PrimRecs n m) {struct fs} : Vector.t (naryFun n) m :=
  match fs with
  | PRs_nil n' => VNil
  | PRs_cons n' m' f fs' => VCons m' (runPrimRec f) (runPrimRecs fs')
  end.

Lemma runPrimRec_unfold (n : arity) (f : PrimRec n) :
  runPrimRec f =
  match f with
  | PR_succ => S
  | PR_zero => O
  | PR_proj n i => eval_proj i
  | PR_compose n m g h => eval_compose (runPrimRecs g) (runPrimRec h)
  | PR_primRec n g h => eval_primRec (runPrimRec g) (runPrimRec h)
  end.
Proof.
  destruct f; reflexivity.
Defined.

Lemma runPrimRecs_unfold (n : arity) (m : arity) (fs : PrimRecs n m) :
  runPrimRecs fs =
  match fs with
  | PRs_nil n' => VNil
  | PRs_cons n' m' f fs' => VCons m' (runPrimRec f) (runPrimRecs fs')
  end.
Proof.
  destruct fs; reflexivity.
Defined.

#[local] Close Scope list_scope.
#[local] Open Scope vector_scope.

#[local] Notation " [ ] " := (VNil).
#[local] Notation " x :: xs " := (VCons _ x xs).
#[local] Notation " [ x ] " := (VCons _ x VNil).

Inductive PrimRecSpec : forall n : arity, PrimRec n -> Vector.t nat n -> nat -> Prop :=
  | PR_succ_spec x
    : PrimRecSpec 1 (PR_succ) [x] (S x)
  | PR_zero_spec
    : PrimRecSpec 0 (PR_zero) [] (O)
  | PR_proj_spec n xs i
    : PrimRecSpec n (PR_proj n i) xs (xs !! i)
  | PR_compose_spec n m g h xs ys z
    (g_spec : PrimRecsSpec n m g xs ys)
    (h_spec : PrimRecSpec m h ys z)
    : PrimRecSpec n (PR_compose n m g h) xs z
  | PR_primRec_spec_O n g h xs z
    (g_spec : PrimRecSpec n g xs z)
    : PrimRecSpec (S n) (PR_primRec n g h) (O :: xs) z
  | PR_primRec_spec_S n g h xs z a acc
    (ACC : PrimRecSpec (S n) (PR_primRec n g h) (a :: xs) acc)
    (h_spec : PrimRecSpec (S (S n)) h (a :: acc :: xs) z)
    : PrimRecSpec (S n) (PR_primRec n g h) (S a :: xs) z
with PrimRecsSpec : forall n : arity, forall m : arity, PrimRecs n m -> Vector.t nat n -> Vector.t nat m -> Prop :=
  | PRs_nil_spec n xs
    : PrimRecsSpec n (O) (PRs_nil n) xs []
  | PRs_cons_spec n m xs y ys f fs
    (f_spec : PrimRecSpec n f xs y)
    (fs_spec : PrimRecsSpec n m fs xs ys)
    : PrimRecsSpec n (S m) (PRs_cons n m f fs) xs (y :: ys).

Fixpoint PrimRecGraph {n : arity} (f : PrimRec n) : Vector.t nat n -> nat -> Prop :=
  match f with
  | PR_succ => fun xs => fun z => S (V.head xs) = z
  | PR_zero => fun xs => fun z => O = z
  | PR_proj n i => fun xs => fun z => xs !! i = z
  | PR_compose n m g h => fun xs => fun z => exists ys, PrimRecsGraph g xs ys /\ PrimRecGraph h ys z
  | PR_primRec n g h => fun xs => nat_rect _ (fun z => PrimRecGraph g (V.tail xs) z) (fun a => fun ACC => fun z => exists y, ACC y /\ PrimRecGraph h (a :: y :: V.tail xs) z) (V.head xs)
  end
with PrimRecsGraph {n : arity} {m : arity} (fs : PrimRecs n m) : Vector.t nat n -> Vector.t nat m -> Prop :=
  match fs with
  | PRs_nil n => fun xs => fun z => [] = z
  | PRs_cons n m f fs => fun xs => fun z => exists y, exists ys, PrimRecGraph f xs y /\ PrimRecsGraph fs xs ys /\ y :: ys = z
  end.

Fixpoint PrimRecGraph_sound (n : arity) (f : PrimRec n) {struct f}
  : forall xs, forall z, PrimRecGraph f xs z -> PrimRecSpec n f xs z
with PrimRecsGraph_sound (n : arity) (m : arity) (fs : PrimRecs n m) {struct fs}
  : forall xs, forall z, PrimRecsGraph fs xs z -> PrimRecsSpec n m fs xs z.
Proof.
  - destruct f; intros xs z CALL.
    + r in CALL. subst z. revert xs. introVCons x xs. revert xs. introVNil. cbv. econs 1.
    + r in CALL. subst z. revert xs. introVNil. econs 2.
    + r in CALL. subst z. econs 3.
    + simpl in CALL. destruct CALL as (ys&CALLs&CALL). econs 4.
      * eapply PrimRecsGraph_sound. exact CALLs.
      * eapply PrimRecGraph_sound. exact CALL.
    + simpl in CALL. revert xs CALL. introVCons a xs. revert z xs. induction a as [ | a ACC]; i.
      * simpl in CALL. unfold V.tail in CALL. simpl in CALL. econs 5.
        eapply PrimRecGraph_sound. exact CALL.
      * simpl in CALL. destruct CALL as [y [CALL IH]]. unfold V.tail in CALL. simpl in CALL. unfold V.tail in IH. simpl in IH. econs 6.
        { eapply ACC with (z := y). exact CALL. }
        { eapply PrimRecGraph_sound. exact IH. }
  - destruct fs; intros xs z CALL.
    + simpl in CALL. subst z. econs 1.
    + simpl in CALL. destruct CALL as [y [ys [CALL [CALLs ?]]]]. subst z. econs 2.
      * eapply PrimRecGraph_sound. exact CALL.
      * eapply PrimRecsGraph_sound. exact CALLs.
Qed.

Fixpoint PrimRecGraph_complete (n : arity) (f : PrimRec n) (xs : Vector.t nat n) (z : nat) (SPEC : PrimRecSpec n f xs z) {struct SPEC}
  : PrimRecGraph f xs z
with PrimRecsGraph_complete (n : arity) (m : arity) (fs : PrimRecs n m) (xs : Vector.t nat n) (z : Vector.t nat m) (SPEC : PrimRecsSpec n m fs xs z) {struct SPEC}
  : PrimRecsGraph fs xs z.
Proof.
  - destruct SPEC; simpl.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + exists ys. split.
      * eapply PrimRecsGraph_complete. exact g_spec.
      * eapply PrimRecGraph_complete. exact SPEC.
    + eapply PrimRecGraph_complete. exact SPEC.
    + exists acc. unfold V.tail. simpl. split.
      * apply PrimRecGraph_complete in SPEC1. exact SPEC1.
      * apply PrimRecGraph_complete in SPEC2. exact SPEC2.
  - destruct SPEC; simpl.
    + reflexivity.
    + exists y, ys. split. 
      * eapply PrimRecGraph_complete. exact f_spec.
      * split.
        { eapply PrimRecsGraph_complete. exact SPEC. }
        { reflexivity. }
Qed.

Theorem PrimRecGraph_correct (n : arity) (f : PrimRec n) (xs : Vector.t nat n) (z : nat)
  : PrimRecGraph f xs z <-> PrimRecSpec n f xs z.
Proof.
  pose proof (LEFT := @PrimRecGraph_complete). pose proof (RIGHT := @PrimRecGraph_sound). now firstorder.
Qed.

Theorem PrimRecsGraph_correct (n : arity) (m : arity) (f : PrimRecs n m) (xs : Vector.t nat n) (z : Vector.t nat m)
  : PrimRecsGraph f xs z <-> PrimRecsSpec n m f xs z.
Proof.
  pose proof (LEFT := @PrimRecsGraph_complete). pose proof (RIGHT := @PrimRecsGraph_sound). now firstorder.
Qed.

Fixpoint PrimRecSpec_sound (n : arity) (f : PrimRec n) (xs : Vector.t nat n) (z : nat) (SPEC : PrimRecSpec n f xs z) {struct SPEC}
  : eval_vec xs (runPrimRec f) = z
with PrimRecsSpec_sound (n : arity) (m : arity) (fs : PrimRecs n m) (xs : Vector.t nat n) (z : Vector.t nat m) (SPEC : PrimRecsSpec n m fs xs z) {struct SPEC}
  : V.map (eval_vec xs) (runPrimRecs fs) = z.
Proof.
  - destruct SPEC.
    + reflexivity.
    + reflexivity.
    + eapply eval_proj_spec.
    + simpl. eapply eval_compose_spec.
      * eapply PrimRecsSpec_sound. exact g_spec.
      * eapply PrimRecSpec_sound. exact SPEC.
    + simpl. eapply PrimRecSpec_sound. exact SPEC.
    + simpl. eapply eval_compose_2_spec.
      * apply PrimRecSpec_sound in SPEC1. simpl in SPEC1. exact SPEC1.
      * apply PrimRecSpec_sound in SPEC2. simpl in SPEC2. simpl. exact SPEC2.
  - destruct SPEC.
    + reflexivity.
    + simpl. eapply f_equal2.
      * eapply PrimRecSpec_sound. exact f_spec.
      * eapply PrimRecsSpec_sound. exact SPEC.
Qed.

Fixpoint PrimRecSpec_complete (n : arity) (f : PrimRec n) {struct f}
  : forall xs, PrimRecSpec n f xs (eval_vec xs (runPrimRec f))
with PrimRecsSpec_complete (n : arity) (m : arity) (fs : PrimRecs n m) {struct fs}
  : forall xs, PrimRecsSpec n m fs xs (V.map (eval_vec xs) (runPrimRecs fs)).
Proof.
  - destruct f; simpl.
    + introVCons x xs. revert xs. introVNil. simpl. econs 1.
    + introVNil. econs 2.
    + i. erewrite eval_proj_spec. econs 3.
    + i. econs 4.
      * eapply PrimRecsSpec_complete.
      * erewrite eval_compose_spec.
        { eapply PrimRecSpec_complete. }
        { reflexivity. }
        { reflexivity. }
    + introVCons a xs. simpl. revert a xs. induction a as [ | a IH].
      * simpl. i. econs 5. eapply PrimRecSpec_complete.
      * simpl. i. econs 6. 
        { eapply IH. }
        { erewrite eval_compose_2_spec.
          - eapply PrimRecSpec_complete.
          - reflexivity.
          - reflexivity.
        }
  - destruct fs; simpl.
    + i. econs 1.
    + i. econs 2.
      * eapply PrimRecSpec_complete.
      * eapply PrimRecsSpec_complete.
Qed.

Theorem PrimRecSpec_iff (n : arity) (f : PrimRec n) (xs : Vector.t nat n) (z : nat)
  : PrimRecSpec n f xs z <-> eval_vec xs (runPrimRec f) = z.
Proof.
  split.
  - intros SPEC. eapply PrimRecSpec_sound; exact SPEC.
  - intros <-. eapply PrimRecSpec_complete.
Qed.

Theorem PrimRecsSpec_iff (n : arity) (m : arity) (f : PrimRecs n m) (xs : Vector.t nat n) (z : Vector.t nat m)
  : PrimRecsSpec n m f xs z <-> V.map (eval_vec xs) (runPrimRecs f) = z.
Proof.
  split.
  - intros SPEC. eapply PrimRecsSpec_sound; exact SPEC.
  - intros <-. eapply PrimRecsSpec_complete.
Qed.

End PRIMITIVE_RECURSION.
