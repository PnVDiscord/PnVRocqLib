Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Category.

Definition monad {M : Type -> Type} {MONAD : isMonad M} {A : Type} : Type :=
  M A.

Declare Scope monad_scope.
Declare Custom Entry do_notation.
Delimit Scope monad_scope with monad.
Bind Scope monad_scope with monad.
Open Scope monad_scope.

Reserved Notation "'do' m" (m custom do_notation at level 10, at level 0, format "'do'  '//' m").
Notation "'do' m" := m : monad_scope.
Notation "'do' m" := (m : monad).

Notation "( m )" := m (in custom do_notation, m at level 10).
Notation "` t" := t (in custom do_notation at level 0, t constr, format "'`' t").
Notation "x" := x (in custom do_notation at level 0, x ident).
Notation "'let' x ':=' t ';' m" := (let x := t in m) (in custom do_notation at level 0, x pattern, t constr, m custom do_notation at level 10, format "'let'  x  ':='  t ';' '//' m").
Notation "x '<-' m1 ';' m2" := (m1 >>= fun x => m2) (in custom do_notation at level 0, x ident, m1 custom do_notation at level 9, m2 custom do_notation at level 10, format "x  '<-'  m1 ';' '//' m2").
Notation "''' x '<-' m1 ';' m2" := (m1 >>= fun 'x => m2) (in custom do_notation at level 0, x strict pattern, m1 custom do_notation at level 9, m2 custom do_notation at level 10, format "''' x  '<-'  m1 ';' '//' m2").
Notation "'ret' t" := (pure t) (in custom do_notation at level 0, t constr, format "'ret'  t").
Notation " m1 ';' m2 " := (m1 >>= fun _ => m2) (in custom do_notation at level 10, m2 custom do_notation at level 10, format "m1 ';' '//' m2").

#[local] Open Scope program_scope.

Class isMonadIter (M : Type -> Type) {MONAD : isMonad M} : Type :=
  monad_iter (I : Type) (R : Type) (step : I -> M (I + R)%type) (i0 : I) : M R.

#[global] Arguments monad_iter {M}%type {MONAD} {isMonadIter} {I}%type {R}%type step%monad_scope i0.

Class MonadIterSpec (M : Type -> Type) {MONAD : isMonad M} {MONADITER : isMonadIter M} {SETOID1 : isSetoid1 M} : Prop :=
  { monad_iter_step {I : Type} {R : Type} (step : I -> M (I + R)%type)
    : monad_iter step == step >=> B.either (monad_iter step) pure
  }.

Section STATE_MONAD.

#[local] Existing Instance B.stateT_isSetoid1.

#[global]
Instance stateT_isMonadIter {M : Type -> Type} {MONAD : isMonad M} {MONADITER : isMonadIter M} {S : Type} : isMonadIter (B.stateT S M) :=
  fun I : Type => fun R : Type => fun step : I -> B.stateT S M (I + R) => fun i0 : I => B.StateT $ fun s0 : S => flip monad_iter (i0, s0) $ fun '(i, s) => do
    '(x, s') <- `B.runStateT (step i) s;
    `match x with
    | inl i' => pure (inl (i', s'))
    | inr x' => pure (inr (x', s'))
    end.

Lemma stateT_MonadIterSpec {M : Type -> Type} {MONAD : isMonad M} {MONADITER : isMonadIter M} {SETOID1 : isSetoid1 M} {S : Type}
  (MONADLAW : MonadLaws M)
  (MONADITERSPEC : MonadIterSpec M)
  : MonadIterSpec (B.stateT S M).
Proof.
  econs; i. pose proof (monad_iter_step (MONADITER := MONADITER) (I := I * S) (R := R * S)) as claim1. do 2 red in claim1.
  cbn. intros i s. unfold flip, "$". rewrite claim1 at 1. unfold ">=>", uncurry, curry. destruct (step i) as [k] eqn: H_OBS; simpl.
  rewrite <- bind_assoc. eapply bind_compatWith_eqProp_r. now intros [[i' | x] s']; simpl; rewrite bind_pure_l.
Qed.

Definition get {M : Type -> Type} {MONAD : isMonad M} {S : Type} : B.stateT S M S :=
  B.StateT $ fun s => pure (s, s).

Definition put {M : Type -> Type} {MONAD : isMonad M} {S : Type} : S -> B.stateT S M unit :=
  fun s => B.StateT $ fun _ => pure (tt, s).

End STATE_MONAD.
