Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Category.

Module DoNotations.

#[universes(polymorphic=yes)]
Definition monad@{u v} {M : Type@{u} -> Type@{v}} {MONAD : isMonad@{u v} M} {A : Type@{u}} : Type@{v} :=
  M A.

Declare Scope monad_scope.
Declare Custom Entry do_notation.

Delimit Scope monad_scope with monad.
Bind Scope monad_scope with monad.
Open Scope monad_scope.

Reserved Notation "'do' m" (m custom do_notation at level 10, at level 0, format "'do'  '//' m").
Notation "'do' m" := m : monad_scope.
Notation "'do' m" := (m : monad).

Notation "x '<-' m1 ';' m2" := (m1 >>= fun x => m2) (in custom do_notation at level 0, x ident, m1 constr, m2 custom do_notation at level 10, format "x  '<-'  m1 ';' '//' m2").
Notation "'let' x ':=' t ';' m" := (let x := t in m) (in custom do_notation at level 0, x pattern, t constr, m custom do_notation at level 10, format "'let'  x  ':='  t ';' '//' m").
Notation "''' x '<-' m1 ';' m2" := (m1 >>= fun 'x => m2) (in custom do_notation at level 0, x pattern, m1 constr, m2 custom do_notation at level 10, format "''' x  '<-'  m1 ';' '//' m2").
Notation "m1 ';' m2" := (m1 >>= fun _ => m2) (in custom do_notation at level 0, m1 constr, m2 custom do_notation at level 10, format "m1 ';' '//' m2").
Notation "'ret' t" := (pure t) (in custom do_notation at level 10, t constr, format "'ret'  t").
Notation "t" := t (in custom do_notation at level 0, t constr).

Section EXAMPLE.

Let do_notation_example1 : option nat := do
  Some 1;
  'x <- Some 2;
  Some 3;
  let y := 4;
  Some 5;
  ret (x + y).

End EXAMPLE.

End DoNotations.

#[local] Open Scope program_scope.

Class isMonadIter (M : Type -> Type) {MONAD : isMonad M} : Type :=
  monad_iter (I : Type) (R : Type) (step : I -> M (I + R)%type) (i0 : I) : M R.

#[global] Arguments monad_iter {M}%_type {MONAD} {isMonadIter} {I}%_type {R}%_type step%_monad_scope i0.

Class MonadIterSpec (M : Type -> Type) {MONAD : isMonad M} {MONADITER : isMonadIter M} {SETOID1 : isSetoid1 M} : Prop :=
  monad_iter_unfold (I : Type) (R : Type) (step : I -> M (I + R)%type)
  : monad_iter step == step >=> B.either (monad_iter step) pure.

Lemma MonadIterSpec_unfold (M : Type -> Type) (MONAD : isMonad M) (MONADITER : isMonadIter M) (SETOID1 : isSetoid1 M) :
  MonadIterSpec M (MONAD := MONAD) (MONADITER := MONADITER) (SETOID1 := SETOID1) =
  (forall I : Type, forall R : Type, forall k : I -> M (I + R)%type, forall x : I, monad_iter k x == bind (k x) (fun y : I + R => match y with inl x' => monad_iter k x' | inr y' => pure y' end)).
Proof.
  reflexivity.
Defined.

Section STATE_MONAD.

#[local] Existing Instance B.stateT_isSetoid1.

Context {S : Type}.

#[global]
Instance stateT_isMonadIter {M : Type -> Type} {MONAD : isMonad M} {MONADITER : isMonadIter M} : isMonadIter (B.stateT S M) :=
  fun I : Type => fun R : Type => fun step : I -> B.stateT S M (I + R) =>
  B.StateT ∘ curry (monad_iter (uncurry (B.runStateT ∘ step) >=> uncurry (B.either (curry (pure ∘ inl)) (curry (pure ∘ inr))))).

#[global]
Instance stateT_MonadIterSpec {M : Type -> Type} {MONAD : isMonad M} {MONADITER : isMonadIter M} {SETOID1 : isSetoid1 M}
  (MONADLAW : MonadLaws M)
  (MONADITERSPEC : MonadIterSpec M)
  : MonadIterSpec (B.stateT S M).
Proof.
  red; i. pose proof (monad_iter_unfold (MONADITER := MONADITER) (I * S) (R * S)) as claim1; do 2 red in claim1.
  cbn. intros i s. unfold curry, "∘", ">=>". simpl. rewrite claim1 at 1. unfold ">=>". simpl. destruct (step i) as [k].
  cbn. rewrite <- bind_assoc. eapply bind_compatWith_eqProp_r. now intros [[x' | i'] s']; simpl; rewrite bind_pure_l.
Qed.

Definition get {M : Type -> Type} {MONAD : isMonad M} : B.stateT S M S :=
  B.StateT $ fun s => pure (s, s).

Definition put {M : Type -> Type} {MONAD : isMonad M} : S -> B.stateT S M unit :=
  fun s => B.StateT $ fun _ => pure (tt, s).

End STATE_MONAD.
