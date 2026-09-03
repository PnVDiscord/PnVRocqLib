Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Category.

Declare Scope monad_scope.
Declare Custom Entry do_notation.
Reserved Notation "'do' m" (m custom do_notation at level 10, at level 100, format "'do'  '//' '[hv' m ']'").

Module DoNotations.

#[universes(polymorphic=yes)]
Definition monad@{d c | } (M : Type@{d} -> Type@{c}) {MONAD : isMonad@{d c} M} {A : Type@{d}} : Type@{c} :=
  M A.

#[global] Delimit Scope monad_scope with monad.
#[global] Bind Scope monad_scope with monad.

Open Scope monad_scope.

Notation "'do' m" := m : monad_scope.

Notation "'ret'" := pure (at level 0) : monad_scope.
Notation "'let' x ':=' t ';' m" := (let x := t in m) (in custom do_notation at level 1, x pattern, t constr, m custom do_notation at level 10, format "'let'  x  ':='  t ';' '//' m").
Notation "''' x '<-' m1 ';' m2" := (bind m1 (fun x => m2)) (in custom do_notation at level 1, x pattern, m1 constr, m2 custom do_notation at level 10, format "''' x  '<-'  m1 ';' '//' m2").
Notation "t" := t (in custom do_notation at level 0, t constr).

Section EXAMPLE.

Let do_notation_example1 : option nat := do
  '_ <- Some 1;
  '(x, _) <- Some (2, 3);
  '_ <- Some 4;
  let y := 5;
  '_ <- Some 6;
  ret (x + y).

Let do_notation_example2 (a : nat) : option nat := do
  '_ <- Some 1;
  'x <- Some 2;
  '_ <- Some 3;
  let y := 4;
  match a with
  | O => pure (x + y)
  | S a' => do
    '_ <- Some 5;
    ret 6
  end.

End EXAMPLE.

End DoNotations.

#[local] Open Scope program_scope.

#[universes(polymorphic=yes)]
Class isMonadIter@{d c | } `(M : Type@{d} -> Type@{c}) `{MONAD : isMonad@{d c} M} : Type@{max(d + 1, c)} :=
  monad_iter (I : Type@{d}) (R : Type@{d}) (step : I -> M (I + R)%type) (i0 : I) : M R.

#[global] Arguments monad_iter {M}%_type_scope {MONAD} {isMonadIter} {I}%_type_scope {R}%_type_scope step%_monad_scope i0.

Class MonadIterSpec `(M : Type -> Type) `{SETOID1 : isSetoid1 M} `{MONAD : isMonad M} `{MONADITER : isMonadIter M (MONAD := MONAD)} : Prop :=
  monad_iter_unfold (I : Type) (R : Type) (step : I -> M (I + R)%type)
  : monad_iter step == (step >=> B.either (monad_iter step) pure).

Lemma MonadIterSpec_unfold (M : Type -> Type) (SETOID1 : isSetoid1 M) (MONAD : isMonad M) (MONADITER : isMonadIter M) :
  MonadIterSpec M (SETOID1 := SETOID1) (MONAD := MONAD) (MONADITER := MONADITER) =
  (forall I : Type, forall R : Type, forall k : I -> M (I + R)%type, forall x : I, monad_iter k x == bind (k x) (fun y : I + R => match y with inl x' => monad_iter k x' | inr y' => pure y' end)).
Proof.
  reflexivity.
Defined.

#[universes(polymorphic=yes)]
Class isMonadTrans@{d c | } `(T : (Type@{d} -> Type@{c}) -> (Type@{d} -> Type@{c})) `{T_liftsMonad : forall M : Type@{d} -> Type@{c}, isMonad@{d c} M -> isMonad@{d c} (T M)} : Type@{max(d + 1, c + 1)} :=
  lift (M : Type@{d} -> Type@{c}) (M_isMonad : isMonad@{d c} M) (A : Type@{d}) (m : M A) : T M A.

#[global] Arguments lift {T} {T_liftsMonad} {isMonadTrans} {M} {M_isMonad} {A} m.

Class MonadTransSpec `(T : (Type -> Type) -> (Type -> Type)) `{T_liftsSetoid1 : forall M : Type -> Type, isSetoid1 M -> isSetoid1 (T M)} `{T_liftsMonad : forall M : Type -> Type, isMonad M -> isMonad (T M)} `{T_isMonadTrans : isMonadTrans T (T_liftsMonad := T_liftsMonad)} : Prop :=
  { MonadTrans_satisfiesMonadLaws (M : Type -> Type) (M_isSetoid1 : isSetoid1 M) (M_isMonad : isMonad M)
    (M_satisfiesMonadLaws : @MonadLaws M M_isSetoid1 M_isMonad)
    : @MonadLaws (T M) (T_liftsSetoid1 M M_isSetoid1) (T_liftsMonad M M_isMonad)
  ; lift_cong (M : Type -> Type) `(M_satisfiesMonadLaws : MonadLaws M) (A : Type) (m : M A) (m' : M A)
    (m_eq_m' : m == m')
    : lift (T := T) m == lift (T := T) m'
  ; lift_pure (M : Type -> Type) `(M_satisfiesMonadLaws : MonadLaws M) (A : Type) (x : A)
    : lift (T := T) (pure x) == pure x
  ; lift_bind (M : Type -> Type) `(M_satisfiesMonadLaws : MonadLaws M) (A : Type) (B : Type) (m : M A) (m' : M A) (k : A -> M B) (k' : A -> M B)
    (m_eq_m' : m == m')
    (k_eq_k' : forall x : A, k x == k' x)
    : lift (T := T) (m >>= k) == (lift m' >>= fun x' : A => lift (k' x')) 
  }.

Section STATE_MONAD.

#[local] Existing Instance B.stateT_isSetoid1.

Context {S : Type}.

#[global]
Instance stateT_isMonadIter {M : Type -> Type} {MONAD : isMonad M} {MONADITER : isMonadIter M} : isMonadIter (B.stateT S M) :=
  fun I : Type => fun R : Type => fun step : I -> B.stateT S M (I + R) =>
  B.StateT ∘ curry (monad_iter (uncurry (B.runStateT ∘ step) >=> uncurry (B.either (curry (pure ∘ inl)) (curry (pure ∘ inr))))).

#[global]
Instance stateT_MonadIterSpec {M : Type -> Type} {SETOID1 : isSetoid1 M} {MONAD : isMonad M} {MONADITER : isMonadIter M}
  (MONADLAW : MonadLaws M)
  (MONADITERSPEC : MonadIterSpec M)
  : MonadIterSpec (B.stateT S M).
Proof.
  red; i. pose proof (monad_iter_unfold (MONADITER := MONADITER) (I * S) (R * S)) as claim1; cbn in claim1.
  cbn. intros i s. unfold curry, "∘", ">=>". simpl. rewrite claim1 at 1. unfold ">=>". simpl. destruct (step i) as [k].
  cbn. rewrite <- bind_assoc. eapply bind_compatWith_eqProp_r. now intros [[x' | i'] s']; simpl; rewrite bind_pure_l.
Qed.

Definition get {M : Type -> Type} {MONAD : isMonad M} : B.stateT S M S :=
  B.StateT $ fun s => pure (s, s).

Definition put {M : Type -> Type} {MONAD : isMonad M} : S -> B.stateT S M unit :=
  fun s => B.StateT $ fun _ => pure (tt, s).

End STATE_MONAD.
