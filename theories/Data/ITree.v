Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Monad.
Require Import PnV.Control.Category.

Declare Scope itree_scope.
Open Scope itree_scope.

Variant itreeF (itree : Type) (E : Type -> Type) (R : Type) : Type :=
  | RetF (r : R) : itreeF itree E R
  | TauF (t : itree) : itreeF itree E R
  | VisF (X : Type) (e : E X) (k : X -> itree) : itreeF itree E R.

#[global] Arguments RetF {itree} {E}%_type_scope {R}%_type_scope r.
#[global] Arguments TauF {itree} {E}%_type_scope {R}%_type_scope t%_itree_scope.
#[global] Arguments VisF {itree} {E}%_type_scope {R}%_type_scope X%_type_scope e k%_itree_scope.

#[projections(primitive)]
CoInductive itree (E : Type -> Type) (R : Type) : Type :=
  go { observe : itreeF (itree E R) E R }.

#[global] Arguments go {E}%_type_scope {R}%_type_scope observe.
#[global] Arguments observe {E}%_type_scope {R}%_type_scope.

Bind Scope itree_scope with itree.
Delimit Scope itree_scope with itree.

Notation Ret r := (go (RetF r)).
Notation Tau t := (go (TauF t)).
Notation Vis X e k := (go (VisF X e k)).

Inductive callE (I : Type) (R : Type) : Type -> Type :=
  | Call : I -> callE I R R.

#[global] Arguments Call {I} {R}.

Inductive stateE (S : Type) : Type -> Type :=
  | GetS : stateE S S
  | PutS : S -> stateE S unit.

#[global] Arguments GetS {S}.
#[global] Arguments PutS {S}.

Section ITREE_METHOD.

Context {E : Type -> Type}.

Definition itree_guard {R1 : Type} {R2 : Type} (k0 : R1 -> itree E R2) (ot0 : itreeF (itree E R1) E R1) (CIH : itree E R1 -> itree E R2) : itree E R2 :=
  match ot0 with
  | RetF r => k0 r
  | TauF t => Tau (CIH t)
  | VisF X e k => Vis X e (fun x : X => CIH (k x))
  end.

Definition itree_bind' {R1 : Type} {R2 : Type} (k : R1 -> itree E R2) : itree E R1 -> itree E R2 :=
  cofix bind' (t : itree E R1) : itree E R2 := itree_guard (R1 := R1) (R2 := R2) k (observe t) bind'.

#[global]
Instance itree_isMonad : isMonad (itree E) :=
  { pure {A : Type} (x : A) := Ret x
  ; bind {A : Type} {B : Type} (m : itree E A) (k : A -> itree E B) := itree_bind' k m
  }.

#[global]
Instance itree_isMonadIter : isMonadIter (itree E) :=
  fun I : Type => fun R : Type => fun step : I -> itree E (I + R) =>
  cofix iter (i : I) : itree E R := itree_isMonad.(bind) (step i) (B.either (fun i' : I => Tau (iter i')) (fun r : R => Ret r)).

Definition itree_trigger {E : Type -> Type} : E ~~> itree E :=
  fun R : Type => fun e : E R => Vis R e (fun x : R => Ret x).

Definition callE_handler {E : Type -> Type} {I : Type} {R : Type} (callee : I -> itree E R) : callE I R ~~> itree E :=
  @callE_rect I R (fun X : Type => fun _ : callE I R X => itree E X) callee.

Definition stateE_handler {S : Type} : stateE S ~~> B.stateT S (itree E) :=
  @stateE_rect S (fun X : Type => fun _ : stateE S X => B.stateT S (itree E) X) get put.

Definition itree_interpret {M : Type -> Type} {M_isMonad : isMonad M} {M_isMonadIter : isMonadIter M} (handle : E ~~> M) : itree E ~~> M :=
  fun R : Type => monad_iter $ fun t0 : itree E R =>
    match observe t0 with
    | RetF r => pure (inr r)
    | TauF t => pure (inl t)
    | VisF X e k => bind (handle X e) (fun x : X => pure (inl (k x)))
    end.

End ITREE_METHOD.

Section CATEGORY.

Import CAT.

#[global]
Instance handlerCat : isCategory :=
  { ob := Type -> Type
  ; hom (E : Type -> Type) (E' : Type -> Type) := E ~~> itree E'
  ; compose {E : Type -> Type} {E' : Type -> Type} {E'' : Type -> Type} (h2 : E' ~~> itree E'') (h1 : E ~~> itree E') := fun R : Type => fun e : E R => itree_interpret (E := E') (M := itree E'') h2 R (h1 R e)
  ; id {E : Type -> Type} := itree_trigger (E := E)
  }.

#[global]
Instance handlerCat_hasCoproduct : hasCoproduct handlerCat :=
  { sum := B.sum1
  ; inl {E : Type -> Type} {E' : Type -> Type} := fun R : Type => fun e : E R => itree_trigger R (@B.inl1 E E' R e)
  ; inr {E : Type -> Type} {E' : Type -> Type} := fun R : Type => fun e : E' R => itree_trigger R (@B.inr1 E E' R e)
  ; case {E : Type -> Type} {E' : Type -> Type} {E'' : Type -> Type} (h1 : E ~~> itree E'') (h2 : E' ~~> itree E'') := fun R : Type => @B.sum1_rect _ _ _ (fun _ : B.sum1 E E' R => itree E'' R) (h1 R) (h2 R)
  }.

#[global]
Instance handlerCat_hasInitial : hasInitial handlerCat :=
  { void := B.void1
  ; exfalso {E : Type -> Type} := fun R : Type => @B.void1_rect _ (fun _ : B.void1 R => itree E R)
  }.

End CATEGORY.

Section RECURSION.

#[local] Notation endo X := (X -> X).

Definition itree_interpret_mrec {E1 : Type -> Type} {E2 : Type -> Type} (ctx : E1 ~~> itree (E1 +' E2)) : itree (E1 +' E2) ~~> itree E2 :=
  fun R : Type => monad_iter $ fun t0 : itree (E1 +' E2) R =>
    match observe t0 with
    | RetF r => Ret (inr r)
    | TauF t => Ret (inl t)
    | VisF X e k =>
      match e with
      | B.inl1 e1 => Ret (inl (bind (ctx X e1) k))
      | B.inr1 e2 => Vis X e2 (fun x : X => pure (inl (k x)))
      end
    end.

Definition itree_mrec {E : Type -> Type} {E' : Type -> Type} (ctx : E ~~> itree (E +' E')) : E ~~> itree E' :=
  fun R : Type => fun e : E R => itree_interpret_mrec (E1 := E) (E2 := E') ctx R (ctx R e).

Definition itree_mrec_fix {E : Type -> Type} {E' : Type -> Type} (ctx : endo (E ~~> itree (E +' E'))) : E ~~> itree E' :=
  itree_mrec (E := E) (E' := E') (ctx handlerCat_hasCoproduct.(CAT.inl)).

Definition itree_rec {E : Type -> Type} {I : Type} {R : Type} (body : I -> itree (callE I R +' E) R) (arg : I) : itree E R :=
  itree_mrec (E := callE I R) (E' := E) (callE_handler body) R (Call arg).

Definition itree_call {E : Type -> Type} {I : Type} {R : Type} (arg : I) : itree (callE I R +' E) R :=
  handlerCat_hasCoproduct.(CAT.inl) R (Call arg).

Definition itree_rec_fix {E : Type -> Type} {I : Type} {R : Type} (body : endo (I -> itree (callE I R +' E) R)) : I -> itree E R :=
  itree_rec (E := E) (I := I) (R := R) (body itree_call).

End RECURSION.
