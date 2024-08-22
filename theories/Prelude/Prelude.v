Require Export PvN.Prelude.Notations.
Require Export PvN.Prelude.SfLib.
Require Export Coq.Arith.Compare_dec.
Require Export Coq.Arith.PeanoNat.
Require Export Coq.Bool.Bool.
Require Export Coq.Classes.RelationClasses.
Require Export Coq.Lists.List.
Require Export Coq.micromega.Lia.
Require Export Coq.Program.Basics.
Require Export Coq.Program.Utils.
Require Export Coq.Relations.Relation_Definitions.
Require Export Coq.Relations.Relation_Operators.
Require Export Coq.Setoids.Setoid.

#[local] Obligation Tactic := idtac.

(** Section SETOID. *)

Class isSetoid (A : Type) : Type :=
  { eqProp (lhs : A) (rhs : A) : Prop
  ; eqProp_Equivalence :: Equivalence eqProp
  }.

Infix "==" := eqProp : type_scope.

#[global, program]
Instance Prop_isSetoid : isSetoid Prop :=
  { eqProp := iff
  ; eqProp_Equivalence := iff_equivalence
  }.

#[global, program]
Instance pi_isSetoid {A : Type} {B : A -> Type} `(SETOID : forall x : A, isSetoid (B x)) : isSetoid (forall x : A, B x) :=
  { eqProp f g := forall x, f x == g x }.
Next Obligation.
  split.
  - intros f1 x. reflexivity.
  - intros f1 f2 EQ x. symmetry; exact (EQ x).
  - intros f1 f2 f3 EQ EQ' x. transitivity (f2 x); [exact (EQ x) | exact (EQ' x)].
Qed.

#[program]
Definition mkSetoidFromPreOrder {A : Type} {leProp : A -> A -> Prop} `(leProp_PreOrder : @PreOrder A leProp) : isSetoid A :=
  {| eqProp (x : A) (y : A) := leProp x y /\ leProp y x |}.
Next Obligation.
  split; ii.
  - exact (conj (@PreOrder_Reflexive A leProp leProp_PreOrder x) (@PreOrder_Reflexive A leProp leProp_PreOrder x)).
  - exact (conj (proj2 H) (proj1 H)).
  - exact (conj (@PreOrder_Transitive A leProp leProp_PreOrder x y z (proj1 H) (proj1 H0)) (@PreOrder_Transitive A leProp leProp_PreOrder z y x (proj2 H0) (proj2 H))).
Defined.

Lemma mkSetoidFromPreOrder_derivesPartialOrder {A : Type} {leProp : A -> A -> Prop} `(leProp_PreOrder : @PreOrder A leProp)
  (SETOID := mkSetoidFromPreOrder leProp_PreOrder)
  : PartialOrder SETOID.(eqProp) leProp.
Proof.
  cbv. intros x y. split; exact (fun H => H).
Defined.

Lemma eqProp_refl {A : Type} `{A_isSetoid : isSetoid A}
  : forall x : A, x == x.
Proof.
  eapply Equivalence_Reflexive.
Defined.

Lemma eqProp_sym {A : Type} `{A_isSetoid : isSetoid A}
  : forall x : A, forall y : A, x == y -> y == x.
Proof.
  eapply Equivalence_Symmetric.
Defined.

Lemma eqProp_trans {A : Type} `{A_isSetoid : isSetoid A}
  : forall x : A, forall y : A, forall z : A, x == y -> y == z -> x == z.
Proof.
  eapply Equivalence_Transitive.
Defined.

Class eqPropCompatible1 {A : Type} {B : Type} `{A_isSetoid : isSetoid A} `{B_isSetoid : isSetoid B} (f : A -> B) : Prop :=
  compatibleWith_eqProp_1 x1 x2 (x_EQ : x1 == x2) : f x1 == f x2.

Class eqPropCompatible2 {A : Type} {B : Type} {C : Type} `{A_isSetoid : isSetoid A} `{B_isSetoid : isSetoid B} `{C_isSetoid : isSetoid C} (f : A -> B -> C) : Prop :=
  compatibleWith_eqProp_2 x1 x2 y1 y2 (x_EQ : x1 == x2) (y_EQ : y1 == y2) : f x1 y1 == f x2 y2.

#[global]
Add Parametric Morphism {A : Type} {B : Type} `{A_isSetoid : isSetoid A} `{B_isSetoid : isSetoid B} (f : A -> B)
  `(COMPAT : @eqPropCompatible1 A B A_isSetoid B_isSetoid f)
  : f with signature (eqProp ==> eqProp)
  as compatibleWith_eqProp_1'.
Proof.
  intros x1 x2 x_EQ. exact (compatibleWith_eqProp_1 x1 x2 x_EQ).
Defined.

#[global]
Add Parametric Morphism {A : Type} {B : Type} {C : Type} `{A_isSetoid : isSetoid A} `{B_isSetoid : isSetoid B} `{C_isSetoid : isSetoid C} (f : A -> B -> C)
  `(COMPAT : @eqPropCompatible2 A B C A_isSetoid B_isSetoid C_isSetoid f)
  : f with signature (eqProp ==> eqProp ==> eqProp)
  as compatibleWith_eqProp_2'.
Proof.
  intros x1 x2 x_EQ y1 y2 y_EQ. exact (compatibleWith_eqProp_2 x1 x2 y1 y2 x_EQ y_EQ).
Defined.

(** End SETOID. *)

(** Section POSET. *)

Class isPoset (A : Type) : Type :=
  { leProp (lhs : A) (rhs : A) : Prop
  ; Poset_isSetoid :: isSetoid A
  ; leProp_PreOrder :: PreOrder leProp
  ; leProp_PartialOrder :: PartialOrder eqProp leProp
  }.

Infix "=<" := leProp : type_scope.

Definition Prop_isPoset : isPoset Prop :=
  let impl_PreOrder : PreOrder impl := {| PreOrder_Reflexive (A : Prop) := id (A := A); PreOrder_Transitive (A : Prop) (B : Prop) (C : Prop) := flip (compose (A := A) (B := B) (C := C)); |} in
  {|
    leProp P Q := P -> Q;
    Poset_isSetoid := mkSetoidFromPreOrder impl_PreOrder;
    leProp_PreOrder := impl_PreOrder;
    leProp_PartialOrder := mkSetoidFromPreOrder_derivesPartialOrder impl_PreOrder;
  |}.

#[program]
Definition pi_isPoset {A : Type} {B : A -> Type} `(POSET : forall x : A, isPoset (B x)) : isPoset (forall x : A, B x) :=
  {| leProp f g := forall x, f x =< g x; Poset_isSetoid := pi_isSetoid (fun x : A => (POSET x).(Poset_isSetoid)) |}.
Next Obligation.
  split.
  - intros f1 x. exact (PreOrder_Reflexive (f1 x)).
  - intros f1 f2 f3 LE1 LE2 x. exact (PreOrder_Transitive (f1 x) (f2 x) (f3 x) (LE1 x) (LE2 x)).
Defined.
Next Obligation.
  i. intros f g. split; [intros f_eq_g | intros [f_le_g g_le_f] x].
  - assert (claim : forall x : A, f x =< g x /\ g x =< f x).
    { intros x. eapply leProp_PartialOrder. exact (f_eq_g x). }
    exact (conj (fun x => proj1 (claim x)) (fun x => proj2 (claim x))).
  - eapply leProp_PartialOrder. exact (conj (f_le_g x) (g_le_f x)).
Defined.

Lemma leProp_refl {A : Type} `{A_isPoset : isPoset A}
  : forall x : A, x =< x.
Proof.
  eapply PreOrder_Reflexive.
Defined.

Lemma leProp_trans {A : Type} `{A_isPoset : isPoset A}
  : forall x : A, forall y : A, forall z : A, x =< y -> y =< z -> x =< z.
Proof.
  eapply PreOrder_Transitive.
Defined.

Lemma leProp_antisymmetry {A : Type} `{A_isPoset : isPoset A}
  : forall x : A, forall y : A, x =< y -> y =< x -> x == y.
Proof.
  intros x y x_le_y y_le_x. exact (proj2 (leProp_PartialOrder x y) (conj x_le_y y_le_x)).
Defined.

Lemma eqProp_implies_leProp {A : Type} `{A_isPoset : isPoset A}
  : forall x : A, forall y : A, x == y -> x =< y.
Proof.
  intros x y x_eq_y. exact (proj1 (proj1 (leProp_PartialOrder x y) x_eq_y)).
Defined.

Class isMonotonic1 {A : Type} {B : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} (f : A -> B) : Prop :=
  compatibleWith_leProp_1 x1 x2 (x_LE : x1 =< x2) : f x1 =< f x2.

Class isMonotonic2 {A : Type} {B : Type} {C : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} `{C_isPoset : isPoset C} (f : A -> B -> C) : Prop :=
  compatibleWith_leProp_2 x1 x2 y1 y2 (x_LE : x1 =< x2) (y_LE : y1 =< y2) : f x1 y1 =< f x2 y2.

#[global]
Add Parametric Morphism {A : Type} {B : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} (f : A -> B)
  `(MONOTONIC : @isMonotonic1 A B A_isPoset B_isPoset f)
  : f with signature (leProp ==> leProp)
  as compatibleWith_leProp_1'.
Proof.
  intros x1 x2 x_LE. exact (compatibleWith_leProp_1 x1 x2 x_LE).
Defined.

#[global]
Add Parametric Morphism {A : Type} {B : Type} {C : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} `{C_isPoset : isPoset C} (f : A -> B -> C)
  `(MONOTONIC : @isMonotonic2 A B C A_isPoset B_isPoset C_isPoset f)
  : f with signature (leProp ==> leProp ==> leProp)
  as compatibleWith_leProp_2'.
Proof.
  intros x1 x2 x_LE y1 y2 y_LE. exact (compatibleWith_leProp_2 x1 x2 y1 y2 x_LE y_LE).
Defined.

#[global]
Add Parametric Morphism {A : Type} {B : Type} {C : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} `{C_isPoset : isPoset C} (f : A -> B -> C)
  `(MONOTONIC : @isMonotonic2 A B C A_isPoset B_isPoset C_isPoset f)
  : f with signature (eqProp ==> leProp ==> leProp)
  as compatibleWith_leProp_2_eqProp_l.
Proof.
  intros x1 x2 x_EQ y1 y2 y_LE. exact (compatibleWith_leProp_2 x1 x2 y1 y2 (eqProp_implies_leProp x1 x2 x_EQ) y_LE).
Defined.

#[global]
Add Parametric Morphism {A : Type} {B : Type} {C : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} `{C_isPoset : isPoset C} (f : A -> B -> C)
  `(MONOTONIC : @isMonotonic2 A B C A_isPoset B_isPoset C_isPoset f)
  : f with signature (leProp ==> eqProp ==> leProp)
  as compatibleWith_leProp_2_eqProp_r.
Proof.
  intros x1 x2 x_LE y1 y2 y_EQ. exact (compatibleWith_leProp_2 x1 x2 y1 y2 x_LE (eqProp_implies_leProp y1 y2 y_EQ)).
Defined.

#[global]
Add Parametric Morphism {A : Type} {B : Type} {C : Type} `{A_isPoset : isPoset A} `{B_isPoset : isPoset B} `{C_isPoset : isPoset C} (f : A -> B -> C)
  `(MONOTONIC : @isMonotonic2 A B C A_isPoset B_isPoset C_isPoset f)
  : f with signature (eqProp ==> eqProp ==> leProp)
  as compatibleWith_leProp_2_eqProp_lr.
Proof.
  intros x1 x2 x_EQ y1 y2 y_EQ. exact (compatibleWith_leProp_2 x1 x2 y1 y2 (eqProp_implies_leProp x1 x2 x_EQ) (eqProp_implies_leProp y1 y2 y_EQ)).
Defined.

(** End POSET. *)

Lemma PreOrder_iff {A : Type} (R : A -> A -> Prop)
  : PreOrder R <-> (forall x, forall y, R x y <-> (forall z, R z x -> R z y)).
Proof.
  firstorder.
Qed.

Class isClosureOperator {A : Type} `{POSET : isPoset A} (cl : A -> A) : Prop :=
  { cl_op_increasing : forall x, x =< cl x
  ; cl_op_idemponent : forall x, cl (cl x) == cl x
  ; cl_op_monotonic : isMonotonic1 cl
  }.

Lemma isClosureOperator_iff {A : Type} `{POSET : isPoset A} (cl : A -> A)
  : isClosureOperator cl <-> (forall x, forall y, x =< cl y <-> cl x =< cl y).
Proof.
  split.
  - intros [INCREASING IDEMPONENT MONOTONIC] x y. split; intros LE.
    + rewrite <- IDEMPONENT with (x := y). eapply MONOTONIC. exact LE.
    + transitivity (cl x). eapply INCREASING. exact LE.
  - intros IFF. split; ii.
    + rewrite -> IFF. reflexivity.
    + eapply leProp_antisymmetry.
      * rewrite <- IFF. reflexivity.
      * rewrite -> IFF. reflexivity.
    + rewrite <- IFF. transitivity x2. exact x_LE. rewrite -> IFF. reflexivity.
Qed.

Class isSetoid1 (F : Type -> Type) : Type :=
  liftSetoid1 (X : Type) `(SETOID : isSetoid X) : isSetoid (F X).

Definition mkSetoid_from_eq {A : Type} : isSetoid A :=
  {| eqProp := @eq A; eqProp_Equivalence := eq_equivalence |}.

#[global]
Instance fromSetoid1 {F : Type -> Type} {A : Type} `(SETOID1 : isSetoid1 F) : isSetoid (F A) :=
  liftSetoid1 A mkSetoid_from_eq.

(** Section FUNCTOR. *)

Class isFunctor (F : Type -> Type) : Type :=
  fmap (A : Type) (B : Type) (f : A -> B) : F A -> F B.

#[global] Arguments fmap {F} {isFunctor} {A} {B} f.

Class FunctorLaws (F : Type -> Type) `{SETOID1 : isSetoid1 F} `{FUNCTOR : isFunctor F} : Prop :=
  { fmap_compatWith_eqProp {A : Type} {B : Type} (f : A -> B) (x : F A) (y : F A)
    (EQ : x == y)
    : fmap f x == fmap f y
  ; fmap_compose {A : Type} {B : Type} {C : Type} (f : A -> B) (g : B -> C)
    : fmap (@compose A B C g f) == compose (fmap g) (fmap f)
  ; fmap_id {A : Type}
    : fmap (@id A) == id
  }.

#[global]
Add Parametric Morphism {F : Type -> Type} `{SETOID1 : isSetoid1 F} `{FUNCTOR : isFunctor F} {A : Type} {B : Type}
  `(FUNCTOR_LAWS : @FunctorLaws F SETOID1 FUNCTOR)
  : (@fmap F FUNCTOR A B) with signature (eq ==> eqProp ==> eqProp)
  as fmap_eq_eqProp_eqProp.
Proof.
  intros f x y EQ. exact (fmap_compatWith_eqProp f x y EQ).
Defined.

(** End FUNCTOR. *)

(** Section MONAD. *)

Class isMonad (M : Type -> Type) : Type :=
  { bind {A : Type} {B : Type} (m : M A) (k : A -> M B) : M B
  ; pure {A : Type} : A -> M A
  }.

Class MonadLaws (M : Type -> Type) `{SETOID1 : isSetoid1 M} `{MONAD : isMonad M} : Prop :=
  { bind_compatWith_eqProp_l {A : Type} {B : Type} (m1 : M A) (m2 : M A) (k : A -> M B)
    (m_EQ : m1 == m2)
    : bind m1 k == bind m2 k
  ; bind_compatWith_eqProp_r {A : Type} {B : Type} (m : M A) (k1 : A -> M B) (k2 : A -> M B)
    (k_EQ : k1 == k2)
    : bind m k1 == bind m k2
  ; bind_assoc {A : Type} {B : Type} {C : Type} (m : M A) (k : A -> M B) (k' : B -> M C)
    : bind m (fun x => bind (k x) k') == bind (bind m k) k'
  ; bind_pure_l {A : Type} {B : Type} (k : A -> M B) (x : A)
    : bind (pure x) k == k x
  ; bind_pure_r {A : Type} (m : M A)
    : bind m pure == m
  }.

#[global]
Add Parametric Morphism {M : Type -> Type} `{SETOID1 : isSetoid1 M} `{MONAD : isMonad M} {A: Type} {B: Type}
  `(MONAD_LAWS : @MonadLaws M SETOID1 MONAD)
  : (@bind M MONAD A B) with signature (eqProp ==> eqProp ==> eqProp)
  as bind_compatWith_eqProp.
Proof.
  intros m1 m2 m_EQ k1 k2 k_EQ.
  rewrite bind_compatWith_eqProp_l with (m1 := m1) (m2 := m2) (m_EQ := m_EQ).
  rewrite bind_compatWith_eqProp_r with (k1 := k1) (k2 := k2) (k_EQ := k_EQ).
  reflexivity.
Qed.

Definition mkFunctorFromMonad {M : Type -> Type} `(MONAD : isMonad M) : isFunctor M :=
  fun A : Type => fun B : Type => fun f : A -> B => fun m : M A => bind m (fun x : A => pure (f x)).

Lemma mkFunctorFromMonad_good {M : Type -> Type} `{SETOID1 : isSetoid1 M} `{MONAD : isMonad M}
  `(MONAD_LAWS : @MonadLaws M SETOID1 MONAD)
  : @FunctorLaws M SETOID1 (mkFunctorFromMonad MONAD).
Proof.
  split; ii.
  - unfold fmap. unfold mkFunctorFromMonad. rewrite EQ. reflexivity.
  - unfold compose. unfold fmap. unfold mkFunctorFromMonad. symmetry.
    rewrite <- bind_assoc. eapply bind_compatWith_eqProp_r. intros i.
    rewrite bind_pure_l. reflexivity.
  - unfold id. unfold fmap. unfold mkFunctorFromMonad.
    rewrite bind_pure_r. reflexivity.
Qed.

Definition liftM2 {M : Type -> Type} {A : Type} {B : Type} {C : Type} `{MONAD : isMonad M} (f : A -> B -> C) : M A -> M B -> M C :=
  fun mx => fun my => bind mx (fun x => bind my (fun y => pure (f x y))).

(** End MONAD. *)

Module E.

#[universes(polymorphic=yes)]
Definition t@{u} (A : Type@{u}) : Type@{u} := A -> Prop.

#[universes(polymorphic=yes)]
Definition In@{u} {A : Type@{u}} (x : A) (X : t@{u} A) : Prop := X x.

#[universes(polymorphic=yes)]
Definition subset@{u} {A : Type@{u}} (X1 : t@{u} A) (X2 : t@{u} A) : Prop :=
  forall x, In@{u} x X1 -> In@{u} x X2.

#[local] Infix "\in" := In : type_scope.

#[local] Infix "\subseteq" := subset : type_scope.

#[global]
Instance ensemble_isPoset {A : Type} : isPoset (E.t A) :=
  let POSET : isPoset (E.t A) := pi_isPoset (fun _ : A => Prop_isPoset) in
  {|
    leProp := subset;
    Poset_isSetoid := {| eqProp lhs rhs := forall x, x \in lhs <-> x \in rhs; eqProp_Equivalence := POSET.(Poset_isSetoid).(eqProp_Equivalence) |};
    leProp_PreOrder := POSET.(leProp_PreOrder);
    leProp_PartialOrder := POSET.(leProp_PartialOrder);
  |}.

#[global]
Instance t_isSetoid1 : isSetoid1 E.t :=
  fun X : Type => fun _ : isSetoid X => (@ensemble_isPoset X).(Poset_isSetoid).

#[global]
Instance t_isMonad : isMonad E.t :=
  { bind {A : Type} {B : Type} (m : E.t A) (k : A -> E.t B) := fun z => exists x, x \in m /\ z \in k x
  ; pure {A : Type} (x : A) := fun z => x = z
  }.

#[global]
Instance t_satisfiesMonadLaws
  : @MonadLaws E.t t_isSetoid1 t_isMonad.
Proof.
  split; cbv; ii; firstorder congruence.
Qed.

Lemma liftM2_spec {A : Type} {B : Type} {C : Type} (f : A -> B -> C) (X : E.t A) (Y : E.t B)
  : forall z, z \in liftM2 f X Y <-> exists x, x \in X /\ exists y, y \in Y /\ z = f x y.
Proof.
  cbv; firstorder.
Qed.

(** Section SET_CONSTRUCTIONS. *)

Inductive unions {A : Type} (Xs : E.t (E.t A)) : E.t A :=
  | In_unions x X
    (H_in : x \in X)
    (H_IN : X \in Xs)
    : x \in unions Xs.

Inductive union {A : Type} (X1 : E.t A) (X2 : E.t A) : E.t A :=
  | In_union_l x
    (H_inl : x \in X1)
    : x \in union X1 X2
  | In_union_r x
    (H_inr : x \in X2)
    : x \in union X1 X2.

Inductive empty {A : Type} : E.t A :=.

Inductive intersection {A : Type} (X1 : E.t A) (X2 : E.t A) : E.t A :=
  | In_intersection x
    (H_IN1 : x \in X1)
    (H_IN2 : x \in X2)
    : x \in intersection X1 X2.

Inductive singleton {A : Type} (x : A) : E.t A :=
  | In_singleton
    : x \in singleton x.

#[universes(polymorphic=yes)]
Definition fromList@{u} {A : Type@{u}} (xs : list A) : E.t@{u} A :=
  fun x => List.In x xs.

#[universes(polymorphic=yes)]
Definition full@{u} {A : Type@{u}} : E.t@{u} A :=
  fun x => True.

#[universes(polymorphic=yes)]
Definition insert@{u} {A : Type@{u}} (x1 : A) (X2 : E.t@{u} A) : E.t@{u} A :=
  fun x => x = x1 \/ x \in X2.

(** End SET_CONSTRUCTIONS. *)

End E.

Notation ensemble := E.t.

#[local] Infix "\in" := E.In : type_scope.

#[local] Infix "\subseteq" := E.subset : type_scope.

Definition eqProp_cl {A : Type} `{SETOID : isSetoid A} (X : ensemble A) : ensemble A :=
  fun z => exists x, z == x /\ x \in X.

#[global]
Instance eqProp_cl_isClosureOperator {A : Type} `{SETOID : isSetoid A}
  : isClosureOperator eqProp_cl.
Proof.
  rewrite isClosureOperator_iff. intros x y. split; intros LE.
  - intros a [b [EQ IN]]. pose proof (LE b IN) as [c [EQ' IN']].
    exists c. split; trivial. etransitivity; eauto.
  - intros a IN. eapply LE. exists a. split; trivial. reflexivity.
Qed.

Definition isCompatibleWith_eqProp {A : Type} `{SETOID : isSetoid A} (P : A -> Prop) : Prop :=
  forall x, P x -> forall y, x == y -> P y.

Lemma eqProp_cl_isCompatibleWith_eqProp {A : Type} `{SETOID : isSetoid A} (X : ensemble A)
  : isCompatibleWith_eqProp (eqProp_cl X).
Proof.
  intros x [a [EQ IN]] y EQ'. exists a. split. rewrite <- EQ'. exact EQ. exact IN.
Qed.
