Require Export PnV.Prelude.Notations.
Require Export PnV.Prelude.SfLib.
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

Create HintDb simplication_hints.

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

Class isSetoid1 (F : Type -> Type) : Type :=
  liftSetoid1 (X : Type) `(SETOID : isSetoid X) : isSetoid (F X).

Definition mkSetoid_from_eq {A : Type} : isSetoid A :=
  {| eqProp := @eq A; eqProp_Equivalence := eq_equivalence |}.

#[global]
Instance fromSetoid1 {F : Type -> Type} {A : Type} `(SETOID1 : isSetoid1 F) : isSetoid (F A) :=
  liftSetoid1 A mkSetoid_from_eq.

#[universes(polymorphic=yes)]
Definition binary_relation_on_image@{u_A u_B} {A : Type@{u_A}} {B : Type@{u_B}} (R : B -> B -> Prop) (f : A -> B) lhs rhs : Prop :=
  R (f lhs) (f rhs).

#[local]
Instance relation_on_image_liftsEquivalence {A : Type} {B : Type} {eqProp : B -> B -> Prop}
  (isEquivalence : Equivalence eqProp)
  : forall f : A -> B, Equivalence (binary_relation_on_image eqProp f).
Proof.
  intros f. constructor.
  - intros x1. exact (Equivalence_Reflexive (f x1)).
  - intros x1 x2 H_1EQ2. exact (Equivalence_Symmetric (f x1) (f x2) H_1EQ2).
  - intros x1 x2 x3 H_1EQ2 H_2EQ3. exact (Equivalence_Transitive (f x1) (f x2) (f x3) H_1EQ2 H_2EQ3).
Defined.

#[local]
Instance relation_on_image_liftsPreOrder {A : Type} {B : Type} {leProp : B -> B -> Prop}
  (isPreOrder : PreOrder leProp)
  : forall f : A -> B, PreOrder (binary_relation_on_image leProp f).
Proof.
  intros f. constructor.
  - intros x1. exact (PreOrder_Reflexive (f x1)).
  - intros x1 x2 x3 H_1LE2 H_2LE3. exact (PreOrder_Transitive (f x1) (f x2) (f x3) H_1LE2 H_2LE3).
Defined.

#[local]
Instance relation_on_image_liftsPartialOrder {A : Type} {B : Type} {eqProp : B -> B -> Prop} {leProp : B -> B -> Prop}
  `{isEquivalence : @Equivalence B eqProp}
  `{isPreOrder : @PreOrder B leProp}
  (isPartialOrder : PartialOrder eqProp leProp)
  : forall f : A -> B, PartialOrder (binary_relation_on_image eqProp f) (binary_relation_on_image leProp f).
Proof.
  intros f x1 x2. constructor.
  - intros H_EQ. constructor.
    + exact (proj1 (proj1 (partial_order_equivalence (f x1) (f x2)) H_EQ)).
    + exact (proj2 (proj1 (partial_order_equivalence (f x1) (f x2)) H_EQ)).
  - intros H_EQ. apply (proj2 (partial_order_equivalence (f x1) (f x2))). constructor.
    + exact (proj1 H_EQ).
    + exact (proj2 H_EQ).
Defined.

Lemma relation_on_image_liftsWellFounded {A : Type} {B : Type} (R : B -> B -> Prop) (f : A -> B)
  (WF : well_founded R)
  : well_founded (binary_relation_on_image R f).
Proof.
  intros x. remember (f x) as y eqn: y_eq_f_x.
  revert x y_eq_f_x. induction (WF y) as [y' _ IH].
  intros x' hyp_eq. econstructor. intros x f_x_R_f_x'.
  subst y'. eapply IH; [exact f_x_R_f_x' | reflexivity].
Defined.

(** Section FUNCTOR. *)

Class isFunctor (F : Type -> Type) : Type :=
  fmap (A : Type) (B : Type) (f : A -> B) : F A -> F B.

#[global] Arguments fmap {F} {isFunctor} {A} {B} f.

Class FunctorLaws (F : Type -> Type) `{SETOID1 : isSetoid1 F} `{FUNCTOR : isFunctor F} : Prop :=
  { fmap_eqPropCompatible1 {A : Type} {B : Type} (f : A -> B) :: eqPropCompatible1 (fmap f)
  ; fmap_compose {A : Type} {B : Type} {C : Type} (f : A -> B) (g : B -> C)
    : fmap (@compose A B C g f) == compose (fmap g) (fmap f)
  ; fmap_id {A : Type}
    : fmap (@id A) == id
  ; fmap_lifts_ext_eq {A : Type} {B : Type} (f1 : A -> B) (f2 : A -> B)
    (f_EQ : forall x, f1 x = f2 x)
    : fmap f1 == fmap f2
  }.

#[global]
Add Parametric Morphism {F : Type -> Type} `{SETOID1 : isSetoid1 F} `{FUNCTOR : isFunctor F} (FUNCTOR_LAWS : FunctorLaws F) (A : Type) (B : Type)
  : (@fmap F FUNCTOR A B) with signature (eqProp (isSetoid := pi_isSetoid (fun _ : A => @mkSetoid_from_eq B)) ==> eqProp ==> eqProp)
  as fmap_compatWith_eqProp.
Proof.
  intros f1 f2 f_EQ x1 x2 x_EQ. rewrite x_EQ. eapply fmap_lifts_ext_eq. exact f_EQ.
Qed.

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
  - unfold fmap. unfold mkFunctorFromMonad. rewrite x_EQ. reflexivity.
  - unfold compose. unfold fmap. unfold mkFunctorFromMonad. symmetry.
    rewrite <- bind_assoc. eapply bind_compatWith_eqProp_r. intros i.
    rewrite bind_pure_l. reflexivity.
  - unfold id. unfold fmap. unfold mkFunctorFromMonad.
    rewrite bind_pure_r. reflexivity.
  - unfold fmap. unfold mkFunctorFromMonad. eapply bind_compatWith_eqProp_r.
    intros i. rewrite f_EQ. reflexivity.
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

#[local] Hint Constructors unions : core.

Lemma in_unions_iff (A : Type) Xs
  : forall z, z \in @unions A Xs <-> (exists X, z \in X /\ X \in Xs).
Proof.
  intros z; split; [intros [? ? ? ?] | intros [? [? ?]]]; eauto.
Qed.

#[global] Hint Rewrite in_unions_iff : simplication_hints.

#[global]
Instance unions_eqPropCompatible1 (A : Type)
  : eqPropCompatible1 (@unions A).
Proof.
  ii. do 2 rewrite in_unions_iff. now firstorder.
Qed.

Inductive union {A : Type} (X1 : E.t A) (X2 : E.t A) : E.t A :=
  | In_union_l x
    (H_inl : x \in X1)
    : x \in union X1 X2
  | In_union_r x
    (H_inr : x \in X2)
    : x \in union X1 X2.

#[local] Hint Constructors union : core.

Lemma in_union_iff (A : Type) X1 X2
  : forall z, z \in @union A X1 X2 <-> (z \in X1 \/ z \in X2).
Proof.
  intros z; split; [intros [? ? | ? ?] | intros [? | ?]]; eauto.
Qed.

#[global] Hint Rewrite in_union_iff : simplication_hints.

#[global]
Instance union_eqPropCompatible2 (A : Type)
  : eqPropCompatible2 (@union A).
Proof.
  ii. do 2 rewrite in_union_iff. now firstorder.
Qed.

Inductive empty {A : Type} : E.t A :=.

#[local] Hint Constructors empty : core.

Lemma in_empty_iff (A : Type)
  : forall z, z \in @empty A <-> False.
Proof.
  intros z; split; [intros [] | intros []]; eauto.
Qed.

#[global] Hint Rewrite in_empty_iff : simplication_hints.

Inductive intersection {A : Type} (X1 : E.t A) (X2 : E.t A) : E.t A :=
  | In_intersection x
    (H_IN1 : x \in X1)
    (H_IN2 : x \in X2)
    : x \in intersection X1 X2.

#[local] Hint Constructors intersection : core.

Lemma in_intersection_iff (A : Type) X1 X2
  : forall z, z \in @intersection A X1 X2 <-> (z \in X1 /\ z \in X2).
Proof.
  intros z; split; [intros [? ? ?] | intros [? ?]]; eauto.
Qed.

#[global] Hint Rewrite in_intersection_iff : simplication_hints.

#[global]
Instance intersection_eqPropCompatible2 (A : Type)
  : eqPropCompatible2 (@intersection A).
Proof.
  ii. do 2 rewrite in_intersection_iff. now firstorder.
Qed.

Inductive singleton {A : Type} (x : A) : E.t A :=
  | In_singleton
    : x \in singleton x.

#[local] Hint Constructors singleton : core.

Lemma in_singleton_iff (A : Type) x
  : forall z, z \in @singleton A x <-> (z = x).
Proof.
  intros z; split; [intros [] | intros ->]; eauto.
Qed.

#[global] Hint Rewrite in_singleton_iff : simplication_hints.

#[universes(polymorphic=yes)]
Definition fromList@{u} {A : Type@{u}} (xs : list A) : E.t@{u} A :=
  fun x => List.In x xs.

#[global] Hint Unfold fromList : simplication_hints.

#[universes(polymorphic=yes)]
Definition full@{u} {A : Type@{u}} : E.t@{u} A :=
  fun x => True.

#[global] Hint Unfold full : simplication_hints.

#[universes(polymorphic=yes)]
Definition insert@{u} {A : Type@{u}} (x1 : A) (X2 : E.t@{u} A) : E.t@{u} A :=
  fun x => x = x1 \/ x \in X2.

#[global] Hint Unfold insert : simplication_hints.

(** End SET_CONSTRUCTIONS. *)

End E.

Notation ensemble := E.t.

#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "\subseteq" := E.subset : type_scope.

Class isAssociative {A : Type} `{SETOID : isSetoid A} (f : A -> A -> A) : Prop :=
  assoc x y z : f x (f y z) == f (f x y) z.

Class isCommutative {A : Type} `{SETOID : isSetoid A} (f : A -> A -> A) : Prop :=
  comm x y : f x y == f y x.

Class isClosureOperator {A : Type} `{POSET : isPoset A} (cl : A -> A) : Prop :=
  { cl_op_extensive : forall x, x =< cl x
  ; cl_op_idempotent : forall x, cl (cl x) == cl x
  ; cl_op_monotonic :: isMonotonic1 cl
  }.

Lemma isClosureOperator_iff {A : Type} `{POSET : isPoset A} (cl : A -> A)
  : isClosureOperator cl <-> (forall x, forall y, x =< cl y <-> cl x =< cl y).
Proof.
  split.
  - intros [EXTENSIVE IDEMPOTENT MONOTONIC] x y. split; intros LE.
    + rewrite <- IDEMPOTENT with (x := y). eapply MONOTONIC. exact LE.
    + transitivity (cl x). eapply EXTENSIVE. exact LE.
  - intros IFF. split; ii.
    + rewrite -> IFF. reflexivity.
    + eapply leProp_antisymmetry.
      * rewrite <- IFF. reflexivity.
      * rewrite -> IFF. reflexivity.
    + rewrite <- IFF. transitivity x2. exact x_LE. rewrite -> IFF. reflexivity.
Qed.

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

Module B.

#[local] Open Scope program_scope.

#[universes(polymorphic=yes)]
Definition dollar@{u v} {A : Type@{u}} {B : Type@{v}} (f : A -> B) (x : A) : B := f x.

#[local] Infix "$" := dollar.
#[local] Infix ">>=" := bind.

Definition kcompose {M} {MONAD : isMonad M} {A} {B} {C} (k1 : A -> M B) (k2 : B -> M C) : A -> M C :=
  fun x => k1 x >>= k2.

#[local] Infix ">=>" := kcompose : program_scope.

Record stateT (S : Type) (M : Type -> Type) (X : Type) : Type :=
  StateT { runStateT : S -> M (X * S)%type }.

#[global] Arguments StateT {S} {M} {X}.
#[global] Arguments runStateT {S} {M} {X}.

#[global]
Instance stateT_isMonad {S} {M} `(M_isMonad : isMonad M) : isMonad (B.stateT S M) :=
  { pure {A} (x : A) := B.StateT $ curry pure x
  ; bind {A} {B} (m : B.stateT S M A) (k : A -> B.stateT S M B) := B.StateT $ B.runStateT m >=> uncurry (B.runStateT ∘ k)
  }.

Definition stateT_isSetoid {S} {M} `{SETOID1 : isSetoid1 M} X : isSetoid (B.stateT S M X) :=
  {|
    eqProp lhs rhs := forall s, B.runStateT lhs s == B.runStateT rhs s;
    eqProp_Equivalence := relation_on_image_liftsEquivalence (pi_isSetoid (fun _ => fromSetoid1 SETOID1)).(eqProp_Equivalence) B.runStateT;
  |}.

#[local]
Instance stateT_isSetoid1 {S} {M} `{SETOID1 : isSetoid1 M} : isSetoid1 (B.stateT S M) :=
  fun X : Type => fun _ : isSetoid X => @stateT_isSetoid S M SETOID1 X.

#[local]
Instance stateT_satisfiesMonadLaws {S} {M} `{SETOID1 : isSetoid1 M} `{MONAD : isMonad M}
  `(MONAD_LAWS : @MonadLaws M SETOID1 MONAD)
  : MonadLaws (B.stateT S M).
Proof.
  split; i.
  - destruct m1 as [m1], m2 as [m2]; simpl in *. intros s. eapply bind_compatWith_eqProp_l. exact (m_EQ s).
  - destruct m as [m]; simpl in *. intros s. eapply bind_compatWith_eqProp_r. intros [x s']. exact (k_EQ x s').
  - destruct m as [m]; simpl in *. intros s. unfold kcompose. rewrite <- bind_assoc.
    eapply bind_compatWith_eqProp_r. intros [x s']. reflexivity.
  - destruct (k x) as [m] eqn: H_OBS. simpl in *. intros s. unfold kcompose. unfold curry. rewrite bind_pure_l. simpl.
    unfold compose. rewrite H_OBS. reflexivity.
  - destruct m as [m]; simpl in *. intros s. unfold kcompose. rewrite <- bind_pure_r with (m := m s) at 2.
    eapply bind_compatWith_eqProp_r. intros [x s']. reflexivity.
Qed.

Lemma Some_ne_None {A : Type} (x : A)
  : Some x <> None.
Proof.
  assert (TRUE : option_rect (fun _ : option A => Prop) (fun _ : A => True) (False) (Some x)) by exact I.
  intros EQ. rewrite EQ in TRUE. exact TRUE.
Defined.

Definition maybe {A : Type} {B : Type} (d : B) (f : A -> B) (m : option A) : B :=
  match m with
  | None => d
  | Some x => f x
  end.

Definition either {A : Type} {B : Type} {C : Type} (f : A -> C) (g : B -> C) (z : A + B) : C :=
  match z with
  | inl x => f x
  | inr y => g y
  end.

Definition Some_dec {A : Type} (x : option A)
  : { x' : A | x = Some x' } + { x = None }.
Proof.
  destruct x as [x' | ].
  - left. exists x'. reflexivity.
  - right. reflexivity.
Defined.

End B.

Infix "$" := B.dollar.
Infix ">>=" := bind.
Infix ">=>" := B.kcompose : program_scope.

Class hasEqDec (A : Type) : Type :=
  eq_dec (x : A) (y : A) : {x = y} + {x <> y}.

#[global]
Instance nat_hasEqDec : hasEqDec nat :=
  Nat.eq_dec.

#[global]
Instance pair_hasEqdec {A : Type} {B : Type}
  `(A_hasEqDec : hasEqDec A)
  `(B_hasEqDec : hasEqDec B)
  : hasEqDec (A * B).
Proof.
  red in A_hasEqDec, B_hasEqDec. red. decide equality.
Defined.

#[global]
Instance option_hasEqDec {A : Type}
  `(EQ_DEC : hasEqDec A)
  : hasEqDec (option A).
Proof.
  exact (fun x : option A => fun y : option A =>
    match x as a, y as b return {a = b} + {a <> b} with
    | None, None => left eq_refl
    | None, Some y' => right (fun EQ : None = Some y' => B.Some_ne_None y' (Equivalence_Symmetric None (Some y') EQ))
    | Some x', None => right (fun EQ : Some x' = None => B.Some_ne_None x' EQ)
    | Some x', Some y' =>
      match EQ_DEC x' y' with
      | left EQ => left (f_equal (@Some A) EQ)
      | right NE => right (fun EQ : Some x' = Some y' => NE (f_equal (B.maybe x' id) EQ))
      end
    end
  ).
Defined.

Class Similarity (A : Type) (B : Type) : Type :=
  is_similar_to (x : A) (y : B) : Prop.

#[global]
Instance forall_liftsSimilarity {I : Type} {A : I -> Type} {B : I -> Type} (SIMILARITY : forall i, Similarity (A i) (B i)) : Similarity (forall i, A i) (forall i, B i) :=
  fun f : forall i, A i => fun g : forall i, B i => forall i, is_similar_to (f i) (g i).

Class isEnumerable (A : Type) : Type :=
  { enum : nat -> A
  ; enum_spec : forall x : A, { n : nat | enum n = x }
  }.

Lemma enum_spec_injective {A : Type} `{ENUMERABLE : isEnumerable A}
  (inj := fun x : A => proj1_sig (enum_spec x))
  : forall x1 : A, forall x2 : A, inj x1 = inj x2 -> x1 = x2.
Proof.
  unfold inj. intros x1 x2 inj_EQ.
  destruct (enum_spec x1) as [n1 EQ1], (enum_spec x2) as [n2 EQ2].
  simpl in *. congruence.
Qed.

Class isCountable (A : Type) : Type :=
  { encode : A -> nat
  ; decode : nat -> option A
  ; decode_encode (x : A)
    : decode (encode x) = Some x 
  }.

#[local]
Instance isCountable_if_isEnumerable {A : Type} `(ENUMERABLE : isEnumerable A) : isCountable A :=
  { encode (x : A) := proj1_sig (enum_spec x)
  ; decode (n : nat) := Some (enum n)
  ; decode_encode (x : A) := f_equal (@Some A) (proj2_sig (enum_spec x))
  }.

Module L.

Include Coq.Lists.List.

Lemma in_remove_iff {A : Type} `(EQ_DEC : hasEqDec A) (x1 : A) (xs2 : list A)
  : forall z, In z (remove Prelude.eq_dec x1 xs2) <-> (In z xs2 /\ z <> x1).
Proof.
  i; split.
  { intros H_IN. eapply in_remove. exact H_IN. }
  { intros [H_IN H_NE]. eapply in_in_remove; [exact H_NE | exact H_IN]. }
Qed.

Lemma rev_inj {A : Type} (xs1 : list A) (xs2 : list A)
  (rev_EQ : rev xs1 = rev xs2)
  : xs1 = xs2.
Proof.
  rewrite <- rev_involutive with (l := xs1).
  rewrite <- rev_involutive with (l := xs2).
  now f_equal.
Qed.

Lemma list_rev_dual {A : Type} (phi : list A -> Prop)
  (H_rev : forall n, phi (L.rev n))
  : forall n, phi n.
Proof.
  intros n. induction n as [ | d n _] using @List.rev_ind.
  - eapply H_rev with (n := []%list).
  - rewrite <- List.rev_involutive with (l := n).
    eapply H_rev with (n := (d :: List.rev n)%list).
Qed.

Lemma list_rev_rect {A : Type} (P : list A -> Type)
  (NIL : P [])
  (TAIL : forall x, forall xs, P xs -> P (xs ++ [x]))
  : forall xs, P xs.
Proof.
  intros xs'. rewrite <- rev_involutive with (l := xs').
  generalize (rev xs') as xs. clear xs'.
  induction xs as [ | x xs IH]; simpl.
  - exact NIL.
  - eapply TAIL. exact IH.
Qed.

Lemma last_cons {A : Type} (x0 : A) (x1 : A) (xs : list A)
  : last (x0 :: xs) x1 = last xs x0.
Proof.
  symmetry. revert x0 x1. induction xs as [ | x xs IH]; simpl; i.
  - reflexivity.
  - destruct xs as [ | x' xs'].
    + reflexivity.
    + erewrite IH with (x1 := x1). reflexivity.
Qed.

Fixpoint mk_edge_seq {V : Type} (v : V) (vs : list V) : list (V * V) :=
  match vs with
  | [] => []
  | v' :: vs' => (v, v') :: mk_edge_seq v' vs'
  end.

Lemma mk_edge_seq_last {V : Type} (v0 : V) (v' : V) (vs : list V)
  : mk_edge_seq v0 (vs ++ [v']) = mk_edge_seq v0 vs ++ [(last vs v0, v')].
Proof.
  revert v0 v'. induction vs as [ | v vs IH]; i.
  - simpl. reflexivity.
  - erewrite -> last_cons. simpl. f_equal. eauto.
Qed.

Lemma in_mk_edge_seq_inv {V : Type} (v0 : V) (v1 : V) (vs : list V)
  (IN : In (v0, v1) (mk_edge_seq v1 vs))
  : In v1 vs.
Proof.
  revert v0 v1 IN. induction vs as [ | v vs IH] using List.rev_ind; simpl; i.
  - exact IN.
  - rewrite in_app_iff. rewrite mk_edge_seq_last in IN.
    rewrite in_app_iff in IN. destruct IN as [IN | [EQ | []]].
    + left. eapply IH; exact IN.
    + inv EQ. right. repeat constructor.
Qed.

Lemma no_dup_mk_edge_seq {V : Type} (v : V) (vs : list V)
  (NO_DUP : NoDup vs)
  : NoDup (mk_edge_seq v vs).
Proof.
  revert v. induction NO_DUP as [ | v vs NOT_IN NO_DUP IH].
  - econstructor 1.
  - simpl. econstructor 2.
    + intros CONTRA. apply in_mk_edge_seq_inv in CONTRA. contradiction.
    + eapply IH.
Qed.

Definition ext_eq_as_finset {A : Type} (xs1 : list A) (xs2 : list A) : Prop :=
  forall x : A, L.In x xs1 <-> L.In x xs2.

Fixpoint lookup {A : Type} {B : Type} {EQ_DEC : hasEqDec A} (x : A) (zs : list (A * B)) : option B :=
  match zs with
  | [] => None
  | (x', y) :: zs' => if eq_dec x x' then Some y else lookup x zs'
  end.

Notation is_finsubset_of xs X := (forall x, L.In x xs -> x \in X).

Notation is_listrep_of xs X := (forall x, L.In x xs <-> x \in X).

End L.
