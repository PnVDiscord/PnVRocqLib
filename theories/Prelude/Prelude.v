Require Export PnV.Prelude.SfLib.
Require Export PnV.Prelude.Notations.
Require Export Stdlib.Arith.Compare_dec.
Require Export Stdlib.Arith.PeanoNat.
Require Export Stdlib.Arith.Wf_nat.
Require Export Stdlib.Bool.Bool.
Require Export Stdlib.Classes.RelationClasses.
Require Import Stdlib.Strings.String.
Require Export Stdlib.Lists.List.
Require Export Stdlib.micromega.Lia.
Require Export Stdlib.Program.Basics.
Require Export Stdlib.Program.Utils.
Require Export Stdlib.Relations.Relation_Definitions.
Require Export Stdlib.Relations.Relation_Operators.
Require Export Stdlib.Setoids.Setoid.

#[local] Obligation Tactic := idtac.

#[global] Create HintDb simplication_hints.

#[global] Hint Rewrite forallb_app orb_true_iff orb_false_iff andb_true_iff andb_false_iff negb_true_iff negb_false_iff Nat.eqb_eq Nat.eqb_neq not_true_iff_false not_false_iff_true : simplication_hints.

Tactic Notation "rewrite!" :=
  autorewrite with simplication_hints in *.

Tactic Notation "gen" uconstr( t ) "as" ident( X ) :=
  eset (X := t); clearbody X; revert X.

Universe U_cosmos.

Class isGood (A : Type@{U_cosmos}) : Type@{U_cosmos} :=
  is_good : A -> Prop.

Definition addComment {A : Type@{U_cosmos}} (comment : string) (obj : A) : A :=
  obj.

Class hasComment (A : Type@{U_cosmos}) : Set :=
  comment : string.

Universe U_discourse.

Constraint U_discourse < U_cosmos.

Universe U_small.

Constraint U_small < U_discourse.

Ltac obs_eqb n m :=
  let H_OBS := fresh "H_OBS" in destruct (Nat.eqb n m) as [ | ] eqn: H_OBS; [rewrite Nat.eqb_eq in H_OBS | rewrite Nat.eqb_neq in H_OBS].

Ltac property X :=
  eapply (proj2_sig X).

#[universes(polymorphic=yes)]
Definition reify@{u v} {A : Type@{u}} {B : Type@{v}} {P : A -> B -> Prop} (f : forall x : A, { y : B | P x y }) : { f : A -> B | forall x, P x (f x) } :=
  @exist (A -> B) (fun f => forall x, P x (f x)) (fun x => proj1_sig (f x)) (fun x => proj2_sig (f x)).

#[universes(polymorphic=yes)]
Definition reify_lemma@{u v} {A : Type@{u}} {B : Type@{v}} {P : A -> B -> Prop} (f : forall x : A, { y : B | P x y }) : forall x, P x (proj1_sig (@reify@{u v} A B P f) x) :=
  proj2_sig (@reify@{u v} A B P f).

(** Section SETOID. *)

#[universes(template)]
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
Defined.

#[program]
Definition mkSetoidFromPreOrder {A : Type} {leProp : A -> A -> Prop} `(leProp_PreOrder : @PreOrder A leProp) : isSetoid A :=
  {| eqProp (x : A) (y : A) := leProp x y /\ leProp y x |}.
Next Obligation.
  split; ii.
  - exact (conj (@PreOrder_Reflexive A leProp leProp_PreOrder x) (@PreOrder_Reflexive A leProp leProp_PreOrder x)).
  - exact (conj (proj2 H) (proj1 H)).
  - exact (conj (@PreOrder_Transitive A leProp leProp_PreOrder x y z (proj1 H) (proj1 H0)) (@PreOrder_Transitive A leProp leProp_PreOrder z y x (proj2 H0) (proj2 H))).
Defined.

Lemma mkSetoidFromPreOrder_good {A : Type} {leProp : A -> A -> Prop} `(leProp_PreOrder : @PreOrder A leProp)
  (SETOID := mkSetoidFromPreOrder leProp_PreOrder)
  : PartialOrder SETOID.(eqProp) leProp.
Proof.
  intros x y; split; exact (fun H => H).
Defined.

#[program]
Definition directProduct_of_two_Setoids {A : Type} {B : Type} (A_isSetoid : isSetoid A) (B_isSetoid : isSetoid B) : isSetoid (A * B) :=
  {| eqProp lhs rhs := fst lhs == fst rhs /\ snd lhs == snd rhs |}.
Next Obligation.
  ii. split.
  - intros p1. split; reflexivity.
  - intros p1 p2 EQ. split; symmetry. exact (proj1 EQ). exact (proj2 EQ).
  - intros p1 p2 p3 EQ EQ'. split; etransitivity. exact (proj1 EQ). exact (proj1 EQ'). exact (proj2 EQ). exact (proj2 EQ').
Defined.

Inductive option_eqProp {A : Type} (eqProp : A -> A -> Prop) : forall lhs : option A, forall rhs : option A, Prop :=
  | option_eqProp_None
    : @option_eqProp A eqProp (@None A) (@None A)
  | option_eqProp_Some (x : A) (y : A)
    (x_eq_y : eqProp x y)
    : @option_eqProp A eqProp (@Some A x) (@Some A y).

#[global]
Instance option_eqProp_Equivalence {A : Type} (eqProp : A -> A -> Prop)
  (eqProp_Equivalence : Equivalence eqProp)
  : Equivalence (option_eqProp eqProp).
Proof with eauto.
  split.
  - intros [x | ]; econs. reflexivity...
  - intros ? ? [ | x y x_eq_y]; econs. symmetry...
  - intros ? ? ? [ | x y x_eq_y] EQ; inv EQ; econs. etransitivity...
Qed.

#[global, program]
Instance option_isSetoid {A : Type} (SETOID : isSetoid A) : isSetoid (option A) :=
  { eqProp := option_eqProp eqProp
  ; eqProp_Equivalence := option_eqProp_Equivalence eqProp eqProp_Equivalence
  }.

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
  (COMPAT : @eqPropCompatible1 A B A_isSetoid B_isSetoid f)
  : f with signature (eqProp ==> eqProp)
  as compatibleWith_eqProp_1'.
Proof.
  intros x1 x2 x_EQ. exact (compatibleWith_eqProp_1 x1 x2 x_EQ).
Defined.

#[global]
Add Parametric Morphism {A : Type} {B : Type} {C : Type} `{A_isSetoid : isSetoid A} `{B_isSetoid : isSetoid B} `{C_isSetoid : isSetoid C} (f : A -> B -> C)
  (COMPAT : @eqPropCompatible2 A B C A_isSetoid B_isSetoid C_isSetoid f)
  : f with signature (eqProp ==> eqProp ==> eqProp)
  as compatibleWith_eqProp_2'.
Proof.
  intros x1 x2 x_EQ y1 y2 y_EQ. exact (compatibleWith_eqProp_2 x1 x2 y1 y2 x_EQ y_EQ).
Defined.

(** End SETOID. *)

(** Section PROSET. *)

#[universes(template)]
Class isProset (A : Type) : Type :=
  { leProp (lhs : A) (rhs : A) : Prop
  ; Proset_isSetoid :: isSetoid A
  ; leProp_PreOrder :: PreOrder leProp
  ; leProp_PartialOrder :: PartialOrder eqProp leProp
  }.

Infix "=<" := leProp : type_scope.

Definition dualPreOrder {A : Type} {ge : A -> A -> Prop} (gePreOrder : PreOrder ge) : PreOrder (flip ge) :=
  {|
    PreOrder_Reflexive (x : A) := @PreOrder_Reflexive A ge gePreOrder x;
    PreOrder_Transitive (x : A) (y : A) (z : A) := flip (@PreOrder_Transitive A ge gePreOrder z y x);
  |}.

Definition Prop_isProset : isProset Prop :=
  let impl_PreOrder : @PreOrder Prop impl := dualPreOrder {| PreOrder_Reflexive (A : Prop) := @id A; PreOrder_Transitive (A : Prop) (B : Prop) (C : Prop) := @compose C B A; |} in
  {|
    leProp P Q := P -> Q;
    Proset_isSetoid := mkSetoidFromPreOrder impl_PreOrder;
    leProp_PreOrder := impl_PreOrder;
    leProp_PartialOrder := mkSetoidFromPreOrder_good impl_PreOrder;
  |}.

#[program]
Definition pi_isProset {A : Type} {B : A -> Type} `(PROSET : forall x : A, isProset (B x)) : isProset (forall x : A, B x) :=
  {| leProp f g := forall x, f x =< g x; Proset_isSetoid := pi_isSetoid (fun x : A => (PROSET x).(Proset_isSetoid)) |}.
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

Lemma leProp_refl {A : Type} `{A_isProset : isProset A}
  : forall x : A, x =< x.
Proof.
  eapply PreOrder_Reflexive.
Defined.

Lemma leProp_trans {A : Type} `{A_isProset : isProset A}
  : forall x : A, forall y : A, forall z : A, x =< y -> y =< z -> x =< z.
Proof.
  eapply PreOrder_Transitive.
Defined.

Lemma leProp_antisymmetry {A : Type} `{A_isProset : isProset A}
  : forall x : A, forall y : A, x =< y -> y =< x -> x == y.
Proof.
  intros x y x_le_y y_le_x. exact (proj2 (leProp_PartialOrder x y) (conj x_le_y y_le_x)).
Defined.

Lemma eqProp_implies_leProp {A : Type} `{A_isProset : isProset A}
  : forall x : A, forall y : A, x == y -> x =< y.
Proof.
  intros x y x_eq_y. exact (proj1 (proj1 (leProp_PartialOrder x y) x_eq_y)).
Defined.

Class isMonotonic1 {A : Type} {B : Type} `{A_isProset : isProset A} `{B_isProset : isProset B} (f : A -> B) : Prop :=
  compatibleWith_leProp_1 x1 x2 (x_LE : x1 =< x2) : f x1 =< f x2.

Class isMonotonic2 {A : Type} {B : Type} {C : Type} `{A_isProset : isProset A} `{B_isProset : isProset B} `{C_isProset : isProset C} (f : A -> B -> C) : Prop :=
  compatibleWith_leProp_2 x1 x2 y1 y2 (x_LE : x1 =< x2) (y_LE : y1 =< y2) : f x1 y1 =< f x2 y2.

#[global]
Add Parametric Morphism {A : Type} {B : Type} `{A_isProset : isProset A} `{B_isProset : isProset B} (f : A -> B)
  (MONOTONIC : @isMonotonic1 A B A_isProset B_isProset f)
  : f with signature (eqProp ==> eqProp)
  as isMonotonic1_compatWith_eqProp.
Proof.
  ii. eapply leProp_antisymmetry.
  - eapply MONOTONIC. eapply eqProp_implies_leProp. exact H.
  - eapply MONOTONIC. eapply eqProp_implies_leProp. symmetry. exact H.
Defined.

#[global]
Add Parametric Morphism {A : Type} {B : Type} `{A_isProset : isProset A} `{B_isProset : isProset B} (f : A -> B)
  (MONOTONIC : @isMonotonic1 A B A_isProset B_isProset f)
  : f with signature (leProp ==> leProp)
  as compatibleWith_leProp_1'.
Proof.
  intros x1 x2 x_LE. exact (compatibleWith_leProp_1 x1 x2 x_LE).
Defined.

#[global]
Add Parametric Morphism {A : Type} {B : Type} {C : Type} `{A_isProset : isProset A} `{B_isProset : isProset B} `{C_isProset : isProset C} (f : A -> B -> C)
  (MONOTONIC : @isMonotonic2 A B C A_isProset B_isProset C_isProset f)
  : f with signature (eqProp ==> eqProp ==> eqProp)
  as isMonotonic2_compatWith_eqProp.
Proof.
  ii. eapply leProp_antisymmetry.
  - eapply MONOTONIC; eapply eqProp_implies_leProp; assumption.
  - eapply MONOTONIC; eapply eqProp_implies_leProp; symmetry; assumption.
Defined.

#[global]
Add Parametric Morphism {A : Type} {B : Type} {C : Type} `{A_isProset : isProset A} `{B_isProset : isProset B} `{C_isProset : isProset C} (f : A -> B -> C)
  (MONOTONIC : @isMonotonic2 A B C A_isProset B_isProset C_isProset f)
  : f with signature (leProp ==> leProp ==> leProp)
  as compatibleWith_leProp_2'.
Proof.
  intros x1 x2 x_LE y1 y2 y_LE. exact (compatibleWith_leProp_2 x1 x2 y1 y2 x_LE y_LE).
Defined.

#[global]
Add Parametric Morphism {A : Type} {B : Type} {C : Type} `{A_isProset : isProset A} `{B_isProset : isProset B} `{C_isProset : isProset C} (f : A -> B -> C)
  (MONOTONIC : @isMonotonic2 A B C A_isProset B_isProset C_isProset f)
  : f with signature (eqProp ==> leProp ==> leProp)
  as compatibleWith_leProp_2_eqProp_l.
Proof.
  intros x1 x2 x_EQ y1 y2 y_LE. exact (compatibleWith_leProp_2 x1 x2 y1 y2 (eqProp_implies_leProp x1 x2 x_EQ) y_LE).
Defined.

#[global]
Add Parametric Morphism {A : Type} {B : Type} {C : Type} `{A_isProset : isProset A} `{B_isProset : isProset B} `{C_isProset : isProset C} (f : A -> B -> C)
  (MONOTONIC : @isMonotonic2 A B C A_isProset B_isProset C_isProset f)
  : f with signature (leProp ==> eqProp ==> leProp)
  as compatibleWith_leProp_2_eqProp_r.
Proof.
  intros x1 x2 x_LE y1 y2 y_EQ. exact (compatibleWith_leProp_2 x1 x2 y1 y2 x_LE (eqProp_implies_leProp y1 y2 y_EQ)).
Defined.

#[global]
Add Parametric Morphism {A : Type} {B : Type} {C : Type} `{A_isProset : isProset A} `{B_isProset : isProset B} `{C_isProset : isProset C} (f : A -> B -> C)
  (MONOTONIC : @isMonotonic2 A B C A_isProset B_isProset C_isProset f)
  : f with signature (eqProp ==> eqProp ==> leProp)
  as compatibleWith_leProp_2_eqProp_lr.
Proof.
  intros x1 x2 x_EQ y1 y2 y_EQ. exact (compatibleWith_leProp_2 x1 x2 y1 y2 (eqProp_implies_leProp x1 x2 x_EQ) (eqProp_implies_leProp y1 y2 y_EQ)).
Defined.

(** End PROSET. *)

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
  {isEquivalence : @Equivalence B eqProp}
  {isPreOrder : @PreOrder B leProp}
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
  intros x' hyp_eq. econs. intros x f_x_R_f_x'.
  subst y'. eapply IH; [exact f_x_R_f_x' | reflexivity].
Defined.

#[global]
Instance subSetoid {A : Type} {SETOID : isSetoid A} (P : A -> Prop) : isSetoid (@sig A P) :=
  { eqProp (lhs : @sig A P) (rhs : @sig A P) := proj1_sig lhs == proj1_sig rhs
  ; eqProp_Equivalence := relation_on_image_liftsEquivalence SETOID.(eqProp_Equivalence) (@proj1_sig A P)
  }.

#[global]
Instance subProset {A : Type} {PROSET : isProset A} (P : A -> Prop) : isProset (@sig A P) :=
  { leProp (lhs : @sig A P) (rhs : @sig A P) := proj1_sig lhs =< proj1_sig rhs
  ; Proset_isSetoid := subSetoid P
  ; leProp_PreOrder := relation_on_image_liftsPreOrder _ (@proj1_sig A P)
  ; leProp_PartialOrder := relation_on_image_liftsPartialOrder _ (@proj1_sig A P)
  }.

(** Section FUNCTOR. *)

#[universes(polymorphic=yes)]
Class isFunctor@{d c} (F : Type@{d} -> Type@{c}) : Type :=
  fmap (A : Type@{d}) (B : Type@{d}) (f : A -> B) : F A -> F B.

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

#[universes(polymorphic=yes)]
Class isMonad@{d c} (M : Type@{d} -> Type@{c}) : Type :=
  { bind {A : Type@{d}} {B : Type@{d}} (m : M A) (k : A -> M B) : M B
  ; pure {A : Type@{d}} (x : A) : M A
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

#[global, universes(polymorphic=yes)]
Instance mkFunctorFromMonad@{d c} {M : Type@{d} -> Type@{c}} `(MONAD : isMonad@{d c} M) : isFunctor@{d c} M :=
  fun A : Type@{d} => fun B : Type@{d} => fun f : A -> B => fun m : M A => bind m (fun x : A => pure (f x)).

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
Definition t@{u} (A : Type@{u}) : Type@{u} :=
  A -> Prop.

#[universes(polymorphic=yes)]
Definition In@{u} {A : Type@{u}} (x : A) (X : t@{u} A) : Prop :=
  X x.

#[universes(polymorphic=yes)]
Definition isSubsetOf@{u} {A : Type@{u}} (X1 : t@{u} A) (X2 : t@{u} A) : Prop :=
  forall x, In@{u} x X1 -> In@{u} x X2.

#[local] Infix "\in" := In : type_scope.
#[local] Infix "\subseteq" := isSubsetOf : type_scope.

#[global]
Instance ensemble_isProset {A : Type} : isProset (E.t A) :=
  let PROSET : isProset (E.t A) := pi_isProset (fun _ : A => Prop_isProset) in
  {|
    leProp := isSubsetOf;
    Proset_isSetoid := {| eqProp lhs rhs := forall x, x \in lhs <-> x \in rhs; eqProp_Equivalence := PROSET.(Proset_isSetoid).(eqProp_Equivalence) |};
    leProp_PreOrder := PROSET.(leProp_PreOrder);
    leProp_PartialOrder := PROSET.(leProp_PartialOrder);
  |}.

#[global]
Add Parametric Morphism {A : Type}
  : (@In A) with signature (eq ==> eqProp ==> iff)
  as In_compatWith_eqProp.
Proof.
  intros z X1 X2 X_EQ. exact (X_EQ z).
Defined.

#[global]
Instance t_isSetoid1 : isSetoid1 E.t :=
  fun X : Type => fun _ : isSetoid X => (@ensemble_isProset X).(Proset_isSetoid).

#[global, universes(polymorphic=yes)]
Instance t_isMonad@{d} : isMonad@{d d} E.t@{d} :=
  { bind {A : Type@{d}} {B : Type@{d}} (m : E.t A) (k : A -> E.t B) := fun z => exists x, x \in m /\ z \in k x
  ; pure {A : Type@{d}} (x : A) := fun z => x = z
  }.

#[global]
Instance t_satisfiesMonadLaws
  : @MonadLaws E.t t_isSetoid1 t_isMonad.
Proof.
  split; cbv; ii; firstorder congruence.
Qed.

Lemma liftM2_spec {A : Type} {B : Type} {C : Type} (f : A -> B -> C) (X : E.t A) (Y : E.t B)
  : forall z, z \in liftM2 f X Y <-> (exists x, x \in X /\ exists y, y \in Y /\ z = f x y).
Proof.
  cbv; firstorder.
Qed.

(** Section SET_CONSTRUCTIONS. *)

Inductive unions@{u} {A : Type@{u}} (Xs : E.t@{u} (E.t@{u} A)) (x : A) : Prop :=
  | In_unions (X : E.t@{u} A)
    (H_in : x \in X)
    (H_IN : X \in Xs)
    : E.In@{u} x (unions Xs).

#[local] Hint Constructors unions : core.

Lemma in_unions_iff (A : Type) Xs
  : forall z, z \in @unions A Xs <-> (exists X, z \in X /\ X \in Xs).
Proof.
  intros z; split; [intros [? ? ?] | intros [? [? ?]]]; eauto.
Qed.

#[global] Hint Rewrite in_unions_iff : simplication_hints.

#[global]
Instance unions_eqPropCompatible1 (A : Type)
  : eqPropCompatible1 (@unions A).
Proof.
  ii. do 2 rewrite in_unions_iff. now firstorder.
Qed.

Inductive union@{u} {A : Type@{u}} (X1 : E.t@{u} A) (X2 : E.t@{u} A) (x : A) : Prop :=
  | In_union_l
    (H_inl : x \in X1)
    : E.In@{u} x (union X1 X2)
  | In_union_r
    (H_inr : x \in X2)
    : E.In@{u} x (union X1 X2).

#[local] Hint Constructors union : core.

Lemma in_union_iff (A : Type) X1 X2
  : forall z, z \in @union A X1 X2 <-> (z \in X1 \/ z \in X2).
Proof.
  intros z; split; [intros [? | ?] | intros [? | ?]]; eauto.
Qed.

#[global] Hint Rewrite in_union_iff : simplication_hints.

#[global]
Instance union_eqPropCompatible2 (A : Type)
  : eqPropCompatible2 (@union A).
Proof.
  ii. do 2 rewrite in_union_iff. now firstorder.
Qed.

Inductive empty@{u} {A : Type@{u}} : E.t@{u} A :=.

#[local] Hint Constructors empty : core.

Lemma in_empty_iff (A : Type)
  : forall z, z \in @empty A <-> False.
Proof.
  intros z; split; [intros [] | intros []]; eauto.
Qed.

#[global] Hint Rewrite in_empty_iff : simplication_hints.

Inductive intersection@{u} {A : Type@{u}} (X1 : E.t@{u} A) (X2 : E.t@{u} A) (x : A) : Prop :=
  | In_intersection
    (H_IN1 : x \in X1)
    (H_IN2 : x \in X2)
    : E.In@{u} x (intersection X1 X2).

#[local] Hint Constructors intersection : core.

Lemma in_intersection_iff (A : Type) X1 X2
  : forall z, z \in @intersection A X1 X2 <-> (z \in X1 /\ z \in X2).
Proof.
  intros z; split; [intros [? ?] | intros [? ?]]; eauto.
Qed.

#[global] Hint Rewrite in_intersection_iff : simplication_hints.

#[global]
Instance intersection_eqPropCompatible2 (A : Type)
  : eqPropCompatible2 (@intersection A).
Proof.
  ii. do 2 rewrite in_intersection_iff. now firstorder.
Qed.

Inductive singleton@{u} {A : Type@{u}} (x : A) : E.t@{u} A :=
  | In_singleton
    : E.In@{u} x (singleton x).

#[local] Hint Constructors singleton : core.

Lemma in_singleton_iff (A : Type) x
  : forall z, z \in @singleton A x <-> (z = x).
Proof.
  intros z; split; [intros [] | intros ->]; eauto.
Qed.

#[global] Hint Rewrite in_singleton_iff : simplication_hints.

Inductive image@{u v} {A : Type@{u}} {B : Type@{v}} (f : A -> B) (X : E.t@{u} A) (y : B) : Prop :=
  | In_image x
    (IMAGE : y = f x)
    (H_IN : x \in X)
    : E.In@{v} y (image f X).

#[local] Hint Constructors image : core.

Lemma in_image_iff (A : Type) (B : Type) f X
  : forall z, z \in @image A B f X <-> (exists x, z = f x /\ x \in X).
Proof.
  intros z; split; [intros [? ? ?] | intros [? [-> ?]]]; eauto.
Qed.

#[global] Hint Rewrite in_image_iff : simplication_hints.

#[global]
Add Parametric Morphism {A : Type} {B : Type}
  : (@image A B) with signature (eqProp (isSetoid := pi_isSetoid (fun _ => mkSetoid_from_eq)) ==> eqProp ==> eqProp)
  as image_compatWith_eqProp.
Proof.
  intros f1 f2 f_EQ X1 X2 X_EQ. intros z. do 4 red in f_EQ. do 6 red in X_EQ.
  do 2 rewrite in_image_iff in *. now split; i; des; exists x; rewrite f_EQ, X_EQ in *.
Qed.

Inductive preimage@{u v} {A : Type@{u}} {B : Type@{v}} (f : A -> B) (Y : E.t@{v} B) (x : A) : Prop :=
  | In_preimage y
    (IMAGE : y = f x)
    (H_IN : y \in Y)
    : E.In@{u} x (preimage f Y).

#[local] Hint Constructors preimage : core.

Lemma in_preimage_iff (A : Type) (B : Type) f Y
  : forall z, z \in @preimage A B f Y <-> (exists y, y = f z /\ y \in Y).
Proof.
  intros z; split; [intros [? ? ?] | intros [? [-> ?]]]; eauto.
Qed.

#[global] Hint Rewrite in_preimage_iff : simplication_hints.

#[global]
Add Parametric Morphism {A : Type} {B : Type}
  : (@preimage A B) with signature (eqProp (isSetoid := pi_isSetoid (fun _ => mkSetoid_from_eq)) ==> eqProp ==> eqProp)
  as preimage_compatWith_eqProp.
Proof.
  intros f1 f2 f_EQ Y1 Y2 Y_EQ. intros z. do 4 red in f_EQ. do 6 red in Y_EQ.
  do 2 rewrite in_preimage_iff in *. now split; i; des; exists y; rewrite f_EQ, Y_EQ in *.
Qed.

Inductive full@{u} {A : Type@{u}} (x : A) : Prop :=
  | in_full
    : E.In@{u} x (full).

#[local] Hint Constructors full : core.

Lemma in_full_iff (A : Type)
  : forall z, z \in @full A <-> True.
Proof.
  intros z; eauto.
Qed.

#[global] Hint Rewrite in_full_iff : simplication_hints.

#[universes(polymorphic=yes)]
Definition fromList@{u} {A : Type@{u}} (xs : list A) : E.t@{u} A :=
  fun x => List.In x xs.

#[global] Hint Unfold fromList : simplication_hints.

#[universes(polymorphic=yes)]
Definition insert@{u} {A : Type@{u}} (x1 : A) (X2 : E.t@{u} A) : E.t@{u} A :=
  fun x => x = x1 \/ x \in X2.

#[global] Hint Unfold insert : simplication_hints.

Lemma in_insert_iff (A : Type) x1 X2
  : forall z, z \in @insert A x1 X2 <-> (z = x1 \/ z \in X2).
Proof.
  reflexivity.
Qed.

#[global] Hint Rewrite in_insert_iff : simplication_hints.

#[global]
Add Parametric Morphism {A : Type}
  : (@insert A) with signature (eq ==> eqProp ==> eqProp)
  as insert_compatWith_eqProp.
Proof.
  firstorder.
Qed.

#[universes(polymorphic=yes)]
Definition complement@{u} {A : Type@{u}} (X : E.t@{u} A) : E.t@{u} A :=
  fun x => ~ x \in X.

#[global] Hint Unfold complement : simplication_hints.

Lemma in_complement_iff (A : Type) X
  : forall z, z \in @complement A X <-> (~ z \in X).
Proof.
  reflexivity.
Qed.

#[global] Hint Rewrite in_complement_iff : simplication_hints.

#[global]
Add Parametric Morphism {A : Type}
  : (@complement A) with signature (eqProp ==> eqProp)
  as complement_compatWith_eqProp.
Proof.
  firstorder.
Qed.

#[universes(polymorphic=yes)]
Definition delete@{u} {A : Type@{u}} (x1 : A) (X2 : E.t@{u} A) : E.t@{u} A :=
  fun x => x <> x1 /\ x \in X2.

#[global] Hint Unfold delete : simplication_hints.

Lemma in_delete_iff (A : Type) x1 X2
  : forall z, z \in @delete A x1 X2 <-> (z <> x1 /\ z \in X2).
Proof.
  reflexivity.
Qed.

#[global] Hint Rewrite in_delete_iff : simplication_hints.

#[global]
Add Parametric Morphism {A : Type}
  : (@delete A) with signature (eq ==> eqProp ==> eqProp)
  as delete_compatWith_eqProp.
Proof.
  firstorder.
Qed.

#[universes(polymorphic=yes)]
Definition intersections@{u} {A : Type@{u}} (Xs : E.t@{u} (E.t@{u} A)) : E.t@{u} A :=
  fun x => forall X, X \in Xs -> x \in X.

#[global] Hint Unfold intersections : simplication_hints.

Lemma in_intersections_iff (A : Type) Xs
  : forall z, z \in @intersections A Xs <-> (forall X, X \in Xs -> z \in X).
Proof.
  reflexivity.
Qed.

#[global] Hint Rewrite in_intersections_iff : simplication_hints.

#[global]
Add Parametric Morphism {A : Type}
  : (@intersections A) with signature (eqProp ==> eqProp)
  as intersections_compatWith_eqProp.
Proof.
  firstorder.
Qed.

(** End SET_CONSTRUCTIONS. *)

Ltac unfold_E := repeat
  match goal with
  | [ H : context[ E.In _ (fun _ => _) ] |- _ ] => unfold E.In in H
  | [ |- context[ E.In _ (fun _ => _) ] ] => unfold E.In
  | [ H : context[ E.isSubsetOf _ (fun _ => _) ] |- _ ] => unfold E.isSubsetOf in H
  | [ |- context[ E.isSubsetOf _ (fun _ => _) ] ] => unfold E.isSubsetOf
  end.

#[global]
Instance subseteq_PreOrder {A : Type}
  : PreOrder (@E.isSubsetOf A).
Proof.
  exact (leProp_PreOrder).
Defined.

Lemma insert_monotonic {A : Type} (x1 : A) (X2 : E.t A) (X2' : E.t A)
  (SUBSET : X2 \subseteq X2')
  : E.insert x1 X2 \subseteq E.insert x1 X2'.
Proof.
  intros z [-> | H_IN]; [left; reflexivity | right; exact (SUBSET z H_IN)].
Qed.

End E.

Notation ensemble := E.t.

#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "\subseteq" := E.isSubsetOf : type_scope.

Lemma unfold_ensemble_eqProp (A : Type) (X1 : ensemble A) (X2 : ensemble A)
  : X1 == X2 <-> (X1 \subseteq X2 /\ X2 \subseteq X1).
Proof.
  transitivity (forall z, z \in X1 <-> z \in X2).
  - reflexivity.
  - firstorder.
Qed.

#[global] Hint Rewrite unfold_ensemble_eqProp : simplication_hints.

(** Section Tactics. *)

Tactic Notation "s!" :=
  repeat (
    autorewrite with simplication_hints in *;
    E.unfold_E;
    simpl in *;
    autounfold with simplication_hints in *
  ).

Tactic Notation "ss!" :=
  s!; subst; eauto with *; firstorder (try first [lia | congruence | f_equal]).

Tactic Notation "done!" :=
  now ii; first [congruence | lia | repeat ss!; done].

Module Tac.

Ltac lightening_hook :=
  contradiction || done!.

Ltac lightening :=
  ii;
  first
  [ lazymatch goal with
    | [ |- context [@False_rect _ ?FF] ] => exfalso; contradiction FF
    | [ |- context [@False_rec _ ?FF] ] => exfalso; contradiction FF
    | [ |- context [@False_ind _ ?FF] ] => exfalso; contradiction FF
    | [ H : context [@False_rect _ ?FF] |- _ ] => exfalso; contradiction FF
    | [ H : context [@False_rec _ ?FF] |- _ ] => exfalso; contradiction FF
    | [ H : context [@False_ind _ ?FF] |- _ ] => exfalso; contradiction FF
    end
  | exfalso; tauto congruence
  | exfalso; lightening_hook
  ].

Ltac done :=
  done!.

End Tac.

(** End Tactics. *)

Section OPERATION_PROPS.

Context {A : Type} `{SETOID : isSetoid A}.

Class isAssociative (f : A -> A -> A) : Prop :=
  assoc x y z : f x (f y z) == f (f x y) z.

Class isCommutative (f : A -> A -> A) : Prop :=
  comm x y : f x y == f y x.

Class isIdempotent (f : A -> A -> A) : Prop :=
  idem x : f x x == x.

Class distributesOver (MUL : A -> A -> A) (ADD : A -> A -> A) : Prop :=
  { left_distr x y z
    : MUL x (ADD y z) == ADD (MUL x y) (MUL x z)
  ; right_distr x y z
    : MUL (ADD y z) x == ADD (MUL y x) (MUL z x)
  }.

Class isIdentityElementOf (e : A) (f : A -> A -> A) : Prop :=
  { left_id x
    : f e x == x
  ; right_id x
    : f x e == x
  }.

Class isInverseOperatorOf (INV : A -> A) (OP : A -> A -> A) {e : A} {IDENTITY : isIdentityElementOf e OP} : Prop :=
  { left_inv x
    : OP (INV x) x == e
  ; right_inv x
    : OP x (INV x) == e
  }.

Class AbsorptionLaw (OP1 : A -> A -> A) (OP2 : A -> A -> A) : Prop :=
  { absorption_law1 x y
    : OP1 x (OP2 x y) == x
  ; absorption_law2 x y
    : OP2 x (OP1 x y) == x
  }.

Class isAnnihilatorFor (a : A) (OP : A -> A -> A) : Prop :=
  { left_ann x
    : OP a x == a
  ; right_ann x
    : OP x a == a
  }.

#[local]
Instance inverse_compatWith_eqProp (OP : A -> A -> A) (e : A) (INV : A -> A)
  (COMPAT : eqPropCompatible2 OP)
  (ASSOCIATIVE : isAssociative OP)
  (IDENTITY : isIdentityElementOf e OP)
  (INVERSE : isInverseOperatorOf INV OP)
  : eqPropCompatible1 INV.
Proof.
  ii. rewrite <- right_id.
  rewrite <- right_inv with (x := x2).
  assert (claim : OP (INV x1) x2 == e).
  { rewrite <- x_EQ. eapply left_inv. }
  rewrite assoc. rewrite claim. eapply left_id.
Qed.

End OPERATION_PROPS.

Class isClosureOperator {A : Type} `{PROSET : isProset A} (cl : A -> A) : Prop :=
  { cl_op_extensive : forall x, x =< cl x
  ; cl_op_idempotent : forall x, cl (cl x) == cl x
  ; cl_op_monotonic :: isMonotonic1 cl
  }.

Lemma isClosureOperator_iff {A : Type} `{PROSET : isProset A} (cl : A -> A)
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

Class isCompatibleWith_eqProp {A : Type} `{SETOID : isSetoid A} (P : A -> Prop) : Prop :=
  compatWith_eqProp : forall x, P x -> forall y, x == y -> P y.

#[global]
Add Parametric Morphism {A : Type} {SETOID : isSetoid A} (P : A -> Prop) (COMPAT : isCompatibleWith_eqProp (A := A) (SETOID := SETOID) P)
  : P with signature (eqProp ==> iff)
  as isCompatibleWith_eqProp_sig_eqProp_iff.
Proof.
  intros x y EQ; red in COMPAT. now split; intros H_P; eapply COMPAT; eauto.
Qed.

#[global]
Instance eqProp_cl_isCompatibleWith_eqProp {A : Type} `{SETOID : isSetoid A} (X : ensemble A)
  : isCompatibleWith_eqProp (eqProp_cl X).
Proof.
  intros x [a [EQ IN]] y EQ'. exists a. split. rewrite <- EQ'. exact EQ. exact IN.
Qed.

#[global]
Instance isCompatibleWith_eqProp_forall {A : Type} {B : A -> Type} `{SETOID : forall i : A, isSetoid (B i)} (P : forall i : A, B i -> Prop)
  (COMPAT : forall i : A, isCompatibleWith_eqProp (P i))
  : isCompatibleWith_eqProp (fun x => forall i : A, P i (x i)).
Proof.
  intros x P_x y EQ i. exact (COMPAT i (x i) (P_x i) (y i) (EQ i)).
Defined.

#[global]
Instance isCompatibleWith_eqProp_exists {A : Type} {B : A -> Type} `{SETOID : forall i : A, isSetoid (B i)} (P : forall i : A, B i -> Prop)
  (COMPAT : forall i : A, isCompatibleWith_eqProp (P i))
  : isCompatibleWith_eqProp (fun x => exists i : A, P i (x i)).
Proof.
  intros x [i P_x] y EQ. exists i. exact (COMPAT i (x i) P_x (y i) (EQ i)).
Defined.

Module B.

#[local] Open Scope program_scope.

Inductive transitiveClosure {A : Type} (R : A -> A -> Prop) (x : A) (y : A) : Prop :=
  | transitiveClosure_once
    (STEP : R x y)
    : transitiveClosure R x y
  | transitiveClosure_trans z
    (STEPs : transitiveClosure R x z)
    (STEP : transitiveClosure R z y)
    : transitiveClosure R x y.

#[local] Hint Constructors transitiveClosure : core.

Lemma transitiveClosure_lift_well_founded {A : Type} (R : A -> A -> Prop)
  (R_wf : well_founded R)
  : well_founded (transitiveClosure R).
Proof.
  intros x. pose proof (R_wf x) as H_ACC. clear R_wf.
  induction H_ACC as [x H_ACC_inv IH]. constructor 1.
  induction 1 as [x y | x y z H1 IH1 H2 IH2]; eauto.
  eapply IH2; eauto.
Qed.

Definition Prop_to_Set (P : Prop) : Set :=
  P.

#[universes(polymorphic=yes)]
Definition isSome@{u} {A : Type@{u}} (m : option A) : bool :=
  match m with
  | Some _ => true
  | None => false
  end.

#[universes(polymorphic=yes)]
Definition dollar@{u v} {A : Type@{u}} {B : A -> Type@{v}} (f : forall x : A, B x) (x : A) : B x :=
  f x.

#[local] Infix "$" := dollar.
#[local] Infix ">>=" := bind.

Definition kcompose {M} {MONAD : isMonad M} {A} {B} {C} (k1 : A -> M B) (k2 : B -> M C) : A -> M C :=
  fun x => k1 x >>= k2.

#[local] Infix ">=>" := kcompose : program_scope.

#[universes(template)]
Record stateT (S : Type) (M : Type -> Type) (X : Type) : Type :=
  StateT { runStateT : S -> M (X * S)%type }.

#[global] Arguments StateT {S} {M} {X}.
#[global] Arguments runStateT {S} {M} {X}.

#[global]
Instance stateT_isMonad {S} {M} `(M_isMonad : isMonad M) : isMonad (B.stateT S M) :=
  { pure {A} (x : A) := B.StateT (curry pure x)
  ; bind {A} {B} (m : B.stateT S M A) (k : A -> B.stateT S M B) := B.StateT (B.runStateT m >=> uncurry (B.runStateT ∘ k))
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
  (MONAD_LAWS : @MonadLaws M SETOID1 MONAD)
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

Definition maybe {A : Type} {B : option A -> Type} (d : B None) (f : forall x : A, B (Some x)) (m : option A) : B m :=
  match m with
  | None => d
  | Some x => f x
  end.

Definition fromMaybe {A : Type} (d : A) (m : option A) : A :=
  maybe d (fun x : A => x) m.

Definition either {A : Type} {B : Type} {C : (A + B) -> Type} (f : forall x : A, C (inl x)) (g : forall y : B, C (inr y)) (z : A + B) : C z :=
  match z with
  | inl x => f x
  | inr y => g y
  end.

Definition Some_dec {A : Type} (x : option A)
  : { x' : A | x = Some x' } + B.Prop_to_Set (x = None).
Proof.
  destruct x as [x' | ].
  - left. exists x'. reflexivity.
  - right. red. reflexivity.
Defined.

Definition ne_None_elim {A : Type} (x : option A) (ne_None : x <> None) : { x' : A | x = Some x' } :=
  match Some_dec x with
  | inl x' => x'
  | inr eq_None => False_rect _ (ne_None eq_None)
  end.

#[global]
Instance list_isMonad : isMonad list :=
  { pure {A : Type} (x : A) := [x]
  ; bind {A : Type} {B : Type} (xs : list A) (k : A -> list B) := concat (map k xs)
  }.

#[global]
Instance option_isSetoid1 : isSetoid1 option :=
  @option_isSetoid.

#[global]
Instance option_isMonad : isMonad option :=
  { pure {A : Type} := @Some A
  ; bind {A : Type} {B : Type} (m : option A) (k : A -> option B) := maybe None k m
  }.

#[global]
Instance option_satisfiesMonadLaws
  : MonadLaws option (SETOID1 := option_isSetoid1) (MONAD := option_isMonad).
Proof.
  split; i; simpl in *.
  - inv m_EQ; simpl.
    + econs.
    + reflexivity.
  - destruct m as [x | ]; simpl.
    + specialize k_EQ with (x := x). trivial.
    + econs.
  - destruct m as [x | ]; simpl.
    + reflexivity.
    + econs.
  - reflexivity.
  - destruct m as [x | ]; simpl.
    + reflexivity.
    + econs.
Qed.

Lemma bind_isSome_iff {A : Type} {B : Type} (m : option A) (k : A -> option B)
  : isSome (bind m k) = true <-> (exists x, m = Some x /\ isSome (k x) = true).
Proof.
  destruct m as [x | ]; simpl; now firstorder congruence.
Qed.

Lemma pure_isSome_iff {A : Type} (x : A)
  : isSome (pure x) = true <-> True.
Proof.
  tauto.
Qed.

Lemma liftM2_isSome_iff {A : Type} {B : Type} {C : Type} (m1 : option A) (m2 : option B) (f : A -> B -> C)
  : isSome (liftM2 f m1 m2) = true <-> (exists x, exists y, m1 = Some x /\ m2 = Some y).
Proof.
  unfold liftM2. simpl. destruct m1 as [x | ], m2 as [y | ]; simpl; split; i; des; try congruence.
  exists x. exists y. split; trivial.
Qed.

Lemma observe_bind {A : Type} {B : Type} (m : option A) (k : A -> option B) (z : option B) :
  @B.maybe A (fun _ : option A => option B) None k m = z <->
  match z with
  | Some y => exists x, m = Some x /\ k x = Some y
  | None => m = None \/ (exists x, m = Some x /\ k x = None)
  end. 
Proof.
  destruct m as [x | ]; cbn.
  - destruct (k x) as [y | ] eqn: H_OBS; destruct z as [obs | ]; firstorder try congruence.
    exists x. split; congruence.
  - destruct z as [obs | ]; split; i; des; tauto || congruence.
Qed.

#[universes(polymorphic=yes)]
Definition Rel_id@{u} {A : Type@{u}} : ensemble@{u} (A * A) :=
  fun '(x1, x2) => x1 = x2.

#[universes(polymorphic=yes)]
Definition Rel_flip@{u} {A : Type@{u}} {B : Type@{u}} (R1 : ensemble@{u} (A * B)) : ensemble@{u} (B * A) :=
  fun '(x1, x2) => R1 (x2, x1).

#[universes(polymorphic=yes)]
Definition Rel_compose@{u} {A : Type@{u}} {B : Type@{u}} {C : Type@{u}} (R1 : ensemble@{u} (B * C)) (R2 : ensemble@{u} (A * B)) : ensemble@{u} (A * C) :=
  fun '(x1, x2) => exists x, R2 (x1, x) /\ R1 (x, x2).

Inductive sum1 (X : Type -> Type) (Y : Type -> Type) (A : Type) : Type :=
  | inl1 (INL : X A) : sum1 X Y A
  | inr1 (INR : Y A) : sum1 X Y A.

#[global] Arguments sum1 X%_type Y%_type.
#[global] Arguments inl1 {X} {Y} {A}.
#[global] Arguments inr1 {X} {Y} {A}.

Inductive void1 (A : Type) : Type :=.

#[universes(template), projections(primitive)]
Record sig {A : Type} {P : A -> Prop} : Type :=
  { proj1_sig : A
  ; proj2_sig : P proj1_sig
  }.

#[global] Arguments B.sig : clear implicits.

Notation exist x y := {| proj1_sig := x; proj2_sig := y; |}.

#[universes(template), projections(primitive)]
Record sigT {A : Type} {P : A -> Type} : Type :=
  { projT1 : A
  ; projT2 : P projT1
  }.

#[global] Arguments B.sigT : clear implicits.

Notation existT x y := {| projT1 := x; projT2 := y; |}.

#[universes(template), projections(primitive)]
Record prod {A : Type} {B : Type} : Type :=
  { fst : A
  ; snd : B
  }.

#[global] Arguments B.prod : clear implicits.

Notation pair x y := {| fst := x; snd := y; |}.

#[universes(template), projections(primitive)]
Class retracts (X : Type) (P : Prop) : Type :=
  { section : X -> P
  ; retraction : P -> X
  ; retraction_section (x : X)
    : retraction (section x) = x
  ; section_retraction (H : P)
    : section (retraction H) = H
  }.

#[local]
Instance trivial_retraction (P : Prop) : retracts (Prop_to_Set P) P :=
  { section (x : Prop_to_Set P) := x
  ; retraction (H : P) := H
  ; retraction_section := @eq_refl (Prop_to_Set P)
  ; section_retraction := @eq_refl (Prop_to_Set P)
  }.

End B.

Notation StateT k := {| B.runStateT := k |}.

Infix "+'" := B.sum1 (at level 50, left associativity) : type_scope.

Infix "$" := B.dollar.
Infix ">>=" := bind.
Infix ">=>" := B.kcompose : program_scope.

Class hasEqDec (A : Type) : Type :=
  eq_dec (x : A) (y : A) : {x = y} + {x <> y}.

Definition eqb {A : Type} {hasEqDec : hasEqDec A} (x : A) (y : A) : bool :=
  if eq_dec x y then true else false.

Lemma eqb_eq {A : Type} {hasEqDec : hasEqDec A} (x : A) (y : A)
  : eqb x y = true <-> x = y.
Proof.
  unfold eqb. destruct (eq_dec x y) as [H_yes | H_no]; done!.
Qed.

Lemma eqb_neq {A : Type} {hasEqDec : hasEqDec A} (x : A) (y : A)
  : eqb x y = false <-> x <> y.
Proof.
  unfold eqb. destruct (eq_dec x y) as [H_yes | H_no]; done!.
Qed.

Theorem eqb_spec {A : Type} {hasEqDec : hasEqDec A} (x : A) (y : A) (b : bool)
  : eqb x y = b <-> (if b then x = y else x <> y).
Proof.
  destruct b; [eapply eqb_eq | eapply eqb_neq].
Qed.

#[global]
Instance nat_hasEqDec : hasEqDec nat :=
  Nat.eq_dec.

#[global]
Instance pair_hasEqdec {A : Type} {B : Type}
  (A_hasEqDec : hasEqDec A)
  (B_hasEqDec : hasEqDec B)
  : hasEqDec (A * B).
Proof.
  red in A_hasEqDec, B_hasEqDec. red. decide equality.
Defined.

#[global]
Instance bool_hasEqDec
  : hasEqDec bool.
Proof.
  red. decide equality.
Defined.

#[global]
Instance sum_hasEqDec {A : Type} {B : Type}
  (A_hasEqDec : hasEqDec A)
  (B_hasEqDec : hasEqDec B)
  : hasEqDec (A + B).
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

Section SIMILARITY.

Infix "=~=" := is_similar_to.

#[global]
Instance Similarity_forall {D : Type} {D' : Type} {C : D -> Type} {C' : D' -> Type} (DOM_SIM : Similarity D D') (COD_SIM : forall x : D, forall x' : D', is_similar_to (Similarity := DOM_SIM) x x' -> Similarity (C x) (C' x')) : Similarity (forall x : D, C x) (forall x' : D', C' x') :=
  fun f => fun f' => forall x : D, forall x' : D', forall x_corres : is_similar_to (Similarity := DOM_SIM) x x', is_similar_to (Similarity := COD_SIM x x' x_corres) (f x) (f' x').

Inductive Similarity_sum {A : Type} {A' : Type} {B : Type} {B' : Type} (A_SIM : Similarity A A') (B_SIM : Similarity B B') : (A + B)%type -> (A' + B')%type -> Prop :=
  | inl_corres (x : A) (x' : A')
    (x_corres : x =~= x')
    : inl x =~= inl x'
  | inr_corres (y : B) (y' : B')
    (y_corres : y =~= y')
    : inr y =~= inr y'.

#[local] Hint Constructors Similarity_sum : simplication_hints.

Inductive Similarity_prod {A : Type} {A' : Type} {B : Type} {B' : Type} (A_SIM : Similarity A A') (B_SIM : Similarity B B') : (A * B)%type -> (A' * B')%type -> Prop :=
  | pair_corres (p : A * B) (p' : A' * B')
    (fst_corres : fst p =~= fst p')
    (snd_corres : snd p =~= snd p')
    : p =~= p'.

#[local] Hint Constructors Similarity_prod : simplication_hints.

#[local] Obligation Tactic := i.

#[local, program]
Instance sum_isSetoid {A : Type} {B : Type} {A_isSetoid : isSetoid A} {B_isSetoid : isSetoid B} : isSetoid (A + B)%type :=
  { eqProp := Similarity_sum eqProp eqProp }.
Next Obligation.
  split; ii.
  - destruct x; econs; eauto with *.
  - destruct x, y; inv H; econs; eauto with *.
  - destruct x, y, z; inv H; inv H0; econs; etransitivity; eauto with *.
Qed.

#[local, program]
Instance prod_isSetoid {A : Type} {B : Type} {A_isSetoid : isSetoid A} {B_isSetoid : isSetoid B} : isSetoid (A * B)%type :=
  { eqProp := Similarity_prod eqProp eqProp }.
Next Obligation.
  split; ii.
  - destruct x; econs; eauto with *.
  - destruct x, y; inv H; econs; eauto with *.
  - destruct x, y, z; inv H; inv H0; econs; etransitivity; eauto with *.
Qed.

#[local, program]
Instance fun_isSetoid {A : Type} {B : Type} {A_isSetoid : isSetoid A} {B_isSetoid : isSetoid B} : isSetoid { f : A -> B | eqPropCompatible1 f } :=
  { eqProp f1 f2 := forall x1 : A, forall x2 : A, is_similar_to (Similarity := eqProp) x1 x2 -> is_similar_to (Similarity := eqProp) (proj1_sig f1 x1) (proj1_sig f2 x2) }.
Next Obligation.
  split.
  - intros [f1 H_f1]; ii; simpl in *. unfold is_similar_to in *. eauto with *.
  - intros [f1 H_f1] [f2 H_f2]; ii; simpl in *. unfold is_similar_to in *. symmetry; eauto with *.
  - intros [f1 H_f1] [f2 H_f2] [f3 H_f3]; ii; simpl in *. unfold is_similar_to in *. transitivity (f2 x2); eauto with *.
Qed.

End SIMILARITY.

#[universes(template)]
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

#[global]
Instance nat_isEnumerable : isEnumerable nat :=
  { enum := id
  ; enum_spec x := @exist _ _ x eq_refl
  }.

#[universes(template)]
Class isCountable (A : Type) : Type :=
  { encode : A -> nat
  ; decode : nat -> option A
  ; decode_encode (x : A)
    : decode (encode x) = Some x 
  }.

Lemma encode_inj {A : Type} `{COUNTABLE : isCountable A} x1 x2
  (EQ : encode x1 = encode x2)
  : x1 = x2.
Proof.
  apply f_equal with (f := decode) in EQ. do 2 rewrite decode_encode in *. congruence.
Qed.

#[global]
Instance isCountable_if_isEnumerable {A : Type} `(ENUMERABLE : isEnumerable A) : isCountable A :=
  { encode (x : A) := proj1_sig (enum_spec x)
  ; decode (n : nat) := Some (enum n)
  ; decode_encode (x : A) := f_equal (@Some A) (proj2_sig (enum_spec x))
  }.

#[global]
Instance Empty_set_isCountable : isCountable Empty_set :=
  { encode := Empty_set_rec _
  ; decode _ := None
  ; decode_encode := Empty_set_ind _
  }.

Module L.

Include Stdlib.Lists.List.

Definition null {A : Type} (l : list A) : bool :=
  match l with
  | L.nil => true
  | L.cons _ _ => false
  end.

Lemma null_spec (A : Type) (l : list A)
  : forall b, null l = b <-> (if b then l = [] else l <> []).
Proof.
  destruct l; intros [ | ]; simpl; done!.
Qed.

#[global] Hint Rewrite null_spec in_map_iff in_app_iff : simplication_hints.

Lemma in_remove_iff (A : Type) `(EQ_DEC : hasEqDec A) (x1 : A) (xs2 : list A)
  : forall z, In z (remove Prelude.eq_dec x1 xs2) <-> (In z xs2 /\ z <> x1).
Proof.
  i; split.
  { intros H_IN. eapply in_remove. exact H_IN. }
  { intros [H_IN H_NE]. eapply in_in_remove; [exact H_NE | exact H_IN]. }
Qed.

#[global] Hint Rewrite in_remove_iff : simplication_hints.

Fixpoint replicate {A : Type} (n : nat) (x : A) : list A :=
  match n with
  | O => []
  | S n => x :: replicate n x
  end.

Lemma replicate_unfold {A : Type} (n : nat) (x : A) :
  replicate n x =
  match n with
  | O => []
  | S n => x :: replicate n x
  end.
Proof.
  destruct n; reflexivity.
Defined.

Lemma replicate_rev_unfold {A : Type} (n : nat) (x : A) :
  replicate n x =
  match n with
  | O => []
  | S n => replicate n x ++ [x]
  end.
Proof.
  destruct n as [ | n]; simpl; trivial.
  induction n as [ | n IH]; simpl; congruence.
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

Lemma list_rev_inj {A : Type} (l1 : list A) (l2 : list A)
  (EQ : rev l1 = rev l2)
  : l1 = l2.
Proof.
  rewrite <- rev_involutive with (l := l1). rewrite <- rev_involutive with (l := l2). congruence.
Qed.

Lemma app_cancel_l {A : Type} (prefix : list A) (suffix1 : list A) (suffix2 : list A)
  (EQ : prefix ++ suffix1 = prefix ++ suffix2)
  : suffix1 = suffix2.
Proof.
  revert suffix1 suffix2 EQ; induction prefix as [ | x xs IH]; simpl; intros; eauto. eapply IH; congruence.
Qed.

Lemma list_rev_app {A : Type} (l1 : list A) (l2 : list A)
  : rev (l1 ++ l2) = (rev l2 ++ rev l1).
Proof.
  induction l1 as [ | x1 l1 IH]; simpl.
  - rewrite app_nil_r. reflexivity.
  - rewrite IH. now rewrite <- app_assoc.
Qed.

Lemma app_cancel_r {A : Type} (prefix1 : list A) (prefix2 : list A) (suffix : list A)
  (EQ : prefix1 ++ suffix = prefix2 ++ suffix)
  : prefix1 = prefix2.
Proof.
  revert prefix1 prefix2 EQ. induction suffix as [suffix] using list_rev_dual.
  induction prefix1 as [prefix1] using list_rev_dual. induction prefix2 as [prefix2] using list_rev_dual.
  do 2 rewrite <- list_rev_app. intros EQ. apply rev_inj in EQ. apply app_cancel_l in EQ. congruence.
Qed.

Lemma forallb_spec {A : Type} (p : A -> bool) (xs : list A)
  : forall b, forallb p xs = b <-> (if b then forall x, In x xs -> p x = true else exists x, In x xs /\ p x = false).
Proof with try now firstorder.
  intros [ | ]; [exact (forallb_forall p xs) | induction xs as [ | x xs IH]; simpl in *]...
  rewrite andb_false_iff; firstorder; subst...
Qed.

#[local] Infix "!!" := nth_error : list_scope.

Lemma In_nth_error_Some {A : Type} (xs : list A) (x : A)
  (IN : In x xs)
  : exists n, xs !! n = Some x /\ n < length xs.
Proof with try (lia || done).
  revert x IN; induction xs as [ | x1 xs IH]; simpl; intros x0 IN... destruct IN as [<- | IN].
  - exists 0%nat; split...
  - pose proof (IH x0 IN) as (n & EQ & LE). exists (S n). split...
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
  - econs 1.
  - simpl. econs 2.
    + intros CONTRA. apply in_mk_edge_seq_inv in CONTRA. contradiction.
    + eapply IH.
Qed.

Fixpoint lookup {A : Type} {B : Type} {EQ_DEC : hasEqDec A} (x : A) (zs : list (A * B)) : option B :=
  match zs with
  | [] => None
  | (x', y) :: zs' => if eq_dec x x' then Some y else lookup x zs'
  end.

Notation is_finsubset_of xs X := (forall x, L.In x xs -> x \in X).

Notation is_listrep_of xs X := (forall x, L.In x xs <-> x \in X).

Lemma map_image_eq {A : Type} {B : Type} {C : Type} (f : A -> C) (g : B -> C) (xs : list A)
  (IMAGE : forall x, L.In x xs -> { y : B | f x = g y })
  : { ys : list B | L.map f xs = L.map g ys }.
Proof.
  induction xs as [ | x' xs' IH].
  - exists []. reflexivity.
  - pose proof (IMAGE x' (or_introl eq_refl)) as [y y_EQ].
    pose proof (IH (fun x => fun IN => IMAGE x (or_intror IN))) as [ys ys_EQ].
    exists (y :: ys). simpl. f_equal. exact y_EQ. exact ys_EQ.
Defined.

Lemma lookup_map {A : Type} {B : Type} (f : A -> B) (xs : list A) (i : nat)
  : map f xs !! i = match xs !! i with Some x => Some (f x) | None => None end.
Proof.
  revert i. induction xs as [ | x xs IH], i as [ | i]; simpl in *; try congruence; eauto.
Qed.

Section SUBSEQUENCE.

Context {A : Type}.

Lemma snoc_inv_iff (xs1 : list A) (xs2 : list A) (y1 : A) (y2 : A)
  : xs1 ++ [y1] = xs2 ++ [y2] <-> (xs1 = xs2 /\ y1 = y2).
Proof.
  split.
  - intros EQ.
    assert (length xs1 = length xs2) as LENGTH.
    { enough (length xs1 + 1 = length xs2 + 1)%nat by lia. apply f_equal with (f := @length A) in EQ. do 2 rewrite length_app in EQ; trivial. }
    assert (y1 = y2) as H_y.
    { enough (Some y1 = Some y2) by congruence.
      pose proof (f_equal (fun xs => xs !! length xs1) EQ) as YES. simpl in YES. rewrite LENGTH in YES at 2.
      rewrite nth_error_app2 in YES; try lia. rewrite nth_error_app2 in YES; try lia.
      replace (Datatypes.length xs1 - Datatypes.length xs1) with 0 in YES by lia.
      replace (Datatypes.length xs2 - Datatypes.length xs2) with 0 in YES by lia.
      exact YES.
    }
    split; trivial. eapply app_cancel_r with (suffix := [y1]). congruence.
  - intros [? ?]; congruence.
Qed.

Inductive subseq : list A -> list A -> Prop :=
  | subseq_nil
    : subseq [] []
  | subseq_skip xs ys z
    (SUBSEQ : subseq xs ys)
    : subseq xs (ys ++ [z])
  | subseq_snoc xs ys z
    (SUBSEQ : subseq xs ys)
    : subseq (xs ++ [z]) (ys ++ [z]).

#[local] Hint Constructors subseq : core.

Lemma subseq_Forall_Forall (P : A -> Prop) xs ys
  (SUBSEQ : subseq xs ys)
  (FORALL : Forall P ys)
  : Forall P xs.
Proof.
  induction SUBSEQ; eauto.
  - rewrite Forall_app in FORALL. tauto.
  - rewrite -> Forall_app in FORALL |- *. tauto.
Qed.

Lemma subseq_refl l
  : subseq l l.
Proof.
  induction l as [ | x xs IH] using list_rev_rect; eauto.
Qed.

#[local] Hint Resolve subseq_refl : core.

Lemma subseq_middle xs y zs
  : subseq (xs ++ zs) (xs ++ [y] ++ zs).
Proof.
  revert xs y. induction zs as [ | z zs IH] using list_rev_rect; intros.
  - rewrite app_nil_r. simpl. econstructor 2; eauto.
  - rewrite -> app_assoc with (l := xs). replace (xs ++ [y] ++ zs ++ [z]) with ((xs ++ [y]) ++ zs ++ [z]) by now repeat rewrite <- app_assoc.
    rewrite -> app_assoc with (l := xs ++ [y]). econstructor 3; rewrite <- app_assoc; eauto.
Qed.

Lemma nil_subseq l
  : subseq [] l.
Proof.
  induction l as [ | x xs IH] using list_rev_rect; eauto.
Qed.

#[local] Hint Resolve nil_subseq : core.

Lemma proper_subseq_length xs ys
  (SUBSEQ : subseq xs ys)
  : xs = ys \/ (length xs < length ys)%nat.
Proof.
  induction SUBSEQ.
  - left; trivial.
  - destruct IHSUBSEQ as [IH | IH].
    + subst xs. right. rewrite length_app. simpl. lia.
    + right. rewrite length_app. simpl. lia.
  - destruct IHSUBSEQ as [IH | IH].
    + left; congruence.
    + right. do 2 rewrite length_app; simpl. lia.
Qed.

Lemma subseq_antisym xs ys
  (SUBSEQ1 : subseq xs ys)
  (SUBSEQ2 : subseq ys xs)
  : xs = ys.
Proof.
  apply proper_subseq_length in SUBSEQ1, SUBSEQ2.
  destruct SUBSEQ1; trivial. symmetry.
  destruct SUBSEQ2; trivial. lia.
Qed.

Lemma length_lt_wf (f := @length A)
  : well_founded (fun x => fun y => f x < f y)%nat.
Proof.
  intros x. remember (f x) as y eqn: y_eq_f_x.
  revert x y_eq_f_x. induction (lt_wf y) as [y' _ IH].
  intros x' hyp_eq. econstructor. intros x f_x_R_f_x'.
  subst y'. eapply IH; [exact f_x_R_f_x' | reflexivity].
Defined.

Lemma subseq_trans xs ys zs
  (SUBSEQ1 : subseq xs ys)
  (SUBSEQ2 : subseq ys zs)
  : subseq xs zs.
Proof.
  pose proof (COPY := SUBSEQ1). apply proper_subseq_length in COPY. destruct COPY as [-> | LENGTH1]; trivial.
  revert xs ys LENGTH1 SUBSEQ1 SUBSEQ2. induction (length_lt_wf zs) as [zs _ IH]; intros.
  pose proof (COPY := SUBSEQ2). apply proper_subseq_length in COPY. destruct COPY as [-> | LENGTH2]; trivial.
  destruct SUBSEQ2; eauto; rename xs0 into zs.
  - econstructor 2. eapply IH with (ys := zs); eauto.
    rewrite length_app; simpl; lia.
  - inversion SUBSEQ1; subst; eauto; rename z0 into w, ys0 into ws.
    + rewrite snoc_inv_iff in H1. destruct H1 as [-> ->]. econstructor 2.
      pose proof (COPY := SUBSEQ). apply proper_subseq_length in COPY. destruct COPY as [-> | LENGTH]; trivial.
      eapply IH with (ys := zs); eauto. rewrite length_app. simpl. lia.
    + rewrite snoc_inv_iff in H1. destruct H1 as [-> ->]. econstructor 3. rename xs0 into xs.
      pose proof (COPY := SUBSEQ). apply proper_subseq_length in COPY. destruct COPY as [-> | LENGTH]; trivial.
      eapply IH with (ys := zs); eauto. rewrite length_app. simpl. lia.
Qed.

#[global]
Instance subseq_PreOrder
  : PreOrder subseq.
Proof.
  split; [exact subseq_refl | exact subseq_trans].
Qed.

#[global]
Instance subseq_PartialOrder
  : PartialOrder eq subseq.
Proof.
  intros xs1 xs2. split; cbv.
  - intros ->; split; eapply subseq_refl.
  - intros [? ?]; eapply subseq_antisym; trivial.
Qed.

Definition strict_subseq (xs : list A) (ys : list A) : Prop :=
  xs <> ys /\ subseq xs ys.

Lemma strict_subseq_length_lt xs ys
  (SUBSEQ : strict_subseq xs ys)
  : (length xs < length ys)%nat.
Proof.
  destruct SUBSEQ as [NE SUBSEQ]. apply proper_subseq_length in SUBSEQ.
  destruct SUBSEQ as [EQ | SUBSEQ]; [contradiction | eauto].
Qed.

Lemma strict_subseq_well_founded
  : well_founded strict_subseq.
Proof.
  intros xs. induction (length_lt_wf xs) as [xs _ IH].
  econstructor. intros ys H_ys. eapply IH. now eapply strict_subseq_length_lt.
Qed.

End SUBSEQUENCE.

End L.

Class AxiomsForOpenSets@{u} (X : Type@{u}) (T : ensemble@{u} (ensemble@{u} X)) : Prop :=
  { full_isOpen
    : E.In@{u} E.full T
  ; unions_isOpen Os
    (OPENs : E.isSubsetOf@{u} Os T)
    : E.In@{u} (E.unions Os) T
  ; intersection_isOpen O1 O2
    (OPEN1 : E.In@{u} O1 T)
    (OPEN2 : E.In@{u} O2 T)
    : E.In@{u} (E.intersection O1 O2) T
  ; isOpen_compatWith_ext_eq O1 O2
    (OPEN : E.In@{u} O1 T)
    (EXT_EQ : forall x : X, E.In@{u} x O1 <-> E.In@{u} x O2)
    : E.In@{u} O2 T
  }.

Lemma empty_isOpen {X : Type} {T : ensemble (ensemble X)} `{TOPOLOGY : AxiomsForOpenSets X T}
  : E.empty \in T.
Proof.
  eapply isOpen_compatWith_ext_eq with (O1 := E.unions E.empty).
  - eapply unions_isOpen. ii. done!.
  - i. done!.
Qed.

(** Section BASIC_TOPOLOGY. *)

Class topology (A : Type) : Type :=
  { isOpen (O : ensemble A) : Prop
  ; AxiomsForTopology :: AxiomsForOpenSets A isOpen
  }.

#[global]
Add Parametric Morphism {A : Type} `{TOPOLOGY : topology A}
  : (@isOpen A TOPOLOGY) with signature (eqProp ==> iff)
  as isOpen_compatWith_eqProp.
Proof.
  ii; split; i; eapply isOpen_compatWith_ext_eq; done!.
Qed.

Lemma empty_in_T {A : Type} `{TOPOLOGY : topology A}
  : isOpen (@E.empty A).
Proof.
  eapply empty_isOpen.
Defined.

Lemma full_in_T {A : Type} `{TOPOLOGY : topology A}
  : isOpen (@E.full A).
Proof.
  eapply full_isOpen.
Defined.

Lemma unions_in_T {A : Type} `{TOPOLOGY : topology A} (Os : ensemble (ensemble A))
  (OPENs : forall O, O \in Os -> isOpen O)
  : isOpen (@E.unions A Os).
Proof.
  eapply unions_isOpen; eauto.
Defined.

Lemma intersection_in_T {A : Type} `{TOPOLOGY : topology A} (O1 : ensemble A) (O2 : ensemble A)
  (OPEN1 : isOpen O1)
  (OPEN2 : isOpen O2)
  : isOpen (@E.intersection A O1 O2).
Proof.
  eapply intersection_isOpen; eauto.
Defined.

#[global] Hint Resolve empty_in_T unions_in_T full_in_T intersection_in_T isOpen_compatWith_eqProp : simplication_hints.

Theorem Kuratowski_cl {X : Type} (cl : ensemble X -> ensemble X)
  (cl_isClosureOperator : isClosureOperator cl)
  (cl_preserves_empty : cl E.empty == E.empty)
  (cl_subadditive : forall U, forall V, cl (E.union U V) \subseteq E.union (cl U) (cl V))
  (cl_classic : forall U, cl (E.complement (E.complement U)) == E.complement (E.complement (cl U)))
  (T := fun O : ensemble X => let C := E.complement O in C == cl C)
  : AxiomsForOpenSets X T.
Proof.
  cbn zeta in T; subst T; ii; split; i.
  - red. eapply leProp_antisymmetry.
    + done!.
    + transitivity (cl E.empty).
      { eapply cl_op_monotonic. done!. }
      rewrite cl_preserves_empty. done!.
  - red. eapply leProp_antisymmetry.
    + eapply cl_op_extensive.
    + do 2 red in OPENs. intros x IN H_in. rewrite E.in_unions_iff in H_in. destruct H_in as [U [H_in H_IN]].
      pose proof (OPENs U H_IN) as H_EQ. revert x IN H_in. change (cl (E.complement (E.unions Os)) =< E.complement U).
      rewrite H_EQ. eapply cl_op_monotonic. intros x H_in CONTRA. done!.
  - red in OPEN1, OPEN2. red. eapply leProp_antisymmetry.
    + eapply cl_op_extensive.
    + transitivity (cl (E.complement (E.complement (E.union (E.complement O1) (E.complement O2))))).
      { eapply cl_op_monotonic. intros x IN IN'. contradiction IN'. left. intros H_inl. contradiction IN'. right. intros H_inr. contradiction IN. done!. }
      transitivity (E.complement (E.complement (E.union (E.complement O1) (E.complement O2)))).
      { rewrite cl_classic. intros x IN IN'. contradiction IN. intros CONTRA. contradiction IN'.
        clear IN IN'. rewrite OPEN1, OPEN2. revert x CONTRA. eapply cl_subadditive.
      }
      done!.
  - red. red in OPEN. change (O1 == O2) in EXT_EQ. rewrite <- EXT_EQ. exact OPEN.
Qed.

Definition isContinuous {A : Type} {B : Type} {A_topology : topology A} {B_topology : topology B} (f : A -> B) : Prop :=
  forall Y : ensemble B, isOpen Y -> isOpen (E.preimage f Y).

Section COD_TOP.

Context {DOM : Type} {COD : Type} {TOPOLOGY : topology DOM} (f : DOM -> COD).

Definition OpenSets_in_COD : ensemble (ensemble COD) :=
  fun U => isOpen (E.preimage f U).

#[local] Opaque isOpen.
#[local] Hint Resolve full_isOpen unions_isOpen intersection_isOpen : core.
#[local] Hint Unfold E.In : core.

#[global]
Instance OpenSets_in_COD_satisfiesAxiomsForOpenSets
  : AxiomsForOpenSets COD OpenSets_in_COD.
Proof with reflexivity || eauto.
  unfold OpenSets_in_COD. destruct TOPOLOGY.(AxiomsForTopology) as [H1 H2 H3 H4]. split.
  - red. eapply isOpen_compatWith_ext_eq with (O1 := E.full)... intros x. split; intros IN... econs...
  - i. red. do 2 red in OPENs. eapply isOpen_compatWith_ext_eq with (O1 := E.unions (fun U => exists O, O \in Os /\ isOpen U /\ E.preimage f O == U)).
    + eapply H2. intros U H_U. red in H_U. destruct H_U as (O & O_in & U_in & EQ). eapply isOpen_compatWith_ext_eq with (O1 := E.preimage f O)...
    + intros x. split; intros H_IN.
      * destruct H_IN as [U H_IN U_IN]. red in U_IN. destruct U_IN as (O & O_IN & U_IN & H_EQ). rewrite <- H_EQ in H_IN. econs... done!.
      * destruct H_IN as [O -> H_IN]. destruct H_IN as [O H_IN O_IN]. exists (E.preimage f O); done!.
  - i. red in OPEN1, OPEN2 |- *. eapply isOpen_compatWith_ext_eq with (O1 := E.intersection (E.preimage f O1) (E.preimage f O2)).
    + eapply intersection_isOpen...
    + intros x; split; intros H_IN; ss!.
  - i. red in OPEN |- *. change (O1 == O2) in EXT_EQ. eapply isOpen_compatWith_ext_eq with (O1 := E.preimage f O1)... intros x. rewrite EXT_EQ...
Qed.

End COD_TOP.

Section SUBSPACE_TOPOLOGY.

#[local] Opaque "\in".

#[global, program]
Instance Subspace_topology {A : Type} {P : A -> Prop} (TOPOLOGY : topology A) : topology (@sig A P) :=
  { isOpen U := exists O : ensemble A, isOpen O /\ (forall z, proj1_sig z \in O <-> z \in U) }.
Next Obligation.
  ii. split.
  - exists E.full. done!.
  - i. exists (E.unions (Os >>= (fun U => fun O => (forall z, proj1_sig z \in O <-> z \in U) /\ isOpen O))). split.
    { eapply unions_in_T. done!. }
    { done!. }
  - i. ss!. exists (E.intersection x0 x). split.
    { eapply intersection_in_T; done!. }
    { done!. }
  - done!.
Qed.

Lemma proj1_sig_isContinuous {A : Type} {TOPOLOGY : topology A} (P : A -> Prop)
  : @isContinuous (@sig A P) A (Subspace_topology TOPOLOGY) TOPOLOGY (@proj1_sig A P).
Proof.
  intros Y OPEN. simpl. exists Y; done!.
Qed.

End SUBSPACE_TOPOLOGY.

#[universes(template)]
Class isQuotientOf (Q : Type) (X : Type) {SETOID : isSetoid X} : Type :=
  { prj : X -> Q
  ; prj_eq (x1 : X) (x2 : X) (EQUIV : x1 == x2) : prj x1 = prj x2
  ; rec {Y : Type} (f : X -> Y) (f_cong : forall x1, forall x2, x1 == x2 -> f x1 = f x2) : Q -> Y
  ; rec_compute {Y : Type} (f : X -> Y) (f_cong : forall x1, forall x2, x1 == x2 -> f x1 = f x2)
    : forall x, rec f f_cong (prj x) = f x
  ; rec_unique {Y : Type} (f : X -> Y) (f_cong : forall x1, forall x2, x1 == x2 -> f x1 = f x2)
    : forall rec', (forall x, rec' (prj x) = f x) -> (forall q, rec' q = rec f f_cong q)
  }.

Module Quot.

Section QuotientTopology.

Context {X : Type} {TOPOLOGY : topology X} {SETOID : isSetoid X} {Q : Type} {QUOTIENT : isQuotientOf Q X}.

#[global]
Instance QuotientTopology : topology Q :=
  { isOpen := OpenSets_in_COD prj
  ; AxiomsForTopology := OpenSets_in_COD_satisfiesAxiomsForOpenSets prj
  }.

End QuotientTopology.

End Quot.

(** End BASIC_TOPOLOGY. *)

#[universes(template), projections(primitive)]
Class Equipotent (A : Type) (B : Type) : Type :=
  { _rarr (x : A) : B
  ; _larr (y : B) : A
  ; _rarr_larr y : _rarr (_larr y) = y
  ; _larr_rarr x : _larr (_rarr x) = x
  }.

#[global] Hint Rewrite @_rarr_larr : simplication_hints.
#[global] Hint Rewrite @_larr_rarr : simplication_hints.

Section Equipotent_instances.

#[local] Obligation Tactic := intros; simpl.

#[local]
Instance Equipotent_Reflexive {A : Type} : Equipotent A A :=
  { _rarr (x : A) := x
  ; _larr (x : A) := x
  ; _rarr_larr (x : A) := eq_refl
  ; _larr_rarr (x : A) := eq_refl
  }.

#[local]
Instance Equipotent_Symmetric {A : Type} {B : Type} (A_eq_B : Equipotent A B) : Equipotent B A :=
  { _rarr (y : B) := _larr y
  ; _larr (x : A) := _rarr x
  ; _rarr_larr (x : A) := _larr_rarr x
  ; _larr_rarr (y : B) := _rarr_larr y
  }.

#[local, program]
Instance Equipotent_Transitive {A : Type} {B : Type} {C : Type} (A_eq_B : Equipotent A B) (B_eq_C : Equipotent B C) : Equipotent A C :=
  { _rarr (x : A) := _rarr (_rarr x)
  ; _larr (z : C) := _larr (_larr z)
  }.
Next Obligation.
  rewrite _rarr_larr with (y := _larr y). eapply _rarr_larr.
Defined.
Next Obligation.
  rewrite _larr_rarr with (x := _rarr x). eapply _larr_rarr.
Defined.

End Equipotent_instances.

Class equipotent (A : Type) (B : Type) : Prop :=
  equipotent_proof : inhabited (Equipotent A B).
