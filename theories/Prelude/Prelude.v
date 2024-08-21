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
Instance product_isSetoid {A : Type} {B : A -> Type} `(SETOID : forall x : A, isSetoid (B x)) : isSetoid (forall x : A, B x) :=
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

Lemma PreOrder_iff {A : Type} (R : A -> A -> Prop)
  : PreOrder R <-> (forall x, forall y, R x y <-> (forall z, R z x -> R z y)).
Proof.
  firstorder.
Qed.

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
Definition product_isPoset {A : Type} {B : A -> Type} `(POSET : forall x : A, isPoset (B x)) : isPoset (forall x : A, B x) :=
  {| leProp f g := forall x, f x =< g x; Poset_isSetoid := product_isSetoid (fun x : A => (POSET x).(Poset_isSetoid)) |}.
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
