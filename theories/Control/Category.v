Require Import PnV.Prelude.Prelude.

Notation "E '~~>' F" := (forall X : Type, E X -> F X) (at level 95, right associativity) : type_scope.

Module CAT.

#[universes(polymorphic=yes)]
Class isCategory@{u v} : Type :=
  { ob : Type@{u}
  ; hom (D : ob) (C : ob) : Type@{v}
  ; compose {A} {B} {C} (g : hom B C) (f : hom A B) : hom A C
  ; id {A} : hom A A
  }.

#[universes(polymorphic=yes)]
Definition op@{u v} (CAT : isCategory@{u v}) : isCategory@{u v} :=
  {|
    ob := CAT.(ob);
    hom (Cod : CAT.(ob)) (Dom : CAT.(ob)) := CAT.(hom) Dom Cod;
    compose (C : CAT.(ob)) (B : CAT.(ob)) (A : CAT.(ob)) (f : CAT.(hom) A B) (g : CAT.(hom) B C) := CAT.(@compose) A B C g f;
    id (A : CAT.(ob)) := CAT.(@id) A;
  |}.

#[universes(polymorphic=yes)]
Class hasCoproduct@{u v} (C : isCategory@{u v}) : Type :=
  { sum (X : C.(ob)) (Y : C.(ob)) : C.(ob)
  ; inl {X : C.(ob)} {Y : C.(ob)} : C.(hom) X (sum X Y)
  ; inr {X : C.(ob)} {Y : C.(ob)} : C.(hom) Y (sum X Y)
  ; case {X : C.(ob)} {Y : C.(ob)} {Z : C.(ob)} (f : C.(hom) X Z) (g : C.(hom) Y Z) : C.(hom) (sum X Y) Z
  }.

#[universes(polymorphic=yes)]
Class hasInitial@{u v} (C : isCategory@{u v}) : Type :=
  { void : C.(ob)
  ; exfalso {X : C.(ob)} : C.(hom) void X
  }.

End CAT.

Section HASK.

#[local, universes(polymorphic=yes)]
Instance Hask@{u v} : CAT.isCategory@{u v} :=
  { ob := Type@{v}
  ; hom (D : Type@{v}) (C : Type@{v}) := D -> C
  ; compose {A : Type@{v}} {B : Type@{v}} {C : Type@{v}} (g : B -> C) (f : A -> B) := fun x : A => g (f x)
  ; id {A : Type@{v}} := fun x : A => x
  }.

End HASK.
