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

#[universes(polymorphic=yes)]
Class isCovariantFunctor@{u1 v1 u2 v2} (Dom : isCategory@{u1 v1}) (Cod : isCategory@{u2 v2}) : Type :=
  { fmap_ob : Dom.(ob) -> Cod.(ob)
  ; fmap_hom {A} {B} (f : Dom.(hom) A B) : Cod.(hom) (fmap_ob A) (fmap_ob B)
  }.

Section LAW.

#[universes(polymorphic=yes)]
Class isLawfulCategory@{u v} (CAT : isCategory@{u v}) {SETOID : forall Dom : CAT.(ob), forall Cod : CAT.(ob), isSetoid (CAT.(hom) Dom Cod)} : Prop :=
  { compose_assoc {A} {B} {C} {D} (f : CAT.(hom) A B) (g : CAT.(hom) B C) (h : CAT.(hom) C D)
    : compose h (compose g f) == compose (compose h g) f
  ; compose_id_l {A} {B} (f : CAT.(hom) A B)
    : compose id f == f
  ; compose_id_r {A} {B} (f : CAT.(hom) A B)
    : compose f id == f
  }.

#[universes(polymorphic=yes)]
Class isLawfulCovariantFunctor@{u1 v1 u2 v2} {Dom : isCategory@{u1 v1}} {Cod : isCategory@{u2 v2}} {SETOID : forall X : Dom.(ob), forall Y : Dom.(ob), isSetoid (Dom.(hom) X Y)} (FUNCTOR : isCovariantFunctor@{u1 v1 u2 v2} Dom Cod) {liftSETOID : forall X : Dom.(ob), forall Y : Dom.(ob), isSetoid (Dom.(hom) X Y) -> isSetoid (Cod.(hom) (fmap_ob X) (fmap_ob Y))} : Prop :=
  { fmap_compose {A} {B} {C} (f : Dom.(hom) A B) (g : Dom.(hom) B C)
    : fmap_hom (Dom.(@compose) A B C g f) == compose (fmap_hom g) (fmap_hom f)
  ; fmap_id {A}
    : fmap_hom (Dom.(@id) A) == id
  ; fmap_lifts_ext_eq {A} {B} (f : Dom.(hom) A B) (f' : Dom.(hom) A B)
    (f_EQ : f == f')
    : fmap_hom f == fmap_hom f'
  }.

End LAW.

End CAT.

Section HASK.

#[local, universes(polymorphic=yes)]
Instance Hask@{u v} : CAT.isCategory@{u v} :=
  { ob := Type@{v}
  ; hom (D : Type@{v}) (C : Type@{v}) := D -> C
  ; compose {A : Type@{v}} {B : Type@{v}} {C : Type@{v}} (g : B -> C) (f : A -> B) := fun x : A => g (f x)
  ; id {A : Type@{v}} := fun x : A => x
  }.

#[local, universes(polymorphic=yes)]
Instance Setoid_on_Hask@{u v} (Dom : Hask@{u v}.(CAT.ob)) (Cod : Hask@{u v}.(CAT.ob)) : isSetoid (Hask@{u v}.(CAT.hom) Dom Cod) :=
  pi_isSetoid (fun _ => mkSetoid_from_eq).

#[local, universes(polymorphic=yes)]
Instance Functor_CAT_Functor@{u1 v1 u2 v2} (F : Type@{v1} -> Type@{v2}) {F_isFunctor : isFunctor@{v1 v2} F} : CAT.isCovariantFunctor@{u1 v1 u2 v2} Hask@{u2 v2} Hask@{u2 v2} :=
  { fmap_ob := F
  ; fmap_hom {A : Type@{v1}} {B : Type@{v1}} (f : A -> B) := fmap f
  }.

#[global]
Instance Functor_CAT_Functor_good {F : Type -> Type} {F_isFunctor : isFunctor F} {F_isSetoid1 : isSetoid1 F}
  (FUNCTOR_LAWS : FunctorLaws F)
  : CAT.isLawfulCovariantFunctor (SETOID := Setoid_on_Hask) (Functor_CAT_Functor F) (liftSETOID := fun X : Type => fun Y : Type => fun SETOID : isSetoid (X -> Y) => pi_isSetoid (fun _ => liftSetoid1 (isSetoid1 := F_isSetoid1) _ mkSetoid_from_eq)).
Proof.
  destruct FUNCTOR_LAWS. split; cbn in fmap_compose, fmap_id |- *; intros.
  - eapply fmap_compose.
  - eapply fmap_id.
  - eapply fmap_lifts_ext_eq. exact f_EQ.
Qed.

End HASK.
