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
Definition commutes@{d c} {Src : Type@{d}} {Tgt : Type@{c}} (REL_Src : Src -> Src -> Prop) (REL_Tgt : Tgt -> Tgt -> Prop) (MAP : Src -> Tgt -> Prop) : Prop :=
  forall x : Src, forall y' : Tgt, (exists x' : Src, REL_Src x x' /\ MAP x' y') <-> (exists y : Tgt, MAP x y /\ REL_Tgt y y').

Class isLawfulCategory (CAT : isCategory) {SETOID : forall Dom : CAT.(ob), forall Cod : CAT.(ob), isSetoid (CAT.(hom) Dom Cod)} : Prop :=
  { compose_assoc {A : CAT.(ob)} {B : CAT.(ob)} {C : CAT.(ob)} {D : CAT.(ob)} (h : CAT.(hom) C D) (g : CAT.(hom) B C) (f : CAT.(hom) A B)
    : compose h (compose g f) == compose (compose h g) f
  ; compose_id_l {A : CAT.(ob)} {B : CAT.(ob)} (f : CAT.(hom) A B)
    : compose id f == f
  ; compose_id_r {A : CAT.(ob)} {B : CAT.(ob)} (f : CAT.(hom) A B)
    : compose f id == f
  }.

Class isLawfulCovariantFunctor {Dom : isCategory} {Cod : isCategory} {SETOID : forall X : Dom.(ob), forall Y : Dom.(ob), isSetoid (Dom.(hom) X Y)} (FUNCTOR : isCovariantFunctor Dom Cod) {liftSETOID : forall X : Dom.(ob), forall Y : Dom.(ob), isSetoid (Dom.(hom) X Y) -> isSetoid (Cod.(hom) (fmap_ob X) (fmap_ob Y))} : Prop :=
  { fmap_compose {A : Dom.(ob)} {B : Dom.(ob)} {C : Dom.(ob)} (g : Dom.(hom) B C) (f : Dom.(hom) A B)
    : fmap_hom (Dom.(@compose) A B C g f) == compose (fmap_hom g) (fmap_hom f)
  ; fmap_id {A : Dom.(ob)}
    : fmap_hom (Dom.(@id) A) == id
  ; fmap_comm {A : Dom.(ob)} {B : Dom.(ob)}
    : commutes eqProp eqProp (fun f : Dom.(hom) A B => fun fmap_f : Cod.(hom) (fmap_ob A) (fmap_ob B) => fmap_hom f == fmap_f)
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

#[local]
Instance Setoid_on_Hask (Dom : Hask.(CAT.ob)) (Cod : Hask.(CAT.ob)) : isSetoid (Hask.(CAT.hom) Dom Cod) :=
  pi_isSetoid (fun _ : Dom => mkSetoid_from_eq).

#[global]
Instance Hask_isLawfulCategory
  : CAT.isLawfulCategory Hask (SETOID := Setoid_on_Hask).
Proof.
  split; cbv; reflexivity.
Qed.

#[local, universes(polymorphic=yes)]
Instance Functor_isCovariantFunctor@{u1 v1 u2 v2} (F : Type@{v1} -> Type@{v2}) {F_isFunctor : isFunctor@{v1 v2} F} : CAT.isCovariantFunctor@{u1 v1 u2 v2} Hask@{u2 v2} Hask@{u2 v2} :=
  { fmap_ob := F
  ; fmap_hom {A : Type@{v1}} {B : Type@{v1}} (f : A -> B) := fmap f
  }.

#[global]
Instance Functor_isCovariantFunctor_good {F : Type -> Type} {F_isFunctor : isFunctor F} {F_isSetoid1 : isSetoid1 F}
  (FUNCTOR_LAWS : FunctorLaws F (FUNCTOR := F_isFunctor) (SETOID1 := F_isSetoid1))
  : CAT.isLawfulCovariantFunctor (SETOID := Setoid_on_Hask) (Functor_isCovariantFunctor F) (liftSETOID := fun X : Type => fun Y : Type => fun _ : isSetoid (X -> Y) => pi_isSetoid (fun _ : F X => liftSetoid1 (isSetoid1 := F_isSetoid1) Y mkSetoid_from_eq)).
Proof with eauto with *.
  destruct FUNCTOR_LAWS. split; cbn in fmap_compose, fmap_id |- *; intros.
  - eapply fmap_compose.
  - eapply fmap_id.
  - red. intros f fmap_f. split.
    + intros (f'&f_EQ&fmap_f_EQ). exists fmap_f. split...
      intros x. rewrite <- fmap_f_EQ with (x := x). eapply fmap_lifts_ext_eq...
    + intros (fmap_f'&fmap_f_EQ&fmap_f_EQ'). exists f. split...
      intros x. rewrite -> fmap_f_EQ with (x := x)...
Qed.

#[local, universes(polymorphic=yes)]
Instance CovariantFunctor_isFunctor@{u1 v1 u2 v2} (FUNCTOR : CAT.isCovariantFunctor@{u1 v1 u2 v2} Hask@{u1 v1} Hask@{u2 v2}) : isFunctor@{v1 v2} CAT.fmap_ob :=
  fun A : Type@{v1} => fun B : Type@{v1} => fun f : A -> B => CAT.fmap_hom@{u1 v1 u2 v2} f.

#[global]
Instance CovariantFunctor_isFunctor_good {FUNCTOR : CAT.isCovariantFunctor Hask Hask}
  (FUNCTOR_LAWS : CAT.isLawfulCovariantFunctor (SETOID := Setoid_on_Hask) FUNCTOR (liftSETOID := fun X : Type => fun Y : Type => fun _ : isSetoid (X -> Y) => Setoid_on_Hask (FUNCTOR.(CAT.fmap_ob) X) (FUNCTOR.(CAT.fmap_ob) Y)))
  : FunctorLaws CAT.fmap_ob (FUNCTOR := CovariantFunctor_isFunctor FUNCTOR) (SETOID1 := fun X : Type => fun _ : isSetoid X => mkSetoid_from_eq).
Proof with eauto with *.
  split; intros.
  - intros x1 x2; cbv; congruence.
  - unfold fmap. unfold CovariantFunctor_isFunctor. rewrite CAT.fmap_compose. reflexivity.
  - unfold fmap. unfold CovariantFunctor_isFunctor. rewrite CAT.fmap_id. reflexivity.
  - exploit (proj1 (CAT.fmap_comm f1 (fmap f2))).
    + exists f2. split... reflexivity.
    + intros (fmap_f&EQ1&EQ2). now rewrite -> EQ1, <- EQ2...
Qed.

End HASK.
