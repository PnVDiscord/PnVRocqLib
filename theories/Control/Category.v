Require Import PnV.Prelude.Prelude.
Require Import PnV.Data.Vector.
Require Import PnV.Math.ThN.

#[local] Set Printing Universes.

Notation "E '~~>' F" := (forall X : Type, E X -> F X) (at level 95, right associativity) : type_scope.

Module CAT.

#[local] Obligation Tactic := i.

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

Definition fin (n : nat) : isCategory@{Set Set} :=
  {|
    ob := Fin.t n;
    hom i1 i2 := Fin.evalFin i1 <= Fin.evalFin i2;
    compose i i' i'' H_LE' H_LE := le_transitivity H_LE H_LE';
    id i := le_reflexivity;
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
  { map_ob : Dom.(ob) -> Cod.(ob)
  ; map_hom {A} {B} (f : Dom.(hom) A B) : Cod.(hom) (map_ob A) (map_ob B)
  }.

#[universes(polymorphic=yes)]
Definition FunctorCategory@{u1 v1 u2 v2 u3 v3} (Dom : isCategory@{u1 v1}) (Cod : isCategory@{u2 v2}) : isCategory@{u3 v3} :=
  {|
    ob := isCovariantFunctor@{u1 v1 u2 v2} Dom Cod;
    hom F G := forall X : Dom.(ob), Cod.(hom) (F.(map_ob) X) (G.(map_ob) X);
    compose _ _ _ eta2 eta1 := fun X : Dom.(ob) => Cod.(compose) (eta2 X) (eta1 X);
    id _ := fun X : Dom.(ob) => Cod.(id);
  |}.

Section LAW.

#[universes(polymorphic=yes)]
Definition commutes@{d c} {Src : Type@{d}} {Tgt : Type@{c}} (REL_Src : Src -> Src -> Prop) (REL_Tgt : Tgt -> Tgt -> Prop) (MAP : Src -> Tgt -> Prop) : Prop :=
  forall x : Src, forall y' : Tgt, (exists x' : Src, REL_Src x x' /\ MAP x' y') <-> (exists y : Tgt, MAP x y /\ REL_Tgt y y').

Class isLawfulCategory (CAT : isCategory) {SETOID : forall Dom : CAT.(ob), forall Cod : CAT.(ob), isSetoid (CAT.(hom) Dom Cod)} : Prop :=
  { compose_compatWith_eqProp {A : CAT.(ob)} {B : CAT.(ob)} {C : CAT.(ob)} :: eqPropCompatible2 (CAT.(@compose) A B C)
  ; compose_assoc {A : CAT.(ob)} {B : CAT.(ob)} {C : CAT.(ob)} {D : CAT.(ob)} (h : CAT.(hom) C D) (g : CAT.(hom) B C) (f : CAT.(hom) A B)
    : compose h (compose g f) == compose (compose h g) f
  ; compose_id_l {A : CAT.(ob)} {B : CAT.(ob)} (f : CAT.(hom) A B)
    : compose id f == f
  ; compose_id_r {A : CAT.(ob)} {B : CAT.(ob)} (f : CAT.(hom) A B)
    : compose f id == f
  }.

Class isLawfulCovariantFunctor {Dom : isCategory} {Cod : isCategory} (FUNCTOR : isCovariantFunctor Dom Cod) {SETOID : forall X : Dom.(ob), forall Y : Dom.(ob), isSetoid (Dom.(hom) X Y)} {liftSETOID : forall X : Dom.(ob), forall Y : Dom.(ob), isSetoid (Dom.(hom) X Y) -> isSetoid (Cod.(hom) (map_ob X) (map_ob Y))} : Prop :=
  { fmap_compose {A : Dom.(ob)} {B : Dom.(ob)} {C : Dom.(ob)} (g : Dom.(hom) B C) (f : Dom.(hom) A B)
    : map_hom (Dom.(@compose) A B C g f) == compose (map_hom g) (map_hom f)
  ; fmap_id {A : Dom.(ob)}
    : map_hom (Dom.(@id) A) == id
  ; fmap_comm {A : Dom.(ob)} {B : Dom.(ob)}
    : commutes eqProp eqProp (fun f : Dom.(hom) A B => fun fmap_f : Cod.(hom) (map_ob A) (map_ob B) => map_hom f == fmap_f)
  }.

Lemma op_isLawfulCategory {CAT : isCategory} {SETOID : forall Dom : CAT.(ob), forall Cod : CAT.(ob), isSetoid (CAT.(hom) Dom Cod)}
  (CATEGORY_LAW : isLawfulCategory CAT (SETOID := SETOID))
  : isLawfulCategory (op CAT) (SETOID := fun Cod : CAT.(ob) => fun Dom : CAT.(ob) => SETOID Dom Cod).
Proof.
  split; cbn; ii.
  - now rewrite compose_compatWith_eqProp.
  - now rewrite compose_assoc.
  - now rewrite compose_id_r.
  - now rewrite compose_id_l.
Qed.

End LAW.

End CAT.

Section HASK.

Import CAT.

#[local, universes(polymorphic=yes)]
Instance Hask@{u v} : isCategory@{u v} :=
  { ob := Type@{v}
  ; hom (D : Type@{v}) (C : Type@{v}) := D -> C
  ; compose {A : Type@{v}} {B : Type@{v}} {C : Type@{v}} (g : B -> C) (f : A -> B) := fun x : A => g (f x)
  ; id {A : Type@{v}} := fun x : A => x
  }.

#[local]
Instance Setoid_on_Hask (Dom : Hask.(ob)) (Cod : Hask.(ob)) : isSetoid (Hask.(hom) Dom Cod) :=
  pi_isSetoid (fun _ : Dom => mkSetoid_from_eq).

#[global]
Instance Hask_isLawfulCategory
  : isLawfulCategory Hask (SETOID := Setoid_on_Hask).
Proof.
  split; cbv; congruence.
Qed.

#[local, universes(polymorphic=yes)]
Instance Functor_isCovariantFunctor@{u1 v1 u2 v2} (F : Type@{v1} -> Type@{v2}) {F_isFunctor : isFunctor@{v1 v2} F} : isCovariantFunctor@{u1 v1 u2 v2} Hask@{u1 v1} Hask@{u2 v2} :=
  { map_ob := F
  ; map_hom := @fmap@{v1 v2} F F_isFunctor
  }.

#[global]
Instance Functor_isCovariantFunctor_good {F : Type -> Type} {F_isFunctor : isFunctor F} {F_isSetoid1 : isSetoid1 F}
  (FUNCTOR_LAWS : FunctorLaws F (FUNCTOR := F_isFunctor) (SETOID1 := F_isSetoid1))
  : isLawfulCovariantFunctor (Functor_isCovariantFunctor F) (SETOID := Setoid_on_Hask) (liftSETOID := fun X : Type => fun Y : Type => fun _ : isSetoid (X -> Y) => pi_isSetoid (fun _ : F X => liftSetoid1 (isSetoid1 := F_isSetoid1) Y mkSetoid_from_eq)).
Proof with eauto with *.
  split; cbn; i.
  - eapply Prelude.fmap_compose.
  - eapply Prelude.fmap_id.
  - red. intros f fmap_f. split.
    + intros (f'&f_EQ&fmap_f_EQ). exists fmap_f. split...
      intros x. rewrite <- fmap_f_EQ with (x := x). eapply Prelude.fmap_lifts_ext_eq...
    + intros (fmap_f'&fmap_f_EQ&fmap_f_EQ'). exists f. split...
      intros x. rewrite -> fmap_f_EQ with (x := x)...
Qed.

#[local, universes(polymorphic=yes)]
Instance CovariantFunctor_isFunctor@{u1 v1 u2 v2} (F : isCovariantFunctor@{u1 v1 u2 v2} Hask@{u1 v1} Hask@{u2 v2}) : isFunctor@{v1 v2} F.(map_ob) :=
  @map_hom@{u1 v1 u2 v2} Hask@{u1 v1} Hask@{u2 v2} F.

Theorem CovariantFunctor_isFunctor_good {F : isCovariantFunctor Hask Hask}
  : FunctorLaws map_ob (FUNCTOR := CovariantFunctor_isFunctor F) (SETOID1 := fun X : Type => fun _ : isSetoid X => mkSetoid_from_eq) <-> isLawfulCovariantFunctor F (SETOID := Setoid_on_Hask) (liftSETOID := fun X : Type => fun Y : Type => fun _ : isSetoid (X -> Y) => Setoid_on_Hask (F.(map_ob) X) (F.(map_ob) Y)).
Proof with reflexivity || eauto with *.
  split; intros LAW.
  - destruct F as [F fmap]; split; i.
    + exact (@Prelude.fmap_compose F _ _ LAW A B C f g).
    + exact (@Prelude.fmap_id F _ _ LAW A).
    + intros f fmap_f'. split.
      * intros (f'&f_EQ&fmap_f_EQ). exists (map_hom f); split...
        rewrite <- fmap_f_EQ. exact (@Prelude.fmap_lifts_ext_eq F _ _ LAW _ _ _ _ f_EQ).
      * intros (fmap_f&fmap_f_EQ&fmap_f_EQ'). exists f; split...
        rewrite -> fmap_f_EQ, <- fmap_f_EQ'...
  - split; i.
    + cbv; intros x1 x2 ->...
    + unfold fmap. unfold CovariantFunctor_isFunctor. rewrite CAT.fmap_compose...
    + unfold fmap. unfold CovariantFunctor_isFunctor. rewrite CAT.fmap_id...
    + exploit (proj1 (CAT.fmap_comm f1 (fmap f2))).
      { exists f2; split... }
      intros (fmap_f&EQ1&EQ2). rewrite -> EQ1, <- EQ2...
Qed.

End HASK.

Section SLICE.

#[local] Obligation Tactic := idtac.

Import CAT.

#[local, program]
Instance SliceCategory {CAT : isCategory} {SETOID : forall Dom : CAT.(ob), forall Cod : CAT.(ob), isSetoid (CAT.(hom) Dom Cod)} {CATEGORY_LAW : isLawfulCategory CAT (SETOID := SETOID)} (C : CAT.(ob)) : isCategory :=
  { ob := { D : CAT.(ob) & CAT.(hom) D C }
  ; hom X Y := { arr : CAT.(hom) (projT1 X) (projT1 Y) | projT2 X == CAT.(compose) (projT2 Y) arr }
  ; compose {X} {Y} {Z} arr' arr := @exist _ _ (CAT.(compose) (proj1_sig arr') (proj1_sig arr)) _
  ; id {X} := @exist _ _ (CAT.(id)) _
  }.
Next Obligation.
  intros CAT SETOID CATEGORY_LAW C [X f] [Y g] [Z h] [arr' EQ'] [arr EQ]; simpl in *.
  rewrite -> compose_assoc. rewrite -> EQ. now eapply compose_compatWith_eqProp.
Qed.
Next Obligation.
  intros CAT SETOID CATEGORY_LAW C [X f]; simpl in *.
  now rewrite -> compose_id_r.
Qed.

#[local]
Instance SliceCategory_good (CAT : isCategory) (SETOID : forall Dom : CAT.(ob), forall Cod : CAT.(ob), isSetoid (CAT.(hom) Dom Cod)) (C : CAT.(ob))
 (CATEGORY_LAW : isLawfulCategory CAT (SETOID := SETOID))
  : isLawfulCategory (SliceCategory (CAT := CAT) (SETOID := SETOID) (CATEGORY_LAW := CATEGORY_LAW) C) (SETOID := fun Dom => fun Cod => @subSetoid _ (SETOID (projT1 Dom) (projT1 Cod)) _).
Proof with eauto with *.
  split; cbn.
  - intros [X f] [Y g] [Z h] [arr2' EQ2'] [arr2 EQ2] [arr1' EQ1'] [arr1 EQ1]; simpl in *; intros arr2_EQ arr1_EQ. eapply compose_compatWith_eqProp...
  - intros [X f] [Y g] [Z h] [W i]; simpl in *; intros [arr'' EQ''] [arr' EQ'] [arr EQ]; simpl in *. eapply compose_assoc.
  - intros [X f] [Y g]; simpl in *; intros [arr EQ]; simpl in *. eapply compose_id_l.
  - intros [X f] [Y g]; simpl in *; intros [arr EQ]; simpl in *. eapply compose_id_r.
Qed.

End SLICE.

Section CAYLEY.

#[local] Obligation Tactic := i.

Import CAT.

#[local]
Instance CayleyFunctor (CAT : isCategory) : isCovariantFunctor CAT Hask :=
  { map_ob (C : CAT.(ob)) := { D : CAT.(ob) & CAT.(hom) D C }
  ; map_hom {A : CAT.(ob)} {B : CAT.(ob)} (f : CAT.(hom) A B) := fun g : { X : CAT.(ob) & CAT.(hom) X A } => @existT CAT.(ob) (fun Y : CAT.(ob) => CAT.(hom) Y B) (projT1 g) (compose f (projT2 g))
  }.

#[local, universes(polymorphic=yes)]
Instance CayleyCategory@{u v w} (CAT : isCategory@{u v}) : isCategory@{u w} :=
  { ob := CAT.(ob)
  ; hom D C := forall r : CAT.(ob), CAT.(hom) C r -> CAT.(hom) D r
  ; compose _ _ _ G F := fun r => fun X => F r (G r X)
  ; id _ := fun r => fun X => X
  }.

#[local, universes(polymorphic=yes)]
Instance toCayleyCategory_isCovariantFunctor@{u v w} (CAT : isCategory@{u v}) : isCovariantFunctor@{u v u w} CAT (CayleyCategory@{u v w} CAT) :=
  { map_ob (A : CAT.(ob)) := A
  ; map_hom {A : CAT.(ob)} {B : CAT.(ob)} (f : CAT.(hom) A B) := fun C : CAT.(ob) => fun g : CAT.(hom) B C => CAT.(compose) g f
  }.

End CAYLEY.
