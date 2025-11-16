Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Data.Aczel.

Module Type SetTheoreticConcepts.

Parameter V : Type@{Set_V}.

Parameter _eq : V -> V -> Prop.

Parameter _in : V -> V -> Prop.

Parameter _subseteq : V -> V -> Prop.

Parameter _comprehension : (V -> Prop) -> V -> V.

Parameter _emptyset : V.

Parameter _powerset : V -> V.

Parameter _unordered_pair : V -> V -> V.

Parameter _unions : V -> V.

Parameter Ord : Type@{Set_V}.

Parameter _Ord_eq : Ord -> Ord -> Prop.

Parameter _Ord_lt : Ord -> Ord -> Prop.

Parameter _Ord_le : Ord -> Ord -> Prop.

Parameter _zer : Ord.

Parameter _suc : Ord -> Ord.

Parameter _sup : forall A : Type@{Set_u}, (A -> Ord) -> Ord.

Parameter _transfinite_rec : forall D : Type@{Set_V}, (D -> D) -> (forall A : Type@{Set_u}, (A -> D) -> D) -> Ord -> D.

Parameter _Ord_add : Ord -> Ord -> Ord.

Parameter _Ord_mul : Ord -> Ord -> Ord.

Parameter Card : Type@{Set_V}.

Parameter _Card_eq : Card -> Card -> Prop.

Parameter _Card_lt : Card -> Card -> Prop.

Parameter _Card_le : Card -> Card -> Prop.

Parameter _card : forall A : Type@{Set_u}, isSetoid A -> Card.

Parameter _Card_add : Card -> Card -> Card.

Parameter _Card_mul : Card -> Card -> Card.

Parameter _Card_exp : Card -> Card -> Card.

End SetTheoreticConcepts.

Module TypeTheoreticImplementation <: SetTheoreticConcepts.

Definition V : Type@{Set_V} :=
  @Tree.

Definition _eq : V -> V -> Prop :=
  @eqTree.

Definition _in : V -> V -> Prop :=
  @member.

Definition _subseteq : V -> V -> Prop :=
  @isSubsetOf.

Definition _comprehension : (V -> Prop) -> V -> V :=
  @filter.

Definition _emptyset : V :=
  @empty.

Definition _powerset : V -> V :=
  @power.

Definition _unordered_pair : V -> V -> V :=
  @upair.

Definition _unions : V -> V :=
  @unions.

Module Ord.

Definition t : Type@{Set_V} :=
  @Tree.

Section TRANSFINITE.

Context {D : Type@{Set_V}}.

Section FIRST.

Context (suc : D -> D) (bigjoin : forall A : Type@{Set_u}, (A -> D) -> D).

Fixpoint transfinite_rec (t : Ord.t) {struct t} : D :=
  match t with
  | mkNode cs ts => bigjoin cs (fun c : cs => suc (transfinite_rec (ts c)))
  end.

End FIRST.

Section SECOND.

Context (base : D) (suc : D -> D) (bigjoin : forall A : Type@{Set_u}, (A -> D) -> D).

Definition join (x : D) (y : D) : D :=
  bigjoin bool (fun b => if b then x else y).

Fixpoint rec (t : Ord.t) {struct t} : D :=
  match t with
  | mkNode cs ts => join base (bigjoin cs (fun c : cs => suc (rec (ts c))))
  end.

End SECOND.

End TRANSFINITE.

Definition zer : Ord.t :=
  @empty.

Definition suc : Ord.t -> Ord.t :=
  @succ.

Definition sup : forall A : Type@{Set_u}, (A -> Ord.t) -> Ord.t :=
  @indexed_union.

Definition orec (base : Ord.t) (succ : Ord.t -> Ord.t) : Ord.t -> Ord.t :=
  rec base succ sup.

Definition add (o1 : Ord.t) (o2 : Ord.t) : Ord.t :=
  Ord.orec o1 suc o2.

Definition mul (o1 : Ord.t) (o2 : Ord.t) : Ord.t :=
  Ord.orec zer (fun o => Ord.add o o1) o2.

End Ord.

Definition Ord : Type@{Set_V} :=
  Ord.t.

Definition _Ord_eq : Ord -> Ord -> Prop :=
  @rEq.

Definition _Ord_lt : Ord -> Ord -> Prop :=
  @rLt.

Definition _Ord_le : Ord -> Ord -> Prop :=
  @rLe.

Definition _zer : Ord :=
  Ord.zer.

Definition _suc : Ord -> Ord :=
  Ord.suc.

Definition _sup : forall A : Type@{Set_u}, (A -> Ord) -> Ord :=
  Ord.sup.

#[global]
Instance Ord_isWellPoset : isWellPoset Ord :=
  { wltProp := rLt
  ; wltProp_Transitive := rLt_StrictOrder.(StrictOrder_Transitive)
  ; wltProp_well_founded := rLt_wf 
  }.

Definition _transfinite_rec : forall D : Type@{Set_V}, (D -> D) -> (forall A : Type@{Set_u}, (A -> D) -> D) -> Ord -> D :=
  @Ord.transfinite_rec.

Definition _Ord_add : Ord -> Ord -> Ord :=
  Ord.add.

Definition _Ord_mul : Ord -> Ord -> Ord :=
  Ord.mul.

Section HARTOGS.

Definition Hartogs (D : Type@{Set_u}) : Ord :=
  mkNode (B.sig (D -> D -> Prop) (@well_founded D)) (fun RWF => @fromWfSet D RWF.(B.proj1_sig) RWF.(B.proj2_sig)).

End HARTOGS.

Module Cardinality.

#[projections(primitive)]
Record t : Type@{Set_V} :=
  mk
  { carrier : Type@{Set_u}
  ; carrier_isSetoid : isSetoid carrier
  }.

#[global] Existing Instance carrier_isSetoid.

Variant le (lhs : Cardinality.t) (rhs : Cardinality.t) : Prop :=
  | le_intro (f : forall x : lhs.(carrier), rhs.(carrier))
    (f_cong : eqPropCompatible1 f)
    (f_inj : forall x1, forall x2, f x1 == f x2 -> x1 == x2)
    : le lhs rhs.

Variant eq (lhs : Cardinality.t) (rhs : Cardinality.t) : Prop :=
  | eq_intro (f : forall x : lhs.(carrier), rhs.(carrier)) (g : forall y : rhs.(carrier), lhs.(carrier))
    (f_cong : eqPropCompatible1 f)
    (g_cong : eqPropCompatible1 g)
    (f_inj : forall x1, forall x2, f x1 == f x2 -> x1 == x2)
    (g_inj : forall y1, forall y2, g y1 == g y2 -> y1 == y2)
    : eq lhs rhs.

Variant lt (lhs : Cardinality.t) (rhs : Cardinality.t) : Prop :=
  | lt_intro
    (LE : Cardinality.le lhs rhs)
    (NE : ~ Cardinality.eq lhs rhs)
    : lt lhs rhs.

Definition add (kappa : Cardinality.t) (lambda : Cardinality.t) : Cardinality.t :=
  mk (kappa.(carrier) + lambda.(carrier))%type sum_isSetoid.

Definition mul (kappa : Cardinality.t) (lambda : Cardinality.t) : Cardinality.t :=
  mk (kappa.(carrier) * lambda.(carrier))%type prod_isSetoid.

Definition exp (kappa : Cardinality.t) (lambda : Cardinality.t) : Cardinality.t :=
  mk { f : kappa.(carrier) -> lambda.(carrier) | eqPropCompatible1 f }%type fun_isSetoid.

End Cardinality.

Definition Card : Type@{Set_V} :=
  Cardinality.t.

Definition _Card_eq : Card -> Card -> Prop :=
  Cardinality.eq.

Definition _Card_lt : Card -> Card -> Prop :=
  Cardinality.lt.

Definition _Card_le : Card -> Card -> Prop :=
  Cardinality.le.

Definition _card : forall A : Type@{Set_u}, isSetoid A -> Card :=
  Cardinality.mk.

Definition _Card_add : Card -> Card -> Card :=
  Cardinality.add.

Definition _Card_mul : Card -> Card -> Card :=
  Cardinality.mul.

Definition _Card_exp : Card -> Card -> Card :=
  Cardinality.exp.

End TypeTheoreticImplementation.
