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

Parameter _lim : forall A : Type@{Set_u}, (A -> Ord) -> Ord.

Parameter _transfinite_rec : forall D : Type@{U_discourse}, (D -> D) -> (forall A : Type@{Set_u}, (A -> D) -> D) -> Ord -> D.

Parameter _Ord_add : Ord -> Ord -> Ord.

Parameter _Ord_mul : Ord -> Ord -> Ord.

Parameter _Ord_exp : Ord -> Ord -> Ord.

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

Definition Ord : Type@{Set_V} :=
  @Tree.

Definition _Ord_eq : Ord -> Ord -> Prop :=
  @rEq.

Definition _Ord_lt : Ord -> Ord -> Prop :=
  @rLt.

Definition _Ord_le : Ord -> Ord -> Prop :=
  @rLe.

Definition _zer : Ord :=
  @empty.

Definition _suc : Ord -> Ord :=
  @succ.

Definition _lim : forall A : Type@{Set_u}, (A -> Ord) -> Ord :=
  @indexed_union.

Section TRANSFINITE.

Context {D : Type@{U_discourse}} (suc : D -> D) (lim : forall A : Type@{Set_u}, (A -> D) -> D).

Fixpoint transfinite_rec (t : Ord) {struct t} : D :=
  match t with
  | mkNode cs ts => lim cs (fun c : cs => suc (transfinite_rec (ts c)))
  end.

End TRANSFINITE.

Definition _transfinite_rec : forall D : Type@{U_discourse}, (D -> D) -> (forall A : Type@{Set_u}, (A -> D) -> D) -> Ord -> D :=
  @transfinite_rec.

Definition _Ord_add : Ord -> Ord -> Ord.
Admitted.

Definition _Ord_mul : Ord -> Ord -> Ord.
Admitted.

Definition _Ord_exp : Ord -> Ord -> Ord.
Admitted.

Section HARTOGS.

Definition Hartogs (D : Type@{Set_u}) : Ord :=
  mkNode { R : D -> D -> Prop | well_founded R } (fun RWF => @fromWf D (proj1_sig RWF) (proj2_sig RWF)).

End HARTOGS.

Section TOTALIFY.

Context {A : Type@{Set_u}}.

Variable R : A -> A -> Prop.

Hypothesis R_wf : well_founded R.

Definition toSet_eqProp (lhs : A) (rhs : A) : Prop :=
  @fromAcc A R lhs (R_wf lhs) =ᵣ @fromAcc A R rhs (R_wf rhs).

End TOTALIFY.

Definition Card : Type@{Set_V} :=
  Tree.

Definition _Card_eq : Card -> Card -> Prop.
Admitted.

Definition _Card_lt : Card -> Card -> Prop.
Admitted.

Definition _Card_le : Card -> Card -> Prop.
Admitted.

Definition _card : forall A : Type@{Set_u}, isSetoid A -> Card.
Admitted.

Definition _Card_add : Card -> Card -> Card.
Admitted.

Definition _Card_mul : Card -> Card -> Card.
Admitted.

Definition _Card_exp : Card -> Card -> Card.
Admitted.

End TypeTheoreticImplementation.
