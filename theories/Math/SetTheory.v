Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Data.Aczel.
Require Import PnV.Math.ConstructiveOrdinal.

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
