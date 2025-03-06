Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Data.Aczel.

Module Type SetTheoreticConcepts.

Parameter V : Type@{Set_V}.

Parameter _eq : V -> V -> Prop.

Parameter _in : V -> V -> Prop.

Parameter _subseteq : V -> V -> Prop.

Parameter _emptyset : V.

Parameter _powerset : V -> V.

Parameter _unordered_pair : V -> V -> V.

Parameter _unions : V -> V.

Parameter _filter : (V -> Prop) -> V -> V.

Parameter Ord : Type@{Set_V}.

Parameter _Ord_eq : Ord -> Ord -> Prop.

Parameter _Ord_lt : Ord -> Ord -> Prop.

Parameter _Ord_le : Ord -> Ord -> Prop.

Parameter _zer : Ord.

Parameter _suc : Ord -> Ord.

Parameter _lim : forall A : Type@{Set_u}, (A -> Ord) -> Ord.

Parameter _Ord_add : Ord -> Ord -> Ord.

Parameter _Ord_mul : Ord -> Ord -> Ord.

Parameter _Ord_exp : Ord -> Ord -> Ord.

Parameter Card : Type@{Set_V}.

Parameter _Card_add : Card -> Card -> Card.

Parameter _Card_mul : Card -> Card -> Card.

Parameter _Card_exp : Card -> Card -> Card.

Parameter card : Type@{Set_u} -> Card.

End SetTheoreticConcepts.
