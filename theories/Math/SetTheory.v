Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Data.Aczel.

Module Type SetTheoreticConcepts.

Parameter V : Type@{Set_V}.

Parameter Ord : Type@{Set_V}.

Parameter Card : Type@{Set_u} -> V.

End SetTheoreticConcepts.
