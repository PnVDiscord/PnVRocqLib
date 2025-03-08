Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Data.Aczel.

Module Type Ordinals.

Parameter Ord : Type@{Set_V}.

End Ordinals.

Module TypeTheoreticOrdinals <: Ordinals.

Definition Ord : Type@{Set_V} :=
  Tree.

#[global]
Instance Ord_isWellPoset : isWellPoset Ord :=
  { wltProp := rLt
  ; wltProp_Transitive := rLt_StrictOrder.(StrictOrder_Transitive)
  ; wltProp_well_founded := rLt_wf 
  }.

Section TRANSFINITE.

Context {D : Type@{U_discourse}} (suc : D -> D) (lim : forall A : Type@{Set_u}, (A -> D) -> D).

Fixpoint transfinite_rec (o : Ord) {struct o} : D :=
  match o with
  | mkNode cs ts => lim cs (fun c => suc (transfinite_rec (ts c)))
  end.

End TRANSFINITE.

Section HARTOGS.

Definition Hartogs (D : Type@{Set_u}) : Ord :=
  mkNode { R : D -> D -> Prop | well_founded R } (fun RWF => @fromWf D (proj1_sig RWF) (proj2_sig RWF)).

End HARTOGS.

End TypeTheoreticOrdinals.
