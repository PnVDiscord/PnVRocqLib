Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Data.Aczel.

Module TypeTheoreticOrdinals.

Definition ord : Type@{Set_V} :=
  Tree.

#[global]
Instance ord_isWellPoset : isWellPoset ord :=
  { wltProp := rLt
  ; wltProp_Transitive := rLt_StrictOrder.(StrictOrder_Transitive)
  ; wltProp_well_founded := rLt_wf 
  }.

Section TRANSFINITE.

Context {D : Type@{Set_V}} (suc : D -> D) (lim : forall A : Type@{Set_u}, (A -> D) -> D).

Fixpoint tf_rec (o : ord) {struct o} : D :=
  match o with
  | mkNode cs ts => lim cs (fun c => suc (tf_rec (ts c)))
  end.

End TRANSFINITE.

Section HARTOGS.

Definition Hartogs (D : Type@{Set_u}) : ord :=
  mkNode { R : D -> D -> Prop | well_founded R } (fun RWF => @fromWf D (proj1_sig RWF) (proj2_sig RWF)).

End HARTOGS.

End TypeTheoreticOrdinals.
