Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.X.

#[local] Infix "=~=" := is_similar_to : type_scope.
#[local] Infix "∈" := L.In.

#[universes(polymorphic=yes), projections(primitive)]
Record alist@{u v} {K : Type@{u}} {V : Type@{v}} : Type@{max(u, v)} :=
  mk_alist { kvlist : list (K * V) } as al.

#[global] Arguments alist : clear implicits.

Definition Similarity_alist_finite_partial_map {KEY : Type} {VAL : Type} {VAL' : Type} (VAL_sim : Similarity VAL VAL') : Similarity (alist KEY VAL) (KEY -> option VAL') :=
  fun al : alist KEY VAL => fun m' : KEY -> option VAL' => forall key, ⟪ SUBMAP1 : forall val, (key, val) ∈ al.(kvlist) -> (exists val', val =~= val' /\ m' key = Some val') ⟫ /\ ⟪ SUBMAP2 : forall val', m' key = Some val' -> (exists val, val =~= val' /\ (key, val) ∈ al.(kvlist)) ⟫.

Instance alist_corresponds_to_finite_partial_map {KEY : Type} {VAL : Type} : Similarity (alist KEY VAL) (KEY -> option VAL) :=
  Similarity_alist_finite_partial_map eq.

Theorem alist_corresponds_to_finite_partial_map_iff (KEY : Type) (VAL : Type) (al : alist KEY VAL) (m : KEY -> option VAL)
  : al =~= m <-> (forall k, forall v, (k, v) ∈ al.(kvlist) <-> m k = Some v).
Proof.
  done!.
Qed.

#[global] Hint Rewrite alist_corresponds_to_finite_partial_map_iff : simplication_hints.
