Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.X.
Require Import PnV.Data.FiniteSet.

#[local] Infix "=~=" := is_similar_to : type_scope.
#[local] Infix "∈" := L.In.

Module FM.

Import FS.

#[universes(template), projections(primitive)]
Record alist {K : Type} {V : Type} : Type :=
  mk_alist { kvlist : list (K * V) } as al.

#[global] Arguments alist : clear implicits.

#[global]
Instance alist_isSetoid {K : Type} {V : Type} (K_hasEqDec : hasEqDec K) (V_isSetoid : isSetoid V) : isSetoid (alist K V) :=
  { eqProp (lhs : alist K V) (rhs : alist K V) := forall k : K, eqProp (isSetoid := @option_isSetoid V V_isSetoid) (L.lookup (EQ_DEC := K_hasEqDec) k lhs.(kvlist)) (L.lookup (EQ_DEC := K_hasEqDec) k rhs.(kvlist))
  ; eqProp_Equivalence := relation_on_image_liftsEquivalence (pi_isSetoid (fun _ => @option_isSetoid V V_isSetoid)).(eqProp_Equivalence) (fun al : alist K V => fun k : K => L.lookup (EQ_DEC := K_hasEqDec) k al.(kvlist))
  }.

Definition Similarity_alist_finite_partial_map {KEY : Type} {VAL : Type} {VAL' : Type} (VAL_sim : Similarity VAL VAL') : Similarity (alist KEY VAL) (KEY -> option VAL') :=
  fun al : alist KEY VAL => fun m' : KEY -> option VAL' => forall key, ⟪ SUBMAP1 : forall val, (key, val) ∈ al.(kvlist) -> (exists val', val =~= val' /\ m' key = Some val') ⟫ /\ ⟪ SUBMAP2 : forall val', m' key = Some val' -> (exists val, val =~= val' /\ (key, val) ∈ al.(kvlist)) ⟫.

#[global]
Instance alist_corresponds_to_finite_partial_map {KEY : Type} {VAL : Type} : Similarity (alist KEY VAL) (KEY -> option VAL) :=
  Similarity_alist_finite_partial_map eq.

Theorem alist_corresponds_to_finite_partial_map_iff (KEY : Type) (VAL : Type) (al : alist KEY VAL) (m : KEY -> option VAL)
  : al =~= m <-> (forall k, forall v, (k, v) ∈ al.(kvlist) <-> m k = Some v).
Proof.
  done!.
Qed.

#[global] Hint Rewrite alist_corresponds_to_finite_partial_map_iff : simplication_hints.

End FM.
