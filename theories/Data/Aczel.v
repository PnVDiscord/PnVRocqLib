Require Import PvN.Prelude.Prelude.

Module Type AczelSig.

Parameter t : Type.

Axiom t_isSetoid : isSetoid t.

#[local] Existing Instance t_isSetoid.

End AczelSig.

Universe Set_u.

Module Aczel <: AczelSig.

Inductive Tree : Type :=
  | mkNode (cs : Type@{Set_u}) (ts : forall c : cs, Tree).

Definition t := Tree.

Fixpoint eqTree (lhs : Tree) (rhs : Tree) : Prop :=
  match lhs, rhs with
  | mkNode cs1 ts1, mkNode cs2 ts2 => (forall c1 : cs1, exists c2 : cs2, eqTree (ts1 c1) (ts2 c2)) /\ (forall c2 : cs2, exists c1 : cs1, eqTree (ts1 c1) (ts2 c2))
  end.

Lemma eqTree_Reflexive
  : Reflexive eqTree.
Proof.
  intros x. induction x as [csx tsx IH]. simpl. split.
  - intros c1. exists c1. exact (IH _).
  - intros c1. exists c1. exact (IH _).
Defined.

Lemma eqTree_Symmetric
  : Symmetric eqTree.
Proof.
  intros x. induction x as [csx tsx IH], y as [csy tsy]. simpl. intros [x2y y2x]. split.
  - intros c1. pose proof (y2x c1) as [c2 EQ]. exists c2. exact (IH _ _ EQ).
  - intros c1. pose proof (x2y c1) as [c2 EQ]. exists c2. exact (IH _ _ EQ).
Defined.

Lemma eqTree_Transitive
  : Transitive eqTree.
Proof.
  intros x. induction x as [csx tsx IH], y as [csy tsy], z as [csz tsz]. simpl. intros [x2y y2x] [y2z z2y]. split.
  - intros c1. pose proof (x2y c1) as [c2 EQ]. pose proof (y2z c2) as [c3 EQ']. exists c3. exact (IH _ _ _ EQ EQ').
  - intros c1. pose proof (z2y c1) as [c2 EQ]. pose proof (y2x c2) as [c3 EQ']. exists c3. exact (IH _ _ _ EQ' EQ).
Defined.

#[global]
Instance Tree_isSetoid : isSetoid Tree :=
  { eqProp := eqTree
  ; eqProp_Equivalence := {| Equivalence_Reflexive := eqTree_Reflexive; Equivalence_Symmetric := eqTree_Symmetric; Equivalence_Transitive := eqTree_Transitive |}
  }.

Definition t_isSetoid : isSetoid t := Tree_isSetoid.

Definition children (x : Tree) : Type@{Set_u} :=
  match x with
  | mkNode cs _ => cs
  end.

Definition childnodes (x : Tree) : forall c : children x, Tree :=
  match x with
  | mkNode _ ts => ts
  end.

End Aczel.
