Require Import PvN.Prelude.Prelude.

Module Type AczelSig.

Parameter t : Type.

Axiom t_isSetoid : isSetoid t.

#[local] Existing Instance t_isSetoid.

Parameter member : t -> t -> Prop.

#[local] Infix "\in" := member : type_scope.

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

#[global]
Instance eqTree_Reflexive
  : Reflexive eqTree.
Proof.
  intros x. induction x as [csx tsx IH]. simpl. split.
  - intros c1. exists c1. exact (IH _).
  - intros c1. exists c1. exact (IH _).
Defined.

#[global]
Instance eqTree_Symmetric
  : Symmetric eqTree.
Proof.
  intros x. induction x as [csx tsx IH], y as [csy tsy]. simpl. intros [x2y y2x]. split.
  - intros c1. pose proof (y2x c1) as [c2 EQ]. exists c2. exact (IH _ _ EQ).
  - intros c1. pose proof (x2y c1) as [c2 EQ]. exists c2. exact (IH _ _ EQ).
Defined.

#[global]
Instance eqTree_Transitive
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

Lemma eqTree_unfold
  : eqTree = (fun lhs => fun rhs => lhs == rhs).
Proof.
  reflexivity.
Defined.

Ltac unred_eqTree := rewrite eqTree_unfold in *.

Definition children (x : Tree) : Type@{Set_u} :=
  match x with
  | mkNode cs _ => cs
  end.

Definition childnodes {x : Tree} : forall c : children x, Tree :=
  match x with
  | mkNode _ ts => ts
  end.

Definition member (x : Tree) (y : Tree) : Prop :=
  exists c : children y, x == childnodes c.

Infix "\in" := member : type_scope.

Lemma eqProp_member_member x y z
  (EQ : x == y)
  (IN : y \in z)
  : x \in z.
Proof.
  destruct IN as [c EQ']. exists c. transitivity y; [exact EQ | exact EQ'].
Defined.

Lemma member_eqProp_member x y z
  (IN : x \in y)
  (EQ : y == z)
  : x \in z.
Proof.
  destruct IN as [c EQ'], y as [csy tsy], z as [csz tsz]. simpl in *.
  destruct EQ as [y2z z2y]. pose proof (y2z c) as [c' EQ]. exists c'.
  simpl. transitivity (tsy c); [exact EQ' | exact EQ].
Defined.

#[global]
Add Parametric Morphism
  : member with signature (eqProp ==> eqProp ==> iff)
  as member_compatWith_eqTree.
Proof.
  intros x1 y1 EQ1 x2 y2 EQ2; split; intros H_IN.
  - eapply member_eqProp_member; [eapply eqProp_member_member; [eapply eqTree_Symmetric; exact EQ1 | exact H_IN] | exact EQ2].
  - eapply member_eqProp_member; [eapply eqProp_member_member; [exact EQ1 | exact H_IN] | eapply eqTree_Symmetric; exact EQ2].
Defined.

#[global]
Add Parametric Morphism
  : (Acc member) with signature (eqProp ==> iff)
  as Acc_member_compatWith_eqTree.
Proof.
  intros x y EQ; split; intros [H_inv].
  - econs. intros z H_IN. eapply H_inv. eapply member_eqProp_member; [exact H_IN | eapply eqTree_Symmetric; exact EQ].
  - econs. intros z H_IN. eapply H_inv. eapply member_eqProp_member; [exact H_IN | exact EQ].
Defined.

Lemma member_wf
  : well_founded member.
Proof.
  intros x. induction x as [csx tsx IH]; simpl. econs.
  intros y [c EQ]. simpl in *. eapply Acc_member_compatWith_eqTree; [exact EQ | eapply IH].
Defined.

Definition member_rect (P : Tree -> Type)
  (IND : forall x, (forall y, y \in x -> P y) -> P x)
  : forall x, P x.
Proof.
  exact (@well_founded_induction_type Tree member member_wf P IND).
Defined.

End Aczel.
