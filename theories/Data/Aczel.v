Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Prelude.ConstructiveFacts.

Universe Set_u.

Universe Set_V.

Constraint Set_u < Set_V.

Create HintDb aczel_hints.

Inductive Tree : Type@{Set_V} :=
  | mkNode (cs : Type@{Set_u}) (ts : forall c : cs, Tree) : Tree.

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

Lemma eqTree_unfold
  : eqTree = (fun lhs => fun rhs => lhs == rhs).
Proof.
  reflexivity.
Defined.

Ltac unred_eqTree :=
  rewrite eqTree_unfold in *.

Definition children (x : Tree) : Type@{Set_u} :=
  match x with
  | mkNode cs _ => cs
  end.

Definition childnodes (x : Tree) : forall c : children x, Tree :=
  match x with
  | mkNode _ ts => ts
  end.

Lemma Tree_eta x
  : mkNode (children x) (childnodes x) = x.
Proof.
  destruct x as [csx tsx]; reflexivity.
Defined.

Definition member (x : Tree) (y : Tree) : Prop :=
  exists c : children y, x == childnodes y c.

#[local] Infix "\in" := member : type_scope.

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

Theorem member_rect (P : Tree -> Type)
  (IND : forall x, (forall y, y \in x -> P y) -> P x)
  : forall x, P x.
Proof.
  intros x. induction (member_wf x) as [x _ IH]. exact (IND x IH).
Defined.

#[global] Hint Resolve eqTree_Reflexive eqTree_Symmetric eqTree_Transitive : aczel_hints.

#[local] Hint Resolve Equivalence_Reflexive Equivalence_Symmetric Equivalence_Transitive : core.

#[local] Hint Resolve eqProp_refl eqProp_sym eqProp_trans leProp_refl leProp_trans leProp_antisymmetry eqProp_implies_leProp : core.

#[global] Hint Unfold children childnodes member : aczel_hints.

#[local] Tactic Notation "done" :=
  now autounfold with aczel_hints in *; firstorder with aczel_hints; eauto with *.

Lemma member_intro cs ts c
  : ts c \in mkNode cs ts.
Proof.
  done.
Qed.

#[global] Hint Resolve member_intro : aczel_hints.

Theorem extensionality x y
  (EXT_EQ : forall z, z \in x <-> z \in y)
  : x == y.
Proof.
  destruct x as [csx tsx], y as [csy tsy]; simpl; i. split; intros c.
  - pose proof (proj1 (EXT_EQ (tsx c)) (member_intro _ _ _)) as [c' EQ]; done.
  - pose proof (proj2 (EXT_EQ (tsy c)) (member_intro _ _ _)) as [c' EQ]; done.
Qed.

Definition isSubsetOf x y : Prop :=
  forall z, z \in x -> z \in y.

#[local] Infix "\subseteq" := isSubsetOf : type_scope.

#[global] Hint Unfold isSubsetOf : aczel_hints.

#[global]
Instance isSubsetOf_PreOrder
  : PreOrder isSubsetOf.
Proof.
  split; ii; try done.
Qed.

#[global]
Instance isSubsetOf_PartialOrder
  : PartialOrder eqProp isSubsetOf.
Proof.
  intros x y. cbn. unfold flip. rewrite eqTree_unfold. split.
  - intros EQ. split; ii; rewrite EQ in *; done.
  - intros [LE GE]. eapply extensionality; done.
Qed.

Lemma eqTree_intro (lhs : Tree) (rhs : Tree)
  (SUBSET : lhs \subseteq rhs)
  (SUBSET' : rhs \subseteq lhs)
  : lhs == rhs.
Proof.
  exact (proj2 (isSubsetOf_PartialOrder lhs rhs) (conj SUBSET SUBSET')).
Qed.

#[global]
Add Parametric Morphism
  : isSubsetOf with signature (eqProp ==> eqProp ==> iff)
  as isSubsetOf_compatWith_eqProp.
Proof with eauto with *.
  intros x1 y1 EQ1 x2 y2 EQ2. transitivity (x1 \subseteq y2); unfold "\subseteq"; split; intros SUBSET z H_in.
  - rewrite <- EQ2...
  - rewrite -> EQ2...
  - rewrite <- EQ1 in H_in...
  - rewrite -> EQ1 in H_in...
Qed.

#[global]
Instance member_isCompatibleWith_eqProp_fst z
  : isCompatibleWith_eqProp (fun w => member w z).
Proof.
  intros x IN y EQ. rewrite <- EQ. exact IN.
Qed.

#[global]
Instance member_isCompatibleWith_eqProp_snd z
  : isCompatibleWith_eqProp (fun w => member z w).
Proof.
  intros x IN y EQ. rewrite <- EQ. exact IN.
Qed.

#[global]
Instance eqProp_isCompatibleWith_eqProp_fst z
  : isCompatibleWith_eqProp (fun w => w == z).
Proof.
  ii; etransitivity; eauto.
Qed.

#[global]
Instance eqProp_isCompatibleWith_eqProp_snd z
  : isCompatibleWith_eqProp (fun w => z == w).
Proof.
  ii; etransitivity; eauto.
Qed.

#[global]
Instance eqProp_isCompatibleWith_isSubsetOf_fst z
  : isCompatibleWith_eqProp (fun w => isSubsetOf z w).
Proof.
  now ii; eapply isSubsetOf_compatWith_eqProp; eauto.
Qed.

#[global]
Instance eqProp_isCompatibleWith_isSubsetOf_snd z
  : isCompatibleWith_eqProp (fun w => isSubsetOf w z).
Proof.
  intros x H1 y H2 w H3. eapply H1. rewrite H2. exact H3.
Qed.

(** Section SET_CONSTRUCTIONS. *)

#[local] Opaque eqProp.

Definition filterc (x : Tree) (P : children x -> Prop) : Tree :=
  mkNode (@sig (children x) P) (fun c => childnodes x (proj1_sig c)).

Theorem filterc_spec x P
  : forall z, z \in filterc x P <-> (exists cx : children x, z == childnodes x cx /\ P cx).
Proof.
  intros z. split.
  - intros [[cx H_P] EQ]. simpl in *; eauto with *.
  - intros [cx [EQ H_P]]. exists (@exist _ _ cx H_P); eauto with *.
Qed.

#[global] Hint Rewrite filterc_spec : simplication_hints.

Corollary subset_filterc x
  : forall z, z \subseteq x <-> (exists P, z == filterc x P).
Proof.
  intros z. split.
  - intros SUBSET. exists (fun cx => childnodes x cx \in z). eapply eqTree_intro.
    + intros y IN. pose proof (SUBSET y IN) as [c EQ]. rewrite filterc_spec. exists c. split; trivial. rewrite <- EQ. exact IN.
    + intros y IN. rewrite filterc_spec in IN. destruct IN as [cx [EQ IN]]. rewrite -> EQ. exact IN.
  - intros [P EQ] y IN. rewrite EQ in IN. destruct IN as [[c H_P] EQ']. simpl in *. rewrite EQ'. eapply member_intro.
Qed.

Definition filter (P : Tree -> Prop) (x : Tree) : Tree :=
  filterc x (fun c => P (childnodes x c)).

Theorem filter_spec P x
  : forall z, z \in filter P x <-> (exists c, P (childnodes x c) /\ z == childnodes x c).
Proof.
  intros z. unfold filter. rewrite filterc_spec. done.
Qed.

#[global] Hint Rewrite filter_spec : simplication_hints.

Corollary filter_good P x
  (COMPAT : isCompatibleWith_eqProp P)
  : forall z, z \in filter P x <-> (z \in x /\ P z).
Proof.
  intros z. rewrite filter_spec. split.
  - intros [c [H_P EQ]]. split.
    + rewrite EQ. eapply member_intro.
    + eapply COMPAT; eauto with *.
  - intros [[c EQ] H_P]. exists c. done.
Qed.

#[global]
Instance filter_eqPropCompatible1 P
  (COMPAT : isCompatibleWith_eqProp P)
  : eqPropCompatible1 (filter P).
Proof.
  now ii; eapply eqTree_intro; ii; rewrite filter_good in *; eauto with *; [rewrite <- x_EQ | rewrite -> x_EQ].
Qed.

Definition power (x : Tree) : Tree :=
  mkNode (children x -> Prop) (filterc x).

Theorem power_spec x
  : forall z, z \in power x <-> z \subseteq x.
Proof.
  intros z. rewrite subset_filterc. unfold power. eauto with *.
Qed.

#[global] Hint Rewrite power_spec : simplication_hints.

#[global]
Instance power_eqPropCompatible1
  : eqPropCompatible1 power.
Proof.
  ii; eapply eqTree_intro; ii; rewrite power_spec in *; ii; [rewrite <- x_EQ | rewrite -> x_EQ]; eauto.
Qed.

Definition indexed_union (I : Type@{Set_u}) (x_i : I -> Tree) : Tree :=
  mkNode { i : I & children (x_i i) } (fun c => childnodes (x_i (projT1 c)) (projT2 c)).

Theorem indexed_union_spec I x_i
  : forall z, z \in indexed_union I x_i <-> (exists i, z \in x_i i).
Proof.
  intros z. split.
  - intros [[i c] EQ]; simpl in *; eauto with *.
  - intros [i [c EQ]]; simpl in *; exists (@existT _ _ i c); eauto with *.
Qed.

#[global] Hint Rewrite indexed_union_spec : simplication_hints.

#[global]
Instance indexed_union_eqPropCompatible1 I
  : eqPropCompatible1 (indexed_union I).
Proof.
  ii. change (forall i : I, x1 i == x2 i) in x_EQ.
  eapply eqTree_intro; ii; rewrite indexed_union_spec in *; des; exists i; [rewrite <- x_EQ | rewrite -> x_EQ]; eauto with *.
Qed.

Definition unions (x : Tree) : Tree :=
  indexed_union (children x) (childnodes x).

Theorem unions_spec x
  : forall z, z \in unions x <-> (exists y, z \in y /\ y \in x).
Proof.
  intros z. unfold unions. rewrite indexed_union_spec. split.
  - intros [i [c EQ]]; simpl in *; exists (childnodes x i); split; eauto with *.
  - intros [y [IN [c EQ]]]; simpl in *. exists c. rewrite <- EQ. exact IN.
Qed.

#[global] Hint Rewrite unions_spec : simplication_hints.

#[global]
Instance unions_eqPropCompatible1
  : eqPropCompatible1 unions.
Proof.
  ii; eapply eqTree_intro; ii; rewrite unions_spec in *; des; exists y; [rewrite <- x_EQ | rewrite -> x_EQ]; done.
Qed.

Definition empty : Tree :=
  mkNode Empty_set (@Empty_set_rect (fun _ => Tree)).

Theorem empty_spec
  : forall z, z \in empty <-> False.
Proof.
  intros z. split.
  - intros [[] ?].
  - intros [].
Qed.

#[global] Hint Rewrite empty_spec : simplication_hints.

Definition upair (x1 : Tree) (x2 : Tree) : Tree :=
  mkNode bool (fun b => if b then x1 else x2).

Theorem upair_spec x1 x2
  : forall z, z \in upair x1 x2 <-> (z == x1 \/ z == x2).
Proof.
  intros z. split.
  - intros [[ | ] EQ]; simpl in *; eauto with *.
  - intros [EQ | EQ]; [exists true | exists false]; eauto with *.
Qed.

#[global] Hint Rewrite upair_spec : simplication_hints.

#[global]
Instance upair_eqPropCompatible2
  : eqPropCompatible2 upair.
Proof.
  ii; eapply eqTree_intro; ii; rewrite upair_spec in *; [rewrite <- x_EQ, <- y_EQ | rewrite -> x_EQ, -> y_EQ]; eauto with *.
Qed.

#[global]
Instance upair_comm
  : isCommutative upair.
Proof.
  ii. eapply eqTree_intro; ii; rewrite upair_spec in *; done.
Qed.

Definition union (x1 : Tree) (x2 : Tree) : Tree :=
  unions (upair x1 x2).

Theorem union_spec x1 x2
  : forall z, z \in union x1 x2 <-> (z \in x1 \/ z \in x2).
Proof.
  intros z. unfold union. rewrite unions_spec. split.
  - intros [y [IN IN']]; rewrite upair_spec in IN'.
    destruct IN' as [EQ | EQ]; rewrite EQ in IN; eauto.
  - intros [IN | IN]; [exists x1 | exists x2]; rewrite upair_spec; eauto with *.
Qed.

#[global] Hint Rewrite union_spec : simplication_hints.

#[global]
Instance union_eqPropCompatible2
  : eqPropCompatible2 union.
Proof.
  ii; eapply eqTree_intro; ii; rewrite union_spec in *; [rewrite <- x_EQ, <- y_EQ | rewrite -> x_EQ, -> y_EQ]; eauto with *.
Qed.

Definition intersection (x : Tree) (y : Tree) : Tree :=
  filter (fun z => z \in x) y.

Theorem intersection_spec x y
  : forall z, z \in intersection x y <-> (z \in x /\ z \in y).
Proof.
  intros z. unfold intersection. rewrite filter_good.
  - done.
  - intros a IN b EQ. rewrite <- EQ. exact IN.
Qed.

#[global] Hint Rewrite intersection_spec : simplication_hints.

#[global]
Instance intersection_eqPropCompatible2
  : eqPropCompatible2 intersection.
Proof.
  ii; eapply eqTree_intro; ii; rewrite intersection_spec in *; [rewrite <- x_EQ, <- y_EQ | rewrite -> x_EQ, -> y_EQ]; done.
Qed.

Definition singleton (x : Tree) : Tree :=
  upair x x.

Theorem singleton_spec x
  : forall z, z \in singleton x <-> z == x.
Proof.
  intros z. unfold singleton. rewrite upair_spec. done.
Qed.

#[global] Hint Rewrite singleton_spec : simplication_hints.

Corollary singleton_inj x y
  (EQ : singleton x == singleton y)
  : x == y.
Proof.
  assert (IN : x \in singleton x) by now rewrite singleton_spec.
  rewrite EQ in IN. rewrite singleton_spec in IN. done.
Qed.

#[global]
Instance singleton_eqPropCompatible1
  : eqPropCompatible1 singleton.
Proof.
  ii. eapply eqTree_intro; ii.
  - rewrite singleton_spec in *. rewrite <- x_EQ. exact H.
  - rewrite singleton_spec in *. rewrite -> x_EQ. exact H.
Qed.

Definition pair (x : Tree) (y : Tree) : Tree :=
  upair (singleton x) (upair x y).

Lemma upair_eq_upair_implies x1 y1 x2 y2
  (EQ : upair x1 y1 == upair x2 y2)
  : (x1 == x2 /\ y1 == y2) \/ (x1 == y2 /\ x2 == y1).
Proof.
  assert (H_in : x1 \in upair x1 y1).
  { rewrite upair_spec. now left. }
  rewrite EQ in H_in. rewrite upair_spec in H_in.
  destruct H_in as [H_EQ | H_EQ].
  - left. split; trivial. rewrite H_EQ in EQ.
    assert (IN : y1 \in upair x2 y1).
    { rewrite upair_spec. now right. }
    rewrite -> EQ in IN. rewrite upair_spec in IN.
    destruct IN as [H_EQ' | H_EQ'].
    + rewrite -> H_EQ'. symmetry. rewrite <- singleton_spec.
      unfold singleton. rewrite -> H_EQ' in EQ. rewrite -> EQ.
      rewrite upair_spec. now right.
    + eauto with *.
  - right. split; trivial. rewrite H_EQ in EQ.
    assert (IN : x2 \in upair x2 y2).
    { rewrite upair_spec. now left. }
    rewrite <- EQ in IN. rewrite upair_spec in IN.
    destruct IN as [H_EQ' | H_EQ'].
    + rewrite -> H_EQ'. symmetry. rewrite <- singleton_spec.
      unfold singleton. rewrite -> H_EQ' in EQ. rewrite <- EQ.
      rewrite upair_spec. now right.
    + eauto with *.
Qed.

Lemma singleton_eq_upair_implies x y z
  (EQ : singleton x == upair y z)
  : x == y /\ y == z.
Proof.
  revert x y z EQ. enough (WTS : forall x, forall y, forall z, singleton x == upair y z -> x == y).
  { ii. enough (ENOUGH : x == y).
    - split; trivial. rewrite comm in EQ. apply WTS in EQ. rewrite EQ in ENOUGH. done.
    - eapply WTS. exact EQ.
  }
  intros x y z EQ. unfold singleton in EQ. apply upair_eq_upair_implies in EQ. destruct EQ as [[EQ1 H_EQ] | [EQ1 H_EQ]]; done.
Qed.

Theorem pair_inv x1 x2 y1 y2
  (EQ : pair x1 y1 == pair x2 y2)
  : x1 == x2 /\ y1 == y2.
Proof.
  unfold pair in EQ. apply upair_eq_upair_implies in EQ. destruct EQ as [[EQ1 H_EQ] | [EQ1 H_EQ]].
  - apply singleton_inj in EQ1. split; trivial. apply upair_eq_upair_implies in H_EQ. destruct H_EQ as [[EQ2 EQ3] | [EQ2 EQ3]]; eauto with *.
  - apply singleton_eq_upair_implies in H_EQ. apply singleton_eq_upair_implies in EQ1.
    destruct EQ1 as [EQ1 EQ2], H_EQ as [EQ3 EQ4]. rewrite EQ4, EQ3, EQ1, EQ2. rewrite <- EQ4, <- EQ3, <- EQ2. now split.
Qed.

#[global]
Instance pair_eqPropCompatible2
  : eqPropCompatible2 pair.
Proof.
  ii. unfold pair. now rewrite x_EQ, y_EQ.
Qed.

Definition fst (t : Tree) : Tree :=
  unions (filter (fun x => singleton x \in t) (unions t)).

#[global]
Instance fst_eqPropCompatible1
  : eqPropCompatible1 fst.
Proof.
  ii. unfold fst. eapply eqTree_intro; ii; rewrite unions_spec in *.
  - des. exists y. split; trivial. rewrite filter_spec in *. des.
    assert (IN : childnodes (unions x1) c \in unions x1) by now eapply member_intro.
    rewrite -> x_EQ in IN at 2. destruct IN as [c' EQ]. exists c'. rewrite <- EQ. rewrite <- x_EQ. done.
  - des. exists y. split; trivial. rewrite filter_spec in *. des.
    assert (IN : childnodes (unions x2) c \in unions x2) by now eapply member_intro.
    rewrite <- x_EQ in IN at 2. destruct IN as [c' EQ]. exists c'. rewrite <- EQ. rewrite -> x_EQ. done.
Qed.

Definition snd (t : Tree) : Tree :=
  unions (filter (fun y => pair (fst t) y == t) (unions t)).

#[global]
Instance snd_eqPropCompatible1
  : eqPropCompatible1 snd.
Proof.
  ii. unfold snd. eapply eqTree_intro; ii; rewrite unions_spec in *.
  - des. exists y. split; trivial. rewrite filter_spec in *. des.
    assert (IN : childnodes (unions x1) c \in unions x1) by now eapply member_intro.
    rewrite -> x_EQ in IN at 2. destruct IN as [c' EQ]. exists c'. rewrite <- EQ. rewrite <- x_EQ. done.
  - des. exists y. split; trivial. rewrite filter_spec in *. des.
    assert (IN : childnodes (unions x2) c \in unions x2) by now eapply member_intro.
    rewrite <- x_EQ in IN at 2. destruct IN as [c' EQ]. exists c'. rewrite <- EQ. rewrite -> x_EQ. done.
Qed.

Theorem destruct_pair (t : Tree)
  (EQ : exists x, exists y, t == pair x y)
  : t == pair (fst t) (snd t).
Proof.
  destruct EQ as (x & y & EQ). rewrite EQ at 1.
  assert (claim : unions t == upair x y).
  { eapply eqTree_intro; intros z H_IN.
    - rewrite EQ in H_IN. rewrite unions_spec in H_IN. destruct H_IN as (w & H_in & H_IN).
      unfold pair in H_IN. rewrite upair_spec in H_IN. destruct H_IN as [H_EQ | H_EQ]; rewrite H_EQ in H_in; clear w H_EQ.
      + rewrite upair_spec. left. rewrite <- singleton_spec. exact H_in.
      + exact H_in.
    - rewrite upair_spec in H_IN. rewrite EQ. clear t EQ. destruct H_IN as [EQ | EQ].
      + rewrite unions_spec. exists (singleton x). split.
        * rewrite singleton_spec. exact EQ.
        * unfold pair. rewrite upair_spec. now left.
      + rewrite unions_spec. exists (upair x y). split.
        * rewrite upair_spec. now right.
        * unfold pair. rewrite upair_spec. now right.
  }
  assert (FST_EQ : x == fst t).
  { unfold fst. eapply eqTree_intro; intros z H_in.
    - rewrite unions_spec. exists x. split; trivial. rewrite filter_good.
      + split.
        * rewrite claim. rewrite upair_spec. now left.
        * rewrite EQ. unfold pair. rewrite upair_spec. now left.
      + intros a H_in' b EQ'. rewrite EQ' in H_in'. exact H_in'.
    - rewrite unions_spec in H_in. destruct H_in as (w & H_in & H_IN). rewrite filter_good in H_IN.
      + destruct H_IN as [H_IN1 H_IN2]. rewrite claim in H_IN1.
        rewrite upair_spec in H_IN1. destruct H_IN1 as [EQ' | EQ']; rewrite EQ' in H_in, H_IN2; clear w EQ'.
        * exact H_in.
        * rewrite EQ in H_IN2. unfold pair in H_IN2. rewrite upair_spec in H_IN2. destruct H_IN2 as [EQ' | EQ'].
          { apply singleton_inj in EQ'. rewrite <- EQ'. exact H_in. }
          { apply singleton_eq_upair_implies in EQ'. destruct EQ' as [EQ1 EQ2]. rewrite EQ2. exact H_in. }
      + intros a H_in' b EQ'. rewrite <- EQ'. exact H_in'.
  }
  assert (SND_EQ : y == snd t).
  { unfold snd. eapply eqTree_intro; intros z H_in.
    - rewrite unions_spec. exists y. split; trivial. rewrite filter_good.
      + split.
        * rewrite claim. rewrite upair_spec. now right.
        * rewrite <- FST_EQ. now rewrite EQ.
      + intros a H_EQ b EQ'. rewrite <- EQ'. exact H_EQ.
    - rewrite unions_spec in H_in. destruct H_in as (w & H_in & H_IN). rewrite filter_good in H_IN.
      + rewrite <- FST_EQ in H_IN. destruct H_IN as [H_IN EQ']. rewrite <- EQ' in EQ. apply pair_inv in EQ.
        destruct EQ as [_ EQ]. rewrite <- EQ. exact H_in.
      + intros a H_EQ b EQ'. rewrite <- EQ'. exact H_EQ.
  }
  now rewrite FST_EQ, SND_EQ.
Qed.

Corollary fst_pair x y
  : fst (pair x y) == x.
Proof.
  set (t := pair x y).
  assert (claim : t == pair (fst t) (snd t)).
  { eapply destruct_pair. now exists x, y. }
  unfold t in claim at 1. now apply pair_inv in claim.
Qed.

Corollary snd_pair x y
  : snd (pair x y) == y.
Proof.
  set (t := pair x y).
  assert (claim : t == pair (fst t) (snd t)).
  { eapply destruct_pair. now exists x, y. }
  unfold t in claim at 1. now apply pair_inv in claim.
Qed.

Definition Cartesian_product (X : Tree) (Y : Tree) : Tree :=
  filter (fun z => exists x, x \in X /\ exists y, y \in Y /\ z == pair x y) (power (power (union X Y))).

Lemma Cartesian_product_spec X Y
  : forall z, z \in Cartesian_product X Y <-> (exists x, x \in X /\ exists y, y \in Y /\ z == pair x y).
Proof.
  intros z. unfold Cartesian_product. rewrite filter_good.
  - rewrite power_spec. split.
    + intros (SUBSET & x & x_in_X & y & y_in_Y & EQ). done.
    + intros (x & x_in_X & y & y_in_Y & EQ). split.
      * intros a a_in. rewrite power_spec. intros b b_in. unfold pair in EQ. rewrite EQ in a_in. rewrite upair_spec in a_in. destruct a_in as [EQ' | EQ'].
        { rewrite EQ' in b_in. rewrite singleton_spec in b_in. rewrite b_in. rewrite union_spec. left. exact x_in_X. }
        { rewrite EQ' in b_in. rewrite upair_spec in b_in. destruct b_in as [EQ'' | EQ'']; rewrite EQ''; rewrite union_spec; [left | right]; trivial. }
      * done.
  - intros a (x & x_in & y & y_in & EQ) b a_eq_b. exists x. split; trivial. exists y. split; trivial. rewrite <- a_eq_b; trivial.
Qed.

(** End SET_CONSTRUCTIONS. *)

Section STRONG_COLLECTION.

(* << A Sketch of the Proof of Strong Collection >>
  -- Advice of "Hanul Jeon"
  > Aczel의 Strong Collection의 증명을 스케치해보면,
  > 우선 forall x:X, exists y, phi(x,y)가 성립한다고 합시다.
  > 여기서 AC를 적용해서 forall x:X, phi(x,f(x))인 f를 찾고,
  > base set을 X의 base와 똑같이 잡을 겁니다.
  > 그리고 원소는 f(x)에 대응하게끔 잡을 거고요.
  > 문제는 AC가 Coq에서 작동할 것 같지 않다는 거네요.
*)

Hypothesis AC : forall A : Type, forall B : Type, forall P : A -> B -> Prop, (forall x, exists y, P x y) -> (exists f, forall x, P x (f x)).

Theorem AxiomOfChoice_implies_StrongCollection (P : Tree -> Tree -> Prop)
  (COMPAT1 : forall y, isCompatibleWith_eqProp (fun x => P x y))
  (COMPAT2 : forall x, isCompatibleWith_eqProp (fun y => P x y))
  : forall X, (forall x, x \in X -> exists y, P x y) -> exists Y, (forall x, x \in X -> exists y, y \in Y /\ P x y) /\ (forall y, y \in Y -> exists x, x \in X /\ P x y).
Proof with eauto with *.
  intros X NONEMPTY. set (base_set := children X).
  assert (claim : exists f : base_set -> Tree, forall x : base_set, P (childnodes X x) (f x)).
  { eapply AC with (P := fun x : base_set => fun y : Tree => P (childnodes X x) y)... }
  destruct claim as [f claim]. exists (mkNode base_set (fun x => f x)). split.
  - intros x [c EQ]. exists (f c). split... eapply COMPAT1...
  - intros x [c EQ]. exists (childnodes X c). split... eapply COMPAT2...
Qed.

End STRONG_COLLECTION.

(** Section RANK_COMPARISON. *)

Inductive rLt (lhs : Tree) (rhs : Tree) : Prop :=
  | rLt_intro
    (H_rLe : exists c, lhs ≦ᵣ childnodes rhs c)
    : lhs <ᵣ rhs
  where "lhs <ᵣ rhs" := (rLt lhs rhs) : type_scope
with rLe (lhs : Tree) (rhs : Tree) : Prop :=
  | rLe_intro
    (H_rLt : forall c, childnodes lhs c <ᵣ rhs)
    : lhs ≦ᵣ rhs
  where "lhs ≦ᵣ rhs" := (rLe lhs rhs) : type_scope.

#[global] Hint Constructors rLt rLe : aczel_hints.

Fixpoint rLt_inv (x : Tree) (y : Tree) (H_rLt : y <ᵣ x) {struct H_rLt}
  : exists c1 : children x, forall c2 : children y, childnodes y c2 <ᵣ childnodes x c1
with rLe_inv (x : Tree) (y : Tree) (H_rLe : x ≦ᵣ y) {struct H_rLe}
  : forall c1 : children x, exists c2 : children y, childnodes x c1 ≦ᵣ childnodes y c2.
Proof.
  - destruct H_rLt as [[c2 H_rLe]]. exists c2. intros c1.
    pose proof (rLe_inv y (childnodes x c2) H_rLe c1) as [c H_rLe'].
    econs. exists c. exact H_rLe'.
  - destruct H_rLe as [H_rLt]. intros c1.
    pose proof (rLt_inv y (childnodes x c1) (H_rLt c1)) as [c2 H_rLt'].
    exists c2. econs. exact H_rLt'.
Qed.

Lemma rLe_refl x
  : x ≦ᵣ x.
Proof.
  induction x as [cx tsx IH]; simpl; eauto with *.
Qed.

Lemma rLe_trans x y z
  (LE1 : x ≦ᵣ y)
  (LE2 : y ≦ᵣ z)
  : x ≦ᵣ z.
Proof.
  revert x y z LE1 LE2.
  induction x as [csx tsnx IH], y as [csy tsy], z as [csz tsz]; simpl.
  intros [H_rLt1] [H_rLt2]. econs. intros c. simpl in *.
  pose proof (H_rLt1 c) as [[c' H_rLe1]]. simpl in *.
  pose proof (H_rLt2 c') as [[c'' H_rLe2]]. simpl in *.
  eauto with *.
Qed.

#[global]
Instance rLe_PreOrder : PreOrder rLe :=
  { PreOrder_Reflexive := rLe_refl
  ; PreOrder_Transitive := rLe_trans
  }.

Definition rEq_asSetoid : isSetoid Tree :=
  mkSetoidFromPreOrder rLe_PreOrder.

Definition rEq (lhs : Tree) (rhs : Tree) : Prop :=
  rEq_asSetoid.(eqProp) lhs rhs.

Infix "=ᵣ" := rEq (at level 70, no associativity) : type_scope.

Lemma rEq_iff x y
  : x =ᵣ y <-> (x ≦ᵣ y /\ y ≦ᵣ x).
Proof.
  reflexivity.
Defined.

#[global] Hint Rewrite rEq_iff : simplication_hints.

#[global]
Instance rEq_Equivalence : Equivalence rEq :=
  rEq_asSetoid.(eqProp_Equivalence).

#[global]
Instance rLe_PartialOrder : PartialOrder rEq rLe :=
  mkSetoidFromPreOrder_good rLe_PreOrder.

Lemma rLe_eqTree_rLe x y z
  (H_rLe : x ≦ᵣ y)
  (EQ : y == z)
  : x ≦ᵣ z.
Proof.
  revert y z H_rLe EQ. induction x as [csx tsx IH].
  intros [csy tsy] [csz tsz] [H_rLt] [y_subseteq_z z_subseteq_y]. econs; intros cx. simpl in *.
  pose proof (H_rLt cx) as [[cy ?]]. pose proof (y_subseteq_z cy) as [cz ?]. eauto with *.
Qed.

Lemma eqTree_rLe_rLe x y z
  (EQ : x == y)
  (H_rLe : y ≦ᵣ z)
  : x ≦ᵣ z.
Proof.
  revert y z H_rLe EQ. induction x as [csx tsx IH].
  intros [csy tsy] [csz tsz] [H_rLt] [x2y y2x]. econs; intros cx. simpl in *.
  pose proof (x2y cx) as [cy ?]. pose proof (H_rLt cy) as [[cz ?]]. eauto with *.
Qed.

#[global] Hint Resolve rLe_eqTree_rLe eqTree_rLe_rLe : aczel_hints.

#[global]
Add Parametric Morphism
  : rLe with signature (eqProp ==> eqProp ==> iff)
  as rLe_compatWith_eqProp.
Proof.
  intros x1 x2 x_EQ y1 y2 y_EQ. split; i.
  - eapply rLe_eqTree_rLe; eauto. eapply eqTree_rLe_rLe; eauto. done.
  - eapply rLe_eqTree_rLe; eauto. eapply eqTree_rLe_rLe; eauto. done.
Qed.

#[global]
Add Parametric Morphism
  : rEq with signature (eqProp ==> eqProp ==> iff)
  as rEq_compatWith_eqProp.
Proof.
  intros x1 x2 x_EQ y1 y2 y_EQ. split; intros H_rEq.
  - rewrite rEq_iff in *. rewrite -> x_EQ, -> y_EQ in H_rEq. done.
  - rewrite rEq_iff in *. rewrite <- x_EQ, <- y_EQ in H_rEq. done.
Qed.

#[global]
Add Parametric Morphism
  : rLt with signature (eqProp ==> eqProp ==> iff)
  as rLt_compatWith_eqProp.
Proof.
  intros x1 x2 x_EQ y1 y2 y_EQ. split; intros [[c H_rLe]].
  - pose proof (member_intro (children y1) (childnodes y1) c) as IN.
    rewrite Tree_eta in IN. rewrite -> y_EQ in IN at 2. destruct IN as [c' EQ'].
    econs. exists c'. rewrite <- EQ'. rewrite <- x_EQ. exact H_rLe.
  - pose proof (member_intro (children y2) (childnodes y2) c) as IN.
    rewrite Tree_eta in IN. rewrite <- y_EQ in IN at 2. destruct IN as [c' EQ'].
    econs. exists c'. rewrite <- EQ'. rewrite -> x_EQ. exact H_rLe.
Qed.

Lemma rLt_implies_rLe lhs rhs
  (H_rLt : lhs <ᵣ rhs)
  : lhs ≦ᵣ rhs.
Proof.
  rename lhs into x, rhs into y.
  destruct H_rLt as [[cy H_rLe]].
  rewrite -> H_rLe. clear x H_rLe.
  induction y as [csy tsy IH]. simpl in *.
  specialize IH with (c := cy).
  destruct (tsy cy) as [csz tsz] eqn: cy_EQ_z.
  econs. intros cz. specialize IH with (cy := cz).
  rewrite <- cy_EQ_z in IH. eauto with *.
Qed.

Lemma member_implies_rLt x y
  (IN : x \in y)
  : x <ᵣ y.
Proof.
  destruct IN as [c EQ]. econs. exists c. eauto with *.
Qed.

Lemma subseteq_implies_rLe x y
  (SUBSET : x \subseteq y)
  : x ≦ᵣ y.
Proof.
  econs. intros c. eapply member_implies_rLt.
  exact (SUBSET (childnodes x c) (member_intro _ _ _)).
Qed.

#[global] Hint Resolve rLt_implies_rLe member_implies_rLt : aczel_hints.

Lemma rLe_rLt_rLt x y z
  (x_rLe_y : x ≦ᵣ y)
  (y_rLt_z : y <ᵣ z)
  : x <ᵣ z.
Proof.
  destruct y_rLt_z as [[c rLe]]. econs. exists c. transitivity y; eauto with *.
Qed.

Lemma rLt_rLe_rLt x y z
  (x_rLt_y : x <ᵣ y)
  (y_rLe_z : y ≦ᵣ z)
  : x <ᵣ z.
Proof.
  destruct y as [csy tsy]. destruct x_rLt_y as [[cy x_rLe_cy]]. destruct z as [csz tsz]. destruct y_rLe_z as [H_rLt].
  simpl in *. pose proof (H_rLt cy) as [[cz cy_rLe_cz]]. econs. exists cz. transitivity (tsy cy); eauto with *.
Qed.

#[local] Hint Resolve rLe_rLt_rLt rLt_rLe_rLt : core.

#[global]
Add Parametric Morphism
  : rLt with signature (rEq ==> rEq ==> iff)
  as rLt_compatWith_rEq.
Proof.
  i. destruct H, H0. split; eauto.
Qed.

#[global]
Add Parametric Morphism
  : rLe with signature (rEq ==> rEq ==> iff)
  as rLe_compatWith_rEq.
Proof.
  i. destruct H, H0. split; etransitivity; eauto; etransitivity; eauto.
Qed.

#[global]
Add Parametric Morphism
  : rLt with signature (eqProp ==> eqProp ==> iff) as rLt_compatWith_eq.
Proof.
  intros x1 y1 EQ1 x2 y2 EQ2. split; intros [[w H_rLe]].
  - eapply rLt_rLe_rLt with (y := x2).
    + econs. eexists. rewrite <- EQ1. exact H_rLe.
    + now rewrite -> EQ2.
  - eapply rLt_rLe_rLt with (y := y2).
    + econs. eexists. rewrite -> EQ1. exact H_rLe.
    + now rewrite <- EQ2.
Qed.

Lemma rLt_eqPropCompatible2
  : eqPropCompatible2 (A_isSetoid := rEq_asSetoid) (B_isSetoid := rEq_asSetoid) rLt.
Proof.
  ii. change (rLt x1 y1 <-> rLt x2 y2). now rewrite <- x_EQ, <- y_EQ.
Qed.

Theorem rLt_wf
  : well_founded rLt.
Proof.
  intros rhs. remember rhs as lhs eqn: lhs_EQ_rhs.
  assert (lhs_rLe_rhs : lhs ≦ᵣ rhs) by now rewrite lhs_EQ_rhs.
  clear lhs_EQ_rhs. rename lhs into x, rhs into y, lhs_rLe_rhs into x_rLe_y.
  revert y x x_rLe_y. induction y as [csy tsy IH].
  intros [csx tsx] [x_rLe_y]. simpl in x_rLe_y.
  econstructor. intros z [[c [z_rLe_cx]]]. simpl in *.
  pose proof (x_rLe_y c) as [[c' H_rLe]]. eapply IH; transitivity (tsx c); eauto with *.
Qed.

#[global]
Instance rLt_StrictOrder
  : StrictOrder rLt.
Proof.
  split.
  - eapply well_founded_implies_Irreflexive. eapply rLt_wf.
  - intros x y z H_rLt1 H_rLt2. eapply rLe_rLt_rLt with (y := y); trivial. eapply rLt_implies_rLe; trivial.
Qed.

Lemma rLe_ext x y
  (EXT : forall z, z <ᵣ x -> z <ᵣ y)
  : x ≦ᵣ y.
Proof.
  econs. intros c. eapply EXT. eapply member_implies_rLt. eapply member_intro.
Qed.

Lemma rEq_ext x y
  (EXT : forall z, z <ᵣ x <-> z <ᵣ y)
  : x =ᵣ y.
Proof.
  rewrite rEq_iff. split; eapply rLe_ext; now firstorder.
Qed.

Lemma rLt_eqPropCompatible2_rEq
  : eqPropCompatible2 (A_isSetoid := rEq_asSetoid) (B_isSetoid := rEq_asSetoid) (C_isSetoid := Prop_isSetoid) rLt.
Proof.
  ii. change ((x1 <ᵣ y1) <-> (x2 <ᵣ y2)). now rewrite -> x_EQ, -> y_EQ.
Qed.

#[global]
Instance rLt_isWellOrdering : isWoset Tree (SETOID := rEq_asSetoid) :=
  { Woset_isWellPoset := {| wltProp := rLt; wltProp_Transitive := rLt_StrictOrder.(StrictOrder_Transitive); wltProp_well_founded := rLt_wf; |}
  ; Woset_eqPropCompatible2 := rLt_eqPropCompatible2_rEq
  ; Woset_ext_eq := rEq_ext
  }.

Lemma mkNode_rEq (t : Tree) (cs : Type@{Set_u}) (ts : cs -> Tree)
  : mkNode cs ts =ᵣ t <-> (forall u, t ≦ᵣ u <-> (forall c, ts c <ᵣ u)).
Proof.
  split.
  - intros H_EQ u. rewrite <- H_EQ. split.
    + intros [H_rLt]. exact H_rLt.
    + intros H_rLt. econs. exact H_rLt.
  - intros H_EQ. split.
    + econs. simpl. rewrite <- H_EQ. reflexivity.
    + rewrite -> H_EQ. intros c. econs. exists c. reflexivity.
Qed.

(** End RANK_COMPARISON. *)

Fixpoint fromAcc {A : Type@{Set_u}} {R : A -> A -> Prop} (x : A) (ACC : Acc R x) {struct ACC} : Tree :=
  match ACC with
  | Acc_intro _ ACC_INV => mkNode { y : A | R y x } (fun c => @fromAcc A R (proj1_sig c) (ACC_INV (proj1_sig c) (proj2_sig c)))
  end.

Lemma fromAcc_unfold (A : Type@{Set_u}) (R : A -> A -> Prop) (x : A) (ACC : Acc R x)
  : forall z, z \in @fromAcc A R x ACC <-> (exists c : { y : A | R y x }, z == fromAcc (proj1_sig c) (Acc_inv ACC (proj2_sig c))).
Proof.
  intros z. destruct ACC as [ACC_INV]; simpl in *. reflexivity.
Qed.

#[global] Hint Rewrite fromAcc_unfold : simplication_hints.

Fixpoint fromAcc_pirrel (A : Type@{Set_u}) (R : A -> A -> Prop) (x : A) (ACC : Acc R x) (ACC' : Acc R x) {struct ACC}
  : fromAcc x ACC == fromAcc x ACC'.
Proof.
  destruct ACC as [ACC_INV], ACC' as [ACC_INV']. eapply eqTree_intro.
  - intros z H_in. rewrite fromAcc_unfold in *. destruct H_in as [c EQ].
    pose proof (fromAcc_pirrel A R (proj1_sig c) (ACC_INV (proj1_sig c) (proj2_sig c)) (ACC_INV' (proj1_sig c) (proj2_sig c))) as claim.
    exists c. rewrite <- claim. exact EQ.
  - intros z H_in. rewrite fromAcc_unfold in *. destruct H_in as [c EQ].
    pose proof (fromAcc_pirrel A R (proj1_sig c) (ACC_INV (proj1_sig c) (proj2_sig c)) (ACC_INV' (proj1_sig c) (proj2_sig c))) as claim.
    exists c. rewrite -> claim. exact EQ.
Qed.

Lemma fromAcc_member_fromAcc_intro (A : Type@{Set_u}) (R : A -> A -> Prop) (x : A) (x' : A) (ACC : Acc R x) (ACC' : Acc R x')
  (R_x_x' : R x x')
  : fromAcc x ACC \in fromAcc x' ACC'.
Proof.
  rewrite fromAcc_unfold. exists (@exist _ _ x R_x_x'). simpl. eapply fromAcc_pirrel.
Qed.

Fixpoint fromAcc_isMonotonic (A : Type) (R1 : A -> A -> Prop) (R2 : A -> A -> Prop) (x : A) (INCL : forall x : A, forall x' : A, forall LE : R1 x x', R2 x x') (ACC1 : Acc R1 x) (ACC2 : Acc R2 x) {struct ACC1} : fromAcc x ACC1 ≦ᵣ fromAcc x ACC2.
Proof.
  destruct ACC1, ACC2; simpl. econs. simpl. intros [c R1_c_x]; simpl.
  econs. simpl. exists (@exist _ _ c (INCL c x R1_c_x)). simpl.
  eapply fromAcc_isMonotonic. exact INCL.
Qed.

Definition fromWf {A : Type@{Set_u}} (R : A -> A -> Prop) (R_wf : well_founded R) (x : A) : Tree :=
  @fromAcc A R x (R_wf x).

Lemma fromWf_unfold {A : Type@{Set_u}} (R : A -> A -> Prop) (R_wf : well_founded R) (x : A)
  : forall z, z \in @fromWf A R R_wf x <-> (exists y : A, R y x /\ z == @fromWf A R R_wf y).
Proof.
  intros z; split.
  - intros z_in. unfold fromWf in z_in. rewrite fromAcc_unfold in z_in. destruct z_in as [[y R_y_x] z_eq]; simpl proj1_sig in z_eq.
    exists y. split; trivial. rewrite z_eq. eapply fromAcc_pirrel.
  - intros (y & R_y_x & z_eq). rewrite z_eq. unfold fromWf. eapply fromAcc_member_fromAcc_intro. exact R_y_x.
Qed.

Lemma fromWf_isSupremum {A : Type@{Set_u}} (R : A -> A -> Prop) (R_wf : well_founded R) (t : Tree) (x : A)
  (LE : forall y : A, R y x -> @fromWf A R R_wf y <ᵣ t)
  : @fromWf A R R_wf x ≦ᵣ t.
Proof.
  unfold fromWf. destruct (R_wf x) as [ACC_INV]. simpl.
  econs. simpl. intros [y R_y_x]; simpl. rewrite fromAcc_pirrel. now eapply LE.
Qed.

Lemma fromWf_isMonotonic {A : Type} {R1 : A -> A -> Prop} {R2 : A -> A -> Prop} (x : A)
  (INCL : forall x : A, forall x' : A, forall LE : R1 x x', R2 x x')
  (R1_wf : well_founded R1)
  (R2_wf : well_founded R2)
  : @fromWf A R1 R1_wf x ≦ᵣ @fromWf A R2 R2_wf x.
Proof.
  unfold fromWf. eapply fromAcc_isMonotonic; eauto.
Qed.

Lemma fromWf_cong {A : Type} {B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) (f : A -> B)
  (RA_wf : well_founded RA)
  (RB_wf : well_founded RB)
  (f_cong : forall x1 : A, forall x2 : A, forall LT : RA x1 x2, RB (f x1) (f x2))
  : forall x : A, @fromWf A RA RA_wf x ≦ᵣ @fromWf B RB RB_wf (f x).
Proof.
  intros x. pose proof (RA_wf x) as H_ACC. induction H_ACC as [x _ IH].
  eapply rLe_ext. unfold fromWf. intros z LT. destruct LT as [[c LE]]; simpl in *.
  destruct (RA_wf x) as [H_Acc_inv]; simpl in *. destruct c as [c RA_c_x]; simpl in *.
  pose proof (IH _ RA_c_x) as H. unfold fromWf in *. econs.
  destruct (RB_wf (f x)) as [H_Acc_inv']; simpl. exists (@exist _ _ (f c) (f_cong c x RA_c_x)). simpl.
  rewrite LE. rewrite fromAcc_pirrel with (ACC' := RA_wf c). rewrite H.
  now rewrite fromAcc_pirrel with (A := B) (ACC := (H_Acc_inv' (f c) (f_cong c x RA_c_x))) (ACC' := RB_wf (f c)).
Qed.

Lemma fromWf_eq_fromWf_intro {A : Type} {B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) (f : A -> B)
  (RA_wf : well_founded RA)
  (RB_wf : well_founded RB)
  (f_sim : forall x' : A, forall y : B, (exists x : A, RA x x' /\ y = f x) <-> (exists y' : B, RB y y' /\ y' = f x'))
  : forall x : A, @fromWf A RA RA_wf x == @fromWf B RB RB_wf (f x).
Proof.
  intros x'. eapply extensionality. pose proof (RA_wf x') as H_ACC. induction H_ACC as [x' _ IH].
  intros z; split; intros z_in.
  - rewrite fromWf_unfold in z_in. destruct z_in as (x & H_RA & z_eq). rewrite z_eq. clear z z_eq.
    assert (exists y' : B, RB (f x) y' /\ y' = f x') as (y & H_RB & ->).
    { rewrite <- f_sim. exists x; split; trivial. }
    rewrite fromWf_unfold. exists (f x). split; trivial. eapply extensionality. eapply IH. exact H_RA.
  - rewrite fromWf_unfold in z_in. destruct z_in as (y & H_RB & z_eq). rewrite z_eq. clear z z_eq.
    assert (exists x : A, RA x x' /\ y = f x) as (x & H_RA & ->).
    { rewrite -> f_sim. exists (f x'); split; trivial. }
    rewrite fromWf_unfold. exists x. split; trivial. symmetry. eapply extensionality. eapply IH. exact H_RA.
Qed.

Definition fromWfSet {A : Type@{Set_u}} (R : A -> A -> Prop) (R_wf : well_founded R) : Tree :=
  mkNode A (@fromWf A R R_wf).

Lemma fromWfSet_isMonotonic {A : Type} {R1 : A -> A -> Prop} {R2 : A -> A -> Prop}
  (INCL : forall x : A, forall x' : A, forall LE : R1 x x', R2 x x')
  (R1_wf : well_founded R1)
  (R2_wf : well_founded R2)
  : @fromWfSet A R1 R1_wf ≦ᵣ @fromWfSet A R2 R2_wf.
Proof.
  econs. i. econs. exists c. eapply fromWf_isMonotonic; eauto.
Qed.

Lemma fromWfSet_cong {A : Type} {B : Type} (RA : A -> A -> Prop) (RB : B -> B -> Prop) (f : A -> B)
  (RA_wf : well_founded RA)
  (RB_wf : well_founded RB)
  (f_cong : forall x1 : A, forall x2 : A, forall LT : RA x1 x2, RB (f x1) (f x2))
  : @fromWfSet A RA RA_wf ≦ᵣ @fromWfSet B RB RB_wf.
Proof.
  unfold fromWfSet. econs. intros c. econs. simpl in *. exists (f c). eapply fromWf_cong; eauto.
Qed.

Definition succ (x : Tree) : Tree :=
  union x (singleton x).

Theorem succ_spec x
  : forall z, z \in succ x <-> (z \in x \/ z == x).
Proof.
  unfold succ. intros z. rewrite union_spec. rewrite singleton_spec. reflexivity.
Qed.

#[global] Hint Rewrite succ_spec : simplication_hints.

#[global]
Instance succ_eqPropCompatible1
  : eqPropCompatible1 succ.
Proof.
  ii. now eapply eqTree_intro; ii; rewrite succ_spec in *; [rewrite <- x_EQ | rewrite -> x_EQ].
Qed.

Lemma rEq_succ_iff (alpha : Tree) (beta : Tree)
  : alpha =ᵣ succ beta <-> (forall z, z <ᵣ alpha <-> z ≦ᵣ beta).
Proof.
  split.
  - intros H_rEq z. split.
    + intros H_LT. rewrite -> H_rEq in H_LT. clear alpha H_rEq.
      destruct H_LT as [[c H_rLe]]. simpl in *. destruct c as [[ | ] c]; simpl in *.
      * rewrite H_rLe. eapply rLt_implies_rLe. eapply member_implies_rLt. now exists c.
      * destruct c; simpl; trivial.
    + intros H_rLe. rewrite -> H_rEq. econs. simpl. refine (let c : children (singleton beta) := true in _).
      exists (@existT bool (fun i : bool => children (if i then beta else singleton beta)) false c); eauto.
  - intros H_sup. eapply rEq_ext. intros z; split.
    + intros H_rLt. econs. simpl. refine (let c : children (singleton beta) := true in _).
      exists (@existT bool (fun i : bool => children (if i then beta else singleton beta)) false c). ss!.
    + intros [[c H_rLe]]. simpl in *. destruct c as [[ | ] c]; simpl in *.
      * rewrite -> H_sup. eapply rLt_implies_rLe. eapply rLe_rLt_rLt; eauto. eapply member_implies_rLt. now exists c.
      * rewrite -> H_sup. destruct c; simpl; trivial.
Qed.

Lemma succ_rLe_intro alpha beta
  (H_rLt : alpha <ᵣ beta)
  : succ alpha ≦ᵣ beta.
Proof.
  econs. intros [[ | ] c]; simpl.
  - transitivity alpha; eauto. eapply member_implies_rLt. exists c. reflexivity.
  - destruct c as [ | ]; simpl in *; eauto.
Qed.

Lemma rLt_succ_intro alpha
  : alpha <ᵣ succ alpha.
Proof.
  econs. simpl. now exists (@existT _ _ false true); simpl.
Qed.

Definition isTransitiveSet (x : Tree) : Prop :=
  forall y, y \in x -> forall z, z \in y -> z \in x.

#[global] Hint Unfold isTransitiveSet : aczel_hints.

#[global]
Instance isTransitiveSet_compatWith_eqTree
  : isCompatibleWith_eqProp isTransitiveSet.
Proof.
  intros alpha alpha_isTranstiveSet beta alpha_eq_beta.
  unfold isTransitiveSet in *; ii; des.
  rewrite <- alpha_eq_beta in *; eauto with *.
Qed.

Section ORDINAL_basic1.

#[local] Transparent eqProp.

Variant isOrdinal (alpha : Tree) : Prop :=
  | transitive_set_of_transitive_sets_isOrdinal
    (TRANS : isTransitiveSet alpha)
    (TRANS' : forall beta, beta \in alpha -> isTransitiveSet beta)
    : isOrdinal alpha.

#[local] Hint Constructors isOrdinal : core.

Lemma isOrdinal_member_isOrdinal alpha beta
  (ORDINAL : isOrdinal alpha)
  (MEMBER : beta \in alpha)
  : isOrdinal beta.
Proof.
  inversion ORDINAL; eauto with *.
Defined.

#[global]
Add Parametric Morphism
  : isOrdinal with signature (eqProp (isSetoid := Tree_isSetoid) ==> iff)
  as isOrdinal_eqPropCompatible.
Proof.
  intros alpha alpha' H; split; intros [? ?]; econs.
  - rewrite -> H in TRANS; eauto.
  - ii. eapply TRANS' with (y := y); eauto. rewrite -> H; eauto.
  - rewrite <- H in TRANS; eauto.
  - ii. eapply TRANS' with (y := y); eauto. rewrite <- H; eauto.
Qed.

Lemma fromWf_isOrdinal {A : Type} (R : A -> A -> Prop)
  (R_wf : well_founded R)
  (R_trans : Transitive R)
  : forall x : A, isOrdinal (@fromWf A R R_wf x).
Proof.
  econs.
  - intros y y_in. unfold fromWf in y_in. rewrite fromAcc_unfold in y_in.
    destruct y_in as [[c R_c_x] y_eq]. simpl proj1_sig in y_eq.
    rewrite fromAcc_pirrel with (ACC' := R_wf c) in y_eq. change (y == @fromWf A R R_wf c) in y_eq.
    intros z z_in. rewrite y_eq in z_in. unfold fromWf in z_in |- *. rewrite fromAcc_unfold in z_in |- *.
    destruct z_in as [[c1 R_c1_c] z_eq]. exists (@exist _ _ c1 (R_trans c1 c x R_c1_c R_c_x)). simpl proj1_sig in z_eq |- *.
    rewrite z_eq. eapply fromAcc_pirrel.
  - intros beta H_in y y_in z z_in. rewrite fromWf_unfold in H_in. destruct H_in as (c & R_c_x & beta_eq).
    rewrite -> beta_eq in y_in |- *. rewrite fromWf_unfold in y_in. destruct y_in as (c1 & R_c1_c & y_eq).
    rewrite y_eq in z_in. rewrite fromWf_unfold in z_in. destruct z_in as (c2 & R_c2_c1 & z_eq).
    rewrite z_eq. rewrite fromWf_unfold. exists c2. split; eauto with *.
Qed.

End ORDINAL_basic1.

Module Totalify.

Section well_founded_to_Woset.

Context {A : Type@{Set_u}} (R : A -> A -> Prop) (R_wf : well_founded R).

#[local] Notation hash := (@fromWf A R R_wf).

#[local]
Instance mkSetoid_from_wellfounded : isSetoid A :=
  { eqProp x y := hash x =ᵣ hash y 
  ; eqProp_Equivalence := relation_on_image_liftsEquivalence rEq_asSetoid.(eqProp_Equivalence) hash
  }.

Definition hash_rLt (x : A) (y : A) : Prop :=
  hash x <ᵣ hash y.

#[local]
Instance mkWellPoset_from_wellfounded : isWellPoset A :=
  { wltProp := hash_rLt
  ; wltProp_well_founded := relation_on_image_liftsWellFounded rLt hash rLt_wf
  ; wltProp_Transitive x y z := rLt_StrictOrder.(StrictOrder_Transitive) (hash x) (hash y) (hash z)
  }.

Lemma hash_rLt_eqPropCompatible2
  : eqPropCompatible2 hash_rLt.
Proof.
  ii. change (hash x1 <ᵣ hash y1 <-> hash x2 <ᵣ hash y2).
  change (hash x1 =ᵣ hash x2) in x_EQ.
  change (hash y1 =ᵣ hash y2) in y_EQ.
  now rewrite -> x_EQ, -> y_EQ.
Qed.

Lemma hash_preserves (x : A) (y : A)
  (H_R : R x y)
  : hash_rLt x y.
Proof.
  red. eapply member_implies_rLt.
  unfold fromWf. now eapply fromAcc_member_fromAcc_intro.
Qed.

Lemma hash_rLt_extensionality (x : A) (y : A)
  (EXT_EQ : forall z, hash_rLt z x <-> hash_rLt z y)
  : hash x =ᵣ hash y.
Proof.
  eapply rEq_ext. intros z.
  unfold hash_rLt in EXT_EQ.
  split; intros H_rLt.
  - unfold fromWf in H_rLt.
    destruct (R_wf x) as [ACC_INV]; simpl in H_rLt.
    destruct H_rLt as [[[c R_c_x] H_rLe]]; simpl in *.
    pose proof (hash_preserves c x R_c_x) as claim1. red in claim1.
    eapply rLe_rLt_rLt; eauto.
    rewrite -> EXT_EQ in claim1. erewrite fromAcc_pirrel. exact claim1.
  - unfold fromWf in H_rLt.
    destruct (R_wf y) as [ACC_INV]; simpl in H_rLt.
    destruct H_rLt as [[[c R_c_y] H_rLe]]; simpl in *.
    pose proof (hash_preserves c y R_c_y) as claim1. red in claim1.
    eapply rLe_rLt_rLt; eauto.
    rewrite <- EXT_EQ in claim1. erewrite fromAcc_pirrel. exact claim1.
Qed.

#[local]
Instance mkWoset_from_wellfounded : isWoset A :=
  { Woset_isWellPoset := mkWellPoset_from_wellfounded
  ; Woset_eqPropCompatible2 := hash_rLt_eqPropCompatible2
  ; Woset_ext_eq := hash_rLt_extensionality
  }.

Lemma fromWf_rEq (x : A)
  : @fromWf A R R_wf x =ᵣ @fromWf A wltProp wltProp_well_founded x.
Proof.
  enough (WTS : forall t : Tree, forall x : A, @fromWf A R R_wf x <ᵣ t -> @fromWf A R R_wf x =ᵣ @fromWf A wltProp wltProp_well_founded x).
  { eapply WTS with (t := succ (@fromWf A R R_wf x)). eapply rLt_succ_intro. }
  intros t. rename x into a. pose proof (rLt_wf t) as H_Acc. induction H_Acc as [t _ IH]; intros x H_rLt. split.
  - eapply fromWf_isMonotonic. intros b c H_R. red. red. eapply hash_preserves. exact H_R.
  - eapply fromWf_isSupremum. intros y y_wlt_x. do 2 red in y_wlt_x. rewrite <- IH with (y := @fromWf A R R_wf x); eauto.
Qed.

Lemma fromWfSet_rEq
  : @fromWfSet A R R_wf =ᵣ @fromWfSet A wltProp wltProp_well_founded.
Proof.
  now split; simpl; econs; simpl; intros c; econs; simpl; exists c; rewrite fromWf_rEq.
Qed.

End well_founded_to_Woset.

End Totalify.

Section toWellPoset.

Inductive le_insert_top {A : Type} (le : A -> A -> Prop) (x : option A) : option A -> Prop :=
  | le_insert_top_rhs_None
    : le_insert_top le x None
  | le_insert_top_rhs_Some x' y'
    (EQ : x = Some x')
    (LE : le x' y')
    : le_insert_top le x (Some y').

#[local] Hint Constructors le_insert_top : simplication_hints.

Definition toWellPoset_lt {Idx : Type@{Set_u}} {A : Idx -> Type} (lt : forall i : Idx, A i -> A i -> Prop) (lhs : { i : Idx & option (A i) }) (rhs : { i : Idx & option (A i) }) : Prop :=
  exists x : option (A (projT1 rhs)), le_insert_top (fun a : A (projT1 rhs) => fun a' : A (projT1 rhs) => lt (projT1 rhs) a a' \/ a = a') x (projT2 rhs) /\ lhs = @existT _ _ (projT1 rhs) x /\ rhs <> @existT _ _ (projT1 rhs) x.

Lemma toWellPoset_lt_well_founded {Idx : Type@{Set_u}} {A : Idx -> Type} (lt : forall i : Idx, A i -> A i -> Prop)
  (lt_wf : forall i : Idx, well_founded (lt i))
  : well_founded (toWellPoset_lt lt).
Proof.
  enough (WTS : forall i : Idx, forall x' : A i, Acc (toWellPoset_lt lt) (@existT _ _ i (Some x'))).
  { intros [i1 [x1' | ]]; eauto. econs. intros [i2 x2]. unfold toWellPoset_lt at 1. intros (x3 & H_le_insert_top & EQ & NE); simpl in *. rewrite EQ. destruct x3 as [x3' | ]; eauto. congruence. }
  intros i x. induction (lt_wf i x) as [x _ IH]. i. econs. i. inv H. des; subst. inv H0. destruct LE; eauto. subst x'. simpl in *; congruence.
Qed.

Lemma toWellPoset_lt_Transitive {projT2_eq : forall A : Type, forall B : A -> Type, forall x : A, forall y : B x, forall y' : B x, @existT A B x y = @existT A B x y' -> y = y'} {Idx : Type@{Set_u}} {A : Idx -> Type} (lt : forall i : Idx, A i -> A i -> Prop)
  (lt_Irreflexive : forall i : Idx, Irreflexive (lt i))
  (lt_Transitive : forall i : Idx, Transitive (lt i))
  : Transitive (toWellPoset_lt lt).
Proof.
  red. intros [cx H_cx] [cy H_cy] [cz H_cz]; simpl.
  assert (le_Transitive : forall i, Transitive (fun lhs => fun rhs => lt i lhs rhs \/ lhs = rhs)).
  { intros i; specialize (lt_Transitive i). red in lt_Transitive |- *. ss!. }
  intros H1 H2. red in H1, H2 |- *. des; simpl in *.
  pose proof (lt_Transitive cy) as claim1. red in claim1. inv H1; inv H2; simpl in *.
  - destruct H_cx, x0, x; done!.
  - inv H0.
  - destruct x; inv H0. apply projT2_eq in H2. subst a. ss!. exists (Some x'); done!.
  - inv H0. inv H4. inv H2. destruct H_cx; inv H1. apply projT2_eq in H0, H2. subst a y'. destruct LE, LE0; ss!.
    exists (Some x'); ss!; ss!. intros H_contra. apply projT2_eq in H_contra. inv H_contra.
    contradiction (lt_Irreflexive cz x'); ss!.
Qed.

Lemma fromWf_toWoset_lt {projT2_eq : forall A : Type, forall B : A -> Type, forall x : A, forall y : B x, forall y' : B x, @existT A B x y = @existT A B x y' -> y = y'} (A : Type) (B : A -> Type) (R : forall i : A, B i -> B i -> Prop) (R_wf : forall i : A, well_founded (R i)) (i : A) (x : B i)
  : fromWf (toWellPoset_lt R) (toWellPoset_lt_well_founded R R_wf) (@existT _ _ i (Some x)) == fromWf (R i) (R_wf i) x.
Proof.
  symmetry. pose proof (R_wf i x) as H_Acc. unfold fromWf.
  induction H_Acc as [x _ IH]; simpl. eapply extensionality. intros z; split; intros H_IN.
  - rewrite fromAcc_unfold in H_IN |- *. destruct H_IN as [[y R_y_x] EQ]; simpl in *.
    assert (toWellPoset_lt R (existT _ i (Some y)) (existT _ i (Some x))) as claim1.
    { exists (Some y); ss!.
      - econs 2; ss!.
      - intros H_contra. apply projT2_eq in H_contra. inv H_contra. contradiction (well_founded_implies_Irreflexive (R i) (R_wf i) y).
    }
    exists (@exist _ _ (@existT _ _ i (Some y)) claim1). simpl. rewrite EQ. rewrite <- fromAcc_pirrel. rewrite IH; eauto. eapply fromAcc_pirrel.
  - rewrite fromAcc_unfold in H_IN |- *. destruct H_IN as [[y R_y_x] EQ]; simpl in *. destruct y as [i' x'].
    pose proof (COPY := R_y_x). inv COPY. ss!. inv H. destruct LE.
    + inv H0. apply projT2_eq in H4. subst x'. exists (@exist _ _ x'0 H). simpl. rewrite EQ. symmetry. rewrite <- fromAcc_pirrel. erewrite IH; eauto. eapply fromAcc_pirrel.
    + done!.
Qed.

Lemma fromWfSet_toWoset_lt_superset {projT2_eq : forall A : Type, forall B : A -> Type, forall x : A, forall y : B x, forall y' : B x, @existT A B x y = @existT A B x y' -> y = y'} (A : Type) (B : A -> Type) (R : forall i : A, B i -> B i -> Prop) (R_wf : forall i : A, well_founded (R i))
  : mkNode A (fun i : A => fromWfSet (R i) (R_wf i)) \subseteq fromWfSet (toWellPoset_lt R) (toWellPoset_lt_well_founded R R_wf).
Proof.
  unfold fromWfSet. intros z H_EQ. ss!. simpl in *. eexists (@existT _ _ x None). simpl. rewrite H. clear z H. eapply extensionality. intros z; split; intros H_EQ.
  - ss!. simpl in *. rewrite H. erewrite <- @fromWf_toWoset_lt at 1; eauto. unfold fromWf. eapply fromAcc_member_fromAcc_intro. exists (Some x0). ss!; done!.
  - unfold fromWf in H_EQ. rewrite fromAcc_unfold in H_EQ. ss!. destruct x0 as [[i y] H_y]; simpl in *. pose proof (COPY := H_y). inv COPY. ss!. inv H0. destruct x0; ss!. inv H1. apply projT2_eq in H4. subst y. exists b. simpl. rewrite H. rewrite <- @fromWf_toWoset_lt; eauto. eapply fromAcc_pirrel.
Qed.

Lemma fromWfSet_toWoset_lt_rEq {projT2_eq : forall A : Type, forall B : A -> Type, forall x : A, forall y : B x, forall y' : B x, @existT A B x y = @existT A B x y' -> y = y'} (A : Type) (B : A -> Type) (R : forall i : A, B i -> B i -> Prop) (R_wf : forall i : A, well_founded (R i))
  : fromWfSet (toWellPoset_lt R) (toWellPoset_lt_well_founded R R_wf) =ᵣ mkNode A (fun i : A => fromWfSet (R i) (R_wf i)).
Proof.
  split; cycle 1.
  - eapply subseteq_implies_rLe. eapply @fromWfSet_toWoset_lt_superset; eauto.
  - econs. intros c. simpl in *. destruct c as [i [y | ]].
    + rewrite @fromWf_toWoset_lt; eauto. transitivity (fromWfSet (R i) (R_wf i)); eapply member_implies_rLt; ss!. exists i; ss!.
    + econs. exists i. simpl. unfold fromWfSet. eapply subseteq_implies_rLe. intros z z_in. simpl.
      unfold fromWf in z_in. rewrite fromAcc_unfold in z_in. des. destruct c as [[i' x] ?]; simpl in *.
      pose proof (COPY := t); inv COPY. des. ss!. inv H0. apply projT2_eq in H4. subst x0. inv H. destruct x; try contradiction.
      exists b. simpl. rewrite z_in. rewrite <- @fromWf_toWoset_lt; eauto. eapply fromAcc_pirrel. 
Qed.

Lemma fromWf_toWoset_Some_in_fromWf_toWoset_Some_iff {projT2_eq : forall A : Type, forall B : A -> Type, forall x : A, forall y : B x, forall y' : B x, @existT A B x y = @existT A B x y' -> y = y'} (A : Type) (B : A -> Type) (R : forall i : A, B i -> B i -> Prop) (R_wf : forall i : A, well_founded (R i)) x y
  : fromWf (toWellPoset_lt R) (toWellPoset_lt_well_founded R R_wf) x \in fromWf (toWellPoset_lt R) (toWellPoset_lt_well_founded R R_wf) y <-> (exists z, toWellPoset_lt R z y /\ fromWf (toWellPoset_lt R) (toWellPoset_lt_well_founded R R_wf) x == fromWf (toWellPoset_lt R) (toWellPoset_lt_well_founded R R_wf) z).
Proof.
  unfold fromWf. split; cycle 1.
  - intros H_LT. rewrite @fromAcc_unfold. des. exists (@exist _ _ z H_LT). simpl. rewrite H_LT0. eapply fromAcc_pirrel.
  - rewrite fromAcc_unfold. intros [[c H_LT] EQ]; simpl in *. exists c. ss!. rewrite EQ. eapply fromAcc_pirrel.
Qed.

Fixpoint toWellPoset (t : Tree) : { D : Type@{Set_u} & D -> D -> Prop } :=
  match t with
  | mkNode cs ts => @existT Type@{Set_u} (fun D : Type@{Set_u} => D -> D -> Prop) { c : cs & option (projT1 (toWellPoset (ts c))) } (toWellPoset_lt (fun c : cs => projT2 (toWellPoset (ts c))))
  end.

Lemma toWellPoset_well_founded (t : Tree)
  : @well_founded (projT1 (toWellPoset t)) (projT2 (toWellPoset t)).
Proof.
  induction t as [cs ts IH]; simpl in *.
  eapply toWellPoset_lt_well_founded. exact IH.
Defined.

Lemma toWellPoset_Transitive {projT2_eq : forall A : Type, forall B : A -> Type, forall x : A, forall y : B x, forall y' : B x, @existT A B x y = @existT A B x y' -> y = y'} (t : Tree)
  : @Transitive (projT1 (toWellPoset t)) (projT2 (toWellPoset t)).
Proof.
  induction t as [cs ts IH]; simpl. eapply @toWellPoset_lt_Transitive; eauto.
  intros i. eapply well_founded_implies_Irreflexive. eapply toWellPoset_well_founded.
Qed.

Theorem fromWfSet_toWellPoset_rEq {projT2_eq : forall A : Type, forall B : A -> Type, forall x : A, forall y : B x, forall y' : B x, @existT A B x y = @existT A B x y' -> y = y'} (t : Tree)
  : @fromWfSet (projT1 (toWellPoset t)) (projT2 (toWellPoset t)) (toWellPoset_well_founded t) =ᵣ t.
Proof.
  induction t as [cs ts IH]. simpl. rewrite -> @fromWfSet_toWoset_lt_rEq; eauto. split; econs; intros c; simpl in *; econs; exists c; simpl; rewrite IH; reflexivity.
Qed.

Lemma fromWf_toWellPoset_in_fromWf_toWellPoset {projT2_eq : forall A : Type, forall B : A -> Type, forall x : A, forall y : B x, forall y' : B x, @existT A B x y = @existT A B x y' -> y = y'} (t : Tree) (x : projT1 (toWellPoset t)) (y : projT1 (toWellPoset t))
  (H_lt : projT2 (toWellPoset t) x y)
  : fromWf (projT2 (toWellPoset t)) (toWellPoset_well_founded t) x \in fromWf (projT2 (toWellPoset t)) (toWellPoset_well_founded t) y.
Proof.
  revert t x y H_lt. pose proof (@fromWf_toWoset_lt projT2_eq) as claim1. induction t as [cs ts IH]; simpl; i. rewrite @fromWf_toWoset_Some_in_fromWf_toWoset_Some_iff; eauto. 
Qed.

Theorem fromWf_toWellPoset_in_fromWf_toWellPoset_iff {projT2_eq : forall A : Type, forall B : A -> Type, forall x : A, forall y : B x, forall y' : B x, @existT A B x y = @existT A B x y' -> y = y'} (t : Tree) (x : projT1 (toWellPoset t)) (y : projT1 (toWellPoset t))
  : fromWf (projT2 (toWellPoset t)) (toWellPoset_well_founded t) x \in fromWf (projT2 (toWellPoset t)) (toWellPoset_well_founded t) y <-> (exists z : projT1 (toWellPoset t), projT2 (toWellPoset t) z y /\ fromWf (projT2 (toWellPoset t)) (toWellPoset_well_founded t) x == fromWf (projT2 (toWellPoset t)) (toWellPoset_well_founded t) z).
Proof.
  split.
  - pose proof (@fromWf_toWoset_lt projT2_eq) as lemma1.
    unfold fromWf in *. revert x y. induction t as [cs ts IH]; simpl; intros ? ? H_IN. destruct x as [cx x], y as [cy y]. destruct x as [x | ], y as [y | ]; simpl in *.
    + pose proof (COPY := H_IN). do 2 rewrite lemma1 with (A := cs) (B := fun c => projT1 (toWellPoset (ts c))) in COPY. rewrite fromAcc_unfold in COPY. destruct COPY as [[z H_R] EQ]; simpl in *.
      exists (@existT _ _ cy (Some z)). split.
      { exists (Some z). ss!.
        - econs 2; ss!.
        - intros H_contra. apply projT2_eq in H_contra. inv H_contra. contradiction (well_founded_implies_Irreflexive _ (toWellPoset_well_founded (ts cy)) z).
      }
      { do 2 rewrite lemma1 with (A := cs) (B := fun c => projT1 (toWellPoset (ts c))). symmetry. rewrite <- fromAcc_pirrel. symmetry. exact EQ. }
    + pose proof (COPY := H_IN). rewrite lemma1 with (A := cs) (B := fun c => projT1 (toWellPoset (ts c))) in COPY. rewrite fromAcc_unfold in COPY. destruct COPY as [[z H_R] EQ]; simpl in *.
      exists z. split; eauto. symmetry. rewrite fromAcc_pirrel. rewrite <- EQ. symmetry. rewrite lemma1 with (A := cs) (B := fun c => projT1 (toWellPoset (ts c))). eapply fromAcc_pirrel.
    + pose proof (COPY := H_IN). rewrite lemma1 with (A := cs) (B := fun c => projT1 (toWellPoset (ts c))) in COPY. rewrite fromAcc_unfold in COPY. destruct COPY as [[z H_R] EQ]; simpl in *.
      rewrite EQ in H_IN. rewrite fromAcc_unfold in H_IN. destruct H_IN as [[c' H_LT'] EQ']; simpl in *. destruct H_LT' as [w [H_LT' [? NE']]]; subst c'; simpl in *. pose proof (COPY := H_LT'). inv COPY. ss!. exists (@existT _ _ cy (Some z)). split.
      { exists (Some z); ss!.
        - econs 2; ss!.
        - intros H_contra. apply projT2_eq in H_contra. inv H_contra. contradiction (well_founded_implies_Irreflexive _ (toWellPoset_well_founded (ts cy)) z).
      }
      { rewrite lemma1 with (A := cs) (B := fun c => projT1 (toWellPoset (ts c))). symmetry. rewrite <- fromAcc_pirrel. symmetry. exact EQ. }
    + pose proof (COPY := H_IN). rewrite fromAcc_unfold in COPY. destruct COPY as [[z H_R] EQ]; simpl in *.
      exists z. split; eauto. symmetry. rewrite fromAcc_pirrel. rewrite <- EQ. symmetry. reflexivity.
  - intros (z & H_LT & EQ). pose proof (COPY := H_LT). apply @fromWf_toWellPoset_in_fromWf_toWellPoset in COPY; eauto. rewrite EQ. eauto.
Qed.

End toWellPoset.
