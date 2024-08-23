Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.

Universe Set_u.

Universe Set_V.

Constraint Set_u < Set_V.

Create HintDb aczel_hints.

Inductive Tree : Type@{Set_V} :=
  | mkNode (cs : Type@{Set_u}) (ts : forall c : cs, Tree).

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

Theorem extenesionality x y
  (EXT_EQ : forall z, z \in x <-> z \in y)
  : x == y.
Proof.
  destruct x as [csx tsx], y as [csy tsy]; simpl; i. split; intros c.
  - pose proof (proj1 (EXT_EQ (tsx c)) (member_intro _ _ _)) as [c' EQ]; done.
  - pose proof (proj2 (EXT_EQ (tsy c)) (member_intro _ _ _)) as [c' EQ]; done.
Qed.

Definition isSubsetOf x y : Prop :=
  forall z, z \in x -> z \in y.

#[local] Infix "\subseteq" := isSubsetOf.

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
  - intros [LE GE]. eapply extenesionality; done.
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

Section SET_CONSTRUCTIONS.

#[local] Opaque eqProp.

Definition filterc (x : Tree) (P : children x -> Prop) : Tree :=
  mkNode (@sig (children x) P) (fun c => childnodes x (proj1_sig c)).

Theorem filterc_spec x P
  : forall z, z \in filterc x P <-> exists cx : children x, z == childnodes x cx /\ P cx.
Proof.
  intros z. split.
  - intros [[cx H_P] EQ]. simpl in *; eauto with *.
  - intros [cx [EQ H_P]]. exists (@exist _ _ cx H_P); eauto with *.
Qed.

Corollary subset_filterc x
  : forall z, z \subseteq x <-> exists P, z == filterc x P.
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
  : forall z, z \in filter P x <-> exists c, P (childnodes x c) /\ z == childnodes x c.
Proof.
  intros z. unfold filter. rewrite filterc_spec. done.
Qed.

Corollary filter_good P x
  (COMPAT : isCompatibleWith_eqProp P)
  : forall z, z \in filter P x <-> z \in x /\ P z.
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

#[global]
Instance power_eqPropCompatible1
  : eqPropCompatible1 power.
Proof.
  ii; eapply eqTree_intro; ii; rewrite power_spec in *; ii; [rewrite <- x_EQ | rewrite -> x_EQ]; eauto.
Qed.

Definition indexed_union (I : Type@{Set_u}) (x_i : I -> Tree) : Tree :=
  mkNode { i : I & children (x_i i) } (fun c => childnodes (x_i (projT1 c)) (projT2 c)).

Theorem indexed_union_spec I x_i
  : forall z, z \in indexed_union I x_i <-> exists i, z \in x_i i.
Proof.
  intros z. split.
  - intros [[i c] EQ]; simpl in *; eauto with *.
  - intros [i [c EQ]]; simpl in *; exists (@existT _ _ i c); eauto with *.
Qed.

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
  : forall z, z \in unions x <-> exists y, z \in y /\ y \in x.
Proof.
  intros z. unfold unions. rewrite indexed_union_spec. split.
  - intros [i [c EQ]]; simpl in *; exists (childnodes x i); split; eauto with *.
  - intros [y [IN [c EQ]]]; simpl in *. exists c. rewrite <- EQ. exact IN.
Qed.

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

Definition upair (x1 : Tree) (x2 : Tree) : Tree :=
  mkNode bool (fun b => if b then x1 else x2).

Theorem upair_spec x1 x2
  : forall z, z \in upair x1 x2 <-> z == x1 \/ z == x2.
Proof.
  intros z. split.
  - intros [[ | ] EQ]; simpl in *; eauto with *.
  - intros [EQ | EQ]; [exists true | exists false]; eauto with *.
Qed.

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
  : forall z, z \in union x1 x2 <-> z \in x1 \/ z \in x2.
Proof.
  intros z. unfold union. rewrite unions_spec. split.
  - intros [y [IN IN']]; rewrite upair_spec in IN'.
    destruct IN' as [EQ | EQ]; rewrite EQ in IN; eauto.
  - intros [IN | IN]; [exists x1 | exists x2]; rewrite upair_spec; eauto with *.
Qed.

#[global]
Instance union_eqPropCompatible2
  : eqPropCompatible2 union.
Proof.
  ii; eapply eqTree_intro; ii; rewrite union_spec in *; [rewrite <- x_EQ, <- y_EQ | rewrite -> x_EQ, -> y_EQ]; eauto with *.
Qed.

Definition intersection (x : Tree) (y : Tree) : Tree :=
  filter (fun z => z \in x) y.

Theorem intersection_spec x y
  : forall z, z \in intersection x y <-> z \in x /\ z \in y.
Proof.
  intros z. unfold intersection. rewrite filter_good.
  - done.
  - intros a IN b EQ. rewrite <- EQ. exact IN.
Qed.

#[global]
Instance intersection_eqPropCompatible2
  : eqPropCompatible2 intersection.
Proof.
  ii; eapply eqTree_intro; ii; rewrite intersection_spec in *; [rewrite <- x_EQ, <- y_EQ | rewrite -> x_EQ, -> y_EQ]; done.
Qed.

Definition singlton (x : Tree) : Tree :=
  upair x x.

Theorem singlton_spec x
  : forall z, z \in singlton x <-> z == x.
Proof.
  intros z. unfold singlton. rewrite upair_spec. done.
Qed.

Corollary singlton_inj x y
  (EQ : singlton x == singlton y)
  : x == y.
Proof.
  assert (IN : x \in singlton x) by now rewrite singlton_spec.
  rewrite EQ in IN. rewrite singlton_spec in IN. done.
Qed.

#[global]
Instance singlton_eqPropCompatible1
  : eqPropCompatible1 singlton.
Proof.
  ii. eapply eqTree_intro; ii.
  - rewrite singlton_spec in *. rewrite <- x_EQ. exact H.
  - rewrite singlton_spec in *. rewrite -> x_EQ. exact H.
Qed.

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
    + rewrite -> H_EQ'. symmetry. rewrite <- singlton_spec.
      unfold singlton. rewrite -> H_EQ' in EQ. rewrite -> EQ.
      rewrite upair_spec. now right.
    + eauto with *.
  - right. split; trivial. rewrite H_EQ in EQ.
    assert (IN : x2 \in upair x2 y2).
    { rewrite upair_spec. now left. }
    rewrite <- EQ in IN. rewrite upair_spec in IN.
    destruct IN as [H_EQ' | H_EQ'].
    + rewrite -> H_EQ'. symmetry. rewrite <- singlton_spec.
      unfold singlton. rewrite -> H_EQ' in EQ. rewrite <- EQ.
      rewrite upair_spec. now right.
    + eauto with *.
Qed.

Lemma singleton_eq_upair_implies x y z
  (EQ : singlton x == upair y z)
  : x == y /\ y == z.
Proof.
  revert x y z EQ. enough (WTS : forall x, forall y, forall z, singlton x == upair y z -> x == y).
  { ii. enough (ENOUGH : x == y).
    - split; trivial. rewrite comm in EQ. apply WTS in EQ. rewrite EQ in ENOUGH. done.
    - eapply WTS. exact EQ.
  }
  intros x y z EQ. unfold singlton in EQ. apply upair_eq_upair_implies in EQ. destruct EQ as [[EQ1 H_EQ] | [EQ1 H_EQ]]; done.
Qed.

Definition pair (x : Tree) (y : Tree) : Tree :=
  upair (singlton x) (upair x y).

Theorem pair_inv x1 x2 y1 y2
  (EQ : pair x1 y1 == pair x2 y2)
  : x1 == x2 /\ y1 == y2.
Proof.
  unfold pair in EQ. apply upair_eq_upair_implies in EQ. destruct EQ as [[EQ1 H_EQ] | [EQ1 H_EQ]].
  - apply singlton_inj in EQ1. split; trivial. apply upair_eq_upair_implies in H_EQ. destruct H_EQ as [[EQ2 EQ3] | [EQ2 EQ3]]; eauto with *.
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
  unions (filter (fun x => singlton x \in t) (unions t)).

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
      + rewrite upair_spec. left. rewrite <- singlton_spec. exact H_in.
      + exact H_in.
    - rewrite upair_spec in H_IN. rewrite EQ. clear t EQ. destruct H_IN as [EQ | EQ].
      + rewrite unions_spec. exists (singlton x). split.
        * rewrite singlton_spec. exact EQ.
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
          { apply singlton_inj in EQ'. rewrite <- EQ'. exact H_in. }
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

End SET_CONSTRUCTIONS.

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

Hypothesis AC : forall A : Type@{Set_u}, forall B : Type@{Set_V}, forall P : A -> B -> Prop, (forall x, exists y, P x y) -> (exists f, forall x, P x (f x)).

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

Inductive rLt (lhs : Tree) (rhs : Tree) : Prop :=
  | rLt_intro c
    (H_rLe : rLe lhs (childnodes rhs c))
    : rLt lhs rhs
with rLe (lhs : Tree) (rhs : Tree) : Prop :=
  | rLe_intro
    (H_rLt : forall c, rLt (childnodes lhs c) rhs)
    : rLe lhs rhs.

#[global] Hint Constructors rLt rLe : aczel_hints.

Infix "≦ᵣ" := rLe (at level 70, no associativity) : type_scope.

Infix "<ᵣ" := rLt (at level 70, no associativity) : type_scope.

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
  pose proof (H_rLt1 c) as [c' H_rLe1]. simpl in *.
  pose proof (H_rLt2 c') as [c'' H_rLe2]. simpl in *. eauto with *.
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

#[global] Hint Unfold rEq : aczel_hints.

#[global]
Instance rEq_Equivalence : Equivalence rEq :=
  rEq_asSetoid.(eqProp_Equivalence).

#[global]
Instance rLe_PartialOrder : PartialOrder rEq rLe :=
  mkSetoidFromPreOrder_derivesPartialOrder rLe_PreOrder.

Lemma rLe_eqTree_rLe x y z
  (H_rLe : x ≦ᵣ y)
  (EQ : y == z)
  : x ≦ᵣ z.
Proof.
  revert y z H_rLe EQ. induction x as [csx tsx IH].
  intros [csy tsy] [csz tsz] [H_rLt] [y_subseteq_z z_subseteq_y]. econs; intros cx. simpl in *.
  pose proof (H_rLt cx) as [cy ?]. pose proof (y_subseteq_z cy) as [cz ?]. eauto with *.
Qed.

Lemma eqTree_rLe_rLe x y z
  (EQ : x == y)
  (H_rLe : y ≦ᵣ z)
  : x ≦ᵣ z.
Proof.
  revert y z H_rLe EQ. induction x as [csx tsx IH].
  intros [csy tsy] [csz tsz] [H_rLt] [x2y y2x]. econs; intros cx. simpl in *.
  pose proof (x2y cx) as [cy ?]. pose proof (H_rLt cy) as [cz ?]. eauto with *.
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
  - do 4 red. do 4 red in H_rEq. rewrite -> x_EQ, -> y_EQ in H_rEq. done.
  - do 4 red. do 4 red in H_rEq. rewrite <- x_EQ, <- y_EQ in H_rEq. done.
Qed.

#[global]
Add Parametric Morphism
  : rLt with signature (eqProp ==> eqProp ==> iff)
  as rLt_compatWith_eqProp.
Proof.
  intros x1 x2 x_EQ y1 y2 y_EQ. split; intros [c H_rLe].
  - pose proof (member_intro (children y1) (childnodes y1) c) as IN.
    rewrite Tree_eta in IN. rewrite -> y_EQ in IN at 2. destruct IN as [c' EQ'].
    exists c'. rewrite <- EQ'. rewrite <- x_EQ. exact H_rLe.
  - pose proof (member_intro (children y2) (childnodes y2) c) as IN.
    rewrite Tree_eta in IN. rewrite <- y_EQ in IN at 2. destruct IN as [c' EQ'].
    exists c'. rewrite <- EQ'. rewrite -> x_EQ. exact H_rLe.
Qed.

Lemma rLt_implies_rLe lhs rhs
  (H_rLt : lhs <ᵣ rhs)
  : lhs ≦ᵣ rhs.
Proof.
  rename lhs into x, rhs into y.
  destruct H_rLt as [cy H_rLe].
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
  destruct IN as [c EQ]. exists c. eauto with *.
Qed.

#[global] Hint Resolve rLt_implies_rLe member_implies_rLt : aczel_hints.

Lemma rLe_rLt_rLt x y z
  (x_rLe_y : x ≦ᵣ y)
  (y_rLt_z : y <ᵣ z)
  : x <ᵣ z.
Proof.
  destruct y_rLt_z as [c rLe]. exists c. transitivity y; eauto with *.
Qed.

Lemma rLt_rLe_rLt x y z
  (x_rLt_y : x <ᵣ y)
  (y_rLe_z : y ≦ᵣ z)
  : x <ᵣ z.
Proof.
  destruct y as [csy tsy]. destruct x_rLt_y as [cy x_rLe_cy]. destruct z as [csz tsz]. destruct y_rLe_z as [H_rLt].
  simpl in *. unnw. pose proof (H_rLt cy) as [cz cy_rLe_cz]. exists cz. transitivity (tsy cy); eauto with *.
Qed.

#[local] Hint Resolve rLe_rLt_rLt rLt_rLe_rLt : core.

#[global]
Add Parametric Morphism
  : rLt with signature (eqProp ==> eqProp ==> iff) as rLt_compatWith_eq.
Proof.
  intros x1 y1 EQ1 x2 y2 EQ2. split; intros [w H_rLe].
  - eapply rLt_rLe_rLt with (y := x2).
    + eexists. rewrite <- EQ1. exact H_rLe.
    + now rewrite -> EQ2.
  - eapply rLt_rLe_rLt with (y := y2).
    + eexists. rewrite -> EQ1. exact H_rLe.
    + now rewrite <- EQ2.
Qed.

Theorem rLt_wf
  : well_founded rLt.
Proof.
  intros rhs. remember rhs as lhs eqn: lhs_EQ_rhs.
  assert (lhs_rLe_rhs : lhs ≦ᵣ rhs) by now rewrite lhs_EQ_rhs.
  clear lhs_EQ_rhs. rename lhs into x, rhs into y, lhs_rLe_rhs into x_rLe_y.
  revert y x x_rLe_y. induction y as [csy tsy IH].
  intros [csx tsx] [x_rLe_y]. simpl in x_rLe_y. unnw.
  econstructor. intros z [c [z_rLe_cx]]. simpl in *.
  pose proof (x_rLe_y c) as [c' H_rLe]. eapply IH; transitivity (tsx c); eauto with *.
Qed.

#[global]
Instance rLt_StrictOrder
  : StrictOrder rLt.
Proof.
  split.
  - eapply well_founded_implies_Irreflexive. eapply rLt_wf.
  - intros x y z H_rLt1 H_rLt2. eapply rLe_rLt_rLt with (y := y); trivial. eapply rLt_implies_rLe; trivial.
Qed.

Fixpoint fromAcc {A : Type@{Set_u}} {R : A -> A -> Prop} (x : A) (ACC : Acc R x) {struct ACC} : Tree :=
  match ACC with
  | Acc_intro _ ACC_INV => mkNode { y : A | R y x } (fun c => @fromAcc A R (proj1_sig c) (ACC_INV (proj1_sig c) (proj2_sig c)))
  end.

Lemma fromAcc_unfold {A : Type@{Set_u}} {R : A -> A -> Prop} x ACC
  : forall z, z \in @fromAcc A R x ACC <-> exists c : { y : A | R y x }, z == fromAcc (proj1_sig c) (Acc_inv ACC (proj2_sig c)).
Proof.
  intros z. destruct ACC as [ACC_INV]; simpl in *.
  split; intros [[c H_R] EQ]; rewrite eqTree_unfold in *; now exists (@exist _ _ c H_R).
Qed.

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

Definition fromWf {A : Type@{Set_u}} {R : A -> A -> Prop} (Wf : well_founded R) : Tree :=
  indexed_union A (fun i => @fromAcc A R i (Wf i)).

Definition isTransitiveSet (x : Tree) : Prop :=
  forall y, y \in x -> forall z, z \in y -> z \in x.

#[global] Hint Unfold isTransitiveSet : aczel_hints.

Lemma isTransitiveSet_compatWith_eqTree
  : isCompatibleWith_eqProp isTransitiveSet.
Proof.
  intros alpha alpha_isTranstiveSet beta alpha_eq_beta.
  unfold isTransitiveSet in *; ii; des.
  rewrite <- alpha_eq_beta in *; eauto with *.
Qed.

Variant isOrdinal (x : Tree) : Prop :=
  | transitive_set_of_transitive_sets_isOrdinal
    (TRANS : isTransitiveSet x)
    (TRANS' : forall y, y \in x -> isTransitiveSet y)
    : isOrdinal x.

#[global] Hint Constructors isOrdinal : aczel_hints.

Lemma every_member_of_Ordinal_isOrdinal (x : Tree)
  (ORDINAL : isOrdinal x)
  : forall y, y \in x -> isOrdinal y.
Proof.
  inv ORDINAL; eauto with *.
Qed.

Lemma isOrdinal_compatWith_eqTree
  : isCompatibleWith_eqProp isOrdinal.
Proof with eauto with *.
  intros alpha [? ?] beta alpha_eq_beta. split.
  - eapply isTransitiveSet_compatWith_eqTree...
  - intros gamma gamm_in_beta; unnw.
    rewrite <- alpha_eq_beta in gamm_in_beta...
Qed.

Lemma member_implies_subseteq_forOrdinal alpha beta
  (ORDINAL : isOrdinal alpha)
  (IN : beta \in alpha)
  : beta \subseteq alpha.
Proof.
  inv ORDINAL; eauto with *.
Qed.

#[global] Hint Resolve every_member_of_Ordinal_isOrdinal member_implies_subseteq_forOrdinal : aczel_hints.
