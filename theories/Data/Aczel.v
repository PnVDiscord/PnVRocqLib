Require Import PvN.Prelude.Prelude.

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

Definition power (x : Tree) : Tree :=
  mkNode (children x -> Prop) (filterc x).

Theorem power_spec x
  : forall z, z \in power x <-> z \subseteq x.
Proof.
  intros z. rewrite subset_filterc. unfold power. eauto with *.
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

Definition bigcup (x : Tree) : Tree :=
  indexed_union (children x) (childnodes x).

Theorem bigcup_spec x
  : forall z, z \in bigcup x <-> exists y, z \in y /\ y \in x.
Proof.
  intros z. unfold bigcup. rewrite indexed_union_spec. split.
  - intros [i [c EQ]]; simpl in *; exists (childnodes x i); split; eauto with *.
  - intros [y [IN [c EQ]]]; simpl in *. exists c. rewrite <- EQ. exact IN.
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

Definition union (x1 : Tree) (x2 : Tree) : Tree :=
  bigcup (upair x1 x2).

Theorem union_spec x1 x2
  : forall z, z \in union x1 x2 <-> z \in x1 \/ z \in x2.
Proof.
  intros z. unfold union. rewrite bigcup_spec. split.
  - intros [y [IN IN']]; rewrite upair_spec in IN'.
    destruct IN' as [EQ | EQ]; rewrite EQ in IN; eauto.
  - intros [IN | IN]; [exists x1 | exists x2]; rewrite upair_spec; eauto with *.
Qed.

Definition singleton (x : Tree) : Tree :=
  upair x x.

Theorem singleton_spec x
  : forall z, z \in singleton x <-> z == x.
Proof.
  intros z. unfold singleton. rewrite upair_spec. done.
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
  assert (claim1 : exists f : base_set -> Tree, forall x : base_set, P (childnodes X x) (f x)).
  { eapply AC with (P := fun x : base_set => fun y : Tree => P (childnodes X x) y)... }
  destruct claim1 as [f claim1]. exists (mkNode base_set (fun x => f x)). split.
  - intros x [c EQ]. exists (f c). split... eapply COMPAT1...
  - intros x [c EQ]. exists (childnodes X c). split... eapply COMPAT2...
Qed.

End STRONG_COLLECTION.
