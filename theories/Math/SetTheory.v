Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Data.Aczel.

Module Type SetTheoreticConcepts.

Parameter V : Type@{Set_V}.

Parameter _eq : V -> V -> Prop.

Parameter _in : V -> V -> Prop.

Parameter _subseteq : V -> V -> Prop.

Parameter _comprehension : (V -> Prop) -> V -> V.

Parameter _emptyset : V.

Parameter _powerset : V -> V.

Parameter _unordered_pair : V -> V -> V.

Parameter _unions : V -> V.

Parameter Ord : Type@{Set_V}.

Parameter _Ord_eq : Ord -> Ord -> Prop.

Parameter _Ord_lt : Ord -> Ord -> Prop.

Parameter _Ord_le : Ord -> Ord -> Prop.

Parameter _zer : Ord.

Parameter _suc : Ord -> Ord.

Parameter _sup : forall A : Type@{Set_u}, (A -> Ord) -> Ord.

Parameter _transfinite_rec : forall D : Type@{Set_V}, (D -> D) -> (forall A : Type@{Set_u}, (A -> D) -> D) -> Ord -> D.

Parameter _Ord_add : Ord -> Ord -> Ord.

Parameter _Ord_mul : Ord -> Ord -> Ord.

Parameter Card : Type@{Set_V}.

Parameter _Card_eq : Card -> Card -> Prop.

Parameter _Card_lt : Card -> Card -> Prop.

Parameter _Card_le : Card -> Card -> Prop.

Parameter _card : forall A : Type@{Set_u}, isSetoid A -> Card.

Parameter _Card_add : Card -> Card -> Card.

Parameter _Card_mul : Card -> Card -> Card.

Parameter _Card_exp : Card -> Card -> Card.

End SetTheoreticConcepts.

Module TypeTheoreticImplementation <: SetTheoreticConcepts.

Definition V : Type@{Set_V} :=
  @Tree.

Definition _eq : V -> V -> Prop :=
  @eqTree.

Definition _in : V -> V -> Prop :=
  @member.

Definition _subseteq : V -> V -> Prop :=
  @isSubsetOf.

Definition _comprehension : (V -> Prop) -> V -> V :=
  @filter.

Definition _emptyset : V :=
  @empty.

Definition _powerset : V -> V :=
  @power.

Definition _unordered_pair : V -> V -> V :=
  @upair.

Definition _unions : V -> V :=
  @unions.

Module Ord.

Definition t : Type@{Set_V} :=
  @Tree.

Section TRANSFINITE.

Context {D : Type@{Set_V}}.

Section FIRST.

Context (suc : D -> D) (bigjoin : forall A : Type@{Set_u}, (A -> D) -> D).

Fixpoint transfinite_rec (t : Ord.t) {struct t} : D :=
  match t with
  | mkNode cs ts => bigjoin cs (fun c : cs => suc (transfinite_rec (ts c)))
  end.

End FIRST.

Section SECOND.

Context (base : D) (suc : D -> D) (bigjoin : forall A : Type@{Set_u}, (A -> D) -> D).

Definition join (x : D) (y : D) : D :=
  bigjoin bool (fun b => if b then x else y).

Fixpoint rec (t : Ord.t) {struct t} : D :=
  match t with
  | mkNode cs ts => join base (bigjoin cs (fun c : cs => suc (rec (ts c))))
  end.

End SECOND.

End TRANSFINITE.

Definition zer : Ord.t :=
  @empty.

Definition suc : Ord.t -> Ord.t :=
  @succ.

Definition sup : forall A : Type@{Set_u}, (A -> Ord.t) -> Ord.t :=
  @indexed_union.

Definition orec (base : Ord.t) (succ : Ord.t -> Ord.t) : Ord.t -> Ord.t :=
  rec base succ sup.

Definition add (o1 : Ord.t) (o2 : Ord.t) : Ord.t :=
  Ord.orec o1 suc o2.

Definition mul (o1 : Ord.t) (o2 : Ord.t) : Ord.t :=
  Ord.orec zer (fun o => Ord.add o o1) o2.

End Ord.

Definition Ord : Type@{Set_V} :=
  Ord.t.

#[global] Typeclasses Opaque Ord.

Definition _Ord_eq : Ord -> Ord -> Prop :=
  @rEq.

Definition _Ord_lt : Ord -> Ord -> Prop :=
  @rLt.

Definition _Ord_le : Ord -> Ord -> Prop :=
  @rLe.

Definition _zer : Ord :=
  @Ord.zer.

Definition _suc : Ord -> Ord :=
  @Ord.suc.

Definition _sup : forall A : Type@{Set_u}, (A -> Ord) -> Ord :=
  @Ord.sup.

#[global]
Instance Ord_isWellPoset : isWellPoset Ord :=
  { wltProp := rLt
  ; wltProp_Transitive := rLt_StrictOrder.(StrictOrder_Transitive)
  ; wltProp_well_founded := rLt_wf 
  }.

Definition _transfinite_rec : forall D : Type@{Set_V}, (D -> D) -> (forall A : Type@{Set_u}, (A -> D) -> D) -> Ord -> D :=
  @Ord.transfinite_rec.

Definition _Ord_add : Ord -> Ord -> Ord :=
  Ord.add.

Definition _Ord_mul : Ord -> Ord -> Ord :=
  Ord.mul.

Theorem OrdComparability_implies_EM
  (COMPARABILITY : forall alpha : Ord, forall beta : Ord, alpha ≦ᵣ beta \/ beta <ᵣ alpha)
  : forall P : Type, inhabited (P + (P -> Empty_set))%type.
Proof.
  i. pose proof (COMPARABILITY (mkNode P (fun _ => Ord.zer)) (mkNode (P -> Empty_set) (fun _ => Ord.zer))) as [YES | NO].
  - assert (NP : P -> False).
    { intros H. destruct YES. simpl in *. pose proof (H_rLt H) as [[c H_rLe]]; simpl in *. pose proof (c H) as []. }
    econs. right. intros H. pose proof (NP H) as [].
  - destruct NO as [[c H_rLe]]; simpl in *. econs. left. exact c.
Qed.

Corollary OrdTrichotomy_implies_LEM
  (trichotomous : forall alpha : Ord, forall beta : Ord, alpha =ᵣ beta \/ (alpha <ᵣ beta \/ beta <ᵣ alpha))
  : forall P : Prop, P \/ ~ P.
Proof.
  enough (COMPARABILITY : forall alpha : Ord, forall beta : Ord, alpha ≦ᵣ beta \/ beta <ᵣ alpha).
  {  intros P. pose proof (OrdComparability_implies_EM COMPARABILITY P) as [[YES | NO]]; [left | right]; firstorder. }
  intros alpha beta. pose proof (trichotomous alpha beta) as [H_EQ | [H_LT | H_GT]].
  - left. exact (proj1 H_EQ).
  - left. eapply rLt_implies_rLe. exact H_LT.
  - right. exact H_GT.
Qed.

Section HARTOGS.

Definition Hartogs (D : Type@{Set_u}) : Ord :=
  mkNode (B.sig (D -> D -> Prop) (@well_founded D)) (fun RWF => @fromWfSet D RWF.(B.proj1_sig) RWF.(B.proj2_sig)).

End HARTOGS.

Definition toSet (t : Tree) : Type@{Set_u} :=
  projT1 (toWellPoset t).

Definition toSet_wlt (t : Tree) : forall lhs : toSet t, forall rhs : toSet t, Prop :=
  projT2 (toWellPoset t).

#[global] Arguments toSet_wlt t / lhs rhs.

Lemma toSet_wlt_well_founded (t : Tree)
  : well_founded (toSet_wlt t).
Proof.
  eapply toWellPoset_well_founded.
Defined.

Definition rank (t : Tree) : Tree :=
  @fromWfSet (toSet t) (toSet_wlt t) (toSet_wlt_well_founded t).

Section ToOrderType.

Definition ToOrderType : Tree -> Type@{Set_u} :=
  toSet.

Variable alpha : Tree.

#[global]
Instance ToOrderType_isSetoid : isSetoid (ToOrderType alpha) :=
  @Totalify.mkSetoid_from_wellfounded (toSet alpha) (toSet_wlt alpha) (toSet_wlt_well_founded alpha).

#[global]
Instance ToOrderType_isWoset : isWoset (ToOrderType alpha) :=
  @Totalify.mkWoset_from_wellfounded (toSet alpha) (toSet_wlt alpha) (toSet_wlt_well_founded alpha).

End ToOrderType.

#[global] Typeclasses Opaque ToOrderType.

Module Cardinality.

#[projections(primitive)]
Record t : Type@{Set_V} :=
  mk
  { carrier : Type@{Set_u}
  ; carrier_isSetoid : isSetoid carrier
  }.

#[global] Existing Instance carrier_isSetoid.

Variant le (lhs : Cardinality.t) (rhs : Cardinality.t) : Prop :=
  | le_intro (f : forall x : lhs.(carrier), rhs.(carrier))
    (f_cong : eqPropCompatible1 f)
    (f_inj : forall x1, forall x2, f x1 == f x2 -> x1 == x2).

Variant eq (lhs : Cardinality.t) (rhs : Cardinality.t) : Prop :=
  | eq_intro (f : forall x : lhs.(carrier), rhs.(carrier)) (g : forall y : rhs.(carrier), lhs.(carrier))
    (f_cong : eqPropCompatible1 f)
    (g_cong : eqPropCompatible1 g)
    (f_inj : forall x1, forall x2, f x1 == f x2 -> x1 == x2)
    (g_inj : forall y1, forall y2, g y1 == g y2 -> y1 == y2).

Variant lt (lhs : Cardinality.t) (rhs : Cardinality.t) : Prop :=
  | lt_intro
    (LE : Cardinality.le lhs rhs)
    (NE : ~ Cardinality.eq lhs rhs).

Definition add (kappa : Cardinality.t) (lambda : Cardinality.t) : Cardinality.t :=
  mk (kappa.(carrier) + lambda.(carrier))%type sum_isSetoid.

Definition mul (kappa : Cardinality.t) (lambda : Cardinality.t) : Cardinality.t :=
  mk (kappa.(carrier) * lambda.(carrier))%type prod_isSetoid.

Definition exp (kappa : Cardinality.t) (lambda : Cardinality.t) : Cardinality.t :=
  mk { f : kappa.(carrier) -> lambda.(carrier) | eqPropCompatible1 f }%type fun_isSetoid.

#[global]
Instance _Card_eq_Equivalence
  : Equivalence Cardinality.eq.
Proof.
  split.
  - intros kappa. exists id id; firstorder.
  - intros kappa kappa' [f g ? ? ? ?]. exists g f; firstorder.
  - intros kappa kappa' kappa'' [f g ? ? ? ?] [f' g' ? ? ? ?]. exists (compose f' f) (compose g g'); unfold compose; firstorder.
Qed.

#[global] 
Instance t_isSetoid : isSetoid Cardinality.t :=
  { eqProp := Cardinality.eq
  ; eqProp_Equivalence := _Card_eq_Equivalence
  }.

#[global]
Instance _Card_le_PreOrder
  : PreOrder Cardinality.le.
Proof.
  split.
  - intros kappa. exists id; firstorder.
  - intros kappa kappa' kappa'' [f ? ?] [f' ? ?]. exists (compose f' f); firstorder.
Qed.

#[global]
Instance _Card_le_PartialOrder
  : PartialOrder Cardinality.eq Cardinality.le.
Proof.
  intros kappa kappa'; split; cbv.
  - intros [f g ? ? ? ?]; split; [exists f | exists g]; firstorder.
  - intros [[f ? ?] [g ? ?]]; exists f g; firstorder.
Qed.

#[global]
Instance t_isProset : isProset Cardinality.t :=
  { Proset_isSetoid := Cardinality.t_isSetoid
  ; leProp := Cardinality.le
  ; leProp_PreOrder := _Card_le_PreOrder
  ; leProp_PartialOrder := _Card_le_PartialOrder
  }.

#[global]
Instance _Card_lt_StrictOrder
  : StrictOrder Cardinality.lt.
Proof.
  split.
  - intros kappa [[f ? ?] H_not]. contradiction H_not; eapply _Card_eq_Equivalence.(Equivalence_Reflexive).
  - intros kappa kappa' kappa'' [[f ? ?] H_not] [[g ? ?] H_not']. split.
    + eapply _Card_le_PreOrder; [exists f | exists g]; firstorder.
    + intros [f' g' ? ?]; contradiction H_not'. exists g (compose f g'); firstorder.
Qed.

#[global]
Instance t_hasStrictOrder : hasStrictOrder Cardinality.t :=
  { lt := Cardinality.lt
  ; lt_StrictOrder := _Card_lt_StrictOrder
  }.

Definition ofType (A : Type@{Set_u}) : Cardinality.t :=
  {|
    Cardinality.carrier := A;
    Cardinality.carrier_isSetoid := @mkSetoid_from_eq A
  |}.

End Cardinality.

Definition Card : Type@{Set_V} :=
  Cardinality.t.

#[global] Typeclasses Opaque Card.

Definition _Card_eq : Card -> Card -> Prop :=
  @eqProp Cardinality.t Cardinality.t_isSetoid.

Definition _Card_lt : Card -> Card -> Prop :=
  @lt Cardinality.t Cardinality.t_hasStrictOrder.

Definition _Card_le : Card -> Card -> Prop :=
  @leProp Cardinality.t Cardinality.t_isProset.

Definition _card : forall A : Type@{Set_u}, isSetoid A -> Card :=
  Cardinality.mk.

Definition _Card_add : Card -> Card -> Card :=
  Cardinality.add.

Definition _Card_mul : Card -> Card -> Card :=
  Cardinality.mul.

Definition _Card_exp : Card -> Card -> Card :=
  Cardinality.exp.

End TypeTheoreticImplementation.
