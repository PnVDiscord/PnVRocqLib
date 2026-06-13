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

Parameter _Ord_exp : Ord -> Ord -> Ord.

Parameter Card : Type@{Set_V}.

Parameter _card : V -> Card.

Parameter _Card_eq : Card -> Card -> Prop.

Parameter _Card_lt : Card -> Card -> Prop.

Parameter _Card_le : Card -> Card -> Prop.

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

Definition add (alpha : Ord.t) (beta : Ord.t) : Ord.t :=
  Ord.orec alpha suc beta.

Definition mul (alpha : Ord.t) (beta : Ord.t) : Ord.t :=
  Ord.orec zer (fun beta1 => Ord.add beta1 alpha) beta.

Definition one : Ord.t :=
  Ord.suc Ord.zer.

Definition exp (alpha : Ord.t) (beta : Ord.t) : Ord.t :=
  Ord.orec one (fun beta1 : Ord.t => Ord.mul beta1 alpha) beta.

End Ord.

Definition Ord : Type@{Set_V} :=
  Ord.t.

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

Definition _Ord_exp : Ord -> Ord -> Ord :=
  Ord.exp.

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
  { intros P. pose proof (OrdComparability_implies_EM COMPARABILITY P) as [[YES | NO]]; [left | right]; firstorder. }
  intros alpha beta. pose proof (trichotomous alpha beta) as [H_EQ | [H_LT | H_GT]].
  - left. exact (proj1 H_EQ).
  - left. eapply rLt_implies_rLe. exact H_LT.
  - right. exact H_GT.
Qed.

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

Section toSet.

Variable alpha : Tree.

#[local]
Instance toSet_isSetoid : isSetoid (toSet alpha) :=
  @Totalify.mkSetoid_from_wellfounded (toSet alpha) (toSet_wlt alpha) (toSet_wlt_well_founded alpha).

#[local]
Instance toSet_isWoset : isWoset (toSet alpha) :=
  @Totalify.mkWoset_from_wellfounded (toSet alpha) (toSet_wlt alpha) (toSet_wlt_well_founded alpha).

End toSet.

#[global] Typeclasses Opaque toSet.

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
    Cardinality.carrier_isSetoid := @mkSetoid_from_eq A;
  |}.

Definition toTree (kappa : Cardinality.t) : Tree :=
  let C : Tree := @mkNode (B.sig (kappa.(Cardinality.carrier) -> kappa.(Cardinality.carrier) -> Prop) (fun R => well_founded R /\ (forall x, forall x', x == x' \/ R x x' \/ R x' x) /\ Transitive R /\ eqPropCompatible2 R)) (fun R_wf => fromWfSet R_wf.(B.proj1_sig) (proj1 R_wf.(B.proj2_sig))) in
  let P (t : Tree) : Prop := forall WOSET : @isWoset kappa.(Cardinality.carrier) kappa.(Cardinality.carrier_isSetoid), t ≦ᵣ @fromWfSet kappa.(Cardinality.carrier) wltProp wltProp_well_founded in
  unions (filter P C).

End Cardinality.

Definition Card : Type@{Set_V} :=
  Cardinality.t.

Definition _card (t : V) : Card :=
  Cardinality.mk (children t) (children_isSetoid t).

Notation card := _card.

Definition _Card_eq : Card -> Card -> Prop :=
  @eqProp Cardinality.t Cardinality.t_isSetoid.

Definition _Card_lt : Card -> Card -> Prop :=
  @lt Cardinality.t Cardinality.t_hasStrictOrder.

Definition _Card_le : Card -> Card -> Prop :=
  @leProp Cardinality.t Cardinality.t_isProset.

Definition _Card_add : Card -> Card -> Card :=
  Cardinality.add.

Definition _Card_mul : Card -> Card -> Card :=
  Cardinality.mul.

Definition _Card_exp : Card -> Card -> Card :=
  Cardinality.exp.

Definition hartogs (D : Type@{Set_u}) : Tree :=
  mkNode (B.sig (D -> D -> Prop) (@well_founded D)) (fun RWF => @fromWfSet D RWF.(B.proj1_sig) RWF.(B.proj2_sig)).

End TypeTheoreticImplementation.

Section ORDINAL_ARITHMETIC.

Import TypeTheoreticImplementation.

#[local] Typeclasses Opaque Ord.t.

Let Ord_isSetoid : isSetoid Ord.t :=
  rEq_asSetoid.

#[local] Existing Instance Ord_isSetoid.

#[local]
Instance Ord_isProset : isProset Ord.t :=
  { Proset_isSetoid := Ord_isSetoid
  ; leProp := rLe
  ; leProp_PreOrder := rLe_PreOrder
  ; leProp_PartialOrder := rLe_PartialOrder
  }.

Definition Ord_one : Ord.t :=
  Ord.one.

Definition Ord_join (alpha : Ord.t) (beta : Ord.t) : Ord.t :=
  Ord.sup bool (fun b : bool => if b then alpha else beta).

Definition Ord_exp (alpha : Ord.t) (beta : Ord.t) : Ord.t :=
  Ord.exp alpha beta.

Lemma Ord_zer_rLe (alpha : Ord.t)
  : Ord.zer ≦ᵣ alpha.
Proof.
  unfold Ord.zer. econs. intros c. destruct c.
Qed.

Lemma Ord_sup_rLe_intro (I : Type@{Set_u}) (alphas : I -> Ord.t) (beta : Ord.t)
  (LE : forall i : I, alphas i ≦ᵣ beta)
  : Ord.sup I alphas ≦ᵣ beta.
Proof.
  unfold Ord.sup. rewrite indexed_union_rLe_iff. exact LE.
Qed.

Lemma Ord_rLe_sup_intro (I : Type@{Set_u}) (alphas : I -> Ord.t) (i : I)
  : alphas i ≦ᵣ Ord.sup I alphas.
Proof.
  unfold Ord.sup. eapply rLe_indexed_union_intro. exists i. reflexivity.
Qed.

Lemma Ord_sup_empty_rLe (alphas : Empty_set -> Ord.t) (alpha : Ord.t)
  : Ord.sup Empty_set alphas ≦ᵣ alpha.
Proof.
  eapply Ord_sup_rLe_intro. intros [].
Qed.

Lemma Ord_sup_empty_rEq (alphas : Empty_set -> Ord.t)
  : Ord.sup Empty_set alphas =ᵣ Ord.zer.
Proof.
  rewrite rEq_iff. split.
  - eapply Ord_sup_empty_rLe.
  - eapply Ord_zer_rLe.
Qed.

Lemma Ord_suc_rLe (alpha : Ord.t) (beta : Ord.t)
  (LE : alpha ≦ᵣ beta)
  : Ord.suc alpha ≦ᵣ Ord.suc beta.
Proof.
  unfold Ord.suc. rewrite succ_rLe_iff. rewrite rLt_succ_iff. exact LE.
Qed.

Lemma Ord_rLe_suc (alpha : Ord.t)
  : alpha ≦ᵣ Ord.suc alpha.
Proof.
  unfold Ord.suc. eapply rLt_implies_rLe. eapply rLt_succ_intro.
Qed.

Lemma Ord_suc_rEq (alpha : Ord.t) (beta : Ord.t)
  (EQ : alpha =ᵣ beta)
  : Ord.suc alpha =ᵣ Ord.suc beta.
Proof.
  rewrite rEq_iff in *. destruct EQ as [LE GE]. split; now eapply Ord_suc_rLe.
Qed.

Lemma Ord_join_l (alpha : Ord.t) (beta : Ord.t)
  : alpha ≦ᵣ Ord_join alpha beta.
Proof.
  unfold Ord_join. change ((fun b : bool => if b then alpha else beta) true ≦ᵣ Ord.sup bool (fun b : bool => if b then alpha else beta)). eapply Ord_rLe_sup_intro.
Qed.

Lemma Ord_join_r (alpha : Ord.t) (beta : Ord.t)
  : beta ≦ᵣ Ord_join alpha beta.
Proof.
  unfold Ord_join. change ((fun b : bool => if b then alpha else beta) false ≦ᵣ Ord.sup bool (fun b : bool => if b then alpha else beta)). eapply Ord_rLe_sup_intro.
Qed.

Lemma Ord_join_spec (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LE_alpha : alpha ≦ᵣ alpha1)
  (LE_beta : beta ≦ᵣ alpha1)
  : Ord_join alpha beta ≦ᵣ alpha1.
Proof.
  unfold Ord_join. eapply Ord_sup_rLe_intro. intros [ | ]; assumption.
Qed.

Lemma Ord_join_max_l (alpha : Ord.t) (beta : Ord.t)
  (LE : beta ≦ᵣ alpha)
  : Ord_join alpha beta =ᵣ alpha.
Proof.
  rewrite rEq_iff. split.
  - eapply Ord_join_spec; [reflexivity | exact LE].
  - eapply Ord_join_l.
Qed.

Lemma Ord_join_max_r (alpha : Ord.t) (beta : Ord.t)
  (LE : alpha ≦ᵣ beta)
  : Ord_join alpha beta =ᵣ beta.
Proof.
  rewrite rEq_iff. split.
  - eapply Ord_join_spec; [exact LE | reflexivity].
  - eapply Ord_join_r.
Qed.

Lemma Ord_join_comm (alpha : Ord.t) (beta : Ord.t)
  : Ord_join alpha beta =ᵣ Ord_join beta alpha.
Proof.
  rewrite rEq_iff. split; eapply Ord_join_spec; [eapply Ord_join_r | eapply Ord_join_l | eapply Ord_join_r | eapply Ord_join_l].
Qed.

Lemma Ord_join_assoc (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  : Ord_join alpha (Ord_join beta alpha1) =ᵣ Ord_join (Ord_join alpha beta) alpha1.
Proof.
  rewrite rEq_iff. split.
  - eapply Ord_join_spec.
    + transitivity (Ord_join alpha beta); [eapply Ord_join_l | eapply Ord_join_l].
    + eapply Ord_join_spec.
      * transitivity (Ord_join alpha beta); [eapply Ord_join_r | eapply Ord_join_l].
      * eapply Ord_join_r.
  - eapply Ord_join_spec.
    + eapply Ord_join_spec.
      * eapply Ord_join_l.
      * transitivity (Ord_join beta alpha1); [eapply Ord_join_l | eapply Ord_join_r].
    + transitivity (Ord_join beta alpha1); [eapply Ord_join_r | eapply Ord_join_r].
Qed.

Lemma Ord_join_absorb_l (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LE : beta ≦ᵣ alpha)
  : Ord_join alpha (Ord_join beta alpha1) =ᵣ Ord_join alpha alpha1.
Proof.
  rewrite rEq_iff. split.
  - eapply Ord_join_spec.
    + eapply Ord_join_l.
    + eapply Ord_join_spec.
      * transitivity alpha; [exact LE | eapply Ord_join_l].
      * eapply Ord_join_r.
  - eapply Ord_join_spec.
    + eapply Ord_join_l.
    + transitivity (Ord_join beta alpha1); [eapply Ord_join_r | eapply Ord_join_r].
Qed.

Lemma Ord_join_rEq_l (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (EQ : alpha =ᵣ beta)
  : Ord_join alpha alpha1 =ᵣ Ord_join beta alpha1.
Proof.
  rewrite rEq_iff in *. destruct EQ as [LE GE]. split; eapply Ord_join_spec.
  - transitivity beta; [exact LE | eapply Ord_join_l].
  - eapply Ord_join_r.
  - transitivity alpha; [exact GE | eapply Ord_join_l].
  - eapply Ord_join_r.
Qed.

Lemma Ord_join_rEq_r (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (EQ : beta =ᵣ alpha1)
  : Ord_join alpha beta =ᵣ Ord_join alpha alpha1.
Proof.
  rewrite rEq_iff in *. destruct EQ as [LE GE]. split; eapply Ord_join_spec.
  - eapply Ord_join_l.
  - transitivity alpha1; [exact LE | eapply Ord_join_r].
  - eapply Ord_join_l.
  - transitivity beta; [exact GE | eapply Ord_join_r].
Qed.

Lemma Ord_join_isOrdinal (alpha : Ord.t) (beta : Ord.t)
  (ALPHA : isOrdinal alpha)
  (BETA : isOrdinal beta)
  : isOrdinal (Ord_join alpha beta).
Proof.
  unfold Ord_join. eapply sup_isOrdinal. intros [ | ]; assumption.
Qed.

Lemma Ord_sup_rLe (I : Type@{Set_u}) (alphas : I -> Ord.t) (betas : I -> Ord.t)
  (LE : forall i : I, alphas i ≦ᵣ betas i)
  : Ord.sup I alphas ≦ᵣ Ord.sup I betas.
Proof.
  eapply Ord_sup_rLe_intro. intros i. transitivity (betas i).
  - eapply LE.
  - eapply Ord_rLe_sup_intro.
Qed.

Lemma Ord_sup_rEq (I : Type@{Set_u}) (alphas : I -> Ord.t) (betas : I -> Ord.t)
  (EQ : forall i : I, alphas i =ᵣ betas i)
  : Ord.sup I alphas =ᵣ Ord.sup I betas.
Proof.
  rewrite rEq_iff. split; eapply Ord_sup_rLe; intros i; pose proof (EQ i) as [LE GE]; assumption.
Qed.

Lemma Ord_mkNode_suc_sup_rEq (cs : Type@{Set_u}) (ts : cs -> Ord.t)
  : mkNode cs ts =ᵣ Ord.sup cs (fun c : cs => Ord.suc (ts c)).
Proof.
  rewrite mkNode_rEq. intros u. split.
  - intros LE c. unfold Ord.sup in LE. pose proof (proj1 (indexed_union_rLe_iff cs (fun c : cs => Ord.suc (ts c)) u) LE c) as H. unfold Ord.suc in H. rewrite succ_rLe_iff in H. exact H.
  - intros LT. eapply Ord_sup_rLe_intro. intros c. unfold Ord.suc. rewrite succ_rLe_iff. exact (LT c).
Qed.

Lemma Ord_orec_unfold (base : Ord.t) (next : Ord.t -> Ord.t) (cs : Type@{Set_u}) (ts : cs -> Ord.t)
  : Ord.orec base next (mkNode cs ts) = Ord_join base (Ord.sup cs (fun c : cs => next (Ord.orec base next (ts c)))).
Proof.
  reflexivity.
Qed.

Lemma Ord_orec_all (base : Ord.t) (next : Ord.t -> Ord.t)
  (NEXT_LE : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (NEXT_MON : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  : (forall beta : Ord.t, base ≦ᵣ Ord.orec base next beta) /\ (forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> Ord.orec base next alpha ≦ᵣ Ord.orec base next beta) /\ (forall alpha : Ord.t, forall beta : Ord.t, alpha <ᵣ beta -> next (Ord.orec base next alpha) ≦ᵣ Ord.orec base next beta).
Proof.
  enough (REC : forall beta : Ord.t, base ≦ᵣ Ord.orec base next beta /\ (forall alpha : Ord.t, alpha ≦ᵣ beta -> Ord.orec base next alpha ≦ᵣ Ord.orec base next beta) /\ (forall alpha : Ord.t, alpha <ᵣ beta -> next (Ord.orec base next alpha) ≦ᵣ Ord.orec base next beta)).
  { splits.
    - intros beta. exact (proj1 (REC beta)).
    - intros alpha beta LE. exact (proj1 (proj2 (REC beta)) alpha LE).
    - intros alpha beta LT. exact (proj2 (proj2 (REC beta)) alpha LT).
  }
  intros beta. induction (rLt_wf beta) as [beta _ IH]. destruct beta as [cs ts]. rewrite Ord_orec_unfold.
  assert (BASE : base ≦ᵣ Ord_join base (Ord.sup cs (fun c : cs => next (Ord.orec base next (ts c))))).
  { eapply Ord_join_l. }
  assert (NEXT : forall alpha : Ord.t, alpha <ᵣ mkNode cs ts -> next (Ord.orec base next alpha) ≦ᵣ Ord_join base (Ord.sup cs (fun c : cs => next (Ord.orec base next (ts c))))).
  { intros alpha LT. destruct LT as [[c LE]]. transitivity (next (Ord.orec base next (ts c))).
    - eapply NEXT_MON. exact (proj1 (proj2 (IH (ts c) (member_implies_rLt (ts c) (mkNode cs ts) (member_intro cs ts c)))) alpha LE).
    - transitivity (Ord.sup cs (fun c0 : cs => next (Ord.orec base next (ts c0)))).
      + change ((fun c0 : cs => next (Ord.orec base next (ts c0))) c ≦ᵣ Ord.sup cs (fun c0 : cs => next (Ord.orec base next (ts c0)))). eapply Ord_rLe_sup_intro.
      + eapply Ord_join_r.
  }
  assert (MON : forall alpha : Ord.t, alpha ≦ᵣ mkNode cs ts -> Ord.orec base next alpha ≦ᵣ Ord_join base (Ord.sup cs (fun c : cs => next (Ord.orec base next (ts c))))).
  { intros [cs_alpha ts_alpha] LE. rewrite Ord_orec_unfold. eapply Ord_join_spec.
    - exact BASE.
    - eapply Ord_sup_rLe_intro. intros c. eapply NEXT. eapply rLt_rLe_rLt with (y := mkNode cs_alpha ts_alpha).
      + eapply member_implies_rLt. eapply member_intro.
      + exact LE.
  }
  splits; [exact BASE | exact MON | exact NEXT].
Qed.

Lemma Ord_orec_le_base (base : Ord.t) (next : Ord.t -> Ord.t)
  (NEXT_LE : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (NEXT_MON : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  (beta : Ord.t)
  : base ≦ᵣ Ord.orec base next beta.
Proof.
  pose proof (Ord_orec_all base next NEXT_LE NEXT_MON) as (BASE & _ & _). eapply BASE.
Qed.

Lemma Ord_orec_base_rLe (base : Ord.t) (next : Ord.t -> Ord.t) (beta : Ord.t)
  : base ≦ᵣ Ord.orec base next beta.
Proof.
  induction beta as [cs ts IH]. rewrite Ord_orec_unfold. eapply Ord_join_l.
Qed.

Lemma Ord_orec_rLe (base : Ord.t) (next : Ord.t -> Ord.t) (alpha : Ord.t) (beta : Ord.t)
  (NEXT_LE : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (NEXT_MON : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  (LE : alpha ≦ᵣ beta)
  : Ord.orec base next alpha ≦ᵣ Ord.orec base next beta.
Proof.
  pose proof (Ord_orec_all base next NEXT_LE NEXT_MON) as (_ & MON & _). eapply MON. exact LE.
Qed.

Lemma Ord_orec_rEq_r (base : Ord.t) (next : Ord.t -> Ord.t) (alpha : Ord.t) (beta : Ord.t)
  (NEXT_LE : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (NEXT_MON : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  (EQ : alpha =ᵣ beta)
  : Ord.orec base next alpha =ᵣ Ord.orec base next beta.
Proof.
  rewrite rEq_iff in *. destruct EQ as [LE GE]. split; now eapply Ord_orec_rLe.
Qed.

Lemma Ord_orec_next_rLe (base : Ord.t) (next : Ord.t -> Ord.t) (alpha : Ord.t) (beta : Ord.t)
  (NEXT_LE : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (NEXT_MON : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  (LT : alpha <ᵣ beta)
  : next (Ord.orec base next alpha) ≦ᵣ Ord.orec base next beta.
Proof.
  pose proof (Ord_orec_all base next NEXT_LE NEXT_MON) as (_ & _ & NEXT). eapply NEXT. exact LT.
Qed.

Lemma Ord_orec_zer (base : Ord.t) (next : Ord.t -> Ord.t)
  : Ord.orec base next Ord.zer =ᵣ base.
Proof.
  unfold Ord.zer, empty. rewrite Ord_orec_unfold. eapply Ord_join_max_l. eapply Ord_sup_empty_rLe.
Qed.

Lemma Ord_orec_suc (base : Ord.t) (next : Ord.t -> Ord.t)
  (NEXT_LE : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (NEXT_MON : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  : forall alpha, Ord.orec base next (Ord.suc alpha) =ᵣ next (Ord.orec base next alpha).
Proof.
  i. rewrite rEq_iff. split.
  - remember (Ord.suc alpha) as suc_alpha eqn:EQ. destruct suc_alpha as [cs ts]. rewrite Ord_orec_unfold. eapply Ord_join_spec.
    + transitivity (Ord.orec base next alpha).
      * eapply Ord_orec_le_base; eauto.
      * eapply NEXT_LE.
    + eapply Ord_sup_rLe_intro. intros c. eapply NEXT_MON. eapply Ord_orec_rLe; eauto.
      assert (LT : ts c <ᵣ Ord.suc alpha).
      { rewrite <- EQ. eapply member_implies_rLt. eapply member_intro. }
      unfold Ord.suc in LT. rewrite rLt_succ_iff in LT. exact LT.
  - eapply Ord_orec_next_rLe; eauto. unfold Ord.suc. eapply rLt_succ_intro.
Qed.

Lemma Ord_orec_sup (base : Ord.t) (next : Ord.t -> Ord.t) (I : Type@{Set_u}) (alphas : I -> Ord.t)
  (NEXT_LE : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (NEXT_MON : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  : Ord.orec base next (Ord.sup I alphas) =ᵣ Ord_join base (Ord.sup I (fun i : I => Ord.orec base next (alphas i))).
Proof.
  rewrite rEq_iff. split.
  - change (Ord.orec base next (mkNode { i : I & children (alphas i) } (fun c => childnodes (alphas (projT1 c)) (projT2 c))) ≦ᵣ Ord_join base (Ord.sup I (fun i : I => Ord.orec base next (alphas i)))).
    rewrite Ord_orec_unfold. eapply Ord_join_spec.
    + eapply Ord_join_l.
    + eapply Ord_sup_rLe_intro. intros [i c]. transitivity (Ord.orec base next (alphas i)).
      { eapply Ord_orec_next_rLe; eauto. eapply member_implies_rLt. eapply member_intro. }
      transitivity (Ord.sup I (fun i : I => Ord.orec base next (alphas i))).
      { change ((fun i : I => Ord.orec base next (alphas i)) i ≦ᵣ Ord.sup I (fun i : I => Ord.orec base next (alphas i))). eapply Ord_rLe_sup_intro. }
      { eapply Ord_join_r. }
  - eapply Ord_join_spec.
    + eapply Ord_orec_le_base; eauto.
    + eapply Ord_sup_rLe_intro. intros i. eapply Ord_orec_rLe; eauto. eapply Ord_rLe_sup_intro.
Qed.

Lemma Ord_orec_sup_inhabited (base : Ord.t) (next : Ord.t -> Ord.t) (I : Type@{Set_u}) (alphas : I -> Ord.t)
  (NEXT_LE : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (NEXT_MON : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  (INHABITED : inhabited I)
  : Ord.orec base next (Ord.sup I alphas) =ᵣ Ord.sup I (fun i : I => Ord.orec base next (alphas i)).
Proof.
  etransitivity.
  - eapply Ord_orec_sup; eauto.
  - destruct INHABITED as [i]. eapply Ord_join_max_r. transitivity (Ord.orec base next (alphas i)).
    + eapply Ord_orec_base_rLe.
    + change ((fun i : I => Ord.orec base next (alphas i)) i ≦ᵣ Ord.sup I (fun i : I => Ord.orec base next (alphas i))). eapply Ord_rLe_sup_intro.
Qed.

Lemma Ord_orec_join (base : Ord.t) (next : Ord.t -> Ord.t) (alpha : Ord.t) (beta : Ord.t)
  (NEXT_LE : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (NEXT_MON : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  : Ord.orec base next (Ord_join alpha beta) =ᵣ Ord_join (Ord.orec base next alpha) (Ord.orec base next beta).
Proof.
  unfold Ord_join at 1. etransitivity.
  - eapply Ord_orec_sup_inhabited; eauto. constructor. exact true.
  - unfold Ord_join. eapply Ord_sup_rEq. intros [ | ]; reflexivity.
Qed.

Lemma Ord_orec_isOrdinal (base : Ord.t) (next : Ord.t -> Ord.t)
  (BASE : isOrdinal base)
  (NEXT : forall alpha : Ord.t, isOrdinal alpha -> isOrdinal (next alpha))
  : forall beta, isOrdinal (Ord.orec base next beta).
Proof.
  induction beta as [cs ts IH]. rewrite Ord_orec_unfold. eapply Ord_join_isOrdinal.
  - exact BASE.
  - eapply sup_isOrdinal. intros c. eapply NEXT. eapply IH.
Qed.

Lemma Ord_one_isOrdinal
  : isOrdinal Ord_one.
Proof.
  unfold Ord_one. eapply suc_isOrdinal. eapply zer_isOrdinal.
Qed.

Lemma Ord_add_base_l (alpha : Ord.t) (beta : Ord.t)
  : alpha ≦ᵣ Ord.add alpha beta.
Proof.
  unfold Ord.add. eapply Ord_orec_le_base.
  - eapply Ord_rLe_suc.
  - intros alpha1 beta1 LE. eapply Ord_suc_rLe. exact LE.
Qed.

Lemma Ord_add_base_r (alpha : Ord.t) (beta : Ord.t)
  : beta ≦ᵣ Ord.add alpha beta.
Proof.
  revert alpha. induction (rLt_wf beta) as [beta _ IH]. intros alpha. destruct beta as [cs ts]. eapply rLe_intro_var1.
  intros beta' IN. destruct IN as [c EQ]. eapply rLe_rLt_rLt with (y := ts c).
  - eapply eqTree_rLe_rLe; [exact EQ | reflexivity].
  - eapply rLt_rLe_rLt with (y := Ord.suc (Ord.add alpha (ts c))).
    + unfold Ord.suc. rewrite rLt_succ_iff. eapply IH. eapply member_implies_rLt. eapply member_intro.
    + unfold Ord.add. rewrite Ord_orec_unfold. transitivity (Ord.sup cs (fun c0 : cs => Ord.suc (Ord.orec alpha Ord.suc (ts c0)))).
      * change ((fun c0 : cs => Ord.suc (Ord.orec alpha Ord.suc (ts c0))) c ≦ᵣ Ord.sup cs (fun c0 : cs => Ord.suc (Ord.orec alpha Ord.suc (ts c0)))). eapply Ord_rLe_sup_intro.
      * eapply Ord_join_r.
Qed.

Lemma Ord_add_zer_r (alpha : Ord.t)
  : Ord.add alpha Ord.zer =ᵣ alpha.
Proof.
  unfold Ord.add. eapply Ord_orec_zer.
Qed.

Lemma Ord_add_suc (alpha : Ord.t) (beta : Ord.t)
  : Ord.add alpha (Ord.suc beta) =ᵣ Ord.suc (Ord.add alpha beta).
Proof.
  unfold Ord.add. eapply Ord_orec_suc.
  - eapply Ord_rLe_suc.
  - intros alpha1 beta1 LE. eapply Ord_suc_rLe. exact LE.
Qed.

Lemma Ord_add_one_r (alpha : Ord.t)
  : Ord.add alpha Ord_one =ᵣ Ord.suc alpha.
Proof.
  unfold Ord_one. etransitivity.
  - eapply Ord_add_suc.
  - eapply Ord_suc_rEq. eapply Ord_add_zer_r.
Qed.

Lemma Ord_add_mkNode (alpha : Ord.t) (cs : Type@{Set_u}) (ts : cs -> Ord.t)
  : Ord.add alpha (mkNode cs ts) =ᵣ Ord_join alpha (Ord.sup cs (fun c : cs => Ord.suc (Ord.add alpha (ts c)))).
Proof.
  unfold Ord.add. rewrite Ord_orec_unfold. reflexivity.
Qed.

Lemma Ord_add_rLe_r (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LE : beta ≦ᵣ alpha1)
  : Ord.add alpha beta ≦ᵣ Ord.add alpha alpha1.
Proof.
  unfold Ord.add. eapply Ord_orec_rLe; eauto.
  - eapply Ord_rLe_suc.
  - intros beta1 beta2 LE'. eapply Ord_suc_rLe. exact LE'.
Qed.

Lemma Ord_add_rEq_r (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (EQ : beta =ᵣ alpha1)
  : Ord.add alpha beta =ᵣ Ord.add alpha alpha1.
Proof.
  rewrite rEq_iff in *. destruct EQ as [LE GE]. split; now eapply Ord_add_rLe_r.
Qed.

Lemma Ord_add_sup (alpha : Ord.t) (I : Type@{Set_u}) (betas : I -> Ord.t)
  : Ord.add alpha (Ord.sup I betas) =ᵣ Ord_join alpha (Ord.sup I (fun i : I => Ord.add alpha (betas i))).
Proof.
  unfold Ord.add. eapply Ord_orec_sup.
  - eapply Ord_rLe_suc.
  - intros beta alpha1 LE. eapply Ord_suc_rLe. exact LE.
Qed.

Lemma Ord_add_sup_inhabited (alpha : Ord.t) (I : Type@{Set_u}) (betas : I -> Ord.t)
  (INHABITED : inhabited I)
  : Ord.add alpha (Ord.sup I betas) =ᵣ Ord.sup I (fun i : I => Ord.add alpha (betas i)).
Proof.
  etransitivity.
  - eapply Ord_add_sup.
  - destruct INHABITED as [i]. eapply Ord_join_max_r. transitivity (Ord.add alpha (betas i)).
    + eapply Ord_add_base_l.
    + change ((fun i : I => Ord.add alpha (betas i)) i ≦ᵣ Ord.sup I (fun i : I => Ord.add alpha (betas i))). eapply Ord_rLe_sup_intro.
Qed.

Lemma Ord_add_join (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  : Ord.add alpha (Ord_join beta alpha1) =ᵣ Ord_join (Ord.add alpha beta) (Ord.add alpha alpha1).
Proof.
  unfold Ord_join at 1. etransitivity.
  - eapply Ord_add_sup_inhabited. constructor. exact true.
  - unfold Ord_join. eapply Ord_sup_rEq. intros [ | ]; reflexivity.
Qed.

Lemma Ord_add_rLe_l (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LE : alpha ≦ᵣ beta)
  : Ord.add alpha alpha1 ≦ᵣ Ord.add beta alpha1.
Proof.
  revert alpha beta LE. induction (rLt_wf alpha1) as [alpha1 _ IH]. intros alpha beta LE. destruct alpha1 as [cs ts].
  unfold Ord.add. rewrite 2 Ord_orec_unfold. eapply Ord_join_spec.
  - transitivity beta.
    + exact LE.
    + eapply Ord_join_l.
  - eapply Ord_sup_rLe_intro. intros c. transitivity (Ord.suc (Ord.orec beta Ord.suc (ts c))).
    + eapply Ord_suc_rLe. eapply IH.
      * eapply member_implies_rLt. eapply member_intro.
      * exact LE.
    + transitivity (Ord.sup cs (fun c : cs => Ord.suc (Ord.orec beta Ord.suc (ts c)))).
      * change ((fun c : cs => Ord.suc (Ord.orec beta Ord.suc (ts c))) c ≦ᵣ Ord.sup cs (fun c0 : cs => Ord.suc (Ord.orec beta Ord.suc (ts c0)))). eapply Ord_rLe_sup_intro.
      * eapply Ord_join_r.
Qed.

Lemma Ord_add_rEq_l (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (EQ : alpha =ᵣ beta)
  : Ord.add alpha alpha1 =ᵣ Ord.add beta alpha1.
Proof.
  rewrite rEq_iff in *. destruct EQ as [LE GE]. split; now eapply Ord_add_rLe_l.
Qed.

#[local]
Instance Ord_add_isMonotonic2
  : isMonotonic2 Ord.add.
Proof.
  intros alpha beta alpha1 beta1 LE_alpha LE_gamma. transitivity (Ord.add beta alpha1).
  - eapply Ord_add_rLe_l. exact LE_alpha.
  - eapply Ord_add_rLe_r. exact LE_gamma.
Qed.

Theorem Ord_add_isOrdinal (alpha : Ord.t) (beta : Ord.t)
  (ORDINAL : isOrdinal alpha)
  : isOrdinal (Ord.add alpha beta).
Proof.
  unfold Ord.add. eapply Ord_orec_isOrdinal.
  - exact ORDINAL.
  - intros alpha1 ORDINAL'. eapply suc_isOrdinal. exact ORDINAL'.
Qed.

Lemma Ord_add_rLt_r (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LT : beta <ᵣ alpha1)
  : Ord.add alpha beta <ᵣ Ord.add alpha alpha1.
Proof.
  eapply rLt_rLe_rLt with (y := Ord.add alpha (Ord.suc beta)).
  - eapply rLt_rLe_rLt with (y := Ord.suc (Ord.add alpha beta)).
    + eapply rLt_succ_intro.
    + exact (proj2 (proj1 (rEq_iff _ _) (Ord_add_suc alpha beta))).
  - eapply Ord_add_rLe_r. unfold Ord.suc. eapply succ_rLe_intro. exact LT.
Qed.

Lemma Ord_add_rLt_larger (alpha : Ord.t) (beta : Ord.t)
  (POS : Ord.zer <ᵣ beta)
  : alpha <ᵣ Ord.add alpha beta.
Proof.
  eapply rLt_rLe_rLt with (y := Ord.add alpha Ord_one).
  - eapply rLt_rLe_rLt with (y := Ord.suc alpha).
    + eapply rLt_succ_intro.
    + exact (proj2 (proj1 (rEq_iff _ _) (Ord_add_one_r alpha))).
  - eapply Ord_add_rLe_r. unfold Ord_one, Ord.suc. eapply succ_rLe_intro. exact POS.
Qed.

Lemma Ord_add_zer_l (alpha : Ord.t)
  : Ord.add Ord.zer alpha =ᵣ alpha.
Proof.
  induction alpha as [cs ts IH]. unfold Ord.add. rewrite Ord_orec_unfold.
  etransitivity.
  { eapply Ord_join_max_r. eapply Ord_zer_rLe. }
  etransitivity.
  - eapply Ord_sup_rEq. intros c. eapply Ord_suc_rEq. exact (IH c).
  - symmetry. eapply Ord_mkNode_suc_sup_rEq.
Qed.

Lemma Ord_add_assoc (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  : Ord.add (Ord.add alpha beta) alpha1 =ᵣ Ord.add alpha (Ord.add beta alpha1).
Proof.
  revert alpha beta. induction (rLt_wf alpha1) as [alpha1 _ IH]. intros alpha beta. destruct alpha1 as [cs ts].
  etransitivity.
  { eapply Ord_add_mkNode. }
  symmetry. etransitivity.
  { eapply Ord_add_rEq_r. eapply Ord_add_mkNode. }
  etransitivity.
  { eapply Ord_add_join. }
  etransitivity.
  { eapply Ord_join_rEq_r. eapply Ord_add_sup. }
  etransitivity.
  { eapply Ord_join_assoc. }
  etransitivity.
  - eapply Ord_join_rEq_l. eapply Ord_join_max_l. eapply Ord_add_base_l.
  - eapply Ord_join_rEq_r. eapply Ord_sup_rEq. intros c. etransitivity.
    + eapply Ord_add_suc.
    + eapply Ord_suc_rEq. symmetry. eapply IH. eapply member_implies_rLt. eapply member_intro.
Qed.

Lemma Ord_orec_add (base : Ord.t) (next : Ord.t -> Ord.t) (alpha : Ord.t) (beta : Ord.t)
  (NEXT_LE : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (NEXT_MON : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  : Ord.orec base next (Ord.add alpha beta) =ᵣ Ord.orec (Ord.orec base next alpha) next beta.
Proof.
  revert alpha. induction (rLt_wf beta) as [beta _ IH]. intros alpha. destruct beta as [cs ts].
  etransitivity.
  { eapply Ord_orec_rEq_r; eauto. eapply Ord_add_mkNode. }
  etransitivity.
  { eapply Ord_orec_join; eauto. }
  etransitivity.
  { eapply Ord_join_rEq_r. eapply Ord_orec_sup; eauto. }
  etransitivity.
  { eapply Ord_join_absorb_l. eapply Ord_orec_base_rLe. }
  etransitivity.
  eapply Ord_join_rEq_r. eapply Ord_sup_rEq. intros c. etransitivity.
  - eapply Ord_orec_suc; eauto.
  - pose proof (proj1 (rEq_iff _ _) (IH (ts c) (member_implies_rLt (ts c) (mkNode cs ts) (member_intro cs ts c)) alpha)) as [LE GE].
    rewrite rEq_iff. split.
    + eapply NEXT_MON. exact LE.
    + eapply NEXT_MON. exact GE.
  - rewrite Ord_orec_unfold. reflexivity.
Qed.

Lemma Ord_mul_zer_r (alpha : Ord.t)
  : Ord.mul alpha Ord.zer =ᵣ Ord.zer.
Proof.
  unfold Ord.mul. eapply Ord_orec_zer.
Qed.

Lemma Ord_mul_suc (alpha : Ord.t) (beta : Ord.t)
  : Ord.mul alpha (Ord.suc beta) =ᵣ Ord.add (Ord.mul alpha beta) alpha.
Proof.
  unfold Ord.mul. eapply Ord_orec_suc.
  - intros alpha1. eapply Ord_add_base_l.
  - intros alpha1 beta1 LE. eapply Ord_add_rLe_l. exact LE.
Qed.

Lemma Ord_mul_rLe_r (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LE : beta ≦ᵣ alpha1)
  : Ord.mul alpha beta ≦ᵣ Ord.mul alpha alpha1.
Proof.
  unfold Ord.mul. eapply Ord_orec_rLe; eauto.
  - intros beta1. eapply Ord_add_base_l.
  - intros beta1 beta2 LE'. eapply Ord_add_rLe_l. exact LE'.
Qed.

Lemma Ord_mul_rEq_r (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (EQ : beta =ᵣ alpha1)
  : Ord.mul alpha beta =ᵣ Ord.mul alpha alpha1.
Proof.
  rewrite rEq_iff in *. destruct EQ as [LE GE]. split; now eapply Ord_mul_rLe_r.
Qed.

Lemma Ord_mul_rLe_l (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LE : alpha ≦ᵣ beta)
  : Ord.mul alpha alpha1 ≦ᵣ Ord.mul beta alpha1.
Proof.
  revert alpha beta LE. induction (rLt_wf alpha1) as [alpha1 _ IH]. intros alpha beta LE. destruct alpha1 as [cs ts].
  unfold Ord.mul. rewrite 2 Ord_orec_unfold. eapply Ord_join_spec.
  - eapply Ord_zer_rLe.
  - eapply Ord_sup_rLe_intro. intros c. transitivity (Ord.add (Ord.orec Ord.zer (fun beta1 : Ord.t => Ord.add beta1 beta) (ts c)) alpha).
    + eapply Ord_add_rLe_l. eapply IH.
      * eapply member_implies_rLt. eapply member_intro.
      * exact LE.
    + transitivity (Ord.add (Ord.orec Ord.zer (fun beta1 : Ord.t => Ord.add beta1 beta) (ts c)) beta).
      * eapply Ord_add_rLe_r. exact LE.
      * transitivity (Ord.sup cs (fun c : cs => Ord.add (Ord.orec Ord.zer (fun beta1 : Ord.t => Ord.add beta1 beta) (ts c)) beta)).
        { change ((fun c : cs => Ord.add (Ord.orec Ord.zer (fun beta1 : Ord.t => Ord.add beta1 beta) (ts c)) beta) c ≦ᵣ Ord.sup cs (fun c0 : cs => Ord.add (Ord.orec Ord.zer (fun beta1 : Ord.t => Ord.add beta1 beta) (ts c0)) beta)). eapply Ord_rLe_sup_intro. }
        { eapply Ord_join_r. }
Qed.

Lemma Ord_mul_rEq_l (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (EQ : alpha =ᵣ beta)
  : Ord.mul alpha alpha1 =ᵣ Ord.mul beta alpha1.
Proof.
  rewrite rEq_iff in *. destruct EQ as [LE GE]. split; now eapply Ord_mul_rLe_l.
Qed.

#[local]
Instance Ord_mul_isMonotonic2
  : isMonotonic2 Ord.mul.
Proof.
  intros alpha beta alpha1 beta1 LE_alpha LE_gamma. transitivity (Ord.mul beta alpha1).
  - eapply Ord_mul_rLe_l. exact LE_alpha.
  - eapply Ord_mul_rLe_r. exact LE_gamma.
Qed.

Lemma Ord_mul_sup (alpha : Ord.t) (I : Type@{Set_u}) (betas : I -> Ord.t)
  : Ord.mul alpha (Ord.sup I betas) =ᵣ Ord.sup I (fun i : I => Ord.mul alpha (betas i)).
Proof.
  unfold Ord.mul. etransitivity.
  - eapply Ord_orec_sup.
    + intros beta. eapply Ord_add_base_l.
    + intros beta alpha1 LE. eapply Ord_add_rLe_l. exact LE.
  - eapply Ord_join_max_r. eapply Ord_zer_rLe.
Qed.

Lemma Ord_mul_join (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  : Ord.mul alpha (Ord_join beta alpha1) =ᵣ Ord_join (Ord.mul alpha beta) (Ord.mul alpha alpha1).
Proof.
  unfold Ord_join at 1. etransitivity.
  - eapply Ord_mul_sup.
  - unfold Ord_join. eapply Ord_sup_rEq. intros [ | ]; reflexivity.
Qed.

Lemma Ord_mul_zer_l (alpha : Ord.t)
  : Ord.mul Ord.zer alpha =ᵣ Ord.zer.
Proof.
  induction alpha as [cs ts IH]. unfold Ord.mul. rewrite Ord_orec_unfold. eapply Ord_join_max_l.
  eapply Ord_sup_rLe_intro. intros c. transitivity (Ord.add Ord.zer Ord.zer).
  - exact (proj1 (proj1 (rEq_iff _ _) (Ord_add_rEq_l (Ord.mul Ord.zer (ts c)) Ord.zer Ord.zer (IH c)))).
  - exact (proj1 (proj1 (rEq_iff _ _) (Ord_add_zer_r Ord.zer))).
Qed.

Lemma Ord_mul_one_r (alpha : Ord.t)
  : Ord.mul alpha Ord_one =ᵣ alpha.
Proof.
  unfold Ord_one. etransitivity.
  - eapply Ord_mul_suc.
  - etransitivity.
    + eapply Ord_add_rEq_l. eapply Ord_mul_zer_r.
    + eapply Ord_add_zer_l.
Qed.

Lemma Ord_mul_base_l (alpha : Ord.t) (beta : Ord.t)
  (POS : Ord.zer <ᵣ beta)
  : alpha ≦ᵣ Ord.mul alpha beta.
Proof.
  transitivity (Ord.mul alpha Ord_one).
  - exact (proj2 (proj1 (rEq_iff _ _) (Ord_mul_one_r alpha))).
  - eapply Ord_mul_rLe_r. unfold Ord_one, Ord.suc. eapply succ_rLe_intro. exact POS.
Qed.

Theorem Ord_mul_isOrdinal (alpha : Ord.t) (beta : Ord.t)
  (ORDINAL : isOrdinal alpha)
  : isOrdinal (Ord.mul alpha beta).
Proof.
  unfold Ord.mul. eapply Ord_orec_isOrdinal.
  - eapply zer_isOrdinal.
  - intros alpha1 ORDINAL'. eapply Ord_add_isOrdinal. exact ORDINAL'.
Qed.

Lemma Ord_mul_rLt_r (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (POS : Ord.zer <ᵣ alpha)
  (LT : beta <ᵣ alpha1)
  : Ord.mul alpha beta <ᵣ Ord.mul alpha alpha1.
Proof.
  eapply rLt_rLe_rLt with (y := Ord.mul alpha (Ord.suc beta)).
  - eapply rLt_rLe_rLt with (y := Ord.add (Ord.mul alpha beta) alpha).
    + eapply Ord_add_rLt_larger. exact POS.
    + exact (proj2 (proj1 (rEq_iff _ _) (Ord_mul_suc alpha beta))).
  - eapply Ord_mul_rLe_r. unfold Ord.suc. eapply succ_rLe_intro. exact LT.
Qed.

Lemma Ord_mul_rLt_larger (alpha : Ord.t) (beta : Ord.t)
  (POS : Ord.zer <ᵣ alpha)
  (TWO : Ord_one <ᵣ beta)
  : alpha <ᵣ Ord.mul alpha beta.
Proof.
  eapply rLt_rLe_rLt with (y := Ord.mul alpha (Ord.suc Ord_one)).
  - eapply rLt_rLe_rLt with (y := Ord.add alpha alpha).
    + eapply Ord_add_rLt_larger. exact POS.
    + transitivity (Ord.add (Ord.mul alpha Ord_one) alpha).
      * eapply Ord_add_rLe_l. exact (proj2 (proj1 (rEq_iff _ _) (Ord_mul_one_r alpha))).
      * exact (proj2 (proj1 (rEq_iff _ _) (Ord_mul_suc alpha Ord_one))).
  - eapply Ord_mul_rLe_r. unfold Ord.suc. eapply succ_rLe_intro. exact TWO.
Qed.

Lemma Ord_mul_one_l (alpha : Ord.t)
  : Ord.mul Ord_one alpha =ᵣ alpha.
Proof.
  induction alpha as [cs ts IH]. unfold Ord.mul. rewrite Ord_orec_unfold.
  etransitivity.
  { eapply Ord_join_max_r. eapply Ord_zer_rLe. }
  etransitivity.
  - eapply Ord_sup_rEq. intros c. etransitivity.
    { eapply Ord_add_rEq_l. exact (IH c). }
    unfold Ord_one. etransitivity.
    { eapply Ord_add_suc. }
    { eapply Ord_suc_rEq. eapply Ord_add_zer_r. }
  - symmetry. eapply Ord_mkNode_suc_sup_rEq.
Qed.

Lemma Ord_mul_mkNode (alpha : Ord.t) (cs : Type@{Set_u}) (ts : cs -> Ord.t)
  : Ord.mul alpha (mkNode cs ts) =ᵣ Ord.sup cs (fun c : cs => Ord.add (Ord.mul alpha (ts c)) alpha).
Proof.
  unfold Ord.mul. rewrite Ord_orec_unfold. eapply Ord_join_max_r. eapply Ord_zer_rLe.
Qed.

Lemma Ord_mul_dist (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  : Ord.mul alpha (Ord.add beta alpha1) =ᵣ Ord.add (Ord.mul alpha beta) (Ord.mul alpha alpha1).
Proof.
  revert alpha beta. induction (rLt_wf alpha1) as [alpha1 _ IH]. intros alpha beta. destruct alpha1 as [cs ts].
  etransitivity.
  { eapply Ord_mul_rEq_r. eapply Ord_add_mkNode. }
  etransitivity.
  { eapply Ord_mul_join. }
  etransitivity.
  { eapply Ord_join_rEq_r. eapply Ord_mul_sup. }
  etransitivity.
  - eapply Ord_join_rEq_r. eapply Ord_sup_rEq. intros c.
    etransitivity.
    { eapply Ord_mul_suc. }
    etransitivity.
    { eapply Ord_add_rEq_l. eapply IH. eapply member_implies_rLt. eapply member_intro. }
    eapply Ord_add_assoc.
  - symmetry. etransitivity.
    + eapply Ord_add_rEq_r. eapply Ord_mul_mkNode.
    + eapply Ord_add_sup.
Qed.

Lemma Ord_mul_assoc (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  : Ord.mul (Ord.mul alpha beta) alpha1 =ᵣ Ord.mul alpha (Ord.mul beta alpha1).
Proof.
  revert alpha beta. induction (rLt_wf alpha1) as [alpha1 _ IH]. intros alpha beta. destruct alpha1 as [cs ts].
  etransitivity.
  { eapply Ord_mul_mkNode. }
  symmetry. etransitivity.
  { eapply Ord_mul_rEq_r. eapply Ord_mul_mkNode. }
  etransitivity.
  { eapply Ord_mul_sup. }
  eapply Ord_sup_rEq. intros c. etransitivity.
  { eapply Ord_mul_dist. }
  { eapply Ord_add_rEq_l. symmetry. eapply IH. eapply member_implies_rLt. eapply member_intro. }
Qed.

Lemma Ord_exp_zer_r (alpha : Ord.t)
  : Ord_exp alpha Ord.zer =ᵣ Ord_one.
Proof.
  unfold Ord_exp, Ord.exp. eapply Ord_orec_zer.
Qed.

Lemma Ord_exp_base (alpha : Ord.t) (beta : Ord.t)
  (POS : Ord.zer <ᵣ alpha)
  : Ord_one ≦ᵣ Ord_exp alpha beta.
Proof.
  unfold Ord_exp, Ord.exp. eapply Ord_orec_le_base.
  - intros alpha1. eapply Ord_mul_base_l. exact POS.
  - intros alpha1 beta1 LE. eapply Ord_mul_rLe_l. exact LE.
Qed.

Lemma Ord_exp_pos (alpha : Ord.t) (beta : Ord.t)
  : Ord.zer <ᵣ Ord_exp alpha beta.
Proof.
  eapply rLt_rLe_rLt with (y := Ord_one).
  - unfold Ord_one, Ord.suc. eapply rLt_succ_intro.
  - unfold Ord_exp, Ord.exp. eapply Ord_orec_base_rLe.
Qed.

Lemma Ord_exp_mkNode (alpha : Ord.t) (cs : Type@{Set_u}) (ts : cs -> Ord.t)
  : Ord_exp alpha (mkNode cs ts) =ᵣ Ord_join Ord_one (Ord.sup cs (fun c : cs => Ord.mul (Ord_exp alpha (ts c)) alpha)).
Proof.
  unfold Ord_exp, Ord.exp. rewrite Ord_orec_unfold. reflexivity.
Qed.

Lemma Ord_exp_suc (alpha : Ord.t) (beta : Ord.t)
  (POS : Ord.zer <ᵣ alpha)
  : Ord_exp alpha (Ord.suc beta) =ᵣ Ord.mul (Ord_exp alpha beta) alpha.
Proof.
  unfold Ord_exp, Ord.exp. eapply Ord_orec_suc.
  - intros alpha1. eapply Ord_mul_base_l. exact POS.
  - intros alpha1 beta1 LE. eapply Ord_mul_rLe_l. exact LE.
Qed.

Lemma Ord_exp_rLe_r (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (POS : Ord.zer <ᵣ alpha)
  (LE : beta ≦ᵣ alpha1)
  : Ord_exp alpha beta ≦ᵣ Ord_exp alpha alpha1.
Proof.
  unfold Ord_exp, Ord.exp. eapply Ord_orec_rLe; eauto.
  - intros beta1. eapply Ord_mul_base_l. exact POS.
  - intros beta1 beta2 LE'. eapply Ord_mul_rLe_l. exact LE'.
Qed.

Lemma Ord_exp_rEq_r (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (POS : Ord.zer <ᵣ alpha)
  (EQ : beta =ᵣ alpha1)
  : Ord_exp alpha beta =ᵣ Ord_exp alpha alpha1.
Proof.
  rewrite rEq_iff in *. destruct EQ as [LE GE]. split; now eapply Ord_exp_rLe_r.
Qed.

Lemma Ord_exp_rLe_l (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (LE : alpha ≦ᵣ beta)
  : Ord_exp alpha alpha1 ≦ᵣ Ord_exp beta alpha1.
Proof.
  revert alpha beta LE. induction (rLt_wf alpha1) as [alpha1 _ IH]. intros alpha beta LE. destruct alpha1 as [cs ts].
  transitivity (Ord_join Ord_one (Ord.sup cs (fun c : cs => Ord.mul (Ord_exp alpha (ts c)) alpha))).
  { exact (proj1 (proj1 (rEq_iff _ _) (Ord_exp_mkNode alpha cs ts))). }
  transitivity (Ord_join Ord_one (Ord.sup cs (fun c : cs => Ord.mul (Ord_exp beta (ts c)) beta))).
  - eapply Ord_join_spec.
    + eapply Ord_join_l.
    + transitivity (Ord.sup cs (fun c : cs => Ord.mul (Ord_exp beta (ts c)) beta)).
      * eapply Ord_sup_rLe. intros c. transitivity (Ord.mul (Ord_exp beta (ts c)) alpha).
        { eapply Ord_mul_rLe_l. eapply IH. eapply member_implies_rLt. eapply member_intro. exact LE. }
        { eapply Ord_mul_rLe_r. exact LE. }
      * eapply Ord_join_r.
  - exact (proj2 (proj1 (rEq_iff _ _) (Ord_exp_mkNode beta cs ts))).
Qed.

Lemma Ord_exp_rEq_l (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (EQ : alpha =ᵣ beta)
  : Ord_exp alpha alpha1 =ᵣ Ord_exp beta alpha1.
Proof.
  rewrite rEq_iff in *. destruct EQ as [LE GE]. split; now eapply Ord_exp_rLe_l.
Qed.

Lemma Ord_exp_sup (alpha : Ord.t) (I : Type@{Set_u}) (betas : I -> Ord.t)
  (POS : Ord.zer <ᵣ alpha)
  : Ord_exp alpha (Ord.sup I betas) =ᵣ Ord_join Ord_one (Ord.sup I (fun i : I => Ord_exp alpha (betas i))).
Proof.
  unfold Ord_exp, Ord.exp. eapply Ord_orec_sup.
  - intros beta. eapply Ord_mul_base_l. exact POS.
  - intros beta alpha1 LE. eapply Ord_mul_rLe_l. exact LE.
Qed.

Lemma Ord_exp_sup_inhabited (alpha : Ord.t) (I : Type@{Set_u}) (betas : I -> Ord.t)
  (POS : Ord.zer <ᵣ alpha)
  (INHABITED : inhabited I)
  : Ord_exp alpha (Ord.sup I betas) =ᵣ Ord.sup I (fun i : I => Ord_exp alpha (betas i)).
Proof.
  etransitivity.
  - eapply Ord_exp_sup. exact POS.
  - destruct INHABITED as [i]. eapply Ord_join_max_r. transitivity (Ord_exp alpha (betas i)).
    + unfold Ord_exp, Ord.exp. eapply Ord_orec_le_base.
      * intros beta. eapply Ord_mul_base_l. exact POS.
      * intros beta alpha1 LE. eapply Ord_mul_rLe_l. exact LE.
    + change ((fun i : I => Ord_exp alpha (betas i)) i ≦ᵣ Ord.sup I (fun i : I => Ord_exp alpha (betas i))). eapply Ord_rLe_sup_intro.
Qed.

Lemma Ord_exp_join (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (POS : Ord.zer <ᵣ alpha)
  : Ord_exp alpha (Ord_join beta alpha1) =ᵣ Ord_join (Ord_exp alpha beta) (Ord_exp alpha alpha1).
Proof.
  unfold Ord_join at 1. etransitivity.
  - eapply Ord_exp_sup_inhabited; eauto. do 2 econs.
  - unfold Ord_join. eapply Ord_sup_rEq. intros [ | ]; reflexivity.
Qed.

Lemma Ord_exp_one_r (alpha : Ord.t)
  (POS : Ord.zer <ᵣ alpha)
  : Ord_exp alpha Ord_one =ᵣ alpha.
Proof.
  unfold Ord_one. etransitivity.
  { eapply Ord_exp_suc. exact POS. }
  etransitivity.
  - eapply Ord_mul_rEq_l. eapply Ord_exp_zer_r.
  - eapply Ord_mul_one_l.
Qed.

Lemma Ord_exp_one_l (alpha : Ord.t)
  : Ord_exp Ord_one alpha =ᵣ Ord_one.
Proof.
  induction alpha as [cs ts IH]. etransitivity.
  { eapply Ord_exp_mkNode. }
  eapply Ord_join_max_l. eapply Ord_sup_rLe_intro. intros c.
  transitivity (Ord.mul Ord_one Ord_one).
  - exact (proj1 (proj1 (rEq_iff _ _) (Ord_mul_rEq_l (Ord_exp Ord_one (ts c)) Ord_one Ord_one (IH c)))).
  - exact (proj1 (proj1 (rEq_iff _ _) (Ord_mul_one_r Ord_one))).
Qed.

Theorem Ord_exp_isOrdinal (alpha : Ord.t) (beta : Ord.t)
  (ALPHA : isOrdinal alpha)
  : isOrdinal (Ord_exp alpha beta).
Proof.
  unfold Ord_exp, Ord.exp. eapply Ord_orec_isOrdinal.
  - eapply Ord_one_isOrdinal.
  - intros alpha1 ORDINAL. eapply Ord_mul_isOrdinal. exact ORDINAL.
Qed.

Lemma Ord_exp_add (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (POS : Ord.zer <ᵣ alpha)
  : Ord_exp alpha (Ord.add beta alpha1) =ᵣ Ord.mul (Ord_exp alpha beta) (Ord_exp alpha alpha1).
Proof.
  revert beta. induction (rLt_wf alpha1) as [alpha1 _ IH]. intros beta. destruct alpha1 as [cs ts].
  etransitivity.
  { eapply Ord_exp_rEq_r. exact POS. eapply Ord_add_mkNode. }
  etransitivity.
  { eapply Ord_exp_join. exact POS. }
  etransitivity.
  { eapply Ord_join_rEq_r. eapply Ord_exp_sup. exact POS. }
  etransitivity.
  { eapply Ord_join_assoc. }
  etransitivity.
  { eapply Ord_join_rEq_l. eapply Ord_join_max_l. eapply Ord_exp_base. exact POS. }
  etransitivity.
  - eapply Ord_join_rEq_r. eapply Ord_sup_rEq. intros c. etransitivity.
    { eapply Ord_exp_suc. exact POS. }
    etransitivity.
    { eapply Ord_mul_rEq_l. eapply IH. eapply member_implies_rLt. eapply member_intro. }
    { eapply Ord_mul_assoc. }
  - symmetry. etransitivity.
    { eapply Ord_mul_rEq_r. eapply Ord_exp_mkNode. }
    etransitivity.
    { eapply Ord_mul_join. }
    etransitivity.
    { eapply Ord_join_rEq_l. eapply Ord_mul_one_r. }
    { eapply Ord_join_rEq_r. eapply Ord_mul_sup. }
Qed.

Lemma Ord_exp_mul (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (POS : Ord.zer <ᵣ alpha)
  : Ord_exp alpha (Ord.mul beta alpha1) =ᵣ Ord_exp (Ord_exp alpha beta) alpha1.
Proof.
  revert beta. induction (rLt_wf alpha1) as [alpha1 _ IH]. intros beta. destruct alpha1 as [cs ts].
  etransitivity.
  { eapply Ord_exp_rEq_r. exact POS. eapply Ord_mul_mkNode. }
  etransitivity.
  { eapply Ord_exp_sup. exact POS. }
  symmetry. etransitivity.
  { eapply Ord_exp_mkNode. }
  eapply Ord_join_rEq_r. eapply Ord_sup_rEq. intros c. symmetry. etransitivity.
  - eapply Ord_exp_add. exact POS.
  - eapply Ord_mul_rEq_l. eapply IH. eapply member_implies_rLt. eapply member_intro.
Qed.

Lemma Ord_exp_rLt_r (alpha : Ord.t) (beta : Ord.t) (alpha1 : Ord.t)
  (TWO : Ord_one <ᵣ alpha)
  (LT : beta <ᵣ alpha1)
  : Ord_exp alpha beta <ᵣ Ord_exp alpha alpha1.
Proof.
  assert (POS : Ord.zer <ᵣ alpha).
  { eapply rLe_rLt_rLt with (y := Ord_one).
    - unfold Ord_one, Ord.suc. eapply rLt_implies_rLe. eapply rLt_succ_intro.
    - exact TWO.
  }
  eapply rLt_rLe_rLt with (y := Ord_exp alpha (Ord.suc beta)).
  - eapply rLt_rLe_rLt with (y := Ord.mul (Ord_exp alpha beta) alpha).
    + eapply Ord_mul_rLt_larger.
      * eapply Ord_exp_pos.
      * exact TWO.
    + exact (proj2 (proj1 (rEq_iff _ _) (Ord_exp_suc alpha beta POS))).
  - eapply Ord_exp_rLe_r.
    + exact POS.
    + unfold Ord.suc. eapply succ_rLe_intro. exact LT.
Qed.

Fixpoint Ord_of_nat (n : nat) : Ord.t :=
  match n with
  | O => empty
  | S n' => succ (Ord_of_nat n')
  end.

Lemma Ord_of_nat_zer
  : Ord_of_nat O = Ord.zer.
Proof.
  reflexivity.
Qed.

Lemma Ord_of_nat_suc (n : nat)
  : Ord_of_nat (S n) = Ord.suc (Ord_of_nat n).
Proof.
  reflexivity.
Qed.

Lemma Ord_of_nat_one
  : Ord_of_nat 1 = Ord_one.
Proof.
  reflexivity.
Qed.

Lemma Ord_of_nat_isOrdinal (n : nat)
  : isOrdinal (Ord_of_nat n).
Proof.
  induction n as [ | n IH]; simpl.
  - eapply zer_isOrdinal.
  - eapply suc_isOrdinal. exact IH.
Qed.

Lemma Ord_of_nat_rLe (m : nat) (n : nat)
  (LE : m <= n)
  : Ord_of_nat m ≦ᵣ Ord_of_nat n.
Proof.
  revert m LE; induction n as [ | n IH]; intros m LE.
  - destruct m as [ | m].
    + reflexivity.
    + lia.
  - destruct m as [ | m].
    + eapply Ord_zer_rLe.
    + simpl. eapply Ord_suc_rLe. eapply IH. lia.
Qed.

Lemma Ord_of_nat_rLt (m : nat) (n : nat)
  (LT : m < n)
  : Ord_of_nat m <ᵣ Ord_of_nat n.
Proof.
  destruct n as [ | n].
  - lia.
  - destruct m as [ | m].
    + simpl. unfold Ord.suc. rewrite rLt_succ_iff.
      eapply Ord_zer_rLe.
    + simpl. unfold Ord.suc. rewrite rLt_succ_iff.
      change (Ord_of_nat (S m) ≦ᵣ Ord_of_nat n).
      eapply Ord_of_nat_rLe. lia.
Qed.

Lemma Ord_add_of_nat (m : nat) (n : nat)
  : Ord.add (Ord_of_nat m) (Ord_of_nat n) =ᵣ Ord_of_nat (m + n).
Proof.
  induction n as [ | n IH]; simpl.
  - rewrite Nat.add_0_r. eapply Ord_add_zer_r.
  - rewrite Nat.add_succ_r. etransitivity.
    { eapply Ord_add_suc. }
    { eapply Ord_suc_rEq. exact IH. }
Qed.

Lemma Ord_mul_of_nat (m : nat) (n : nat)
  : Ord.mul (Ord_of_nat m) (Ord_of_nat n) =ᵣ Ord_of_nat (m * n).
Proof.
  induction n as [ | n IH]; simpl.
  - rewrite Nat.mul_0_r. eapply Ord_mul_zer_r.
  - rewrite Nat.mul_succ_r. etransitivity.
    { eapply Ord_mul_suc. }
    etransitivity.
    { eapply Ord_add_rEq_l. exact IH. }
    { eapply Ord_add_of_nat. }
Qed.

Lemma Ord_exp_of_nat (m : nat) (n : nat)
  (POS : 0 < m)
  : Ord_exp (Ord_of_nat m) (Ord_of_nat n) =ᵣ Ord_of_nat (Nat.pow m n).
Proof.
  induction n as [ | n IH]; simpl.
  - eapply Ord_exp_zer_r.
  - etransitivity.
    { eapply Ord_exp_suc. change (Ord_of_nat O <ᵣ Ord_of_nat m). eapply Ord_of_nat_rLt. exact POS. }
    etransitivity.
    { eapply Ord_mul_rEq_l. exact IH. }
    { rewrite Nat.mul_comm. eapply Ord_mul_of_nat. }
Qed.

Definition omega : Ord.t :=
  indexed_union nat Ord_of_nat.

Lemma omega_upperbound (n : nat)
  : Ord_of_nat n <ᵣ omega.
Proof.
  eapply rLt_rLe_rLt with (y := Ord_of_nat (S n)).
  - eapply Ord_of_nat_rLt. lia.
  - change (Ord_of_nat (S n) ≦ᵣ Ord.sup nat Ord_of_nat). eapply Ord_rLe_sup_intro.
Qed.

Lemma omega_supremum (alpha : Ord.t)
  (LE : forall n : nat, Ord_of_nat n ≦ᵣ alpha)
  : omega ≦ᵣ alpha.
Proof.
  unfold omega. rewrite indexed_union_rLe_iff. exact LE.
Qed.

Lemma omega_isOrdinal
  : isOrdinal omega.
Proof.
  unfold omega. eapply sup_isOrdinal. eapply Ord_of_nat_isOrdinal.
Qed.

End ORDINAL_ARITHMETIC.
