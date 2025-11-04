Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Data.Aczel.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Prelude.AC.
Require Import PnV.Math.SetTheory.

Import TypeTheoreticImplementation.

Module InducedOrdinal <: LEM_ModuleAttribute.

Section THEORY_ON_RANK.

#[local] Infix "\in" := member : type_scope.

#[local] Existing Instance rEq_asSetoid.

#[local]
Instance Tree_rLt_isWellPoset : isWellPoset Tree :=
  { wltProp := rLt
  ; wltProp_Transitive := rLt_StrictOrder.(StrictOrder_Transitive)
  ; wltProp_well_founded := rLt_wf
  }.

#[local]
Instance Tree_rLt_isWoset : isWoset Tree (SETOID := rEq_asSetoid) :=
  { Woset_isWellPoset := Tree_rLt_isWellPoset
  ; Woset_eqPropCompatible2 := rLt_eqPropCompatible2
  ; Woset_ext_eq := rEq_ext
  }.

Lemma trichotomy (lhs : Tree) (rhs : Tree)
  : lhs =ᵣ rhs \/ (lhs <ᵣ rhs \/ rhs <ᵣ lhs).
Proof.
  change (lhs == rhs \/ lhs ≺ rhs \/ rhs ≺ lhs).
  eapply @O.wlt_trichotomous. exact classic.
Qed.

Lemma rLe_or_rGt (lhs : Tree) (rhs : Tree)
  : lhs ≦ᵣ rhs \/ rhs <ᵣ lhs.
Proof.
  pose proof (trichotomy lhs rhs) as [H | [H | H]]; try tauto; left.
  - now rewrite H.
  - now eapply rLt_implies_rLe.
Qed.

Lemma rLt_iff_not_rGe (lhs : Tree) (rhs : Tree)
  : lhs <ᵣ rhs <-> ~ rhs ≦ᵣ lhs.
Proof.
  split.
  - intros H_rLt H_rLe. contradiction (rLt_StrictOrder.(StrictOrder_Irreflexive) lhs).
    eapply rLt_rLe_rLt; eauto.
  - pose proof (rLe_or_rGt rhs lhs); tauto.
Qed.

Lemma rLe_total (lhs : Tree) (rhs : Tree)
  : lhs ≦ᵣ rhs \/ rhs ≦ᵣ lhs.
Proof.
  pose proof (rLe_or_rGt lhs rhs) as [H | H]; try tauto; right.
  now eapply rLt_implies_rLe.
Qed.

Lemma rLe_iff_rLt_or_rEq (lhs : Tree) (rhs : Tree)
  : lhs ≦ᵣ rhs <-> (lhs <ᵣ rhs \/ lhs =ᵣ rhs).
Proof.
  split.
  - intros H_rLe. pose proof (trichotomy lhs rhs) as [H | [H | H]]; try tauto.
    contradiction (rLt_StrictOrder.(StrictOrder_Irreflexive) rhs). eapply rLt_rLe_rLt; eauto.
  - intros [H | H].
    + eapply rLt_implies_rLe; eauto.
    + exact (proj1 H).
Qed.

Fixpoint fromAcc_complete (A : Type) (R : A -> A -> Prop) (x : A) (H_Acc : Acc R x) (o : Tree) (LT : o <ᵣ @fromAcc A R x H_Acc) {struct H_Acc} : exists x' : A, exists H_Acc' : Acc R x', o =ᵣ @fromAcc A R x' H_Acc'.
Proof.
  destruct H_Acc as [H_ACC_inv]; simpl in *. destruct LT as [[[c R_c_x] LE]]; simpl in *.
  rewrite rLe_iff_rLt_or_rEq in LE. destruct LE as [LT | EQ].
  - eapply fromAcc_complete. exact LT.
  - exists c. exists (H_ACC_inv c R_c_x). exact EQ.
Qed.

Lemma fromWf_complete {A : Type} (R : A -> A -> Prop) (R_wf : well_founded R) (x : A) (o : Tree)
  (LT : o <ᵣ @fromWf A R R_wf x)
  : exists x' : A, o =ᵣ @fromWf A R R_wf x'.
Proof.
  unfold fromWf in *. apply fromAcc_complete in LT. des.
  exists x'. rewrite fromAcc_pirrel. exact LT.
Qed.

Lemma fromWfSet_complete {A : Type} (R : A -> A -> Prop) (R_wf : well_founded R) (x : A) (o : Tree)
  (LT : o <ᵣ @fromWfSet A R R_wf)
  : exists x' : A, o =ᵣ @fromWf A R R_wf x'.
Proof.
  unfold fromWfSet in LT. destruct LT as [[c LE]]; simpl in *.
  rewrite rLe_iff_rLt_or_rEq in LE. destruct LE as [LT | EQ].
  - eapply fromWf_complete. exact LT.
  - exists c. eauto.
Qed.

Lemma fromWfSet_lt {A : Type} {R : A -> A -> Prop} {R' : A -> A -> Prop}
  (INCL : forall x : A, forall x' : A, forall LE : R x x', R' x x')
  (WF : well_founded R)
  (WF' : well_founded R')
  (TOP : exists top : A, (exists x, R' x top) /\ (forall x, forall x', R x x' -> R' x' top))
  : @fromWfSet A R WF <ᵣ @fromWfSet A R' WF'.
Proof.
  des. econs. exists top. simpl. unfold fromWf. destruct (WF' top) as [H_ACC_inv]; simpl. econs. intros x'.
  pose proof (classic (exists x0, R x0 x')) as [YES | NO].
  - des. econs. exists (@exist _ _ x' (TOP0 _ _ YES)). simpl in *. unfold fromWf. eapply fromAcc_isMonotonic; eauto.
  - econs. simpl. exists (@exist _ _ x TOP). simpl. unfold fromWfSet in x'. simpl in x'. unfold fromWf.
    destruct (WF x'), (H_ACC_inv x TOP); econs; simpl. intros [c R_c_x']. contradiction NO. now exists c.
Qed.

Variant is_minimum_of (P : Tree -> Prop) (o : Tree) : Prop :=
  | is_minimum_of_intro
    (IN : P o)
    (MIN : forall o' : Tree, forall IN : P o', o ≦ᵣ o').

Lemma minimum_exists (P : Tree -> Prop)
  (INHABITED : exists o, P o)
  : exists o', is_minimum_of P o'.
Proof.
  pose proof (O.minimisation_lemma (classic := classic) P INHABITED) as (o' & IN & MIN); unnw.
  exists o'. econs; eauto. intros o1 o1_in. rewrite rLe_iff_rLt_or_rEq. now eapply MIN.
Qed.

Lemma limit_or_succ (alpha : Tree)
  : ⟪ LIMIT : alpha =ᵣ unions alpha ⟫ \/ ⟪ SUCC : exists beta, alpha =ᵣ succ beta ⟫.
Proof.
  unnw. destruct alpha as [cs ts]. pose proof (classic (forall c, exists c', ts c <ᵣ ts c')) as [YES | NO].
  - left. split.
    + econs. simpl; i. econs. simpl. pose proof (YES c) as [c' [[t H_rLe]]].
      exists (@existT cs (fun i => children (ts i)) c' t). exact H_rLe.
    + econs. simpl; i. econs. simpl. exists (projT1 c). eapply rLt_implies_rLe. econs. now exists (projT2 c).
  - assert (exists c : cs, forall c' : cs, ~ ts c <ᵣ ts c') as [c H_c].
    { eapply NNPP. intros H_contra. contradiction NO. intros c.
      eapply NNPP. intros H. contradiction H_contra. exists c. intros c' YES. contradiction H. eauto.
    }
    right. exists (ts c). rewrite rEq_succ_iff. intros z. split.
    + intros [[c' H_rLe]]. simpl in *. pose proof (classic (ts c' ≦ᵣ ts c)) as [H | H].
      * transitivity (ts c'); eauto.
      * pose proof (H_c c') as H'. pose proof (rLe_or_rGt (ts c') (ts c)); tauto.
    + intros H_rLe. econs. simpl. now exists c.
Qed.

Theorem transfinite_induction (P : Tree -> Prop)
  (P_zero : forall o, forall ZERO : o =ᵣ empty, P o)
  (P_succ : forall o, forall alpha : Tree, ⟪ IH : P alpha ⟫ -> forall SUCC : o =ᵣ succ alpha, P o)
  (P_lim' : forall o, forall I : Type, ⟪ INHABITED : inhabited I ⟫ -> forall alpha : I -> Tree, ⟪ IH : forall i, P (alpha i) ⟫ -> forall LIMIT : o =ᵣ @indexed_union I alpha, ⟪ OPEN : forall i1 : I, exists i2 : I, alpha i1 <ᵣ alpha i2 ⟫ -> P o)
  : forall o : Tree, P o.
Proof.
  intros o. pose proof (rLt_wf o) as H_Acc. induction H_Acc as [o _ IH]. pose proof (limit_or_succ o) as [LIMIT | SUCC]; unnw.
  - pose proof (classic (inhabited (children o))) as [YES | NO].
    + eapply P_lim' with (I := children o); eauto.
      * intros i. eapply IH. econs. now exists i.
      * destruct o; simpl in *. intros c. destruct LIMIT as [LE1 LE2]. unfold unions, indexed_union in *. simpl in *. destruct LE1 as [H_rLt]. simpl in *.
        pose proof (H_rLt c) as [[c' H_rLe]]. simpl in *. exists (projT1 c'). econs. exists (projT2 c'). exact H_rLe.
    + eapply P_zero. split.
      * econs. intros i. contradiction NO. econs. exact i.
      * econs. simpl. intros [].
  - destruct SUCC as [beta SUCC]. eapply P_succ; eauto. eapply IH. rewrite rEq_succ_iff in SUCC. now rewrite -> SUCC.
Qed.

Section _REC1.

Context {D : Type}.
Variable good : D -> Prop.
Variable dle : D -> D -> Prop.
#[local] Infix "⊑" := dle.

Hypothesis dle_refl : forall d1 : D, forall GOOD1 : good d1, d1 ⊑ d1.
Hypothesis dle_trans : forall d1 : D, forall d2 : D, forall d3 : D, forall GOOD1 : good d1, forall GOOD2 : good d2, forall GOOD3 : good d3, forall LE : d1 ⊑ d2, forall LE' : d2 ⊑ d3, d1 ⊑ d3.

Lemma dle_unfold (d1 : D) (d2 : D)
  (GOOD1 : good d1)
  (GOOD2 : good d2)
  : d1 ⊑ d2 <-> (forall d : D, forall GOOD : good d, d ⊑ d1 -> d ⊑ d2).
Proof.
  split; ii; eauto.
Qed.

Let deq (lhs : D) (rhs : D) : Prop :=
  lhs ⊑ rhs /\ rhs ⊑ lhs.
#[local] Infix "≡" := deq.
#[local] Hint Unfold deq : core.

Lemma deq_refl d1
  (GOOD1 : good d1)
  : d1 ≡ d1.
Proof.
  split; eauto.
Qed.

Lemma deq_sym d1 d2
  (EQ : d1 ≡ d2)
  : d2 ≡ d1.
Proof.
  unfold deq in *; tauto.
Qed.

Lemma deq_trans d1 d2 d3
  (GOOD1 : good d1)
  (GOOD2 : good d2)
  (GOOD3 : good d3)
  (EQ : d1 ≡ d2)
  (EQ' : d2 ≡ d3)
  : d1 ≡ d3.
Proof.
  red in EQ, EQ'; split; eapply dle_trans with (d2 := d2); eauto; tauto.
Qed.

Variable djoin : forall I : Type, (I -> D) -> D.
Hypothesis djoin_good : forall I : Type, forall ds : I -> D, forall CHAIN : forall i1, forall i2, ds i1 ⊑ ds i2 \/ ds i2 ⊑ ds i1, forall GOODs : forall i, good (ds i), good (djoin I ds).
Hypothesis djoin_supremum : forall I : Type, forall ds : I -> D, forall CHAIN : forall i1, forall i2, ds i1 ⊑ ds i2 \/ ds i2 ⊑ ds i1, forall GOODs : forall i, good (ds i), forall d : D, forall GOOD : good d, djoin I ds ⊑ d <-> (forall i, ds i ⊑ d).

Lemma djoin_upperbound (I : Type) (ds : I -> D)
  (CHAIN : forall i1, forall i2, ds i1 ⊑ ds i2 \/ ds i2 ⊑ ds i1)
  (GOODs : forall i, good (ds i))
  : forall i : I, ds i ⊑ djoin I ds.
Proof.
  i. eapply djoin_supremum; eauto.
Qed.

Variable dnext : D -> D.
Hypothesis dnext_good : forall d : D, forall GOOD : good d, good (dnext d).
Hypothesis dnext_extensive : forall d : D, forall GOOD : good d, d ⊑ dnext d.
Hypothesis dnext_congruence : forall d : D, forall d' : D, forall GOOD : good d, forall GOOD' : good d', forall EQ : d ≡ d', dnext d ≡ dnext d'.

Variable dbase : D.
Hypothesis dbase_good : good dbase.

Let rec : Tree -> D :=
  Ord.rec dbase dnext djoin.

Let rLe_Reflexive (o : Tree) : o ≦ᵣ o :=
  PreOrder_Reflexive o.

Let trivial_rLt (cs : Type) (ts : cs -> Tree) (c : cs) : ts c <ᵣ mkNode cs ts :=
  rLt_intro (ts c) (mkNode cs ts) (@ex_intro _ _ c (rLe_Reflexive (ts c))).

#[local] Hint Resolve rLe_Reflexive trivial_rLt : core.

Theorem rec_spec (o : Tree)
  : ⟪ mono_rec : forall o', o' ≦ᵣ o -> rec o' ⊑ rec o ⟫ /\ ⟪ base_rec : dbase ⊑ rec o ⟫ /\ ⟪ next_rec : forall o', o' <ᵣ o -> dnext (rec o') ⊑ rec o ⟫ /\ ⟪ good_rec : good (rec o) ⟫.
Proof.
  rename o into t. pose proof (rLt_wf t) as H_Acc. induction H_Acc as [t _ IH]. destruct t as [cs ts]; simpl.
  assert (H_chain : forall cs' : Type, forall ts' : cs' -> Tree, forall LE : forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c, forall c1 : cs', forall c2 : cs', dnext (rec (ts' c1)) ⊑ dnext (rec (ts' c2)) \/ dnext (rec (ts' c2)) ⊑ dnext (rec (ts' c1))).
  { ii.
    assert (ts' c1 <ᵣ mkNode cs ts /\ ts' c2 <ᵣ mkNode cs ts) as [helper1 helper2].
    { split; econs; eapply LE. }
    pose proof (trichotomy (ts' c1) (ts' c2)) as [EQ | [LT | GT]].
    - hexploit (dnext_congruence (rec (ts' c1)) (rec (ts' c2))).
      + eapply IH; eauto.
      + eapply IH; eauto.
      + destruct EQ as [LE1 LE2]. split; eapply IH; eauto.
      + intros H_deq. left. exact (proj1 H_deq).
    - left. eapply dle_trans with (d2 := rec (ts' c2)); eauto.
      + eapply dnext_good. eapply IH; eauto.
      + eapply IH; eauto.
      + eapply dnext_good. eapply IH; eauto.
      + eapply IH; eauto.
      + eapply dnext_extensive. eapply IH; eauto.
    - right. eapply dle_trans with (d2 := rec (ts' c1)); eauto.
      + eapply dnext_good. eapply IH; eauto.
      + eapply IH; eauto.
      + eapply dnext_good. eapply IH; eauto.
      + eapply IH; eauto.
      + eapply dnext_extensive. eapply IH; eauto.
  }
  assert (H_dnext_good : forall cs' : Type, forall ts' : cs' -> Tree, forall LE : forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c, forall c' : cs', good (dnext (rec (ts' c')))).
  { ii. eapply dnext_good. eapply IH; eauto. econs. eapply LE. }
  set (fun cs' : Type => fun ts' : cs' -> Tree => fun b : bool => if b then dbase else djoin cs' (fun c' => dnext (rec (ts' c')))) as f.
  assert (claim1 : forall b1 : bool, forall b2 : bool, forall cs' : Type, forall ts' : cs' -> Tree, forall LE : forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c, f cs' ts' b1 ⊑ f cs' ts' b2 \/ f cs' ts' b2 ⊑ f cs' ts' b1).
  { ii.
    assert (helper1 : forall c' : cs', ts' c' <ᵣ mkNode cs ts).
    { i; econs; eapply LE. }
    assert (helper2 : dbase ⊑ djoin cs' (fun c' : cs' => dnext (rec (ts' c'))) \/ djoin cs' (fun c' : cs' => dnext (rec (ts' c'))) ⊑ dbase).
    { pose proof (classic (inhabited cs')) as [YES | NO].
      - destruct YES as [c']. left. eapply dle_trans with (d2 := dnext (rec (ts' c'))); eauto.
        + eapply dle_trans with (d2 := rec (ts' c')); eauto.
          * eapply IH; eauto.
          * eapply IH; eauto.
          * eapply dnext_extensive. eapply IH; eauto.
        + eapply djoin_upperbound with (ds := fun c' : cs' => dnext (rec (ts' c'))); eauto.
      - right. eapply djoin_supremum; eauto. intros c'. contradiction NO. econs. exact c'.
    }
    destruct b1, b2; simpl in *; eauto; [tauto | left; eapply dle_refl]. eapply djoin_good; eauto.
  }
  assert (claim2 : forall b : bool, forall cs' : Type, forall ts' : cs' -> Tree, forall LE : forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c, good (f cs' ts' b)).
  { ii. destruct b; eauto. }
  set (djoin bool (f cs ts)) as x.
  assert (claim3 : good x).
  { eapply djoin_good; eauto. }
  assert (claim4 : dbase ⊑ x).
  { eapply djoin_upperbound with (ds := f cs ts) (i := true); eauto. }
  assert (claim5 : forall cs' : Type, forall ts' : cs' -> Tree, forall H_rLt : forall c, ts' c <ᵣ mkNode cs ts, forall c' : cs', exists c : cs, ts' c' ≦ᵣ ts c).
  { ii. pose proof (H_rLt c') as [[c H_rLe]]; simpl in *. exists c. exact H_rLe. }
  assert (claim6 : forall o : Tree, forall LE : o ≦ᵣ mkNode cs ts, rec o ⊑ x).
  { intros [cs' ts'] [H_rLt]. simpl in *. unfold Ord.join.
    change (fun b : bool => if b then dbase else djoin cs' (fun c : cs' => dnext (rec (ts' c)))) with (f cs' ts').
    rewrite -> djoin_supremum; eauto. destruct i; eauto. simpl. eapply djoin_supremum; i; eauto.
    unfold x. eapply dle_trans with (d2 := djoin cs' (fun c' => dnext (rec (ts' c')))); eauto.
    - eapply djoin_good; eauto.
    - eapply djoin_upperbound with (ds := fun c' : cs' => dnext (rec (ts' c'))); eauto.
    - eapply djoin_supremum; eauto. intros c'. pose proof (H_rLt c') as [[c H_rLe]]; simpl in *.
      rewrite rLe_iff_rLt_or_rEq in H_rLe. destruct H_rLe as [H_LT | H_EQ].
      + eapply dle_trans with (d2 := dnext (rec (ts c))); eauto.
        { eapply dle_trans with (d2 := rec (ts c)); eauto.
          - eapply IH; eauto.
          - eapply IH; eauto.
          - eapply dnext_extensive; eauto. eapply IH; eauto.
        }
        { unfold f. eapply dle_trans with (d2 := djoin cs (fun i : cs => dnext (rec (ts i)))); eauto.
          - eapply djoin_good; eauto.
          - eapply djoin_upperbound with (ds := fun c : cs => dnext (rec (ts c))); eauto.
          - eapply djoin_upperbound with (ds := f cs ts) (i := false); eauto.
        }
      + eapply dle_trans with (d2 := dnext (rec (ts c))); eauto.
        { eapply dnext_congruence.
          - eapply IH; eauto.
          - eapply IH; eauto.
          - destruct H_EQ as [H_LE1 H_LE2]. split; eapply IH; eauto.
        }
        { unfold f. eapply dle_trans with (d2 := djoin cs (fun i : cs => dnext (rec (ts i)))); eauto.
          - eapply djoin_good; eauto.
          - eapply djoin_upperbound with (ds := fun c : cs => dnext (rec (ts c))); eauto.
          - eapply djoin_upperbound with (ds := f cs ts) (i := false); eauto.
        }
  }
  split; eauto. split; eauto. split; eauto. intros o H_rLt.
  pose proof (classic (exists o' : Tree, o <ᵣ o' /\ o' <ᵣ mkNode cs ts)) as [YES | NO].
  - unfold Ord.join. des. hexploit (IH o'); eauto. i; des. eapply dle_trans with (d2 := rec o'); eauto.
    + eapply dnext_good. eapply IH; eauto.
    + unfold x, f in claim6. eapply claim6. eapply rLt_implies_rLe; eauto.
  - assert (exists c, ts c =ᵣ o) as [c H_rEq].
    { eapply NNPP. intros H_contra. rewrite rLt_iff_not_rGe in H_rLt. contradiction H_rLt.
      econs. simpl. intros c. pose proof (trichotomy (ts c) o) as [H_EQ | [H_LT | H_GT]]; eauto.
      - contradiction H_contra; eauto.
      - contradiction NO; eauto.
    }
    assert (rec o ≡ rec (ts c)) as claim7.
    { destruct H_rEq; split; eapply IH; eauto. }
    unfold Ord.join. eapply dle_trans with (d2 := dnext (rec (ts c))); eauto.
    { eapply dnext_good. eapply IH; eauto. }
    { eapply dnext_congruence.
      - eapply IH; eauto.
      - eapply IH; eauto.
      - eapply deq_sym; eauto.
    }
    { eapply dle_trans with (d2 := djoin cs (fun i : cs => dnext (rec (ts i)))); eauto.
      - eapply djoin_good; eauto.
      - eapply djoin_upperbound with (ds := fun c : cs => dnext (rec (ts c))); eauto.
      - eapply djoin_upperbound with (ds := f cs ts) (i := false); eauto.
    }
Qed.

Lemma le_rec (t : Tree) (t' : Tree)
  (H_rLe : t ≦ᵣ t')
  : rec t ⊑ rec t'.
Proof.
  eapply rec_spec; eauto.
Qed.

Lemma eq_rec (t : Tree) (t' : Tree)
  (H_rLe : t =ᵣ t')
  : rec t ≡ rec t'.
Proof.
  destruct H_rLe; split; eapply rec_spec; eauto.
Qed.

Lemma lt_rec (t : Tree) (t' : Tree)
  (H_rLt : t <ᵣ t')
  : dnext (rec t) ⊑ rec t'.
Proof.
  eapply rec_spec; eauto.
Qed.

Lemma rec_le_base (t : Tree)
  : dbase ⊑ rec t.
Proof.
  eapply rec_spec; eauto.
Qed.

Lemma good_rec (t : Tree)
  : good (rec t).
Proof.
  eapply rec_spec; eauto.
Qed.

#[local] Hint Resolve le_rec lt_rec eq_rec rec_le_base good_rec deq_sym : core.

Lemma rec_dnext_dle (t : Tree) (t' : Tree)
  (H_rLe : t ≦ᵣ t')
  : dnext (rec t) ⊑ dnext (rec t').
Proof.
  rewrite rLe_iff_rLt_or_rEq in H_rLe. destruct H_rLe as [H_rLt | H_rEq].
  - eapply dle_trans with (d2 := rec t'); eauto.
  - eapply dnext_congruence; eauto.
Qed.

Lemma rec_chain (t : Tree) (t' : Tree)
  : rec t ⊑ rec t' \/ rec t' ⊑ rec t.
Proof.
  pose proof (rLe_total t t') as [H | H]; [left | right]; eauto.
Qed.

Lemma rec_next_chain (t : Tree) (t' : Tree)
  : dnext (rec t) ⊑ dnext (rec t') \/ dnext (rec t') ⊑ dnext (rec t).
Proof.
  pose proof (rLe_total t t') as [H | H]; [left | right]; eapply rec_dnext_dle; eauto.
Qed.

Lemma good_next_rec (cs : Type) (ts : cs -> Tree)
  : forall c : cs, good (dnext (rec (ts c))).
Proof.
  eauto.
Qed.

#[local] Hint Resolve rec_dnext_dle rec_chain rec_next_chain good_next_rec : core.

Let j (cs : Type) (ts : cs -> Tree) (b : bool) : D :=
  if b then dbase else djoin cs (fun c => dnext (rec (ts c))).

Lemma j_chain (cs : Type) (ts : cs -> Tree) (b : bool) (b' : bool)
  : j cs ts b ⊑ j cs ts b' \/ j cs ts b' ⊑ j cs ts b.
Proof.
  assert (dbase ⊑ djoin cs (fun c => dnext (rec (ts c))) \/ djoin cs (fun c => dnext (rec (ts c))) ⊑ dbase) as claim1.
  { pose proof (classic (inhabited cs)) as [YES | NO]; [left | right].
    - destruct YES as [c]. eapply dle_trans with (d2 := dnext (rec (ts c))); eauto. eapply djoin_upperbound with (ds := fun c : cs => dnext (rec (ts c))); eauto.
    - eapply djoin_supremum; eauto. intros c. contradiction NO. econs. exact c.
  }
  destruct b, b'; simpl; eauto; try tauto.
Qed.

Lemma good_j (cs : Type) (ts : cs -> Tree)
  : forall b, good (j cs ts b).
Proof.
  intros [ | ]; simpl; eauto.
Qed.

#[local] Hint Resolve j_chain good_j : core.

Lemma rec_zero (o : Tree)
  (ZERO : o =ᵣ empty)
  : rec o ≡ dbase.
Proof.
  eapply deq_trans with (d2 := rec empty); eauto. simpl.
  change (djoin bool (j Empty_set (Empty_set_rect _)) ≡ dbase). split.
  - eapply djoin_supremum; eauto. intros [ | ]; eauto. eapply djoin_supremum; eauto. intros [].
  - eapply djoin_upperbound with (ds := j Empty_set (Empty_set_rect _)) (i := true); eauto.
Qed.

Lemma rec_succ (o : Tree) (alpha : Tree)
  (SUCC : o =ᵣ succ alpha)
  : rec o ≡ dnext (rec alpha).
Proof.
  eapply deq_trans with (d2 := rec (succ alpha)); eauto. simpl.
  change (djoin bool (j { b : bool & children (if b then alpha else singleton alpha) } (fun c => childnodes (if projT1 c then alpha else singleton alpha) (projT2 c))) ≡ dnext (rec alpha)). split.
  - eapply djoin_supremum; eauto. intros [ | ]; eauto. eapply djoin_supremum; eauto. intros [[ | ] c]; simpl; eapply rec_dnext_dle.
    + eapply rLt_implies_rLe. econs. exists c. reflexivity.
    + simpl in c. destruct c as [ | ]; reflexivity.
  - refine (let c : { b : bool & children (if b then alpha else singleton alpha) } := @existT _ _ false true in _).
    eapply dle_trans with (d2 := djoin { b : bool & children (if b then alpha else singleton alpha) } (fun c => dnext (rec (childnodes (if projT1 c then alpha else singleton alpha) (projT2 c))))); eauto.
    + eapply djoin_upperbound with (ds := fun c : {b : bool & children (if b then alpha else singleton alpha)} => dnext (rec (childnodes (if projT1 c then alpha else singleton alpha) (projT2 c)))) (i := c); eauto.
    + eapply djoin_upperbound with (ds := j { b : bool & children (if b then alpha else singleton alpha) } (fun c => childnodes (if projT1 c then alpha else singleton alpha) (projT2 c))) (i := false); eauto.
Qed.

Lemma rec_lim' (o : Tree) (cs : Type) (ts : cs -> Tree)
  (LIM_ORD : forall c1 : cs, exists c2 : cs, ts c1 <ᵣ ts c2)
  (INHABITED : inhabited cs)
  (LIM' : o =ᵣ indexed_union cs ts)
  : rec o ≡ djoin cs (fun c : cs => rec (ts c)).
Proof.
  destruct INHABITED as [c]. destruct o as [cs' ts']; simpl.
  change (djoin bool (j cs' ts') ≡ djoin cs (fun i : cs => rec (ts i))); split.
  - eapply djoin_supremum; eauto. intros [ | ]; simpl.
    + eapply dle_trans with (d2 := rec (ts c)); eauto. eapply djoin_upperbound with (ds := fun i : cs => rec (ts i)) (i := c); eauto.
    + eapply djoin_supremum; eauto. clear c. intros c'. destruct LIM' as [LE1 LE2]; simpl in *. destruct LE1 as [H_rLt]; simpl in *.
      pose proof (H_rLt c') as [[c H_rLe]]; simpl in *. eapply dle_trans with (d2 := rec (ts (projT1 c))); eauto.
      * eapply lt_rec. econs. exists (projT2 c). exact H_rLe.
      * eapply djoin_upperbound with (ds := fun i : cs => rec (ts i)) (i := projT1 c); eauto.
  - eapply djoin_supremum; eauto. clear c. intros c. eapply dle_trans with (d2 := djoin cs (fun c => rec (ts c))); eauto.
    + eapply djoin_upperbound with (ds := fun i : cs => rec (ts i)) (i := c); eauto.
    + clear c. eapply djoin_supremum; eauto. intros c1. simpl in *. pose proof (LIM_ORD c1) as [c2 H_rLt].
      destruct H_rLt as [[c H_rLe]]. destruct LIM' as [LE1 LE2]. destruct LE2 as [LE2]; simpl in *.
      pose proof (LE2 (@existT cs (fun i : cs => children (ts i)) c2 c)) as claim1. simpl in *. destruct claim1 as [[c' H_rLe']]. simpl in *.
      eapply dle_trans with (d2 := rec (ts' c')); eauto. eapply dle_trans with (d2 := djoin cs' (fun i : cs' => dnext (rec (ts' i)))); eauto.
      * eapply dle_trans with (d2 := dnext (rec (ts' c'))); eauto. eapply djoin_upperbound with (ds := fun i : cs' => dnext (rec (ts' i))) (i := c'); eauto.
      * eapply djoin_upperbound with (ds := j cs' ts') (i := false); eauto.
Qed.

#[local] Notation dunion := (Ord.join djoin).

Lemma dunion_good (d1 : D) (d2 : D)
  (GOOD1 : good d1)
  (GOOD2 : good d2)
  (CHAIN : d1 ⊑ d2 \/ d2 ⊑ d1)
  : good (dunion d1 d2).
Proof.
  eapply djoin_good; eauto.
  - intros [ | ] [ | ]; eauto. des; eauto.
  - intros [ | ]; eauto.
Qed.

#[local] Hint Resolve dunion_good : core.

Lemma dunion_supremum (d1 : D) (d2 : D)
  (GOOD1 : good d1)
  (GOOD2 : good d2)
  (CHAIN : d1 ⊑ d2 \/ d2 ⊑ d1)
  : forall d : D, good d -> d1 ⊑ d -> d2 ⊑ d -> dunion d1 d2 ⊑ d.
Proof.
  ii. eapply djoin_supremum; eauto.
  - intros [ | ] [ | ]; eauto. des; eauto.
  - intros [ | ]; eauto.
  - intros [ | ]; eauto.
Qed.

Lemma dunion_l (d1 : D) (d2 : D)
  (GOOD1 : good d1)
  (GOOD2 : good d2)
  (CHAIN : d1 ⊑ d2 \/ d2 ⊑ d1)
  : d1 ⊑ dunion d1 d2.
Proof.
  eapply djoin_upperbound with (ds := fun b : bool => if b then d1 else d2) (i := true).
  - intros [ | ] [ | ]; eauto. des; auto.
  - intros [ | ]; eauto.
Qed.

Lemma dunion_r (d1 : D) (d2 : D)
  (GOOD1 : good d1)
  (GOOD2 : good d2)
  (CHAIN : d1 ⊑ d2 \/ d2 ⊑ d1)
  : d2 ⊑ dunion d1 d2.
Proof.
  eapply djoin_upperbound with (ds := fun b : bool => if b then d1 else d2) (i := false).
  - intros [ | ] [ | ]; eauto. des; auto.
  - intros [ | ]; eauto.
Qed.

#[local] Hint Resolve dunion_supremum dunion_l dunion_r : core.

Lemma BASEJOIN (cs : Type) (ts : cs -> Tree)
  : dbase ⊑ djoin cs (fun c : cs => rec (ts c)) \/ djoin cs (fun c : cs => rec (ts c)) ⊑ dbase.
Proof.
  destruct (classic (inhabited cs)) as [YES | NO].
  - destruct YES as [c]. left. eapply dle_trans with (d2 := rec (ts c)); eauto.
    eapply djoin_upperbound with (ds := fun a => rec (ts a)) (i := c); eauto.
  - right. eapply djoin_supremum; eauto. intros c. contradiction NO. econs. exact c.
Qed.

Lemma BASENEXTJOIN (cs : Type) (ts : cs -> Tree)
  : dbase ⊑ djoin cs (fun c : cs => dnext (rec (ts c))) \/ djoin cs (fun c : cs => dnext (rec (ts c))) ⊑ dbase.
Proof.
  destruct (classic (inhabited cs)) as [YES | NO].
  { destruct YES as [c]. left.
    eapply dle_trans with (d2 := rec (ts c)); eauto.
    eapply dle_trans with (d2 := dnext (rec (ts c))); eauto.
    eapply djoin_upperbound with (ds := fun c => dnext (rec (ts c))); eauto.
  }
  { right. eapply djoin_supremum; eauto. intros c. contradiction NO. econs; exact c. }
Qed.

#[local] Hint Resolve BASEJOIN BASENEXTJOIN : core.

Lemma rec_join (cs : Type) (ts : cs -> Tree)
  : rec (indexed_union cs ts) ≡ dunion dbase (djoin cs (fun i : cs => rec (ts i))).
Proof.
  simpl.
  change (djoin bool (j { i : cs & children (ts i) } (fun c => childnodes (ts (projT1 c)) (projT2 c))) ≡ dunion dbase (djoin cs (fun i : cs => rec (ts i)))); split.
  - eapply djoin_supremum; eauto.
    intros [ | ]; simpl; eauto. eapply djoin_supremum; eauto. intros [c i]; simpl.
    eapply dle_trans with (d2 := rec (ts c)); eauto.
    + eapply lt_rec. econs. exists i; eauto.
    + eapply dle_trans with (d2 := djoin _ (fun c => rec (ts c))); eauto.
      eapply djoin_upperbound with (ds := fun c => rec (ts c)); eauto.
  - change (dunion dbase (djoin cs (fun i : cs => rec (ts i)))  ⊑ rec (indexed_union cs ts)). eapply dunion_supremum; eauto.
    eapply djoin_supremum; eauto. intros c. eapply le_rec. econs. intros i. econs. simpl. exists (@existT _ _ c i); eauto.
Qed.

Lemma rec_is_join (o : Tree) (cs : Type) (ts : cs -> Tree)
  (JOIN : o =ᵣ indexed_union cs ts)
  : rec o ≡ dunion dbase (djoin cs (fun c : cs => rec (ts c))).
Proof.
  eapply deq_trans with (d2 := rec (indexed_union cs ts)); eauto.
  eapply rec_join.
Qed.

Lemma rec_join_inhabited (cs : Type) (ts : cs -> Tree)
  (INHABITED : inhabited cs)
  : rec (indexed_union cs ts) ≡ djoin cs (fun c : cs => rec (ts c)).
Proof.
  eapply deq_trans with (d2 := dunion dbase (djoin cs (fun i : cs => rec (ts i)))); eauto.
  - eapply rec_join with (cs := cs) (ts := ts).
  - split.
    + destruct INHABITED as [c]. eapply dunion_supremum; eauto.
      eapply dle_trans with (d2 := rec (ts c)); eauto.
      eapply djoin_supremum with (ds := fun c : cs => rec (ts c)); eauto.
    + eapply dunion_r; eauto.
Qed.

Lemma rec_is_join_inhabited (o : Tree) (cs : Type) (ts : cs -> Tree)
  (INHABITED : inhabited cs)
  (JOIN : o =ᵣ indexed_union cs ts)
  : rec o ≡ djoin cs (fun c : cs => rec (ts c)).
Proof.
  eapply deq_trans with (d2 := rec (indexed_union cs ts)); eauto.
  eapply rec_join_inhabited; eauto.
Qed.

#[local] Hint Resolve rec_is_join_inhabited : core.

Lemma rec_union o o'
  : rec (union o o') ≡ dunion (rec o) (rec o').
Proof.
  assert (INHABITED : inhabited bool).
  { constructor. exact true. }
  split.
  { eapply dle_trans with (d2 := djoin bool (fun b : bool => rec (if b then o else o'))); eauto.
    - eapply rec_join_inhabited; eauto.
    - eapply djoin_supremum; eauto. intros [ | ]; eauto.
  }
  { eapply dle_trans with (d2 := djoin bool (fun b : bool => rec (if b then o else o'))); eauto.
    - eapply djoin_supremum; eauto.
      + intros [ | ] [ | ]; simpl; eauto.
      + intros [ | ]; simpl; eauto.
      + intros [ | ].
        * eapply djoin_upperbound with (ds := fun b : bool => rec (if b then o else o')) (i := true); eauto.
        * eapply djoin_upperbound with (ds := fun b : bool => rec (if b then o else o')) (i := false); eauto.
    - eapply rec_join_inhabited; eauto.
  }
Qed.

Lemma rec_unique (f : Tree -> D)
  (ZERO : forall o : Tree, o =ᵣ empty -> f o ≡ dbase)
  (SUCC : forall o : Tree, forall alpha : Tree, o =ᵣ succ alpha -> f o ≡ dnext (f alpha))
  (LIM' : forall o : Tree, forall I : Type, forall alpha : I -> Tree, o =ᵣ indexed_union I alpha -> inhabited I -> (forall i1, exists i2, alpha i1 <ᵣ alpha i2) -> f o ≡ djoin I (fun i : I => f (alpha i)))
  (GOOD : forall o, good (f o))
  : forall o, f o ≡ rec o.
Proof.
  eapply transfinite_induction.
  - ii. eapply deq_trans with (d2 := dbase); eauto. eapply deq_sym. eapply rec_zero; eauto.
  - ii. eapply deq_trans with (d2 := dnext (f alpha)); eauto. eapply deq_sym. eapply deq_trans with (d2 := dnext (rec alpha)); eauto. eapply rec_succ; eauto.
  - ii. des.
    assert (CHAIN : forall i1, forall i2, dle (f (alpha i1)) (f (alpha i2)) \/ dle (f (alpha i2)) (f (alpha i1))).
    { ii. pose proof (rec_chain (alpha i1) (alpha i2)) as [LE | LE].
      - left. eapply dle_trans with (d2 := rec (alpha i1)). 1,2,3: eauto. eapply H0. eapply dle_trans with (d2 := rec (alpha i2)). 1,2,3: eauto. exact LE. eapply H0.
      - right. eapply dle_trans with (d2 := rec (alpha i2)). 1,2,3: eauto. eapply H0. eapply dle_trans with (d2 := rec (alpha i1)). 1,2,3: eauto. exact LE. eapply H0.
    }
    eapply deq_sym. eapply deq_trans with (d2 := djoin I (fun i => f (alpha i))); eauto.
    + eapply deq_trans with (d2 := djoin I (fun i => rec (alpha i))); eauto. split; eapply djoin_supremum. 1,2,3,5,6,7: eauto.
      * i. eapply dle_trans with (d2 := f (alpha i)). 1,2,3: eauto. eapply H0. eapply djoin_upperbound with (ds := fun i => f (alpha i)); eauto.
      * i. eapply dle_trans with (d2 := rec (alpha i)). 1,2,3: eauto. eapply H0. eapply djoin_upperbound with (ds := fun i => rec (alpha i)); eauto.
Qed.

Lemma rec_unique2 (f : Tree -> D)
  (FIX : forall cs : Type, forall ts : cs -> Tree, f (mkNode cs ts) ≡ dunion dbase (djoin cs (fun c : cs => dnext (f (ts c)))))
  (GOOD : forall o : Tree, good (f o))
  : forall t : Tree, f t ≡ rec t.
Proof.
  induction t as [cs ts IH]; simpl.
  assert (NEXTLE : forall c1 : cs, forall c2 : cs, ts c1 ≦ᵣ ts c2 -> dnext (f (ts c1)) ⊑ dnext (f (ts c2))).
  { ii. eapply dle_trans with (d2 := dnext (rec (ts c1))); eauto.
    - eapply dnext_congruence; eauto.
    - eapply dle_trans with (d2 := dnext (rec (ts c2))); eauto. eapply dnext_congruence; eauto.
  }
  assert (NEXTCHAIN : forall c1 : cs, forall c2 : cs, dnext (f (ts c1)) ⊑ dnext (f (ts c2)) \/ dnext (f (ts c2)) ⊑ dnext (f (ts c1))).
  { ii. pose proof (rLe_total (ts c1) (ts c2)) as [? | ?]; eauto. }
  assert (BASE : dbase ⊑ djoin cs (fun c => dnext (f (ts c))) \/ djoin cs (fun c => dnext (f (ts c))) ⊑ dbase).
  { ii. destruct (classic (inhabited cs)) as [YES | NO]; [left | right].
    - destruct YES as [c]. eapply dle_trans with (d2 := f (ts c)); eauto.
      + eapply dle_trans with (d2 := rec (ts c)); eauto. eapply IH.
      + eapply dle_trans with (d2 := dnext (f (ts c))); eauto. eapply djoin_upperbound with (ds := fun c => dnext (f (ts c))); eauto.
    - eapply djoin_supremum; eauto. intros c. contradiction NO. econs. exact c.
  }
  assert (H1_good : good (dunion dbase (djoin cs (fun c => dnext (f (ts c)))))).
  { eapply dunion_good; eauto. }
  assert (H2_good : good (dunion dbase (djoin cs (fun c => dnext (rec (ts c)))))).
  { eapply djoin_good; [eapply j_chain | eapply good_j]. }
  split.
  - eapply dle_trans with (d2 := dunion dbase (djoin cs (fun c => dnext (f (ts c))))). 1,2,3: eauto.
    + eapply FIX.
    + eapply djoin_supremum; eauto.
      * intros [ | ] [ | ]; simpl; eauto. destruct BASE; eauto.
      * intros [ | ]; eauto.
      * intros [ | ]; eauto. eapply dle_trans with (d2 := djoin cs (fun c => dnext (rec (ts c)))); eauto.
        eapply djoin_supremum; eauto. intros i. eapply dle_trans with (d2 := dnext (rec (ts i))). 1,2,3: eauto.
        { eapply dnext_congruence; eauto. }
        { eapply djoin_upperbound with (ds := fun c => dnext (rec (ts c))); eauto. }
  - eapply dle_trans with (d2 := dunion dbase (djoin cs (fun c => dnext (f (ts c))))). 1,2,3: eauto.
    + eapply dunion_supremum; eauto. eapply dle_trans with (d2 := djoin cs (fun c => dnext (f (ts c)))). 1,2,3: eauto.
      * eapply djoin_supremum; eauto. intros i. eapply dle_trans with (d2 := dnext (f (ts i))). 1,2,3: eauto.
        { eapply dnext_congruence; eauto. }
        { eapply djoin_upperbound with (ds := fun c => dnext (f (ts c))); eauto. }
      * eapply dunion_r; eauto.
    + eapply FIX.
Qed.

Lemma rec_good (o : Tree)
  : good (rec o).
Proof.
  eapply good_rec; eauto.
Qed.

Lemma rec_next_good (o : Tree)
  : good (dnext (rec o)).
Proof.
  eapply dnext_good. eapply rec_good; eauto.
Qed.

Inductive strictly_increasing : D -> D -> Prop :=
  | strictly_increasing_intro (alpha : Tree) (beta : Tree)
    (LT : alpha <ᵣ beta)
    (INCR : ~ rec beta ⊑ rec alpha)
    : strictly_increasing (rec alpha) (rec beta).

Lemma strictly_increasing_well_founded
  : well_founded strictly_increasing.
Proof.
  assert (claim1 : forall o : Tree, Acc strictly_increasing (rec o)).
  { intros o. pose proof (rLt_wf o) as H_Acc. induction H_Acc as [o _ IH].
    econs. intros o' H. inv H. eapply IH.
    pose proof (rLe_or_rGt o alpha) as [LE | GT].
    - contradiction INCR. rewrite H2. eapply le_rec. exact LE.
    - exact GT.
  }
  intros d. econs. intros d' H. inv H. eapply claim1.
Qed.

Definition not_fixed (beta : Tree) : Prop :=
  forall alpha : Tree, forall LT : alpha <ᵣ beta, ~ rec beta ⊑ rec alpha.

Lemma fixed_point_after (alpha : Tree) (beta : Tree)
  (FIX : dnext (rec alpha) ⊑ rec alpha)
  (LE : alpha ≦ᵣ beta)
  : rec beta ⊑ rec alpha.
Proof.
  revert alpha FIX LE. induction beta using @transfinite_induction; ii.
  - eapply le_rec; eauto. rewrite ZERO. econs. intros [].
  - assert (dnext (rec alpha) ≡ rec alpha) as claim1.
    { split; eauto. }
    eapply rLe_iff_rLt_or_rEq in LE. destruct LE as [LT | EQ].
    + unnw. eapply dle_trans with (d2 := dnext (rec beta2)). 1,2,3: eauto.
      * eapply rec_succ; eauto.
      * eapply dle_trans with (d2 := dnext (rec alpha)); eauto. eapply dnext_congruence; eauto. rewrite rEq_succ_iff in SUCC. rewrite -> SUCC in LT. split; eauto.
    + eapply le_rec; eauto. eapply EQ.
  - hexploit rec_is_join_inhabited; try eassumption. i; des. rename I into cs, alpha into ts, alpha0 into alpha.
    assert (claim1 : forall c1 : cs, forall c2 : cs, rec (ts c1) ⊑ rec (ts c2) \/ rec (ts c2) ⊑ rec (ts c1)).
    { ii. pose proof (rLe_total (ts c1) (ts c2)) as [H_LE | H_LE]; [left | right]; eapply le_rec; eauto. }
    eapply dle_trans with (d2 := djoin cs (fun c => rec (ts c))). 1,2,3: eauto.
    + eapply H2.
    + eapply djoin_supremum; eauto. intros i. pose proof (rLe_or_rGt (ts i) alpha) as [H_LE | H_GT]; eauto. eapply H0; eauto. eapply rLt_implies_rLe; eauto.
Qed.

Lemma end_le_end (o : Tree) (o' : Tree)
  (LE : o ≦ᵣ o')
  (NOT_END : not_fixed o')
  : not_fixed o.
Proof.
  ii. eapply NOT_END with (alpha := alpha).
  - eapply rLt_rLe_rLt; eauto.
  - assert (claim1 : succ alpha ≦ᵣ o).
    { econs. simpl. intros [[ | ] c]; simpl.
      - transitivity alpha; eauto. destruct alpha; eauto.
      - destruct c; eauto.
    }
    eapply fixed_point_after with (alpha := alpha).
    + eapply dle_trans with (d2 := rec (succ alpha)); eauto.
      eapply rec_succ. reflexivity.
    + transitivity o; eauto. eapply rLt_implies_rLe; eauto.
Qed.

Lemma least_lt_incr_acc (o : Tree)
  (INCR : not_fixed o)
  : o ≦ᵣ @fromWf D strictly_increasing strictly_increasing_well_founded (rec o).
Proof.
  pose proof (rLt_wf o) as H_Acc. induction H_Acc as [o _ IH].
  pose proof (rLe_or_rGt o (@fromWf D strictly_increasing strictly_increasing_well_founded (rec o))) as [H_LE | H_GT]; eauto.
  destruct o; simpl. econs. simpl. intros c.
  assert (claim1 : not_fixed (ts c)).
  { eapply end_le_end with (o' := mkNode cs ts); eauto. eapply rLt_implies_rLe; eauto. }
  pose proof (IH (ts c) (trivial_rLt cs ts c) claim1) as claim2. eapply rLe_rLt_rLt; eauto.
  assert (strictly_increasing (rec (ts c)) (rec (mkNode cs ts))) as claim3.
  { econs; eauto. }
  econs. eapply member_implies_rLt. unfold fromWf. eapply fromAcc_member_fromAcc_intro. exact claim3.
Qed.

Lemma hartogs_fixed
  : ~ not_fixed (Hartogs D).
Proof.
  intros H_contra. apply least_lt_incr_acc in H_contra; eauto.
  eapply rLt_iff_not_rGe. 2: exact H_contra. eapply rLe_rLt_rLt with (y := @fromWfSet D strictly_increasing strictly_increasing_well_founded).
  - eapply rLt_implies_rLe. econs. unfold fromWfSet. exists (rec (Hartogs D)). reflexivity.
  - econs. simpl. exists (@B.exist strictly_increasing strictly_increasing_well_founded). reflexivity.
Qed.

Theorem _fixpoint_theorem_1
  : dnext (rec (Hartogs D)) ≡ rec (Hartogs D).
Proof.
  split.
  - eapply NNPP. intros H_contra. eapply hartogs_fixed. eapply end_le_end with (o' := succ (Hartogs D)).
    { eapply rLt_implies_rLe. econs. simpl. exists (@existT _ _ false true). simpl. reflexivity. }
    intros o H_rLt H_dle. eapply H_contra. eapply dle_trans with (d2 := rec (succ (Hartogs D))). 1,2,3: eauto.
    + eapply rec_succ. reflexivity.
    + pose proof (rLe_or_rGt o (Hartogs D)) as [H_rLe | H_rGt].
      * eapply dle_trans with (d2 := rec o); eauto.
      * exfalso. eapply rLt_iff_not_rGe; [exact H_rLt | ].
        assert (claim1 : succ (Hartogs D) =ᵣ succ (Hartogs D)) by reflexivity.
        rewrite rEq_succ_iff in claim1. eapply succ_rLe_intro; eauto.
  - eapply dnext_extensive; eauto.
Qed.

End _REC1.

End THEORY_ON_RANK.

End InducedOrdinal.

Definition toSet_wlt (t : Tree) (lhs : toSet t) (rhs : toSet t) : Prop :=
  fromWf (projT2 (toWoSet t)) (toWoSet_well_founded t) lhs <ᵣ fromWf (projT2 (toWoSet t)) (toWoSet_well_founded t) rhs.

#[global] Arguments toSet_wlt t / lhs rhs.

Section ClassicalWoset.

#[local] Infix "\in" := member : type_scope.

Lemma toSet_wlt_Transitive t
  : Transitive (toSet_wlt t).
Proof.
  red. i. eapply (rLt_StrictOrder).(StrictOrder_Transitive); eauto.
Qed.

Lemma toSet_wlt_well_founded t
  : well_founded (toSet_wlt t).
Proof.
  eapply relation_on_image_liftsWellFounded. eapply rLt_wf.
Qed.

#[global]
Instance toSet_isWellPoset (t : Tree) : isWellPoset (toSet t) :=
  { wltProp := toSet_wlt t
  ; wltProp_Transitive := toSet_wlt_Transitive t
  ; wltProp_well_founded := toSet_wlt_well_founded t
  }.

#[global]
Instance toSet_wlt_eqPropCompatible2 t
  : eqPropCompatible2 (toSet_wlt t).
Proof.
  red. ii; simpl in *. unfold toSet_wlt. rewrite x_EQ. rewrite y_EQ. reflexivity.
Qed.

Lemma toSet_wlt_extensional {t : Tree} (x : toSet t) (y : toSet t)
  (EXT_EQ : forall z : toSet t, wltProp z x <-> wltProp z y)
  : x == y.
Proof.
  simpl in *. eapply rEq_ext. intros z. split; intros H_rLt.
  - rewrite <- @fromWf_toWoset_rEq with (t := z) in H_rLt; cycle 1.
    { ii; eapply projT2_eq; eauto. }
    rewrite <- @fromWf_toWoset_rEq with (t := z); cycle 1.
    { ii; eapply projT2_eq; eauto. }
    unfold fromWfSet in *. eapply rLt_rLe_rLt; eauto. clear z H_rLt.
    unfold fromWf in *. destruct (toWoSet_well_founded t x) as [H_ACC_inv], (toWoSet_well_founded t y) as [H_ACC_inv']. unfold toSet in *.
    econs. intros [cz z]. simpl in *. rewrite fromAcc_pirrel with (ACC' := toWoSet_well_founded t cz). rewrite <- EXT_EQ with (z := cz).
    econs. simpl. exists (@exist _ _ cz z). simpl. rewrite fromAcc_pirrel. reflexivity.
  - rewrite <- @fromWf_toWoset_rEq with (t := z) in H_rLt; cycle 1.
    { ii; eapply projT2_eq; eauto. }
    rewrite <- @fromWf_toWoset_rEq with (t := z); cycle 1.
    { ii; eapply projT2_eq; eauto. }
    unfold fromWfSet in *. eapply rLt_rLe_rLt; eauto. clear z H_rLt.
    unfold fromWf in *. destruct (toWoSet_well_founded t x) as [H_ACC_inv], (toWoSet_well_founded t y) as [H_ACC_inv']. unfold toSet in *.
    econs. intros [cz z]. simpl in *. rewrite fromAcc_pirrel with (ACC' := toWoSet_well_founded t cz). rewrite -> EXT_EQ with (z := cz).
    econs. simpl. exists (@exist _ _ cz z). simpl. rewrite fromAcc_pirrel. reflexivity.
Qed.

#[global]
Instance toSet_isWoset (t : Tree) : isWoset (toSet t) :=
  { Woset_isWellPoset := toSet_isWellPoset t
  ; Woset_eqPropCompatible2 := toSet_wlt_eqPropCompatible2 t
  ; Woset_ext_eq := toSet_wlt_extensional (t := t)
  }.

Corollary toSet_wlt_trichotomous (t : Tree)
  : forall x : toSet t, forall y : toSet t, x == y \/ (x ≺ y \/ y ≺ x).
Proof.
  eapply @O.wlt_trichotomous. exact classic.
Qed.

End ClassicalWoset.

Module __wellorderingtheorem1 <: LEM_ModuleAttribute <: AC_ModuleAttribute.

Variant good {X : Type} {SETOID : isSetoid X} (P : X -> Prop) (R : X -> X -> Prop) : Prop :=
  | good_intro
    (SOUND : forall a : X, forall b : X, forall LT : R a b, P a /\ P b)
    (COMPLETE : forall a : X, forall b : X, forall IN : P a, forall IN' : P b, a == b \/ (R a b \/ R b a))
    (WELL_FOUNDED : well_founded R)
    : good P R.

Section WELL_ORDERING_THEOREM.

Context {X : Type}.

#[projections(primitive)]
Record pair : Type :=
  { P (x : X) : Prop
  ; R (x : X) (y : X) : Prop
  } as s.

Variant pair_le (s : pair) (s' : pair) : Prop :=
  | pair_le_intro
    (P_incl : forall a : X, forall IN : s.(P) a, s'.(P) a)
    (R_incl : forall a : X, forall b : X, forall LT : s.(R) a b, s'.(R) a b)
    (NO_INSERTION : forall a : X, forall b : X, forall IN' : s.(P) b, s'.(R) a b <-> s.(R) a b)
    : pair_le s s'.

#[global]
Instance pair_le_Reflexive 
  : Reflexive pair_le.
Proof.
  intros s0. econs; eauto.
Qed.

#[global]
Instance pair_le_Transitive
  : Transitive pair_le.
Proof.
  intros s0 s1 s2 [? ? ?] [? ? ?]. simpl in *.
  econs; simpl in *; eauto; i. rewrite <- NO_INSERTION; eauto.
Qed.

#[global]
Instance pair_le_PreOrder : PreOrder pair_le :=
  { PreOrder_Reflexive := pair_le_Reflexive
  ; PreOrder_Transitive := pair_le_Transitive
  }.

Let pair_isSetoid : isSetoid pair :=
  mkSetoidFromPreOrder pair_le_PreOrder.

#[local] Existing Instance pair_isSetoid.

#[local]
Instance pair_isProset : isProset pair :=
  { leProp := pair_le
  ; Proset_isSetoid := pair_isSetoid
  ; leProp_PreOrder := pair_le_PreOrder
  ; leProp_PartialOrder := mkSetoidFromPreOrder_good pair_le_PreOrder
  }.

Definition pair_sup (I : Type) (chain : I -> pair) : pair :=
  {| P (x : X) := exists i : I, (chain i).(P) x; R (x : X) (y : X) := exists i : I, (chain i).(R) x y; |}.

Lemma pair_sup_isSupremum (I : Type) (chain : I -> pair)
  (H_chain : forall i1 : I, forall i2 : I, chain i1 =< chain i2 \/ chain i2 =< chain i1)
  : is_supremum_of (pair_sup I chain) (fun s : pair => exists i : I, s = chain i).
Proof.
  intros u; split.
  - intros [? ? ?]. intros x x_in. destruct x_in as [i ->]. econs; i.
    + eapply P_incl. simpl. exists i; eauto.
    + eapply R_incl. simpl. exists i; eauto.
    + rewrite -> NO_INSERTION; simpl; eauto. split.
      * intros [i' H_R]. pose proof (H_chain i i') as [[? ? ?] | [? ? ?]]; eauto. rewrite <- NO_INSERTION0; eauto.
      * intros H_R. exists i. eauto.
  - intros u_in. do 2 red in u_in. econs; simpl; i; des.
    + hexploit (u_in (chain i)).
      { exists i. reflexivity. }
      intros [? ? ?]; eauto.
    + hexploit (u_in (chain i)).
      { exists i. reflexivity. }
      intros [? ? ?]; eauto.
    + hexploit (u_in (chain i)).
      { exists i. reflexivity. }
      intros [? ? ?]. rewrite -> NO_INSERTION; eauto. split.
      * intros H_R. exists i. eauto.
      * intros [i' H_R]. pose proof (H_chain i i') as [[? ? ?] | [? ? ?]]; eauto. rewrite <- NO_INSERTION0; eauto.
Qed.

Context {SETOID : isSetoid X}.

#[local] Notation good s := (__wellorderingtheorem1.good (X := X) (SETOID := SETOID) s.(P) s.(R)).

Lemma pair_sup_good (I : Type) (chain : I -> pair)
  (H_chain : forall i1 : I, forall i2 : I, chain i1 =< chain i2 \/ chain i2 =< chain i1)
  (chain_good : forall i : I, good (chain i))
  : good (pair_sup I chain).
Proof.
  split.
  - intros a b [i H_R]. pose proof (chain_good i) as [? ? ?]. pose proof (SOUND a b H_R). split; exists i; tauto.
  - intros a b [i1 H_P1] [i2 H_P2]. pose proof (H_chain i1 i2) as [[? ? ?] | [? ? ?]].
    + pose proof (chain_good i2) as [? ? ?]. hexploit (COMPLETE _ _ (P_incl _ H_P1) H_P2); eauto.
      intros [? | [? | ?]]; [left; tauto | right | right]; [left | right]; exists i2; tauto.
    + pose proof (chain_good i1) as [? ? ?]. hexploit (COMPLETE _ _ H_P1 (P_incl _ H_P2)); eauto.
      intros [? | [? | ?]]; [left; tauto | right | right]; [left | right]; exists i1; tauto.
  - intros x1. econs. intros x0 [i H_R]. pose proof (chain_good i) as [? ? ?].
    assert (H_Acc : Acc (chain i).(R) x0) by eauto.
    pose proof (SOUND _ _ H_R) as [H_P _]. clear H_R. induction H_Acc as [x0 _ IH]; intros; econs; intros y [i' H_R'].
    assert (LT : (chain i).(R) y x0).
    { pose proof (H_chain i i') as [[? ? ?] | [? ? ?]]; eauto. rewrite <- NO_INSERTION; eauto. }
    eapply IH; eauto. pose proof (SOUND _ _ LT) as [? ?]; tauto.
Qed.

Section NEXT.

Variable next : pair -> pair.

Hypothesis next_extensive : forall s : pair, s =< next s.

Hypothesis next_good : forall s : pair, good s -> good (next s).

Hypothesis next_exhausted : forall s : pair, (forall x : X, s.(P) x) \/ (exists x : X, (next s).(P) x /\ ~ s.(P) x).

End NEXT.

End WELL_ORDERING_THEOREM.

#[global] Arguments __wellorderingtheorem1.pair : clear implicits.

End __wellorderingtheorem1. 
