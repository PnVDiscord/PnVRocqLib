Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.ThN.
Require Import PnV.Math.BooleanAlgebra.

#[local] Infix " \in " := E.In.
#[local] Infix " \subseteq " := E.subset.
#[local] Notation In := List.In.

#[local] Hint Resolve E.insert_monotonic : core.

Section PROPOSITONAL_LOGIC.

Definition propLetter : Set := nat.

Inductive formula : Set :=
  | AtomF (i : propLetter) : formula
  | ContradictionF : formula
  | NegationF (p1 : formula) : formula
  | ConjunctionF (p1 : formula) (p2 : formula) : formula
  | DisjunctionF (p1 : formula) (p2 : formula) : formula
  | ImplicationF (p1 : formula) (p2 : formula) : formula
  | BiconditionalF (p1 : formula) (p2 : formula) : formula.

#[global]
Instance propLetter_hasEqDec : hasEqDec propLetter :=
  Nat.eq_dec.

#[global]
Instance formula_hasEqDec
  : hasEqDec formula.
Proof.
  red. decide equality. eapply propLetter_hasEqDec.
Defined.

Fixpoint evalFormula (env : propLetter -> Prop) (p : formula) {struct p} : Prop :=
  match p with
  | AtomF i => env i
  | ContradictionF => False
  | NegationF p1 => ~ evalFormula env p1
  | ConjunctionF p1 p2 => evalFormula env p1 /\ evalFormula env p2
  | DisjunctionF p1 p2 => evalFormula env p1 \/ evalFormula env p2
  | ImplicationF p1 p2 => evalFormula env p1 -> evalFormula env p2
  | BiconditionalF p1 p2 => evalFormula env p1 <-> evalFormula env p2
  end.

Definition entails (Gamma : ensemble formula) (C : formula) : Prop :=
  forall e : propLetter -> Prop, (forall H : formula, H \in Gamma -> evalFormula e H) -> evalFormula e C.

Infix "⊨" := entails : type_scope.

#[local] Hint Unfold entails : core.

Inductive infers (Gamma : ensemble formula) : forall C : formula, Prop :=
  | ByAssumption C
    (IN : C \in Gamma)
    : Gamma ⊢ C
  | ContradictionI A
    (INFERS1 : Gamma ⊢ A)
    (INFERS2 : Gamma ⊢ NegationF A)
    : Gamma ⊢ ContradictionF
  | ContradictionE A
    (INFERS1 : Gamma ⊢ ContradictionF)
    : Gamma ⊢ A
  | NegationI A
    (INFERS1 : E.insert A Gamma ⊢ ContradictionF)
    : Gamma ⊢ NegationF A
  | NegationE A
    (INFERS1 : E.insert (NegationF A) Gamma ⊢ ContradictionF)
    : Gamma ⊢ A
  | ConjunctionI A B
    (INFERS1 : Gamma ⊢ A)
    (INFERS2 : Gamma ⊢ B)
    : Gamma ⊢ ConjunctionF A B
  | ConjunctionE1 A B
    (INFERS1 : Gamma ⊢ ConjunctionF A B)
    : Gamma ⊢ A
  | ConjunctionE2 A B
    (INFERS1 : Gamma ⊢ ConjunctionF A B)
    : Gamma ⊢ B
  | DisjunctionI1 A B
    (INFERS1 : Gamma ⊢ A)
    : Gamma ⊢ DisjunctionF A B
  | DisjunctionI2 A B
    (INFERS1 : Gamma ⊢ B)
    : Gamma ⊢ DisjunctionF A B
  | DisjunctionE A B C
    (INFERS1 : Gamma ⊢ DisjunctionF A B)
    (INFERS2 : E.insert A Gamma ⊢ C)
    (INFERS3 : E.insert B Gamma ⊢ C)
    : Gamma ⊢ C
  | ImplicationI A B
    (INFERS1 : E.insert A Gamma ⊢ B)
    : Gamma ⊢ ImplicationF A B
  | ImplicationE A B
    (INFERS1 : Gamma ⊢ ImplicationF A B)
    (INFERS2 : Gamma ⊢ A)
    : Gamma ⊢ B
  | BiconditionalI A B
    (INFERS1 : E.insert A Gamma ⊢ B)
    (INFERS2 : E.insert B Gamma ⊢ A)
    : Gamma ⊢ BiconditionalF A B
  | BiconditionalE1 A B
    (INFERS1 : Gamma ⊢ BiconditionalF A B)
    (INFERS2 : Gamma ⊢ A)
    : Gamma ⊢ B
  | BiconditionalE2 A B
    (INFERS1 : Gamma ⊢ BiconditionalF A B)
    (INFERS2 : Gamma ⊢ B)
    : Gamma ⊢ A
  where " Gamma ⊢ C " := (infers Gamma C) : type_scope.

#[local] Hint Constructors infers : core.

Lemma extend_entails Gamma Gamma' C
  (ENTAILS: Gamma ⊨ C)
  (SUBSET: Gamma \subseteq Gamma')
  : Gamma' ⊨ C.
Proof.
  ii. eapply ENTAILS. eauto.
Qed.

Definition is_structure (Gamma : ensemble formula) : Prop :=
  forall p : formula, p \in Gamma <-> evalFormula (E.preimage AtomF Gamma) p.

Lemma structure_gives_its_subset_to_model (Gamma : ensemble formula) (Gamma' : ensemble formula)
  (IS_STRUCTURE : is_structure Gamma')
  (INCL : Gamma \subseteq Gamma')
  : forall p, p \in Gamma -> evalFormula (E.preimage AtomF Gamma') p.
Proof.
  ii. eapply IS_STRUCTURE. eauto with *.
Qed.

Lemma Law_of_Excluded_Middle A
  : E.empty ⊢ DisjunctionF A (NegationF A).
Proof with repeat ((now left) || right).
  eapply NegationE, ContradictionI.
  - eapply DisjunctionI2, NegationI, ContradictionI.
    + eapply DisjunctionI1, ByAssumption...
    + eapply ByAssumption...
  - eapply ByAssumption...
Qed.

Lemma Cut_property Gamma A B
  (INFERS : Gamma ⊢ A)
  (IMPLY : E.insert A Gamma ⊢ B)
  : Gamma ⊢ B.
Proof.
  assert (claim : Gamma ⊢ ImplicationF A B).
  { eapply ImplicationI; exact IMPLY. }
  eapply ImplicationE; [exact claim | exact INFERS].
Qed.

Lemma extend_infers Gamma Gamma' C
  (INFERS : Gamma ⊢ C)
  (SUBSET : Gamma \subseteq Gamma')
  : Gamma' ⊢ C.
Proof with eauto.
  revert Gamma' SUBSET. induction INFERS; ii.
  - eapply ByAssumption with (C := C)...
  - eapply ContradictionI with (A := A)...
  - eapply ContradictionE with (A := A)...
  - eapply NegationI with (A := A)...
  - eapply NegationE with (A := A)...
  - eapply ConjunctionI with (A := A) (B := B)...
  - eapply ConjunctionE1 with (A := A) (B := B)...
  - eapply ConjunctionE2 with (A := A) (B := B)...
  - eapply DisjunctionI1 with (A := A) (B := B)...
  - eapply DisjunctionI2 with (A := A) (B := B)...
  - eapply DisjunctionE with (A := A) (B := B) (C := C)...
  - eapply ImplicationI with (A := A) (B := B)...
  - eapply ImplicationE with (A := A) (B := B)...
  - eapply BiconditionalI with (A := A) (B := B)...
  - eapply BiconditionalE1 with (A := A) (B := B)...
  - eapply BiconditionalE2 with (A := A) (B := B)...
Qed.

Lemma Deduction_thm (Gamma : ensemble formula) (H : formula) (C : formula)
  : Gamma ⊢ ImplicationF H C <-> E.insert H Gamma ⊢ C.
Proof.
  split; intros INFERS.
  - eapply ImplicationE with (A := H).
    + enough (INFERS' : E.insert H Gamma ⊢ H).
      { eapply extend_infers with (Gamma := Gamma); done!. }
      eapply ByAssumption; done!.
    + eapply ByAssumption; done!.
  - eapply ImplicationI. exact INFERS.
Qed.

Fixpoint depth (p : formula) {struct p} : nat :=
  match p with
  | AtomF i => 0
  | ContradictionF => 1
  | NegationF p1 => S (depth p1)
  | ConjunctionF p1 p2 => S (max (depth p1) (depth p2))
  | DisjunctionF p1 p2 => S (max (depth p1) (depth p2))
  | ImplicationF p1 p2 => S (max (depth p1) (depth p2))
  | BiconditionalF p1 p2 => S (max (depth p1) (depth p2))
  end.

#[local] Notation plus6 i := (S (S (S (S (S (S i)))))).

Fixpoint enumFormula' (rk : nat) (seed0 : nat) {struct rk} : formula :=
  match rk with
  | O => AtomF seed0
  | S rk' =>
    let seed1 := fst (cp seed0) in
    let piece := snd (cp seed0) in
    let seed2 := fst (cp seed1) in
    let seed3 := snd (cp seed1) in
    match piece with
    | 0 => ContradictionF
    | 1 => NegationF (enumFormula' rk' seed1)
    | 2 => ConjunctionF (enumFormula' rk' seed2) (enumFormula' rk' seed3)
    | 3 => DisjunctionF (enumFormula' rk' seed2) (enumFormula' rk' seed3)
    | 4 => ImplicationF (enumFormula' rk' seed2) (enumFormula' rk' seed3)
    | 5 => BiconditionalF (enumFormula' rk' seed2) (enumFormula' rk' seed3)
    | plus6 i => AtomF i
    end
  end.

#[local]
Tactic Notation "tac_aux1" :=
  match goal with
  | [ H : cp ?seed = ?rhs |- _ ] => rewrite H; simpl
  end.

#[local]
Tactic Notation "tac_aux2" :=
  match goal with
  | [ H : enumFormula' ?rk ?seed = ?p |- _ ] => rewrite <- H
  end.

#[local]
Tactic Notation "tac" :=
  unfold enumFormula'; repeat tac_aux1; repeat tac_aux2; eauto.

Lemma ideaOf_enumFormula' (p : formula) (rk : nat)
  (RANK_LE : depth p <= rk)
  : { seed0 : nat | enumFormula' rk seed0 = p }.
Proof with tac.
  revert p rk RANK_LE.
  pose proof (claim1 := fun x: nat => fun y: nat => fun z: nat => proj2 (cp_spec x y z)).
  induction p as [i | | p1 IH1 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2]; simpl.
  { intros [ | r'] H.
    - exists (i)...
    - assert (H0: cp (sum_from_0_to (0 + plus6 i) + plus6 i) = (0, plus6 i)) by now apply claim1.
      exists (sum_from_0_to (0 + plus6 i) + plus6 i)...
  }
  all: intros r H; set (rk := pred r); (assert (H0: S rk = r) by lia); rewrite <- H0.
  { set (piece := 0).
    exists (piece)...
  }
  { set (piece := 1).
    assert (H1: depth p1 <= rk) by lia.
    pose proof (IH1 rk H1) as [seed2 H2].
    assert (H3: cp (sum_from_0_to (seed2 + piece) + piece) = (seed2, piece)) by now apply claim1.
    exists (sum_from_0_to (seed2 + piece) + piece)...
  }
  { set (piece := 2).
    assert (H1: max (depth p1) (depth p2) <= rk) by lia.
    assert (H2: depth p1 <= rk) by lia.
    assert (H3: depth p2 <= rk) by lia.
    pose proof (IH1 rk H2) as [seed2 H4].
    pose proof (IH2 rk H3) as [seed3 H5].
    assert (H6: cp (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
    assert (H7: cp (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
    exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
  }
  { set (piece := 3).
    assert (H1: max (depth p1) (depth p2) <= rk) by lia.
    assert (H2: depth p1 <= rk) by lia.
    assert (H3: depth p2 <= rk) by lia.
    pose proof (IH1 rk H2) as [seed2 H4].
    pose proof (IH2 rk H3) as [seed3 H5].
    assert (H6: cp (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
    assert (H7: cp (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
    exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
  }
  { set (piece := 4).
    assert (H1: max (depth p1) (depth p2) <= rk) by lia.
    assert (H2: depth p1 <= rk) by lia.
    assert (H3: depth p2 <= rk) by lia.
    pose proof (IH1 rk H2) as [seed2 H4].
    pose proof (IH2 rk H3) as [seed3 H5].
    assert (H6: cp (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
    assert (H7: cp (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
    exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
  }
  { set (piece := 5).
    assert (H1: max (depth p1) (depth p2) <= rk) by lia.
    assert (H2: depth p1 <= rk) by lia.
    assert (H3: depth p2 <= rk) by lia.
    pose proof (IH1 rk H2) as [seed2 H4].
    pose proof (IH2 rk H3) as [seed3 H5].
    assert (H6: cp (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece) = (sum_from_0_to (seed2 + seed3) + seed3, piece)) by now apply claim1.
    assert (H7: cp (sum_from_0_to (seed2 + seed3) + seed3) = (seed2, seed3)) by now apply claim1.
    exists (sum_from_0_to ((sum_from_0_to (seed2 + seed3) + seed3) + piece) + piece)...
  }
Qed.

Definition enumFormula (seed : nat) : formula :=
  let rk := fst (cp seed) in
  let seed0 := snd (cp seed) in
  enumFormula' rk seed0.

Theorem enumFormula_good (p : formula)
  : { seed : nat | enumFormula seed = p }.
Proof.
  epose proof (ideaOf_enumFormula' p (depth p) _) as [seed0 H_EQ].
  exists (cpInv (depth p) seed0). unfold cp, enumFormula.
  now repeat rewrite -> cpInv_rightInv.
Unshelve.
  reflexivity.
Qed.

#[global]
Instance formula_isEnumerable : isEnumerable formula :=
  { enum := enumFormula
  ; enum_spec := enumFormula_good
  }.

End PROPOSITONAL_LOGIC.

#[local] Hint Unfold entails : core.
#[local] Hint Constructors infers : core.

Module PropositialLogicNotations.

Infix "⊢" := infers : type_scope.
Infix "⊨" := entails : type_scope.

End PropositialLogicNotations.

Import PropositialLogicNotations.

Section WEAK_COMPLETENESS.

Definition ContradictionF_bool : bool :=
  false.

Definition NegationF_bool (b1 : bool) : bool :=
  match b1 with
  | true => false
  | false => true
  end.

Definition ConjunctionF_bool (b1 : bool) (b2 : bool) : bool :=
  match b1, b2 with
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => false
  end.

Definition DisjunctionF_bool (b1 : bool) (b2 : bool) : bool :=
  match b1, b2 with
  | true, true => true
  | true, false => true
  | false, true => true
  | false, false => false
  end.

Definition ImplicationF_bool (b1 : bool) (b2 : bool) : bool :=
  match b1, b2 with
  | true, true => true
  | true, false => false
  | false, true => true
  | false, false => true
  end.

Definition BiconditionalF_bool (b1 : bool) (b2 : bool) : bool :=
  match b1, b2 with
  | true, true => true
  | true, false => false
  | false, true => false
  | false, false => true
  end.

Fixpoint eval_bool (env : propLetter -> bool) (p : formula) {struct p} : bool :=
  match p with
  | AtomF i => env i
  | ContradictionF => ContradictionF_bool
  | NegationF p1 => NegationF_bool (eval_bool env p1)
  | ConjunctionF p1 p2 => ConjunctionF_bool (eval_bool env p1) (eval_bool env p2)
  | DisjunctionF p1 p2 => DisjunctionF_bool (eval_bool env p1) (eval_bool env p2)
  | ImplicationF p1 p2 => ImplicationF_bool (eval_bool env p1) (eval_bool env p2)
  | BiconditionalF p1 p2 => BiconditionalF_bool (eval_bool env p1) (eval_bool env p2)
  end.

Lemma eval_bool_true_iff (e : propLetter -> bool) (p : formula)
  : eval_bool e p = true <-> evalFormula (fun i => if e i then True else False) p.
Proof.
  revert e. induction p as [i | | p1 IH1 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2]; simpl; ii.
  - destruct (e i) as [ | ]; done!.
  - done!.
  - specialize IH1 with (e := e). destruct (eval_bool e p1) as [ | ]; done!.
  - specialize IH1 with (e := e). specialize IH2 with (e := e). destruct (eval_bool e p1) as [ | ], (eval_bool e p2) as [ | ]; done!.
  - specialize IH1 with (e := e). specialize IH2 with (e := e). destruct (eval_bool e p1) as [ | ], (eval_bool e p2) as [ | ]; done!.
  - specialize IH1 with (e := e). specialize IH2 with (e := e). destruct (eval_bool e p1) as [ | ], (eval_bool e p2) as [ | ]; done!.
  - specialize IH1 with (e := e). specialize IH2 with (e := e). destruct (eval_bool e p1) as [ | ], (eval_bool e p2) as [ | ]; done!.
Qed.

Theorem eval_bool_spec (e : propLetter -> bool) (p : formula)
  (e' := fun i => if e i then True else False)
  : forall b, eval_bool e p = b <-> (if b then evalFormula e' p else ~ evalFormula e' p).
Proof.
  intros [ | ].
  - eapply eval_bool_true_iff with (e := e) (p := p).
  - subst e'. rewrite <- eval_bool_true_iff with (e := e) (p := p).
    destruct (eval_bool e p) as [ | ]; done.
Qed.

Definition finite_entails (Gamma : list formula) (C : formula) : Prop :=
  forall e : propLetter -> bool, (forall H, In H Gamma -> eval_bool e H = true) -> eval_bool e C = true.

#[local] Hint Unfold finite_entails : simplication_hints.

Lemma finite_entails_monotonic (Gamma : list formula) (Gamma' : list formula) (C : formula)
  (ENTAILS : finite_entails Gamma C)
  (SUBSET : forall H, In H Gamma -> In H Gamma')
  : finite_entails Gamma' C.
Proof.
  done!.
Qed.

Lemma finite_entails_premise (Gamma : list formula) (H : formula)
  (IN : In H Gamma)
  : finite_entails Gamma H.
Proof.
  eapply finite_entails_monotonic with (Gamma := [H]).
  - ii. done!.
  - now simpl; intros ? [-> | []].
Qed.

Theorem finite_entails_if_entails (Gamma : list formula) (C : formula)
  (ENTAILS : E.fromList Gamma ⊨ C)
  : finite_entails Gamma C.
Proof.
  red in ENTAILS. intros e Gamma_SAT. rewrite -> eval_bool_spec with (e := e).
  eapply ENTAILS. ii. rewrite <- eval_bool_spec with (e := e) (b := true).
  eapply Gamma_SAT. done!.
Qed.

Fixpoint occurs (i : propLetter) (p : formula) {struct p} : Prop :=
  match p with
  | AtomF i' => i = i'
  | ContradictionF => False
  | NegationF p1 => occurs i p1
  | ConjunctionF p1 p2 => occurs i p1 \/ occurs i p2
  | DisjunctionF p1 p2 => occurs i p1 \/ occurs i p2
  | ImplicationF p1 p2 => occurs i p1 \/ occurs i p2
  | BiconditionalF p1 p2 => occurs i p1 \/ occurs i p2
  end.

Definition gen_context_for (env : propLetter -> bool) : list propLetter -> list formula :=
  L.map (fun i : propLetter => if env i then AtomF i else NegationF (AtomF i)).

Lemma infers_dec (C : formula)
  : { ls : list propLetter | ⟪ OCCURS : forall l, In l ls <-> occurs l C ⟫ /\ ⟪ INFERS_DEC : forall e, let Gamma := E.fromList (gen_context_for e ls) in if eval_bool e C then Gamma ⊢ C else Gamma ⊢ NegationF C ⟫ }.
Proof.
  unnw. revert C.
  assert (AUX1 : forall e, forall ls1, forall ls2, E.fromList (gen_context_for e ls1) \subseteq E.fromList (gen_context_for e (ls1 ++ ls2))).
  { intros e ls1 lhs2 p IN. s!. unfold gen_context_for in *. rewrite L.in_map_iff in *. destruct IN as [l [<- IN]]. exists l. done!. }
  assert (AUX2 : forall e, forall ls1, forall ls2, E.fromList (gen_context_for e ls2) \subseteq E.fromList (gen_context_for e (ls1 ++ ls2))).
  { intros e ls1 lhs2 p IN. s!. unfold gen_context_for in *. rewrite L.in_map_iff in *. destruct IN as [l [<- IN]]. exists l. done!. }
  intros p. induction p as [i | | p1 IH1 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2 | p1 IH1 p2 IH2].
  - exists [i]. split; i.
    + ss!.
    + simpl. destruct (e i) as [ | ]; eapply ByAssumption; done!.
  - exists []. split; i.
    + ss!.
    + simpl. eapply NegationI. eapply ContradictionI with (A := ContradictionF).
      * eapply ByAssumption. done!.
      * eapply ContradictionE. eapply ByAssumption. done!.
  - destruct IH1 as (ls1 & IFF1 & INFERS1). exists ls1. split; i.
    + ss!.
    + simpl. specialize INFERS1 with (e := e). simpl in INFERS1.
      destruct (eval_bool e p1) as [ | ] eqn: OBS1; cbn.
      * eapply NegationI. eapply ContradictionI with (A := p1).
        { eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls1)); done!. }
        { eapply ByAssumption. done!. }
      * done!.
  - destruct IH1 as (ls1 & IFF1 & INFERS1), IH2 as (ls2 & IFF2 & INFERS2). exists (ls1 ++ ls2). split; i.
    + ss!.
    + simpl. specialize INFERS1 with (e := e). specialize INFERS2 with (e := e). simpl in INFERS1, INFERS2.
      destruct (eval_bool e p1) as [ | ] eqn: OBS1; destruct (eval_bool e p2) as [ | ] eqn: OBS2; cbn; trivial.
      * eapply ConjunctionI.
        { eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls1)); trivial. }
        { eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls2)); trivial. }
      * assert (claim1 : E.insert (ConjunctionF p1 p2) (E.fromList (gen_context_for e (ls1 ++ ls2))) ⊢ NegationF p2).
        { eapply extend_infers with (Gamma := E.fromList (gen_context_for e (ls1 ++ ls2))); trivial.
          - eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls2)); trivial.
          - done!.
        }
        eapply NegationI. eapply ContradictionI with (Gamma := E.insert (ConjunctionF p1 p2) (E.fromList (gen_context_for e (ls1 ++ ls2)))) (A := p2); trivial.
        eapply ConjunctionE2 with (A := p1). eapply ByAssumption. done!.
      * assert (claim1 : E.insert (ConjunctionF p1 p2) (E.fromList (gen_context_for e (ls1 ++ ls2))) ⊢ NegationF p1).
        { eapply extend_infers with (Gamma := E.fromList (gen_context_for e (ls1 ++ ls2))); trivial.
          - eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls1)); trivial.
          - done!.
        }
        eapply NegationI. eapply ContradictionI with (Gamma := E.insert (ConjunctionF p1 p2) (E.fromList (gen_context_for e (ls1 ++ ls2)))) (A := p1); trivial.
        eapply ConjunctionE1 with (B := p2). eapply ByAssumption. done!.
      * assert (claim1 : E.insert (ConjunctionF p1 p2) (E.fromList (gen_context_for e (ls1 ++ ls2))) ⊢ NegationF p1).
        { eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls1)); trivial. ii. right. eapply AUX1; done. }
        assert (claim2 : E.insert (ConjunctionF p1 p2) (E.fromList (gen_context_for e (ls1 ++ ls2))) ⊢ NegationF p2).
        { eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls2)); trivial. ii. right. eapply AUX2; done. }
        eapply NegationI. eapply ContradictionI with (Gamma := E.insert (ConjunctionF p1 p2) (E.fromList (gen_context_for e (ls1 ++ ls2)))) (A := p1); trivial.
        eapply ConjunctionE1 with (B := p2). eapply ByAssumption. done!.
  - destruct IH1 as (ls1 & IFF1 & INFERS1), IH2 as (ls2 & IFF2 & INFERS2). simpl in INFERS1, INFERS2. exists (ls1 ++ ls2). split; i.
    + ss!.
    + simpl. specialize INFERS1 with (e := e); specialize INFERS2 with (e := e).
      destruct (eval_bool e p1) as [ | ] eqn: OBS1; destruct (eval_bool e p2) as [ | ] eqn: OBS2; cbn.
      * eapply DisjunctionI1. eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls1)); trivial.
      * eapply DisjunctionI1. eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls1)); trivial.
      * eapply DisjunctionI2. eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls2)); trivial.
      * eapply NegationI. eapply DisjunctionE with (A := p1) (B := p2).
        { eapply ByAssumption; done!. }
        { eapply ContradictionI with (A := p1).
          - eapply ByAssumption; done!.
          - eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls1)); trivial.
            ii. right. right. eapply AUX1; done.
        }
        { eapply ContradictionI with (A := p2).
          - eapply ByAssumption; done!.
          - eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls2)); trivial.
            ii. right. right. eapply AUX2; done!.
        }
  - destruct IH1 as (ls1 & IFF1 & INFERS1), IH2 as (ls2 & IFF2 & INFERS2). exists (ls1 ++ ls2). split; i.
    + ss!.
    + simpl. specialize INFERS1 with (e := e). specialize INFERS2 with (e := e). simpl in INFERS1, INFERS2.
      destruct (eval_bool e p1) as [ | ] eqn: OBS1; destruct (eval_bool e p2) as [ | ] eqn: OBS2; cbn; trivial.
      * eapply ImplicationI. eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls2)); trivial.
        ii. right. eapply AUX2; done.
      * eapply NegationI. eapply ContradictionI with (A := p2).
        { eapply ImplicationE with (A := p1).
          - eapply ByAssumption. done!.
          - eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls1)); trivial.
            ii. right. eapply AUX1. done!.
        }
        { eapply NegationI. eapply ContradictionI with (A := p2).
          - eapply ByAssumption. done!.
          - eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls2)); trivial.
            ii. right. right. eapply AUX2; done!.
        }
      * eapply ImplicationI. eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls2)).
        { eapply INFERS2. }
        { ii. right. eapply AUX2; done!. }
      * eapply ImplicationI. eapply ContradictionE. eapply ImplicationE with (A := NegationF p1).
        { eapply ImplicationI. eapply ContradictionI with (A := p1).
          - eapply ByAssumption. done!.
          - eapply ByAssumption. done!.
        }
        { eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls1)); trivial.
          ii. right. eapply AUX1. done!.
        }
  - destruct IH1 as (ls1 & IFF1 & INFERS1), IH2 as (ls2 & IFF2 & INFERS2). exists (ls1 ++ ls2). split; i.
    + ss!.
    + simpl. specialize INFERS1 with (e := e). specialize INFERS2 with (e := e). simpl in INFERS1, INFERS2.
      destruct (eval_bool e p1) as [ | ] eqn: OBS1; destruct (eval_bool e p2) as [ | ] eqn: OBS2; cbn; trivial.
      * eapply BiconditionalI.
        { eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls2)); trivial.
          ii. right. eapply AUX2. done!.
        }
        { eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls1)); trivial.
          ii. right. eapply AUX1. done!.
        }
      * eapply NegationI.
        { eapply ContradictionI with (A := p2).
          - eapply BiconditionalE1 with (A := p1).
            + eapply ByAssumption. done!.
            + eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls1)); trivial.
              ii. right. eapply AUX1; done!.
          - eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls2)); trivial.
            ii. right. eapply AUX2; done!.
        }
      * eapply NegationI.
        { eapply ContradictionI with (A := p1).
          - eapply BiconditionalE2 with (B := p2).
            + eapply ByAssumption. done!.
            + eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls2)); trivial.
              ii. right. eapply AUX2; done!.
          - eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls1)); trivial.
            ii. right. eapply AUX1; done!.
        }
      * eapply BiconditionalI.
        { eapply NegationE. eapply ContradictionI with (A := p1).
          - eapply ByAssumption. done!.
          - eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls1)); trivial.
            ii. right. right. eapply AUX1; done!.
        }
        { eapply NegationE. eapply ContradictionI with (A := p2).
          - eapply ByAssumption. done!.
          - eapply extend_infers with (Gamma := E.fromList (gen_context_for e ls2)); trivial.
            ii. right. right. eapply AUX2; done!.
        }
Qed.

Lemma is_theorem_if_is_deducible_for_any_gen_context (C : formula) (ls : list propLetter)
  (OCCURS : forall i : propLetter, In i ls -> occurs i C)
  (INFERS : forall e : propLetter -> bool, E.fromList (gen_context_for e ls) ⊢ C)
  : E.fromList [] ⊢ C.
Proof.
  revert ls C OCCURS INFERS.
  assert (MAP_EXT : forall ls : list propLetter, forall f1 : propLetter -> formula, forall f2 : propLetter -> formula,
    forall EXT : forall l : propLetter, In l ls -> f1 l = f2 l,
    List.map f1 ls = List.map f2 ls
  ).
  { induction ls as [ | l ls IH]; simpl; ii; [ | f_equal]; eauto with *. }
  induction ls as [ | i ls IH]; simpl; i.
  - eapply INFERS. exact (fun _ => false).
  - destruct (List.in_dec Nat.eq_dec i ls) as [YES | NO].
    + eapply IH. ss!. intros e. eapply extend_infers with (Gamma := E.fromList (gen_context_for e (i :: ls))).
      * eapply INFERS.
      * simpl. destruct (e i) as [ | ] eqn: H_OBS; intros H IN.
        { s!. destruct IN as [<- | IN]; unfold gen_context_for in *; ss!. exists i. rewrite H_OBS; ss!. }
        { s!. destruct IN as [<- | IN]; unfold gen_context_for in *; ss!. exists i. rewrite H_OBS; ss!. }
    + eapply IH. done!. intros e. destruct (e i) as [ | ] eqn: H_OBS.
      * set (e' := fun l : propLetter => if eq_dec i l then false else e l).
        assert (INFERS' : E.insert (NegationF (AtomF i)) (E.fromList (gen_context_for e' ls)) ⊢ C).
        { specialize INFERS with (e := e'). unfold e' in INFERS. destruct (eq_dec i i) as [EQ | NE]; [clear EQ | contradiction].
          fold e' in INFERS. eapply extend_infers with (Gamma := E.fromList (NegationF (AtomF i) :: gen_context_for e' ls)); ss!.
        }
        assert (H_EQ : gen_context_for e ls = gen_context_for e' ls).
        { specialize MAP_EXT with (ls := ls) (f1 := fun i => if e i then AtomF i else NegationF (AtomF i)) (f2 := fun i => if e' i then AtomF i else NegationF (AtomF i)). 
          unfold gen_context_for. eapply MAP_EXT. intros i' IN'. unfold e'. destruct (eq_dec i i') as [EQ | NE].
          - subst i'. contradiction.
          - reflexivity.
        }
        assert (claim1 : E.insert (NegationF (AtomF i)) (E.fromList (gen_context_for e ls)) ⊢ C).
        { rewrite -> H_EQ; trivial. }
        assert (claim2 : E.fromList (gen_context_for e ls) ⊢ DisjunctionF (AtomF i) (NegationF (AtomF i))).
        { eapply extend_infers with (Gamma := E.empty); [eapply Law_of_Excluded_Middle | done]. }
        eapply DisjunctionE with (A := AtomF i) (B := NegationF (AtomF i)) (C := C); trivial.
        specialize INFERS with (e := e). rewrite H_OBS in INFERS.
        eapply extend_infers with (Gamma := E.fromList (AtomF i :: gen_context_for e ls)); ss!.
      * set (e' := fun l : propLetter => if eq_dec i l then true else e l).
        assert (INFERS' : E.insert (AtomF i) (E.fromList (gen_context_for e' ls)) ⊢ C).
        { specialize INFERS with (e := e'). unfold e' in INFERS. destruct (eq_dec i i) as [EQ | NE]; [clear EQ | contradiction].
          fold e' in INFERS. eapply extend_infers with (Gamma := E.fromList (AtomF i :: gen_context_for e' ls)); ss!.
        }
        assert (H_EQ : gen_context_for e ls = gen_context_for e' ls).
        { specialize MAP_EXT with (ls := ls) (f1 := fun i => if e i then AtomF i else NegationF (AtomF i)) (f2 := fun i => if e' i then AtomF i else NegationF (AtomF i)). 
          unfold gen_context_for. eapply MAP_EXT. intros i' IN'. unfold e'. destruct (eq_dec i i') as [EQ | NE].
          - subst i'. contradiction.
          - reflexivity.
        }
        assert (claim1 : E.insert (AtomF i) (E.fromList (gen_context_for e ls)) ⊢ C).
        { rewrite -> H_EQ; trivial. }
        assert (claim2 : E.fromList (gen_context_for e ls) ⊢ DisjunctionF (AtomF i) (NegationF (AtomF i))).
        { eapply extend_infers with (Gamma := E.empty); [eapply Law_of_Excluded_Middle | done]. }
        eapply DisjunctionE with (A := AtomF i) (B := NegationF (AtomF i)) (C := C); trivial.
        specialize INFERS with (e := e). rewrite H_OBS in INFERS.
        eapply extend_infers with (Gamma := E.fromList (NegationF (AtomF i) :: gen_context_for e ls)); ss!.
Qed.

Theorem tautology_is_theorem (C : formula)
  (ENTAILS : finite_entails [] C)
  : E.fromList [] ⊢ C.
Proof.
  unfold finite_entails in ENTAILS. pose proof (infers_dec C) as (ls & ?); des.
  eapply is_theorem_if_is_deducible_for_any_gen_context with (ls := ls).
  - done!.
  - intros e. specialize INFERS_DEC with (e := e). specialize ENTAILS with (e := e).
    destruct (eval_bool e C) as [ | ] eqn: OBS; trivial. discriminate ENTAILS. done!.
Qed.

Corollary weak_completeness (Gamma : list formula) (C : formula)
  (ENTAILS : finite_entails Gamma C)
  : E.fromList Gamma ⊢ C.
Proof.
  revert C ENTAILS. induction Gamma as [ | H Gamma IH].
  - exact tautology_is_theorem.
  - ii. eapply extend_infers with (Gamma := E.insert H (E.fromList Gamma)).
    { eapply ImplicationE with (A := H).
      - eapply extend_infers with (Gamma := E.fromList Gamma).
        + eapply IH. intros e Gamma_SAT. simpl. red in ENTAILS. destruct (eval_bool e H) as [ | ] eqn: H_OBS.
          * rewrite ENTAILS with (e := e); trivial; simpl. intros A [<- | IN]; eauto.
          * now destruct (eval_bool e C) as [ | ].
        + done!.
      - eapply ByAssumption. done!.
    }
    { now intros A [<- | IN]; [left | right]. }
Qed.

End WEAK_COMPLETENESS.

Section LindenbaumBooleanAlgebra.

Import ListNotations.

#[global]
Instance formula_isBA : isBA formula :=
  { andB := ConjunctionF
  ; orB := DisjunctionF
  ; notB := NegationF
  ; trueB := ImplicationF ContradictionF ContradictionF
  ; falseB := ContradictionF
  }.

#[local] Obligation Tactic := i.

#[global, program]
Instance formula_isSetoid : isSetoid formula :=
  { eqProp (lhs : formula) (rhs : formula) := E.singleton lhs ⊢ rhs /\ E.singleton rhs ⊢ lhs }.
Next Obligation with done!.
  split.
  - ii. split; eapply ByAssumption...
  - ii; des...
  - ii; des. split; eapply Cut_property; try eassumption; eapply extend_infers; try eassumption...
Qed.

#[global]
Instance LBA_satisfiesBooleanAlgebraLaws
  : BooleanAlgebraLaws formula_isBA.
Proof with done!.
  repeat (split; ii); simpl in *; des.
  { eapply ConjunctionI.
    - eapply Cut_property with (A := x1).
      + eapply ConjunctionE1, ByAssumption...
      + eapply extend_infers...
    - eapply Cut_property with (A := y1).
      + eapply ConjunctionE2, ByAssumption...
      + eapply extend_infers...
  }
  { eapply ConjunctionI.
    - eapply Cut_property with (A := x2).
      + eapply ConjunctionE1, ByAssumption...
      + eapply extend_infers...
    - eapply Cut_property with (A := y2).
      + eapply ConjunctionE2, ByAssumption...
      + eapply extend_infers...
  }
  { eapply DisjunctionE.
    - eapply ByAssumption...
    - eapply DisjunctionI1, extend_infers...
    - eapply DisjunctionI2, extend_infers...
  }
  { eapply DisjunctionE.
    - eapply ByAssumption...
    - eapply DisjunctionI1, extend_infers...
    - eapply DisjunctionI2, extend_infers...
  }
  { eapply NegationI. eapply ContradictionI with (A := x1).
    - eapply extend_infers...
    - eapply ByAssumption...
  }
  { eapply NegationI. eapply ContradictionI with (A := x2).
    - eapply extend_infers...
    - eapply ByAssumption...
  }
  { eapply ConjunctionI.
    - eapply ConjunctionI.
      + eapply ConjunctionE1, ByAssumption...
      + eapply ConjunctionE1, ConjunctionE2, ByAssumption...
    - eapply ConjunctionE2, ConjunctionE2, ByAssumption...
  }
  { eapply ConjunctionI.
    - eapply ConjunctionE1, ConjunctionE1, ByAssumption...
    - eapply ConjunctionI.
      + eapply ConjunctionE2, ConjunctionE1, ByAssumption...
      + eapply ConjunctionE2, ByAssumption...
  }
  { eapply DisjunctionE.
    - eapply ByAssumption...
    - eapply DisjunctionI1, DisjunctionI1, ByAssumption. left...
    - eapply DisjunctionE.
      + eapply ByAssumption. left...
      + eapply DisjunctionI1, DisjunctionI2, ByAssumption. left...
      + eapply DisjunctionI2, ByAssumption. left...
  }
  { eapply DisjunctionE.
    - eapply ByAssumption...
    - eapply DisjunctionE.
      + eapply ByAssumption. left...
      + eapply DisjunctionI1, ByAssumption. left...
      + eapply DisjunctionI2, DisjunctionI1, ByAssumption. left...
    - eapply DisjunctionI2, DisjunctionI2, ByAssumption. left...
  }
  { eapply ConjunctionI.
    - eapply ConjunctionE2, ByAssumption...
    - eapply ConjunctionE1, ByAssumption...
  }
  { eapply ConjunctionI.
    - eapply ConjunctionE2, ByAssumption...
    - eapply ConjunctionE1, ByAssumption...
  }
  { eapply DisjunctionE.
    - eapply ByAssumption...
    - eapply DisjunctionI2, ByAssumption. left...
    - eapply DisjunctionI1, ByAssumption. left...
  }
  { eapply DisjunctionE.
    - eapply ByAssumption...
    - eapply DisjunctionI2, ByAssumption. left...
    - eapply DisjunctionI1, ByAssumption. left...
  }
  { eapply DisjunctionE.
    - eapply ConjunctionE2, ByAssumption...
    - eapply DisjunctionI1, ConjunctionI.
      + eapply ConjunctionE1, ByAssumption. right...
      + eapply ByAssumption. left...
    - eapply DisjunctionI2, ConjunctionI.
      + eapply ConjunctionE1, ByAssumption. right...
      + eapply ByAssumption. left...
  }
  { eapply DisjunctionE.
    - eapply ByAssumption...
    - eapply ConjunctionI.
      + eapply ConjunctionE1, ByAssumption. left...
      + eapply DisjunctionI1, ConjunctionE2, ByAssumption. left...
    - eapply ConjunctionI.
      + eapply ConjunctionE1, ByAssumption. left...
      + eapply DisjunctionI2, ConjunctionE2, ByAssumption. left...
  }
  { eapply DisjunctionE.
    - eapply ConjunctionE1, ByAssumption...
    - eapply DisjunctionI1, ConjunctionI.
      + eapply ByAssumption. left...
      + eapply ConjunctionE2, ByAssumption. right...
    - eapply DisjunctionI2, ConjunctionI.
      + eapply ByAssumption. left...
      + eapply ConjunctionE2, ByAssumption. right...
  }
  { eapply DisjunctionE.
    - eapply ByAssumption...
    - eapply ConjunctionI.
      + eapply DisjunctionI1, ConjunctionE1, ByAssumption. left...
      + eapply ConjunctionE2, ByAssumption. left...
    - eapply ConjunctionI.
      + eapply DisjunctionI2, ConjunctionE1, ByAssumption. left...
      + eapply ConjunctionE2, ByAssumption. left...
  }
  { eapply DisjunctionE.
    - eapply ByAssumption...
    - eapply ConjunctionI.
      + eapply DisjunctionE.
        * eapply ByAssumption. right...
        * eapply DisjunctionI1, ByAssumption. left...
        * eapply DisjunctionI2, ConjunctionE1, ByAssumption. left...
      + eapply DisjunctionE.
        * eapply ByAssumption. right...
        * eapply DisjunctionI1, ByAssumption. left...
        * eapply DisjunctionI2, ConjunctionE2, ByAssumption. left...
    - eapply ConjunctionI.
      + eapply DisjunctionE.
        * eapply ByAssumption. right...
        * eapply DisjunctionI1, ByAssumption. left...
        * eapply DisjunctionI2, ConjunctionE1, ByAssumption. left...
      + eapply DisjunctionE.
        * eapply ByAssumption. right...
        * eapply DisjunctionI1, ByAssumption. left...
        * eapply DisjunctionI2, ConjunctionE2, ByAssumption. left...
  }
  { eapply DisjunctionE.
    - eapply ConjunctionE1, ByAssumption...
    - eapply DisjunctionI1, ByAssumption. left...
    - eapply DisjunctionE.
      + eapply ConjunctionE2, ByAssumption. right...
      + eapply DisjunctionI1, ByAssumption. left...
      + eapply DisjunctionI2, ConjunctionI.
        * eapply ByAssumption. right; left...
        * eapply ByAssumption. left...
  }
  { eapply DisjunctionE.
    - eapply ByAssumption...
    - eapply ConjunctionI.
      + eapply DisjunctionI1, ConjunctionE1, ByAssumption. left...
      + eapply DisjunctionI1, ConjunctionE2, ByAssumption. left...
    -  eapply ConjunctionI.
      + eapply DisjunctionI2, ByAssumption. left...
      + eapply DisjunctionI2, ByAssumption. left...
  }
  { eapply DisjunctionE.
    - eapply ConjunctionE1, ByAssumption...
    - eapply DisjunctionE.
      + eapply ConjunctionE2, ByAssumption. right...
      + eapply DisjunctionI1, ConjunctionI.
        * eapply ByAssumption. right; left...
        * eapply ByAssumption. left...
      + eapply DisjunctionI2, ByAssumption. left...
    - eapply DisjunctionI2, ByAssumption. left...
  }
  { eapply ConjunctionE2, ByAssumption... }
  { eapply ConjunctionI.
    - eapply ImplicationI, ByAssumption. left...
    - eapply ByAssumption...
  }
  { eapply ConjunctionE1, ByAssumption... }
  { eapply ConjunctionI.
    - eapply ByAssumption...
    - eapply ImplicationI, ByAssumption. left...
  }
  { eapply DisjunctionE.
    - eapply ByAssumption...
    - eapply ContradictionE, ByAssumption. left...
    - eapply ByAssumption. left...
  }
  { eapply DisjunctionI2, ByAssumption... }
  { eapply DisjunctionE.
    - eapply ByAssumption...
    - eapply ByAssumption. left...
    - eapply ContradictionE, ByAssumption. left...
  }
  { eapply DisjunctionI1, ByAssumption... }
  { eapply ConjunctionE1, ByAssumption... }
  { eapply ConjunctionI.
    - eapply ByAssumption...
    - eapply ContradictionE, ByAssumption...
  }
  { eapply ConjunctionE2, ByAssumption... }
  { eapply ConjunctionI.
    - eapply ContradictionE, ByAssumption...
    - eapply ByAssumption...
  }
  { eapply ImplicationI, ByAssumption. left... }
  { eapply DisjunctionI1, ImplicationI, ByAssumption. left... }
  { eapply ImplicationI, ByAssumption. left... }
  { eapply DisjunctionI2, ImplicationI, ByAssumption. left... }
  { eapply ConjunctionE1, ByAssumption... }
  { eapply ConjunctionI; eapply ByAssumption... }
  { eapply DisjunctionE.
    - eapply ByAssumption...
    - eapply ByAssumption. left...
    - eapply ByAssumption. left...
  }
  { eapply DisjunctionI1, ByAssumption... }
  { eapply ConjunctionE1, ByAssumption... }
  { eapply ConjunctionI.
    - eapply ByAssumption...
    - eapply DisjunctionI1, ByAssumption...
  }
  { eapply DisjunctionE.
    - eapply ByAssumption...
    - eapply ByAssumption. left...
    - eapply ConjunctionE1, ByAssumption. left...
  }
  { eapply DisjunctionI1, ByAssumption... }
  { eapply ContradictionI with (A := x).
    - eapply ConjunctionE1, ByAssumption...
    - eapply ConjunctionE2, ByAssumption...
  }
  { eapply ContradictionE, ByAssumption... }
  { eapply ImplicationI, ByAssumption. left... }
  { eapply extend_infers.
    - eapply Law_of_Excluded_Middle.
    - ii...
  }
Qed.

#[global]
Instance LindenbaumBooleanAlgebra : @isCBA formula formula_isSetoid :=
  { CBA_isBA := formula_isBA
  ; CBA_satisfiesBooleanAlgebraLaws := LBA_satisfiesBooleanAlgebraLaws
  ; CBA_countable := formula_isEnumerable
  }.

Lemma leB_iff (lhs : formula) (rhs : formula)
  : lhs =< rhs <-> E.singleton lhs ⊢ rhs.
Proof with reflexivity || trivial.
  simpl. split.
  - intros [INFERS INFERS'].
    eapply Cut_property with (A := ConjunctionF lhs rhs)...
    eapply ConjunctionE2, ByAssumption. left...
  - intros INFERS. split.
    + eapply ConjunctionE1, ByAssumption...
    + eapply ConjunctionI...
      eapply ByAssumption...
Qed.

Lemma andsB_le_iff (xs : list formula) (b : formula)
  : andsB xs =< b <-> (exists X, L.is_listrep_of xs X /\ X ⊢ b).
Proof.
  rewrite leB_iff. revert b. induction xs as [ | x xs IH]; i; split.
  - intros H_LE. exists E.empty. split. done!. eapply Cut_property with (A := andsB []).
    + eapply ImplicationI, ByAssumption; done!.
    + eapply extend_infers with (Gamma := E.singleton (andsB [])); done!.
  - intros [X [LISTREP INFERS]]. eapply extend_infers with (Gamma := X); done!.
  - intros INFERS. exploit (proj1 (IH (ImplicationF x b))).
    + eapply ImplicationI. eapply Cut_property with (A := andsB (x :: xs)).
      { simpl. eapply ConjunctionI.
        - eapply ByAssumption; done!.
        - eapply ByAssumption; done!.
      }
      { eapply extend_infers with (Gamma := E.singleton (andsB (x :: xs))); done!. }
    + intros [X [LISTREP INFERS']]. pose proof (in_dec eq_dec x xs) as [H_in | H_not_in].
      { exploit (proj2 (IH b)).
        - exists X. split. done!. eapply ImplicationE. exact INFERS'. eapply ByAssumption. done!.
        - intros INFERS''. exists (E.insert x X). split. done!. eapply ImplicationE.
          + eapply extend_infers with (Gamma := X); done!.
          + eapply ByAssumption; done!.
      }
      { exists (E.insert x X). split. done!. eapply ImplicationE.
        - eapply extend_infers with (Gamma := X). exact INFERS'. done!.
        - eapply ByAssumption. done!.
      }
  - intros [X [LISTREP INFERS]]. destruct (in_dec eq_dec x xs) as [H_in | H_not_in].
    + exploit (proj2 (IH b)).
      * exists X. split; done!.
      * intros INFERS'. eapply Cut_property with (A := andsB xs).
        { eapply ConjunctionE2, ByAssumption; done!. }
        { eapply extend_infers. exact INFERS'. done!. }
    + exploit (proj2 (IH (ImplicationF x b))).
      * exists (E.intersection X (E.complement (E.singleton x))). split. done!.
        eapply ImplicationI. eapply extend_infers with (Gamma := X); done!.
      * intros INFERS'. eapply ImplicationE with (A := x).
        { eapply Cut_property with (A := andsB xs).
          - eapply ConjunctionE2, ByAssumption; ss!.
          - eapply extend_infers. exact INFERS'. done!.
        }
        { eapply ConjunctionE1, ByAssumption; ss!. }
Qed.

#[global]
Add Parametric Morphism :
  infers with signature (eqProp ==> eqProp ==> iff)
  as infers_compatWith_eqProp.
Proof.
  intros X X' X_eq_X' b b' [INFERS1 INFERS2]. split.
  - intros INFERS. eapply Cut_property with (A := b).
    + eapply extend_infers; done!.
    + eapply extend_infers; done!.
  - intros INFERS. eapply Cut_property with (A := b').
    + eapply extend_infers; done!.
    + eapply extend_infers; done!.
Qed.

End LindenbaumBooleanAlgebra.

Section CONSTRUCTIVE_FACTS.

Import ListNotations.

Variant Th (X : ensemble formula) (b : formula) : Prop :=
  | In_Th
    (INFERS : X ⊢ b)
    : b \in Th X.

#[local] Hint Constructors Th : core.

#[global]
Add Parametric Morphism :
  Th with signature (eqProp ==> eqProp)
  as Th_lifts_eqProp.
Proof.
  intros X X' X_eq_X' b. split; intros [INFERS]; econstructor.
  - now rewrite <- X_eq_X'.
  - now rewrite -> X_eq_X'.
Qed.

Lemma lemma1_of_1_3_8 (X : ensemble formula)
  : isFilter (Th X).
Proof with reflexivity || eauto.
  eapply isFilter_intro.
  - exists trueB. econstructor.
    eapply ImplicationI, ByAssumption; done!.
  - intros x1 x2 [INFERS1] [INFERS2].
    econstructor. eapply ConjunctionI; done!.
  - intros x [INFERS] x' x_le_x'. apply leB_iff in x_le_x'.
    econstructor. eapply Cut_property. exact INFERS.
    eapply extend_infers with (Gamma := E.singleton x); done!.
Qed.

Lemma cl_isSubsetOf_Th (X : ensemble formula)
  : cl X \subseteq Th X.
Proof with eauto.
  intros b [xs ?]; des. apply andsB_le_iff in andsB_LE.
  destruct andsB_LE as [X' [xs_repr_X' INFERS]].
  econstructor. eapply extend_infers...
  intros z z_in. eapply FINITE_SUBSET, xs_repr_X'...
Qed.

Theorem inference_is_finite (X : ensemble formula) (b : formula)
  (INFERS : X ⊢ b)
  : exists xs, exists X', L.is_finsubset_of xs X /\ L.is_listrep_of xs X' /\ X' ⊢ b.
Proof.
  induction INFERS.
  - exists [C], (E.singleton C). split. ss!. split. done!.
    eapply ByAssumption. done!.
  - destruct IHINFERS1 as [xs1 [X1' [? [? ?]]]], IHINFERS2 as [xs2 [X2' [? [? ?]]]].
    exists (xs1 ++ xs2), (E.union X1' X2'). split. done!. split. done!.
    eapply ContradictionI with (A := A); eapply extend_infers; ss!.
  - destruct IHINFERS as [xs [X' [? [? ?]]]].
    exists xs, X'. split. done!. split. done!.
    eapply ContradictionE; done!.
  - destruct IHINFERS as [xs [X' [? [? ?]]]].
    exists (L.remove eq_dec A xs), (E.delete A X'). split. done!. split. done!.
    eapply NegationI. eapply extend_infers; ss!. pose proof (eq_dec x A) as [? | ?]; done!.
  - destruct IHINFERS as [xs [X' [? [? ?]]]].
    exists (L.remove eq_dec (NegationF A) xs), (E.delete (NegationF A) X'). split. done!. split. done!.
    eapply NegationE. eapply extend_infers; ss!. pose proof (eq_dec x (NegationF A)) as [? | ?]; done!.
  - destruct IHINFERS1 as [xs1 [X1' [? [? ?]]]], IHINFERS2 as [xs2 [X2' [? [? ?]]]].
    exists (xs1 ++ xs2), (E.union X1' X2'). split. done!. split. done!.
    eapply ConjunctionI; eapply extend_infers; ss!.
  - destruct IHINFERS as [xs [X' [? [? ?]]]].
    exists xs, X'. split. done!. split. done!.
    eapply ConjunctionE1; done!.
  - destruct IHINFERS as [xs [X' [? [? ?]]]].
    exists xs, X'. split. done!. split. done!.
    eapply ConjunctionE2; ss!.
  - destruct IHINFERS as [xs [X' [? [? ?]]]].
    exists xs, X'. split. done!. split. done!.
    eapply DisjunctionI1; ss!.
  - destruct IHINFERS as [xs [X' [? [? ?]]]].
    exists xs, X'. split. done!. split. done!.
    eapply DisjunctionI2; ss!.
  - destruct IHINFERS1 as [xs1 [X1' [? [? ?]]]], IHINFERS2 as [xs2 [X2' [? [? ?]]]], IHINFERS3 as [xs3 [X3' [? [? ?]]]].
    exists (xs1 ++ (L.remove eq_dec A xs2 ++ L.remove eq_dec B xs3)), (E.union X1' (E.union (E.delete A X2') (E.delete B X3'))). split. done!. split. done!.
    eapply DisjunctionE with (A := A) (B := B).
    + eapply extend_infers with (Gamma := X1'); ss!.
    + eapply extend_infers with (Gamma := X2'); trivial.
      ii; s!. pose proof (eq_dec x A) as [? | ?]; pose proof (eq_dec x B) as [? | ?]; done!.
    + eapply extend_infers with (Gamma := X3'); trivial.
      ii; s!. pose proof (eq_dec x A) as [? | ?]; pose proof (eq_dec x B) as [? | ?]; done!.
  - destruct IHINFERS as [xs [X' [? [? ?]]]].
    exists (L.remove eq_dec A xs), (E.delete A X'). split. done!. split. done!.
    eapply ImplicationI. eapply extend_infers; ss!. pose proof (eq_dec x A) as [? | ?]; done!.
  - destruct IHINFERS1 as [xs1 [X1' [? [? ?]]]], IHINFERS2 as [xs2 [X2' [? [? ?]]]].
    exists (xs1 ++ xs2), (E.union X1' X2'). split. done!. split. done!.
    eapply ImplicationE; eapply extend_infers; ss!.
  - destruct IHINFERS1 as [xs1 [X1' [? [? ?]]]], IHINFERS2 as [xs2 [X2' [? [? ?]]]].
    exists (L.remove eq_dec A xs1 ++ L.remove eq_dec B xs2), (E.union (E.delete A X1') (E.delete B X2')). split. done!. split. done!.
    eapply BiconditionalI; eapply extend_infers; ss!. pose proof (eq_dec x A) as [? | ?]; done!. pose proof (eq_dec x B) as [? | ?]; done!.
  - destruct IHINFERS1 as [xs1 [X1' [? [? ?]]]], IHINFERS2 as [xs2 [X2' [? [? ?]]]].
    exists (xs1 ++ xs2), (E.union X1' X2'). split. done!. split. done!.
    eapply BiconditionalE1; eapply extend_infers; ss!.
  - destruct IHINFERS1 as [xs1 [X1' [? [? ?]]]], IHINFERS2 as [xs2 [X2' [? [? ?]]]].
    exists (xs1 ++ xs2), (E.union X1' X2'). split. done!. split. done!.
    eapply BiconditionalE2; eapply extend_infers; ss!.
Qed.

Corollary Th_isSubsetOf_cl (X : ensemble formula)
  : Th X \subseteq cl X.
Proof.
  intros b [INFERS].
  pose proof (inference_is_finite X b INFERS) as [xs [X' [? [? ?]]]].
  exists xs. unnw. split; eauto. eapply andsB_le_iff. exists X'. eauto.
Qed.

Corollary cl_eq_Th (X : ensemble formula)
  : cl X == Th X.
Proof.
  s!. split.
  - eapply cl_isSubsetOf_Th.
  - eapply Th_isSubsetOf_cl.
Qed.

Lemma inconsistent_cl_iff (X : ensemble formula)
  : inconsistent (cl X) <-> X ⊢ ContradictionF.
Proof.
  change (inconsistent (cl X) <-> X ⊢ falseB). split.
  - intros [botB [botB_in botB_eq_falseB]].
    pose proof (cl_isSubsetOf_Th X botB botB_in) as [INFERS].
    now rewrite <- botB_eq_falseB.
  - intros INFERS. exists falseB. split; eauto with *.
    eapply Th_isSubsetOf_cl; eauto.
Qed.

#[local] Hint Resolve fact1_of_1_2_8 fact2_of_1_2_8 fact3_of_1_2_8 fact4_of_1_2_8 fact5_of_1_2_8 lemma1_of_1_2_11 inconsistent_compatWith_isSubsetOf inconsistent_cl_iff : core.

Lemma filters_is_inconsistent_iff (F : ensemble formula)
  (F_isFilter : isFilter F)
  : inconsistent F <-> F ⊢ ContradictionF.
Proof with eauto with *.
  split; intros INCONSISTENT.
  - eapply inconsistent_cl_iff.
    eapply inconsistent_compatWith_isSubsetOf with (X := F)...
  - eapply inconsistent_compatWith_isSubsetOf with (X := cl F)...
    eapply inconsistent_cl_iff...
Qed.

Fixpoint axiom_set (X : ensemble formula) (n : nat) {struct n} : ensemble formula :=
  match n with
  | O => X
  | S n' => E.union (axiom_set X n') (insertion (improveFilter (Th X) n') n')
  end.

Lemma lemma1_of_1_3_9 (X : ensemble formula) (n : nat)
  : improveFilter (Th X) n == Th (axiom_set X n).
Proof with eauto with *.
  revert X. induction n as [ | n IH]; [reflexivity | intros X b].
  simpl. unfold Insertion. rewrite cl_eq_Th, IH. split; intros b_in.
  - rewrite <- cl_eq_Th. rewrite <- cl_eq_Th in b_in. revert b b_in.
    change ((cl (E.union (Th (axiom_set X n)) (insertion (Th (axiom_set X n)) n))) \subseteq (cl (E.union (axiom_set X n) (insertion (Th (axiom_set X n)) n)))).
    transitivity (cl (cl (E.union (axiom_set X n) (insertion (Th (axiom_set X n)) n)))).
    + eapply fact4_of_1_2_8. intros b [b_in | b_in].
      * rewrite <- cl_eq_Th in b_in. revert b b_in. eapply fact4_of_1_2_8. ii; left...
      * rewrite cl_eq_Th. econstructor. eapply ByAssumption. right...
    + eapply fact5_of_1_2_8...
  - rewrite <- cl_eq_Th. rewrite <- cl_eq_Th in b_in. revert b b_in.
    eapply fact4_of_1_2_8. intros b [b_in | b_in].
    + left. econstructor. eapply ByAssumption...
    + right...
Qed.

Lemma completeness_theorem_prototype (X : ensemble formula) (b : formula) (env : propLetter -> Prop)
  (ENTAILS : X ⊨ b)
  (EQUICONSISTENT : equiconsistent (Th (E.insert (NegationF b) X)) (evalFormula env))
  (SUBSET : Th (E.insert (NegationF b) X) \subseteq evalFormula env)
  (IS_FILTER : isFilter (evalFormula env))
  : X ⊢ b.
Proof with eauto with *.
  revert EQUICONSISTENT SUBSET IS_FILTER. pose (evalFormula env) as X'.
  fold X'. ii.
  assert (claim1 : evalFormula env b).
  { eapply ENTAILS. ii.
    eapply SUBSET. econstructor.
    eapply ByAssumption. right...
  }
  assert (claim2 : inconsistent (cl X')).
  { eapply inconsistent_cl_iff.
    eapply ContradictionI with (A := b).
    - eapply ByAssumption...
    - eapply ByAssumption. eapply SUBSET. econstructor. eapply ByAssumption. left...
  }
  assert (claim3 : inconsistent (Th (E.insert (NegationF b) X))).
  { eapply EQUICONSISTENT. eapply inconsistent_compatWith_isSubsetOf with (X := cl X')... }
  eapply NegationE. eapply inconsistent_cl_iff. rewrite cl_eq_Th...
Qed.

Definition MaximalConsistentSet (X : ensemble formula) : ensemble formula :=
  completeFilterOf (Th X).

Variant full_axiom_set (X : ensemble formula) (b : formula) : Prop :=
  | In_full_axiom_set (n : nat)
    (H_IN : b \in axiom_set X n)
    : b \in full_axiom_set X.

Lemma lemma2_of_1_3_9 (X : ensemble formula)
  : MaximalConsistentSet X \subseteq Th (full_axiom_set X).
Proof.
  intros z [n z_in].
  pose proof (proj1 (lemma1_of_1_3_9 X n z) z_in) as [INFERS].
  econstructor. eapply extend_infers; eauto. ii. now exists (n).
Qed.

Lemma lemma3_of_1_3_9_aux1 (xs : list formula) (X : ensemble formula)
  (FINITE_SUBSET : L.is_finsubset_of xs (full_axiom_set X))
  : exists m, L.is_finsubset_of xs (improveFilter (Th X) m).
Proof with eauto with *.
  revert X FINITE_SUBSET. induction xs as [ | x xs IH]; simpl; ii.
  - exists 0. tauto.
  - assert (claim1 : forall z : formula, In z xs -> z \in full_axiom_set X) by now firstorder.
    assert (claim2 : x \in full_axiom_set X) by now firstorder.
    inversion claim2.
    assert (claim3 : x \in improveFilter (Th X) n).
    { eapply lemma1_of_1_3_9. econstructor. eapply ByAssumption... }
    pose proof (IH X claim1) as [m claim4].
    assert (m <= n \/ n <= m) as [m_le_n | n_lt_m] by lia.
    + exists n. intros z [x_eq_z | z_in_xs].
      { subst z... }
      { eapply lemma1_of_1_2_12... }
    + exists m. intros z [x_eq_z | z_in_xs].
      { subst z. eapply lemma1_of_1_2_12... }
      { eapply claim4... }
Qed.

Lemma lemma3_of_1_3_9 (X : ensemble formula)
  : Th (full_axiom_set X) \subseteq MaximalConsistentSet X.
Proof with eauto with *.
  intros z [INFERS].
  pose proof (inference_is_finite (full_axiom_set X) z INFERS) as [xs [X' [xs_isFiniteSubsetOf [xs_isListRepOf INFERS']]]].
  pose proof (lemma3_of_1_3_9_aux1 xs X xs_isFiniteSubsetOf) as [m claim1].
  assert (claim2 : isFilter (improveFilter (Th X) m)).
  { eapply @lemma1_of_1_2_11 with (CBA := LindenbaumBooleanAlgebra). eapply lemma1_of_1_3_8. }
  inversion claim2. exists m. unnw.
  eapply CLOSED_UPWARD with (x := andsB xs).
  - eapply fact5_of_1_2_8... exists xs...
  - eapply andsB_le_iff. now firstorder.
Qed.

Variant MaximalConsistentSet_spec (X : ensemble formula) (F : ensemble formula) : Prop :=
  | MaximalConsistentSetSpec_areTheFollowings
    (SUBSET : Th X \subseteq F)
    (EQUICONSISTENT : equiconsistent (Th X) F)
    (CLOSED_infers : forall b : formula, b \in F <-> F ⊢ b)
    (META_DN : forall b : formula, << NEGATION : NegationF b \in F -> ContradictionF \in F >> -> b \in F)
    (IMPLICATION_FAITHFUL : forall b : formula, forall b' : formula, ImplicationF b b' \in F <-> << IMPLICATION : b \in F -> b' \in F >>)
    : MaximalConsistentSet_spec X F.

Theorem theorem_of_1_3_10 (X : ensemble formula)
  : MaximalConsistentSet_spec X (MaximalConsistentSet X).
Proof with eauto with *.
  pose proof (lemma1 := @lemma1_of_1_3_8).
  pose proof (theorem_of_1_2_14 (Th X) (lemma1 X)) as [? ? ? ?].
  fold (MaximalConsistentSet X) in SUBSET, IS_FILTER, COMPLETE, EQUICONSISTENT.
  assert (CLOSED_infers : forall b : formula, b \in MaximalConsistentSet X <-> MaximalConsistentSet X ⊢ b).
  { intros b. split; intros b_in.
    - enough (to_show : b \in Th (MaximalConsistentSet X)) by now inversion to_show.
      rewrite <- cl_eq_Th. eapply fact3_of_1_2_8...
    - eapply fact5_of_1_2_8... rewrite -> cl_eq_Th...
  }
  assert (META_DN : forall b : formula, (NegationF b \in MaximalConsistentSet X -> ContradictionF \in MaximalConsistentSet X) -> b \in MaximalConsistentSet X).
  { intros b NEGATION. eapply COMPLETE. split.
    - intros INCONSISTENT. eapply inconsistent_compatWith_isSubsetOf...
      transitivity (E.insert b (MaximalConsistentSet X)).
      + ii; right...
      + eapply fact3_of_1_2_8.
    - intros INCONSISTENT.
      assert (claim1 : E.insert b (MaximalConsistentSet X) ⊢ ContradictionF).
      { now eapply inconsistent_cl_iff. }
      exists (ContradictionF). split... eapply NEGATION, CLOSED_infers, NegationI... reflexivity.
  }
  assert (IMPLICATION_FAITHFUL : forall b : formula, forall b' : formula, ImplicationF b b' \in MaximalConsistentSet X <-> (b \in MaximalConsistentSet X -> b' \in MaximalConsistentSet X)).
  { intros b b'. split.
    - intros IMPLICATION b_in.
      eapply CLOSED_infers. eapply ImplicationE with (A := b).
      + eapply CLOSED_infers...
      + eapply CLOSED_infers...
    - intros IMPLICATION. eapply META_DN.
      intros H_in. eapply CLOSED_infers.
      assert (claim1 : E.insert (ImplicationF b b') (MaximalConsistentSet X) ⊢ ContradictionF).
      { eapply ContradictionI with (A := ImplicationF b b').
        - eapply ByAssumption. left...
        - eapply extend_infers with (Gamma := MaximalConsistentSet X).
          + eapply CLOSED_infers...
          + ii; right...
      }
      assert (claim2 : MaximalConsistentSet X ⊢ ConjunctionF b (NegationF b')).
      { eapply DisjunctionE with (A := b) (B := NegationF b).
        - eapply extend_infers with (Gamma := E.empty).
          + eapply Law_of_Excluded_Middle.
          + done!.
        - eapply DisjunctionE with (A := b') (B := NegationF b').
          + eapply extend_infers with (Gamma := E.empty).
            { eapply Law_of_Excluded_Middle. }
            { done!. }
          + eapply ContradictionE.
            eapply Cut_property with (A := ImplicationF b b').
            { eapply ImplicationI, ByAssumption. right; left... }
            { eapply extend_infers. exact claim1. ii; s!. tauto. }
          + eapply ConjunctionI.
            { eapply ByAssumption. right; left... }
            { eapply ByAssumption. left... }
        - eapply ContradictionE.
          eapply Cut_property with (A := ImplicationF b b').
          + eapply ImplicationI, ContradictionE.
            eapply ContradictionI with (A := b).
            { eapply ByAssumption. left... }
            { eapply ByAssumption. right; left... }
          + eapply extend_infers... ii; s!. tauto.
      }
      assert (claim3 : MaximalConsistentSet X ⊢ b).
      { eapply ConjunctionE1... }
      assert (claim4 : MaximalConsistentSet X ⊢ NegationF b').
      { eapply ConjunctionE2. exact claim2. }
      eapply ContradictionI with (A := b'); trivial.
      eapply CLOSED_infers, IMPLICATION, CLOSED_infers; trivial.
  }
  repeat (split; trivial).
Qed.

End CONSTRUCTIVE_FACTS.
