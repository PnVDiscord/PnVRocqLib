Require Import PnV.Prelude.Prelude.

#[local] Infix " \in " := E.In.
#[local] Infix " \subseteq " := E.subset.
#[local] Notation In := List.In.

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

Fixpoint evalFormula (e : propLetter -> Prop) (p : formula) {struct p} : Prop :=
  match p with
  | AtomF i => e i
  | ContradictionF => False
  | NegationF p1 => ~ evalFormula e p1
  | ConjunctionF p1 p2 => evalFormula e p1 /\ evalFormula e p2
  | DisjunctionF p1 p2 => evalFormula e p1 \/ evalFormula e p2
  | ImplicationF p1 p2 => evalFormula e p1 -> evalFormula e p2
  | BiconditionalF p1 p2 => evalFormula e p1 <-> evalFormula e p2
  end.

Section PROPOSITONAL_LOGIC.

Definition entails (Gamma : ensemble formula) (C : formula) : Prop :=
  forall e : propLetter -> Prop, (forall H : formula, H \in Gamma -> evalFormula e H) -> evalFormula e C.

Infix "⊨" := entails.

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

#[local] Hint Resolve E.insert_monotonic : core.

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
  unnw.  revert C.
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

End PROPOSITONAL_LOGIC.
