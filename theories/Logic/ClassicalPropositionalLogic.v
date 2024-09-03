Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Math.BooleanAlgebra.
Require Import PnV.Logic.PropositionalLogic.

Import PropositialLogicNotations.

#[local] Infix " \in " := E.In.
#[local] Infix " \subseteq " := E.subset.
#[local] Notation In := List.In.

#[local] Hint Resolve E.insert_monotonic : core.

Lemma ByAssumption_preserves (Gamma : ensemble formula) (C : formula)
  (ELEM : C \in Gamma)
  : Gamma ⊨ C.
Proof.
  eapply extend_entails with (Gamma := E.singleton C); done!.
Qed.

Lemma ContradictionI_preserves (Gamma : ensemble formula) (A : formula)
  (ENTAILS1 : Gamma ⊨ A)
  (ENTAILS2 : Gamma ⊨ NegationF A)
  : Gamma ⊨ ContradictionF.
Proof.
  ii. pose proof (ENTAILS1 e H) as claim1. pose proof (ENTAILS2 e H) as claim2. ss!.
Qed.

Lemma ContradictionE_preserves (Gamma : ensemble formula) (A : formula)
  (ENTAILS1 : Gamma ⊨ ContradictionF)
  : Gamma ⊨ A.
Proof.
  ii. ss!.
Qed.

Lemma NegationI_preserves (Gamma : ensemble formula) (A : formula)
  (ENTAILS1 : E.insert A Gamma ⊨ ContradictionF)
  : Gamma ⊨ NegationF A.
Proof.
  ii. eapply ENTAILS1; done!.
Qed.

Lemma NegationE_preserves (Gamma : ensemble formula) (A : formula)
  (ENTAILS1 : E.insert (NegationF A) Gamma ⊨ ContradictionF)
  : Gamma ⊨ A.
Proof.
  ii. eapply NNPP. ii. eapply ENTAILS1; done!.
Qed.

Lemma ConjunctionI_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
  (ENTAILS1 : Gamma ⊨ A)
  (ENTAILS2 : Gamma ⊨ B)
  : Gamma ⊨ ConjunctionF A B.
Proof.
  ii. simpl. split; [eapply ENTAILS1 | eapply ENTAILS2]; ss!.
Qed.

Lemma ConjunctionE1_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
  (ENTAILS1 : Gamma ⊨ ConjunctionF A B)
  : Gamma ⊨ A.
Proof.
  ii. eapply ENTAILS1; done!.
Qed.

Lemma ConjunctionE2_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
  (ENTAILS1 : Gamma ⊨ ConjunctionF A B)
  : Gamma ⊨ B.
Proof with (simpl in *; tauto) || eauto with *.
  ii. eapply ENTAILS1; done!.
Qed.

Lemma DisjunctionI1_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
  (ENTAILS1 : Gamma ⊨ A)
  : Gamma ⊨ DisjunctionF A B.
Proof.
  ii. left. eapply ENTAILS1; done!.
Qed.

Lemma DisjunctionI2_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
  (ENTAILS1 : Gamma ⊨ B)
  : Gamma ⊨ DisjunctionF A B.
Proof.
  ii. right. eapply ENTAILS1; done!.
Qed.

Lemma DisjunctionE_preserves (Gamma : ensemble formula) (A : formula) (B : formula) (C : formula)
  (ENTAILS1 : Gamma ⊨ DisjunctionF A B)
  (ENTAILS2 : E.insert A Gamma ⊨ C)
  (ENTAILS3 : E.insert B Gamma ⊨ C)
  : Gamma ⊨ C.
Proof.
  ii. unfold entails in ENTAILS1. simpl in ENTAILS1. destruct (ENTAILS1 e H) as [? | ?]; [eapply ENTAILS2 | eapply ENTAILS3]; done!.
Qed.

Lemma ImplicationI_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
  (ENTAILS1 : E.insert A Gamma ⊨ B)
  : Gamma ⊨ ImplicationF A B.
Proof.
  ii. eapply ENTAILS1; done!.
Qed.

Lemma ImplicationE_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
  (ENTAILS1 : Gamma ⊨ ImplicationF A B)
  (ENTAILS2 : Gamma ⊨ A)
  : Gamma ⊨ B.
Proof.
  ii. unfold entails in ENTAILS1. simpl in ENTAILS1. eapply ENTAILS1; done!.
Qed.

Lemma BiconditionalI_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
  (ENTAILS1 : E.insert A Gamma ⊨ B)
  (ENTAILS2 : E.insert B Gamma ⊨ A)
  : Gamma ⊨ BiconditionalF A B.
Proof.
  ii. split; i; [eapply ENTAILS1 | eapply ENTAILS2]; done!.
Qed.

Lemma BiconditionalE1_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
  (ENTAILS1 : Gamma ⊨ BiconditionalF A B)
  (ENTAILS2 : Gamma ⊨ A)
  : Gamma ⊨ B.
Proof.
  ii. unfold entails in ENTAILS1. simpl in ENTAILS1. eapply ENTAILS1; done!.
Qed.

Lemma BiconditionalE2_preserves (Gamma : ensemble formula) (A : formula) (B : formula)
  (ENTAILS1 : Gamma ⊨ BiconditionalF A B)
  (ENTAILS2 : Gamma ⊨ B)
  : Gamma ⊨ A.
Proof.
  ii. unfold entails in ENTAILS1. simpl in ENTAILS1. eapply ENTAILS1; done!.
Qed.

Theorem the_propositional_soundness_theorem (X : ensemble formula) (b : formula)
  (INFERS : X ⊢ b)
  : X ⊨ b.
Proof with eauto.
  induction INFERS.
  - eapply ByAssumption_preserves with (C := C)...
  - eapply ContradictionI_preserves with (A := A)...
  - eapply ContradictionE_preserves with (A := A)...
  - eapply NegationI_preserves with (A := A)...
  - eapply NegationE_preserves with (A := A)...
  - eapply ConjunctionI_preserves with (A := A) (B := B)...
  - eapply ConjunctionE1_preserves with (A := A) (B := B)...
  - eapply ConjunctionE2_preserves with (A := A) (B := B)...
  - eapply DisjunctionI1_preserves with (A := A) (B := B)...
  - eapply DisjunctionI2_preserves with (A := A) (B := B)...
  - eapply DisjunctionE_preserves with (A := A) (B := B) (C := C)...
  - eapply ImplicationI_preserves with (A := A) (B := B)...
  - eapply ImplicationE_preserves with (A := A) (B := B)...
  - eapply BiconditionalI_preserves with (A := A) (B := B)...
  - eapply BiconditionalE1_preserves with (A := A) (B := B)...
  - eapply BiconditionalE2_preserves with (A := A) (B := B)...
Qed.

Lemma hasModel_ifConsistent (X : ensemble formula)
  (CONSISTENT : X ⊬ ContradictionF)
  : X \subseteq MaximallyConsistentSet X /\ is_structure (MaximallyConsistentSet X).
Proof with first [eassumption | trivial]. (* Infinitely grateful for Sohn's advice! *)
  ii. set (X_dagger := MaximallyConsistentSet X).
  pose proof (theorem_of_1_3_10 X) as [? ? ? ? ?].
  fold X_dagger in SUBSET, EQUICONSISTENT, CLOSED_infers, META_DN, IMPLICATION_FAITHFUL.
  pose proof (theorem_of_1_2_14 (Th X) (lemma1_of_1_3_8 X)) as [SUBSET' IS_FILTER' COMPLETE' EQUICONSISTENT'].
  fold (MaximallyConsistentSet X) in SUBSET', IS_FILTER', COMPLETE', EQUICONSISTENT'.
  fold X_dagger in SUBSET', IS_FILTER', COMPLETE', EQUICONSISTENT'.
  pose proof (claim1 := Th_isSubsetOf_cl X).
  pose proof (claim2 := cl_isSubsetOf_Th X).
  assert (cl_eq_Th : cl X == Th X) by ss!.
  assert (claim3 : equiconsistent (cl X) X_dagger).
  { transitivity (Th X); trivial. now rewrite cl_eq_Th. }
  assert (claim4 : ~ inconsistent X_dagger).
  { intros INCONSISTENT. contradiction CONSISTENT. eapply inconsistent_cl_iff, claim3... }
  assert (claim5 : ~ inconsistent (cl X_dagger)).
  { intros INCONSISTENT. contradiction claim4. pose proof (fact5_of_1_2_8 X_dagger IS_FILTER').
    rewrite -> filters_is_inconsistent_iff... eapply extend_infers with (Gamma := cl X_dagger)...
    rewrite <- filters_is_inconsistent_iff... eapply fact1_of_1_2_8...
  }
  assert (
    forall i : propLetter,
    AtomF i \in X_dagger <-> evalFormula (E.preimage AtomF X_dagger) (AtomF i)
  ) as caseAtomF.
  { ii. change (AtomF i \in X_dagger <-> i \in E.preimage AtomF X_dagger). s!.
    rewrite CLOSED_infers. split.
    - intros INFERS. exists (AtomF i). split... rewrite CLOSED_infers...
    - intros [? [-> IN]]. rewrite <- CLOSED_infers...
  }
  assert (
    ContradictionF \in X_dagger <-> evalFormula (E.preimage AtomF X_dagger) ContradictionF
  ) as caseContradictionF.
  { simpl. rewrite CLOSED_infers, <- inconsistent_cl_iff. tauto. }
  assert (
    forall p1 : formula,
    forall IH1 : p1 \in X_dagger <-> evalFormula (E.preimage AtomF X_dagger) p1,
    NegationF p1 \in X_dagger <-> evalFormula (E.preimage AtomF X_dagger) (NegationF p1)
  ) as caseNegationF.
  { ii. simpl. rewrite <- IH1, CLOSED_infers. split.
    - intros INFERS H_in. contradiction claim5.
      eapply inconsistent_cl_iff. eapply ContradictionI with (A := p1)...
      eapply CLOSED_infers...
    - intros H_not_in.
      eapply CLOSED_infers, META_DN. unnw. intros H_in.
      eapply CLOSED_infers. eapply ContradictionI with (A := NegationF p1).
      + enough (claim6 : MaximallyConsistentSet X ⊢ ImplicationF p1 ContradictionF).
        { eapply NegationI. eapply ImplicationE with (A := p1).
          - eapply extend_infers... ss!.
          - eapply ByAssumption... ss!.
        }
        eapply CLOSED_infers, IMPLICATION_FAITHFUL. tauto.
      + eapply ByAssumption...
  }
  assert (
    forall p1 : formula,
    forall p2 : formula,
    forall IH1 : p1 \in X_dagger <-> evalFormula (E.preimage AtomF X_dagger) p1,
    forall IH2 : p2 \in X_dagger <-> evalFormula (E.preimage AtomF X_dagger) p2,
    ConjunctionF p1 p2 \in X_dagger <-> evalFormula (E.preimage AtomF X_dagger) (ConjunctionF p1 p2)
  ) as caseConjunctionF.
  { ii. simpl. rewrite <- IH1, <- IH2. split.
    - intros H_in. split.
      + eapply CLOSED_infers, ConjunctionE1, CLOSED_infers...
      + eapply CLOSED_infers, ConjunctionE2, CLOSED_infers...
    - intros [H_in1 H_in2].
      eapply CLOSED_infers, ConjunctionI; eapply CLOSED_infers...
  }
  assert (
    forall p1 : formula,
    forall p2 : formula,
    forall IH1 : p1 \in X_dagger <-> evalFormula (E.preimage AtomF X_dagger) p1,
    forall IH2 : p2 \in X_dagger <-> evalFormula (E.preimage AtomF X_dagger) p2,
    DisjunctionF p1 p2 \in X_dagger <-> evalFormula (E.preimage AtomF X_dagger) (DisjunctionF p1 p2)
  ) as caseDisjunctionF.
  { ii. simpl. rewrite <- IH1, <- IH2. split.
    - intros H_in. pose proof (classic (X_dagger ⊢ p1)) as [H_yes | H_no].
      + left. eapply CLOSED_infers...
      + right. eapply CLOSED_infers.
        eapply ImplicationE with (A := NegationF p1).
        { eapply DisjunctionE with (A := p1) (B := p2) (C := ImplicationF (NegationF p1) p2).
          - eapply CLOSED_infers...
          - eapply ImplicationI, ContradictionE. eapply ContradictionI with (A := p1).
            + eapply ByAssumption. right; left...
            + eapply ByAssumption. left...
          - eapply ImplicationI, ByAssumption. right; left...
        }
        { eapply CLOSED_infers, caseNegationF...
          simpl. rewrite <- IH1. intros H_false.
          apply CLOSED_infers in H_false... ss!.
        }
    - intros [H_in | H_in].
      + eapply CLOSED_infers, DisjunctionI1, CLOSED_infers...
      + eapply CLOSED_infers, DisjunctionI2, CLOSED_infers...
  }
  assert (
    forall p1 : formula,
    forall p2 : formula,
    forall IH1 : p1 \in X_dagger <-> evalFormula (E.preimage AtomF X_dagger) p1,
    forall IH2 : p2 \in X_dagger <-> evalFormula (E.preimage AtomF X_dagger) p2,
    ImplicationF p1 p2 \in X_dagger <-> evalFormula (E.preimage AtomF X_dagger) (ImplicationF p1 p2)
  ) as caseImplicationF.
  { ii. rewrite IMPLICATION_FAITHFUL. simpl. unnw. tauto. }
  assert (
    forall p1 : formula,
    forall p2 : formula,
    forall IH1 : p1 \in X_dagger <-> evalFormula (E.preimage AtomF X_dagger) p1,
    forall IH2 : p2 \in X_dagger <-> evalFormula (E.preimage AtomF X_dagger) p2,
    BiconditionalF p1 p2 \in X_dagger <-> evalFormula (E.preimage AtomF X_dagger) (BiconditionalF p1 p2)
  ) as caseBiconditionalF.
  { ii. simpl. transitivity (ImplicationF p1 p2 \in X_dagger /\ ImplicationF p2 p1 \in X_dagger).
    { split.
      - intros H_in. split.
        { eapply CLOSED_infers, ImplicationI. eapply BiconditionalE1 with (A := p1) (B := p2).
          - eapply extend_infers with (Gamma := X_dagger)...
            eapply CLOSED_infers... ss!.
          - eapply ByAssumption. left...
        }
        { eapply CLOSED_infers, ImplicationI. eapply BiconditionalE2 with (A := p1) (B := p2).
          - eapply extend_infers with (Gamma := X_dagger)...
            eapply CLOSED_infers... ss!.
          - eapply ByAssumption. left...
        }
      - intros [H_in1 H_in2].
        eapply CLOSED_infers, BiconditionalI.
        { eapply ImplicationE with (A := p1).
          - eapply extend_infers with (Gamma := X_dagger)...
            eapply CLOSED_infers... ss!.
          - eapply ByAssumption. left...
        }
        { eapply ImplicationE with (A := p2).
          - eapply extend_infers with (Gamma := X_dagger)...
            eapply CLOSED_infers... ss!.
          - eapply ByAssumption. left...
        }
    }
    { split.
      - intros [H_in1 H_in2]. eapply caseImplicationF in H_in1, H_in2... ss!.
      - intros [H_in1 H_in2]. eapply caseImplicationF in H_in1, H_in2... ss!.
    }
  }
  split.
  { transitivity (Th X)... ii. econstructor. eapply ByAssumption... }
  { unfold is_structure. induction p; done!. }
Qed.

Theorem the_propositional_completeness_theorem (Gamma : ensemble formula) (C : formula)
  (ENTAILS : Gamma ⊨ C)
  : Gamma ⊢ C.
Proof with eauto with *.
  eapply NNPP. intros it_is_false_that_Gamma_infers_C.
  set (X := E.insert (NegationF C) Gamma).
  assert (CONSISTENT : X ⊬ ContradictionF).
  { intros INCONSISTENT. contradiction it_is_false_that_Gamma_infers_C. eapply NegationE... }
  pose proof (theorem_of_1_2_14 (Th X) (lemma1_of_1_3_8 X)) as [SUBSET' IS_FILTER' COMPLETE' EQUICONSISTENT'].
  fold (MaximallyConsistentSet X) in SUBSET', IS_FILTER', COMPLETE', EQUICONSISTENT'.
  pose proof (hasModel_ifConsistent X CONSISTENT) as [INCL IS_STRUCTURE].
  unfold is_structure in IS_STRUCTURE.
  pose proof (theorem_of_1_3_10 Gamma) as [? ? ? ? ?]; unnw.
  contradiction it_is_false_that_Gamma_infers_C.
  eapply completeness_theorem_prototype with (env := E.preimage AtomF (MaximallyConsistentSet X)); trivial.
  - unfold equiconsistent in *.
    transitivity (inconsistent (MaximallyConsistentSet X))...
    split; intros [botB [botB_in botB_eq_falseB]].
    + exists botB. split... eapply IS_STRUCTURE...
    + exists botB. split... eapply IS_STRUCTURE...
  - transitivity (MaximallyConsistentSet X)...
    ii. eapply IS_STRUCTURE...
  - eapply isFilter_compatWith_eqProp...
Qed.

Corollary the_propositional_compactness_theorem (Gamma : ensemble formula) (C : formula)
  : Gamma ⊨ C <-> << FINITE_ENTAILS : exists xs, exists X, L.is_finsubset_of xs Gamma /\ L.is_listrep_of xs X /\ X ⊨ C >>.
Proof with eauto.
  unnw. split.
  - intros ENTAILS.
    apply the_propositional_completeness_theorem in ENTAILS.
    apply inference_is_finite in ENTAILS. des. exists (xs), (X').
    split... split... eapply the_propositional_soundness_theorem...
  - i; des. eapply extend_entails... now firstorder.
Qed.
