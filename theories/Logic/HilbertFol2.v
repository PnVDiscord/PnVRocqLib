Require Import PnV.Prelude.Prelude.
Require Import PnV.Data.Vector.
Require Import PnV.Math.BooleanAlgebra.
Require Import PnV.Logic.BasicFol.
Require Import PnV.Logic.BasicFol2.
Require Import PnV.Logic.HilbertFol.
Require Import PnV.Math.ThN.

Import ListNotations.
Import FolNotations.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.
#[local] Notation In := L.In.

Module FolHilbert.

Infix "⊢" := HilbertFol.proves : type_scope.
Notation "Gamma ⊬ C" := (~ Gamma ⊢ C) : type_scope.

Notation inconsistent' := BooleanAlgebra.inconsistent.

Section EXTRA1.

Lemma extend_alpha_proves {L : language} (Gamma : ensemble (frm L)) (Gamma' : ensemble (frm L)) (C : frm L)
  (SUBSET : forall p : frm L, forall IN : p \in Gamma, exists p' : frm L, p ≡ p' /\ p' \in Gamma')
  (PROVE : Gamma ⊢ C)
  : Gamma' ⊢ C.
Proof.
  destruct PROVE as (ps&INCL&(PF)).
  assert (PROVE : E.fromList ps ⊢ C).
  { exists ps. split. done. econs. exact PF. }
  clear PF. revert Gamma Gamma' C SUBSET INCL PROVE. induction ps as [ | p ps IH]; simpl; i.
  - eapply extend_proves with (Gamma := E.fromList []). done. exact PROVE.
  - exploit (SUBSET p). done!. intros (p'&ALPHA&IN). eapply for_Imp_E with (p := p').
    + eapply IH with (Gamma := Gamma).
      * intros q q_in. exploit (SUBSET q); trivial.
      * done!.
      * rewrite <- ALPHA. rewrite Deduction_theorem. eapply extend_proves with (Gamma := E.fromList (p :: ps)); trivial. done!.
    + eapply for_ByHyp; trivial.
Qed.

Definition inconsistent {L : language} (Gamma : ensemble (frm L)) : Prop :=
  forall p, Gamma ⊢ p.

Context {L : language}.

Lemma extend_infers (Gamma : ensemble (frm L)) (Gamma' : ensemble (frm L)) (C : frm L)
  (INFERS : Gamma ⊢ C)
  (SUBSET : Gamma \subseteq Gamma')
  : Gamma' ⊢ C.
Proof.
  eapply extend_proves; eauto.
Qed.

Lemma ByAssumption (Gamma : ensemble (frm L)) C
  (IN : C \in Gamma)
  : Gamma ⊢ C.
Proof.
  eapply for_ByHyp; trivial.
Qed.

Lemma ContradictionI (Gamma : ensemble (frm L)) A
  (INFERS1 : Gamma ⊢ A)
  (INFERS2 : Gamma ⊢ Neg_frm A)
  : Gamma ⊢ Bot_frm.
Proof.
  eapply for_Imp_E. eapply for_Imp_E. exists []. split. done. econs. eapply proof_ex_falso. exact INFERS2. exact INFERS1.
Qed.

Lemma ContradictionE (Gamma : ensemble (frm L)) A
  (INFERS1 : Gamma ⊢ Bot_frm)
  : Gamma ⊢ A.
Proof.
  eapply for_Imp_E with (p := All_frm 0 (Eqn_frm (Var_trm 0) (Var_trm 0))).
  - eapply for_Imp_E with (p := Bot_frm).
    + exists []. split. done. econs. eapply proof_ex_falso.
    + eapply INFERS1.
  - eapply extend_proves with (Gamma := E.empty). done. eapply for_All_I. done. eapply proves_reflexivity.
Qed.

Lemma NegationI (Gamma : ensemble (frm L)) A
  (INFERS1 : E.insert A Gamma ⊢ Bot_frm)
  : Gamma ⊢ Neg_frm A.
Proof.
  rewrite <- Deduction_theorem in INFERS1. eapply for_Imp_E. 2: exact INFERS1. eapply for_compose.
  - eapply for_CP1. eapply INFERS1.
  - eapply for_Imp_I. eapply for_Imp_E.
    + exists []. split. done. econs. eapply proof_dni.
    + eapply extend_proves with (Gamma := E.empty). done. eapply for_All_I. done. eapply proves_reflexivity.
Qed.

Lemma NegationE (Gamma : ensemble (frm L)) A
  (INFERS1 : E.insert (Neg_frm A) Gamma ⊢ Bot_frm)
  : Gamma ⊢ A.
Proof.
  eapply for_Imp_E. exists []. split. done. econs. eapply proof_dne. eapply NegationI. exact INFERS1.
Qed.

Lemma ConjunctionI (Gamma : ensemble (frm L)) A B
  (INFERS1 : Gamma ⊢ A)
  (INFERS2 : Gamma ⊢ B)
  : Gamma ⊢ Con_frm A B.
Proof.
  unfold Con_frm. eapply NegationI. eapply ContradictionI with (A := B).
  - eapply extend_proves with (Gamma := Gamma). done!. eapply INFERS2.
  - eapply for_Imp_E with (p := A). eapply ByAssumption. done!. eapply extend_proves with (Gamma := Gamma). done!. eapply INFERS1.
Qed.

Lemma ConjunctionE1 (Gamma : ensemble (frm L)) A B
  (INFERS1 : Gamma ⊢ Con_frm A B)
  : Gamma ⊢ A.
Proof.
  eapply for_Imp_E. exists []. split. done. econs. eapply proof_dne. unfold Con_frm in INFERS1. eapply for_Imp_E. 2: exact INFERS1.
  eapply for_CP1. eapply for_Imp_I. eapply for_Imp_I. eapply NegationI. eapply ContradictionI with (A := A); eapply for_ByHyp; done!.
Qed.

Lemma ConjunctionE2 (Gamma : ensemble (frm L)) A B
  (INFERS1 : Gamma ⊢ Con_frm A B)
  : Gamma ⊢ B.
Proof.
  eapply for_Imp_E. exists []. split. done. econs. eapply proof_dne. unfold Con_frm in INFERS1. eapply for_Imp_E. 2: exact INFERS1.
  eapply for_CP1. eapply for_Imp_I. eapply for_Imp_I. eapply NegationI. eapply ContradictionI with (A := B); eapply for_ByHyp; done!.
Qed.

Lemma DisjunctionI1 (Gamma : ensemble (frm L)) A B
  (INFERS1 : Gamma ⊢ A)
  : Gamma ⊢ Dis_frm A B.
Proof.
  unfold Dis_frm. eapply NegationI. eapply ContradictionI with (A := A).
  - eapply extend_proves with (Gamma := Gamma); done!.
  - eapply ConjunctionE1. eapply ByAssumption. left. reflexivity.
Qed.

Lemma DisjunctionI2 (Gamma : ensemble (frm L)) A B
  (INFERS1 : Gamma ⊢ B)
  : Gamma ⊢ Dis_frm A B.
Proof.
  unfold Dis_frm. eapply NegationI. eapply ContradictionI with (A := B).
  - eapply extend_proves with (Gamma := Gamma); done!.
  - eapply ConjunctionE2. eapply ByAssumption. left. reflexivity.
Qed.

Lemma DisjunctionE (Gamma : ensemble (frm L)) A B C
  (INFERS1 : Gamma ⊢ Dis_frm A B)
  (INFERS2 : E.insert A Gamma ⊢ C)
  (INFERS3 : E.insert B Gamma ⊢ C)
  : Gamma ⊢ C.
Proof.
  eapply for_Imp_E. exists []. split. done. econs. eapply proof_dne.
  eapply NegationI. unfold Dis_frm in INFERS1. eapply ContradictionI with (A := Con_frm (Neg_frm A) (Neg_frm B)).
  - eapply ConjunctionI; rewrite <- Deduction_theorem; eapply for_CP1; eapply for_Imp_I; trivial.
  - eapply extend_infers with (Gamma := Gamma); done!.
Qed.

Lemma ImplicationI (Gamma : ensemble (frm L)) A B
  (INFERS1 : E.insert A Gamma ⊢ B)
  : Gamma ⊢ Imp_frm A B.
Proof.
  eapply for_Imp_I; trivial.
Qed.

Lemma ImplicationE (Gamma : ensemble (frm L)) A B
  (INFERS1 : Gamma ⊢ Imp_frm A B)
  (INFERS2 : Gamma ⊢ A)
  : Gamma ⊢ B.
Proof.
  eapply for_Imp_E; eauto.
Qed.

Lemma BiconditionalI (Gamma : ensemble (frm L)) A B
  (INFERS1 : E.insert A Gamma ⊢ B)
  (INFERS2 : E.insert B Gamma ⊢ A)
  : Gamma ⊢ Iff_frm A B.
Proof.
  unfold Iff_frm. eapply ConjunctionI; eapply for_Imp_I; eauto.
Qed.

Lemma BiconditionalE1 (Gamma : ensemble (frm L)) A B
  (INFERS1 : Gamma ⊢ Iff_frm A B)
  (INFERS2 : Gamma ⊢ A)
  : Gamma ⊢ B.
Proof.
  unfold Iff_frm in INFERS1. eapply for_Imp_E. eapply ConjunctionE1. eapply INFERS1. eapply INFERS2.
Qed.

Lemma BiconditionalE2 (Gamma : ensemble (frm L)) A B
  (INFERS1 : Gamma ⊢ Iff_frm A B)
  (INFERS2 : Gamma ⊢ B)
  : Gamma ⊢ A.
Proof.
  unfold Iff_frm in INFERS1. eapply for_Imp_E. eapply ConjunctionE2. eapply INFERS1. eapply INFERS2.
Qed.

Lemma UniversalI (Gamma : ensemble (frm L)) x y A
  (FRESH1 : forall p, p \in Gamma -> is_free_in_frm y p = false)
  (FRESH2 : is_free_in_frm y (All_frm x A) = false)
  (INFERS1 : Gamma ⊢ subst_frm (one_subst x (Var_trm y)) A)
  : Gamma ⊢ All_frm x A.
Proof.
  eapply for_All_I' with (y := y); ss!.
Qed.

Lemma UniversalE (Gamma : ensemble (frm L)) x t A
  (INFERS1 : Gamma ⊢ All_frm x A)
  : Gamma ⊢ subst_frm (one_subst x t) A.
Proof.
  eapply for_All_E with (t := t); ss!.
Qed.

Lemma ExistentialI (Gamma : ensemble (frm L)) x t A
  (INFERS1 : Gamma ⊢ subst_frm (one_subst x t) A)
  : Gamma ⊢ Exs_frm x A.
Proof.
  unfold Exs_frm. eapply NegationI. eapply ContradictionI with (A := subst_frm (one_subst x t) (Neg_frm A)).
  - eapply for_All_E. eapply for_ByHyp. done!.
  - simpl. eapply NegationI. eapply ContradictionI with (A := subst_frm (one_subst x t) A).
    + eapply extend_infers. eapply INFERS1. done!.
    + eapply for_ByHyp. done!.
Qed.

Lemma ExistentialE (Gamma : ensemble (frm L)) x y A B
  (FRESH1 : forall p, p \in Gamma -> is_free_in_frm y p = false)
  (FRESH2 : is_free_in_frm y (Exs_frm x A) = false)
  (FRESH3 : is_free_in_frm y B = false)
  (INFERS1 : Gamma ⊢ Exs_frm x A)
  (INFERS2 : E.insert (subst_frm (one_subst x (Var_trm y)) A) Gamma ⊢ B)
  : Gamma ⊢ B.
Proof.
  assert (claim : Gamma ⊢ Imp_frm (Neg_frm B) (All_frm x (Neg_frm A))).
  { eapply for_Imp_I. eapply for_All_I' with (y := y).
    - intros p [-> | IN]; simpl; ss!.
    - ss!.
    - simpl. rewrite <- Deduction_theorem. eapply for_CP1. rewrite -> Deduction_theorem. eapply INFERS2.
  }
  apply for_CP1 in claim. eapply for_Imp_E. exists []. split. done. econs. eapply proof_dne.
  eapply for_Imp_E. eapply claim. exact INFERS1.
Qed.

Lemma EquationI (Gamma : ensemble (frm L)) t
  : Gamma ⊢ Eqn_frm t t.
Proof.
  eapply proves_reflexivity.
Qed.

Lemma EquationE (Gamma : ensemble (frm L)) x t1 t2 A
  (INFERS1 : Gamma ⊢ Eqn_frm t1 t2)
  (INFERS2 : Gamma ⊢ subst_frm (one_subst x t1) A)
  : Gamma ⊢ subst_frm (one_subst x t2) A.
Proof.
  eapply for_Imp_E. 2: eapply INFERS2. eapply proves_eqn_frm. eapply INFERS1.
Qed.

Lemma Law_of_Excluded_Middle (A : frm L)
  : E.empty ⊢ Dis_frm A (Neg_frm A).
Proof with repeat ((now left) || right).
  eapply NegationE, ContradictionI.
  - eapply DisjunctionI2, NegationI, ContradictionI.
    + eapply DisjunctionI1, ByAssumption...
    + eapply ByAssumption...
  - eapply ByAssumption...
Qed.

Lemma Cut_property (Gamma : ensemble (frm L)) A B
  (INFERS : Gamma ⊢ A)
  (IMPLY : E.insert A Gamma ⊢ B)
  : Gamma ⊢ B.
Proof.
  assert (claim : Gamma ⊢ Imp_frm A B).
  { eapply ImplicationI; exact IMPLY. }
  eapply ImplicationE; [exact claim | exact INFERS].
Qed.

#[local] Notation formula := (frm L).

#[global]
Instance formula_isBA : isBA formula :=
  { andB := Con_frm
  ; orB := Dis_frm
  ; notB := Neg_frm
  ; trueB := Imp_frm Bot_frm Bot_frm
  ; falseB := Bot_frm
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
    - intros ? [].
  }
Qed.

Lemma leB_iff (lhs : formula) (rhs : formula)
  : lhs =< rhs <-> E.singleton lhs ⊢ rhs.
Proof with reflexivity || trivial.
  simpl. split.
  - intros [INFERS INFERS'].
    eapply Cut_property with (A := Con_frm lhs rhs)...
    eapply ConjunctionE2, ByAssumption. left...
  - intros INFERS. split.
    + eapply ConjunctionE1, ByAssumption...
    + eapply ConjunctionI...
      eapply ByAssumption...
Qed.

Lemma andsB_le_iff (xs : list formula) (b : formula)
  : andsB xs =< b <-> (exists X, L.is_listrep_of xs X /\ X ⊢ b).
Proof.
  split.
  - intros LE. exists (E.fromList xs). split. done. revert b LE. induction xs as [ | x xs IH]; simpl; i.
    + destruct LE as [INFERS1 INFERS2]. eapply Cut_property with (A := Imp_frm Bot_frm Bot_frm).
      * eapply ImplicationI. eapply for_ByHyp. done!.
      * eapply extend_infers with (Gamma := E.singleton (Imp_frm Bot_frm Bot_frm)).
        { eapply ConjunctionE2. eapply INFERS2. }
        { done!. }
    + destruct LE as [INFERS1 INFERS2]. unfold leProp in IH. simpl in IH. eapply extend_proves with (Gamma := E.insert x (E.fromList xs)). done!.
      rewrite <- Deduction_theorem. eapply IH. split.
      * eapply ConjunctionE1. eapply ByAssumption. econs.
      * eapply ConjunctionI.
        { eapply ByAssumption. done!. }
        { eapply ImplicationI. eapply ConjunctionE2 with (A := Con_frm x (andsB xs)). eapply for_Imp_E with (p := Con_frm x (andsB xs)).
          - eapply for_Imp_I. eapply extend_infers. exact INFERS2. done!.
          - eapply ConjunctionI; eapply for_ByHyp; done!.
        }
  - intros (X&EQ&PROVE). destruct PROVE as (ps&INCL&(PF)).
    assert (SUBSET : forall q, L.In q ps -> L.In q xs) by ss!.
    assert (LE : andsB ps =< b).
    { simpl. split.
      - eapply ConjunctionE1; eapply for_ByHyp; done!.
      - eapply ConjunctionI.
        + eapply for_ByHyp; done!.
        + assert (PROVE : E.fromList ps ⊢ b).
          { exists ps. split. done!. econs. exact PF. }
          revert PROVE. clear. revert b. induction ps as [ | p ps IH]; simpl; i.
          * eapply extend_infers. eapply PROVE. intros ? [].
          * exploit (IH (Imp_frm p b)).
            { eapply for_Imp_I. eapply extend_infers. exact PROVE. done!. }
            intros claim. rewrite Deduction_theorem in claim.
            eapply for_Imp_E with (p := p); cycle 1. eapply ConjunctionE1; eapply for_ByHyp; done!.
            eapply for_Imp_E with (p := andsB ps); cycle 1. eapply ConjunctionE2; eapply for_ByHyp; done!.
            eapply for_Imp_E with (p := Con_frm p (andsB ps)); cycle 1. eapply for_ByHyp; done!.
            eapply for_Imp_I. eapply for_Imp_I. eapply for_Imp_I. eapply extend_infers. eapply claim. done!.
    }
    clear X INCL EQ PF. revert b LE.
    enough (WTS : andsB xs =< andsB ps).
    { ii. etransitivity; eauto. }
    rewrite leB_iff. revert xs SUBSET. induction ps as [ | p ps IH]; simpl; i.
    + eapply for_Imp_I. eapply for_ByHyp. done!.
    + exploit (IH xs). done!. intros claim. eapply ConjunctionI; trivial.
      exploit (SUBSET p). done!. clear. revert p. induction xs as [ | x xs IH]; simpl; intros p IN.
      * tauto.
      * destruct IN as [<- | IN].
        { eapply ConjunctionE1. eapply for_ByHyp; done!. }
        { eapply for_Imp_E; cycle 1. eapply ConjunctionE1. eapply for_ByHyp; econs.
          eapply for_Imp_E; cycle 1. eapply ConjunctionE2. eapply for_ByHyp; econs.
          eapply for_Imp_I. eapply for_Imp_I. eapply extend_infers. exact (IH p IN). done!.
        }
Qed.

#[global]
Add Parametric Morphism :
  (@proves L) with signature (eqProp ==> eqProp ==> iff)
  as proves_compatWith_eqProp.
Proof.
  intros X X' X_eq_X' b b' [INFERS1 INFERS2]. split.
  - intros INFERS. eapply Cut_property with (A := b).
    + eapply extend_infers; done!.
    + eapply extend_infers; done!.
  - intros INFERS. eapply Cut_property with (A := b').
    + eapply extend_infers; done!.
    + eapply extend_infers; done!.
Qed.

Variant Th (X : ensemble formula) (b : formula) : Prop :=
  | In_Th
    (INFERS : X ⊢ b)
    : b \in Th X.

#[local] Hint Constructors Th : core.

Lemma in_Th_iff (X : ensemble formula) (b : formula)
  : b \in Th X <-> X ⊢ b.
Proof.
  split; eauto. intros [?]; trivial.
Qed.

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

Lemma inconsistent_iff (Gamma : ensemble (frm L))
  : inconsistent Gamma <-> Gamma ⊢ Bot_frm.
Proof.
  split.
  - intros INCONSISTENT. eapply INCONSISTENT.
  - intros INCONSISTENT q. eapply ContradictionE. eapply INCONSISTENT.
Qed.

Corollary Th_isSubsetOf_cl (X : ensemble formula)
  : Th X \subseteq cl X.
Proof.
  intros b [PROVE]. destruct PROVE as (ps&INCL&(PF)). exists ps. split; unnw.
  - done.
  - rewrite andsB_le_iff. exists (E.intersection (E.fromList ps) X). split.
    + done!.
    + eapply extend_proves with (Gamma := E.fromList ps). done!. exists ps. split. done. econs. exact PF.
Qed.

Corollary cl_eq_Th (X : ensemble formula)
  : cl X == Th X.
Proof.
  s!. split.
  - eapply cl_isSubsetOf_Th.
  - eapply Th_isSubsetOf_cl.
Qed.

Lemma inconsistent_cl_iff (X : ensemble (frm L))
  : Bot_frm \in cl X <-> X ⊢ Bot_frm.
Proof.
  split.
  - intros IN. rewrite cl_eq_Th in IN. destruct IN as [INFERS]. exact INFERS.
  - intros INFERS. rewrite cl_eq_Th. econs. exact INFERS.
Qed.

Lemma filter_inconsistent_iff (F : ensemble formula)
  (F_isFilter : isFilter F)
  : inconsistent F <-> Bot_frm \in F.
Proof with eauto with *.
  split.
  - intros INCONSISTENT. pose proof (fact5_of_1_2_8 F F_isFilter) as SUBSET.
    eapply SUBSET. rewrite inconsistent_cl_iff. now rewrite <- inconsistent_iff.
  - intros IN. pose proof (fact3_of_1_2_8 F) as SUBSET.
    rewrite inconsistent_iff. rewrite <- inconsistent_cl_iff. now eapply SUBSET.
Qed.

Lemma inconsistent_okay (Gamma : ensemble (frm L))
  : inconsistent Gamma <-> inconsistent' (cl Gamma).
Proof.
  unfold inconsistent'. rewrite inconsistent_iff. split.
  - intros INFERS. exists Bot_frm. split; try reflexivity.
    rewrite cl_eq_Th. econs; trivial.
  - intros [botB [IN EQ]].
    enough (WTS : Bot_frm \in Th Gamma).
    { destruct WTS; trivial. }
    simpl in *. rewrite cl_eq_Th in IN. destruct EQ as [INFERS _].
    econs. eapply cut_one with (A := botB); trivial. destruct IN as [PROVE]; trivial.
Qed.

Section UNION.

Variable f : nat -> ensemble (frm L).

Definition union_f : ensemble (frm L) :=
  fun p => exists n, p \in f n.

Hypothesis incl : forall n1 : nat, forall n2 : nat, forall LE : n1 <= n2, f n1 \subseteq f n2.

Lemma subset_union_f n
  : f n \subseteq union_f.
Proof.
  intros q q_in. exists n. exact q_in.
Qed.

Lemma union_f_proves_iff p
  : union_f ⊢ p <-> (exists n, f n ⊢ p).
Proof.
  split.
  - intros (ps&INCL&(PF)).
    enough (WTS : exists n, E.fromList ps \subseteq f n).
    { destruct WTS as [n SUBSET]. exists n. exists ps. split; trivial. econs; exact PF. }
    clear PF p. induction ps as [ | p ps IH]; simpl.
    + exists 0. done.
    + exploit IH. ii. eapply INCL. done!. intros [n SUBSET]. exploit (INCL p). done!. intros [m IN].
      exists (max n m). intros q q_in. s!. destruct q_in as [-> | q_in].
      * eapply incl with (n1 := m); done!.
      * eapply incl with (n1 := n); done!.
  - intros [n PROVE]. eapply extend_proves with (Gamma := f n). eapply subset_union_f. exact PROVE.
Qed.

Hypothesis equiconsistent : forall n : nat, inconsistent (f n) <-> inconsistent (f (S n)).

Lemma equiconsistent_union_f
  : inconsistent (f 0) <-> inconsistent union_f.
Proof.
  split.
  - intros INCONSISTENT p. eapply extend_proves with (Gamma := f 0). eapply subset_union_f. eapply INCONSISTENT.
  - do 2 rewrite inconsistent_iff. intros INCONSISTENT. rewrite union_f_proves_iff in INCONSISTENT. destruct INCONSISTENT as [n PROVE]. induction n as [ | n IH].
    + eapply PROVE.
    + eapply IH. rewrite <- inconsistent_iff. rewrite equiconsistent. rewrite inconsistent_iff. eapply PROVE.
Qed.

End UNION.

#[local] Hint Resolve fact1_of_1_2_8 fact2_of_1_2_8 fact3_of_1_2_8 fact4_of_1_2_8 fact5_of_1_2_8 lemma1_of_1_2_11 : core.

Context {enum_frm_L : isEnumerable formula}.

#[global]
Instance LindenbaumBooleanAlgebra : isCBA formula (SETOID := formula_isSetoid) :=
  { CBA_isBA := formula_isBA
  ; CBA_satisfiesBooleanAlgebraLaws := LBA_satisfiesBooleanAlgebraLaws 
  ; CBA_countable := enum_frm_L
  }.

Fixpoint axiom_set (X : ensemble formula) (n : nat) {struct n} : ensemble formula :=
  match n with
  | O => X
  | S n => E.union (axiom_set X n) (insertion (improveFilter (Th X) n) n)
  end.

Lemma lemma1_of_1_3_9 (X : ensemble formula) (n : nat)
  : improveFilter (Th X) n == Th (axiom_set X n).
Proof with eauto with *.
  revert X; induction n as [ | n IH]; [reflexivity | intros X b].
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

Lemma axiom_set_equiconsistent (X : ensemble (frm L)) (n : nat)
  : inconsistent (axiom_set X n) <-> inconsistent (axiom_set X (S n)).
Proof with eauto with *.
  split.
  - do 2 rewrite inconsistent_iff. intros INCONSISTENT. eapply extend_infers... done!.
  - do 2 rewrite inconsistent_iff. do 2 rewrite <- in_Th_iff. intros INCONSISTENT.
    rewrite <- lemma1_of_1_3_9 in *. pose proof (lemma2_of_1_2_13 (Th X)) as claim. eapply fact5_of_1_2_8.
    + eapply @lemma1_of_1_2_11 with (CBA := LindenbaumBooleanAlgebra). eapply lemma1_of_1_3_8.
    + rewrite cl_eq_Th. rewrite in_Th_iff. rewrite <- inconsistent_iff. rewrite inconsistent_okay. rewrite cl_eq_Th.
      enough (WTS : inconsistent' (improveFilter (Th X) n)).
      { eapply inconsistent_compatWith_isSubsetOf... ii. rewrite in_Th_iff. eapply ByAssumption... }
      eapply claim with (n2 := S n).
      * eapply lemma1_of_1_3_8.
      * enough (INFERS : improveFilter (Th X) (S n) ⊢ Bot_frm).
        { rewrite <- inconsistent_iff in INFERS. rewrite inconsistent_okay in INFERS.
          eapply inconsistent_compatWith_isSubsetOf with (X := cl (improveFilter (Th X) (S n)))...
          eapply fact5_of_1_2_8... eapply @lemma1_of_1_2_11 with (CBA := LindenbaumBooleanAlgebra). eapply lemma1_of_1_3_8.
        }
        simpl in INCONSISTENT. rewrite cl_eq_Th in INCONSISTENT. rewrite in_Th_iff in INCONSISTENT. simpl.
        eapply extend_infers...
Qed.

Definition MaximallyConsistentSet (X : ensemble formula) : ensemble formula :=
  completeFilterOf (Th X).

Definition full_axiom_set (X : ensemble formula) : ensemble formula :=
  union_f (axiom_set X).

Lemma lemma2_of_1_3_9 (X : ensemble formula)
  : MaximallyConsistentSet X \subseteq Th (full_axiom_set X).
Proof.
  intros z [n z_in].
  pose proof (proj1 (lemma1_of_1_3_9 X n z) z_in) as [INFERS].
  econstructor. eapply extend_infers; eauto. ii. now exists n.
Qed.

Lemma lemma3_of_1_3_9_aux1 (xs : list formula) (X : ensemble formula)
  (FINITE_SUBSET : L.is_finsubset_of xs (full_axiom_set X))
  : exists m, L.is_finsubset_of xs (improveFilter (Th X) m).
Proof with eauto with *.
  revert X FINITE_SUBSET. induction xs as [ | x xs IH]; simpl; ii.
  - exists 0. tauto.
  - assert (claim1 : forall z : formula, In z xs -> z \in full_axiom_set X) by now firstorder.
    assert (claim2 : x \in full_axiom_set X) by now firstorder.
    destruct claim2 as [n IN].
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
  : Th (full_axiom_set X) \subseteq MaximallyConsistentSet X.
Proof with eauto with *.
  intros z [INFERS]. destruct INFERS as (ps&INCL&(PF)).
  pose proof (lemma3_of_1_3_9_aux1 ps X INCL) as [m claim1].
  assert (claim2 : isFilter (improveFilter (Th X) m)).
  { eapply @lemma1_of_1_2_11 with (CBA := LindenbaumBooleanAlgebra). eapply lemma1_of_1_3_8. }
  inversion claim2. exists m.
  eapply CLOSED_UPWARD with (x := andsB ps).
  - eapply fact5_of_1_2_8... exists ps...
  - eapply andsB_le_iff. exists (E.intersection (E.fromList ps) (improveFilter (Th X) m)). split; done!.
Qed.

Variant MaximallyConsistentSet_spec (X : ensemble formula) (F : ensemble formula) : Prop :=
  | MaximallyConsistentSetSpec_areTheFollowings
    (SUBSET : Th X \subseteq F)
    (EQUICONSISTENT : equiconsistent (Th X) F)
    (CLOSED_infers : forall A : formula, A \in F <-> F ⊢ A)
    (META_DN : forall A : formula, << NEGATION : Neg_frm A \in F -> Bot_frm \in F >> -> A \in F)
    (IMPLICATION_FAITHFUL : forall A : formula, forall B : formula, Imp_frm A B \in F <-> << IMPLICATION : A \in F -> B \in F >>)
    (FORALL_FAITHFUL : forall x : ivar, forall A : formula, All_frm x A \in F <-> << FORALL : forall t : trm L, subst_frm (one_subst x t) A \in F >>)
    : MaximallyConsistentSet_spec X F.

End EXTRA1.

Section HENKIN.

#[local] Infix "=~=" := is_similar_to : type_scope.

Context {L : language}.

Section GENERAL_CASE.

Context {Henkin_constants : Set}.

#[local] Notation L' := (augmented_language L Henkin_constants).

#[local] Existing Instance constant_symbols_sim.

#[local] Existing Instance trm_sim.

#[local] Existing Instance trms_sim.

#[local] Existing Instance frm_sim.

#[local] Existing Instance frms_sim.

Lemma embed_frm_Fun_eqAxm (f : L.(function_symbols))
  : embed_frm (@Fun_eqAxm L f) = @Fun_eqAxm L' f.
Proof.
  enough (HACK : forall phi : trms L (function_arity_table L f) -> trms L (function_arity_table L f) -> frm L, forall phi' : trms L' (function_arity_table L' f) -> trms L' (function_arity_table L' f) -> frm L',
    forall INVARIANT : forall a, forall b, embed_frm (phi a b) = phi' (embed_trms a) (embed_trms b),
    embed_frm (eqns_imp (prod_rec (fun _ => frm L) phi (varcouples (function_arity_table L f))) (function_arity_table L f)) = eqns_imp (prod_rec (fun _ => frm L') phi' (varcouples (function_arity_table L f))) (function_arity_table L f)
  ).
  { unfold Fun_eqAxm. simpl. ii; eapply HACK. ii; reflexivity. }
  simpl. generalize (function_arity_table L f) as n; clear f. induction n as [ | n IH]; simpl; ii.
  - rewrite INVARIANT. reflexivity.
  - exploit (IH (fun ts => fun ts' => phi (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts')) (fun ts => fun ts' => phi' (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts'))).
    + ii. rewrite INVARIANT. reflexivity.
    + intros claim. destruct (@varcouples L n) as [lhs rhs] eqn: H_OBS, (@varcouples L' n) as [lhs' rhs'] eqn: H_OBS'; simpl. f_equal; trivial.
Qed.

Lemma embed_frm_Rel_eqAxm (R : L.(relation_symbols))
  : embed_frm (@Rel_eqAxm L R) = @Rel_eqAxm L' R.
Proof.
  enough (HACK : forall phi : trms L (relation_arity_table L R) -> trms L (relation_arity_table L R) -> frm L, forall phi' : trms L' (relation_arity_table L' R) -> trms L' (relation_arity_table L' R) -> frm L',
    forall INVARIANT : forall a, forall b, embed_frm (phi a b) = phi' (embed_trms a) (embed_trms b),
    embed_frm (eqns_imp (prod_rec (fun _ => frm L) phi (varcouples (relation_arity_table L R))) (relation_arity_table L R)) = eqns_imp (prod_rec (fun _ => frm L') phi' (varcouples (relation_arity_table L R))) (relation_arity_table L R)
  ).
  { unfold Rel_eqAxm. simpl. ii; eapply HACK. ii; reflexivity. }
  simpl. generalize (relation_arity_table L R) as n; clear R. induction n as [ | n IH]; simpl; ii.
  - rewrite INVARIANT. reflexivity.
  - exploit (IH (fun ts => fun ts' => phi (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts')) (fun ts => fun ts' => phi' (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts'))).
    + ii. rewrite INVARIANT. reflexivity.
    + intros claim. destruct (@varcouples L n) as [lhs rhs] eqn: H_OBS, (@varcouples L' n) as [lhs' rhs'] eqn: H_OBS'; simpl. f_equal; trivial.
Qed.

Lemma embed_proves (Gamma : ensemble (frm L)) (p : frm L)
  (PROVE : Gamma ⊢ p)
  : E.image (embed_frm (Henkin_constants := Henkin_constants)) Gamma ⊢ embed_frm (Henkin_constants := Henkin_constants) p.
Proof.
  assert (empty_proof_intro : forall q : frm L', proof [] q -> E.empty ⊢ q).
  { ii. exists []. split. intros ?. done. econstructor. eassumption. }
  destruct PROVE as (ps&INCL&(PF)).
  assert (PROVE : E.fromList ps ⊢ p).
  { exists ps. split. done. econstructor. exact PF. }
  clear PF. revert Gamma p INCL PROVE. induction ps as [ | q ps IH]; i.
  - clear INCL. destruct PROVE as (ps&INCL&(PF)).
    assert (ps_spec : forall q : frm L, ~ L.In q ps).
    { intros q q_in. done!. }
    clear INCL. eapply extend_proves with (Gamma := E.empty). done.
    clear Gamma. induction PF; i.
    + contradiction (ps_spec p (or_introl eq_refl)).
    + eapply for_Imp_E; [eapply IHPF1 | eapply IHPF2]; intros q'; specialize ps_spec with (q := q'); ss!.
    + simpl. eapply for_All_I. done. eapply IHPF. done.
    + simpl. eapply empty_proof_intro. eapply IMP1.
    + simpl. eapply empty_proof_intro. eapply IMP2.
    + simpl. eapply empty_proof_intro. eapply CP.
    + simpl. eapply empty_proof_intro. rewrite embed_subst_frm.
      replace (subst_frm (embed_trm ∘ one_subst x t)%prg (embed_frm p)) with (subst_frm (one_subst x (embed_trm (Henkin_constants := Henkin_constants) t)) (embed_frm (Henkin_constants := Henkin_constants) p)).
      * eapply FA1.
      * eapply equiv_subst_in_frm_implies_subst_frm_same. ii. unfold one_subst, cons_subst, nil_subst. unfold "∘"%prg. destruct (eq_dec z x) as [EQ1 | NE1]; trivial.
    + simpl. eapply empty_proof_intro. eapply FA2.
      red in NOT_FREE |- *. rewrite <- NOT_FREE. eapply @embed_fvs_frm with (Henkin_constants := Henkin_constants) (z := x) (p := p).
    + simpl. eapply empty_proof_intro. eapply FA3.
    + eapply proves_reflexivity.
    + eapply for_Imp_I. eapply proves_symmetry. eapply for_ByHyp. done!.
    + eapply for_Imp_I. eapply for_Imp_I. eapply proves_transitivity with (t2 := embed_trm (Var_trm 1)); eapply for_ByHyp; done!.
    + rewrite embed_frm_Fun_eqAxm. eapply empty_proof_intro. exact (@EQN_FUN L' f).
    + rewrite embed_frm_Rel_eqAxm. eapply empty_proof_intro. exact (@EQN_REL L' R).
  - eapply for_Imp_E with (p := embed_frm q).
    + change (E.image (embed_frm (Henkin_constants := Henkin_constants)) Gamma ⊢ embed_frm (Henkin_constants := Henkin_constants) (Imp_frm q p)). eapply IH.
      * intros p' H_in. done!.
      * rewrite Deduction_theorem. eapply extend_proves with (Gamma := E.fromList (q :: ps)).
        { intros p' H_in. done!. }
        { exact PROVE. }
    + eapply for_ByHyp. rewrite E.in_image_iff. exists q. split; trivial. eapply INCL. simpl. left. trivial.
Qed.

Lemma embed_proves_inv (Gamma : ensemble (frm L)) (p : frm L)
  (PROVE : E.image (embed_frm (Henkin_constants := Henkin_constants)) Gamma ⊢ embed_frm (Henkin_constants := Henkin_constants) p)
  : Gamma ⊢ p.
Proof.
  assert (empty_proof_intro : forall q : frm L, proof [] q -> E.empty ⊢ q).
  { ii. exists []. split. intros ?. done. econstructor. eassumption. }
  destruct PROVE as (ps&INCL&(PF)).
  assert (claim : exists qs : list (frm L), ps = L.map embed_frm qs).
  { clear PF p. revert Gamma INCL; induction ps as [ | p ps IH]; simpl; i.
    - exists []. reflexivity.
    - exploit (IH Gamma). done!. intros [qs ->]. exploit (INCL p). done!.
      intros IN. s!. destruct IN as [q [-> IN]]. exists (q :: qs). reflexivity.
  }
  destruct claim as [qs claim]. subst ps.
  assert (PROVE : E.fromList (L.map (embed_frm (Henkin_constants := Henkin_constants)) qs) ⊢ embed_frm (Henkin_constants := Henkin_constants) p).
  { exists (L.map embed_frm qs). split. done!. econs. exact PF. }
  clear PF. revert Gamma p INCL PROVE. induction qs as [ | q qs IH]; i.
  - clear INCL. eapply extend_proves with (Gamma := E.empty). done.
    assert (ALPHA : subst_frm (fun z : ivar => Var_trm (z - 1)) (shift_frm (embed_frm (Henkin_constants := Henkin_constants) p)) ≡ p) by eapply shift_frm_inv.
    rewrite <- ALPHA. eapply extend_proves with (Gamma := E.image (subst_frm (fun z : ivar => Var_trm (z - 1))) E.empty). done!. eapply proves_substitutivity.
    clear ALPHA. remember (shift_frm (embed_frm p)) as p' eqn: INVARIANT. revert INVARIANT PROVE. generalize (embed_frm (Henkin_constants := Henkin_constants) p) as A.
    clear p Gamma; i. destruct PROVE as (ps&INCL&(PF)).
    assert (ps_spec : forall q : frm L', ~ L.In q ps).
    { intros q q_in. done!. }
    clear INCL. revert p' INVARIANT. induction PF; i.
    + contradiction (ps_spec p (or_introl eq_refl)).
    + eapply for_Imp_E with (p := shift_frm p).
      * eapply IHPF1. intros q' CONTRA; eapply ps_spec with (q := q'); ss!. simpl. congruence.
      * eapply IHPF2. intros q' CONTRA; eapply ps_spec with (q := q'); ss!. simpl. congruence.
    + subst. simpl. eapply for_All_I with (p := shift_frm q). done!. eapply IHPF. intros q' CONTRA; eapply ps_spec with (q := q'); ss!. reflexivity.
    + subst. simpl. eapply empty_proof_intro. eapply IMP1.
    + subst. simpl. eapply empty_proof_intro. eapply IMP2.
    + subst. simpl. eapply empty_proof_intro. eapply CP.
    + subst. simpl.
      enough (ALPHA : shift_frm (Henkin_constants := Henkin_constants) (subst_frm (one_subst x t) p) ≡ subst_frm (one_subst (x + 1) (shift_trm t)) (shift_frm p)).
      { rewrite ALPHA. eapply empty_proof_intro. eapply FA1. }
      eapply shift_frm_subst_frm_once.
    + subst. simpl. eapply empty_proof_intro. eapply FA2. red in NOT_FREE |- *. rewrite <- NOT_FREE. eapply shift_frm_fv.
    + subst. simpl. eapply empty_proof_intro. eapply FA3.
    + subst. simpl. eapply proves_reflexivity.
    + subst. eapply for_Imp_I. eapply proves_symmetry. eapply for_ByHyp. done!.
    + subst. eapply for_Imp_I. eapply for_Imp_I. eapply proves_transitivity with (t2 := shift_trm (Henkin_constants := Henkin_constants) (Var_trm 1)); eapply for_ByHyp; done!.
    + subst. rewrite <- embed_frm_Fun_eqAxm. rewrite shift_frm_embed_frm. eapply extend_proves with (Gamma := E.image (subst_frm (fun z : ivar => Var_trm (z + 1))) E.empty). done!.
      eapply proves_substitutivity. eapply empty_proof_intro. eapply EQN_FUN.
    + subst. rewrite <- embed_frm_Rel_eqAxm. rewrite shift_frm_embed_frm. eapply extend_proves with (Gamma := E.image (subst_frm (fun z : ivar => Var_trm (z + 1))) E.empty). done!.
      eapply proves_substitutivity. eapply empty_proof_intro. eapply EQN_REL.
  - eapply for_Imp_E with (p := q).
    + eapply IH.
      * intros p' H_in. exploit (INCL  p'). ss!. intros IN. ss!.
      * simpl. rewrite Deduction_theorem. eapply extend_proves with (Gamma := E.fromList (L.map embed_frm (q :: qs))).
        { intros p' H_in. done!. }
        { exact PROVE. }
    + eapply for_ByHyp. exploit (INCL (embed_frm (Henkin_constants := Henkin_constants) q)). ss!. intros IN. ss!. apply embed_frm_inj in H; subst x; done.
Qed.

Theorem embed_frm_proves_iff (Gamma : ensemble (frm L)) (p : frm L)
  : E.image (embed_frm (Henkin_constants := Henkin_constants)) Gamma ⊢ embed_frm (Henkin_constants := Henkin_constants) p <-> Gamma ⊢ p.
Proof.
  split; [eapply embed_proves_inv | eapply embed_proves].
Qed.

Theorem similar_equiconsistent (Gamma : ensemble (frm L)) (Gamma' : ensemble (frm L'))
  (SIM : is_similar_to (Similarity := frms_sim _ _ _ _ _ Henkin_constants) Gamma Gamma')
  : inconsistent Gamma <-> inconsistent Gamma'.
Proof.
  split; intros INCONSISTENT.
  - rewrite inconsistent_iff in INCONSISTENT. rewrite inconsistent_iff.
    rewrite <- embed_frms_spec in SIM. rewrite <- SIM.
    change (E.image (embed_frm (Henkin_constants := Henkin_constants)) Gamma ⊢ embed_frm (Henkin_constants := Henkin_constants) Bot_frm). now eapply embed_proves.
  - intros p. pose proof (INCONSISTENT (embed_frm p)) as claim.
    rewrite <- embed_frms_spec in SIM. rewrite <- SIM in claim.
    eapply embed_proves_inv. exact claim.
Qed.

Lemma shift_Fun_eqAxm (f : L'.(function_symbols))
  : E.empty ⊢ shift_frm (Fun_eqAxm f).
Proof.
  rewrite <- embed_frm_Fun_eqAxm. rewrite shift_frm_embed_frm.
  eapply extend_proves with (Gamma := E.image (subst_frm (fun z : ivar => Var_trm (z + 1))) E.empty). { done!. }
  eapply proves_substitutivity. exists []. split. done. econstructor. eapply EQN_FUN.
Qed.

Lemma shift_Rel_eqAxm (R : L'.(relation_symbols))
  : E.empty ⊢ shift_frm (Rel_eqAxm R).
Proof.
  rewrite <- embed_frm_Rel_eqAxm. rewrite shift_frm_embed_frm.
  eapply extend_proves with (Gamma := E.image (subst_frm (fun z : ivar => Var_trm (z + 1))) E.empty). { done!. }
  eapply proves_substitutivity. exists []. split. done. econstructor. eapply EQN_REL.
Qed.

Lemma proves_shift (Gamma : ensemble (frm L')) (p : frm L')
  (PROVE : Gamma ⊢ p)
  : E.image shift_frm Gamma ⊢ shift_frm p.
Proof.
  assert (empty_proof_intro : forall q : frm (mkL_with_constant_symbols (function_symbols L) (relation_symbols L) (function_arity_table L) (relation_arity_table L) (constant_symbols L)), proof [] q -> E.empty ⊢ q).
  { ii. exists []. split. intros ?. done. econstructor. eassumption. }
  destruct PROVE as (ps&INCL&(PF)).
  assert (PROVE : E.fromList ps ⊢ p).
  { exists ps. split. done. econstructor. exact PF. }
  clear PF. revert Gamma p INCL PROVE. induction ps as [ | q ps IH]; i.
  - clear INCL. destruct PROVE as (ps&INCL&(PF)).
    assert (ps_spec : forall q : frm L', ~ L.In q ps).
    { intros q q_in. done!. }
    clear INCL. eapply extend_proves with (Gamma := E.empty). done.
    clear Gamma. induction PF; i.
    + contradiction (ps_spec p (or_introl eq_refl)).
    + eapply for_Imp_E; [eapply IHPF1 | eapply IHPF2]; intros q'; specialize ps_spec with (q := q'); ss!.
    + simpl. eapply for_All_I. done. eapply IHPF. done.
    + simpl. eapply empty_proof_intro. eapply IMP1.
    + simpl. eapply empty_proof_intro. eapply IMP2.
    + simpl. eapply empty_proof_intro. eapply CP.
    + simpl. rewrite shift_frm_subst_frm_once. eapply empty_proof_intro. eapply FA1.
    + simpl. eapply empty_proof_intro. eapply FA2. red in NOT_FREE |- *. rewrite shift_frm_fv; trivial.
    + simpl. eapply empty_proof_intro. eapply FA3.
    + eapply proves_reflexivity.
    + eapply for_Imp_I. eapply proves_symmetry. eapply for_ByHyp. done!.
    + eapply for_Imp_I. eapply for_Imp_I. eapply proves_transitivity with (t2 := shift_trm (Henkin_constants := Henkin_constants) (Var_trm 1)); eapply for_ByHyp; done!.
    + eapply shift_Fun_eqAxm.
    + eapply shift_Rel_eqAxm.
  - eapply for_Imp_E with (p := shift_frm q).
    + change (E.image shift_frm Gamma ⊢ shift_frm (Imp_frm q p)). eapply IH.
      * intros p' H_in. done!.
      * rewrite Deduction_theorem. eapply extend_proves with (Gamma := E.fromList (q :: ps)).
        { intros p' H_in. done!. }
        { exact PROVE. }
    + eapply for_ByHyp. rewrite E.in_image_iff. exists q. split; trivial. eapply INCL. simpl. left. trivial.
Qed.

End GENERAL_CASE.

#[local] Notation L' := (augmented_language L Henkin_constants).

#[local] Notation hatom := (ivar + Henkin_constants)%type.

#[local] Notation hsubst := (hatom -> trm L').

#[local] Existing Instance constant_symbols_sim.

#[local] Existing Instance trm_sim.

#[local] Existing Instance trms_sim.

#[local] Existing Instance frm_sim.

#[local] Existing Instance frms_sim.

Lemma Fun_eqAxm_HC_free (f : L'.(function_symbols))
  : forall c : Henkin_constants, HC_occurs_in_frm c (Fun_eqAxm f) = false.
Proof.
  enough (HACK : forall phi : trms L' _ -> trms L' _ -> frm L', forall c,
    forall phi_a_b : forall a, forall b, forall claim : HC_occurs_in_trms c a = false /\ HC_occurs_in_trms c b = false, HC_occurs_in_frm c (phi a b) = false,
    HC_occurs_in_frm c ((nat_rec (fun _ => frm L') (prod_rec (fun _ => frm L') phi (varcouples (function_arity_table L' f))) (fun n => fun q => Imp_frm (Eqn_frm (Var_trm (n + n)) (Var_trm (S (n + n)))) q) (function_arity_table L' f))) = false
  ).
  { ii. unfold Fun_eqAxm. eapply HACK. ii. now s!. }
  induction (function_arity_table L' f) as [ | n IH]; simpl; ii.
  - rewrite phi_a_b; trivial. split; trivial.
  - s!. split. split; trivial. exploit (IH (fun ts : trms L' n => fun ts' : trms L' n => phi (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts'))).
    + ii. rewrite phi_a_b; trivial.
    + intros claim. simpl. destruct (varcouples n) as [lhs rhs] eqn: H_OBS; simpl in *. eapply claim.
Qed.

Lemma Rel_eqAxm_HC_free (R : L'.(relation_symbols))
  : forall c : Henkin_constants, HC_occurs_in_frm c (Rel_eqAxm R) = false.
Proof.
  enough (HACK : forall phi : trms L' _ -> trms L' _ -> frm L', forall c,
    forall phi_a_b : forall a, forall b, forall claim : HC_occurs_in_trms c a = false /\ HC_occurs_in_trms c b = false, HC_occurs_in_frm c (phi a b) = false,
    HC_occurs_in_frm c ((nat_rec (fun _ => frm L') (prod_rec (fun _ => frm L') phi (varcouples (relation_arity_table L' R))) (fun n => fun q => Imp_frm (Eqn_frm (Var_trm (n + n)) (Var_trm (S (n + n)))) q) (relation_arity_table L' R))) = false
  ).
  { ii. unfold Rel_eqAxm. eapply HACK. ii. now s!. }
  induction (relation_arity_table L' R) as [ | n IH]; simpl; ii.
  - rewrite phi_a_b; trivial. split; trivial.
  - s!. split. split; trivial. exploit (IH (fun ts : trms L' n => fun ts' : trms L' n => phi (S_trms n (Var_trm (n + n)) ts) (S_trms n (Var_trm (S (n + n))) ts'))).
    + ii. rewrite phi_a_b; trivial.
    + intros claim. simpl. destruct (varcouples n) as [lhs rhs] eqn: H_OBS; simpl in *. eapply claim.
Qed.

Lemma twilight_Fun_eqAxm (f : L'.(function_symbols))
  : E.empty ⊢ twilight_frm (Fun_eqAxm f).
Proof.
  rewrite untwilight_frm. 2: exact (Fun_eqAxm_HC_free f). set (n := L'.(function_arity_table) f + L'.(function_arity_table) f). set (s := fun z : ivar => Var_trm (z * 2)).
  replace (subst_frm s (Fun_eqAxm f)) with (subst_frm (fun x : ivar => if le_lt_dec n x then Var_trm x else s x) (Fun_eqAxm f)).
  - eapply for_Imp_E with (p := close_from 0 n (Fun_eqAxm f)). eapply subst_frm_close_frm with (n := n) (s := s) (p := Fun_eqAxm f).
    clearbody n. clear s. induction n as [ | n IH]; simpl.
    + exists []. split. done. econs. exact (EQN_FUN f).
    + eapply for_All_I. done. exact IH.
  - eapply equiv_subst_in_frm_implies_subst_frm_same.
    ii. destruct (le_lt_dec n z) as [LE | LT]; trivial. rewrite Fun_eqAxm_free_vars in FREE. lia.
Qed.

Lemma twilight_Rel_eqAxm (R : L'.(relation_symbols))
  : E.empty ⊢ twilight_frm (Rel_eqAxm R).
Proof.
  rewrite untwilight_frm. 2: exact (Rel_eqAxm_HC_free R). set (n := L'.(relation_arity_table) R + L'.(relation_arity_table) R). set (s := fun z : ivar => Var_trm (z * 2)).
  replace (subst_frm s (Rel_eqAxm R)) with (subst_frm (fun x : ivar => if le_lt_dec n x then Var_trm x else s x) (Rel_eqAxm R)).
  - eapply for_Imp_E with (p := close_from 0 n (Rel_eqAxm R)). eapply subst_frm_close_frm with (n := n) (s := s) (p := Rel_eqAxm R).
    clearbody n. clear s. induction n as [ | n IH]; simpl.
    + exists []. split. done. econs. exact (EQN_REL R).
    + eapply for_All_I. done. exact IH.
  - eapply equiv_subst_in_frm_implies_subst_frm_same.
    ii. destruct (le_lt_dec n z) as [LE | LT]; trivial. rewrite Rel_eqAxm_free_vars in FREE. lia.
Qed.

#[local] Opaque Nat.mul Nat.div "mod".

Lemma proves_twilight (Gamma : ensemble (frm L')) (p : frm L')
  (PROVE : Gamma ⊢ p)
  : E.image twilight_frm Gamma ⊢ twilight_frm p.
Proof.
  assert (empty_proof_intro : forall q : frm L', proof [] q -> E.empty ⊢ q).
  { ii. exists []. split. intros ?. done. econstructor. eassumption. }
  destruct PROVE as (ps&INCL&(PF)).
  assert (PROVE : E.fromList ps ⊢ p).
  { exists ps. split. done. econstructor. exact PF. }
  clear PF. revert Gamma p INCL PROVE. induction ps as [ | q ps IH]; i.
  - clear INCL. destruct PROVE as (ps&INCL&(PF)).
    assert (ps_spec : forall q : frm L', ~ L.In q ps).
    { intros q q_in. done!. }
    clear INCL. eapply extend_proves with (Gamma := E.empty). done.
    clear Gamma. induction PF; i.
    + contradiction (ps_spec p (or_introl eq_refl)).
    + eapply for_Imp_E; [eapply IHPF1 | eapply IHPF2]; intros q'; specialize ps_spec with (q := q'); ss!.
    + simpl. eapply for_All_I. done. eapply IHPF. done.
    + simpl. eapply empty_proof_intro. eapply IMP1.
    + simpl. eapply empty_proof_intro. eapply IMP2.
    + simpl. eapply empty_proof_intro. eapply CP.
    + simpl. erewrite subst_hsubst_compat_in_frm. 2: ii; reflexivity.
      replace (hsubst_frm (to_hsubst (one_subst x t)) p) with (hsubst_frm (one_hsubst (inl x) t) p).
      * enough (WTS : (twilight_frm (hsubst_frm (one_hsubst (inl x) t) p)) ≡ (subst_frm (one_subst (2 * x) (twilight_trm t)) (twilight_frm p))).
        { rewrite WTS. eapply empty_proof_intro. eapply FA1. }
        eapply twilight_frm_one_hsubst.
      * eapply equiv_hsubst_in_frm_implies_hsubst_frm_same. ii. unfold one_hsubst, cons_hsubst, nil_hsubst. unfold to_hsubst. unfold one_subst, cons_subst, nil_subst.
        destruct z as [z | z].
        { destruct (eqb _ _) as [ | ] eqn: H_OBS1; destruct (eq_dec _ _) as [EQ2 | NE2]; trivial.
          - rewrite eqb_eq in H_OBS1. hinv H_OBS1.
          - rewrite eqb_neq in H_OBS1. done!.
        }
        { destruct (eqb _ _) as [ | ] eqn: H_OBS; trivial. rewrite eqb_eq in H_OBS. hinv H_OBS. }
    + simpl. eapply empty_proof_intro. eapply FA2.
      red. rewrite Nat.mul_comm. rewrite <- twilight_frm_fvs. exact NOT_FREE.
    + simpl. eapply empty_proof_intro. eapply FA3.
    + eapply proves_reflexivity.
    + eapply for_Imp_I. eapply proves_symmetry. eapply for_ByHyp. done!.
    + eapply for_Imp_I. eapply for_Imp_I. eapply proves_transitivity with (t2 := twilight_trm (Var_trm 1)); eapply for_ByHyp; done!.
    + eapply twilight_Fun_eqAxm.
    + eapply twilight_Rel_eqAxm.
  - eapply for_Imp_E with (p := twilight_frm q).
    + change (E.image twilight_frm Gamma ⊢ twilight_frm (Imp_frm q p)). eapply IH.
      * intros p' H_in. done!.
      * rewrite Deduction_theorem. eapply extend_proves with (Gamma := E.fromList (q :: ps)).
        { intros p' H_in. done!. }
        { exact PROVE. }
    + eapply for_ByHyp. rewrite E.in_image_iff. exists q. split; trivial. eapply INCL. simpl. left. trivial.
Qed.

Lemma proves_hsubstitutivity (sigma : hsubst) (Gamma : ensemble (frm L')) (p : frm L')
  (PROVE : Gamma ⊢ p)
  : E.image (hsubst_frm sigma) Gamma ⊢ hsubst_frm sigma p.
Proof.
  assert (EQ1 : E.image (hsubst_frm sigma) Gamma == E.image (subst_frm (twilight sigma)) (E.image twilight_frm Gamma)).
  { intros z. s!. split; intros [q [-> IN]].
    - exists (twilight_frm q); split.
      + eapply twilight_frm_lemma.
      + done!.
    - rewrite E.in_image_iff in IN. destruct IN as [p' [-> IN]]. exists p'. split.
      + symmetry. eapply twilight_frm_lemma.
      + done!.
  }
  rewrite EQ1. rewrite twilight_frm_lemma. eapply proves_substitutivity. eapply proves_twilight. exact PROVE.
Qed.

Context {enum_frm_L' : isEnumerable (frm L')}.

Fixpoint addHenkin (X : ensemble (frm L')) (n : nat) {struct n} : ensemble (frm L') :=
  match n with
  | O => X
  | S n => E.insert (nth_Henkin_axiom n) (addHenkin X n)
  end.

Lemma addHenkin_incl (X : ensemble (frm L')) (n1 : nat) (n2 : nat)
  (LE : n1 <= n2)
  : addHenkin X n1 \subseteq addHenkin X n2.
Proof.
  revert X. induction LE; i.
  - reflexivity.
  - simpl. etransitivity. eapply IHLE. done!.
Qed.

Lemma addHenkin_nth_Henkin_not_occur (X : ensemble (frm L')) k n (p : frm L')
  (LE : k <= n)
  (HC_free : forall A : frm L', forall c : Henkin_constants, forall IN : A \in X, HC_occurs_in_frm c A = false)
  (IN : p \in addHenkin X k)
  : HC_occurs_in_frm (nth_Henkin_constant n) p = false.
Proof.
  revert n X p LE HC_free IN. induction k as [ | k IH]; simpl; i.
  - eapply HC_free; trivial.
  - s!. destruct IN as [-> | IN].
    + eapply Henkin_constant_does_not_occur_in_any_former_Henkin_axioms. lia.
    + eapply IH with (X := X); done!.
Qed.

Lemma addHenkin_equiconsistent (X : ensemble (frm L')) n
  (HC_free : forall A : frm L', forall c : Henkin_constants, forall IN : A \in X, HC_occurs_in_frm c A = false)
  : inconsistent (addHenkin X n) <-> inconsistent (addHenkin X (S n)).
Proof.
  split; intros INCONSISTENT.
  - intros p. simpl. eapply extend_infers. eapply INCONSISTENT. done!.
  - simpl in INCONSISTENT. rewrite inconsistent_iff in INCONSISTENT. rewrite inconsistent_iff.
    set (x := fst (cp n)). set (phi := enum (snd (cp n))). set (c := @Con_trm L' (inr (nth_Henkin_constant n))).
    assert (PROVE1 : addHenkin X n ⊢ Neg_frm (nth_Henkin_axiom n)).
    { eapply NegationI. exact INCONSISTENT. }
    rewrite Henkin_axiom_is_of_form in PROVE1. fold x in PROVE1. fold c in PROVE1. fold phi in PROVE1.
    assert (PROVE2 : addHenkin X n ⊢ subst_frm (one_subst x c) phi).
    { eapply for_Imp_E. exists []. split. done. econs. eapply proof_dne.
      eapply for_Imp_E. 2: eapply PROVE1. eapply for_CP1. exists []. split. done. econs. eapply proof_ex_falso.
    }
    assert (PROVE3 : addHenkin X n ⊢ Neg_frm (All_frm x phi)).
    { eapply for_Imp_E. 2: eapply PROVE1. eapply for_CP1. eapply for_Imp_I. eapply for_Imp_I. eapply for_ByHyp. done!. }
    eapply ContradictionI with (A := All_frm x phi); trivial.
    clear PROVE1 PROVE3. rename PROVE2 into PROVE. set (Gamma := addHenkin X n) in *.
    destruct PROVE as (ps&INCL&(PF)). set (y := 1 + max (max x (maxs (map last_ivar_frm ps))) (max (last_ivar_frm (All_frm x phi)) (last_ivar_frm (subst_frm (one_subst x c) phi)))).
    eapply extend_alpha_proves with (Gamma := E.image (replace_constant_in_frm (nth_Henkin_constant n) (Var_trm y)) (E.fromList ps)).
    { ii. rewrite E.in_image_iff in IN. destruct IN as [q [-> IN]]. exists q. split; [ | done!].
      exploit (addHenkin_nth_Henkin_not_occur X n n q (@le_n n)); trivial.
      { now eapply INCL. }
      intros claim1. unfold replace_constant_in_frm. transitivity (subst_frm nil_subst q).
      - erewrite subst_hsubst_compat_in_frm. 2: ii; reflexivity. eapply alpha_equiv_eq_intro. eapply equiv_hsubst_in_frm_implies_hsubst_frm_same. intros [u | u] u_free; simpl.
        + unfold one_hsubst, cons_hsubst, nil_hsubst, nil_subst. destruct (eqb _ _) as [ | ] eqn: H_OBS; rewrite eqb_spec in H_OBS; done!.
        + unfold one_hsubst, cons_hsubst, nil_hsubst. destruct (eqb _ _) as [ | ] eqn: H_OBS; rewrite eqb_spec in H_OBS.
          * rewrite H_OBS in u_free. rewrite occurs_free_in_frm_iff in u_free. rewrite in_accum_hatom_in_frm_iff_HC_occurs_in_frm in u_free. congruence.
          * reflexivity.
      - eapply subst_nil_frm. intros u u_free. reflexivity.
    }
    eapply for_All_I' with (y := y).
    + ii. rewrite E.in_image_iff in H. destruct H as [q [-> IN]].
      unfold replace_constant_in_frm. eapply frm_is_fresh_in_hsubst_iff. unfold frm_is_fresh_in_hsubst.
      rewrite L.forallb_forall. unfold compose. intros u u_free. rewrite negb_true_iff. unfold one_hsubst, cons_hsubst, nil_hsubst. destruct (eqb _ _) as [ | ] eqn: H_OBS; rewrite eqb_spec in H_OBS.
      * subst u. rewrite in_accum_hatom_in_frm_iff_HC_occurs_in_frm in u_free. exploit (addHenkin_nth_Henkin_not_occur X n n q (@le_n n)); trivial.
        { now eapply INCL. }
        intros claim. congruence.
      * destruct u as [u | u].
        { rewrite in_accum_hatom_in_frm_iff_is_free_in_frm in u_free. rewrite is_free_in_trm_unfold. erewrite Nat.eqb_neq. intros ->.
          rewrite <- not_false_iff_true in u_free. eapply u_free. eapply last_ivar_frm_gt. red. red.
          transitivity (1 + maxs (map last_ivar_frm ps)).
          - enough (WTS : last_ivar_frm q <= maxs (map last_ivar_frm ps)) by lia.
            eapply in_maxs_ge. done!.
          - lia.
        }
        { reflexivity. }
    + red. eapply last_ivar_frm_gt. lia.
    + assert (ALPHA : subst_frm (one_subst x (Var_trm y)) phi ≡ replace_constant_in_frm (nth_Henkin_constant n) (Var_trm y) (subst_frm (one_subst x c) phi)).
      { eapply alpha_equiv_eq_intro. unfold replace_constant_in_frm. erewrite subst_hsubst_compat_in_frm. 2: ii; reflexivity. erewrite subst_hsubst_compat_in_frm. 2: ii; reflexivity.
        rewrite <- hsubst_compose_frm_spec. eapply equiv_hsubst_in_frm_implies_hsubst_frm_same. intros [u | u] u_free.
        - unfold to_hsubst, hsubst_compose, one_subst, cons_subst, nil_subst, one_hsubst, cons_hsubst, nil_hsubst. destruct (eq_dec u x) as [EQ1 | NE1]; trivial.
          subst u. unfold c. rewrite hsubst_trm_unfold. destruct (eqb _ _) as [ | ] eqn: H_OBS; rewrite eqb_spec in H_OBS; done!.
        - unfold to_hsubst, hsubst_compose, one_subst, cons_subst, nil_subst, one_hsubst, cons_hsubst, nil_hsubst. rewrite hsubst_trm_unfold. destruct (eqb _ _) as [ | ] eqn: H_OBS; rewrite eqb_spec in H_OBS.
          + rewrite H_OBS in u_free. pose proof (@Henkin_constant_does_not_occur_in_enum L enum_frm_L' n) as claim. fold phi in claim.
            rewrite occurs_free_in_frm_iff in u_free. rewrite in_accum_hatom_in_frm_iff_HC_occurs_in_frm in u_free. congruence.
          + reflexivity.
      }
      rewrite ALPHA. eapply proves_hsubstitutivity. exists ps. split. done. econs. exact PF.
Qed.

Theorem Henkin_complete (Gamma : ensemble (frm L')) (x : ivar) (phi : frm L')
  : exists c : Henkin_constants, (Imp_frm (subst_frm (one_subst x (@Con_trm L' (inr c))) phi) (All_frm x phi)) \in union_f (addHenkin Gamma).
Proof.
  set (n := cpInv x (proj1_sig (enum_spec phi))).
  pose proof (@Henkin_axiom_is_of_form L enum_frm_L' n) as claim.
  simpl in claim. exists (nth_Henkin_constant n).
  destruct (enum_spec phi) as [n2 n2_eq]; simpl in *. subst phi.
  assert (EQ : n = cpInv x n2) by reflexivity.
  clearbody n. rewrite <- cp_spec in EQ. rewrite EQ in claim. simpl in claim.
  rewrite <- claim. exists (S n). simpl. left. reflexivity.
Qed.

Definition AddHenkin (X : ensemble (frm L')) : ensemble (frm L') :=
  union_f (addHenkin X).

Theorem AddHenkin_equiconsistent (X : ensemble (frm L'))
  (HC_free : forall A, forall c, A \in X -> HC_occurs_in_frm c A = false)
  : inconsistent X <-> inconsistent (AddHenkin X).
Proof.
  unfold AddHenkin. rewrite <- equiconsistent_union_f; eauto.
  - eapply addHenkin_incl.
  - simpl. intros n. eapply addHenkin_equiconsistent; eauto.
Qed.

#[local] Hint Resolve fact1_of_1_2_8 fact2_of_1_2_8 fact3_of_1_2_8 fact4_of_1_2_8 fact5_of_1_2_8 lemma1_of_1_2_11 : core.

Lemma Th_X_equiconsistent_Th_AddHenkin (X : ensemble (frm L'))
  (HC_free : forall A : frm L', forall c : Henkin_constants, A \in X -> HC_occurs_in_frm c A = false)
  : equiconsistent (Th X) (Th (AddHenkin X)).
Proof.
  red. do 2 rewrite <- cl_eq_Th. do 2 rewrite <- inconsistent_okay. eapply AddHenkin_equiconsistent; trivial.
Qed.

Lemma Th_X_equiconsistent_MaximallyConsistentSet_AddHenkin (X : ensemble (frm L'))
  (HC_free : forall A : frm L', forall c : Henkin_constants, A \in X -> HC_occurs_in_frm c A = false)
  : equiconsistent (Th X) (MaximallyConsistentSet (AddHenkin X)).
Proof with eauto with *.
  split.
  - intros INCONSISTENT. eapply inconsistent_compatWith_isSubsetOf... transitivity (Th (AddHenkin X)).
    + intros p p_in. rewrite <- cl_eq_Th in *. eapply fact4_of_1_2_8... eapply @subset_union_f with (L := L') (f := addHenkin X) (n := 0).
    + etransitivity. 2: eapply lemma3_of_1_3_9. intros p p_in. rewrite <- cl_eq_Th in *. eapply fact4_of_1_2_8... eapply @subset_union_f with (L := L') (f := axiom_set (AddHenkin X)) (n := 0).
  - intros INCONSISTENT. rewrite <- cl_eq_Th. exists Bot_frm. split. 2: reflexivity. rewrite inconsistent_cl_iff.
    assert (INCONSISTENT' : inconsistent' (Th (full_axiom_set (AddHenkin X)))).
    { eapply inconsistent_compatWith_isSubsetOf... eapply lemma2_of_1_3_9. }
    rewrite <- cl_eq_Th in INCONSISTENT'. rewrite <- inconsistent_okay in INCONSISTENT'.
    rewrite <- inconsistent_iff. rewrite equiconsistent_union_f with (f := addHenkin X).
    + rewrite equiconsistent_union_f with (f := axiom_set (AddHenkin X))...
      * intros n1 n2 LE. induction LE as [ | n2 LE IH]; done!.
      * eapply axiom_set_equiconsistent.
    + eapply addHenkin_incl.
    + i. eapply addHenkin_equiconsistent...
Qed.

Theorem theorem_of_1_3_10 (Gamma : ensemble (frm L))
  : MaximallyConsistentSet_spec (E.image embed_frm Gamma) (MaximallyConsistentSet (AddHenkin (E.image embed_frm Gamma))).
Proof with eauto with *.
  set (X := E.image embed_frm Gamma). pose proof (lemma1 := @lemma1_of_1_3_8 L').
  pose proof (theorem_of_1_2_14 (Th (AddHenkin X)) (lemma1 (AddHenkin X))) as [? ? ? ?].
  fold (MaximallyConsistentSet (AddHenkin X)) in SUBSET, IS_FILTER, COMPLETE, EQUICONSISTENT.
  assert (CLOSED_infers : forall b, b \in MaximallyConsistentSet (AddHenkin X) <-> MaximallyConsistentSet (AddHenkin X) ⊢ b).
  { intros b. split; intros b_in.
    - enough (to_show : b \in Th (MaximallyConsistentSet (AddHenkin X))) by now inversion to_show.
      rewrite <- cl_eq_Th. eapply fact3_of_1_2_8...
    - eapply fact5_of_1_2_8... rewrite cl_eq_Th... econs...
  }
  assert (META_DN : forall b, (Neg_frm b \in MaximallyConsistentSet (AddHenkin X) -> Bot_frm \in MaximallyConsistentSet (AddHenkin X)) -> b \in MaximallyConsistentSet (AddHenkin X)).
  { intros b NEGATION. eapply COMPLETE. split.
    - intros INCONSISTENT. eapply inconsistent_compatWith_isSubsetOf...
      transitivity (E.insert b (MaximallyConsistentSet (AddHenkin X))).
      + ii; right...
      + eapply fact3_of_1_2_8.
    - intros INCONSISTENT.
      assert (claim1 : E.insert b (MaximallyConsistentSet (AddHenkin X)) ⊢ Bot_frm).
      { rewrite <- inconsistent_okay in INCONSISTENT... }
      exists (Bot_frm). split...
      + eapply NEGATION, CLOSED_infers, NegationI...
      + reflexivity.
  }
  assert (IMPLICATION_FAITHFUL : forall A, forall B, Imp_frm A B \in MaximallyConsistentSet (AddHenkin X) <-> << IMPLICATION : A \in MaximallyConsistentSet (AddHenkin X) -> B \in MaximallyConsistentSet (AddHenkin X) >>).
  { intros b b'. split.
    - intros IMPLICATION b_in.
      eapply CLOSED_infers. eapply ImplicationE with (A := b).
      + eapply CLOSED_infers...
      + eapply CLOSED_infers...
    - intros IMPLICATION. eapply META_DN.
      intros H_in. eapply CLOSED_infers.
      assert (claim1 : E.insert (Imp_frm b b') (MaximallyConsistentSet (AddHenkin X)) ⊢ Bot_frm).
      { eapply ContradictionI with (A := Imp_frm b b').
        - eapply ByAssumption. left...
        - eapply extend_infers with (Gamma := MaximallyConsistentSet (AddHenkin X)).
          + eapply CLOSED_infers...
          + ii; right...
      }
      assert (claim2 : MaximallyConsistentSet (AddHenkin X) ⊢ Con_frm b (Neg_frm b')).
      { eapply DisjunctionE with (A := b) (B := Neg_frm b).
        - eapply extend_infers with (Gamma := E.empty).
          + eapply Law_of_Excluded_Middle.
          + done!.
        - eapply DisjunctionE with (A := b') (B := Neg_frm b').
          + eapply extend_infers with (Gamma := E.empty).
            { eapply Law_of_Excluded_Middle. }
            { done!. }
          + eapply ContradictionE.
            eapply Cut_property with (A := Imp_frm b b').
            { eapply ImplicationI, ByAssumption. right; left... }
            { eapply extend_infers. exact claim1. ii; s!. tauto. }
          + eapply ConjunctionI.
            { eapply ByAssumption. right; left... }
            { eapply ByAssumption. left... }
        - eapply ContradictionE.
          eapply Cut_property with (A := Imp_frm b b').
          + eapply ImplicationI, ContradictionE.
            eapply ContradictionI with (A := b).
            { eapply ByAssumption. left... }
            { eapply ByAssumption. right; left... }
          + eapply extend_infers... ii; s!. tauto.
      }
      assert (claim3 : MaximallyConsistentSet (AddHenkin X) ⊢ b).
      { eapply ConjunctionE1... }
      assert (claim4 : MaximallyConsistentSet (AddHenkin X) ⊢ Neg_frm b').
      { eapply ConjunctionE2. exact claim2. }
      eapply ContradictionI with (A := b'); trivial.
      eapply CLOSED_infers, IMPLICATION, CLOSED_infers; trivial.
  }
  assert (FORALL_FAITHFUL : forall x, forall A, All_frm x A \in MaximallyConsistentSet (AddHenkin X) <-> << IMPLICATION : forall t, subst_frm (one_subst x t) A \in MaximallyConsistentSet (AddHenkin X) >>).
  { intros x phi. split.
    - intros UNIVERSAL IN. eapply CLOSED_infers. eapply UniversalE with (A := phi). eapply CLOSED_infers...
    - intros UNIVERSAL. unnw. pose proof (Henkin_complete X x phi) as [c IN].
      eapply IMPLICATION_FAITHFUL with (A := subst_frm (one_subst x (@Con_trm L' (inr c))) phi).
      + eapply SUBSET. econs. eapply ByAssumption...
      + eapply UNIVERSAL.
  }
  assert (claim1 : Th X \subseteq MaximallyConsistentSet (AddHenkin X)).
  { transitivity (Th (AddHenkin X))... intros p p_in. rewrite <- cl_eq_Th in *. revert p p_in. eapply fact4_of_1_2_8. unfold AddHenkin. rewrite <- subset_union_f with (n := 0). reflexivity. }
  assert (claim2 : equiconsistent (MaximallyConsistentSet (AddHenkin X)) (Th X)).
  { red. split; intros INCONSISTENT.
    - rewrite <- cl_eq_Th. rewrite <- inconsistent_okay. rewrite AddHenkin_equiconsistent.
      + rewrite inconsistent_okay. rewrite cl_eq_Th. eapply EQUICONSISTENT...
      + intros A c IN. unfold X in IN. rewrite E.in_image_iff in IN. destruct IN as [n [-> IN]]. eapply embed_frm_HC_free.
    - rewrite <- cl_eq_Th in INCONSISTENT. rewrite <- inconsistent_okay in INCONSISTENT.
      eapply EQUICONSISTENT. rewrite <- cl_eq_Th. rewrite <- inconsistent_okay. rewrite <- AddHenkin_equiconsistent...
      intros A c IN. unfold X in IN. rewrite E.in_image_iff in IN. destruct IN as [n [-> IN]]. eapply embed_frm_HC_free.
  }
  red in claim2. repeat (split; trivial); tauto.
Qed.

End HENKIN.

Section MODEL_EXISTENCE.

#[local] Existing Instance V.vec_isSetoid.

Context {L : language} {function_symbols_countable : isCountable L.(function_symbols)} {constant_symbols_countable : isCountable L.(constant_symbols)} {relation_symbols_countable : isCountable L.(relation_symbols)}.

Notation L' := (augmented_language L Henkin_constants).

#[local]
Instance augmented_language_isEnumerable : isEnumerable (frm L') :=
  @frm_isEnumerable L' function_symbols_countable (@sum_isCountable L.(constant_symbols) Henkin_constants constant_symbols_countable (isCountable_if_isEnumerable nat_isEnumerable)) relation_symbols_countable.

Variable X : ensemble (frm L).

Let Delta : ensemble (frm L') :=
  MaximallyConsistentSet (AddHenkin (E.image embed_frm X)).

Let D : Type :=
  trm L'.

Definition interpret_equation (lhs : D) (rhs : D) : Prop :=
  Delta ⊢ Eqn_frm lhs rhs.

#[global]
Instance interpret_equation_Equivalence
  : Equivalence interpret_equation.
Proof with eauto.
  unfold interpret_equation. split.
  - intros x. eapply proves_reflexivity...
  - intros x y EQ. eapply proves_symmetry...
  - intros x y z EQ EQ'. eapply proves_transitivity...
Qed.

Lemma pairwise_equal_intro n vs1 vs2
  (EQ : forall i : Fin.t n, interpret_equation (vs1 !! i) (vs2 !! i))
  : pairwise_equal Delta (vec_to_trms vs1) (vec_to_trms vs2).
Proof.
  revert vs2 EQ. induction vs1 as [ | n v1 vs1 IH].
  - introVNil; simpl; i. econs.
  - introVCons v2 vs2; simpl; i. econs.
    + eapply EQ with (i := FZ).
    + eapply IH. intros i. eapply EQ with (i := FS i).
Qed.

Lemma pairwise_equal_symmetry n (vs1 : Vector.t (trm L') n) (vs2 : Vector.t (trm L') n)
  (EQUAL : pairwise_equal Delta (vec_to_trms vs1) (vec_to_trms vs2))
  : pairwise_equal Delta (vec_to_trms vs2) (vec_to_trms vs1).
Proof.
  revert vs2 EQUAL. induction vs1 as [ | n v1 vs1 IH].
  - introVNil; simpl; i. econs.
  - introVCons v2 vs2; simpl; intros [EQ EQUAL]. econs.
    + eapply proves_symmetry; trivial.
    + eapply IH; trivial.
Qed.

#[local, program]
Instance trmModel : isStructureOf L' :=
  { domain_of_discourse := D
  ; equation_interpret := {| eqProp := interpret_equation; eqProp_Equivalence := interpret_equation_Equivalence |}
  ; function_interpret f vs := Fun_trm f (vec_to_trms vs)
  ; constant_interpret c := Con_trm c
  ; relation_interpret R vs := Delta ⊢ Rel_frm R (vec_to_trms vs)
  }.
Next Obligation.
  econs. exact (Var_trm 0).
Qed.
Next Obligation.
  red. eapply proves_eqn_fun. eapply pairwise_equal_intro; trivial.
Qed.
Next Obligation.
  split; intros INFERS.
  - eapply for_Imp_E. eapply proves_eqn_rel. 2: exact INFERS. eapply pairwise_equal_intro; trivial.
  - eapply for_Imp_E. eapply proves_eqn_rel. 2: exact INFERS. eapply pairwise_equal_symmetry; eapply pairwise_equal_intro; trivial.
Qed.

Definition ivar_interpret : ivar -> domain_of_discourse :=
  Var_trm.

Lemma interpret_trm_trmModel_ivar_interpret (t : trm L')
  : interpret_trm trmModel ivar_interpret t = t
with interpret_trms_trmModel_ivar_interpret n (ts : trms L' n)
  : vec_to_trms (interpret_trms trmModel ivar_interpret ts) = ts.
Proof.
  - trm_ind t; simpl.
    + reflexivity.
    + f_equal. eapply interpret_trms_trmModel_ivar_interpret.
    + reflexivity.
  - trms_ind ts.
    + reflexivity.
    + rewrite interpret_trms_unfold. simpl. f_equal.
      * eapply interpret_trm_trmModel_ivar_interpret.
      * eapply IH.
Qed.

Hypothesis CONSISTENT : X ⊬ Bot_frm.

Theorem trmModel_isModel (p : frm L')
  : p \in Delta <-> interpret_frm trmModel ivar_interpret p.
Proof with eauto with *.
  exploit (@theorem_of_1_2_14 (frm L') (@formula_isSetoid L') LindenbaumBooleanAlgebra (Th (AddHenkin (E.image embed_frm X)))).
  { eapply lemma1_of_1_3_8. }
  intros [SUBSET' IS_FILTER' COMPLETE' EQUICONSISTENT']. fold (MaximallyConsistentSet (AddHenkin (E.image embed_frm X))) in SUBSET', IS_FILTER', COMPLETE', EQUICONSISTENT'.
  fold Delta in SUBSET', IS_FILTER', COMPLETE', EQUICONSISTENT'.
  pose proof (theorem_of_1_3_10 X) as [? ? ? ? ? ?]. fold Delta in SUBSET, EQUICONSISTENT, CLOSED_infers, META_DN, IMPLICATION_FAITHFUL, FORALL_FAITHFUL. unnw.
  assert (CONSISTENT' : Delta ⊬ Bot_frm).
  { intros INCONSISTENT.
    assert (claim1 : ~ inconsistent' Delta).
    { red in EQUICONSISTENT'. rewrite <- EQUICONSISTENT'. rewrite <- cl_eq_Th. rewrite <- inconsistent_okay. rewrite <- AddHenkin_equiconsistent.
      - rewrite <- similar_equiconsistent with (Gamma := X).
        + rewrite inconsistent_iff; trivial.
        + rewrite <- embed_frms_spec. reflexivity.
      - ii. rewrite E.in_image_iff in H. destruct H as [q [-> IN]]. eapply embed_frm_HC_free.
    }
    contradiction claim1. rewrite <- inconsistent_iff in INCONSISTENT.
    rewrite inconsistent_okay in INCONSISTENT. eapply inconsistent_compatWith_isSubsetOf... eapply fact5_of_1_2_8...
  }
  rewrite CLOSED_infers. pattern p. revert p. eapply @frm_depth_lt_ind. intros [R ts | t1 t2 | p1 | p1 p2 | y p1]; simpl; i.
  - rewrite interpret_trms_trmModel_ivar_interpret. reflexivity.
  - do 2 rewrite interpret_trm_trmModel_ivar_interpret. reflexivity.
  - rewrite <- IH with (p' := p1). 2: lia. split.
    + intros INFERS1 INFERS2. contradiction CONSISTENT'.
      eapply ContradictionI with (A := p1); trivial.
    + intros NO. rewrite <- CLOSED_infers. eapply META_DN. intros YES. rewrite CLOSED_infers.
      contradiction NO. rewrite CLOSED_infers in YES. eapply NegationE. eapply ContradictionI with (A := Neg_frm p1).
      * eapply ByAssumption; done!.
      * eapply extend_infers with (Gamma := Delta); done!.
  - rewrite <- IH with (p' := p1). 2: lia. rewrite <- IH with (p' := p2). 2: lia. split.
    + intros INFERS1 INFERS2. eapply ImplicationE with (A := p1); trivial.
    + intros INFERS. rewrite <- CLOSED_infers. eapply IMPLICATION_FAITHFUL. do 2 rewrite CLOSED_infers; trivial.
  - unfold D. split.
    + intros INFERS t. rename y into x. set (s := one_subst x t).
      assert (IFF : interpret_frm trmModel ivar_interpret (subst_frm s p1) <-> interpret_frm trmModel (upd_env x t ivar_interpret) p1).
      { rewrite <- substitution_lemma_frm. eapply interpret_frm_ext. ii. unfold compose, upd_env, s, one_subst, cons_subst, nil_subst.
        destruct (eq_dec z x) as [EQ1 | NE1]; trivial. eapply interpret_trm_trmModel_ivar_interpret.
      }
      rewrite <- IFF. rewrite <- IH with (p' := subst_frm s p1). 2: rewrite subst_preserves_rank; lia.
      unfold s. eapply for_All_E; trivial.
    + intros INTERPRET. rewrite <- CLOSED_infers. eapply FORALL_FAITHFUL.
      intros t. eapply CLOSED_infers. rewrite -> IH with (p' := subst_frm (one_subst y t) p1). 2: rewrite subst_preserves_rank; lia.
      rewrite <- substitution_lemma_frm. eapply interpret_frm_ext with (env' := upd_env y (interpret_trm trmModel ivar_interpret t) ivar_interpret). ii. unfold compose, upd_env, one_subst, cons_subst, nil_subst.
      destruct (eq_dec z y) as [EQ1 | NE1]; trivial. eapply INTERPRET.
Qed.

End MODEL_EXISTENCE.

End FolHilbert.
