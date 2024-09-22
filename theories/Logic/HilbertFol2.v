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
  (FRESH2 : is_free_in_frm y (All_frm x A) = false)
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
    - ii...
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
    + destruct LE as [INFERS1 INFERS2]. unfold leProp in IH. simpl in IH. eapply extend_proves with (Gamma := E.insert x (E.fromList xs)). done!. rewrite <- Deduction_theorem. eapply IH. split.
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
          * eapply extend_infers. eapply PROVE. done!.
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

Section UNION.

Definition union_f (f : nat -> ensemble (frm L)) : ensemble (frm L) :=
  fun p => exists n, p \in f n.

Variable f : nat -> ensemble (frm L).

Hypothesis incl : forall n1 : nat, forall n2 : nat, forall LE : n1 <= n2, f n1 \subseteq f n2.

Lemma subset_union_f n
  : f n \subseteq union_f f.
Proof.
  intros q q_in. exists n. exact q_in.
Qed.

Lemma union_f_proves_iff p
  : union_f f ⊢ p <-> (exists n, f n ⊢ p).
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
  - intros [n INCONSISTENT]. eapply extend_proves with (Gamma := f n). eapply subset_union_f. exact INCONSISTENT.
Qed.

Hypothesis equiconsistent : forall n : nat, inconsistent (f n) <-> inconsistent (f (S n)).

Lemma equiconsistent_union_f
  : inconsistent (f 0) <-> inconsistent (union_f f).
Proof.
  split.
  - intros INCONSISTENT p. eapply extend_proves with (Gamma := f 0). eapply subset_union_f. eapply INCONSISTENT.
  - do 2 rewrite inconsistent_iff. intros INCONSISTENT. rewrite union_f_proves_iff in INCONSISTENT. destruct INCONSISTENT as [n PROVE]. induction n as [ | n IH].
    + eapply PROVE.
    + eapply IH. rewrite <- inconsistent_iff. rewrite equiconsistent. rewrite inconsistent_iff. eapply PROVE.
Qed.

End UNION.

End EXTRA1.

Section HENKIN.

#[local] Infix "=~=" := is_similar_to : type_scope.

Context {L : language}.

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
  : E.image embed_frm Gamma ⊢ embed_frm p.
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
      replace (subst_frm (embed_trm ∘ one_subst x t)%prg (embed_frm p)) with (subst_frm (one_subst x (embed_trm t)) (embed_frm p)).
      * eapply FA1.
      * eapply equiv_subst_in_frm_implies_subst_frm_same. ii. unfold one_subst, cons_subst, nil_subst. unfold "∘"%prg. destruct (eq_dec z x) as [EQ1 | NE1]; trivial.
    + simpl. eapply empty_proof_intro. eapply FA2.
      red. rewrite embed_fvs_frm. exact NOT_FREE.
    + simpl. eapply empty_proof_intro. eapply FA3.
    + eapply proves_reflexivity.
    + eapply for_Imp_I. eapply proves_symmetry. eapply for_ByHyp. done!.
    + eapply for_Imp_I. eapply for_Imp_I. eapply proves_transitivity with (t2 := embed_trm (Var_trm 1)); eapply for_ByHyp; done!.
    + rewrite embed_frm_Fun_eqAxm. eapply empty_proof_intro. exact (@EQN_FUN L' f).
    + rewrite embed_frm_Rel_eqAxm. eapply empty_proof_intro. exact (@EQN_REL L' R).
  - eapply for_Imp_E with (p := embed_frm q).
    + change (E.image embed_frm Gamma ⊢ embed_frm (Imp_frm q p)). eapply IH.
      * intros p' H_in. done!.
      * rewrite Deduction_theorem. eapply extend_proves with (Gamma := E.fromList (q :: ps)).
        { intros p' H_in. done!. }
        { exact PROVE. }
    + eapply for_ByHyp. rewrite E.in_image_iff. exists q. split; trivial. eapply INCL. simpl. left. trivial.
Qed.

Lemma embed_proves_inv (Gamma : ensemble (frm L)) (p : frm L)
  (PROVE : E.image embed_frm Gamma ⊢ embed_frm p)
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
  assert (PROVE : E.fromList (L.map embed_frm qs) ⊢ embed_frm p).
  { exists (L.map embed_frm qs). split. done!. econs. exact PF. }
  clear PF. revert Gamma p INCL PROVE. induction qs as [ | q qs IH]; i.
  - clear INCL. eapply extend_proves with (Gamma := E.empty). done.
    assert (ALPHA : p ≡ subst_frm (fun z : ivar => Var_trm (z / 2)) (subst_frm (fun z : ivar => Var_trm (z * 2)) p)).
    { symmetry. rewrite <- subst_compose_frm_spec. eapply subst_nil_frm. ii. unfold subst_compose. rewrite subst_trm_unfold. f_equal. exploit (div_mod_uniqueness (x * 2) 2 x 0); lia. }
    rewrite ALPHA. eapply extend_proves with (Gamma := E.image (subst_frm (fun z : ivar => Var_trm (z / 2))) E.empty). done!. eapply proves_substitutivity.
    rewrite <- twilight_frm'_embed. clear ALPHA. remember (twilight_frm' (embed_frm p)) as p' eqn: INVARIANT. revert INVARIANT PROVE. generalize (embed_frm p) as A.
    clear p Gamma; i. destruct PROVE as (ps&INCL&(PF)).
    assert (ps_spec : forall q : frm L', ~ L.In q ps).
    { intros q q_in. done!. }
    clear INCL. revert p' INVARIANT. induction PF; i.
    + contradiction (ps_spec p (or_introl eq_refl)).
    + eapply for_Imp_E with (p := twilight_frm' p).
      * eapply IHPF1. intros q' CONTRA; eapply ps_spec with (q := q'); ss!. simpl. congruence.
      * eapply IHPF2. intros q' CONTRA; eapply ps_spec with (q := q'); ss!. simpl. congruence.
    + subst. simpl. eapply for_All_I with (p := twilight_frm' q). done!. eapply IHPF. intros q' CONTRA; eapply ps_spec with (q := q'); ss!. reflexivity.
    + subst. simpl. eapply empty_proof_intro. eapply IMP1.
    + subst. simpl. eapply empty_proof_intro. eapply IMP2.
    + subst. simpl. eapply empty_proof_intro. eapply CP.
    + subst. simpl.
      assert (ALPHA : (twilight_frm' (subst_frm (one_subst x t) p)) ≡ subst_frm (one_subst (2 * x) (twilight_trm' t)) (twilight_frm' p)).
      { rewrite embed_frm_alpha. rewrite <- twilight_frm_decomposition. rewrite embed_subst_frm. transitivity (subst_frm (one_subst (2 * x) (twilight_trm t)) (twilight_frm p)).
        - erewrite subst_hsubst_compat_in_frm with (p := twilight_frm p). 2: ii; reflexivity. transitivity (subst_frm (one_subst (2 * x) (twilight_trm t)) (twilight_frm p)).
          + rewrite <- twilight_frm_one_hsubst. erewrite subst_hsubst_compat_in_frm. 2: ii; reflexivity. eapply alpha_equiv_eq_intro. f_equal.
            eapply equiv_hsubst_in_frm_implies_hsubst_frm_same. intros [z | z] FREE; cbn.
            * unfold one_subst, one_hsubst, cons_subst, cons_hsubst, nil_subst, nil_hsubst. destruct (eq_dec z x) as [EQ1 | NE1]; destruct (eqb _ _) as [ | ] eqn: H_OBS; rewrite eqb_spec in H_OBS; done!.
            * reflexivity.
          + erewrite <- subst_hsubst_compat_in_frm. 2: ii; reflexivity. reflexivity.
        - rewrite <- twilight_frm_decomposition. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
          intros u u_free. unfold one_subst, cons_subst, nil_subst, compose. destruct (eq_dec _ _) as [EQ | NE]; trivial. rewrite twilight_trm_decomposition. reflexivity.
      }
      rewrite ALPHA. eapply empty_proof_intro. eapply FA1.
    + subst. simpl. eapply empty_proof_intro. eapply FA2.
      red. rewrite <- embed_fvs_frm. rewrite <- twilight_frm_decomposition. rewrite Nat.mul_comm. rewrite <- twilight_frm_fvs. exact NOT_FREE.
    + subst. simpl. eapply empty_proof_intro. eapply FA3.
    + subst. simpl. eapply proves_reflexivity.
    + subst. eapply for_Imp_I. eapply proves_symmetry. eapply for_ByHyp. done!.
    + subst. eapply for_Imp_I. eapply for_Imp_I. eapply proves_transitivity with (t2 := twilight_trm' (Var_trm 1)); eapply for_ByHyp; done!.
    + subst. rewrite <- embed_frm_Fun_eqAxm. rewrite twilight_frm'_embed. eapply extend_proves with (Gamma := E.image (subst_frm (fun z : ivar => Var_trm (z * 2))) E.empty). done!.
      eapply proves_substitutivity. eapply empty_proof_intro. eapply EQN_FUN.
    + subst. rewrite <- embed_frm_Rel_eqAxm. rewrite twilight_frm'_embed. eapply extend_proves with (Gamma := E.image (subst_frm (fun z : ivar => Var_trm (z * 2))) E.empty). done!.
      eapply proves_substitutivity. eapply empty_proof_intro. eapply EQN_REL.
  - eapply for_Imp_E with (p := q).
    + eapply IH.
      * intros p' H_in. exploit (INCL p'). ss!. intros IN. ss!.
      * simpl. rewrite Deduction_theorem. eapply extend_proves with (Gamma := E.fromList (L.map embed_frm (q :: qs))).
        { intros p' H_in. done!. }
        { exact PROVE. }
    + eapply for_ByHyp. exploit (INCL (embed_frm q)). ss!. intros IN. ss!. apply embed_frm_inj in H; subst x; done.
Qed.

Theorem embed_frm_proves_iff (Gamma : ensemble (frm L)) (p : frm L)
  : E.image embed_frm Gamma ⊢ embed_frm p <-> Gamma ⊢ p.
Proof.
  split; [eapply embed_proves_inv | eapply embed_proves].
Qed.

Theorem similar_equiconsistent (Gamma : ensemble (frm L)) (Gamma' : ensemble (frm L'))
  (SIM : Gamma =~= Gamma')
  : inconsistent Gamma <-> inconsistent Gamma'.
Proof.
  split; intros INCONSISTENT.
  - rewrite inconsistent_iff in INCONSISTENT. rewrite inconsistent_iff.
    rewrite <- embed_frms_spec in SIM. rewrite <- SIM.
    change (E.image embed_frm Gamma ⊢ embed_frm Bot_frm). now eapply embed_proves.
  - intros p. pose proof (INCONSISTENT (embed_frm p)) as claim.
    rewrite <- embed_frms_spec in SIM. rewrite <- SIM in claim.
    eapply embed_proves_inv. exact claim.
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

Definition AddHenkin (X : ensemble (frm L)) : ensemble (frm L') :=
  union_f (addHenkin (E.image embed_frm X)).

Theorem AddHenkin_equiconsistent (X : ensemble (frm L))
  : inconsistent X <-> inconsistent (AddHenkin X).
Proof.
  transitivity (inconsistent (E.image embed_frm X)).
  - eapply similar_equiconsistent. rewrite <- embed_frms_spec. reflexivity.
  - unfold AddHenkin. rewrite <- equiconsistent_union_f.
    + simpl. reflexivity.
    + eapply addHenkin_incl.
    + intros n. eapply addHenkin_equiconsistent. intros p c IN. rewrite E.in_image_iff in IN. destruct IN as [q [-> IN]]. eapply embed_frm_HC_free.
Qed.

Lemma Henkin_complete (Gamma : ensemble (frm L')) (x : ivar) (phi : frm L')
  (IN : All_frm x phi \in Gamma)
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

End HENKIN.

End FolHilbert.
