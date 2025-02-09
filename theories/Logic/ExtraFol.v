Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.Data.Vector.
Require Import PnV.Logic.BasicFol.
Require Import PnV.Logic.BasicFol2.
Require Import PnV.Logic.HilbertFol.

Module ND.

Section NATURAL_DEDUCTION.

#[local] Infix " \in " := E.In.
#[local] Infix " \subseteq " := E.isSubsetOf.
#[local] Notation In := List.In.

Context {L : language}.

Inductive infers (Gamma : list (frm L)) : frm L -> Set :=
  | ByAssumption C
    (IN : In C Gamma)
    : Gamma ⊢ C
  | EquationI t
    : Gamma ⊢ Eqn_frm t t
  | EquationE A x t1 t2
    (INFERS1 : Gamma ⊢ Eqn_frm t1 t2)
    (INFERS2 : Gamma ⊢ subst_frm (one_subst x t1) A)
    : Gamma ⊢ subst_frm (one_subst x t2) A
  | UniversalI x y A
    (FRESH1 : forall p, In p Gamma -> is_free_in_frm y p = false)
    (FRESH2 : is_free_in_frm y (All_frm x A) = false)
    (INFERS1 : Gamma ⊢ subst_frm (one_subst x (Var_trm y)) A)
    : Gamma ⊢ All_frm x A
  | UniversalE x t A
    (INFERS1 : Gamma ⊢ All_frm x A)
    : Gamma ⊢ subst_frm (one_subst x t) A
  | ExistentialI x t A
    (INFERS1 : Gamma ⊢ subst_frm (one_subst x t) A)
    : Gamma ⊢ Exs_frm x A
  | ExistentialE x y A B
    (FRESH1 : forall p, In p Gamma -> is_free_in_frm y p = false)
    (FRESH2 : is_free_in_frm y (Exs_frm x A) = false)
    (FRESH3 : is_free_in_frm y B = false)
    (INFERS1 : Gamma ⊢ Exs_frm x A)
    (INFERS2 : subst_frm (one_subst x (Var_trm y)) A :: Gamma ⊢ B)
    : Gamma ⊢ B
  | ContradictionI A
    (INFERS1 : Gamma ⊢ A)
    (INFERS2 : Gamma ⊢ Neg_frm A)
    : Gamma ⊢ Bot_frm
  | ContradictionE A
    (INFERS1 : Gamma ⊢ Bot_frm)
    : Gamma ⊢ A
  | NegationI A
    (INFERS1 : A :: Gamma ⊢ Bot_frm)
    : Gamma ⊢ Neg_frm A
  | NegationE A
    (INFERS1 : Neg_frm A :: Gamma ⊢ Bot_frm)
    : Gamma ⊢ A
  | ConjunctionI A B
    (INFERS1 : Gamma ⊢ A)
    (INFERS2 : Gamma ⊢ B)
    : Gamma ⊢ Con_frm A B
  | ConjunctionE1 A B
    (INFERS1 : Gamma ⊢ Con_frm A B)
    : Gamma ⊢ A
  | ConjunctionE2 A B
    (INFERS1 : Gamma ⊢ Con_frm A B)
    : Gamma ⊢ B
  | DisjunctionI1 A B
    (INFERS1 : Gamma ⊢ A)
    : Gamma ⊢ Dis_frm A B
  | DisjunctionI2 A B
    (INFERS1 : Gamma ⊢ B)
    : Gamma ⊢ Dis_frm A B
  | DisjunctionE A B C
    (INFERS1 : Gamma ⊢ Dis_frm A B)
    (INFERS2 : A :: Gamma ⊢ C)
    (INFERS2 : B :: Gamma ⊢ C)
    : Gamma ⊢ Dis_frm A B
  | ImplicationI A B
    (INFERS1 : A :: Gamma ⊢ B)
    : Gamma ⊢ Imp_frm A B
  | ImplicationE A B
    (INFERS1 : Gamma ⊢ Imp_frm A B)
    (INFERS2 : Gamma ⊢ A)
    : Gamma ⊢ B
  | BiconditionalI A B
    (INFERS1 : A :: Gamma ⊢ B)
    (INFERS2 : B :: Gamma ⊢ A)
    : Gamma ⊢ Iff_frm A B
  | BiconditionalE1 A B
    (INFERS1 : Gamma ⊢ Iff_frm A B)
    (INFERS2 : Gamma ⊢ A)
    : Gamma ⊢ B
  | BiconditionalE2 A B
    (INFERS1 : Gamma ⊢ Iff_frm A B)
    (INFERS2 : Gamma ⊢ B)
    : Gamma ⊢ A
  where "Gamma ⊢ C" := (infers Gamma C) : type_scope.

End NATURAL_DEDUCTION.

End ND.
