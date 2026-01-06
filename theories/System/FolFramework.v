Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Logic.BasicFol.
Require Import PnV.Logic.BasicFol2.
Require Import PnV.Logic.HilbertFol.
Require Import PnV.Logic.HilbertFol2.
Require Import PnV.System.P.
Require Import PnV.Data.Vector.
Require Import PnV.System.Lambda1.
Require Import PnV.System.STLC.
Require Import PnV.Logic.ClassicalFol.

#[global]
Coercion named_var (nm : name) : ivar :=
  un_name nm.

#[global]
Instance Similarity_name_ivar : Similarity Name.t ivar :=
  fun nm : name => fun x : ivar => named_var nm = x.

Module FolViewer.

End FolViewer.

Module ExternalSyntax.

Export ChurchStyleStlc.

Section HOAS.

Variant fol_basic_types : Set :=
  | trm_bty : fol_basic_types
  | trms_bty (arity : nat) : fol_basic_types
  | frm_bty : fol_basic_types.

Context {L : InternalSyntax.language}.

Variant fol_symbols : Set :=
  | Function_symbol (f : L.(function_symbols))
  | Constant_symbol (c : L.(constant_symbols))
  | Relation_symbol (R : L.(relation_symbols))
  | Nil_symbol
  | Cons_symbol (arity : nat)
  | Equality_symbol
  | Contradiction_symbol
  | Negation_symbol
  | Conjunction_symbol
  | Disjunction_symbol
  | Implication_symbol
  | Biconditional_symbol
  | UniversalQuantifier_symbol
  | ExistentialQuantifier_symbol.

End HOAS.

End ExternalSyntax.
