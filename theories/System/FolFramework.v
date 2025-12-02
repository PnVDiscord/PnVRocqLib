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

#[global]
Instance mk_fol : language :=
  { basic_types := fol_basic_types
  ; constants := fol_symbols
  }.

#[global]
Instance fol_signature : signature mk_fol :=
  fun symbol : fol_symbols =>
  match symbol return typ mk_fol with
  | Function_symbol f => (arr mk_fol (bty mk_fol (trms_bty (function_arity_table L f))) (bty mk_fol (trm_bty)))
  | Constant_symbol c => (bty mk_fol (trm_bty))
  | Relation_symbol R => (arr mk_fol (bty mk_fol (trms_bty (relation_arity_table L R))) (bty mk_fol (frm_bty)))
  | Nil_symbol => (bty mk_fol (trms_bty 0))
  | Cons_symbol n => (arr mk_fol (bty mk_fol (trm_bty)) (arr mk_fol (bty mk_fol (trms_bty n)) (bty mk_fol (trms_bty (S n)))))
  | Equality_symbol => (arr mk_fol (bty mk_fol (trm_bty)) (arr mk_fol (bty mk_fol (trm_bty)) (bty mk_fol (frm_bty))))
  | Contradiction_symbol => (bty mk_fol (frm_bty))
  | Negation_symbol => (arr mk_fol (bty mk_fol (frm_bty)) (bty mk_fol (frm_bty)))
  | Conjunction_symbol => (arr mk_fol (bty mk_fol (frm_bty)) (arr mk_fol (bty mk_fol (frm_bty)) (bty mk_fol (frm_bty))))
  | Disjunction_symbol => (arr mk_fol (bty mk_fol (frm_bty)) (arr mk_fol (bty mk_fol (frm_bty)) (bty mk_fol (frm_bty))))
  | Implication_symbol => (arr mk_fol (bty mk_fol (frm_bty)) (arr mk_fol (bty mk_fol (frm_bty)) (bty mk_fol (frm_bty))))
  | Biconditional_symbol => (arr mk_fol (bty mk_fol (frm_bty)) (arr mk_fol (bty mk_fol (frm_bty)) (bty mk_fol (frm_bty))))
  | UniversalQuantifier_symbol => (arr mk_fol (arr mk_fol (bty mk_fol (trm_bty)) (bty mk_fol (frm_bty))) (bty mk_fol (frm_bty)))
  | ExistentialQuantifier_symbol => (arr mk_fol (arr mk_fol (bty mk_fol (trm_bty)) (bty mk_fol (frm_bty))) (bty mk_fol (frm_bty)))
  end.

Import ChurchStyleSTLC.

#[local] Notation typ := (typ mk_fol).
#[local] Notation ctx := (ctx mk_fol).
#[local] Notation bty := (bty mk_fol).

Example L_in_example3
  : Typing [("x"%name, bty trm_bty)] (App_trm (Con_trm ExistentialQuantifier_symbol) (App_trm (Con_trm Equality_symbol) (Var_trm "x"))) (bty frm_bty).
Proof.
  eapply App_typ with (ty1 := (bty trm_bty -> bty frm_bty)%typ).
  - econs 4.
  - eapply App_typ with (ty1 := (bty trm_bty)%typ).
    + econs 4.
    + econs 1. econs 1; reflexivity.
Defined.

Example L_in_example3_unfold
  : NbE L_in_example3 = App_trm (Con_trm ExistentialQuantifier_symbol) (Lam_trm "a0" (bty trm_bty) (App_trm (App_trm (Con_trm Equality_symbol) (Var_trm "x")) (Var_trm "a0"))).
Proof.
  reflexivity.
Qed.

Example L_in_example4 c
  : Typing [("p"%name, (bty trm_bty -> bty frm_bty)%typ)] (App_trm (Lam_trm "x" (bty trm_bty) (App_trm (Var_trm "p") (Var_trm "x"))) (Con_trm (Constant_symbol c))) (@bty frm_bty).
Proof.
  eapply App_typ with (ty1 := (bty trm_bty)%typ).
  - eapply Lam_typ. eapply App_typ with (ty1 := (bty trm_bty)).
    + econs 1. econs 2.
      { cbv. left. repeat econs. }
      { econs 1; reflexivity. }
    + econs 1. econs 1; reflexivity.
  - econs 4.
Defined.

Example L_in_example4_unfold c
  : NbE (L_in_example4 c) = (App_trm (Var_trm "p") (Con_trm (Constant_symbol c))).
Proof.
  reflexivity.
Qed.

Example L_in_example5
  : @Typing mk_fol fol_signature [("p"%name, ((bty trm_bty -> bty frm_bty) -> bty frm_bty)%typ)] (Var_trm "p") ((bty trm_bty -> bty frm_bty) -> bty frm_bty)%typ.
Proof.
  eapply Var_typ. econs 1; reflexivity.
Defined.

Example L_in_example5_unfold
  : NbE (L_in_example5) = Lam_trm "a0" (bty trm_bty -> bty frm_bty)%typ (App_trm (Var_trm "p") (Lam_trm "a00" (bty trm_bty) (App_trm (Var_trm "a0") (Var_trm "a00")))).
Proof.
  reflexivity.
Qed.

End HOAS.

#[global] Arguments fol_symbols : clear implicits.
#[global] Arguments mk_fol : clear implicits.
#[global] Arguments fol_signature : clear implicits.

End ExternalSyntax.

Module ObjectZFC.

Variant L_in_relation_symbols : Set :=
  | symbol_IN : L_in_relation_symbols.

#[global, program]
Instance L_in_relation_symbols_isCountable : isCountable L_in_relation_symbols :=
  { encode _ := 0
  ; decode _ := Some symbol_IN
  }.
Next Obligation.
  destruct x; reflexivity.
Qed.

Definition L_in : language :=
  {|
    function_symbols := Empty_set;
    relation_symbols := L_in_relation_symbols;
    constant_symbols := Empty_set;
    function_arity_table := Empty_set_rect (fun _ => nat);
    relation_arity_table := fun _ => 2;
    function_arity_gt_0 := Empty_set_ind _;
    relation_arity_gt_0 := fun _ => (@le_S 1 1 (@le_n 1));
  |}.

End ObjectZFC.
