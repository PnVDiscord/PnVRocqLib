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

Declare Custom Entry fol_view.
Declare Custom Entry subst_view.
Reserved Notation "'\(' EXPR '\)'" (EXPR custom fol_view at level 10, no associativity, format "'\(' EXPR '\)'", at level 0).

Declare Scope trm_scope.
Declare Scope trms_scope.
Declare Scope frm_scope.
Declare Scope subst_scope.

Module FolViewer.

Notation "'\(' EXPR '\)'" := EXPR : frm_scope.
Notation "'\(' EXPR '\)'" := (EXPR : frm _).

Notation "'(' p ')'" := p (p custom fol_view at level 10, no associativity, in custom fol_view at level 0).

#[global] Bind Scope trm_scope with trm.
Notation "'V' x" := (Var_trm (named_var x)) (x constr at level 0, in custom fol_view at level 5).
Notation "'F' f ts" := (Fun_trm f ts) (f constr, ts custom fol_view at level 0, in custom fol_view at level 5).
Notation "'C' c" := (Con_trm c) (c constr, in custom fol_view at level 5).

#[global] Bind Scope trms_scope with trms.
Notation "'[' ']'" := (O_trms) (no associativity, in custom fol_view at level 0).
Notation "t '::' ts" := (S_trms _ t ts) (right associativity, t custom fol_view, ts custom fol_view, in custom fol_view at level 5).

#[global] Bind Scope frm_scope with frm.
Notation "'`[' s ']' p" := (subst_frm s p) (s custom subst_view at level 10, p custom fol_view at level 0, in custom fol_view at level 10, format "`[ s ] p").
Notation "'`(' p ')' '[' x := t ']'" := (subst1 (named_var x) t p) (x constr, t custom fol_view at level 10, p custom fol_view at level 7, in custom fol_view at level 10, format "`( p ) [  x  :=  t  ]").
Notation "'⊥'" := (Bot_frm) (in custom fol_view at level 0).
Notation "'R' R ts" := (Rel_frm R ts) (R constr, ts custom fol_view at level 5, in custom fol_view at level 5).
Notation "t1 '=' t2" := (Eqn_frm t1 t2) (no associativity, in custom fol_view at level 5).
Notation "'¬' p" := (Neg_frm p) (p custom fol_view at level 7, in custom fol_view at level 7).
Notation "'∀' x ',' p" := (All_frm (named_var x) p) (x constr at level 0, p custom fol_view at level 7, in custom fol_view at level 7).
Notation "'∃' x ',' p" := (Exs_frm (named_var x) p) (x constr at level 0, p custom fol_view at level 7, in custom fol_view at level 7).
Notation "p '∧' q" := (Con_frm p q) (p custom fol_view, q custom fol_view, no associativity, in custom fol_view at level 8).
Notation "p '∨' q" := (Dis_frm p q) (p custom fol_view, q custom fol_view, no associativity, in custom fol_view at level 9).
Notation "p '→' q" := (Imp_frm p q) (p custom fol_view, q custom fol_view, no associativity, in custom fol_view at level 10).
Notation "p '↔' q" := (Iff_frm p q) (p custom fol_view, q custom fol_view, no associativity, in custom fol_view at level 10).
Notation "p" := p (p ident, in custom fol_view at level 0).

Bind Scope subst_scope with subst.
Notation "s2 '∘' s1" := (subst_compose s1 s2) (right associativity, in custom subst_view at level 4) : subst_scope.
Notation "s ';' t '/' x" := (cons_subst (named_var x) t s) (left associativity, x constr at level 0, t custom fol_view at level 5, in custom subst_view at level 10).
Notation "t '/' x" := (one_subst (named_var x) t) (no associativity, x constr at level 0, t custom fol_view at level 5, in custom subst_view at level 10).
Notation "'ι'" := (nil_subst) (no associativity, in custom subst_view at level 0).

Notation "p '≡α' q" := (alpha_equiv p q) (no associativity, at level 70) : type_scope.

End FolViewer.

Declare Custom Entry syntax_view.
Declare Scope raw_syntax_scope.

Reserved Notation "'$' EXPR '$'" (EXPR custom syntax_view at level 10, no associativity, format "'$' EXPR '$'", at level 0).

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

Definition mk_fol : language :=
  {|
    basic_types := fol_basic_types;
    constants := fol_symbols;
  |}.

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

#[local] Notation typ := (typ mk_fol).
#[local] Notation ctx := (ctx mk_fol).

Import ChurchStyleSTLC.

Example L_in_example3
  : @Typing mk_fol fol_signature [("x"%name, @bty mk_fol trm_bty)] (App_trm (@Con_trm mk_fol ExistentialQuantifier_symbol) (App_trm (@Con_trm mk_fol Equality_symbol) (Var_trm "x"))) (@bty mk_fol frm_bty).
Proof.
  eapply App_typ with (ty1 := (@bty mk_fol trm_bty -> @bty mk_fol frm_bty)%typ).
  - econs 4.
  - eapply App_typ with (ty1 := (@bty mk_fol trm_bty)%typ).
    + econs 4.
    + econs 1. econs 1; reflexivity.
Defined.

Example L_in_example3_unfold
  : NbE L_in_example3 = App_trm (@Con_trm mk_fol ExistentialQuantifier_symbol) (Lam_trm "a0" (@bty mk_fol trm_bty) (App_trm (App_trm (@Con_trm mk_fol Equality_symbol) (Var_trm "x")) (Var_trm "a0"))).
Proof.
  reflexivity.
Qed.

Example L_in_example4 c
  : @Typing mk_fol fol_signature [("p"%name, (@bty mk_fol trm_bty -> @bty mk_fol frm_bty)%typ)] (App_trm (Lam_trm "x" (@bty mk_fol trm_bty) (App_trm (Var_trm "p") (Var_trm "x"))) (@Con_trm mk_fol (Constant_symbol c))) (@bty mk_fol frm_bty).
Proof.
  eapply App_typ with (ty1 := (@bty mk_fol trm_bty)%typ).
  - eapply Lam_typ. eapply App_typ with (ty1 := (@bty mk_fol trm_bty)).
    + econs 1. econs 2.
      { cbv. left. repeat econs. }
      { econs 1; reflexivity. }
    + econs 1. econs 1; reflexivity.
  - econs 4.
Defined.

Example L_in_example4_unfold c
  : NbE (L_in_example4 c) = (App_trm (Var_trm "p") (@Con_trm mk_fol (Constant_symbol c))).
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

Section EXAMPLE.

Import FolNotations.
Import FolHilbert.
Import FolViewer.

#[local] Notation "t1 '∈' t2" := (@Rel_frm L_in symbol_IN (@S_trms L_in 1 t1 (@S_trms L_in 0 t2 (@O_trms L_in)))) (no associativity, in custom fol_view at level 6).

Example L_in_example1
  : \(`[V "x" / "y"](∀ "x", V "x" ∈ V "y")\) ≡α \(∀ "z", V "z" ∈ V "x"\).
Proof.
  eapply alpha_All_frm with (z := un_name "z"); reflexivity.
Qed.

Example L_in_example2
  : E.empty ⊢ \(∀ "z", (V "z" ∈ V "x" → V "z" ∈ V "x")\).
Proof.
  eapply HilbertCalculus_countable_complete.
  intros STRUCT rho H_Gamma; simpl. ss!.
Qed.

End EXAMPLE.

End ObjectZFC.
