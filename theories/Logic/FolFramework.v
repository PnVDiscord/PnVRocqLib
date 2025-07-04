Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Logic.BasicFol.
Require Import PnV.Logic.BasicFol2.
Require Import PnV.Logic.HilbertFol.
Require Import PnV.Logic.HilbertFol2.
Require Import PnV.System.P.
Require Import PnV.Data.Vector.
Require Import PnV.System.Lambda1.

#[global]
Coercion named_var (nm : name) : ivar :=
  un_name nm.

#[global]
Instance Similarity_name_ivar : Similarity Name.t ivar :=
  fun nm : name => fun x : ivar => named_var nm = x.

Declare Custom Entry trm_view.
Declare Custom Entry trms_view.
Declare Custom Entry frm_view.
Declare Custom Entry subst_view.
Reserved Notation "'\(' EXPR '\)'" (EXPR custom frm_view at level 10, no associativity, format "'\(' EXPR '\)'", at level 0).

Declare Scope trm_scope.
Declare Scope trms_scope.
Declare Scope frm_scope.
Declare Scope subst_scope.

Module FolViewer.

Notation "'\(' EXPR '\)'" := EXPR : frm_scope.
Notation "'\(' EXPR '\)'" := (EXPR : frm _).

#[global] Bind Scope trm_scope with trm.
Notation "'`[' s ']' t" := (subst_trm s t) (s custom subst_view at level 10, t custom trm_view at level 5, in custom trm_view at level 5, format "`[ s ] t").
Notation "'V' x" := (Var_trm (named_var x)) (x constr at level 0, in custom trm_view at level 5).
Notation "'F' f ts" := (Fun_trm f ts) (f constr, ts custom trms_view at level 0, in custom trm_view at level 5).
Notation "'C' c" := (Con_trm c) (c constr, in custom trm_view at level 5).
Notation "t" := t (t ident, in custom trm_view at level 0).
Notation "'(' t ')'" := t (t custom trm_view at level 5, no associativity, in custom trm_view at level 0).

#[global] Bind Scope trms_scope with trms.
Notation "'`[' s ']' ts" := (subst_trms s ts) (s custom subst_view at level 10, ts custom trms_view at level 5, in custom trms_view at level 5, format "`[ s ] ts").
Notation "'[' ']'" := (O_trms) (no associativity, in custom trms_view at level 0).
Notation "t '::' ts" := (S_trms _ t ts) (right associativity, t custom trm_view, ts custom trms_view, in custom trms_view at level 5).
Notation "ts" := ts (ts ident, in custom trms_view at level 0).
Notation "'(' ts ')'" := ts (ts custom trms_view at level 5, no associativity, in custom trms_view at level 0).

#[global] Bind Scope frm_scope with frm.
Notation "'`[' s ']' p" := (subst_frm s p) (s custom subst_view at level 10, p custom frm_view at level 0, in custom frm_view at level 10, format "`[ s ] p").
Notation "'`(' p ')' '[' x := t ']'" := (subst1 (named_var x) t p) (x constr, t custom trm_view at level 10, p custom frm_view at level 7, in custom frm_view at level 10, format "`( p ) [  x  :=  t  ]").
Notation "'⊥'" := (Bot_frm) (in custom frm_view at level 0).
Notation "'R' R ts" := (Rel_frm R ts) (R constr, ts custom trms_view at level 5, in custom frm_view at level 5).
Notation "t1 '=' t2" := (Eqn_frm t1 t2) (t1 custom trm_view at level 5, t2 custom trm_view at level 5, in custom frm_view at level 5).
Notation "'¬' p" := (Neg_frm p) (p custom frm_view at level 7, in custom frm_view at level 7).
Notation "'∀' x ',' p" := (All_frm (named_var x) p) (x constr at level 0, p custom frm_view at level 7, in custom frm_view at level 7).
Notation "'∃' x ',' p" := (Exs_frm (named_var x) p) (x constr at level 0, p custom frm_view at level 7, in custom frm_view at level 7).
Notation "p '∧' q" := (Con_frm p q) (p custom frm_view, q custom frm_view, no associativity, in custom frm_view at level 8).
Notation "p '∨' q" := (Dis_frm p q) (p custom frm_view, q custom frm_view, no associativity, in custom frm_view at level 9).
Notation "p '→' q" := (Imp_frm p q) (p custom frm_view, q custom frm_view, no associativity, in custom frm_view at level 10).
Notation "p '↔' q" := (Iff_frm p q) (p custom frm_view, q custom frm_view, no associativity, in custom frm_view at level 10).
Notation "p" := p (p ident, in custom frm_view at level 0).
Notation "'(' p ')'" := p (p custom frm_view at level 10, no associativity, in custom frm_view at level 0).

Bind Scope subst_scope with subst.
Notation "s2 '∘' s1" := (subst_compose s1 s2) (right associativity, in custom subst_view at level 4) : subst_scope.
Notation "s ';' t '/' x" := (cons_subst (named_var x) t s) (left associativity, x constr at level 0, t custom trm_view at level 5, in custom subst_view at level 10).
Notation "t '/' x" := (one_subst (named_var x) t) (no associativity, x constr at level 0, t custom trm_view at level 5, in custom subst_view at level 10).
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

Lemma typ_eq_pirrel (ty1 : typ) (ty2 : typ)
  : forall EQ1 : ty1 = ty2, forall EQ2 : ty1 = ty2, EQ1 = EQ2.
Proof.
  eapply @eq_pirrel_fromEqDec.
  red; do 3 decide equality.
Qed.

Definition interpret_bty (bty : fol_basic_types) : Set :=
  match bty with
  | trm_bty => InternalSyntax.trm L
  | trms_bty arity => InternalSyntax.trms L arity
  | frm_bty => InternalSyntax.frm L
  end.

Fixpoint interpret_typ (ty : typ) : Set :=
  match ty with
  | bty _ bty_fol => interpret_bty bty_fol
  | arr _ D C => interpret_typ D -> interpret_typ C
  end.

Fixpoint interpret_ctx (Gamma : ctx) : Set :=
  match Gamma with
  | [] => unit
  | (x', ty') :: Gamma' => interpret_typ ty' * interpret_ctx Gamma'
  end.

Fixpoint interpret_Lookup {x} {ty} {Gamma} (LOOKUP : Lookup x ty Gamma) : interpret_ctx Gamma -> interpret_typ ty :=
  match LOOKUP in Lookup _ _ Gamma return interpret_ctx Gamma -> interpret_typ ty with
  | Lookup_Z _ _ Gamma' x' ty' x_eq ty_eq => fun rho : interpret_typ ty' * interpret_ctx Gamma' => match ty_eq in eq _ ty' return interpret_typ ty' * interpret_ctx Gamma' -> interpret_typ ty with eq_refl => fst end rho
  | Lookup_S _ _ Gamma' x' ty' x_ne LOOKUP => fun rho : interpret_typ ty' * interpret_ctx Gamma' => interpret_Lookup LOOKUP (snd rho)
  end.

End HOAS.

#[global] Arguments fol_symbols : clear implicits.
#[global] Arguments mk_fol : clear implicits.
#[global] Arguments fol_signature : clear implicits.

End ExternalSyntax.

Module ObjectZFC.

Variant L_in_relation_symbols : Set :=
  | symbol_IN : L_in_relation_symbols.

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

Import FolViewer.

#[local] Notation "t1 '∈' t2" := (@Rel_frm L_in symbol_IN (@S_trms L_in 1 t1 (@S_trms L_in 0 t2 (@O_trms L_in)))) (t1 custom trm_view at level 5, t2 custom trm_view at level 5, in custom frm_view at level 6).

Example fol_viewer_example1
  : \(`[V "x" / "y"](∀ "x", V "x" ∈ V "y")\) ≡α \(∀ "z", V "z" ∈ V "x"\).
Proof.
  eapply alpha_All_frm with (z := un_name "z"); reflexivity.
Qed.

End EXAMPLE.

End ObjectZFC.
