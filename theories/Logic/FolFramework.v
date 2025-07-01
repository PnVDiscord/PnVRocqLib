Require Import PnV.Prelude.Prelude.
Require Import PnV.Logic.BasicFol.
Require Import PnV.Logic.BasicFol2.
Require Import PnV.Logic.HilbertFol.
Require Import PnV.Logic.HilbertFol2.
Require Import PnV.System.P.
Require Import PnV.Data.Vector.

#[global]
Coercion named_var (nm : name) : ivar :=
  un_name nm.

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

Inductive typ : Set :=
  | arr (D : typ) (C : typ) : typ
  | trm : typ
  | frm : typ
  | vec (n : nat) : typ.

Declare Scope typ_scope.
Bind Scope typ_scope with typ.
Delimit Scope typ_scope with typ.

Notation "D -> C" := (ExternalSyntax.arr D C) : typ_scope.

Section STLC_STYLE_DEFINITION.

#[local] Open Scope typ_scope.

Context {L : language}.

Fixpoint typ_semantics (Ty : typ) : Set :=
  match Ty with
  | D -> C => typ_semantics D -> typ_semantics C
  | trm => InternalSyntax.trm L
  | frm => InternalSyntax.frm L
  | vec n => InternalSyntax.trms L n
  end.

Inductive raw_syntax : Set :=
  | Var_syn (x : name) : raw_syntax
  | App_syn (ast1 : raw_syntax) (ast2 : raw_syntax) : raw_syntax
  | Lam_syn (x : name) (x_ty : typ) (ast1 : raw_syntax) : raw_syntax
  | Fun_trm (f : L.(function_symbols)) (ts : raw_syntax) : raw_syntax
  | Con_trm (c : L.(constant_symbols)) : raw_syntax
  | Rel_frm (R : L.(relation_symbols)) (ts : raw_syntax) : raw_syntax
  | Eqn_frm (t1 : raw_syntax) (t2 : raw_syntax) : raw_syntax
  | Bot_frm : raw_syntax
  | Neg_frm (p1 : raw_syntax) : raw_syntax
  | Con_frm (p1 : raw_syntax) (p2 : raw_syntax) : raw_syntax
  | Dis_frm (p1 : raw_syntax) (p2 : raw_syntax) : raw_syntax
  | Imp_frm (p1 : raw_syntax) (p2 : raw_syntax) : raw_syntax
  | Iff_frm (p1 : raw_syntax) (p2 : raw_syntax) : raw_syntax
  | All_frm (x : name) (p1 : raw_syntax) : raw_syntax
  | Exs_frm (x : name) (p1 : raw_syntax) : raw_syntax
  | Nil_vec : raw_syntax
  | Cons_vec (elem : raw_syntax) (elems : raw_syntax) : raw_syntax.

Inductive typing (Gamma : list (name * typ)) : raw_syntax -> typ -> Prop :=
  | Var_syn_typing x ty
    (LOOKUP : L.lookup x Gamma = Some ty)
    : typing Gamma (Var_syn x) ty
  | App_syn_typing ast1 ast2 ty1 ty2
    (TYP1 : typing Gamma ast1 (ty1 -> ty2))
    (TYP2 : typing Gamma ast2 ty1)
    : typing Gamma (App_syn ast1 ast2) ty2
  | Lam_syn_typing x ast1 ty1 ty2
    (TYP1 : typing ((x, ty1) :: Gamma) ast1 ty2)
    : typing Gamma (Lam_syn x ty1 ast1) (ty1 -> ty2)
  | Fun_trm_typing f ts
    (TYP1 : typing Gamma ts (vec (function_arity_table L f)))
    : typing Gamma (Fun_trm f ts) trm
  | Con_trm_typing c
    : typing Gamma (Con_trm c) trm
  | Rel_frm_typing R ts
    (TYP1 : typing Gamma ts (vec (relation_arity_table L R)))
    : typing Gamma (Rel_frm R ts) frm
  | Eqn_frm_typing t1 t2
    (TYP1 : typing Gamma t1 trm)
    (TYP2 : typing Gamma t2 trm)
    : typing Gamma (Eqn_frm t1 t2) frm
  | Bot_frm_typing
    : typing Gamma (Bot_frm) frm
  | Neg_frm_typing p1
    (TYP1 : typing Gamma p1 frm)
    : typing Gamma (Neg_frm p1) frm
  | Con_frm_typing p1 p2
    (TYP1 : typing Gamma p1 frm)
    (TYP2 : typing Gamma p2 frm)
    : typing Gamma (Con_frm p1 p2) frm
  | Dis_frm_typing p1 p2
    (TYP1 : typing Gamma p1 frm)
    (TYP2 : typing Gamma p2 frm)
    : typing Gamma (Dis_frm p1 p2) frm
  | Imp_frm_typing p1 p2
    (TYP1 : typing Gamma p1 frm)
    (TYP2 : typing Gamma p2 frm)
    : typing Gamma (Imp_frm p1 p2) frm
  | Iff_frm_typing p1 p2
    (TYP1 : typing Gamma p1 frm)
    (TYP2 : typing Gamma p2 frm)
    : typing Gamma (Iff_frm p1 p2) frm
  | All_frm_typing x p1
    (TYP1 : typing ((x, trm) :: Gamma) p1 frm)
    : typing Gamma (All_frm x p1) frm
  | Exs_frm_typing x p1
    (TYP1 : typing ((x, trm) :: Gamma) p1 frm)
    : typing Gamma (Exs_frm x p1) frm
  | Nil_vec_typing
    : typing Gamma (Nil_vec) (vec O)
  | Cons_vec_typing n elem elems
    (TYP1 : typing Gamma elem trm)
    (TYP2 : typing Gamma elems (vec n))
    : typing Gamma (Cons_vec elem elems) (vec (S n)).

Definition is_trm_typ (ty : typ) : bool :=
  match ty with
  | trm => true
  | _ => false
  end.

Definition is_frm_typ (ty : typ) : bool :=
  match ty with
  | frm => true
  | _ => false
  end.

Fixpoint is_pred_typ (ty : typ) : bool :=
  match ty with
  | D -> C => is_trm_typ D && is_pred_typ C
  | frm => true
  | _ => false
  end.

Inductive scheme : nat -> Set :=
  | mono_scheme (p : raw_syntax) : scheme O
  | poly_scheme {n : nat} (phi : name) (ty : typ) (phi_is_pred : is_pred_typ ty = true) (s : scheme n) : scheme (S n).

#[local] Open Scope vec_scope.

Fixpoint scheme_body {n : nat} (s : scheme n) : raw_syntax :=
  match s with
  | mono_scheme p => p
  | poly_scheme _ _ _ s => scheme_body s
  end.

Fixpoint scheme_params {n : nat} (s : scheme n) : Vector.t (name * typ) n :=
  match s with
  | mono_scheme _ => []
  | poly_scheme phi ty _ s => (phi, ty) :: scheme_params s
  end.

End STLC_STYLE_DEFINITION.

Arguments raw_syntax : clear implicits.
Arguments scheme : clear implicits.
Coercion App_syn : raw_syntax >-> Funclass.
Bind Scope raw_syntax_scope with raw_syntax.

Notation "'$' EXPR '$'" := EXPR : raw_syntax_scope.
Notation "'$' EXPR '$'" := (EXPR : raw_syntax _).

Notation "x" := (Var_syn x) (x constr at level 0, in custom syntax_view at level 0).
Notation "[ ]" := (Nil_vec) (in custom syntax_view at level 0).
Notation "[ t ]" := (Cons_vec t Nil_vec) (t custom syntax_view at level 10, in custom syntax_view at level 0).
Notation "[ t1 , t2 , .. , tn ]" := (Cons_vec t1 (Cons_vec t2 .. (Cons_vec tn Nil_vec) ..)) (t1 custom syntax_view at level 10, t2 custom syntax_view at level 10, tn custom syntax_view at level 10, in custom syntax_view at level 0).
Notation "'False'" := (Bot_frm) (in custom syntax_view at level 0).

Notation "'F' f ts" := (Fun_trm f ts) (f constr at level 0, ts custom syntax_view at level 0, in custom syntax_view at level 1).
Notation "'C' c" := (Con_trm c) (c constr at level 0, in custom syntax_view at level 1).
Notation "'R' R ts" := (Rel_frm R ts) (R constr at level 0, ts custom syntax_view at level 0, in custom syntax_view at level 1).
Notation "t1 = t2" := (Eqn_frm t1 t2) (no associativity, t1 custom syntax_view, t2 custom syntax_view, in custom syntax_view at level 1).

Notation "t :: ts" := (Cons_vec t ts) (right associativity, t custom syntax_view, ts custom syntax_view, in custom syntax_view at level 2).

Notation "~ p1" := (Neg_frm p1) (right associativity, p1 custom syntax_view, in custom syntax_view at level 3).
Notation "'forall' x ',' p1" := (All_frm x p1) (p1 custom syntax_view at level 4, in custom syntax_view at level 3).
Notation "'exists' x ',' p1" := (Exs_frm x p1) (p1 custom syntax_view at level 4, in custom syntax_view at level 3).

Notation "p1 /\ p2" := (Con_frm p1 p2) (no associativity, p1 custom syntax_view, p2 custom syntax_view, in custom syntax_view at level 4).
Notation "p1 \/ p2" := (Dis_frm p1 p2) (no associativity, p1 custom syntax_view, p2 custom syntax_view, in custom syntax_view at level 4).
Notation "p1 -> p2" := (Imp_frm p1 p2) (no associativity, p1 custom syntax_view, p2 custom syntax_view, in custom syntax_view at level 4).
Notation "p1 <-> p2" := (Iff_frm p1 p2) (no associativity, p1 custom syntax_view, p2 custom syntax_view, in custom syntax_view at level 4).

Notation "'fun' x ':' ty '=>' e" := (Lam_syn x ty e) (x constr at level 0, ty constr at level 100, e custom syntax_view at level 10, in custom syntax_view at level 10).
Notation "( e )" := e (e custom syntax_view at level 10, in custom syntax_view at level 0).

End ExternalSyntax.

Module ZFC.

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

End ZFC.
