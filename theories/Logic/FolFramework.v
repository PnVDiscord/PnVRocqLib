Require Import PnV.Prelude.Prelude.
Require Import PnV.Logic.BasicFol.
Require Import PnV.Logic.BasicFol2.
Require Import PnV.Logic.HilbertFol.
Require Import PnV.Logic.HilbertFol2.

Declare Custom Entry trm_view.
Declare Custom Entry trms_view.
Declare Custom Entry frm_view.
Declare Custom Entry subst_view.
Reserved Notation "'$' EXPR '$'" (EXPR custom frm_view at level 10, no associativity, format "'$' EXPR '$'", at level 0).

Module FolViewer.

#[global] Declare Scope trm_scope.
#[global] Declare Scope trms_scope.
#[global] Declare Scope frm_scope.
#[global] Declare Scope subst_scope.

Notation "'$' EXPR '$'" := EXPR : frm_scope.
Notation "'$' EXPR '$'" := (EXPR : frm _).

#[global] Bind Scope trm_scope with trm.
Notation "'`[' s ']' t" := (subst_trm s t) (s custom subst_view at level 10, t custom trm_view at level 5, in custom trm_view at level 5, format "`[ s ] t").
Notation "'V' x" := (Var_trm x) (x constr at level 0, in custom trm_view at level 5).
Notation "'F' f ts" := (Fun_trm f ts) (f constr, ts custom trms_view at level 0, in custom trm_view at level 5).
Notation "'C' c" := (Con_trm c) (c constr, in custom trm_view at level 5).
Notation "t" := t (t ident, in custom trm_view at level 0).
Notation "'(' t ')'" := t (t custom trm_view at level 5, no associativity, in custom trm_view at level 0).

#[global] Bind Scope trms_scope with trms.
Notation "'`[' s ']' ts" := (subst_trms s ts) (s custom subst_view at level 10, ts custom trms_view at level 5, in custom trms_view at level 5, format "`[ s ] ts").
Notation "'[' ']'" := (O_trms) (in custom trms_view at level 0) : trms_scope.
Notation "t '::' ts" := (S_trms _ t ts) (t custom trm_view, ts custom trms_view, in custom trms_view at level 0) : trms_scope.
Notation "ts" := ts (ts ident, in custom trms_view at level 0).
Notation "'(' ts ')'" := ts (ts custom trms_view at level 5, no associativity, in custom trms_view at level 0).

#[global] Bind Scope frm_scope with frm.
Notation "'`[' s ']' p" := (subst_frm s p) (s custom subst_view at level 10, p custom frm_view at level 0, in custom frm_view at level 10, format "`[ s ] p").
Notation "'`(' p ')' '[' x := t ']'" := (subst1 x t p) (x constr, t custom trm_view at level 10, p custom frm_view at level 7, in custom frm_view at level 10, format "`( p ) [  x  :=  t  ]").
Notation "'⊥'" := (Bot_frm) (in custom frm_view at level 0).
Notation "t1 '=' t2" := (Eqn_frm t1 t2) (t1 custom trm_view at level 5, t2 custom trm_view at level 5, in custom frm_view at level 6).
Notation "'¬' p" := (Neg_frm p) (p custom frm_view at level 7, in custom frm_view at level 7).
Notation "'∀' x ',' p" := (All_frm x p) (x constr at level 0, p custom frm_view at level 7, in custom frm_view at level 7).
Notation "'∃' x ',' p" := (Exs_frm x p) (x constr at level 0, p custom frm_view at level 7, in custom frm_view at level 7).
Notation "p '∧' q" := (Con_frm p q) (p custom frm_view, q custom frm_view, no associativity, in custom frm_view at level 8).
Notation "p '∨' q" := (Dis_frm p q) (p custom frm_view, q custom frm_view, no associativity, in custom frm_view at level 9).
Notation "p '→' q" := (Imp_frm p q) (p custom frm_view, q custom frm_view, no associativity, in custom frm_view at level 10).
Notation "p '↔' q" := (Iff_frm p q) (p custom frm_view, q custom frm_view, no associativity, in custom frm_view at level 10).
Notation "p" := p (p ident, in custom frm_view at level 0).
Notation "'(' p ')'" := p (p custom frm_view at level 10, no associativity, in custom frm_view at level 0).

Bind Scope subst_scope with subst.
Notation "s2 '∘' s1" := (subst_compose s1 s2) (right associativity, in custom subst_view at level 4) : subst_scope.
Notation "s ';' t '/' x" := (cons_subst x t s) (left associativity, x constr at level 0, t custom trm_view at level 5, in custom subst_view at level 10).
Notation "t '/' x" := (one_subst x t) (no associativity, x constr at level 0, t custom trm_view at level 5, in custom subst_view at level 10).
Notation "'ι'" := (nil_subst) (no associativity, in custom subst_view at level 0).

Notation "p '≡α' q" := (alpha_equiv p q) (no associativity, at level 70) : type_scope.

End FolViewer.

Module Example1.

Import FolViewer.

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

Notation "t1 '∈' t2" := (@Rel_frm L_in symbol_IN (@S_trms L_in 1 t1 (@S_trms L_in 0 t2 (@O_trms L_in)))) (t1 custom trm_view at level 5, t2 custom trm_view at level 5, in custom frm_view at level 6).

Example fol_viewer_example1
  (v0 := 0)
  (v1 := 1)
  : $`[V v0 / v1](∀ v0, V v0 ∈ V v1)$ = $∀ v1, V v1 ∈ V v0$.
Proof.
  reflexivity.
Qed.

Example fol_viewer_example2
  (v0 := 0)
  (v1 := 1)
  (v2 := 2)
  : $`(∀ v0, V v0 ∈ V v1)[ v1 := V v0 ]$ = $∀ v2, V v2 ∈ V v0$.
Proof.
  rewrite subst1_unfold. simpl.
  replace (is_free_in_trm v0 (Var_trm v0)) with true by reflexivity.
  replace (fresh_var v1 (Var_trm v0) $V v0 ∈ V v1$) with v2 by reflexivity.
  rewrite subst1_unfold. f_equal.
  rewrite subst1_unfold. reflexivity.
Qed.

End Example1.
