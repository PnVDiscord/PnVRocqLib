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

Module VIEWER.

Infix "≡" := alpha_equiv : type_scope.

Declare Scope trm_scope.
Declare Scope trms_scope.
Declare Scope frm_scope.
Declare Scope subst_scope.

Notation "'$' EXPR '$'" := EXPR : frm_scope.
Notation "'$' EXPR '$'" := (EXPR : frm _).

Bind Scope frm_scope with frm.
Notation "`[ s ] p" := (subst_frm s p) (s custom subst_view at level 10, p custom frm_view at level 5, in custom frm_view at level 5, format "`[ s ] p").
Notation "'⊥'" := (Bot_frm) (in custom frm_view at level 0).
Notation "t1 '=' t2" := (Eqn_frm t1 t2) (in custom frm_view at level 6).
Notation "'¬' p" := (Neg_frm p) (in custom frm_view at level 7).
Notation "'(∀' x ')' p" := (All_frm x p) (x constr at level 0, p custom frm_view at level 7, in custom frm_view at level 7).
Notation "'(∃' x ')' p" := (Exs_frm x p) (x constr at level 0, p custom frm_view at level 7, in custom frm_view at level 7).
Notation "p '∧' q" := (Con_frm p q) (no associativity, in custom frm_view at level 8).
Notation "p '∨' q" := (Dis_frm p q) (no associativity, in custom frm_view at level 9).
Notation "p '→' q" := (Imp_frm p q) (no associativity, in custom frm_view at level 10).
Notation "p '↔' q" := (Iff_frm p q) (no associativity, in custom frm_view at level 10).
Notation "p" := p (p ident, in custom frm_view at level 0).
Notation "( p )" := p (p custom frm_view at level 10, no associativity, in custom frm_view at level 0).

Bind Scope trm_scope with trm.
Notation "`[ s ] t" := (subst_trm s t) (s custom subst_view at level 10, t custom trm_view at level 5, in custom trm_view at level 5, format "`[ s ] t") : trm_scope.
Notation "'V' x" := (Var_trm x) (x constr at level 0, in custom trm_view at level 0).
Notation "'F' f ts" := (Fun_trm f ts) (f constr, ts custom trm_view at level 0, in custom trm_view at level 5).
Notation "'C' c" := (Con_trm c) (c constr, in custom trm_view at level 0).
Notation "t" := t (t ident, in custom trm_view at level 0).
Notation "( t )" := t (t custom trm_view at level 5, no associativity, in custom trm_view at level 0).

Bind Scope trms_scope with trms.
Notation "`[ s ] ts" := (subst_trms s ts) (s custom subst_view at level 10, ts custom trms_view at level 5, in custom trms_view at level 5, format "`[ s ] ts") : trms_scope.
Notation "[ ]" := (O_trms) (in custom trms_view at level 0) : trms_scope.
Notation "t :: ts" := (S_trms _ t ts) (t custom trm_view, ts custom trms_view, in custom trms_view at level 0) : trms_scope.
Notation "ts" := ts (ts ident, in custom trms_view at level 0).
Notation "( ts )" := ts (ts custom trms_view at level 5, no associativity, in custom trms_view at level 0).

Bind Scope subst_scope with subst.
Notation "s2 ∘ s1" := (subst_compose s1 s2) (right associativity, in custom subst_view at level 4) : subst_scope.
Notation "t / x" := (one_subst x t) (no associativity, x constr at level 0, t custom trm_view at level 5, in custom subst_view at level 10) : subst_scope.

End VIEWER.

Module Example1.

Import VIEWER.

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

End Example1.
