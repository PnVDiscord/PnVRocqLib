Require Import PnV.Prelude.Prelude.
Require Import PnV.Logic.BasicFol.
Require Import PnV.Logic.BasicFol2.
Require Import PnV.Logic.HilbertFol.
Require Import PnV.Logic.HilbertFol2.
Require Import PnV.System.P.
Require Import PnV.Data.Vector.

Module InternalSyntax := PnV.Logic.BasicFol.

Module ExternalSyntax.

Section FOL_SYNTAX.

#[local] Infix "=~=" := is_similar_to.

Context {L : language}.

Let arity : Set :=
  nat.

Inductive trm : Set :=
  | Var_trm (x : name) : trm
  | Fun_trm (f : L.(function_symbols)) (ts : trms (L.(function_arity_table) f)) : trm
  | Con_trm (c : L.(constant_symbols)) : trm
with trms : arity -> Set :=
  | O_trms : trms O
  | S_trms (n : arity) (t : trm) (ts : trms n) : trms (S n).

Inductive frm : Set :=
  | Rel_frm (R : L.(relation_symbols)) (ts : trms (L.(relation_arity_table) R)) : frm
  | Eqn_frm (t1 : trm) (t2 : trm) : frm
  | Bot_frm : frm
  | Neg_frm (p1 : frm) : frm
  | Con_frm (p1 : frm) (p2 : frm) : frm
  | Dis_frm (p1 : frm) (p2 : frm) : frm
  | Imp_frm (p1 : frm) (p2 : frm) : frm
  | Iff_frm (p1 : frm) (p2 : frm) : frm
  | All_frm (y : name) (p1 : frm) : frm
  | Exs_frm (y : name) (p1 : frm) : frm.

Inductive Similarity_trm : Similarity (InternalSyntax.trm L) trm :=
  | Var_trm_corres x x'
    (x_corres : x =~= x')
    : @InternalSyntax.Var_trm L x =~= Var_trm x'
  | Fun_trm_corres f ts ts'
    (ts_corres : ts =~= ts')
    : @InternalSyntax.Fun_trm L f ts =~= Fun_trm f ts'
  | Con_trm_corres c
    : @InternalSyntax.Con_trm L c =~= Con_trm c
with Similarity_trms : forall n : arity, Similarity (InternalSyntax.trms L n) (trms n) :=
  | O_trms_corres
    : @InternalSyntax.O_trms L =~= O_trms
  | S_trms_corres n t t' ts ts'
    (t_corres : t =~= t')
    (ts_corres : ts =~= ts')
    : @InternalSyntax.S_trms L n t ts =~= S_trms n t' ts'.

#[global] Existing Instance Similarity_trm.

#[global] Existing Instance Similarity_trms.

Inductive Similarity_frm : Similarity (InternalSyntax.frm L) frm :=
  | Rel_frm_corres R ts ts'
    (ts_corres : ts =~= ts')
    : @InternalSyntax.Rel_frm L R ts =~= Rel_frm R ts'
  | Eqn_frm_corres t1 t1' t2 t2'
    (t1_corres : t1 =~= t1')
    (t2_corres : t2 =~= t2')
    : @InternalSyntax.Eqn_frm L t1 t2 =~= Eqn_frm t1' t2'
  | Bot_frm_corres
    : @InternalSyntax.Bot_frm L =~= Bot_frm
  | Neg_frm_corres p1 p1'
    (p1_corres : p1 =~= p1')
    : @InternalSyntax.Neg_frm L p1 =~= Neg_frm p1'
  | Con_frm_corres p1 p1' p2 p2'
    (p1_corres : p1 =~= p1')
    (p2_corres : p2 =~= p2')
    : @InternalSyntax.Con_frm L p1 p2 =~= Con_frm p1' p2'
  | Dis_frm_corres p1 p1' p2 p2'
    (p1_corres : p1 =~= p1')
    (p2_corres : p2 =~= p2')
    : @InternalSyntax.Dis_frm L p1 p2 =~= Dis_frm p1' p2'
  | Imp_frm_corres p1 p1' p2 p2'
    (p1_corres : p1 =~= p1')
    (p2_corres : p2 =~= p2')
    : @InternalSyntax.Imp_frm L p1 p2 =~= Imp_frm p1' p2'
  | Iff_frm_corres p1 p1' p2 p2'
    (p1_corres : p1 =~= p1')
    (p2_corres : p2 =~= p2')
    : @InternalSyntax.Iff_frm L p1 p2 =~= Iff_frm p1' p2'
  | All_frm_corres x x' p1 p1'
    (x_corres : x =~= x')
    (p1_corres : p1 =~= p1')
    : @InternalSyntax.All_frm L x p1 =~= All_frm x' p1'
  | Exs_frm_corres x x' p1 p1'
    (x_corres : x =~= x')
    (p1_corres : p1 =~= p1')
    : @InternalSyntax.Exs_frm L x p1 =~= Exs_frm x' p1'.

#[global] Existing Instance Similarity_frm.

End FOL_SYNTAX.

End ExternalSyntax.

Declare Custom Entry trm_view.
Declare Custom Entry trms_view.
Declare Custom Entry frm_view.
Declare Custom Entry subst_view.
Reserved Notation "'$' EXPR '$'" (EXPR custom frm_view at level 10, no associativity, format "'$' EXPR '$'", at level 0).

Module FolViewer.

#[global]
Coercion named_var (nm : name) : ivar :=
  un_name nm.

#[global] Declare Scope trm_scope.
#[global] Declare Scope trms_scope.
#[global] Declare Scope frm_scope.
#[global] Declare Scope subst_scope.

Notation "'$' EXPR '$'" := EXPR : frm_scope.
Notation "'$' EXPR '$'" := (EXPR : frm _).

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
Notation "t1 '=' t2" := (Eqn_frm t1 t2) (t1 custom trm_view at level 5, t2 custom trm_view at level 5, in custom frm_view at level 6).
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
  : $`[V "z" / "x"; V "x" / "y"](∀ "x", V "x" ∈ V "y")$ ≡α $∀ "z", V "z" ∈ V "x"$.
Proof.
  eapply alpha_All_frm with (z := un_name "z"); reflexivity.
Qed.

End Example1.
