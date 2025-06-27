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
with trms : nat -> Set :=
  | O_trms : trms O
  | S_trms (n : nat) (t : trm) (ts : trms n) : trms (S n).

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
