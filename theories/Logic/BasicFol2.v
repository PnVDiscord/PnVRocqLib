Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.Data.Vector.
Require Import Coq.Arith.Wf_nat.
Require Import PnV.Logic.BasicFol.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.
#[local] Notation In := List.In.

Import FolNotations.

Section HENKIN.

Import ListNotations.

#[local] Infix "=~=" := is_similar_to : type_scope.

Definition Henkin_constants : Set := nat.

Context {L : language}.

Let L' : language := augmented_language L Henkin_constants.

Fixpoint HC_occurs_in_trm (hc : Henkin_constants) (t : trm L') : bool :=
  match t with
  | Var_trm x => false
  | Fun_trm f ts => HC_occurs_in_trms hc ts
  | Con_trm c =>
    match c with
    | inl cc => false
    | inr hc' => Nat.eqb hc hc'
    end
  end
with HC_occurs_in_trms {n : nat} (hc : Henkin_constants) (ts : trms L' n) : bool :=
  match ts with
  | O_trms => false
  | S_trms n t ts => HC_occurs_in_trm hc t || HC_occurs_in_trms (n := n) hc ts
  end.

#[local] Opaque HC_occurs_in_trm HC_occurs_in_trms.

Lemma HC_occurs_in_trm_Var_trm hc x
  : HC_occurs_in_trm hc (Var_trm x) = false.
Proof.
  reflexivity.
Defined.

Lemma HC_occurs_in_trm_Fun_trm hc f ts
  : HC_occurs_in_trm hc (Fun_trm f ts) = HC_occurs_in_trms hc ts.
Proof.
  reflexivity.
Defined.

Lemma HC_occurs_in_trm_Con_trm hc c
  : HC_occurs_in_trm hc (Con_trm c) = (match c with inl cc => false | inr hc' => Nat.eqb hc hc' end).
Proof.
  reflexivity.
Defined.

#[local] Hint Rewrite HC_occurs_in_trm_Var_trm HC_occurs_in_trm_Fun_trm HC_occurs_in_trm_Con_trm : simplication_hints.

Lemma HC_occurs_in_trms_O_trms hc
  : HC_occurs_in_trms hc O_trms = false.
Proof.
  reflexivity.
Defined.

Lemma HC_occurs_in_trms_S_trms hc n t ts
  : HC_occurs_in_trms hc (S_trms n t ts) = HC_occurs_in_trm hc t || HC_occurs_in_trms hc ts.
Proof.
  reflexivity.
Defined.

#[local] Hint Rewrite HC_occurs_in_trms_O_trms HC_occurs_in_trms_S_trms : simplication_hints.

Fixpoint HC_occurs_in_frm (hc : Henkin_constants) (p : frm L') : bool :=
  match p with
  | Rel_frm R ts => HC_occurs_in_trms hc ts
  | Eqn_frm t1 t2 => HC_occurs_in_trm hc t1 || HC_occurs_in_trm hc t2
  | Neg_frm p1 => HC_occurs_in_frm hc p1
  | Imp_frm p1 p2 => HC_occurs_in_frm hc p1 || HC_occurs_in_frm hc p2
  | All_frm y p1 => HC_occurs_in_frm hc p1
  end.

Fixpoint accum_HCs_trm (t : trm L') : list Henkin_constants :=
  match t with
  | Var_trm x => []
  | Fun_trm f ts => accum_HCs_trms ts
  | Con_trm c =>
    match c with
    | inl cc => []
    | inr hc => [hc]
    end
  end
with accum_HCs_trms {n : nat} (ts : trms L' n) : list Henkin_constants :=
  match ts with
  | O_trms => []
  | S_trms n t ts => accum_HCs_trm t ++ accum_HCs_trms (n := n) ts
  end.

#[local] Opaque accum_HCs_trm accum_HCs_trms.

Lemma accum_HCs_trm_Var_trm x
  : accum_HCs_trm (Var_trm x) = [].
Proof.
  reflexivity.
Defined.

Lemma accum_HCs_trm_Fun_trm f ts
  : accum_HCs_trm (Fun_trm f ts) = accum_HCs_trms ts.
Proof.
  reflexivity.
Defined.

Lemma accum_HCs_trm_Con_trm c
  : accum_HCs_trm (Con_trm c) = (match c with inl cc => [] | inr hc => [hc] end).
Proof.
  reflexivity.
Defined.

#[local] Hint Rewrite accum_HCs_trm_Var_trm accum_HCs_trm_Fun_trm accum_HCs_trm_Con_trm : simplication_hints.

Lemma accum_HCs_trms_O_trms
  : accum_HCs_trms O_trms = [].
Proof.
  reflexivity.
Defined.

Lemma accum_HCs_trms_S_trms n t ts
  : accum_HCs_trms (S_trms n t ts) = accum_HCs_trm t ++ accum_HCs_trms ts.
Proof.
  reflexivity.
Defined.

#[local] Hint Rewrite accum_HCs_trms_O_trms accum_HCs_trms_S_trms : simplication_hints.

Fixpoint accum_HCs_frm (p : frm L') : list Henkin_constants :=
  match p with
  | Rel_frm R ts => accum_HCs_trms ts
  | Eqn_frm t1 t2 => accum_HCs_trm t1 ++ accum_HCs_trm t2
  | Neg_frm p1 => accum_HCs_frm p1
  | Imp_frm p1 p2 => accum_HCs_frm p1 ++ accum_HCs_frm p2
  | All_frm y p1 => accum_HCs_frm p1
  end.

End HENKIN.

#[global] Opaque HC_occurs_in_trm.

#[global] Hint Rewrite @HC_occurs_in_trm_Var_trm @HC_occurs_in_trm_Fun_trm @HC_occurs_in_trm_Con_trm : simplication_hints.

#[global] Opaque HC_occurs_in_trms.

#[global] Hint Rewrite @HC_occurs_in_trms_O_trms @HC_occurs_in_trms_S_trms : simplication_hints.

#[global] Opaque accum_HCs_trm.

#[global] Hint Rewrite @accum_HCs_trm_Var_trm @accum_HCs_trm_Fun_trm @accum_HCs_trm_Con_trm : simplication_hints.

#[global] Opaque accum_HCs_trms.

#[global] Hint Rewrite @accum_HCs_trms_O_trms @accum_HCs_trms_S_trms : simplication_hints.

