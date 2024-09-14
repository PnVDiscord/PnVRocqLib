Require Import PnV.Prelude.Prelude.
Require Import PnV.Data.Vector.
Require Import PnV.Math.BooleanAlgebra.
Require Import PnV.Logic.BasicFol.
Require Import PnV.Logic.BasicFol2.
Require Import PnV.Logic.HilbertFol.

Import FolNotations.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.
#[local] Notation In := L.In.

Module FolHilbert.

Infix "⊢" := proves : type_scope.

Section HENKIN.

Context {L : language}.

#[local] Notation L' := (augmented_language L Henkin_constants).

#[local] Notation hatom := (ivar + Henkin_constants)%type.

#[local] Notation hsubst := (hatom -> trm L').

#[local] Existing Instance constant_symbols_similarity_instance.

#[local] Existing Instance trm_similarity_instance.

#[local] Existing Instance trms_similarity_instance.

#[local] Existing Instance frm_similarity_instance.

#[local] Existing Instance subst_similarity_instance.

End HENKIN.

End FolHilbert.
