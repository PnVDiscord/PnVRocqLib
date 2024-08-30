Require Import PnV.Prelude.Prelude.
Require Import PnV.Data.Vector.
Require Import PnV.Math.BooleanAlgebra.
Require Import PnV.Logic.BasicFol.
Require Import PnV.Logic.HilbertFol.

Import FolNotations.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.subset.
#[local] Notation In := L.In.

Module FolHilbert.

Infix "⊢" := proves : type_scope.

End FolHilbert.
