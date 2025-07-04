Require Import PnV.Prelude.Prelude.
Require Import PnV.System.P.

Declare Scope typ_scope.

Module ChurchStyleStlc.

  #[projections(primitive)]
  Record language : Type :=
    { basic_types : Set
    ; constants : Set
    }.

  Inductive typ (L : language) : Set :=
    | bty (B : L.(basic_types))
    | arr (D : typ L) (C : typ L) : typ L.

  #[global] Bind Scope typ_scope with typ.
  #[global] Notation "D -> C" := (arr D C) : typ_scope.

  Class signature (L : language) : Set :=
    type_of_constant (c : L.(constants)) : typ L.

  Section STLC.

  Context {L : language}.

  Inductive trm : Set :=
    | Var_trm (x : name)
    | App_trm (e1 : trm) (e2 : trm)
    | Lam_trm (y : name) (ty : typ L) (e1 : trm)
    | Con_trm (c : L.(constants)).

  End STLC.

End ChurchStyleStlc.

#[global] Coercion ChurchStyleStlc.bty : ChurchStyleStlc.basic_types >-> ChurchStyleStlc.typ.
