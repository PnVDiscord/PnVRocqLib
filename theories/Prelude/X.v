Require Export PnV.Prelude.Prelude.

#[projections(primitive)]
Class isFinite@{u} (A : Type@{u}) : Type@{u} :=
  { finite_hasEqDec : hasEqDec@{u} A
  ; finite_enumeration : list A
  ; finite_enumeration_complete
    : forall x : A, L.In x finite_enumeration
  ; finite_enumeration_NoDup
    : NoDup finite_enumeration
  }.

#[global] Existing Instance finite_hasEqDec.
