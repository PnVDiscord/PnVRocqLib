Require Export PnV.Prelude.Prelude.

#[universes(template), projections(primitive)]
Class isFinite (A : Type) : Type :=
  { finite_hasEqDec : hasEqDec A
  ; finite_enumeration : list A
  ; finite_enumeration_complete
    : forall x : A, L.In x finite_enumeration
  ; finite_enumeration_NoDup
    : NoDup finite_enumeration
  }.
