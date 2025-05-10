Require Import PnV.Prelude.Prelude.

Parameter Quot : forall X : Type@{U_discourse}, isSetoid X -> Type.

Axiom Quot_isQuotient : forall X : Type@{U_discourse}, forall SETOID : isSetoid X, isQuotientOf X (SETOID := SETOID) (Quot X SETOID).

#[global]
Instance Quotient_always_exists {X : Type@{U_discourse}} (SETOID : isSetoid X) : isQuotientOf X (Quot X SETOID) :=
  Quot_isQuotient X SETOID.
