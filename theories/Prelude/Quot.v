Require Import PnV.Prelude.Prelude.

Parameter Quot : forall X : Type@{U_discourse}, isSetoid X -> Type.

Axiom Quot_isQuotient : forall X : Type@{U_discourse}, forall SETOID : isSetoid X, isQuotientOf (Quot X SETOID) X (SETOID := SETOID).

#[global]
Instance Quotient_always_exists {X : Type@{U_discourse}} (SETOID : isSetoid X) : isQuotientOf (Quot X SETOID) X :=
  Quot_isQuotient X SETOID.
