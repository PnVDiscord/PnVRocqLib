Require Import PnV.Prelude.Prelude.
Require Export Stdlib.Logic.ChoiceFacts.
Require Export Stdlib.Logic.ClassicalChoice.

Lemma AC {A : Type} {B : A -> Type} (R : forall x : A, forall y : B x, Prop)
  (EXISTENCE : forall x, exists y, R x y)
  : exists f : forall x : A, B x, forall x, R x (f x).
Proof.
  eapply non_dep_dep_functional_choice; [exact choice | exact EXISTENCE].
Defined.

Module Type AC_ModuleAttribute.

End AC_ModuleAttribute.
