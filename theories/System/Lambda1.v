Require Import PnV.Prelude.Prelude.

Module ULC.

Inductive trm {signature : Set} : Set :=
  | Idx (i : nat)
  | App (t1 : @trm signature) (t2 : @trm signature)
  | Lam (t1 : @trm signature)
  | Sym (s : signature).

#[global] Arguments trm : clear implicits.

End ULC.
