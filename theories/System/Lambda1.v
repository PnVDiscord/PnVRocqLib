Require Import PnV.Prelude.Prelude.

Module ULC.

Inductive trm {signature : Set} : Set :=
  | Idx (i : nat)
  | App (t1 : trm) (t2 : trm)
  | Lam (t1 : trm)
  | Sym (s : signature).

#[global] Arguments trm : clear implicits.

End ULC.
