Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Strings.String.
Require Import PnV.Prelude.Prelude.
Require Import PnV.System.Regex.

#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "=~=" := (is_similar_to (Similarity := Re.in_regex eq)) : type_scope.

#[global]
Instance ascii_hasEqDec
  : hasEqDec@{Set} ascii.
Proof.
  exact Ascii.ascii_dec.
Defined.

Module Type TOKEN_SPEC.

Parameter t : Set.

#[global] Parameter t_hasEqDec : hasEqDec@{Set} t.

Parameter rules : list (t * regex ascii).

Parameter skips : list (regex ascii).

End TOKEN_SPEC.

Module LGS (Token : TOKEN_SPEC).

#[local] Existing Instance Token.t_hasEqDec.

Module Error.

Inductive t : Set :=
  | EmptyTokenRule (idx : nat)
  | EmptySkipRule (idx : nat)
  | BadRegex (idx : nat)
  | NoMatch (rest : list ascii)
  | FuelExhausted
  | InternalInvariantBroken.

End Error.

#[universes(polymorphic=yes)]
Definition ErrM@{u} (A : Type@{u}) : Type@{u} :=
  Error.t + A.

#[global, universes(polymorphic=yes)]
Instance result_isMonad@{u} : isMonad@{u u} ErrM@{u} :=
  { bind {A : Type@{u}} {B : Type@{u}} (m : ErrM@{u} A) (k : A -> ErrM@{u} B) := B.either (@inl _ _) k m
  ; pure {A : Type@{u}} (x : A) := inr x
  }.

Module Input.

Definition t : Set :=
  list ascii.

Fixpoint of_string (s : string) : t :=
  match s with
  | EmptyString => []
  | String c s' => c :: of_string s'
  end.

Fixpoint to_string (s : t) : string :=
  match s with
  | [] => EmptyString
  | c :: s' => String c (to_string s')
  end.

End Input.

Lemma Input_to_of_string (s : string)
  : Input.to_string (Input.of_string s) = s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Lemma Input_length_of_string (s : string)
  : length (Input.of_string s) = String.length s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

End LGS.
