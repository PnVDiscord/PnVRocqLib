Require Import PnV.Prelude.Prelude.
Require Import PnV.Data.Graph.

#[local] Infix "\in" := E.In : type_scope.

Module Type GRAMMAR_SPEC.

Parameter terminal : Set.

#[global] Parameter terminal_hasEqDec : hasEqDec terminal.

Parameter all_terminals : list terminal.

Parameter all_terminals_complete : forall t, L.In t all_terminals.

#[global] Hint Resolve all_terminals_complete : simplication_hints.

Parameter nonterminal : Set.

#[global] Parameter nonterminal_hasEqDec : hasEqDec nonterminal.

Parameter all_nonterminals : list nonterminal.

Parameter all_nonterminals_complete : forall nt, L.In nt all_nonterminals.

#[global] Hint Resolve all_nonterminals_complete : simplication_hints.

Parameter token : Set.

#[global] Parameter token_hasEqDec : hasEqDec token.

Parameter token_term : token -> terminal.

Inductive symbol : Set :=
  | T (term : terminal)
  | NT (nt : nonterminal).

#[projections(primitive)]
Record production : Set :=
  mkProduction
  { production_id : nat
  ; prod_lhs : nonterminal
  ; prod_rhs_rev : list symbol
  } as prod.

Parameter productions : list production.

Parameter start : nonterminal.

End GRAMMAR_SPEC.

Module PGS (Grammar : GRAMMAR_SPEC).

#[local] Existing Instance Grammar.terminal_hasEqDec.

#[local] Existing Instance Grammar.nonterminal_hasEqDec.

#[local] Existing Instance Grammar.token_hasEqDec.

Definition terminal : Set :=
  Grammar.terminal.

Definition nonterminal : Set :=
  Grammar.nonterminal.

Definition token : Set :=
  Grammar.token.

Definition symbol : Set :=
  Grammar.symbol.

Definition production : Set :=
  Grammar.production.

Definition T : terminal -> symbol :=
  Grammar.T.

Definition NT : nonterminal -> symbol :=
  Grammar.NT.

Definition token_term : token -> terminal :=
  Grammar.token_term.

Definition productions : list production :=
  Grammar.productions.

Definition start : nonterminal :=
  Grammar.start.

Definition production_id : production -> nat :=
  Grammar.production_id.

Definition prod_lhs : production -> nonterminal :=
  Grammar.prod_lhs.

Definition prod_rhs_rev : production -> list symbol :=
  Grammar.prod_rhs_rev.

#[global]
Instance symbol_hasEqDec
  : hasEqDec@{Set} symbol.
Proof.
  red. decide equality; eapply eq_dec.
Defined.

#[global]
Instance production_hasEqDec
  : hasEqDec@{Set} production.
Proof.
  red. decide equality; unshelve eapply eq_dec.
  eapply list_hasEqDec; eapply symbol_hasEqDec.
Defined.

Module Error.

Inductive t : Set :=
  | BadGrammar
  | UndefinedNonterminal (nt : nonterminal)
  | DuplicateProductionId (id : nat)
  | Conflict
  | MissingGoto
  | UnexpectedToken (tok : token)
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

End PGS.
