Require Import PnV.Prelude.SfLib.

Notation " '⟪' x ':' t '⟫' " := (NW (fun x : unit => match x with tt => t end)) (x name, t at level 200, no associativity, at level 0) : type_scope.

Reserved Infix "==" (no associativity, at level 70).
Reserved Infix "=<" (no associativity, at level 70).

Reserved Infix "≦ᵣ" (no associativity, at level 70).
Reserved Infix "=ᵣ" (no associativity, at level 70).
Reserved Infix "<ᵣ" (no associativity, at level 70).

Reserved Infix "⪳" (no associativity, at level 70).
Reserved Infix "⪵" (no associativity, at level 70).
Reserved Infix "≦" (no associativity, at level 70).
Reserved Infix "≨" (no associativity, at level 70).

Reserved Infix "⊑" (no associativity, at level 70).

Reserved Infix "\in" (no associativity, at level 70).
Reserved Infix "\subseteq" (no associativity, at level 70).

Reserved Infix "∈" (no associativity, at level 70).

Reserved Infix "⊢" (no associativity, at level 70).
Reserved Infix "⊨" (no associativity, at level 70).
Reserved Infix "⊬" (no associativity, at level 70).
Reserved Infix "⊭" (no associativity, at level 70).

Reserved Infix "$" (right associativity, at level 100).
Reserved Infix ">>=" (left associativity, at level 90).
Reserved Infix ">=>" (right associativity, at level 45).
Reserved Infix "!!" (left associativity, at level 25).

Reserved Infix "=~=" (no associativity, at level 70).
