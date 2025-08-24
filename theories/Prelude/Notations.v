Require Import PnV.Prelude.SfLib.

Reserved Infix "==" (no associativity, at level 70).
Reserved Infix "≡" (no associativity, at level 70).

Reserved Infix "≠" (no associativity, at level 70).

Reserved Infix "=<" (no associativity, at level 70).
Reserved Infix "⪳" (no associativity, at level 70).
Reserved Infix "⪵" (no associativity, at level 70).
Reserved Infix "≦" (no associativity, at level 70).
Reserved Infix "≨" (no associativity, at level 70).
Reserved Infix "≺" (no associativity, at level 70).

Reserved Infix "≦ᵣ" (no associativity, at level 70).
Reserved Infix "=ᵣ" (no associativity, at level 70).
Reserved Infix "<ᵣ" (no associativity, at level 70).

Reserved Infix "⊑" (no associativity, at level 70).

Reserved Infix "\in" (no associativity, at level 70).
Reserved Infix "\subseteq" (no associativity, at level 70).

Reserved Infix "∈" (no associativity, at level 70).
Reserved Infix "⊆" (no associativity, at level 70).

Reserved Infix "⊢" (no associativity, at level 70).
Reserved Infix "⊨" (no associativity, at level 70).
Reserved Infix "⊬" (no associativity, at level 70).
Reserved Infix "⊭" (no associativity, at level 70).

Reserved Infix "$" (right associativity, at level 100).
Reserved Infix ">>=" (left associativity, at level 90).
Reserved Infix ">=>" (right associativity, at level 45).
Reserved Infix "!!" (left associativity, at level 25).

Reserved Infix "=~=" (no associativity, at level 70).

Notation " '⟪' x ':' t '⟫' " := (NW (fun x : unit => match x with tt => t end)) (x name, t at level 200, no associativity, at level 0) : type_scope.

Reserved Notation " '`[' A '->' B ']' " (A at level 0, B at level 0, no associativity, at level 0, format "`[ A  ->  B ]").

Reserved Infix "~~>" (no associativity, at level 95).

Reserved Notation " src '~~~[' x ']~~>' tgt " (at level 70, no associativity).
Reserved Notation " src '---[' x ']-->' tgt " (at level 70, no associativity).
Reserved Notation " src '===[' x ']==>' tgt " (at level 70, no associativity).
Reserved Notation " src '~~~[' x ']~~>*' tgt " (at level 70, no associativity).
Reserved Notation " src '---[' x ']-->*' tgt " (at level 70, no associativity).
Reserved Notation " src '===[' x ']==>*' tgt " (at level 70, no associativity).

Reserved Notation "Gamma '∋' x '⦂' A" (at level 70, no associativity).
Reserved Notation "Gamma '⊢' M '⦂' A" (at level 70, no associativity).
Reserved Notation "Gamma '⊢' M '=' N '⦂' A" (at level 70, no associativity).
Reserved Notation "Gamma '⊢' M '⇉' A" (at level 70, no associativity).
Reserved Notation "Gamma '⊢' M '⇇' A" (at level 70, no associativity).

Reserved Infix "~>β" (at level 70, no associativity).
Reserved Infix "~>η" (at level 70, no associativity).
Reserved Infix "~>β*" (at level 70, no associativity).
Reserved Infix "~>η*" (at level 70, no associativity).

Reserved Notation "Gamma '⊢' M '~>β' N '⦂' A" (at level 70, no associativity).
Reserved Notation "Gamma '⊢' M '~>η' N '⦂' A" (at level 70, no associativity).
Reserved Notation "Gamma '⊢' M '~>β*' N '⦂' A" (at level 70, no associativity).
Reserved Notation "Gamma '⊢' M '~>η*' N '⦂' A" (at level 70, no associativity).
