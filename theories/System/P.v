Require Import PnV.Prelude.Prelude.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Byte.

Inductive name : Set :=
  | mk_name (seed : nat) : name.

Declare Scope name_scope.
Bind Scope name_scope with name.
Delimit Scope name_scope with name.

Definition un_name (nm : name) : nat :=
  match nm with
  | mk_name seed => seed
  end.

Section PP_name.

Lemma print_name1_aux_lemma (n : nat)
  (NE : n <> 0)
  : (n / 36) < n.
Proof.
  pose proof (Nat.mod_bound_pos n 36).
  pose proof (Nat.div_mod n 36).
  lia.
Qed.

Definition mkAlphaNum (n : nat) : Byte.byte :=
  match n with
  | 0 => x30
  | 1 => x31
  | 2 => x32
  | 3 => x33
  | 4 => x34
  | 5 => x35
  | 6 => x36
  | 7 => x37
  | 8 => x38
  | 9 => x39
  | 10 => x61
  | 11 => x62
  | 12 => x63
  | 13 => x64
  | 14 => x65
  | 15 => x66
  | 16 => x67
  | 17 => x68
  | 18 => x69
  | 19 => x6a
  | 20 => x6b
  | 21 => x6c
  | 22 => x6d
  | 23 => x6e
  | 24 => x6f
  | 25 => x70
  | 26 => x71
  | 27 => x72
  | 28 => x73
  | 29 => x74
  | 30 => x75
  | 31 => x76
  | 32 => x77
  | 33 => x78
  | 34 => x79
  | 35 => x7a
  | _ => x5f
  end.

Fixpoint print_name1 (n : nat) (H_Acc : Acc lt n) : list Byte.byte :=
  match H_Acc with
  | Acc_intro _ H_Acc_inv =>
    match Nat.eq_dec n 0 with
    | left _ => []
    | right NE => mkAlphaNum (n mod 36) :: print_name1 (n / 36) (H_Acc_inv (n / 36) (print_name1_aux_lemma n NE))
    end
  end.

#[local] Opaque "/" "mod".

Fixpoint print_name1_pirrel (n : nat) (H_Acc : Acc lt n) (H_Acc' : Acc lt n) {struct H_Acc} : print_name1 n H_Acc = print_name1 n H_Acc'.
Proof.
  destruct H_Acc, H_Acc'. simpl. destruct (Nat.eq_dec n 0) as [EQ | NE].
  - reflexivity.
  - f_equal. eapply print_name1_pirrel.
Qed.

Definition unAlphaNum (b : Byte.byte) : option nat :=
  match b with
  | x30 => Some 0
  | x31 => Some 1
  | x32 => Some 2
  | x33 => Some 3
  | x34 => Some 4
  | x35 => Some 5
  | x36 => Some 6
  | x37 => Some 7
  | x38 => Some 8
  | x39 => Some 9
  | x61 => Some 10
  | x62 => Some 11
  | x63 => Some 12
  | x64 => Some 13
  | x65 => Some 14
  | x66 => Some 15
  | x67 => Some 16
  | x68 => Some 17
  | x69 => Some 18
  | x6a => Some 19
  | x6b => Some 20
  | x6c => Some 21
  | x6d => Some 22
  | x6e => Some 23
  | x6f => Some 24
  | x70 => Some 25
  | x71 => Some 26
  | x72 => Some 27
  | x73 => Some 28
  | x74 => Some 29
  | x75 => Some 30
  | x76 => Some 31
  | x77 => Some 32
  | x78 => Some 33
  | x79 => Some 34
  | x7a => Some 35
  | _ => None
  end.

Fixpoint parse_name1 (bs : list Byte.byte) : option nat :=
  match bs with
  | [] => Some 0
  | b :: bs => unAlphaNum b >>= fun n : nat => parse_name1 bs >>= fun ACCUM : nat => pure (ACCUM * 36 + n)
  end.

End PP_name.

Definition print_name (nm : name) : option (list Byte.byte) :=
  let seed : nat := un_name nm in
  let bs : list Byte.byte := print_name1 seed (lt_wf seed) in
  match bs with
  | [] => None
  | b :: _ => unAlphaNum b >>= fun d : nat => if Nat.ltb d 10 then None else Some bs
  end.

Definition parse_name (bs : list Byte.byte) : option name :=
  match bs with
  | [] => None
  | b :: _ => unAlphaNum b >>= fun d : nat => if Nat.ltb d 10 then None else parse_name1 bs >>= fun seed : nat => pure (mk_name seed)
  end.

String Notation name parse_name print_name : name_scope.

#[global]
Instance Similarity_name : Similarity nat name :=
  fun n : nat => fun nm : name => mk_name n = nm.

Section PP_name_EXAMPLE1.

Let x1 : name :=
  "x1".

End PP_name_EXAMPLE1.
