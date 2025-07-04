Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.ThN.
Require Import Coq.Strings.String.
Require Import Coq.Arith.Wf_nat.
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Init.Byte.

Inductive name : Set :=
  | mk_name (seed : nat) : name.

Declare Scope name_scope.
Bind Scope name_scope with name.
Delimit Scope name_scope with name.

#[global]
Instance name_hasEqDec
  : hasEqDec name.
Proof.
  red; decide equality; eapply Nat.eq_dec.
Defined.

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
    | right NE => print_name1 (n / 36) (H_Acc_inv (n / 36) (print_name1_aux_lemma n NE)) ++ [mkAlphaNum (n mod 36)]
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

Lemma unAlphaNum_mkAlphaNum n n'
  : unAlphaNum (mkAlphaNum n) = Some n' <-> (n = n' /\ n < 36).
Proof.
  unfold unAlphaNum, mkAlphaNum in *. split; intros H_OBS.
  - (do 36 try destruct n as [ | n]); (do 36 try destruct n' as [ | n']); try congruence; lia.
  - destruct H_OBS as [<- H_OBS]. (do 36 try destruct n as [ | n]); try congruence; lia.
Qed.

Lemma rewrite_unAlphaNum_mkAlphaNum n
  (BOUND : n < 36)
  : unAlphaNum (mkAlphaNum n) = Some n.
Proof.
  rewrite -> unAlphaNum_mkAlphaNum. lia.
Qed.

Definition parse_name1 (bs : list Byte.byte) : option nat :=
  fold_left (fun ACC : option nat => fun b : Byte.byte => liftM2 (fun n : nat => fun m : nat => m + 36 * n) ACC (unAlphaNum b)) bs (Some 0).

Definition next_name (nm : name) : name :=
  mk_name (1 + 36 * un_name nm).

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

#[local] Opaque "+" "*" Nat.ltb.

Lemma print_next_name (bs : list Byte.byte) nm
  (NAME : print_name nm = Some bs)
  : print_name (next_name nm) = Some (bs ++ [x31]).
Proof.
  unfold next_name; unfold print_name; simpl.
  destruct (Nat.eq_dec (1 + 36 * un_name nm) 0) as [EQ1 | NE1]; simpl in *; try lia.
  replace ((1 + 36 * un_name nm) mod 36) with 1 in *; cycle 1.
  { pose proof (div_mod_inv (1 + 36 * un_name nm) 36 (un_name nm) 1); lia. }
  replace (print_name1 ((1 + 36 * un_name nm) / 36) _) with (print_name1 (un_name nm) (lt_wf (un_name nm))); cycle 1.
  { rewrite print_name1_pirrel with (H_Acc' := lt_wf ((1 + 36 * un_name nm) / 36)).
    replace ((1 + 36 * un_name nm) / 36) with (un_name nm); trivial.
    pose proof (div_mod_uniqueness (1 + 36 * un_name nm) 36 (un_name nm) 1); lia.
  }
  unfold print_name in NAME; destruct (print_name1 (un_name nm) (lt_wf (un_name nm))) as [ | b bs'] eqn: H_OBS; try congruence.
  simpl in NAME |- *; destruct (unAlphaNum b) as [n | ] eqn: H_OBS'; simpl in NAME |- *; try congruence.
  destruct (n <? 10)%nat as [ | ] eqn: H_OBS''; try congruence.
  change (b :: bs' ++ ["1"%byte]) with ((b :: bs') ++ ["1"%byte]); congruence.
Qed.

Lemma parse_next_name (bs : list Byte.byte) nm
  (NAME : parse_name bs = Some nm)
  : parse_name (bs ++ [x31]) = Some (next_name nm).
Proof.
  unfold parse_name in *; destruct bs as [ | b bs]; simpl in *; try congruence.
  destruct (unAlphaNum b) as [n0 | ] eqn: H_n0; simpl in *; try congruence.
  destruct (n0 <? 10)%nat as [ | ] eqn: H_OBS; simpl in *; try congruence.
  unfold parse_name1 in *; change (b :: bs ++ ["1"%byte]) with ((b :: bs) ++ ["1"%byte]).
  rewrite fold_left_app; revert NAME; set (fold_left _) as loop; i.
  destruct (loop (b :: bs) (Some 0)) as [r | ] eqn: H_r; simpl in *; try congruence.
  now replace nm with (mk_name r) by congruence.
Qed.

End PP_name.

String Notation name parse_name print_name : name_scope.

Module Name.

Section PP_name_EXAMPLE1.

Let x1 : name :=
  "x1".

End PP_name_EXAMPLE1.

Notation t := name.

Definition is_valid (nm : Name.t) : bool :=
  B.isSome (print_name nm >>= parse_name).

Definition max (nm1 : Name.t) (nm2 : Name.t) : Name.t :=
  mk_name (Nat.max (un_name nm1) (un_name nm2)).

Fixpoint maxs (nms : list Name.t) : Name.t :=
  match nms with
  | [] => mk_name 0
  | nm :: nms' => max nm (maxs nms')
  end.

End Name.
