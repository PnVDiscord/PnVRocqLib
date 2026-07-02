Require Import Stdlib.Strings.Ascii.
Require Import Stdlib.Strings.String.
Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Monad.
Require Import PnV.Data.FiniteMap.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Data.Graph.
Require Import PnV.System.Regex.
Require Import PnV.Prelude.X.

Import DoNotations.

#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "=~=" := (is_similar_to (Similarity := Re.in_regex eq)) : type_scope.
#[local] Infix "∈" := L.In.
#[local] Infix "⊑" := is_similar_to.

#[local] Existing Instance Similarity_bool_Prop.

#[global]
Instance ascii_hasEqDec
  : hasEqDec@{Set} ascii.
Proof.
  exact Ascii.ascii_dec.
Defined.

#[global]
Instance regex_hasEqDec {A : Set}
  (A_hasEqDec : hasEqDec@{Set} A)
  : hasEqDec@{Set} (regex A).
Proof.
  red in A_hasEqDec |- *. decide equality.
Defined.

Abbreviation all_bools := Bool_FinEnum.all.

Abbreviation in_all_bools_intro := Bool_FinEnum.in_all_intro.

Module Ascii_FinEnum <: FINITE_ENUM.

Definition t : Set :=
  ascii.

Definition t_hasEqDec : hasEqDec@{Set} Ascii_FinEnum.t :=
  ascii_hasEqDec.

Definition all : list ascii := do
  'b0 <- all_bools;
  'b1 <- all_bools;
  'b2 <- all_bools;
  'b3 <- all_bools;
  'b4 <- all_bools;
  'b5 <- all_bools;
  'b6 <- all_bools;
  'b7 <- all_bools;
  ret (Ascii b0 b1 b2 b3 b4 b5 b6 b7).

Lemma in_all_intro
  : forall x : Ascii_FinEnum.t, L.In x Ascii_FinEnum.all.
Proof.
  unfold all; intros [b0 b1 b2 b3 b4 b5 b6 b7].
  eapply in_list_bind_intro with (x := b0); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b1); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b2); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b3); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b4); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b5); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b6); [eapply in_all_bools_intro | ].
  eapply in_list_bind_intro with (x := b7); [eapply in_all_bools_intro | ].
  eapply in_list_pure_intro.
Qed.

Lemma all_no_dup
  : NoDup Ascii_FinEnum.all.
Proof.
  assert (EQ : L.nodup (@eq_dec@{Set} ascii ascii_hasEqDec) all = all) by reflexivity.
  rewrite <- EQ. eapply L.NoDup_nodup.
Qed.

End Ascii_FinEnum.

Abbreviation all_asciis := Ascii_FinEnum.all.

Abbreviation in_all_asciis_intro := Ascii_FinEnum.in_all_intro.

Module Type TOKEN_SPEC.

Parameter t : Set.

Parameter t_hasEqDec : hasEqDec@{Set} TOKEN_SPEC.t.

Parameter rules : list (TOKEN_SPEC.t * regex ascii).

End TOKEN_SPEC.

Module BuildError.

Inductive t : Set :=
  | NullableTokenRule (idx : nat).

End BuildError.

#[universes(polymorphic=yes)]
Definition BuildErrorM@{u | } (A : Type@{u}) : Type@{u} :=
  BuildError.t + A.

#[universes(polymorphic=yes)]
Instance BuildErrorM_isMonad@{u} : isMonad@{u u} BuildErrorM@{u} :=
  { pure {A : Type@{u}} (x : A) := inr x
  ; bind {A : Type@{u}} {B : Type@{u}} (m : BuildErrorM A) (k : A -> BuildErrorM B) := B.either (@inl BuildError.t B) k m
  }.

#[local] Hint Rewrite eqb_spec@{Set} : simplication_hints.
#[local] Hint Rewrite mem_spec : simplication_hints.
#[local] Hint Rewrite existsb_iff : simplication_hints.
#[local] Hint Rewrite forallb_iff : simplication_hints.
#[global] Hint Rewrite in_union_iff: simplication_hints.
#[global] Hint Rewrite in_normalize_iff : simplication_hints.
#[global] Hint Rewrite in_unions_iff : simplication_hints.
#[global] Hint Rewrite product_iff : simplication_hints.

#[local] Hint Rewrite L.filter_In : simplication_hints.

#[local] Existing Instance list_corresponds_to_finite_ensemble.
#[local] Existing Instance alist_corresponds_to_finite_partial_map.

Module MkLGS (Token : TOKEN_SPEC).

Module Input.

Definition t : Set :=
  list ascii.

Fixpoint of_string (s : string) : Input.t :=
  match s with
  | EmptyString => []
  | String c s' => c :: of_string s'
  end.

Fixpoint to_string (s : Input.t) : string :=
  match s with
  | [] => EmptyString
  | c :: s' => String c (to_string s')
  end.

Theorem to_of_string (s : string)
  : to_string (of_string s) = s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Theorem of_to_string (s : Input.t)
  : of_string (to_string s) = s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Theorem length_of_string (s : string)
  : length (of_string s) = String.length s.
Proof.
  induction s as [ | c s IH]; simpl; congruence.
Qed.

Theorem to_string_app (s1 : Input.t) (s2 : Input.t)
  : to_string (s1 ++ s2) = String.append (to_string s1) (to_string s2).
Proof.
  induction s1 as [ | c s1 IH]; simpl; congruence.
Qed.

Theorem prefix_suffix_decompose (s : Input.t) (n : nat)
  (LE : n <= length s)
  : exists prefix, exists suffix, s = prefix ++ suffix /\ length prefix = n.
Proof.
  exists (firstn n s), (skipn n s). rewrite firstn_skipn. rewrite length_firstn. done.
Qed.

Theorem app_cancel_prefix (prefix : Input.t) (s1 : Input.t) (s2 : Input.t)
  (EQ : prefix ++ s1 = prefix ++ s2)
  : s1 = s2.
Proof.
  eapply L.app_cancel_l. exact EQ.
Qed.

Theorem app_cancel_suffix (s1 : Input.t) (s2 : Input.t) (suffix : Input.t)
  (EQ : s1 ++ suffix = s2 ++ suffix)
  : s1 = s2.
Proof.
  eapply L.app_cancel_r. exact EQ.
Qed.

Theorem empty_or_nonempty (s : Input.t)
  : { s = [] } + { exists c, exists s', s = c :: s' }.
Proof.
  destruct s as [ | c s']; [left; reflexivity | right; exists c, s'; reflexivity].
Defined.

Theorem nonempty_prefix_rest_shorter (consumed : Input.t) (rest : Input.t)
  (NONEMPTY : consumed ≠ [])
  : length rest < length (consumed ++ rest).
Proof.
  destruct consumed as [ | c consumed]; done.
Qed.

End Input.

End MkLGS.
