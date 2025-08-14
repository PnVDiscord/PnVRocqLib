Require Import PnV.Prelude.Prelude.

Module Re.

#[universes(template)]
Inductive t {A : Type} : Type :=
  | Null : t
  | Empty : t
  | Char (c : A) : t
  | Union (e1 : @t A) (e2 : @t A) : t
  | Append (e1 : @t A) (e2 : @t A) : t
  | Star (e1 : @t A).

#[global] Arguments t : clear implicits.

#[local] Infix "=~=" := is_similar_to.

Inductive in_regex {A : Type} {A' : Type} (SIM : Similarity A A') : Similarity (list A) (Re.t A') :=
  | in_Empty
    : [] =~= Empty
  | in_Char c c'
    (c_corres : c =~= c')
    : [c] =~= Char c'
  | in_Union_l s e1 e2
    (H_inl : s =~= e1)
    : s =~= Union e1 e2
  | in_Union_r s e1 e2
    (H_inr : s =~= e2)
    : s =~= Union e1 e2
  | in_Append s1 s2 e1 e2
    (H_in1 : s1 =~= e1)
    (H_in2 : s2 =~= e2)
    : s1 ++ s2 =~= Append e1 e2
  | in_Star_nil e1
    : [] =~= Star e1
  | in_Star_app e1 s1 s2
    (H_in1 : s1 =~= e1)
    (H_in2 : s2 =~= Star e1)
    : s1 ++ s2 =~= Star e1.

#[global] Hint Constructors in_regex : simplication_hints.

End Re.

Notation regex := Re.t.

Section REGULAR_LANGUAGE.

#[local] Notation In := L.In.
#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "\subseteq" := E.isSubsetOf : type_scope.

#[local] Hint Rewrite @E.liftM2_spec : simplication_hints.
#[local] Opaque liftM2.

#[local] Infix "∈" := (is_similar_to (Similarity := Re.in_regex eq)) : type_scope.

Import Re.

Context {A : Type}.

Let lang : Type :=
  ensemble (list A).

Inductive star (L : lang) : lang :=
  | star_nil
    : [] \in star L
  | star_app s1 s2
    (H_IN1 : s1 \in L)
    (H_IN2 : s2 \in star L)
    : s1 ++ s2 \in star L.

#[local] Hint Constructors star : core.

Fixpoint eval_regex (e : regex A) {struct e} : lang :=
  match e with
  | Null => E.empty
  | Empty => E.singleton []
  | Char c => E.singleton [c]
  | Union e1 e2 => E.union (eval_regex e1) (eval_regex e2)
  | Append e1 e2 => liftM2 (@L.app A) (eval_regex e1) (eval_regex e2)
  | Star e1 => star (eval_regex e1) 
  end.

Theorem eval_regex_good e s
  : s \in eval_regex e <-> s ∈ e.
Proof with eauto with *.
  split.
  - revert s; induction e; simpl; intros s H_IN; rewrite!; subst...
    + destruct H_IN...
    + des; subst...
    + induction H_IN...
  - intros H_in; induction H_in; simpl; rewrite!...
    red in c_corres; congruence.
Qed.

Fixpoint fromString (s : list A) : regex A :=
  match s with
  | [] => Empty
  | c :: s => Append (Char c) (fromString s)
  end.

Lemma fromString_spec (s : list A)
  : eval_regex (fromString s) == E.singleton s.
Proof with eauto with *.
  induction s as [ | c s IH]; simpl... intros xs; (do 3 red in IH); rewrite!; split.
  - intros ?; des. subst xs. rewrite!. rewrite IH in H0. rewrite!. subst...
  - intros ->. exists [c]; rewrite!; split... exists s; split... rewrite IH; rewrite!...
Qed.

Fixpoint pow (s : list A) (n : nat) {struct n} : list A :=
  match n with
  | O => []
  | S n' => s ++ s ^ n'
  end
where " s ^ n " := (pow s n) : list_scope.

Lemma pow_in_star (s : list A) (e : regex A)
  (s_in_e : s ∈ e)
  : forall n : nat, s ^ n ∈ Star e.
Proof.
  induction n as [ | n IH]; simpl; eauto with *.
Qed.

Lemma pow_app (n1 : nat) (n2 : nat) (s : list A)
  : s ^ (n1 + n2) = s ^ n1 ++ s ^ n2.
Proof.
  revert n2 s. induction n1 as [ | n1 IH]; simpl; eauto.
  ii. rewrite <- app_assoc. rewrite IH; eauto.
Qed.

Lemma star_intro1 (s : list A) (e : regex A)
  (H_in : s ∈ e)
  : s ∈ Star e.
Proof.
  rewrite <- eval_regex_good; simpl.
  rewrite <- app_nil_r with (l := s).
  econstructor; eauto with *.
  rewrite -> eval_regex_good; trivial.
Qed.

Lemma pow_app_star (n : nat) (s1 : list A) (s2 : list A) (e : regex A)
  (H_in1 : s1 ∈ e)
  (H_in2 : s2 ∈ Star e)
  : s1 ^ n ++ s2 ∈ Star e.
Proof.
  revert s1 s2 e H_in1 H_in2. induction n as [ | n IH]; simpl; eauto.
  ii. rewrite <- app_assoc; eauto with *.
Qed.

Fixpoint pumping_constant (e : regex A) : nat :=
  match e with
  | Null => 1
  | Empty => 1
  | Char c => 2
  | Union e1 e2 => pumping_constant e1 + pumping_constant e2
  | Append e1 e2 => pumping_constant e1 + pumping_constant e2
  | Star e1 => pumping_constant e1
  end.

Lemma pumping_constant_ge_1 (e : regex A)
  : pumping_constant e >= 1.
Proof.
  induction e; simpl; lia.
Qed.

Variant pumping (e : regex A) (s : list A) : Prop :=
  | pumping_intro (s1 : list A) (s2 : list A) (s3 : list A)
    (H_split : s = s1 ++ s2 ++ s3)
    (H_ne_nil : s2 <> [])
    (H_constant_ge : length s1 + length s2 <= pumping_constant e)
    (H_pumping : forall m : nat, s1 ++ s2 ^ m ++ s3 ∈ e)
    : pumping e s.

#[local] Hint Rewrite -> length_app : simplication_hints.
#[local] Hint Rewrite <- app_assoc : simplication_hints.
#[local] Hint Constructors Re.in_regex : core.

#[local]
Tactic Notation "using" "eqn" ":" ident( H ) :=
  first [simpl; autorewrite with simplication_hints; lia | (try rewrite H); done!].

Theorem pumping_lemma (e : regex A) (s : list A)
  (H_in : s ∈ e)
  (pumping_constant_le : pumping_constant e <= length s)
  : pumping e s.
Proof.
  induction H_in as [ | c | s e1 e2 H_INL IHL | s e1 e2 H_INR IHR | s1 s2 e1 e2 H_IN1 IH1 H_IN2 IH2 | e1 | e1 s1 s2 H_IN1 IH1 H_IN2 IH2]; simpl in *; try lia.
  - assert (H_le : pumping_constant e1 <= length s) by lia.
    specialize (IHL H_le). destruct IHL as [s1' s2' s3' ? ? ? ?]. exists s1' s2' s3'; using eqn: H_split.
  - assert (H_le : pumping_constant e2 <= length s) by lia.
    specialize (IHR H_le). destruct IHR as [s1' s2' s3' ? ? ? ?]. exists s1' s2' s3'; using eqn: H_split.
  - rewrite length_app in pumping_constant_le.
    assert (pumping_constant e1 <= length s1 \/ pumping_constant e1 > length s1) as [H_le1 | H_gt1] by lia; [ | assert (pumping_constant e2 <= length s2 \/ pumping_constant e2 > length s2) as [H_le2 | H_gt2] by lia]; try lia.
    + specialize (IH1 H_le1). destruct IH1 as [s1' s2' s3' ? ? ? ?]. exists s1' s2' (s3' ++ s2);  try using eqn: H_split.
      i. replace (s1' ++ s2' ^ m ++ s3' ++ s2) with ((s1' ++ s2' ^ m ++ s3') ++ s2) by done!. eauto.
    + specialize (IH2 H_le2). destruct IH2 as [s1' s2' s3' ? ? ? ?]. exists (s1 ++ s1') s2' s3'; try using eqn: H_split.
  - pose proof (pumping_constant_ge_1 e1) as H_0_ge_1; lia.
  - rewrite length_app in pumping_constant_le.
    destruct s1 as [ | c1 s1']; [ | assert (length (c1 :: s1') < pumping_constant e1 \/ length (c1 :: s1') >= pumping_constant e1) as [H_lt1 | H_ge1] by lia]; try using eqn: H_split.
    + exists [] (c1 :: s1') s2; try using eqn: H_split.
      simpl. i. eapply pow_app_star; eauto.
    + specialize (IH1 H_ge1). destruct IH1 as [s' s2' s3' ? ? ? ?].
      exists s' s2' (s3' ++ s2); try using eqn: H_split.
      i. replace (s' ++ s2' ^ m ++ s3' ++ s2) with ((s' ++ s2' ^ m ++ s3') ++ s2) by now repeat rewrite <- app_assoc. eauto with *.
Qed.

End REGULAR_LANGUAGE.

#[global] Hint Constructors star : simplication_hints.
