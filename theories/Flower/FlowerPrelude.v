Require Import PnV.Flower.FlowerAxioms.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Data.Aczel.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Math.SetTheory.

Module __wellorderingtheorem.

Variant good {X : Type} {SETOID : isSetoid X} (P : X -> Prop) (R : X -> X -> Prop) : Prop :=
  | good_intro
    (SOUND : forall a : X, forall b : X, forall LT : R a b, P a /\ P b)
    (COMPLETE : forall a : X, forall b : X, forall IN : P a, forall IN' : P b, a == b \/ (R a b \/ R b a))
    (WELL_FOUNDED : well_founded R)
    : good P R.

Section WELL_ORDERING_THEOREM.

Context {X : Type}.

#[projections(primitive)]
Record pair : Type :=
  { P (x : X) : Prop
  ; R (x : X) (y : X) : Prop
  } as s.

Variant pair_le (s : pair) (s' : pair) : Prop :=
  | pair_le_intro
    (P_incl : forall a : X, forall IN : s.(P) a, s'.(P) a)
    (R_incl : forall a : X, forall b : X, forall LT : s.(R) a b, s'.(R) a b)
    (NO_INSERTION : forall a : X, forall b : X, forall IN' : s.(P) b, s'.(R) a b <-> s.(R) a b)
    : pair_le s s'.

#[global]
Instance pair_le_Reflexive 
  : Reflexive pair_le.
Proof.
  intros s0. econs; eauto.
Qed.

#[global]
Instance pair_le_Transitive
  : Transitive pair_le.
Proof.
  intros s0 s1 s2 [? ? ?] [? ? ?]. simpl in *.
  econs; simpl in *; eauto; i. rewrite <- NO_INSERTION; eauto.
Qed.

#[global]
Instance pair_le_PreOrder : PreOrder pair_le :=
  { PreOrder_Reflexive := pair_le_Reflexive
  ; PreOrder_Transitive := pair_le_Transitive
  }.

Let pair_isSetoid : isSetoid pair :=
  mkSetoidFromPreOrder pair_le_PreOrder.

#[local] Existing Instance pair_isSetoid.

#[local]
Instance pair_isProset : isProset pair :=
  { leProp := pair_le
  ; Proset_isSetoid := pair_isSetoid
  ; leProp_PreOrder := pair_le_PreOrder
  ; leProp_PartialOrder := mkSetoidFromPreOrder_good pair_le_PreOrder
  }.

Definition pair_sup (I : Type) (chain : I -> pair) : pair :=
  {| P (x : X) := exists i : I, (chain i).(P) x; R (x : X) (y : X) := exists i : I, (chain i).(R) x y; |}.

Lemma pair_sup_isSupremum (I : Type) (chain : I -> pair)
  (H_chain : forall i1 : I, forall i2 : I, chain i1 =< chain i2 \/ chain i2 =< chain i1)
  : is_supremum_of (pair_sup I chain) (fun s : pair => exists i : I, s = chain i).
Proof.
  intros u; split.
  - intros [? ? ?]. intros x x_in. destruct x_in as [i ->]. econs; i.
    + eapply P_incl. simpl. exists i; eauto.
    + eapply R_incl. simpl. exists i; eauto.
    + rewrite -> NO_INSERTION; simpl; eauto. split.
      * intros [i' H_R]. pose proof (H_chain i i') as [[? ? ?] | [? ? ?]]; eauto. rewrite <- NO_INSERTION0; eauto.
      * intros H_R. exists i. eauto.
  - intros u_in. do 2 red in u_in. econs; simpl; i; des.
    + hexploit (u_in (chain i)).
      { exists i. reflexivity. }
      intros [? ? ?]; eauto.
    + hexploit (u_in (chain i)).
      { exists i. reflexivity. }
      intros [? ? ?]; eauto.
    + hexploit (u_in (chain i)).
      { exists i. reflexivity. }
      intros [? ? ?]. rewrite -> NO_INSERTION; eauto. split.
      * intros H_R. exists i. eauto.
      * intros [i' H_R]. pose proof (H_chain i i') as [[? ? ?] | [? ? ?]]; eauto. rewrite <- NO_INSERTION0; eauto.
Qed.

Context {SETOID : isSetoid X}.

#[local] Notation good s := (__wellorderingtheorem.good (X := X) (SETOID := SETOID) s.(P) s.(R)).

Lemma pair_sup_good (I : Type) (chain : I -> pair)
  (H_chain : forall i1 : I, forall i2 : I, chain i1 =< chain i2 \/ chain i2 =< chain i1)
  (chain_good : forall i : I, good (chain i))
  : good (pair_sup I chain).
Proof.
  split.
  - intros a b [i H_R]. pose proof (chain_good i) as [? ? ?]. pose proof (SOUND a b H_R). split; exists i; tauto.
  - intros a b [i1 H_P1] [i2 H_P2]. pose proof (H_chain i1 i2) as [[? ? ?] | [? ? ?]].
    + pose proof (chain_good i2) as [? ? ?]. hexploit (COMPLETE _ _ (P_incl _ H_P1) H_P2); eauto.
      intros [? | [? | ?]]; [left; tauto | right | right]; [left | right]; exists i2; tauto.
    + pose proof (chain_good i1) as [? ? ?]. hexploit (COMPLETE _ _ H_P1 (P_incl _ H_P2)); eauto.
      intros [? | [? | ?]]; [left; tauto | right | right]; [left | right]; exists i1; tauto.
  - intros x1. econs. intros x0 [i H_R]. pose proof (chain_good i) as [? ? ?].
    assert (H_Acc : Acc (chain i).(R) x0) by eauto.
    pose proof (SOUND _ _ H_R) as [H_P _]. clear H_R. induction H_Acc as [x0 _ IH]; intros; econs; intros y [i' H_R'].
    assert (LT : (chain i).(R) y x0).
    { pose proof (H_chain i i') as [[? ? ?] | [? ? ?]]; eauto. rewrite <- NO_INSERTION; eauto. }
    eapply IH; eauto. pose proof (SOUND _ _ LT) as [? ?]; tauto.
Qed.

Section NEXT.

Variable next : pair -> pair.

Hypothesis next_extensive : forall s : pair, s =< next s.

Hypothesis next_good : forall s : pair, good s -> good (next s).

Hypothesis next_exhausted : forall s : pair, (forall x : X, s.(P) x) \/ (exists x : X, (next s).(P) x /\ ~ s.(P) x).

End NEXT.

End WELL_ORDERING_THEOREM.

#[global] Arguments __wellorderingtheorem.pair : clear implicits.

End __wellorderingtheorem.
