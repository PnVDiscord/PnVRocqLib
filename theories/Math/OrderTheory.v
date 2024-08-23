Require Import PnV.Prelude.Prelude.

Lemma well_founded_implies_Irreflexive {A : Type} (R : A -> A -> Prop)
  (WF : well_founded R)
  : Irreflexive R.
Proof.
  intros x H_R. induction (WF x) as [x _ IH]. eapply IH with (y := x); exact H_R.
Qed.

Class has_ltProp (A : Type) : Type :=
  { ltProp (lhs : A) (rhs : A) : Prop
  ; ltProp_StrictOrder :: StrictOrder ltProp
  }.

#[program]
Definition mkPosetFrom_ltProp {A : Type} (LTPROP : has_ltProp A) : isPoset A :=
  {| leProp x y := ltProp x y \/ x = y; Poset_isSetoid := mkSetoid_from_eq; |}.
Next Obligation.
  split; ii; firstorder try congruence. left. etransitivity; eauto.
Qed.
Next Obligation.
  destruct LTPROP as [lt [? ?]]. intros x y. cbn. unfold flip. cbv in StrictOrder_Irreflexive, StrictOrder_Transitive.
  split; firstorder try congruence. contradiction (StrictOrder_Irreflexive x). firstorder.
Qed.

Class hasSimulation (Src : Type) (Tgt : Type) {Src_isPoset : isPoset Src} {Tgt_isPoset : isPoset Tgt} : Type :=
  { simulation : Src -> Tgt
  ; simulation_compatWith_eqProp :: eqPropCompatible1 simulation
  ; simulation_spec s t'
    : (exists t, simulation s =< t /\ t == t') <-> (exists s', s =< s' /\ simulation s' == t')
  }.

Class isWellPreOrderedSet (A : Type) (leProp : A -> A -> Prop) {PREORDER : PreOrder leProp} : Type :=
  wellorder (x : nat -> A) : { '(i, j) : nat * nat | i < j /\ leProp (x i) (x j) }.
