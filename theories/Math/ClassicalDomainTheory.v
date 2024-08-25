Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Math.OrderTheory.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.subset.
#[local] Obligation Tactic := i.

#[local] Hint Resolve Equivalence_Reflexive Equivalence_Symmetric Equivalence_Transitive : poset_hints.
#[local] Hint Resolve eqProp_refl eqProp_sym eqProp_trans leProp_refl leProp_trans leProp_antisymmetry eqProp_implies_leProp : poset_hints.
#[global] Hint Resolve supremum_monotonic supremum_unique supremum_congruence is_supremum_of_compatWith_eqProp : poset_hints.

Section CPO_THEORY.

Import CpoDef.

Section SCOTT_TOPOLOGY.

#[local] Opaque "\in".

Context {D : Type} `{PROSET : isProset D}.

Variant isOpen_Scott (O : ensemble D) : Prop :=
  | isOpen_Scott_intro
    (UPWARD_CLOSED : forall x, forall y, x \in O -> x =< y -> y \in O)
    (LIMIT : forall X, forall sup_X, isDirected X -> is_supremum_of sup_X X -> sup_X \in O -> exists x, x \in X /\ x \in O)
    : isOpen_Scott O.

#[local] Hint Constructors isDirected : core.
#[local] Hint Constructors isOpen_Scott : core.

#[global]
Instance isOpen_Scott_good
  : AxiomsForTopology D isOpen_Scott.
Proof.
  split; ii.
  - split; done!.
  - split.
    + intros x y x_IN LE. rewrite E.in_unions_iff in x_IN. destruct x_IN as [O [x_IN H_IN]]. ss!. exists O; done!.
    + intros X sup_X DIRECTED SUPREMUM sup_IN. rewrite E.in_unions_iff in sup_IN. destruct sup_IN as [O [sup_IN H_IN]]. ss!.
      pose proof (OPENs O H_IN) as [? ?]. exploit (LIMIT X sup_X); eauto with *. intros [y [y_IN y_IN']]. exists y; done!.
  - split.
    + done!.
    + intros X sup_X DIRECTED SUPREMUM sup_IN. s!. destruct sup_IN as [sup_IN1 sup_IN2]. destruct OPEN1 as [UPWARD_CLOSED1 LIMIT1], OPEN2 as [UPWARD_CLOSED2 LIMIT2].
      exploit (LIMIT1 X sup_X); eauto with *. intros [x1 [x1_IN x1_IN']]. exploit (LIMIT2 X sup_X); eauto with *. intros [x2 [x2_IN x2_IN']]. destruct DIRECTED.
      pose proof (DIRECTED' x1 x2 x1_IN x2_IN) as [x3 [? [? ?]]]; exists x3; done!.
  - split.
    + intros x y x_IN LE. rewrite <- EXT_EQ in *. destruct OPEN as [? ?]. done!.
    + intros X sup_X DIRECTED SUPREMUM sup_IN. destruct OPEN as [? ?]. rewrite <- EXT_EQ in sup_IN.
      pose proof (LIMIT X sup_X DIRECTED SUPREMUM sup_IN) as [x [? ?]]; exists x; done!.
Qed.

End SCOTT_TOPOLOGY.

#[local]
Instance Scott_topology {D : Type} `{PROSET : isProset D} : topology D :=
  { isOpen := @isOpen_Scott D PROSET
  ; topologyLaws := @isOpen_Scott_good D PROSET
  }.

End CPO_THEORY.
