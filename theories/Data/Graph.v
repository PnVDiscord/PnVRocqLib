Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Category.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Data.FiniteMap.
Require Import PnV.Prelude.X.

Import FS.
Import FM.

#[local] Abbreviation In := L.In.
#[local] Infix "\in" := E.In : type_scope.

Module GRAPH.

#[projections(primitive)]
Class t : Type :=
  mk
  { vertices : Type
  ; edges : ensemble (vertices * vertices)
  } as G.

End GRAPH.

Section GraphTheory_basic1.

#[local] Abbreviation vertices := GRAPH.vertices.
#[local] Abbreviation edges := GRAPH.edges.

Context {G : GRAPH.t}.

#[local] Abbreviation V := G.(vertices).
#[local] Abbreviation E := G.(edges).

Inductive walk (v : V) : V -> list V -> Prop :=
  | walk_refl
    : v ~~~[ [] ]~~> v
  | walk_step (v0 : V) (v1 : V) (w : list V)
    (H_edge : (v0, v1) \in E)
    (H_walk : v1 ~~~[ w ]~~> v)
    : v0 ~~~[ v1 :: w ]~~> v
  where " src ~~~[ w ]~~> tgt " := (walk tgt src w) : type_scope.

#[local] Hint Constructors walk : core.

Lemma walk_last (v0 : V) (v : V) (w : list V)
  (WALK : v0 ~~~[ w ]~~> v)
  : v = last w v0.
Proof.
  induction WALK as [ | v0 v1 w H_edge WALK IH].
  - reflexivity.
  - rewrite -> L.last_cons. exact IH.
Qed.

Theorem walk_iff (v0 : V) (vs : list V)
  : v0 ~~~[ vs ]~~> last vs v0 <-> L.Forall E (L.mk_edge_seq v0 vs).
Proof.
  split.
  - intros WALK. revert v0 WALK. induction vs as [ | v1 vs IH]; i.
    + econstructor 1.
    + simpl. rewrite -> L.last_cons in WALK. inv WALK.
      econstructor 2; eauto.
  - intros H_Forall. revert v0 H_Forall. induction vs as [ | v1 vs IH]; i.
    + simpl. econstructor 1.
    + rewrite -> L.last_cons. simpl in H_Forall. inv H_Forall.
      econstructor 2; eauto.
Qed.

Lemma walk_app (v1 : V) (v2 : V) (v : V) (vs1 : list V) (vs2 : list V)
  (WALK1 : v1 ~~~[ vs1 ]~~> v2)
  (WALK2 : v2 ~~~[ vs2 ]~~> v)
  : v1 ~~~[ vs1 ++ vs2 ]~~> v.
Proof.
  revert v1 v2 v vs2 WALK1 WALK2. induction vs1 as [ | v vs1 IH]; simpl; i; inv WALK1; eauto.
Qed.

Theorem walk_app_iff (v0 : V) (v' : V) (vs1 : list V) (vs2 : list V)
  : v0 ~~~[ vs1 ++ vs2 ]~~> v' <-> (exists v, v0 ~~~[ vs1 ]~~> v /\ v ~~~[ vs2 ]~~> v').
Proof.
  split.
  - intros WALK. revert v0 v' vs2 WALK. induction vs1 as [ | v1 vs1 IH]; simpl; i; eauto.
    inv WALK. apply IH in H_walk. des; eauto.
  - intros VIA. des. eapply walk_app; eauto.
Qed.

Inductive path (v : V) : V -> list V -> Prop :=
  | path_refl
    : v ---[ [] ]--> v
  | path_step (v0 : V) (v1 : V) (p : list V)
    (H_edge : (v0, v1) \in E)
    (H_path : v1 ---[ p ]--> v)
    (NOT_IN : ~ In v1 p)
    : v0 ---[ v1 :: p ]--> v
  where " src ---[ p ]--> tgt " := (path tgt src p) : type_scope.

#[local] Hint Constructors path : core.

Lemma path_vertices_no_dup (v0 : V) (v : V) (p : list V)
  (H_path : v0 ---[ p ]--> v)
  : NoDup p.
Proof.
  induction H_path as [ | v0 v1 p H_edge H_path IH NOT_IN]; econstructor; eauto.
Qed.

Lemma no_dup_walk_is_path (v0 : V) (v : V) (w : list V)
  (NO_DUP : NoDup w)
  (H_walk : v0 ~~~[ w ]~~> v)
  : v0 ---[ w ]--> v.
Proof.
  induction H_walk as [ | v0 v1 w H_edge H_walk IH]; i.
  - econstructor 1.
  - econstructor 2.
    + exact H_edge.
    + eapply IH. now inv NO_DUP.
    + now inv NO_DUP.
Qed.

Theorem path_iff_no_dup_walk (v0 : V) (v : V) (vs : list V)
  : v0 ---[ vs ]--> v <-> (v0 ~~~[ vs ]~~> v /\ NoDup vs).
Proof.
  split.
  - intros H_path. split.
    + induction H_path; simpl; eauto.
    + eapply path_vertices_no_dup; eauto.
  - intros [H_walk NO_DUP].
    eapply no_dup_walk_is_path; eauto.
Qed.

Lemma path_app_inv (v0 : V) (v' : V) (vs1 : list V) (vs2 : list V)
  (PATH : v0 ---[ vs1 ++ vs2 ]--> v')
  : exists v, v0 ---[ vs1 ]--> v /\ v ---[ vs2 ]--> v'.
Proof.
  rewrite -> path_iff_no_dup_walk in PATH. destruct PATH as [WALK NO_DUP].
  rewrite -> walk_app_iff in WALK. destruct WALK as (v&WALK1&WALK2).
  exists v. split; rewrite -> path_iff_no_dup_walk.
  - split; trivial. eapply NoDup_app_remove_r; eauto.
  - split; trivial. eapply NoDup_app_remove_l; eauto.
Qed.

Section Walk_finds_Path.

Lemma mk_subpath (v0 : V) (v1 : V) (v : V) (p : list V)
  (PATH : v0 ---[ p ]--> v)
  (ELEM : In v1 p)
  : exists p', v0 ---[ p' ]--> v1 /\ (exists p'', v1 ---[ p'' ]--> v /\ p = p' ++ p'').
Proof.
  revert v1 ELEM. induction PATH as [ | v0 v1 p H_edge PATH IH NOT_IN]; i; inv ELEM.
  - exists [v2]. split; eauto.
  - rename H into ELEM. pose proof (IH v2 ELEM) as (p'&PATH1&p''&PATH2&EQ).
    exists (v1 :: p'). split.
    + econstructor 2; eauto. subst p. rewrite in_app_iff in NOT_IN. tauto.
    + exists p''. split; [exact PATH2 | now rewrite EQ].
Qed.

Hypothesis In_dec : forall v : V, forall vs : list V, In v vs \/ ~ In v vs.

Theorem walk_finds_path (v0 : V) (v : V) (w : list V)
  (WALK : v0 ~~~[ w ]~~> v)
  : exists p, v0 ---[ p ]--> v.
Proof.
  revert v0 v WALK. induction w as [ | v' w IH] using List.rev_ind; i.
  - inv WALK. exists []. econstructor 1.
  - rewrite -> walk_app_iff in WALK. destruct WALK as (v1&WALK1&WALK2).
    inv WALK2. inv H_walk. pose proof (IH v0 v1 WALK1) as [p PATH].
    pose proof (In_dec v' p) as [ELEM | NOT_IN].
    + pose proof (mk_subpath v0 v' v1 p PATH ELEM) as (p'&PATH'&_).
      exists p'. exact PATH'.
    + exists (p ++ [v']). rewrite -> path_iff_no_dup_walk. split.
      * rewrite -> walk_app_iff. exists v1. split.
        { now eapply path_iff_no_dup_walk. }
        { econstructor 2; eauto. }
      * rewrite <- rev_involutive. eapply NoDup_rev.
        rewrite -> rev_unit. econstructor 2.
        { now rewrite <- In_rev. }
        { eapply NoDup_rev. eapply path_iff_no_dup_walk. exact PATH. }
Qed.

End Walk_finds_Path.

Definition trail (v' : V) (v : V) (vs : list V) : Prop :=
  v ~~~[ vs ]~~> v' /\ NoDup (L.mk_edge_seq v vs).

#[local] Notation " src ===[ t ]==> tgt " := (trail tgt src t) : type_scope.

Lemma path_implies_trail (v0 : V) (v : V) (p : list V)
  (PATH : v0 ---[ p ]--> v)
  : v0 ===[ p ]==> v.
Proof.
  rewrite path_iff_no_dup_walk in PATH.
  destruct PATH as [WALK NO_DUP]. split.
  - exact WALK.
  - eapply L.no_dup_mk_edge_seq. exact NO_DUP.
Qed.

Inductive Walk (v : V) : V -> Type :=
  | Walk_nil
    : `[ v -> v ]
  | Walk_cons v0 v1
    (H_edge : (v0, v1) \in E)
    (H_Walk : `[ v1 -> v ])
    : `[ v0 -> v ]
  where " `[ v -> v' ] " := (Walk v' v) : type_scope.

#[local] Arguments Walk_nil {v}.
#[local] Arguments Walk_cons {v} {v0} {v1}.

Fixpoint Walk_app {v0 : V} {v1 : V} {v2 : V} (H_walk_1 : `[ v0 -> v1 ]) : `[ v1 -> v2 ] -> `[ v0 -> v2 ] :=
  match H_walk_1 with
  | Walk_nil => fun H_walk_2 => H_walk_2
  | Walk_cons H_edge H_walk_1' => fun H_walk_2 => Walk_cons H_edge (Walk_app H_walk_1' H_walk_2)
  end.

#[global]
Instance Walk_cat : CAT.isCategory :=
  { ob := G.(GRAPH.vertices)
  ; hom v v' := `[ v -> v' ]
  ; compose {v0} {v1} {V2} WALK WALK' := Walk_app WALK' WALK
  ; id {v0} := Walk_nil
  }.

Fixpoint Walk_to_walk {v} {v'} (WALK : `[ v -> v' ]) : list V :=
  match WALK with
  | Walk_nil => []
  | Walk_cons H_edge WALK' => v :: Walk_to_walk WALK'
  end.

Definition isAcylic : Prop :=
  forall v : V, forall w : list V, length w > 0 -> ⟪ NOT_A_CYCLE : ~ (v ~~~[ w ]~~> v) ⟫.

End GraphTheory_basic1.

#[global] Arguments Walk_nil {G} {v}.
#[global] Arguments Walk_cons {G} {v} {v0} {v1}.
#[global] Arguments isAcylic : clear implicits.

#[local] Notation " `[ v -> v' ] " := (Walk v' v) : type_scope.

#[projections(primitive)]
Record Labeled {G : GRAPH.t} : Type :=
  { labels : Type
  ; labeling {v} {v'} (E_v_v' : (v, v') \in G.(GRAPH.edges)) : ensemble labels
  }.

#[global] Arguments Labeled : clear implicits.

Definition labeledWalk {G : GRAPH.t} {G_labeled : Labeled G} : forall v, forall v', `[ v -> v' ] -> ensemble (list G_labeled.(labels)) :=
  fix go (v : G.(GRAPH.vertices)) (v' : G.(GRAPH.vertices)) (H_Walk : `[ v -> v' ]) :=
  match H_Walk with
  | Walk_nil => pure (@L.nil G_labeled.(labels))
  | Walk_cons H_edge H_Walk' => liftM2 (@L.cons G_labeled.(labels)) (G_labeled.(labeling) H_edge) (go _ _ H_Walk')
  end.

Module DigraphFixedpoint.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.

#[local] Hint Rewrite L.in_flat_map : simplication_hints.

Section DIGRAPH_FIXEDPOINT.

#[local] Notation " src '~~~[' w ']~~>*('  G  ')' tgt " := (@walk G tgt src w).
#[local] Notation " src '---[' p ']-->*('  G  ')' tgt " := (@path G tgt src p).
#[local] Notation " src '===[' t ']==>*('  G  ')' tgt " := (@trail G tgt src t).

#[local] Infix "=~=" := (is_similar_to (Similarity := list_corresponds_to_finite_ensemble)).
#[local] Abbreviation vertices := GRAPH.vertices.
#[local] Abbreviation edges := GRAPH.edges.

Context {G : GRAPH.t}.

#[local] Abbreviation V := G.(vertices).
#[local] Abbreviation E := G.(edges).

#[local] Notation " src ~~~[ w ]~~> tgt " := (walk tgt src w) : type_scope.

Context {A : Type} (seed : V -> ensemble A).

Inductive gmu (x : V) : ensemble A :=
  | gmu_seed
    : seed x \subseteq gmu x
  | gmu_propagated y
    (EDGE : (x, y) \in E)
    : gmu y \subseteq gmu x.

Definition is_fixedpoint (value : V -> ensemble A) : Prop :=
  forall x, forall a, a \in value x <-> (a \in seed x \/ (exists y, (x, y) \in E /\ a \in value y)).

Theorem gmu_is_fixedpoint
  : is_fixedpoint gmu.
Proof.
  intros x a. split.
  - intros IN. induction IN as [x a SEED | x y EDGE a IN IH].
    + now left.
    + now right; exists y.
  - intros [SEED | (y & EDGE & IN)].
    + now eapply gmu_seed.
    + eapply gmu_propagated; eauto.
Qed.

Theorem gmu_is_least_fixedpoint (value : V -> ensemble A)
  (FIXPOINT : is_fixedpoint value)
  : forall x, gmu x \subseteq value x.
Proof.
  red in FIXPOINT. intros x a IN. induction IN as [x a SEED | x y EDGE a IN IH].
  - rewrite -> FIXPOINT with (x := x) (a := a). now left.
  - rewrite -> FIXPOINT with (x := x) (a := a). right. exists y. split; eauto.
Qed.

Variable seed' : V -> fin_ensemble A.

Hypothesis seed_sim : forall v, seed' v =~= seed v.

Variable vertices' : fin_ensemble V.

Definition reachable (x : V) : ensemble V :=
  fun y => exists w, x ~~~[ w ]~~> y.

Context `{V_dec : hasEqDec V} `{E_dec : forall x : V, forall y : V, B.Decision ((x, y) \in E)}.

Fixpoint reachableb (fuel : nat) (x : V) (y : V) {struct fuel} : bool :=
  match fuel with
  | O => eqb x y
  | S fuel' => eqb x y || L.existsb (fun z => if E_dec x z then reachableb fuel' z y else false) vertices'
  end.

Definition reachable' (x : V) : fin_ensemble V :=
  x :: L.filter (reachableb (L.length vertices') x) vertices'.

Lemma reachableb_elim (fuel : nat) (x : V) (y : V)
  (REACH : reachableb fuel x y = true)
  : exists w, L.length w <= fuel /\ x ~~~[ w ]~~> y.
Proof.
  revert x y REACH. induction fuel as [ | fuel IH]; i; simpl in REACH.
  - rewrite eqb_eq in REACH. subst y.
    exists []. split; [simpl; lia | econstructor 1].
  - rewrite orb_true_iff in REACH. destruct REACH as [EQ | REACH].
    + rewrite eqb_eq in EQ. subst y.
      exists []. split; [simpl; lia | econstructor 1].
    + rewrite -> L.existsb_exists in REACH.
      destruct REACH as (z & z_in & REACH).
      destruct (E_dec x z) as [EDGE | NO_EDGE]; try discriminate.
      pose proof (IH z y REACH) as (w & LENGTH & WALK).
      exists (z :: w). split; [simpl; lia | econstructor 2; eauto].
Qed.

Hypothesis vertices_edge_target : forall x, forall y, (x, y) \in E -> L.In y vertices'.

Lemma walk_elem_in_vertices (x : V) (y : V) (w : list V)
  (WALK : x ~~~[ w ]~~> y)
  : forall z, In z w -> In z vertices'.
Proof.
  induction WALK as [ | v0 v1 w EDGE WALK IH]; intros z IN; inv IN; eauto.
Qed.

Lemma walk_endpoint_in_vertices (x : V) (y : V) (w : list V)
  (WALK : x ~~~[ w ]~~> y)
  (NE : y ≠ x)
  : In y vertices'.
Proof.
  induction WALK as [ | v0 v1 w EDGE WALK IH]; eauto with *.
  pose proof (B.decide (y = v1)) as [EQ | NE']; eauto.
  subst y. eapply vertices_edge_target; eauto.
Qed.

Lemma reachableb_intro (fuel : nat) (x : V) (y : V) (w : list V)
  (WALK : x ~~~[ w ]~~> y)
  (LENGTH : L.length w <= fuel)
  : reachableb fuel x y = true.
Proof.
  revert fuel LENGTH.
  induction WALK as [ | v0 v1 w EDGE WALK IH]; i.
  - destruct fuel as [ | fuel]; simpl.
    + now rewrite eqb_eq.
    + rewrite orb_true_iff. left. now rewrite eqb_eq.
  - destruct fuel as [ | fuel]; simpl in LENGTH; [lia | ].
    simpl. rewrite orb_true_iff. right. rewrite L.existsb_exists.
    exists v1. split; eauto. destruct (E_dec v0 v1) as [EDGE' | NO_EDGE]; ss!.
Qed.

Lemma reachableb_iff_reachable (x : V) (y : V)
  : reachableb (L.length vertices') x y = true <-> y \in reachable x.
Proof.
  split.
  - intros REACH.
    pose proof (reachableb_elim _ _ _ REACH) as (w & _ & WALK).
    now exists w.
  - intros [w WALK].
    assert (exists p, x ---[ p ]-->*( G ) y) as [p PATH].
    { eapply @walk_finds_path with (G := G) (w := w); eauto.
      now intros v vs; pose proof (L.in_dec V_dec v vs) as [YES | NO]; [left | right].
    }
    rewrite path_iff_no_dup_walk in PATH.
    clear WALK. destruct PATH as [WALK NO_DUP].
    eapply reachableb_intro; eauto.
    eapply L.NoDup_incl_length; eauto.
    ii; eapply walk_elem_in_vertices; eauto.
Qed.

Lemma reachable_sim (x : V)
  : reachable' x =~= reachable x.
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff.
  intros y. unfold reachable'. simpl. rewrite -> L.filter_In. split.
  - intros [EQ | [_ REACH]].
    + subst y. exists []. econstructor 1.
    + now rewrite <- reachableb_iff_reachable.
  - intros REACH. destruct REACH as [w WALK].
    destruct (B.decide (y = x)) as [EQ | NE].
    + now left.
    + right. split.
      * eapply walk_endpoint_in_vertices; eauto.
      * rewrite reachableb_iff_reachable. exists w. exact WALK.
Qed.

Lemma walk_gmu (x : V) (y : V) (w : list V)
  (WALK : x ~~~[ w ]~~> y)
  : gmu y \subseteq gmu x.
Proof.
  induction WALK as [ | v0 v1 w EDGE WALK IH]; intros a IN; eauto. eapply gmu_propagated; eauto.
Qed.

Lemma reachable_seed_gmu (x : V) (y : V) (a : A)
  (REACH : y \in reachable x)
  (SEED : a \in seed y)
  : a \in gmu x.
Proof.
  destruct REACH as [w WALK]. eapply walk_gmu; [exact WALK | now eapply gmu_seed].
Qed.

Lemma reachable_step (x : V) (y : V) (z : V)
  (EDGE : (x, y) \in E)
  (REACH : z \in reachable y)
  : z \in reachable x.
Proof.
  destruct REACH as [w WALK]. exists (y :: w). econstructor; eauto.
Qed.

Lemma gmu_reachable_seed (x : V) (a : A)
  (IN : a \in gmu x)
  : exists y, y \in reachable x /\ a \in seed y.
Proof.
  induction IN as [x a SEED | x y EDGE a IN (z & REACH & SEED)].
  - exists x. split; [exists []; econstructor 1 | exact SEED].
  - exists z. split; [eapply reachable_step; eauto | exact SEED].
Qed.

Lemma gmu_iff_reachable_seed (x : V) (a : A)
  : a \in gmu x <-> a \in (reachable x >>= seed).
Proof.
  split.
  - eapply gmu_reachable_seed.
  - intros (y & REACH & SEED). eapply reachable_seed_gmu; eauto.
Qed.

Definition gmu' (x : V) : fin_ensemble A :=
  L.flat_map seed' (reachable' x).

Theorem gmu_sim (x : V)
  : gmu' x =~= gmu x.
Proof.
  pose proof (list_corresponds_to_finite_ensemble_flat_map (reachable' x) (reachable x) seed' seed (reachable_sim x) (fun x : V => fun _ => seed_sim x)) as FLAT_MAP.
  rewrite list_corresponds_to_finite_ensemble_iff in FLAT_MAP |- *. intros a. rewrite FLAT_MAP. symmetry. eapply gmu_iff_reachable_seed.
Qed.

End DIGRAPH_FIXEDPOINT.

#[local] Hint Rewrite @L.last_cons : simplication_hints.
#[local] Hint Constructors walk : simplication_hints.
#[local] Hint Constructors path : simplication_hints.

Section DIGRAPH.

#[local] Notation " src '~~~[' w ']~~>*('  G  ')' tgt " := (@walk G tgt src w).
#[local] Notation " src '---[' p ']-->*('  G  ')' tgt " := (@path G tgt src p).
#[local] Notation " src '===[' t ']==>*('  G  ')' tgt " := (@trail G tgt src t).

#[local] Infix "\in" := E.In.
#[local] Infix "∈" := L.In.

Context {X : Type}.

Fixpoint digraph_value {A : Type} `{EQ_DEC : hasEqDec A} (fuel : nat) (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) : fin_ensemble A :=
  match fuel with
  | O => normalize (seed x)
  | S fuel' => normalize (union (seed x) (flat_map (digraph_value fuel' seed deps) (deps x)))
  end.

Inductive digraph_closure {A : Type} (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (a : A) (x : X) : Prop :=
  | digraph_closure_seed
    (IN : a ∈ seed x)
    : digraph_closure seed deps a x
  | digraph_closure_step y
    (EDGE : y ∈ deps x)
    (IN : digraph_closure seed deps a y)
    : digraph_closure seed deps a x.

Inductive digraph_trace {A : Type} (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (a : A) (x : X) : ensemble (list X) :=
  | digraph_trace_seed
    (IN : a ∈ seed x)
    : [] \in digraph_trace seed deps a x
  | digraph_trace_step y tr
    (EDGE : y ∈ deps x)
    (TRACE : digraph_trace seed deps a y tr)
    : y :: tr \in digraph_trace seed deps a x.

Theorem digraph_closure_iff_trace {A : Type} (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) (a : A)
  : digraph_closure seed deps a x <-> (exists tr, tr \in digraph_trace seed deps a x).
Proof.
  split.
  - intros IN. induction IN as [x IN | x y EDGE IN IH].
    + exists []. eapply digraph_trace_seed. exact IN.
    + destruct IH as [tr TRACE]. exists (y :: tr). eapply digraph_trace_step; eauto.
  - intros [tr TRACE]. induction TRACE as [x IN | x y tr EDGE TRACE IH].
    + eapply digraph_closure_seed; eauto.
    + eapply digraph_closure_step; eauto.
Qed.

Lemma digraph_trace_in_nodes {A : Type} (nodes : fin_ensemble X) (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) (a : A) (tr : list X)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  (TRACE : tr \in digraph_trace seed deps a x)
  : Forall (fun y => y ∈ nodes) tr.
Proof.
  induction TRACE as [x IN | x y tr EDGE TRACE IH]; [econs 1 | econs 2]; eauto.
Qed.

Definition digraph_graph (deps : X -> fin_ensemble X) : GRAPH.t :=
  {|
    GRAPH.vertices := X;
    GRAPH.edges := fun '(x, x') => x' ∈ deps x;
  |}.

Lemma digraph_trace_seed_at_last {A : Type} (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) (a : A) (tr : list X)
  (TRACE : tr \in digraph_trace seed deps a x)
  : a ∈ seed (last tr x).
Proof.
  induction TRACE as [x IN | x y tr EDGE TRACE IH]; ss!.
Qed.

Lemma digraph_trace_walk {A : Type} (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) (a : A) (tr : list X)
  (TRACE : tr \in digraph_trace seed deps a x)
  : x ~~~[ tr ]~~>*( digraph_graph deps ) last tr x.
Proof.
  induction TRACE as [x IN | x y tr EDGE TRACE IH]; ss!.
Qed.

Lemma digraph_walk_trace {A : Type} (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) (a : A) (x' : X) (tr : list X)
  (WALK : x ~~~[ tr ]~~>*( digraph_graph deps ) x')
  (IN : a ∈ seed x')
  : tr \in digraph_trace seed deps a x.
Proof.
  induction WALK as [ | v0 v1 w EDGE WALK IH]; now constructor.
Qed.

Lemma digraph_trace_simple {A : Type} `{X_hasEqDec : hasEqDec X} (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) (a : A) (tr : list X)
  (TRACE : tr \in digraph_trace seed deps a x)
  : exists simple, digraph_trace seed deps a x simple /\ NoDup simple.
Proof.
  pose proof (digraph_trace_walk seed deps x a tr TRACE) as WALK.
  pose proof (digraph_trace_seed_at_last seed deps x a tr TRACE) as SEED.
  assert (exists simple, x ---[ simple ]-->*( digraph_graph deps ) last tr x) as [simple PATH].
  { eapply walk_finds_path with (w := tr); auto. intros v vs.
    now pose proof (@L.in_dec X X_hasEqDec v vs) as [YES | NO]; [left | right].
  }
  rewrite path_iff_no_dup_walk in PATH. destruct PATH as [WALK' NO_DUP].
  exists simple; split; [eapply digraph_walk_trace; eauto | exact NO_DUP].
Qed.

Lemma digraph_trace_simple_bounded {A : Type} `{X_hasEqDec : hasEqDec X} (nodes : fin_ensemble X) (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) (a : A) (tr : list X)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  (TRACE : tr \in digraph_trace seed deps a x)
  : exists simple, simple \in digraph_trace seed deps a x /\ length simple <= length nodes.
Proof.
  pose proof (digraph_trace_simple seed deps x a tr TRACE) as (simple & TRACE' & NO_DUP).
  pose proof (digraph_trace_in_nodes nodes seed deps x a simple deps_CLOSED TRACE') as IN_NODES.
  exists simple. split; trivial. eapply L.NoDup_incl_length; [exact NO_DUP | intros y IN].
  rewrite Forall_forall in IN_NODES. now eapply IN_NODES.
Qed.

Definition digraph_equation {A : Type} (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (value : X -> fin_ensemble A) : Prop :=
  forall x, forall a, a ∈ value x <-> ⟪ UNFOLD : a ∈ seed x \/ (exists y, y ∈ deps x /\ a ∈ value y) ⟫.

Lemma digraph_value_seed {A : Type} `{EQ_DEC : hasEqDec A} (fuel : nat) (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) (a : A)
  (IN : a ∈ seed x)
  : a ∈ digraph_value fuel seed deps x.
Proof.
  destruct fuel as [ | fuel]; ss!.
Qed.

Lemma digraph_value_propagated {A : Type} `{EQ_DEC : hasEqDec A} (fuel : nat) (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) (y : X) (a : A)
  (EDGE : y ∈ deps x)
  (IN : a ∈ digraph_value fuel seed deps y)
  : a ∈ digraph_value (S fuel) seed deps x.
Proof.
  ss!.
Qed.

Theorem digraph_value_elim {A : Type} `{EQ_DEC : hasEqDec A} (fuel : nat) (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) (a : A)
  (IN : a ∈ digraph_value fuel seed deps x)
  : digraph_closure seed deps a x.
Proof.
  revert x a IN. induction fuel as [ | fuel IH]; intros x a IN; simpl in IN.
  - eapply digraph_closure_seed. ss!.
  - ss!.
    + now eapply digraph_closure_seed.
    + eapply digraph_closure_step; ss!.
Qed.

Lemma digraph_value_monotone_step {A : Type} `{EQ_DEC : hasEqDec A} (fuel : nat) (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) (a : A)
  (IN : a ∈ digraph_value fuel seed deps x)
  : a ∈ digraph_value (S fuel) seed deps x.
Proof.
  revert x a IN; induction fuel as [ | fuel IH]; intros x a IN; simpl in IN |- *; ss!.
Qed.

Lemma digraph_value_monotone {A : Type} `{EQ_DEC : hasEqDec A} (fuel1 : nat) (fuel2 : nat) (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) (a : A)
  (LE : fuel1 <= fuel2)
  (IN : a ∈ digraph_value fuel1 seed deps x)
  : a ∈ digraph_value fuel2 seed deps x.
Proof.
  revert fuel1 x a LE IN; induction fuel2 as [ | fuel2 IH]; intros fuel1 x a LE IN.
  - assert (fuel1 = O) as EQ by lia.
    done!.
  - pose proof (Nat.eq_dec fuel1 (S fuel2)) as [EQ | NE].
    + done!.
    + eapply digraph_value_monotone_step. eapply IH with (fuel1 := fuel1) (x := x) (a := a); done!.
Qed.

Theorem digraph_trace_value {A : Type} `{EQ_DEC : hasEqDec A} (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) (a : A) (tr : list X) (fuel : nat)
  (TRACE : tr \in digraph_trace seed deps a x)
  (LE : length tr <= fuel)
  : a ∈ digraph_value fuel seed deps x.
Proof.
  revert fuel LE; induction TRACE as [x IN | x y tr EDGE TRACE IH]; intros fuel LE.
  - now eapply digraph_value_seed.
  - destruct fuel as [ | fuel]; simpl in LE; [lia | eapply digraph_value_propagated]; done!.
Qed.

Theorem digraph_closure_intro {A : Type} `{EQ_DEC : hasEqDec A} (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) (a : A)
  (IN : digraph_closure seed deps a x)
  : exists fuel, a ∈ digraph_value fuel seed deps x.
Proof.
  induction IN as [x SEED_IN | x y EDGE CLOSURE IH].
  - exists O. eapply digraph_value_seed. exact SEED_IN.
  - destruct IH as [fuel VALUE_IN]. exists (S fuel). eapply digraph_value_propagated; eauto.
Qed.

Theorem digraph_closure_least {A : Type} (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (value : X -> fin_ensemble A) (x : X) (a : A)
  (EQUATION : digraph_equation seed deps value)
  (IN : digraph_closure seed deps a x)
  : a ∈ value x.
Proof.
  induction IN as [x SEED_IN | x y EDGE CLOSURE IH].
  - exact (proj2 (EQUATION x a) (or_introl SEED_IN)).
  - exact (proj2 (EQUATION x a) (or_intror (@ex_intro _ _ y (conj EDGE IH)))).
Qed.

#[local] Open Scope function_scope.

Definition digraph_fixedpoint {A : Type} (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (value' : X -> ensemble A) : Prop :=
  forall x, forall a, a \in value' x <-> ⟪ STEP : a ∈ seed x \/ (exists y, y ∈ deps x /\ a \in value' y) ⟫.

Theorem digraph_closure_fixedpoint {A : Type} (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X)
  : digraph_fixedpoint seed deps (fun x => { a : A | digraph_closure seed deps a x }).
Proof.
  intros x a. unfold E.In; unnw. split.
  - intros CLOSURE. destruct CLOSURE as [SEED_IN | y EDGE CLOSURE].
    + now left.
    + now right; exists y.
  - intros [SEED_IN | (y & EDGE & CLOSURE)].
    + now eapply digraph_closure_seed.
    + now eapply digraph_closure_step with (y := y).
Qed.

Theorem digraph_closure_least_fixedpoint {A : Type} (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (value : X -> ensemble A)
  (FIXPOINT : digraph_fixedpoint seed deps value)
  : forall x, { a : A | digraph_closure seed deps a x } \subseteq value x.
Proof.
  intros x a CLOSURE; induction CLOSURE as [x SEED_IN | x y EDGE CLOSURE IH]; ss!.
Qed.

Theorem digraph_closure_intro_bounded {A : Type} `{EQ_DEC : hasEqDec A} `{X_hasEqDec : hasEqDec X} (fuel : nat) (nodes : fin_ensemble X) (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) (a : A)
  (fuel_ENOUGH : length nodes <= fuel)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  (IN : digraph_closure seed deps a x)
  : a ∈ digraph_value fuel seed deps x.
Proof.
  rewrite digraph_closure_iff_trace in IN. destruct IN as [tr TRACE].
  pose proof (digraph_trace_simple_bounded nodes seed deps x a tr deps_CLOSED TRACE) as (simple & TRACE' & LENGTH).
  eapply digraph_trace_value with (tr := simple); ss!.
Qed.

Theorem digraph_value_iff_closure_bounded {A : Type} `{EQ_DEC : hasEqDec A} `{X_hasEqDec : hasEqDec X} (fuel : nat) (nodes : fin_ensemble X) (seed : X -> fin_ensemble A) (deps : X -> fin_ensemble X) (x : X) (a : A)
  (fuel_ENOUGH : length nodes <= fuel)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  : a ∈ digraph_value fuel seed deps x <-> digraph_closure seed deps a x.
Proof.
  split.
  - exact (digraph_value_elim fuel seed deps x a).
  - intros IN. eapply digraph_closure_intro_bounded; eauto.
Qed.

End DIGRAPH.

End DigraphFixedpoint.

#[local] Hint Rewrite L.in_remove_iff : simplication_hints.

Module GraphAPI.

#[local] Infix "=~=" := is_similar_to.

#[universes(template), projections(primitive)]
Class FiniteGraph `{V : Type} : Type :=
  mkFiniteGraph
  { E : ensemble (V * V)
  ; G := {| GRAPH.vertices := V; GRAPH.edges := E |}
  ; V_dec : hasEqDec V
  ; E_dec (v : V) (v' : V) : B.Decision ((v, v') \in E) 
  ; enum_vertices : fin_ensemble V
  ; enum_vertices_contains_all
    : exists extras : ensemble V, enum_vertices =~= E.union { v : V | (exists v_in, (v_in, v) \in E) \/ (exists v_out, (v, v_out) \in E) } extras
  } as GRAPH.

#[global] Arguments E {V} GRAPH.
#[global] Arguments enum_vertices_contains_all {V} GRAPH : simpl never.

#[local] Existing Instance G.
#[global] Existing Instance V_dec.
#[global] Existing Instance E_dec.

Notation " src '~~~[' w ']~~>*('  GRAPH  ')' tgt " := (@walk GRAPH.(G) tgt src w).
Notation " src '---[' p ']-->*('  GRAPH  ')' tgt " := (@path GRAPH.(G) tgt src p).
Notation " src '===[' t ']==>*('  GRAPH  ')' tgt " := (@trail GRAPH.(G) tgt src t).

Abbreviation gmu := (DigraphFixedpoint.gmu (G := G)).

Section FiniteGraph_CONSTRUCTION.

#[local] Obligation Tactic := i.

Context {V : Type}.

#[refine]
Definition emptyFiniteGraph `{V_hasEqDec : hasEqDec V} : @FiniteGraph V :=
  {|
    E := fun '(v, v') => False;
    V_dec := V_hasEqDec;
    E_dec := fun v : V => fun v' : V => B.decide _;
    enum_vertices := [];
  |}.
Proof.
  rewrite FS.subset_lemma in *. done.
Defined.

Lemma emptyFiniteGraph_edge_spec {V_hasEqDec : hasEqDec V}
  : forall edge : V * V, edge \in (emptyFiniteGraph).(E) <-> edge \in E.empty.
Proof.
  intros [v v']; done.
Qed.

#[refine]
Definition insertEdge (v_in : V) (v_out : V) (GRAPH : @FiniteGraph V) : @FiniteGraph V :=
  {|
    E := fun '(v, v') => (v = v_in /\ v' = v_out) \/ E.In (v, v') GRAPH.(E);
    V_dec := GRAPH.(V_dec);
    E_dec := fun v : V => fun v' : V => B.decide _;
    enum_vertices := v_in :: v_out :: GRAPH.(enum_vertices);
  |}.
Proof.
  pose proof GRAPH.(enum_vertices_contains_all) as HH.
  rewrite FS.subset_lemma in *. done.
Defined.

Lemma insertEdge_edge_spec v_in v_out GRAPH
  : forall edge : V * V, edge \in (insertEdge v_in v_out GRAPH).(E) <-> edge \in E.insert (v_in, v_out) GRAPH.(E).
Proof.
  intros [v v']; done.
Qed.

#[refine]
Definition removeEdge (v_in : V) (v_out : V) (GRAPH : @FiniteGraph V) : @FiniteGraph V :=
  {|
    E := fun '(v, v') => (~ (v = v_in /\ v' = v_out)) /\ E.In (v, v') GRAPH.(E);
    V_dec := GRAPH.(V_dec);
    E_dec := fun v : V => fun v' : V => B.decide _;
    enum_vertices := GRAPH.(enum_vertices);
  |}.
Proof.
  pose proof GRAPH.(enum_vertices_contains_all) as HH.
  rewrite FS.subset_lemma in *. done.
Defined.

Lemma removeEdge_edge_spec v_in v_out GRAPH
  : forall edge : V * V, edge \in (removeEdge v_in v_out GRAPH).(E) <-> edge \in E.delete (v_in, v_out) GRAPH.(E).
Proof.
  intros [v v']; done.
Qed.

#[refine]
Definition insertVertex (v_new : V) (GRAPH : @FiniteGraph V) : @FiniteGraph V :=
  {|
    E := GRAPH.(E);
    V_dec := GRAPH.(V_dec);
    E_dec := GRAPH.(E_dec);
    enum_vertices := v_new :: GRAPH.(enum_vertices);
  |}.
Proof.
  pose proof GRAPH.(enum_vertices_contains_all) as HH.
  rewrite FS.subset_lemma in *. done.
Defined.

Lemma insertVertex_edge_spec v_new GRAPH
  : forall edge : V * V, edge \in (insertVertex v_new GRAPH).(E) <-> edge \in GRAPH.(E).
Proof.
  intros [v v']; done.
Qed.

#[refine]
Definition removeVertex (v_old : V) (GRAPH : @FiniteGraph V) : @FiniteGraph V :=
  {|
    E := fun '(v, v') => v ≠ v_old /\ v' ≠ v_old /\ E.In (v, v') GRAPH.(E);
    V_dec := GRAPH.(V_dec);
    E_dec := fun v : V => fun v' : V => B.decide _;
    enum_vertices := @L.remove V GRAPH.(V_dec) v_old GRAPH.(enum_vertices);
  |}.
Proof.
  pose proof GRAPH.(enum_vertices_contains_all) as HH.
  rewrite FS.subset_lemma in *. done.
Defined.

Lemma removeVertex_edge_spec v_old GRAPH
  : forall edge : V * V, edge \in (removeVertex v_old GRAPH).(E) <-> (fst edge ≠ v_old /\ snd edge ≠ v_old /\ edge \in GRAPH.(E)).
Proof.
  intros [v v']; done.
Qed.

Class ColoredGraph {C : Type} (GRAPH : @FiniteGraph V) : Type :=
  color_of_vertex : V -> C.

End FiniteGraph_CONSTRUCTION.

Section EXPORT.

Context `{GRAPH : FiniteGraph}.

#[local] Abbreviation E := GRAPH.(E).

Lemma walk_last (v : V) (v' : V) (w : list V)
  (WALK : v ~~~[ w ]~~>*( GRAPH ) v')
  : v' = last w v.
Proof.
  exact (Graph.walk_last v v' w WALK).
Qed.

Theorem walk_iff (v : V) (w : list V)
  : v ~~~[ w ]~~>*( GRAPH ) last w v <-> L.Forall E (L.mk_edge_seq v w).
Proof.
  exact (Graph.walk_iff v w).
Qed.

Lemma walk_app (v1 : V) (v2 : V) (v : V) (w1 : list V) (w2 : list V)
  (WALK1 : v1 ~~~[ w1 ]~~>*( GRAPH ) v2)
  (WALK2 : v2 ~~~[ w2 ]~~>*( GRAPH ) v)
  : v1 ~~~[ w1 ++ w2 ]~~>*( GRAPH ) v.
Proof.
  exact (Graph.walk_app v1 v2 v w1 w2 WALK1 WALK2).
Qed.

Theorem walk_app_iff (v1 : V) (v : V) (w1 : list V) (w2 : list V)
  : v1 ~~~[ w1 ++ w2 ]~~>*( GRAPH ) v <-> (exists v2, v1 ~~~[ w1 ]~~>*( GRAPH ) v2 /\ v2 ~~~[ w2 ]~~>*( GRAPH ) v).
Proof.
  exact (Graph.walk_app_iff v1 v w1 w2).
Qed.

Lemma path_vertices_no_dup (v : V) (v' : V) (p : list V)
  (PATH : v ---[ p ]-->*( GRAPH ) v')
  : NoDup p.
Proof.
  exact (Graph.path_vertices_no_dup v v' p PATH).
Qed.

Lemma no_dup_walk_is_path (v : V) (v' : V) (w : list V)
  (NO_DUP : NoDup w)
  (WALK : v ~~~[ w ]~~>*( GRAPH ) v')
  : v ---[ w ]-->*( GRAPH ) v'.
Proof.
  exact (Graph.no_dup_walk_is_path v v' w NO_DUP WALK).
Qed.

Theorem path_iff_no_dup_walk (v : V) (v' : V) (w : list V)
  : v ---[ w ]-->*( GRAPH ) v' <-> (v ~~~[ w ]~~>*( GRAPH ) v' /\ NoDup w).
Proof.
  exact (Graph.path_iff_no_dup_walk v v' w).
Qed.

Lemma path_app_inv (v1 : V) (v : V) (p1 : list V) (p2 : list V)
  (PATH : v1 ---[ p1 ++ p2 ]-->*( GRAPH ) v)
  : exists v2, v1 ---[ p1 ]-->*( GRAPH ) v2 /\ v2 ---[ p2 ]-->*( GRAPH ) v.
Proof.
  exact (Graph.path_app_inv v1 v p1 p2 PATH).
Qed.

Lemma mk_subpath (v0 : V) (v : V) (v' : V) (p : list V)
  (PATH : v0 ---[ p ]-->*( GRAPH ) v')
  (ELEM : In v p)
  : exists p', v0 ---[ p' ]-->*( GRAPH ) v /\ (exists p'', v ---[ p'' ]-->*( GRAPH ) v' /\ p = p' ++ p'').
Proof.
  exact (Graph.mk_subpath v0 v v' p PATH ELEM).
Qed.

Theorem walk_finds_path (v : V) (v' : V) (w : list V)
  (WALK : v ~~~[ w ]~~>*( GRAPH ) v')
  : exists p, v ---[ p ]-->*( GRAPH ) v'.
Proof.
  eapply Graph.walk_finds_path with (w := w).
  - ii. now pose proof (L.in_dec V_dec v0 vs) as [YES | NO]; [left | right].
  - exact WALK.
Qed.

Lemma path_implies_trail (v : V) (v' : V) (p : list V)
  (PATH : v ---[ p ]-->*( GRAPH ) v')
  : v ===[ p ]==>*( GRAPH ) v'.
Proof.
  eapply Graph.path_implies_trail with (p := p). exact PATH.
Qed.

Definition reachable (v : V) : ensemble V :=
  fun v' => exists w, v ~~~[ w ]~~>*( GRAPH ) v'.

Lemma reachable_step (v : V) (v' : V) (v'' : V)
  (EDGE : (v, v') \in E)
  (REACHABLE : v'' \in reachable v')
  : v'' \in reachable v.
Proof.
  exact (DigraphFixedpoint.reachable_step v v' v'' EDGE REACHABLE).
Qed.

Lemma enum_vertices_has_edge_tgt (v : V) (v' : V)
  (EDGE : (v, v') \in E)
  : L.In v' enum_vertices.
Proof.
  pose proof GRAPH.(enum_vertices_contains_all) as SIM. ss!.
Qed.

Fixpoint reachableb_accum (fuel : nat) (v : V) (v' : V) {struct fuel} : bool :=
  match fuel with
  | O => eqb v v'
  | S fuel' => eqb v v' || L.existsb (fun v1 => if E_dec v v1 then reachableb_accum fuel' v1 v' else false) enum_vertices
  end.

Lemma reachableb_accum_elim (fuel : nat) (v : V) (v' : V)
  (REACHABLE : reachableb_accum fuel v v' = true)
  : exists w, L.length w <= fuel /\ v ~~~[ w ]~~>*( GRAPH ) v'.
Proof.
  exact (DigraphFixedpoint.reachableb_elim enum_vertices fuel v v' REACHABLE).
Qed.

Lemma reachableb_accum_intro (fuel : nat) (v : V) (v' : V) (w : list V)
  (WALK : v ~~~[ w ]~~>*( GRAPH ) v')
  (LENGTH : L.length w <= fuel)
  : reachableb_accum fuel v v' = true.
Proof.
  exact (DigraphFixedpoint.reachableb_intro enum_vertices enum_vertices_has_edge_tgt fuel v v' w WALK LENGTH).
Qed.

Definition reachableb : forall v : V, forall v' : V, bool :=
  reachableb_accum (L.length enum_vertices).

Theorem reachableb_spec (v : V) (v' : V)
  : reachableb v v' = true <-> v' \in reachable v.
Proof.
  exact (DigraphFixedpoint.reachableb_iff_reachable enum_vertices enum_vertices_has_edge_tgt v v').
Qed.

Definition reachable_impl (v : V) : fin_ensemble V :=
  v :: L.filter (reachableb v) enum_vertices.

Theorem reachable_sim
  : forall v, reachable_impl v =~= reachable v.
Proof.
  exact (DigraphFixedpoint.reachable_sim enum_vertices enum_vertices_has_edge_tgt).
Qed.

Section DIGRAPH.

#[local] Infix "\subseteq" := E.isSubsetOf.

Context {A : Type}.

Definition gmu_impl (seed_impl : V -> fin_ensemble A) (v : V) : fin_ensemble A :=
  L.flat_map seed_impl (reachable_impl v).

Variable seed : V -> ensemble A.

Lemma walk_gmu (v : V) (v' : V) (w : list V)
  (WALK : v ~~~[ w ]~~>*( GRAPH ) v')
  : gmu seed v' \subseteq gmu seed v.
Proof.
  exact (DigraphFixedpoint.walk_gmu seed v v' w WALK).
Qed.

Lemma reachable_seed_gmu (v : V) (v' : V) (a : A)
  (REACHABLE : v' \in reachable v)
  (SEED : a \in seed v')
  : a \in gmu seed v.
Proof.
  exact (DigraphFixedpoint.reachable_seed_gmu seed v v' a REACHABLE SEED).
Qed.

Lemma gmu_reachable_seed (v : V) (a : A)
  (IN : a \in gmu seed v)
  : exists v', v' \in reachable v /\ a \in seed v'.
Proof.
  exact (DigraphFixedpoint.gmu_reachable_seed seed v a IN).
Qed.

Lemma gmu_iff_reachable_seed (v : V) (a : A)
  : a \in gmu seed v <-> a \in (reachable v >>= seed).
Proof.
  exact (DigraphFixedpoint.gmu_iff_reachable_seed seed v a).
Qed.

Theorem gmu_sim (seed_impl : V -> fin_ensemble A)
  (seed_sim : forall v, seed_impl v =~= seed v)
  : forall v, gmu_impl seed_impl v =~= gmu seed v.
Proof.
  exact (DigraphFixedpoint.gmu_sim seed seed_impl seed_sim enum_vertices enum_vertices_has_edge_tgt).
Qed.

#[local] Abbreviation is_fixedpoint value := (forall v, forall a, a \in value v <-> ⟪ STEP : a \in seed v \/ (exists v', (v, v') \in E /\ a \in value v') ⟫).

Theorem gmu_is_fixedpoint
  : is_fixedpoint (gmu seed).
Proof.
  exact (DigraphFixedpoint.gmu_is_fixedpoint seed).
Qed.

Theorem gmu_is_least_fixedpoint (value : V -> ensemble A)
  (FIXPOINT : is_fixedpoint value)
  : forall v, gmu seed v \subseteq value v.
Proof.
  exact (DigraphFixedpoint.gmu_is_least_fixedpoint seed value FIXPOINT).
Qed.

End DIGRAPH.

Section DIGRAPH_FIXEDPOINT.

#[local] Infix "∈" := L.In.
#[local] Infix "\subseteq" := E.isSubsetOf.

Definition deps (v : V) : fin_ensemble V :=
  L.filter (fun v' => if E_dec v v' then true else false) enum_vertices.

Lemma in_deps_iff (v : V) (v' : V)
  : v' ∈ deps v <-> (v, v') \in E.
Proof.
  unfold deps. rewrite L.filter_In.
  destruct (E_dec _ _) as [YES | NO]; ss!.
  eapply enum_vertices_has_edge_tgt; eauto.
Qed.

#[local] Hint Rewrite in_deps_iff : simplication_hints.

Context {A : Type}.

Variable seed : V -> fin_ensemble A.

Definition digraph_cl (v : V) : ensemble A :=
  fun a => DigraphFixedpoint.digraph_closure seed deps a v.

Definition digraph_trace (v : V) : A -> list V -> Prop :=
  fun a => DigraphFixedpoint.digraph_trace seed deps a v.

Theorem digraph_cl_iff_digraph_trace (v : V) (a : A)
  : a \in digraph_cl v <-> (exists tr, tr \in digraph_trace v a).
Proof.
  exact (DigraphFixedpoint.digraph_closure_iff_trace seed deps v a).
Qed.

Lemma digraph_trace_seed_at_last (v : V) (a : A) (tr : list V)
  (TRACE : tr \in digraph_trace v a)
  : a ∈ seed (last tr v).
Proof.
  eapply DigraphFixedpoint.digraph_trace_seed_at_last; eauto.
Qed.

#[local] Hint Constructors walk : core.
#[local] Hint Rewrite @L.last_cons : simplication_hints.

Lemma digraph_trace_walk (v : V) (a : A) (tr : list V)
  (TRACE : tr \in digraph_trace v a)
  : v ~~~[ tr ]~~>*( GRAPH ) L.last tr v.
Proof.
  induction TRACE as [x IN | x y tr EDGE TRACE IH]; ss!.
Qed.

Lemma digraph_trace_simple (v : V) (a : A) (tr : list V)
  (TRACE : tr \in digraph_trace v a)
  : exists simple, simple \in digraph_trace v a /\ NoDup simple.
Proof.
  eapply DigraphFixedpoint.digraph_trace_simple; eauto.
Qed.

Lemma digraph_trace_in_nodes (nodes : fin_ensemble V) (v : V) (a : A) (tr : list V)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  (TRACE : tr \in digraph_trace v a)
  : Forall (fun y => y ∈ nodes) tr.
Proof.
  eapply DigraphFixedpoint.digraph_trace_in_nodes; eauto.
Qed.

Lemma digraph_trace_simple_bounded (nodes : fin_ensemble V) (v : V) (a : A) (tr : list V)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  (TRACE : tr \in digraph_trace v a)
  : exists simple, simple \in digraph_trace v a /\ length simple <= length nodes.
Proof.
  eapply DigraphFixedpoint.digraph_trace_simple_bounded; eauto.
Qed.

Definition is_digraph_fixedpoint (value : V -> ensemble A) : Prop :=
  forall v, forall a, a \in value v <-> ⟪ STEP : a ∈ seed v \/ (exists v', v' ∈ deps v /\ a \in value v') ⟫.

Theorem digraph_cl_is_fixedpoint
  : is_digraph_fixedpoint digraph_cl.
Proof.
  exact (DigraphFixedpoint.digraph_closure_fixedpoint seed deps).
Qed.

Theorem digraph_cl_is_least_fixedpoint (value : V -> ensemble A)
  (FIXPOINT : is_digraph_fixedpoint value)
  : forall v, digraph_cl v \subseteq value v.
Proof.
  exact (DigraphFixedpoint.digraph_closure_least_fixedpoint seed deps value FIXPOINT).
Qed.

Variable A_dec : hasEqDec A.

Definition digraph_cl_accum (fuel : nat) (v : V) : fin_ensemble A :=
  DigraphFixedpoint.digraph_value fuel seed deps v.

Lemma digraph_cl_accum_seed (fuel : nat) (v : V) (a : A)
  (IN : a ∈ seed v)
  : a ∈ digraph_cl_accum fuel v.
Proof.
  exact (DigraphFixedpoint.digraph_value_seed fuel seed deps v a IN).
Qed.

Lemma digraph_cl_accum_propagated (fuel : nat) (v : V) (v' : V) (a : A)
  (EDGE : v' ∈ deps v)
  (IN : a ∈ digraph_cl_accum fuel v')
  : a ∈ digraph_cl_accum (S fuel) v.
Proof.
  exact (DigraphFixedpoint.digraph_value_propagated fuel seed deps v v' a EDGE IN).
Qed.

Theorem digraph_cl_accum_elim (fuel : nat) (v : V) (a : A)
  (IN : a ∈ digraph_cl_accum fuel v)
  : a \in digraph_cl v.
Proof.
  exact (DigraphFixedpoint.digraph_value_elim fuel seed deps v a IN).
Qed.

Lemma digraph_cl_accum_monotone (fuel : nat) (fuel' : nat) (v : V) (a : A)
  (LE : fuel <= fuel')
  (IN : a ∈ digraph_cl_accum fuel v)
  : a ∈ digraph_cl_accum fuel' v.
Proof.
  exact (DigraphFixedpoint.digraph_value_monotone fuel fuel' seed deps v a LE IN).
Qed.

Lemma digraph_trace_diagraph_cl_accum (v : V) (a : A) (tr : list V) (fuel : nat)
  (TRACE : tr \in digraph_trace v a)
  (LE : length tr <= fuel)
  : a ∈ digraph_cl_accum fuel v.
Proof.
  exact (DigraphFixedpoint.digraph_trace_value seed deps v a tr fuel TRACE LE).
Qed.

Theorem digraph_cl_intro (v : V) (a : A)
  (IN : a \in digraph_cl v)
  : exists fuel, a ∈ digraph_cl_accum fuel v.
Proof.
  exact (DigraphFixedpoint.digraph_closure_intro seed deps v a IN).
Qed.

Theorem digraph_cl_accum_good (fuel : nat) (nodes : fin_ensemble V) (v : V) (a : A)
  (fuel_ENOUGH : length nodes <= fuel)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  : a ∈ digraph_cl_accum fuel v <-> a \in digraph_cl v.
Proof.
  split.
  - exact (digraph_cl_accum_elim fuel v a).
  - exact (DigraphFixedpoint.digraph_closure_intro_bounded fuel nodes seed deps v a fuel_ENOUGH deps_CLOSED).
Qed.

Definition digraph_cl_impl : forall v : V, fin_ensemble A :=
  digraph_cl_accum (length enum_vertices).

Theorem digraph_cl_impl_spec (v : V) (a : A)
  : a ∈ digraph_cl_impl v <-> a \in digraph_cl v.
Proof.
  eapply digraph_cl_accum_good with (nodes := enum_vertices).
  - reflexivity.
  - ii. rewrite in_deps_iff in H. eapply enum_vertices_has_edge_tgt. exact H.
Qed.

Corollary digraph_cl_sim
  : forall v, digraph_cl_impl v =~= digraph_cl v.
Proof.
  i; s!. eapply digraph_cl_impl_spec with (v := v).
Qed.

End DIGRAPH_FIXEDPOINT.

End EXPORT.

Module LabeledFiniteGraph.

Module Edge.

#[universes(template)]
Record t {V : Type} {A : Type} : Type :=
  mk
  { src : V
  ; label : A
  ; dst : V
  }.

#[global] Arguments Edge.t : clear implicits.
#[global] Arguments Edge.mk {V} {A}.

#[global]
Instance hasEqDec {V : Type} {A : Type}
  (V_dec : hasEqDec V)
  (A_dec : hasEqDec A)
  : hasEqDec (Edge.t V A).
Proof.
  red in V_dec, A_dec |- *. decide equality.
Defined.

End Edge.

#[universes(template), projections(primitive)]
Record t {V : Type} {A : Type} : Type :=
  mk
  { V_dec : hasEqDec V
  ; A_dec : hasEqDec A
  ; vertices : fin_ensemble V
  ; edges : fin_ensemble (Edge.t V A)
  ; vertices_NoDup
    : NoDup vertices
  ; edges_NoDup
    : NoDup edges
  ; edges_closed (e : Edge.t V A)
    (EDGE : L.In e edges)
    : L.In e.(Edge.src) vertices /\ L.In e.(Edge.dst) vertices
  ; isVertex (v : V) := L.In v vertices
  ; isLabeledEdge (src : V) (label : A) (dst : V) := L.In (Edge.mk src label dst) edges
  ; isEdge (src : V) (dst : V) := exists label, isLabeledEdge src label dst
  }.

#[global] Arguments LabeledFiniteGraph.t : clear implicits.
#[global] Arguments LabeledFiniteGraph.mk {V} {A}.

Section TH.

Context {V : Type} {A : Type}.

Lemma src_isLabeledEdge (G : LabeledFiniteGraph.t V A) (src : V) (label : A) (dst : V)
  (EDGE : G.(isLabeledEdge) src label dst)
  : G.(isVertex) src.
Proof.
  exact (proj1 (G.(edges_closed) (Edge.mk src label dst) EDGE)).
Qed.

Lemma dst_isLabeledEdge (G : LabeledFiniteGraph.t V A) (src : V) (label : A) (dst : V)
  (EDGE : G.(isLabeledEdge) src label dst)
  : G.(isVertex) dst.
Proof.
  exact (proj2 (G.(edges_closed) (Edge.mk src label dst) EDGE)).
Qed.

Lemma src_isEdge (G : LabeledFiniteGraph.t V A) (src : V) (dst : V)
  (EDGE : G.(isEdge) src dst)
  : G.(isVertex) src.
Proof.
  destruct EDGE as [label EDGE]. eapply src_isLabeledEdge. exact EDGE.
Qed.

Lemma dst_isEdge (G : LabeledFiniteGraph.t V A) (src : V) (dst : V)
  (EDGE : G.(isEdge) src dst)
  : G.(isVertex) dst.
Proof.
  destruct EDGE as [label EDGE]. eapply dst_isLabeledEdge. exact EDGE.
Qed.

Fixpoint labels_raw {V_dec : hasEqDec V} (edges : fin_ensemble (Edge.t V A)) (src : V) (dst : V) : fin_ensemble A :=
  match edges with
  | [] => []
  | edge :: edges' =>
    if @B.decide (src = edge.(Edge.src)) (V_dec src edge.(Edge.src)) then
      if @B.decide (dst = edge.(Edge.dst)) (V_dec dst edge.(Edge.dst)) then
        edge.(Edge.label) :: labels_raw (V_dec := V_dec) edges' src dst
      else
        labels_raw (V_dec := V_dec) edges' src dst
    else
      labels_raw (V_dec := V_dec) edges' src dst
  end.

Lemma in_labels_raw_iff {V_dec : hasEqDec V} (edges : fin_ensemble (Edge.t V A)) (src : V) (dst : V) (label : A)
  : L.In label (labels_raw (V_dec := V_dec) edges src dst) <-> L.In (Edge.mk src label dst) edges.
Proof.
  induction edges as [ | edge edges IH]; simpl.
  - done.
  - destruct edge as [src' label' dst']; simpl. des_ifs; done.
Qed.

Definition labels (G : LabeledFiniteGraph.t V A) (src : V) (dst : V) : fin_ensemble A :=
  L.nodup G.(A_dec) (labels_raw (V_dec := G.(V_dec)) G.(edges) src dst).

Lemma labels_In (G : LabeledFiniteGraph.t V A) (src : V) (dst : V) (label : A)
  : L.In label (labels G src dst) <-> G.(isLabeledEdge) src label dst.
Proof.
  unfold labels, isLabeledEdge. rewrite L.nodup_In. eapply in_labels_raw_iff.
Qed.

Lemma labels_NoDup (G : LabeledFiniteGraph.t V A) (src : V) (dst : V)
  : NoDup (labels G src dst).
Proof.
  unfold labels. eapply L.NoDup_nodup.
Qed.

Fixpoint successors_raw (V_dec : hasEqDec V) (edges : fin_ensemble (Edge.t V A)) (src : V) : fin_ensemble V :=
  match edges with
  | [] => []
  | edge :: edges' =>
    if @B.decide (src = edge.(Edge.src)) (V_dec src edge.(Edge.src)) then
      edge.(Edge.dst) :: successors_raw V_dec edges' src
    else
      successors_raw V_dec edges' src
  end.

Lemma successors_raw_In (V_dec : hasEqDec V) (edges : fin_ensemble (Edge.t V A)) (src : V) (dst : V)
  : L.In dst (successors_raw V_dec edges src) <-> (exists label, L.In (Edge.mk src label dst) edges).
Proof.
  induction edges as [ | edge edges IH]; simpl.
  - done.
  - destruct edge as [src' label' dst']; simpl. des_ifs; done.
Qed.

Definition successors (G : LabeledFiniteGraph.t V A) (src : V) : fin_ensemble V :=
  L.nodup G.(V_dec) (successors_raw G.(V_dec) G.(edges) src).

Lemma successors_In (G : LabeledFiniteGraph.t V A) (src : V) (dst : V)
  : L.In dst (successors G src) <-> G.(isEdge) src dst.
Proof.
  unfold successors, isEdge. rewrite L.nodup_In. eapply successors_raw_In.
Qed.

Lemma successors_NoDup (G : LabeledFiniteGraph.t V A) (src : V)
  : NoDup (successors G src).
Proof.
  unfold successors. eapply L.NoDup_nodup.
Qed.

Fixpoint predecessors_raw (V_dec : hasEqDec V) (edges : fin_ensemble (Edge.t V A)) (dst : V) : fin_ensemble V :=
  match edges with
  | [] => []
  | edge :: edges' =>
    if @B.decide (dst = edge.(Edge.dst)) (V_dec dst edge.(Edge.dst)) then
      edge.(Edge.src) :: predecessors_raw V_dec edges' dst
    else
      predecessors_raw V_dec edges' dst
  end.

Lemma predecessors_raw_In (V_dec : hasEqDec V) (edges : fin_ensemble (Edge.t V A)) (src : V) (dst : V)
  : L.In src (predecessors_raw V_dec edges dst) <-> (exists label, L.In (Edge.mk src label dst) edges).
Proof.
  induction edges as [ | edge edges IH]; simpl.
  - done.
  - destruct edge as [src' label' dst']; simpl. des_ifs; done.
Qed.

Definition predecessors (G : LabeledFiniteGraph.t V A) (dst : V) : fin_ensemble V :=
  L.nodup G.(V_dec) (predecessors_raw G.(V_dec) G.(edges) dst).

Lemma predecessors_In (G : LabeledFiniteGraph.t V A) (src : V) (dst : V)
  : L.In src (predecessors G dst) <-> G.(isEdge) src dst.
Proof.
  unfold predecessors, isEdge. rewrite L.nodup_In. eapply predecessors_raw_In.
Qed.

Lemma predecessors_NoDup (G : LabeledFiniteGraph.t V A) (dst : V)
  : NoDup (predecessors G dst).
Proof.
  unfold predecessors. eapply L.NoDup_nodup.
Qed.

Fixpoint successors_by_label_raw (V_dec : hasEqDec V) (A_dec : hasEqDec A) (edges : fin_ensemble (Edge.t V A)) (label : A) (src : V) : fin_ensemble V :=
  match edges with
  | [] => []
  | edge :: edges' =>
    if @B.decide (src = edge.(Edge.src)) (V_dec src edge.(Edge.src)) then
      if @B.decide (label = edge.(Edge.label)) (A_dec label edge.(Edge.label)) then
        edge.(Edge.dst) :: successors_by_label_raw V_dec A_dec edges' label src
      else
        successors_by_label_raw V_dec A_dec edges' label src
    else
      successors_by_label_raw V_dec A_dec edges' label src
  end.

Lemma successors_by_label_raw_In (V_dec : hasEqDec V) (A_dec : hasEqDec A) (edges : fin_ensemble (Edge.t V A)) (src : V) (label : A) (dst : V)
  : L.In dst (successors_by_label_raw V_dec A_dec edges label src) <-> L.In (Edge.mk src label dst) edges.
Proof.
  induction edges as [ | edge edges IH]; simpl.
  - done.
  - destruct edge as [src' label' dst']; simpl. des_ifs; done.
Qed.

Definition successors_by_label (G : LabeledFiniteGraph.t V A) (label : A) (src : V) : fin_ensemble V :=
  L.nodup G.(V_dec) (successors_by_label_raw G.(V_dec) G.(A_dec) G.(edges) label src).

Lemma successors_by_label_In (G : LabeledFiniteGraph.t V A) (src : V) (label : A) (dst : V)
  : L.In dst (successors_by_label G label src) <-> G.(isLabeledEdge) src label dst.
Proof.
  unfold successors_by_label, isLabeledEdge. rewrite L.nodup_In. eapply successors_by_label_raw_In.
Qed.

Lemma successors_by_label_NoDup (G : LabeledFiniteGraph.t V A) (label : A) (src : V)
  : NoDup (successors_by_label G label src).
Proof.
  unfold successors_by_label. eapply L.NoDup_nodup.
Qed.

Fixpoint predecessors_by_label_raw (V_dec : hasEqDec V) (A_dec : hasEqDec A) (edges : fin_ensemble (Edge.t V A)) (label : A) (dst : V) : fin_ensemble V :=
  match edges with
  | [] => []
  | edge :: edges' =>
    if @B.decide (dst = edge.(Edge.dst)) (V_dec dst edge.(Edge.dst)) then
      if @B.decide (label = edge.(Edge.label)) (A_dec label edge.(Edge.label)) then
        edge.(Edge.src) :: predecessors_by_label_raw V_dec A_dec edges' label dst
      else
        predecessors_by_label_raw V_dec A_dec edges' label dst
    else
      predecessors_by_label_raw V_dec A_dec edges' label dst
  end.

Lemma predecessors_by_label_raw_In (V_dec : hasEqDec V) (A_dec : hasEqDec A) (edges : fin_ensemble (Edge.t V A)) (src : V) (label : A) (dst : V)
  : L.In src (predecessors_by_label_raw V_dec A_dec edges label dst) <-> L.In (Edge.mk src label dst) edges.
Proof.
  induction edges as [ | edge edges IH]; simpl.
  - done.
  - destruct edge as [src' label' dst']; simpl. des_ifs; done.
Qed.

Definition predecessors_by_label (G : LabeledFiniteGraph.t V A) (label : A) (dst : V) : fin_ensemble V :=
  L.nodup G.(V_dec) (predecessors_by_label_raw G.(V_dec) G.(A_dec) G.(edges) label dst).

Lemma predecessors_by_label_In (G : LabeledFiniteGraph.t V A) (src : V) (label : A) (dst : V)
  : L.In src (predecessors_by_label G label dst) <-> G.(isLabeledEdge) src label dst.
Proof.
  unfold predecessors_by_label, isLabeledEdge. rewrite L.nodup_In. eapply predecessors_by_label_raw_In.
Qed.

Lemma predecessors_by_label_NoDup (G : LabeledFiniteGraph.t V A) (label : A) (dst : V)
  : NoDup (predecessors_by_label G label dst).
Proof.
  unfold predecessors_by_label. eapply L.NoDup_nodup.
Qed.

Definition closed (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A)) : Prop :=
  forall edge, L.In edge edges -> (L.In edge.(Edge.src) vertices /\ L.In edge.(Edge.dst) vertices).

Definition edge_closedb (V_dec : hasEqDec V) (vertices : fin_ensemble V) (edge : Edge.t V A) : bool :=
  mem (EQ_DEC := V_dec) edge.(Edge.src) vertices && mem (EQ_DEC := V_dec) edge.(Edge.dst) vertices.

Lemma edge_closedb_true_iff (V_dec : hasEqDec V) (vertices : fin_ensemble V) (edge : Edge.t V A)
  : edge_closedb V_dec vertices edge = true <-> (L.In edge.(Edge.src) vertices /\ L.In edge.(Edge.dst) vertices).
Proof.
  unfold edge_closedb. rewrite andb_true_iff. rewrite !mem_spec. reflexivity.
Qed.

Definition closedb (V_dec : hasEqDec V) (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A)) : bool :=
  L.forallb (edge_closedb V_dec vertices) edges.

Lemma closedb_true_iff (V_dec : hasEqDec V) (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A))
  : closedb V_dec vertices edges = true <-> closed vertices edges.
Proof.
  unfold closedb, closed. rewrite L.forallb_forall. split.
  - intros CLOSED edge EDGE. specialize (CLOSED edge EDGE).
    now rewrite edge_closedb_true_iff in CLOSED.
  - intros CLOSED edge EDGE. rewrite edge_closedb_true_iff.
    now eapply CLOSED.
Qed.

#[refine]
Definition build_closed (V_dec : hasEqDec V) (A_dec : hasEqDec A) (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A)) (CLOSED : closed vertices edges) : t V A :=
  {|
    V_dec := V_dec;
    A_dec := A_dec;
    vertices := L.nodup V_dec vertices;
    edges := L.nodup (Edge.hasEqDec V_dec A_dec) edges;
  |}.
Proof.
  - eapply L.NoDup_nodup.
  - eapply L.NoDup_nodup.
  - intros edge EDGE. rewrite L.nodup_In in EDGE.
    pose proof (CLOSED edge EDGE) as [SRC DST].
    split; rewrite L.nodup_In; assumption.
Defined.

Lemma build_closed_isVertex (V_dec : hasEqDec V) (A_dec : hasEqDec A) (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A))
  (CLOSED : closed vertices edges)
  : forall v, (build_closed V_dec A_dec vertices edges CLOSED).(isVertex) v <-> L.In v vertices.
Proof.
  intros v. unfold isVertex, build_closed. simpl. rewrite L.nodup_In. reflexivity.
Qed.

Lemma build_closed_isLabeledEdge (V_dec : hasEqDec V) (A_dec : hasEqDec A) (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A))
  (CLOSED : closed vertices edges)
  (src : V) (label : A) (dst : V)
  : (build_closed V_dec A_dec vertices edges CLOSED).(isLabeledEdge) src label dst <-> L.In (Edge.mk src label dst) edges.
Proof.
  unfold isLabeledEdge, build_closed. simpl. rewrite L.nodup_In. reflexivity.
Qed.

Lemma build_closed_isEdge (V_dec : hasEqDec V) (A_dec : hasEqDec A) (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A))
  (CLOSED : closed vertices edges)
  (src : V) (dst : V)
  : (build_closed V_dec A_dec vertices edges CLOSED).(isEdge) src dst <-> (exists label, L.In (Edge.mk src label dst) edges).
Proof.
  unfold isEdge. setoid_rewrite build_closed_isLabeledEdge. reflexivity.
Qed.

Definition edge_vertices (edges : fin_ensemble (Edge.t V A)) : fin_ensemble V :=
  L.flat_map (fun edge => [edge.(Edge.src); edge.(Edge.dst)]) edges.

Lemma edge_vertices_In (edges : fin_ensemble (Edge.t V A)) (v : V)
  : L.In v (edge_vertices edges) <-> (exists edge, L.In edge edges /\ (v = edge.(Edge.src) \/ v = edge.(Edge.dst))).
Proof.
  unfold edge_vertices. rewrite L.in_flat_map. split.
  - intros [edge [EDGE IN]]. exists edge. split; [exact EDGE | ].
    simpl in IN. destruct IN as [SRC | [DST | []]]; [left | right]; symmetry; assumption.
  - intros [edge [EDGE [SRC | DST]]].
    + exists edge. split; [exact EDGE | simpl; left; symmetry; exact SRC].
    + exists edge. split; [exact EDGE | simpl; right; left; symmetry; exact DST].
Qed.

Lemma span_closed (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A))
  : closed (vertices ++ edge_vertices edges) edges.
Proof.
  intros edge EDGE. split.
  - rewrite L.in_app_iff. right. rewrite edge_vertices_In.
    exists edge. split; [exact EDGE | left; reflexivity].
  - rewrite L.in_app_iff. right. rewrite edge_vertices_In.
    exists edge. split; [exact EDGE | right; reflexivity].
Qed.

Definition span (V_dec : hasEqDec V) (A_dec : hasEqDec A) (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A)) : t V A :=
  build_closed V_dec A_dec (vertices ++ edge_vertices edges) edges (span_closed vertices edges).

Lemma span_isVertex (V_dec : hasEqDec V) (A_dec : hasEqDec A) (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A)) (v : V)
  : (span V_dec A_dec vertices edges).(isVertex) v <-> (L.In v vertices \/ exists edge, L.In edge edges /\ (v = edge.(Edge.src) \/ v = edge.(Edge.dst))).
Proof.
  unfold span. rewrite build_closed_isVertex. rewrite L.in_app_iff, edge_vertices_In. reflexivity.
Qed.

Lemma span_isLabeledEdge (V_dec : hasEqDec V) (A_dec : hasEqDec A) (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A)) (src : V) (label : A) (dst : V)
  : (span V_dec A_dec vertices edges).(isLabeledEdge) src label dst <-> L.In (Edge.mk src label dst) edges.
Proof.
  unfold span. eapply build_closed_isLabeledEdge.
Qed.

Definition build (V_dec : hasEqDec V) (A_dec : hasEqDec A) (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A)) : option (t V A) :=
  let ok := closedb V_dec vertices edges in
  match @B.decide (ok = true) (bool_hasEqDec ok true) with
  | left OK =>
    Some (build_closed V_dec A_dec vertices edges (proj1 (closedb_true_iff V_dec vertices edges) OK))
  | right _ => None
  end.

Lemma build_some_closed (V_dec : hasEqDec V) (A_dec : hasEqDec A) (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A)) (G : LabeledFiniteGraph.t V A)
  (BUILD : build V_dec A_dec vertices edges = Some G)
  : closed vertices edges.
Proof.
  unfold build in BUILD.
  destruct (@B.decide (closedb V_dec vertices edges = true) (bool_hasEqDec (closedb V_dec vertices edges) true)) as [CLOSED | NOT_CLOSED].
  - eapply (proj1 (closedb_true_iff V_dec vertices edges)). exact CLOSED.
  - discriminate.
Qed.

Lemma build_complete (V_dec : hasEqDec V) (A_dec : hasEqDec A) (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A))
  (CLOSED : closed vertices edges)
  : exists G, build V_dec A_dec vertices edges = Some G.
Proof.
  unfold build.
  assert (CHECK : closedb V_dec vertices edges = true).
  { now rewrite closedb_true_iff. }
  destruct (@B.decide (closedb V_dec vertices edges = true) (bool_hasEqDec (closedb V_dec vertices edges) true)) as [YES | NO].
  - eexists. reflexivity.
  - contradiction.
Qed.

Lemma build_isSome_iff (V_dec : hasEqDec V) (A_dec : hasEqDec A) (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A))
  : (exists G, build V_dec A_dec vertices edges = Some G) <-> closed vertices edges.
Proof.
  split.
  - intros [G BUILD]. exact (build_some_closed V_dec A_dec vertices edges G BUILD).
  - intros CLOSED. exact (build_complete V_dec A_dec vertices edges CLOSED).
Qed.

Lemma build_some_isVertex (V_dec : hasEqDec V) (A_dec : hasEqDec A) (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A)) (G : LabeledFiniteGraph.t V A)
  (BUILD : build V_dec A_dec vertices edges = Some G)
  (v : V)
  : G.(isVertex) v <-> L.In v vertices.
Proof.
  unfold build in BUILD.
  destruct (@B.decide (closedb V_dec vertices edges = true) (bool_hasEqDec (closedb V_dec vertices edges) true)) as [CLOSED | NOT_CLOSED].
  - inv BUILD. eapply build_closed_isVertex.
  - discriminate.
Qed.

Lemma build_some_isLabeledEdge (V_dec : hasEqDec V) (A_dec : hasEqDec A) (vertices : fin_ensemble V) (edges : fin_ensemble (Edge.t V A)) (G : LabeledFiniteGraph.t V A)
  (BUILD : build V_dec A_dec vertices edges = Some G)
  (src : V) (label : A) (dst : V)
  : G.(isLabeledEdge) src label dst <-> L.In (Edge.mk src label dst) edges.
Proof.
  unfold build in BUILD.
  destruct (@B.decide (closedb V_dec vertices edges = true) (bool_hasEqDec (closedb V_dec vertices edges) true)) as [CLOSED | NOT_CLOSED].
  - inv BUILD. eapply build_closed_isLabeledEdge.
  - discriminate.
Qed.

Inductive walk (G : LabeledFiniteGraph.t V A) : V -> list A -> list V -> V -> Prop :=
  | walk_nil v
    (VERTEX : G.(isVertex) v)
    : walk G v [] [] v
  | walk_cons src label mid word trace dst
    (EDGE : G.(isLabeledEdge) src label mid)
    (REST : walk G mid word trace dst)
    : walk G src (label :: word) (mid :: trace) dst.

Lemma walk_app (G : LabeledFiniteGraph.t V A) (src : V) (mid : V) (dst : V) (word1 : list A) (word2 : list A) (trace1 : list V) (trace2 : list V)
  (WALK1 : walk G src word1 trace1 mid)
  (WALK2 : walk G mid word2 trace2 dst)
  : walk G src (word1 ++ word2) (trace1 ++ trace2) dst.
Proof.
  induction WALK1 as [v VERTEX | src label next word trace mid EDGE REST IH].
  - simpl. exact WALK2.
  - simpl. econstructor 2; eauto.
Qed.

Lemma walk_source (G : LabeledFiniteGraph.t V A) (src : V) (word : list A) (trace : list V) (dst : V)
  (WALK : walk G src word trace dst)
  : G.(isVertex) src.
Proof.
  induction WALK as [v VERTEX | src label mid word trace dst EDGE REST IH].
  - exact VERTEX.
  - exact (src_isLabeledEdge G src label mid EDGE).
Qed.

Lemma walk_target (G : LabeledFiniteGraph.t V A) (src : V) (word : list A) (trace : list V) (dst : V)
  (WALK : walk G src word trace dst)
  : G.(isVertex) dst.
Proof.
  induction WALK as [v VERTEX | src label mid word trace dst EDGE REST IH].
  - exact VERTEX.
  - exact IH.
Qed.

Lemma walk_length (G : LabeledFiniteGraph.t V A) (src : V) (word : list A) (trace : list V) (dst : V)
  (WALK : walk G src word trace dst)
  : L.length trace = L.length word.
Proof.
  induction WALK as [v VERTEX | src label mid word trace dst EDGE REST IH]; simpl; congruence.
Qed.

Definition word_walk (G : LabeledFiniteGraph.t V A) (src : V) (word : list A) (dst : V) : Prop :=
  exists trace, walk G src word trace dst.

Definition dataflow {D : Type} `{D_hasEqDec : hasEqDec D} (G : LabeledFiniteGraph.t V A) (seed : V -> fin_ensemble D) (node : V) : fin_ensemble D :=
  DigraphFixedpoint.digraph_value (length G.(vertices)) seed (successors G) node.

Definition dataflow_closure {D : Type} (G : LabeledFiniteGraph.t V A) (seed : V -> fin_ensemble D) (value : D) (node : V) : Prop :=
  DigraphFixedpoint.digraph_closure seed (successors G) value node.

Lemma successors_isVertex (G : LabeledFiniteGraph.t V A) (src : V) (dst : V)
  (IN : L.In dst (successors G src))
  : G.(isVertex) dst.
Proof.
  apply successors_In in IN. exact (dst_isEdge G src dst IN).
Qed.

Lemma dataflow_sound {D : Type} `{D_hasEqDec : hasEqDec D} (G : LabeledFiniteGraph.t V A) (seed : V -> fin_ensemble D) (node : V) (value : D)
  (IN : L.In value (dataflow G seed node))
  : dataflow_closure G seed value node.
Proof.
  unfold dataflow in IN. unfold dataflow_closure.
  exact (@DigraphFixedpoint.digraph_value_elim V D D_hasEqDec (length G.(vertices)) seed (successors G) node value IN).
Qed.

Lemma dataflow_complete {D : Type} `{D_hasEqDec : hasEqDec D} (G : LabeledFiniteGraph.t V A) (seed : V -> fin_ensemble D) (node : V) (value : D)
  (CLOSURE : dataflow_closure G seed value node)
  : L.In value (dataflow G seed node).
Proof.
  unfold dataflow. unfold dataflow_closure in CLOSURE.
  refine (@DigraphFixedpoint.digraph_closure_intro_bounded V D D_hasEqDec G.(V_dec) (length G.(vertices)) G.(vertices) seed (successors G) node value _ _ CLOSURE).
  - lia.
  - intros src dst EDGE. unfold isVertex.
    exact (successors_isVertex G src dst EDGE).
Qed.

Theorem dataflow_In {D : Type} `{D_hasEqDec : hasEqDec D} (G : LabeledFiniteGraph.t V A) (seed : V -> fin_ensemble D) (node : V) (value : D)
  : L.In value (dataflow G seed node) <-> dataflow_closure G seed value node.
Proof.
  split.
  - eapply dataflow_sound.
  - eapply dataflow_complete.
Qed.

Definition dataflow_walk {D : Type} (G : LabeledFiniteGraph.t V A) (seed : V -> fin_ensemble D) (value : D) (node : V) : Prop :=
  exists target word trace, walk G node word trace target /\ L.In value (seed target).

Lemma dataflow_closure_walk_sound {D : Type} (G : LabeledFiniteGraph.t V A) (seed : V -> fin_ensemble D) (node : V) (value : D)
  (NODE : G.(isVertex) node)
  (CLOSURE : dataflow_closure G seed value node)
  : dataflow_walk G seed value node.
Proof.
  unfold dataflow_closure in CLOSURE. revert NODE.
  induction CLOSURE as [node IN | node dependency EDGE CLOSURE IH]; intros NODE.
  - exists node, [], []. split.
    + econstructor 1. exact NODE.
    + exact IN.
  - apply successors_In in EDGE. destruct EDGE as [label EDGE].
    destruct (IH (dst_isLabeledEdge G node label dependency EDGE)) as (target & word & trace & WALK & SEED).
    exists target, (label :: word), (dependency :: trace). split.
    + econstructor 2; eauto.
    + exact SEED.
Qed.

Lemma dataflow_walk_closure {D : Type} (G : LabeledFiniteGraph.t V A) (seed : V -> fin_ensemble D) (node : V) (value : D)
  (WITNESS : dataflow_walk G seed value node)
  : dataflow_closure G seed value node.
Proof.
  destruct WITNESS as (target & word & trace & WALK & SEED).
  unfold dataflow_closure. revert value SEED.
  induction WALK as [node NODE | node label dependency word trace target EDGE WALK IH]; intros value SEED.
  - now eapply DigraphFixedpoint.digraph_closure_seed.
  - eapply DigraphFixedpoint.digraph_closure_step with (y := dependency).
    + apply successors_In. exists label. exact EDGE.
    + now eapply IH.
Qed.

Theorem dataflow_closure_iff_walk {D : Type} (G : LabeledFiniteGraph.t V A) (seed : V -> fin_ensemble D) (node : V) (value : D)
  (NODE : G.(isVertex) node)
  : dataflow_closure G seed value node <-> dataflow_walk G seed value node.
Proof.
  split.
  - intros CLOSURE.
    exact (dataflow_closure_walk_sound G seed node value NODE CLOSURE).
  - eapply dataflow_walk_closure.
Qed.

Theorem dataflow_In_iff_walk {D : Type} `{D_hasEqDec : hasEqDec D} (G : LabeledFiniteGraph.t V A) (seed : V -> fin_ensemble D) (node : V) (value : D)
  (NODE : G.(isVertex) node)
  : L.In value (dataflow G seed node) <-> dataflow_walk G seed value node.
Proof.
  rewrite dataflow_In.
  exact (dataflow_closure_iff_walk G seed node value NODE).
Qed.

Definition deterministic (G : LabeledFiniteGraph.t V A) : Prop :=
  forall src label dst1 dst2, G.(isLabeledEdge) src label dst1 -> G.(isLabeledEdge) src label dst2 -> dst1 = dst2.

#[projections(primitive)]
Record PartialDeterministic (V : Type) (A : Type) : Type :=
  mkPartialDeterministic
  { graph : t V A
  ; step : V -> A -> option V
  ; step_spec src label dst
    : step src label = Some dst <-> graph.(isLabeledEdge) src label dst
  }.

#[global] Arguments mkPartialDeterministic {V A} graph step step_spec.
#[global] Arguments graph {V A} _.
#[global] Arguments step {V A} _ src label.
#[global] Arguments step_spec {V A} _ src label dst.

Lemma PartialDeterministic_deterministic (D : PartialDeterministic V A)
  : deterministic D.(graph).
Proof.
  intros src label dst1 dst2 EDGE1 EDGE2.
  pose proof (proj2 (D.(step_spec) src label dst1) EDGE1) as STEP1.
  pose proof (proj2 (D.(step_spec) src label dst2) EDGE2) as STEP2.
  congruence.
Qed.

Fixpoint run_word (D : PartialDeterministic V A) (src : V) (word : list A) {struct word} : option V :=
  match word with
  | [] =>
    if L.in_dec D.(graph).(V_dec) src D.(graph).(vertices) then
      Some src
    else
      None
  | label :: word' =>
    match D.(step) src label with
    | Some dst => run_word D dst word'
    | None => None
    end
  end.

Lemma run_word_sound (D : PartialDeterministic V A) (src : V) (word : list A) (dst : V)
  (RUN : run_word D src word = Some dst)
  : word_walk D.(graph) src word dst.
Proof.
  revert src dst RUN. induction word as [ | label word IH]; intros src dst RUN.
  - simpl in RUN. destruct (L.in_dec D.(graph).(V_dec) src D.(graph).(vertices)) as [VERTEX | NOT_VERTEX].
    + inv RUN. exists []. econstructor 1. exact VERTEX.
    + discriminate.
  - simpl in RUN. destruct (D.(step) src label) as [mid | ] eqn: STEP; [ | discriminate].
    specialize (IH mid dst RUN) as [trace WALK].
    exists (mid :: trace). econstructor 2.
    + eapply (proj1 (D.(step_spec) src label mid)). exact STEP.
    + exact WALK.
Qed.

Lemma run_word_complete (D : PartialDeterministic V A) (src : V) (word : list A) (trace : list V) (dst : V)
  (WALK : walk D.(graph) src word trace dst)
  : run_word D src word = Some dst.
Proof.
  induction WALK as [v VERTEX | src label mid word trace dst EDGE REST IH].
  - simpl. destruct (L.in_dec D.(graph).(V_dec) v D.(graph).(vertices)) as [YES | NO].
    + reflexivity.
    + contradiction.
  - simpl. pose proof (proj2 (D.(step_spec) src label mid) EDGE) as STEP.
    rewrite STEP. exact IH.
Qed.

Theorem run_word_spec (D : PartialDeterministic V A) (src : V) (word : list A) (dst : V)
  : run_word D src word = Some dst <-> word_walk D.(graph) src word dst.
Proof.
  split.
  - eapply run_word_sound.
  - intros [trace WALK]. exact (run_word_complete D src word trace dst WALK).
Qed.

#[refine]
Definition filter_edges (G : LabeledFiniteGraph.t V A) (keep : Edge.t V A -> bool) : t V A :=
  {|
    V_dec := G.(V_dec);
    A_dec := G.(A_dec);
    vertices := G.(vertices);
    edges := L.filter keep G.(edges);
  |}.
Proof.
  - exact G.(vertices_NoDup).
  - eapply L.NoDup_filter. exact G.(edges_NoDup).
  - intros edge EDGE. rewrite L.filter_In in EDGE. destruct EDGE as [EDGE _].
    exact (G.(edges_closed) edge EDGE).
Defined.

Lemma filter_edges_isVertex (G : LabeledFiniteGraph.t V A) (keep : Edge.t V A -> bool) (v : V)
  : (filter_edges G keep).(isVertex) v <-> G.(isVertex) v.
Proof.
  reflexivity.
Qed.

Lemma filter_edges_isLabeledEdge (G : LabeledFiniteGraph.t V A) (keep : Edge.t V A -> bool) (src : V) (label : A) (dst : V)
  : (filter_edges G keep).(isLabeledEdge) src label dst <-> (G.(isLabeledEdge) src label dst /\ keep (Edge.mk src label dst) = true).
Proof.
  unfold isLabeledEdge, filter_edges. simpl. rewrite L.filter_In. reflexivity.
Qed.

Lemma filter_edges_isEdge (G : LabeledFiniteGraph.t V A) (keep : Edge.t V A -> bool) (src : V) (dst : V)
  : (filter_edges G keep).(isEdge) src dst <-> (exists label, G.(isLabeledEdge) src label dst /\ keep (Edge.mk src label dst) = true).
Proof.
  unfold isEdge. setoid_rewrite filter_edges_isLabeledEdge. reflexivity.
Qed.

Definition filter_labels (G : LabeledFiniteGraph.t V A) (keep : A -> bool) : t V A :=
  filter_edges G (fun edge => keep edge.(Edge.label)).

Lemma filter_labels_isVertex (G : LabeledFiniteGraph.t V A) (keep : A -> bool) (v : V)
  : (filter_labels G keep).(isVertex) v <-> G.(isVertex) v.
Proof.
  unfold filter_labels. eapply filter_edges_isVertex.
Qed.

Lemma filter_labels_isLabeledEdge (G : LabeledFiniteGraph.t V A) (keep : A -> bool) (src : V) (label : A) (dst : V)
  : (filter_labels G keep).(isLabeledEdge) src label dst <-> (G.(isLabeledEdge) src label dst /\ keep label = true).
Proof.
  unfold filter_labels. rewrite filter_edges_isLabeledEdge. simpl. reflexivity.
Qed.

Lemma filter_labels_isEdge (G : LabeledFiniteGraph.t V A) (keep : A -> bool) (src : V) (dst : V)
  : (filter_labels G keep).(isEdge) src dst <-> (exists label, G.(isLabeledEdge) src label dst /\ keep label = true).
Proof.
  unfold isEdge. setoid_rewrite filter_labels_isLabeledEdge. reflexivity.
Qed.

Definition reverse_edge (edge : Edge.t V A) : Edge.t V A :=
  Edge.mk edge.(Edge.dst) edge.(Edge.label) edge.(Edge.src).

Lemma reverse_edge_involutive (edge : Edge.t V A)
  : reverse_edge (reverse_edge edge) = edge.
Proof.
  destruct edge. reflexivity.
Qed.

Lemma reverse_edge_injective (edge1 : Edge.t V A) (edge2 : Edge.t V A)
  (EQ : reverse_edge edge1 = reverse_edge edge2)
  : edge1 = edge2.
Proof.
  rewrite <- (reverse_edge_involutive edge1), <- (reverse_edge_involutive edge2).
  now rewrite EQ.
Qed.

#[refine]
Definition reverse (G : LabeledFiniteGraph.t V A) : t V A :=
  {|
    V_dec := G.(V_dec);
    A_dec := G.(A_dec);
    vertices := G.(vertices);
    edges := L.map reverse_edge G.(edges);
  |}.
Proof.
  - exact G.(vertices_NoDup).
  - eapply L.NoDup_map_injective_on.
    + intros edge1 edge2 _ _ EQ. now eapply reverse_edge_injective.
    + exact G.(edges_NoDup).
  - intros edge EDGE. rewrite L.in_map_iff in EDGE.
    destruct EDGE as [original [EQ EDGE]]. subst edge.
    pose proof (G.(edges_closed) original EDGE) as [SRC DST].
    unfold reverse_edge. simpl. split; assumption.
Defined.

Lemma reverse_isVertex (G : LabeledFiniteGraph.t V A) (v : V)
  : (reverse G).(isVertex) v <-> G.(isVertex) v.
Proof.
  reflexivity.
Qed.

Lemma reverse_isLabeledEdge (G : LabeledFiniteGraph.t V A) (src : V) (label : A) (dst : V)
  : (reverse G).(isLabeledEdge) src label dst <-> G.(isLabeledEdge) dst label src.
Proof.
  unfold reverse, isLabeledEdge. simpl. rewrite L.in_map_iff. split.
  - intros [original [EQ EDGE]]. destruct original as [src' label' dst']. simpl in EQ. inv EQ.
    exact EDGE.
  - intros EDGE. exists (Edge.mk dst label src). split; [reflexivity | exact EDGE].
Qed.

Lemma reverse_isEdge (G : LabeledFiniteGraph.t V A) (src : V) (dst : V)
  : (reverse G).(isEdge) src dst <-> G.(isEdge) dst src.
Proof.
  unfold isEdge. setoid_rewrite reverse_isLabeledEdge. reflexivity.
Qed.

Definition retained_edge (keep : V -> bool) (edge : Edge.t V A) : bool :=
  keep edge.(Edge.src) && keep edge.(Edge.dst).

#[refine]
Definition induced (G : LabeledFiniteGraph.t V A) (keep : V -> bool) : t V A :=
  {|
    V_dec := G.(V_dec);
    A_dec := G.(A_dec);
    vertices := L.filter keep G.(vertices);
    edges := L.filter (retained_edge keep) G.(edges);
  |}.
Proof.
  - eapply L.NoDup_filter. exact G.(vertices_NoDup).
  - eapply L.NoDup_filter. exact G.(edges_NoDup).
  - intros edge EDGE. rewrite L.filter_In in EDGE. destruct EDGE as [EDGE KEEP].
    unfold retained_edge in KEEP. rewrite andb_true_iff in KEEP. destruct KEEP as [SRC_KEEP DST_KEEP].
    pose proof (G.(edges_closed) edge EDGE) as [SRC DST]. split; rewrite L.filter_In; split; assumption.
Defined.

Lemma induced_isVertex (G : LabeledFiniteGraph.t V A) (keep : V -> bool) (v : V)
  : (induced G keep).(isVertex) v <-> (G.(isVertex) v /\ keep v = true).
Proof.
  unfold isVertex, induced. simpl. rewrite L.filter_In. reflexivity.
Qed.

Lemma induced_isLabeledEdge (G : LabeledFiniteGraph.t V A) (keep : V -> bool) (src : V) (label : A) (dst : V)
  : (induced G keep).(isLabeledEdge) src label dst <-> (G.(isLabeledEdge) src label dst /\ keep src = true /\ keep dst = true).
Proof.
  unfold isLabeledEdge, induced. simpl. rewrite L.filter_In.
  unfold retained_edge. simpl. rewrite andb_true_iff. tauto.
Qed.

Lemma induced_isEdge (G : LabeledFiniteGraph.t V A) (keep : V -> bool) (src : V) (dst : V)
  : (induced G keep).(isEdge) src dst <-> (G.(isEdge) src dst /\ keep src = true /\ keep dst = true).
Proof.
  unfold isEdge. setoid_rewrite induced_isLabeledEdge. firstorder.
Qed.

End TH.

Definition map_edge {V : Type} {W : Type} {A : Type} (f : V -> W) (edge : Edge.t V A) : Edge.t W A :=
  Edge.mk (f edge.(Edge.src)) edge.(Edge.label) (f edge.(Edge.dst)).

Lemma map_vertices_closed {V : Type} {W : Type} {A : Type} (f : V -> W) (G : LabeledFiniteGraph.t V A)
  : closed (L.map f G.(vertices)) (L.map (map_edge f) G.(edges)).
Proof.
  intros mapped_edge MAPPED_EDGE. rewrite L.in_map_iff in MAPPED_EDGE.
  destruct MAPPED_EDGE as [original_edge [EQ EDGE]]. subst mapped_edge.
  pose proof (G.(edges_closed) original_edge EDGE) as [SRC DST].
  split; rewrite L.in_map_iff.
  - exists original_edge.(Edge.src). split; [reflexivity | exact SRC].
  - exists original_edge.(Edge.dst). split; [reflexivity | exact DST].
Qed.

Definition map_vertices {V : Type} {W : Type} {A : Type} (W_dec : hasEqDec W) (f : V -> W) (G : LabeledFiniteGraph.t V A) : t W A :=
  build_closed W_dec G.(A_dec) (L.map f G.(vertices)) (L.map (map_edge f) G.(edges)) (map_vertices_closed f G).

Lemma map_vertices_isVertex {V : Type} {W : Type} {A : Type} (W_dec : hasEqDec W) (f : V -> W) (G : LabeledFiniteGraph.t V A) (w : W)
  : (map_vertices W_dec f G).(isVertex) w <-> (exists v, G.(isVertex) v /\ f v = w).
Proof.
  unfold map_vertices. rewrite build_closed_isVertex, L.in_map_iff. split.
  - intros [v [EQ IN]]. exists v. split; assumption.
  - intros [v [IN EQ]]. exists v. split; assumption.
Qed.

Lemma map_vertices_atomic_edge_In {V : Type} {W : Type} {A : Type} (W_dec : hasEqDec W) (f : V -> W) (G : LabeledFiniteGraph.t V A) (mapped_edge : Edge.t W A)
  : L.In mapped_edge (map_vertices W_dec f G).(edges) <-> (exists original_edge, L.In original_edge G.(edges) /\ map_edge f original_edge = mapped_edge).
Proof.
  unfold map_vertices, build_closed. simpl. rewrite L.nodup_In, L.in_map_iff. split.
  - intros [original_edge [EQ EDGE]]. exists original_edge. split; assumption.
  - intros [original_edge [EDGE EQ]]. exists original_edge. split; assumption.
Qed.

Lemma map_vertices_isLabeledEdge {V : Type} {W : Type} {A : Type} (W_dec : hasEqDec W) (f : V -> W) (G : LabeledFiniteGraph.t V A) (mapped_src : W) (label : A) (mapped_dst : W)
  : (map_vertices W_dec f G).(isLabeledEdge) mapped_src label mapped_dst <-> (exists src dst, G.(isLabeledEdge) src label dst /\ f src = mapped_src /\ f dst = mapped_dst).
Proof.
  unfold isLabeledEdge. rewrite map_vertices_atomic_edge_In. split.
  - intros [original_edge [EDGE EQ]]. destruct original_edge as [src label' dst].
    unfold map_edge in EQ. simpl in EQ. inv EQ.
    exists src, dst. split; [exact EDGE | split; reflexivity].
  - intros [src [dst [EDGE [SRC DST]]]].
    exists (Edge.mk src label dst). split; [exact EDGE | ].
    unfold map_edge. simpl. congruence.
Qed.

Lemma map_vertices_isEdge {V : Type} {W : Type} {A : Type} (W_dec : hasEqDec W) (f : V -> W) (G : LabeledFiniteGraph.t V A) (mapped_src : W) (mapped_dst : W)
  : (map_vertices W_dec f G).(isEdge) mapped_src mapped_dst <-> (exists src dst, G.(isEdge) src dst /\ f src = mapped_src /\ f dst = mapped_dst).
Proof.
  split.
  - intros [label EDGE].
    pose proof (proj1 (map_vertices_isLabeledEdge W_dec f G mapped_src label mapped_dst) EDGE) as MAPPED.
    destruct MAPPED as [src [dst [ORIGINAL [SRC DST]]]].
    exists src, dst. split; [exists label; exact ORIGINAL | split; assumption].
  - intros [src [dst [[label EDGE] [SRC DST]]]].
    exists label. eapply (proj2 (map_vertices_isLabeledEdge W_dec f G mapped_src label mapped_dst)).
    exists src, dst. split; [exact EDGE | split; assumption].
Qed.

#[projections(primitive)]
Record Homomorphism {V : Type} {W : Type} {A : Type} (G : LabeledFiniteGraph.t V A)
  (H : t W A)
  : Type :=
  mkHomomorphism
  { vertex_map : V -> W
  ; vertex_preserving v
    (VERTEX : G.(isVertex) v)
    : H.(isVertex) (vertex_map v)
  ; edge_preserving src label dst
    (EDGE : G.(isLabeledEdge) src label dst)
    : H.(isLabeledEdge) (vertex_map src) label (vertex_map dst)
  }.

#[global] Arguments Homomorphism {V W A} G H.
#[global] Arguments mkHomomorphism {V W A G H} vertex_map vertex_preserving edge_preserving.
#[global] Arguments vertex_map {V W A G H} _ _.
#[global] Arguments vertex_preserving {V W A G H} _ v VERTEX.
#[global] Arguments edge_preserving {V W A G H} _ src label dst EDGE.

Lemma homomorphism_isEdge {V : Type} {W : Type} {A : Type} (G : LabeledFiniteGraph.t V A)
  (H : t W A)
  (hom : Homomorphism G H) (src : V) (dst : V)
  (EDGE : G.(isEdge) src dst)
  : H.(isEdge) (hom.(vertex_map) src) (hom.(vertex_map) dst).
Proof.
  destruct EDGE as [label EDGE]. exists label. now eapply hom.(edge_preserving).
Qed.

Module Homomorphism.

#[refine]
Definition id {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) : Homomorphism G G :=
  {| vertex_map := fun v => v |}.
Proof.
  - intros v VERTEX. exact VERTEX.
  - intros src label dst EDGE. exact EDGE.
Defined.

#[refine]
Definition compose {U : Type} {V : Type} {W : Type} {A : Type}
  {G1 : t U A}
  {G2 : t V A}
  {G3 : t W A}
  (g : Homomorphism G2 G3) (f : Homomorphism G1 G2) : Homomorphism G1 G3 :=
  {| vertex_map := fun v => g.(vertex_map) (f.(vertex_map) v) |}.
Proof.
  - intros v VERTEX.
    eapply g.(vertex_preserving). now eapply f.(vertex_preserving).
  - intros src label dst EDGE.
    eapply g.(edge_preserving). now eapply f.(edge_preserving).
Defined.

#[refine]
Definition of_map_vertices {V : Type} {W : Type} {A : Type} (W_dec : hasEqDec W) (f : V -> W) (G : LabeledFiniteGraph.t V A) : Homomorphism G (map_vertices W_dec f G) :=
  {| vertex_map := f |}.
Proof.
  - intros v VERTEX. rewrite map_vertices_isVertex.
    exists v. split; [exact VERTEX | reflexivity].
  - intros src label dst EDGE. rewrite map_vertices_isLabeledEdge.
    exists src, dst. split; [exact EDGE | split; reflexivity].
Defined.

Lemma id_vertex_map {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (v : V)
  : (id G).(vertex_map) v = v.
Proof.
  reflexivity.
Qed.

Lemma compose_vertex_map {U : Type} {V : Type} {W : Type} {A : Type}
  {G1 : t U A}
  {G2 : t V A}
  {G3 : t W A}
  (g : Homomorphism G2 G3) (f : Homomorphism G1 G2) (v : U)
  : (compose g f).(vertex_map) v = g.(vertex_map) (f.(vertex_map) v).
Proof.
  reflexivity.
Qed.

Lemma walk_preserving {U : Type} {V : Type} {A : Type} {G : LabeledFiniteGraph.t U A}
  {H : t V A}
  (hom : Homomorphism G H) (src : U) (word : list A) (trace : list U) (dst : U)
  (WALK : walk G src word trace dst)
  : walk H (hom.(vertex_map) src) word (L.map hom.(vertex_map) trace) (hom.(vertex_map) dst).
Proof.
  induction WALK as [v VERTEX | src label mid word trace dst EDGE REST IH].
  - simpl. econstructor 1. now eapply hom.(vertex_preserving).
  - simpl. econstructor 2.
    + now eapply hom.(edge_preserving).
    + exact IH.
Qed.

Lemma word_walk_preserving {U : Type} {V : Type} {A : Type} {G : LabeledFiniteGraph.t U A}
  {H : t V A}
  (hom : Homomorphism G H) (src : U) (word : list A) (dst : U)
  (WALK : word_walk G src word dst)
  : word_walk H (hom.(vertex_map) src) word (hom.(vertex_map) dst).
Proof.
  destruct WALK as [trace WALK]. exists (L.map hom.(vertex_map) trace).
  exact (walk_preserving hom src word trace dst WALK).
Qed.

End Homomorphism.

#[projections(primitive)]
Record TotalDeterministic (V : Type) (A : Type) : Type :=
  mkTotalDeterministic
  { total_graph : t V A
  ; total_step : V -> A -> V
  ; total_step_vertex src label
    (VERTEX : total_graph.(isVertex) src)
    : total_graph.(isVertex) (total_step src label)
  ; total_step_spec src label dst
    (VERTEX : total_graph.(isVertex) src)
    : total_graph.(isLabeledEdge) src label dst <-> dst = total_step src label
  }.

#[global] Arguments mkTotalDeterministic {V A} total_graph total_step total_step_vertex total_step_spec.
#[global] Arguments total_graph {V A} _.
#[global] Arguments total_step {V A} _ src label.
#[global] Arguments total_step_vertex {V A} _ src label VERTEX.
#[global] Arguments total_step_spec {V A} _ src label dst VERTEX.

Lemma TotalDeterministic_deterministic {V : Type} {A : Type} (D : TotalDeterministic V A)
  : deterministic D.(total_graph).
Proof.
  intros src label dst1 dst2 EDGE1 EDGE2.
  pose proof (src_isLabeledEdge D.(total_graph) src label dst1 EDGE1) as VERTEX.
  pose proof (proj1 (D.(total_step_spec) src label dst1 VERTEX) EDGE1) as EQ1.
  pose proof (proj1 (D.(total_step_spec) src label dst2 VERTEX) EDGE2) as EQ2.
  congruence.
Qed.

Fixpoint total_run_word {V : Type} {A : Type} (D : TotalDeterministic V A) (src : V) (word : list A) {struct word} : V :=
  match word with
  | [] => src
  | label :: word' => total_run_word D (D.(total_step) src label) word'
  end.

Lemma total_run_word_isVertex {V : Type} {A : Type} (D : TotalDeterministic V A) (src : V) (word : list A)
  (VERTEX : D.(total_graph).(isVertex) src)
  : D.(total_graph).(isVertex) (total_run_word D src word).
Proof.
  revert src VERTEX. induction word as [ | label word IH]; intros src VERTEX.
  - exact VERTEX.
  - simpl. eapply IH. now eapply D.(total_step_vertex).
Qed.

Lemma total_run_word_sound {V : Type} {A : Type} (D : TotalDeterministic V A) (src : V) (word : list A)
  (VERTEX : D.(total_graph).(isVertex) src)
  : word_walk D.(total_graph) src word (total_run_word D src word).
Proof.
  revert src VERTEX. induction word as [ | label word IH]; intros src VERTEX.
  - exists []. econstructor 1. exact VERTEX.
  - simpl. pose proof (D.(total_step_vertex) src label VERTEX) as NEXT_VERTEX.
    specialize (IH (D.(total_step) src label) NEXT_VERTEX) as [trace WALK].
    exists (D.(total_step) src label :: trace). econstructor 2.
    + eapply (proj2 (D.(total_step_spec) src label (D.(total_step) src label) VERTEX)).
      reflexivity.
    + exact WALK.
Qed.

Lemma total_run_word_complete {V : Type} {A : Type} (D : TotalDeterministic V A) (src : V) (word : list A) (trace : list V) (dst : V)
  (WALK : walk D.(total_graph) src word trace dst)
  : total_run_word D src word = dst.
Proof.
  induction WALK as [v VERTEX | src label mid word trace dst EDGE REST IH].
  - reflexivity.
  - simpl.
    pose proof (src_isLabeledEdge D.(total_graph) src label mid EDGE) as VERTEX.
    pose proof (proj1 (D.(total_step_spec) src label mid VERTEX) EDGE) as EQ.
    rewrite <- EQ. exact IH.
Qed.

Theorem total_run_word_spec {V : Type} {A : Type} (D : TotalDeterministic V A) (src : V) (word : list A) (dst : V)
  (VERTEX : D.(total_graph).(isVertex) src)
  : total_run_word D src word = dst <-> word_walk D.(total_graph) src word dst.
Proof.
  split.
  - intros RUN. rewrite <- RUN. now eapply total_run_word_sound.
  - intros [trace WALK]. exact (total_run_word_complete D src word trace dst WALK).
Qed.

#[refine]
Definition to_partial {V : Type} {A : Type} (D : TotalDeterministic V A) : PartialDeterministic V A :=
  {|
    graph := D.(total_graph);
    step := fun src label =>
      if L.in_dec D.(total_graph).(V_dec) src D.(total_graph).(vertices) then
        Some (D.(total_step) src label)
      else
        None;
  |}.
Proof.
  intros src label dst. simpl.
  destruct (L.in_dec D.(total_graph).(V_dec) src D.(total_graph).(vertices)) as [VERTEX | NOT_VERTEX].
  - split.
    + intros STEP. inv STEP.
      eapply (proj2 (D.(total_step_spec) src label (D.(total_step) src label) VERTEX)).
      reflexivity.
    + intros EDGE.
      pose proof (proj1 (D.(total_step_spec) src label dst VERTEX) EDGE) as EQ.
      subst dst. reflexivity.
  - split.
    + discriminate.
    + intros EDGE. exfalso. eapply NOT_VERTEX.
      exact (src_isLabeledEdge D.(total_graph) src label dst EDGE).
Defined.

Lemma to_partial_graph {V : Type} {A : Type} (D : TotalDeterministic V A)
  : (to_partial D).(graph) = D.(total_graph).
Proof.
  reflexivity.
Qed.

Lemma to_partial_step_isVertex {V : Type} {A : Type} (D : TotalDeterministic V A) (src : V) (label : A)
  (VERTEX : D.(total_graph).(isVertex) src)
  : (to_partial D).(step) src label = Some (D.(total_step) src label).
Proof.
  unfold to_partial. simpl.
  destruct (L.in_dec D.(total_graph).(V_dec) src D.(total_graph).(vertices)) as [YES | NO].
  - reflexivity.
  - contradiction.
Qed.

Lemma to_partial_step_nonvertex {V : Type} {A : Type} (D : TotalDeterministic V A) (src : V) (label : A)
  (NOT_VERTEX : ~ D.(total_graph).(isVertex) src)
  : (to_partial D).(step) src label = None.
Proof.
  unfold to_partial. simpl.
  destruct (L.in_dec D.(total_graph).(V_dec) src D.(total_graph).(vertices)) as [YES | NO].
  - contradiction.
  - reflexivity.
Qed.

Lemma to_partial_run_word_agrees {V : Type} {A : Type} (D : TotalDeterministic V A) (src : V) (word : list A)
  (VERTEX : D.(total_graph).(isVertex) src)
  : run_word (to_partial D) src word = Some (total_run_word D src word).
Proof.
  eapply (proj2 (run_word_spec (to_partial D) src word (total_run_word D src word))).
  change (word_walk D.(total_graph) src word (total_run_word D src word)).
  exact (total_run_word_sound D src word VERTEX).
Qed.

Lemma to_partial_run_word_sound {V : Type} {A : Type} (D : TotalDeterministic V A) (src : V) (word : list A) (dst : V)
  (RUN : run_word (to_partial D) src word = Some dst)
  : word_walk D.(total_graph) src word dst.
Proof.
  exact (proj1 (run_word_spec (to_partial D) src word dst) RUN).
Qed.

Lemma to_partial_run_word_complete {V : Type} {A : Type} (D : TotalDeterministic V A) (src : V) (word : list A) (dst : V)
  (WALK : word_walk D.(total_graph) src word dst)
  : run_word (to_partial D) src word = Some dst.
Proof.
  exact (proj2 (run_word_spec (to_partial D) src word dst) WALK).
Qed.

Theorem to_partial_run_word_spec {V : Type} {A : Type} (D : TotalDeterministic V A) (src : V) (word : list A) (dst : V)
  : run_word (to_partial D) src word = Some dst <-> word_walk D.(total_graph) src word dst.
Proof.
  split; [eapply to_partial_run_word_sound | eapply to_partial_run_word_complete].
Qed.

Theorem to_partial_run_word_total_iff {V : Type} {A : Type} (D : TotalDeterministic V A) (src : V) (word : list A) (dst : V)
  (VERTEX : D.(total_graph).(isVertex) src)
  : run_word (to_partial D) src word = Some dst <-> total_run_word D src word = dst.
Proof.
  pose proof (to_partial_run_word_agrees D src word VERTEX) as AGREES.
  split.
  - intros RUN. rewrite AGREES in RUN. inv RUN. reflexivity.
  - intros EQ. rewrite EQ in AGREES. exact AGREES.
Qed.

Definition normalize_seeds {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) : fin_ensemble V :=
  L.nodup G.(V_dec) (L.filter (fun v => mem (EQ_DEC := G.(V_dec)) v G.(vertices)) seeds).

Lemma normalize_seeds_In {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (v : V)
  : L.In v (normalize_seeds G seeds) <-> (L.In v seeds /\ G.(isVertex) v).
Proof.
  unfold normalize_seeds, isVertex.
  rewrite L.nodup_In, L.filter_In, mem_spec. reflexivity.
Qed.

Lemma normalize_seeds_NoDup {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V)
  : NoDup (normalize_seeds G seeds).
Proof.
  unfold normalize_seeds. eapply L.NoDup_nodup.
Qed.

Definition closure_step {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (known : fin_ensemble V) : fin_ensemble V :=
  L.nodup G.(V_dec) (known ++ L.flat_map (successors G) known).

Lemma closure_step_In {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (known : fin_ensemble V) (v : V)
  : L.In v (closure_step G known) <-> (L.In v known \/ exists src, L.In src known /\ G.(isEdge) src v).
Proof.
  unfold closure_step.
  rewrite L.nodup_In, L.in_app_iff, L.in_flat_map.
  setoid_rewrite successors_In. reflexivity.
Qed.

Lemma closure_step_contains {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (known : fin_ensemble V) (v : V)
  (IN : L.In v known)
  : L.In v (closure_step G known).
Proof.
  rewrite closure_step_In. now left.
Qed.

Lemma closure_step_successor {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (known : fin_ensemble V) (src : V) (dst : V)
  (SRC : L.In src known)
  (EDGE : G.(isEdge) src dst)
  : L.In dst (closure_step G known).
Proof.
  rewrite closure_step_In. right. exists src. split; assumption.
Qed.

Lemma closure_step_NoDup {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (known : fin_ensemble V)
  : NoDup (closure_step G known).
Proof.
  unfold closure_step. eapply L.NoDup_nodup.
Qed.

Lemma closure_step_isVertex {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (known : fin_ensemble V)
  (KNOWN : forall v, L.In v known -> G.(isVertex) v)
  : forall v, L.In v (closure_step G known) -> G.(isVertex) v.
Proof.
  intros v IN. rewrite closure_step_In in IN.
  destruct IN as [IN | [src [SRC EDGE]]].
  - now eapply KNOWN.
  - exact (dst_isEdge G src v EDGE).
Qed.

Lemma closure_step_monotone {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (known1 : fin_ensemble V) (known2 : fin_ensemble V)
  (INCL : forall v, L.In v known1 -> L.In v known2)
  : forall v, L.In v (closure_step G known1) -> L.In v (closure_step G known2).
Proof.
  intros v IN. rewrite closure_step_In in IN |- *.
  destruct IN as [IN | [src [SRC EDGE]]].
  - left. now eapply INCL.
  - right. exists src. split; [now eapply INCL | exact EDGE].
Qed.

Definition closure_iter {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (fuel : nat) (known : fin_ensemble V) : fin_ensemble V :=
  iter fuel (closure_step G) known.

Lemma closure_iter_contains {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (fuel : nat) (known : fin_ensemble V) (v : V)
  (IN : L.In v known)
  : L.In v (closure_iter G fuel known).
Proof.
  unfold closure_iter. revert known v IN.
  induction fuel as [ | fuel IH]; intros known v IN; simpl.
  - exact IN.
  - eapply IH. now eapply closure_step_contains.
Qed.

Lemma closure_iter_mono_fuel {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (fuel1 : nat) (fuel2 : nat) (known : fin_ensemble V) (v : V)
  (LE : fuel1 <= fuel2)
  (IN : L.In v (closure_iter G fuel1 known))
  : L.In v (closure_iter G fuel2 known).
Proof.
  unfold closure_iter in *. revert fuel1 known v LE IN.
  induction fuel2 as [ | fuel2 IH]; intros fuel1 known v LE IN.
  - assert (fuel1 = 0) as EQ.
    { lia. }
    subst fuel1. exact IN.
  - destruct fuel1 as [ | fuel1].
    + simpl in IN. exact (closure_iter_contains G (S fuel2) known v IN).
    + simpl in IN |- *.
      eapply IH with (fuel1 := fuel1) (known := closure_step G known); [lia | exact IN].
Qed.

Lemma closure_iter_NoDup {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (fuel : nat) (known : fin_ensemble V)
  (NO_DUP : NoDup known)
  : NoDup (closure_iter G fuel known).
Proof.
  unfold closure_iter. revert known NO_DUP.
  induction fuel as [ | fuel IH]; intros known NO_DUP; simpl.
  - exact NO_DUP.
  - eapply IH. eapply closure_step_NoDup.
Qed.

Lemma closure_iter_isVertex {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (fuel : nat) (known : fin_ensemble V)
  (KNOWN : forall v, L.In v known -> G.(isVertex) v)
  : forall v, L.In v (closure_iter G fuel known) -> G.(isVertex) v.
Proof.
  unfold closure_iter. revert known KNOWN.
  induction fuel as [ | fuel IH]; intros known KNOWN v IN; simpl in IN.
  - now eapply KNOWN.
  - eapply IH; [ | exact IN].
    intros v0 IN0. exact (closure_step_isVertex G known KNOWN v0 IN0).
Qed.

Lemma closure_iter_monotone {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (fuel : nat) (known1 : fin_ensemble V) (known2 : fin_ensemble V)
  (INCL : forall v, L.In v known1 -> L.In v known2)
  : forall v, L.In v (closure_iter G fuel known1) -> L.In v (closure_iter G fuel known2).
Proof.
  unfold closure_iter. revert known1 known2 INCL.
  induction fuel as [ | fuel IH]; intros known1 known2 INCL v IN; simpl in IN |- *.
  - now eapply INCL.
  - eapply IH; [ | exact IN].
    intros v0 IN0. exact (closure_step_monotone G known1 known2 INCL v0 IN0).
Qed.

Definition vertex_list_subsetb {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (xs : fin_ensemble V) (ys : fin_ensemble V) : bool :=
  L.forallb (fun v => mem (EQ_DEC := G.(V_dec)) v ys) xs.

Lemma vertex_list_subsetb_sound {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (xs : fin_ensemble V) (ys : fin_ensemble V)
  (SUBSET : vertex_list_subsetb G xs ys = true)
  : forall v, L.In v xs -> L.In v ys.
Proof.
  unfold vertex_list_subsetb in SUBSET. rewrite L.forallb_forall in SUBSET.
  intros v IN. specialize (SUBSET v IN). now rewrite mem_spec in SUBSET.
Qed.

Lemma vertex_list_subsetb_complete {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (xs : fin_ensemble V) (ys : fin_ensemble V)
  (SUBSET : forall v, L.In v xs -> L.In v ys)
  : vertex_list_subsetb G xs ys = true.
Proof.
  unfold vertex_list_subsetb. rewrite L.forallb_forall.
  intros v IN. rewrite mem_spec. now eapply SUBSET.
Qed.

Lemma vertex_list_subsetb_false_new {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (xs : fin_ensemble V) (ys : fin_ensemble V)
  (SUBSET : vertex_list_subsetb G xs ys = false)
  : exists v, L.In v xs /\ ~ L.In v ys.
Proof.
  unfold vertex_list_subsetb in SUBSET.
  pose proof (forallb_false_exists (fun v => mem (EQ_DEC := G.(V_dec)) v ys) xs SUBSET) as [v [IN MEM]].
  exists v. split; [exact IN | ]. now rewrite mem_spec in MEM.
Qed.

Lemma NoDup_incl_new_length_lt {V : Type} (V_dec : hasEqDec V) (xs : fin_ensemble V) (ys : fin_ensemble V) (x : V)
  (NO_DUP_XS : NoDup xs)
  (NO_DUP_YS : NoDup ys)
  (IN_XS : L.In x xs)
  (NOT_IN_YS : ~ L.In x ys)
  (INCL : forall y, L.In y ys -> L.In y xs)
  : L.length ys < L.length xs.
Proof.
  enough (LE : L.length ys <= L.length (L.remove V_dec x xs)).
  { pose proof (@remove_length_lt V V_dec x xs IN_XS) as LT.
    eapply Nat.le_lt_trans; [exact LE | exact LT].
  }
  eapply L.NoDup_incl_length.
  - exact NO_DUP_YS.
  - intros y IN. rewrite L.in_remove_iff. split.
    + now eapply INCL.
    + intros EQ. subst y. contradiction.
Qed.

Lemma closure_step_length_if_not_subset {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (known : fin_ensemble V)
  (NO_DUP : NoDup known)
  (NOT_SUBSET : vertex_list_subsetb G (closure_step G known) known = false)
  : L.length known < L.length (closure_step G known).
Proof.
  pose proof (vertex_list_subsetb_false_new G (closure_step G known) known NOT_SUBSET) as [v [IN_STEP NOT_IN]].
  eapply NoDup_incl_new_length_lt with (V_dec := G.(V_dec)) (x := v).
  - eapply closure_step_NoDup.
  - exact NO_DUP.
  - exact IN_STEP.
  - exact NOT_IN.
  - intros v0 IN0. now eapply closure_step_contains.
Qed.

Lemma closure_step_fixed_if_subset {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (known : fin_ensemble V)
  (SUBSET : vertex_list_subsetb G (closure_step G known) known = true)
  : forall v, L.In v (closure_step G known) -> L.In v known.
Proof.
  exact (vertex_list_subsetb_sound G (closure_step G known) known SUBSET).
Qed.

Lemma closure_iter_length_bound {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (fuel : nat) (known : fin_ensemble V)
  (NO_DUP : NoDup known)
  (KNOWN : forall v, L.In v known -> G.(isVertex) v)
  : L.length (closure_iter G fuel known) <= L.length G.(vertices).
Proof.
  eapply L.NoDup_incl_length.
  - exact (closure_iter_NoDup G fuel known NO_DUP).
  - intros v IN. unfold isVertex in *.
    exact (closure_iter_isVertex G fuel known KNOWN v IN).
Qed.

Lemma closure_not_fixed_length_lower {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (known : fin_ensemble V)
  (NO_DUP : NoDup known)
  (n : nat) (NOT_FIXED_PREFIX : forall i, i < n -> vertex_list_subsetb G (closure_step G (closure_iter G i known)) (closure_iter G i known) = false)
  : n <= L.length (closure_iter G n known).
Proof.
  revert NOT_FIXED_PREFIX. induction n as [ | n IH]; intros NOT_FIXED_PREFIX; [simpl; lia | ].
  unfold closure_iter at 1. rewrite iter_succ.
  assert (ITER_NO_DUP : NoDup (closure_iter G n known)).
  { exact (closure_iter_NoDup G n known NO_DUP). }
  assert (NOT_FIXED_N : vertex_list_subsetb G (closure_step G (closure_iter G n known)) (closure_iter G n known) = false).
  { eapply NOT_FIXED_PREFIX. lia. }
  pose proof (closure_step_length_if_not_subset G (closure_iter G n known) ITER_NO_DUP NOT_FIXED_N) as LT.
  assert (PREFIX : forall i, i < n -> vertex_list_subsetb G (closure_step G (closure_iter G i known)) (closure_iter G i known) = false).
  { intros i LT_I. eapply NOT_FIXED_PREFIX. lia. }
  specialize (IH PREFIX).
  unfold closure_iter in LT, IH. lia.
Qed.

Lemma closure_first_fixed_before_bound {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (known : fin_ensemble V)
  (NO_DUP : NoDup known)
  (KNOWN : forall v, L.In v known -> G.(isVertex) v)
  : exists i, i <= L.length G.(vertices) /\ vertex_list_subsetb G (closure_step G (closure_iter G i known)) (closure_iter G i known) = true.
Proof.
  set (fuel := L.length G.(vertices)).
  destruct (L.existsb (fun i => vertex_list_subsetb G (closure_step G (closure_iter G i known)) (closure_iter G i known)) (L.seq 0 (S fuel))) eqn: EX.
  - rewrite L.existsb_exists in EX.
    destruct EX as [i [IN_SEQ FIXED]].
    rewrite L.in_seq in IN_SEQ. exists i. split; [lia | exact FIXED].
  - assert (NOT_FIXED : forall i, i <= fuel -> vertex_list_subsetb G (closure_step G (closure_iter G i known)) (closure_iter G i known) = false).
    { intros i LE_I.
      assert (IN_SEQ : L.In i (L.seq 0 (S fuel))).
      { rewrite L.in_seq. lia. }
      destruct (vertex_list_subsetb G (closure_step G (closure_iter G i known)) (closure_iter G i known)) eqn: FIXED; [ | reflexivity].
      assert (EX_TRUE : L.existsb (fun j => vertex_list_subsetb G (closure_step G (closure_iter G j known)) (closure_iter G j known)) (L.seq 0 (S fuel)) = true).
      { rewrite L.existsb_exists. exists i. split; [exact IN_SEQ | exact FIXED]. }
      congruence.
    }
    assert (PREFIX : forall i, i < S fuel -> vertex_list_subsetb G (closure_step G (closure_iter G i known)) (closure_iter G i known) = false).
    { intros i LT_I. eapply NOT_FIXED. lia. }
    pose proof (closure_not_fixed_length_lower G known NO_DUP (S fuel) PREFIX) as LE_LOWER.
    pose proof (closure_iter_length_bound G (S fuel) known NO_DUP KNOWN) as LE_BOUND.
    unfold fuel in *. lia.
Qed.

Lemma closure_iter_after_fixed_subset {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (known : fin_ensemble V) (i : nat) (j : nat) (FIXED : forall v, L.In v (closure_step G (closure_iter G i known)) -> L.In v (closure_iter G i known))
  (LE : i <= j)
  : forall v, L.In v (closure_iter G j known) -> L.In v (closure_iter G i known).
Proof.
  unfold closure_iter in *. induction j as [ | j IH]; intros v IN.
  - assert (i = 0) as EQ.
    { lia. }
    subst i. exact IN.
  - destruct (Nat.eq_dec i (S j)) as [EQ | NE].
    + subst i. exact IN.
    + assert (LE_PREV : i <= j).
      { lia. }
      rewrite iter_succ in IN.
      eapply FIXED.
      eapply closure_step_monotone.
      * intros v0 IN0. eapply IH; [exact LE_PREV | exact IN0].
      * exact IN.
Qed.

Lemma closure_iter_fixed_at_vertex_bound {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (known : fin_ensemble V)
  (NO_DUP : NoDup known)
  (KNOWN : forall v, L.In v known -> G.(isVertex) v)
  : forall v, L.In v (closure_step G (closure_iter G (L.length G.(vertices)) known)) -> L.In v (closure_iter G (L.length G.(vertices)) known).
Proof.
  destruct (closure_first_fixed_before_bound G known NO_DUP KNOWN) as [i [LE_I FIXED_I]].
  assert (FIXED : forall v, L.In v (closure_step G (closure_iter G i known)) -> L.In v (closure_iter G i known)).
  { exact (closure_step_fixed_if_subset G (closure_iter G i known) FIXED_I). }
  intros v IN.
  assert (IN_NEXT : L.In v (closure_iter G (S (L.length G.(vertices))) known)).
  { unfold closure_iter. rewrite iter_succ. exact IN. }
  pose proof (closure_iter_after_fixed_subset G known i (S (L.length G.(vertices))) FIXED) as AFTER_FIXED.
  specialize (AFTER_FIXED ltac:(lia) v IN_NEXT).
  exact (closure_iter_mono_fuel G i (L.length G.(vertices)) known v LE_I AFTER_FIXED).
Qed.

Definition reachable_vertices {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) : fin_ensemble V :=
  closure_iter G (L.length G.(vertices)) (normalize_seeds G seeds).

Lemma reachable_vertices_NoDup {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V)
  : NoDup (reachable_vertices G seeds).
Proof.
  unfold reachable_vertices.
  eapply closure_iter_NoDup. eapply normalize_seeds_NoDup.
Qed.

Lemma reachable_vertices_isVertex {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (v : V)
  (IN : L.In v (reachable_vertices G seeds))
  : G.(isVertex) v.
Proof.
  unfold reachable_vertices in IN.
  eapply closure_iter_isVertex; [ | exact IN].
  intros seed SEED. rewrite normalize_seeds_In in SEED. exact (proj2 SEED).
Qed.

Lemma reachable_vertices_seed {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (seed : V)
  (SEED : L.In seed seeds)
  (VERTEX : G.(isVertex) seed)
  : L.In seed (reachable_vertices G seeds).
Proof.
  unfold reachable_vertices. eapply closure_iter_contains.
  rewrite normalize_seeds_In. split; assumption.
Qed.

Lemma reachable_vertices_step_closed {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (v : V)
  (IN : L.In v (closure_step G (reachable_vertices G seeds)))
  : L.In v (reachable_vertices G seeds).
Proof.
  unfold reachable_vertices in *.
  eapply closure_iter_fixed_at_vertex_bound.
  - eapply normalize_seeds_NoDup.
  - intros seed SEED. rewrite normalize_seeds_In in SEED. exact (proj2 SEED).
  - exact IN.
Qed.

Lemma reachable_vertices_edge_closed {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (src : V) (dst : V)
  (SRC : L.In src (reachable_vertices G seeds))
  (EDGE : G.(isEdge) src dst)
  : L.In dst (reachable_vertices G seeds).
Proof.
  eapply reachable_vertices_step_closed.
  exact (closure_step_successor G (reachable_vertices G seeds) src dst SRC EDGE).
Qed.

Lemma walk_one {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (src : V) (label : A) (dst : V)
  (EDGE : G.(isLabeledEdge) src label dst)
  : walk G src [label] [dst] dst.
Proof.
  econstructor 2.
  - exact EDGE.
  - econstructor 1. exact (dst_isLabeledEdge G src label dst EDGE).
Qed.

Definition reachable_witness {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (dst : V) : Prop :=
  exists seed, L.In seed seeds /\ G.(isVertex) seed /\ exists word trace, walk G seed word trace dst.

Lemma closure_step_reachable_sound {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (known : fin_ensemble V)
  (SOUND : forall v, L.In v known -> reachable_witness G seeds v)
  : forall v, L.In v (closure_step G known) -> reachable_witness G seeds v.
Proof.
  intros v IN. rewrite closure_step_In in IN.
  destruct IN as [IN | [src [SRC [label EDGE]]]].
  - now eapply SOUND.
  - specialize (SOUND src SRC).
    destruct SOUND as [seed [SEED [SEED_VERTEX [word [trace WALK]]]]].
    exists seed. split; [exact SEED | split; [exact SEED_VERTEX | ]].
    exists (word ++ [label]), (trace ++ [v]).
    exact (walk_app G seed src v word [label] trace [v] WALK (walk_one G src label v EDGE)).
Qed.

Lemma closure_iter_reachable_sound {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (fuel : nat) (known : fin_ensemble V)
  (SOUND : forall v, L.In v known -> reachable_witness G seeds v)
  : forall v, L.In v (closure_iter G fuel known) -> reachable_witness G seeds v.
Proof.
  unfold closure_iter. revert known SOUND.
  induction fuel as [ | fuel IH]; intros known SOUND v IN; simpl in IN.
  - now eapply SOUND.
  - eapply IH; [ | exact IN].
    exact (closure_step_reachable_sound G seeds known SOUND).
Qed.

Lemma normalize_seeds_reachable_sound {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (seed : V)
  (IN : L.In seed (normalize_seeds G seeds))
  : reachable_witness G seeds seed.
Proof.
  rewrite normalize_seeds_In in IN. destruct IN as [SEED VERTEX].
  exists seed. split; [exact SEED | split; [exact VERTEX | ]].
  exists [], []. econstructor 1. exact VERTEX.
Qed.

Lemma reachable_vertices_sound {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (dst : V)
  (IN : L.In dst (reachable_vertices G seeds))
  : reachable_witness G seeds dst.
Proof.
  unfold reachable_vertices in IN.
  eapply closure_iter_reachable_sound; [ | exact IN].
  intros seed SEED. exact (normalize_seeds_reachable_sound G seeds seed SEED).
Qed.

Lemma reachable_vertices_walk_closed {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (src : V) (word : list A) (trace : list V) (dst : V)
  (SRC : L.In src (reachable_vertices G seeds))
  (WALK : walk G src word trace dst)
  : L.In dst (reachable_vertices G seeds).
Proof.
  revert SRC. induction WALK as [v VERTEX | src label mid word trace dst EDGE REST IH]; intros SRC.
  - exact SRC.
  - eapply IH. eapply reachable_vertices_edge_closed.
    + exact SRC.
    + exists label. exact EDGE.
Qed.

Lemma reachable_vertices_complete {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (dst : V)
  (REACHABLE : reachable_witness G seeds dst)
  : L.In dst (reachable_vertices G seeds).
Proof.
  destruct REACHABLE as [seed [SEED [VERTEX [word [trace WALK]]]]].
  eapply reachable_vertices_walk_closed.
  - exact (reachable_vertices_seed G seeds seed SEED VERTEX).
  - exact WALK.
Qed.

Theorem reachable_vertices_In {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (dst : V)
  : L.In dst (reachable_vertices G seeds) <-> (exists seed, L.In seed seeds /\ G.(isVertex) seed /\ exists word trace, walk G seed word trace dst).
Proof.
  split.
  - eapply reachable_vertices_sound.
  - eapply reachable_vertices_complete.
Qed.

Definition reachable_vertexb {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (v : V) : bool :=
  mem (EQ_DEC := G.(V_dec)) v (reachable_vertices G seeds).

Lemma reachable_vertexb_true_iff {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (v : V)
  : reachable_vertexb G seeds v = true <-> L.In v (reachable_vertices G seeds).
Proof.
  unfold reachable_vertexb. rewrite mem_spec. reflexivity.
Qed.

Definition reachable_subgraph {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) : t V A :=
  induced G (reachable_vertexb G seeds).

Lemma reachable_subgraph_isVertex {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (v : V)
  : (reachable_subgraph G seeds).(isVertex) v <-> L.In v (reachable_vertices G seeds).
Proof.
  unfold reachable_subgraph. rewrite induced_isVertex, reachable_vertexb_true_iff.
  split.
  - intros [_ IN]. exact IN.
  - intros IN. split; [exact (reachable_vertices_isVertex G seeds v IN) | exact IN].
Qed.

Lemma reachable_subgraph_isLabeledEdge {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (src : V) (label : A) (dst : V)
  : (reachable_subgraph G seeds).(isLabeledEdge) src label dst <-> (G.(isLabeledEdge) src label dst /\ L.In src (reachable_vertices G seeds) /\ L.In dst (reachable_vertices G seeds)).
Proof.
  unfold reachable_subgraph. rewrite induced_isLabeledEdge.
  rewrite !reachable_vertexb_true_iff. tauto.
Qed.

Lemma reachable_subgraph_isLabeledEdge_src {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (src : V) (label : A) (dst : V)
  : (reachable_subgraph G seeds).(isLabeledEdge) src label dst <-> (G.(isLabeledEdge) src label dst /\ L.In src (reachable_vertices G seeds)).
Proof.
  rewrite reachable_subgraph_isLabeledEdge. split.
  - tauto.
  - intros [EDGE SRC]. split; [exact EDGE | split; [exact SRC | ]].
    eapply reachable_vertices_edge_closed.
    + exact SRC.
    + exists label. exact EDGE.
Qed.

Lemma reachable_subgraph_isEdge {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (src : V) (dst : V)
  : (reachable_subgraph G seeds).(isEdge) src dst <-> (G.(isEdge) src dst /\ L.In src (reachable_vertices G seeds)).
Proof.
  unfold isEdge. setoid_rewrite reachable_subgraph_isLabeledEdge_src. firstorder.
Qed.

Definition coaccessible_vertices {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (targets : fin_ensemble V) : fin_ensemble V :=
  reachable_vertices (reverse G) targets.

Lemma coaccessible_vertices_NoDup {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (targets : fin_ensemble V)
  : NoDup (coaccessible_vertices G targets).
Proof.
  unfold coaccessible_vertices. eapply reachable_vertices_NoDup.
Qed.

Lemma coaccessible_vertices_isVertex {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (targets : fin_ensemble V) (v : V)
  (IN : L.In v (coaccessible_vertices G targets))
  : G.(isVertex) v.
Proof.
  unfold coaccessible_vertices in IN.
  pose proof (reachable_vertices_isVertex (reverse G) targets v IN) as VERTEX.
  now rewrite reverse_isVertex in VERTEX.
Qed.

Theorem coaccessible_vertices_In {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (targets : fin_ensemble V) (src : V)
  : L.In src (coaccessible_vertices G targets) <-> (exists target, L.In target targets /\ G.(isVertex) target /\ exists word trace, walk (reverse G) target word trace src).
Proof.
  unfold coaccessible_vertices. rewrite reachable_vertices_In.
  setoid_rewrite reverse_isVertex. reflexivity.
Qed.

Lemma coaccessible_vertices_isLabeledEdge_closed {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (targets : fin_ensemble V) (src : V) (label : A) (dst : V)
  (EDGE : G.(isLabeledEdge) src label dst)
  (DST : L.In dst (coaccessible_vertices G targets))
  : L.In src (coaccessible_vertices G targets).
Proof.
  unfold coaccessible_vertices in *. eapply reachable_vertices_edge_closed.
  - exact DST.
  - exists label. now rewrite <- reverse_isLabeledEdge in EDGE.
Qed.

Lemma coaccessible_vertices_isEdge_closed {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (targets : fin_ensemble V) (src : V) (dst : V)
  (EDGE : G.(isEdge) src dst)
  (DST : L.In dst (coaccessible_vertices G targets))
  : L.In src (coaccessible_vertices G targets).
Proof.
  destruct EDGE as [label EDGE].
  exact (coaccessible_vertices_isLabeledEdge_closed G targets src label dst EDGE DST).
Qed.

Definition coaccessible_vertexb {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (targets : fin_ensemble V) (v : V) : bool :=
  mem (EQ_DEC := G.(V_dec)) v (coaccessible_vertices G targets).

Lemma coaccessible_vertexb_true_iff {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (targets : fin_ensemble V) (v : V)
  : coaccessible_vertexb G targets v = true <-> L.In v (coaccessible_vertices G targets).
Proof.
  unfold coaccessible_vertexb. rewrite mem_spec. reflexivity.
Qed.

Definition trim_vertexb {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (targets : fin_ensemble V) (v : V) : bool :=
  reachable_vertexb G seeds v && coaccessible_vertexb G targets v.

Lemma trim_vertexb_true_iff {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (targets : fin_ensemble V) (v : V)
  : trim_vertexb G seeds targets v = true <-> (L.In v (reachable_vertices G seeds) /\ L.In v (coaccessible_vertices G targets)).
Proof.
  unfold trim_vertexb. rewrite andb_true_iff.
  rewrite reachable_vertexb_true_iff, coaccessible_vertexb_true_iff. reflexivity.
Qed.

Definition trim {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (targets : fin_ensemble V) : t V A :=
  induced G (trim_vertexb G seeds targets).

Lemma trim_isVertex {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (targets : fin_ensemble V) (v : V)
  : (trim G seeds targets).(isVertex) v <-> (L.In v (reachable_vertices G seeds) /\ L.In v (coaccessible_vertices G targets)).
Proof.
  unfold trim. rewrite induced_isVertex, trim_vertexb_true_iff. split.
  - intros [_ IN]. exact IN.
  - intros [REACH COACCESS]. split.
    + exact (reachable_vertices_isVertex G seeds v REACH).
    + split; assumption.
Qed.

Lemma trim_isLabeledEdge {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (targets : fin_ensemble V) (src : V) (label : A) (dst : V)
  : (trim G seeds targets).(isLabeledEdge) src label dst <-> (G.(isLabeledEdge) src label dst /\ (L.In src (reachable_vertices G seeds) /\ L.In src (coaccessible_vertices G targets)) /\ (L.In dst (reachable_vertices G seeds) /\ L.In dst (coaccessible_vertices G targets))).
Proof.
  unfold trim. rewrite induced_isLabeledEdge.
  rewrite !trim_vertexb_true_iff. reflexivity.
Qed.

Lemma trim_isLabeledEdge_boundary {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (targets : fin_ensemble V) (src : V) (label : A) (dst : V)
  : (trim G seeds targets).(isLabeledEdge) src label dst <-> (G.(isLabeledEdge) src label dst /\ L.In src (reachable_vertices G seeds) /\ L.In dst (coaccessible_vertices G targets)).
Proof.
  rewrite trim_isLabeledEdge. split.
  - intros [EDGE [[SRC_REACH SRC_COACCESS] [DST_REACH DST_COACCESS]]].
    splits; eauto.
  - intros [EDGE [SRC_REACH DST_COACCESS]].
    assert (DST_REACH : L.In dst (reachable_vertices G seeds)).
    { eapply reachable_vertices_edge_closed.
      - exact SRC_REACH.
      - exists label. exact EDGE.
    }
    assert (SRC_COACCESS : L.In src (coaccessible_vertices G targets)).
    { exact (coaccessible_vertices_isLabeledEdge_closed G targets src label dst EDGE DST_COACCESS). }
    splits; eauto.
Qed.

Lemma trim_isEdge_boundary {V : Type} {A : Type} (G : LabeledFiniteGraph.t V A) (seeds : fin_ensemble V) (targets : fin_ensemble V) (src : V) (dst : V)
  : (trim G seeds targets).(isEdge) src dst <-> (G.(isEdge) src dst /\ L.In src (reachable_vertices G seeds) /\ L.In dst (coaccessible_vertices G targets)).
Proof.
  unfold isEdge. setoid_rewrite trim_isLabeledEdge_boundary. firstorder.
Qed.

End LabeledFiniteGraph.

Module Canonical := LabeledFiniteGraph.

End GraphAPI.
