Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Category.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Data.FiniteMap.

#[local] Notation In := L.In.
#[local] Infix "\in" := E.In : type_scope.

Module GRAPH.

#[projections(primitive)]
Class t : Type :=
  { vertices : Type
  ; edges : ensemble (vertices * vertices)
  } as G.

End GRAPH.

Section GraphTheory_basic1.

#[local] Notation vertices := GRAPH.vertices.
#[local] Notation edges := GRAPH.edges.

Context {G : GRAPH.t}.

#[local] Notation V := G.(vertices).
#[local] Notation E := G.(edges).

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
Proof with eauto.
  split.
  - intros H_path. split.
    + induction H_path; simpl...
    + eapply path_vertices_no_dup...
  - intros [H_walk NO_DUP].
    eapply no_dup_walk_is_path...
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

End GraphTheory_basic1.

#[global] Arguments Walk_nil {G} {v}.
#[global] Arguments Walk_cons {G} {v} {v0} {v1}.

#[local] Notation " `[ v -> v' ] " := (Walk v' v) : type_scope.

Module GraphNotations.

Notation " src ~~~[ w ]~~>* tgt " := (walk tgt src w) : type_scope.
Notation " src ---[ p ]-->* tgt " := (path tgt src p) : type_scope.
Notation " src ===[ t ]==>* tgt " := (trail tgt src t) : type_scope.

End GraphNotations.

#[projections(primitive)]
Record Labeled {G : GRAPH.t} : Type :=
  { labels : Type
  ; labeling {v} {v'} (E_v_v' : (v, v') \in G.(GRAPH.edges)) : ensemble labels
  }.

#[global] Arguments Labeled : clear implicits.

Fixpoint labeledWalk {G : GRAPH.t} {G_labeled : Labeled G} {v} {v'} (H_Walk : `[ v -> v' ]) : ensemble (list G_labeled.(labels)) :=
  match H_Walk with
  | Walk_nil => pure (@L.nil G_labeled.(labels))
  | Walk_cons H_edge H_Walk' => liftM2 (@L.cons G_labeled.(labels)) (G_labeled.(labeling) H_edge) (labeledWalk H_Walk')
  end.

Module DigraphFixedpoint.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.

Section DIGRAPH_FIXEDPOINT.

#[local] Notation " src '~~~[' w ']~~>*('  G  ')' tgt " := (@walk G tgt src w).
#[local] Notation " src '---[' p ']-->*('  G  ')' tgt " := (@path G tgt src p).
#[local] Notation " src '===[' t ']==>*('  G  ')' tgt " := (@trail G tgt src t).

#[local] Infix "=~=" := (is_similar_to (Similarity := list_corresponds_to_finite_ensemble)).
#[local] Notation vertices := GRAPH.vertices.
#[local] Notation edges := GRAPH.edges.

Context {G : GRAPH.t}.

#[local] Notation V := G.(vertices).
#[local] Notation E := G.(edges).

#[local] Notation " src ~~~[ w ]~~> tgt " := (walk tgt src w) : type_scope.

Context {A : Type} (seed : V -> ensemble A).

Inductive gmu (x : V) : ensemble A :=
  | gmu_seed
    : seed x \subseteq gmu x
  | gmu_propagated y
    (EDGE : (x, y) \in E)
    : gmu y \subseteq gmu x.

Variable seed' : V -> list A.

Hypothesis seed_sim : forall v, seed' v =~= seed v.

Variable vertices' : list V.

Hypothesis vertices_sim : vertices' =~= E.full.

Lemma vertices'_complete (v : V)
  : In v vertices'.
Proof.
  pose proof vertices_sim as SIM.
  rewrite list_corresponds_to_finite_ensemble_iff in SIM.
  rewrite -> SIM. econs.
Qed.

Definition reachable (x : V) : ensemble V :=
  fun y => exists w, x ~~~[ w ]~~> y.

Context `{V_dec : hasEqDec V} `{E_dec : forall x : V, forall y : V, B.Decision ((x, y) \in E)}.

Fixpoint reachableb (fuel : nat) (x : V) (y : V) {struct fuel} : bool :=
  match fuel with
  | O => eqb x y
  | S fuel' => eqb x y || L.existsb (fun z => if E_dec x z then reachableb fuel' z y else false) vertices'
  end.

Definition reachable' (x : V) : list V :=
  L.filter (reachableb (L.length vertices') x) vertices'.

Lemma reachableb_sound (fuel : nat) (x : V) (y : V)
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

Lemma reachableb_complete (fuel : nat) (x : V) (y : V) (w : list V)
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
    exists v1. split; [eapply vertices'_complete | ].
    destruct (E_dec v0 v1) as [EDGE' | NO_EDGE]; ss!.
Qed.

Lemma reachableb_iff_reachable (x : V) (y : V)
  : reachableb (L.length vertices') x y = true <-> y \in reachable x.
Proof.
  split.
  - intros REACH.
    pose proof (reachableb_sound _ _ _ REACH) as (w & _ & WALK).
    now exists w.
  - intros [w WALK].
    assert (exists p, x ---[ p ]-->*( G ) y) as [p PATH].
    { eapply @walk_finds_path with (G := G) (w := w); eauto.
      now intros v vs; pose proof (L.in_dec eq_dec v vs) as [YES | NO]; [left | right].
    }
    rewrite path_iff_no_dup_walk in PATH.
    clear WALK. destruct PATH as [WALK NO_DUP].
    eapply reachableb_complete; eauto.
    eapply L.NoDup_incl_length; eauto.
    ii; eapply vertices'_complete.
Qed.

Lemma reachable_sim (x : V)
  : reachable' x =~= reachable x.
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff.
  intros y. unfold reachable'. rewrite -> L.filter_In. split.
  - intros [_ REACH]. now rewrite <- reachableb_iff_reachable.
  - intros REACH. split.
    + eapply vertices'_complete.
    + now rewrite reachableb_iff_reachable.
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

Definition gmu' (x : V) : list A :=
  L.flat_map seed' (reachable' x).

Theorem gmu_sim (x : V)
  : gmu' x =~= gmu x.
Proof.
  pose proof (list_corresponds_to_finite_ensemble_flat_map (reachable' x) (reachable x) seed' seed (reachable_sim x) seed_sim) as FLAT_MAP.
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

Fixpoint digraph_value {A : Type} `{EQ_DEC : hasEqDec A} (fuel : nat) (seed : X -> list A) (deps : X -> list X) (x : X) : list A :=
  match fuel with
  | O => normalize (seed x)
  | S fuel' => normalize (union (seed x) (flat_map (digraph_value fuel' seed deps) (deps x)))
  end.

Inductive digraph_closure {A : Type} (seed : X -> list A) (deps : X -> list X) (a : A) (x : X) : Prop :=
  | digraph_closure_seed
    (IN : a ∈ seed x)
    : digraph_closure seed deps a x
  | digraph_closure_step y
    (EDGE : y ∈ deps x)
    (IN : digraph_closure seed deps a y)
    : digraph_closure seed deps a x.

Inductive digraph_trace {A : Type} (seed : X -> list A) (deps : X -> list X) (a : A) (x : X) : ensemble (list X) :=
  | digraph_trace_seed
    (IN : a ∈ seed x)
    : [] \in digraph_trace seed deps a x
  | digraph_trace_step y trace
    (EDGE : y ∈ deps x)
    (TRACE : digraph_trace seed deps a y trace)
    : y :: trace \in digraph_trace seed deps a x.

Theorem digraph_closure_iff_trace {A : Type} (seed : X -> list A) (deps : X -> list X) (x : X) (a : A)
  : digraph_closure seed deps a x <-> (exists trace, trace \in digraph_trace seed deps a x).
Proof.
  split.
  - intros IN. induction IN as [x IN | x y EDGE IN IH].
    + exists []. eapply digraph_trace_seed. exact IN.
    + destruct IH as [trace TRACE]. exists (y :: trace). eapply digraph_trace_step; eauto.
  - intros [trace TRACE]. induction TRACE as [x IN | x y trace EDGE TRACE IH].
    + eapply digraph_closure_seed; eauto.
    + eapply digraph_closure_step; eauto.
Qed.

Lemma digraph_trace_in_nodes {A : Type} (nodes : list X) (seed : X -> list A) (deps : X -> list X) (x : X) (a : A) (trace : list X)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  (TRACE : trace \in digraph_trace seed deps a x)
  : Forall (fun y => y ∈ nodes) trace.
Proof.
  induction TRACE as [x IN | x y trace EDGE TRACE IH]; [econs 1 | econs 2]; eauto.
Qed.

Definition digraph_graph (deps : X -> list X) : GRAPH.t :=
  {|
    GRAPH.vertices := X;
    GRAPH.edges := fun '(x, x') => x' ∈ deps x;
  |}.

Lemma digraph_trace_seed_at_last {A : Type} (seed : X -> list A) (deps : X -> list X) (x : X) (a : A) (trace : list X)
  (TRACE : trace \in digraph_trace seed deps a x)
  : a ∈ seed (last trace x).
Proof.
  induction TRACE as [x IN | x y trace EDGE TRACE IH]; ss!.
Qed.

Lemma digraph_trace_walk {A : Type} (seed : X -> list A) (deps : X -> list X) (x : X) (a : A) (trace : list X)
  (TRACE : trace \in digraph_trace seed deps a x)
  : x ~~~[ trace ]~~>*( digraph_graph deps ) last trace x.
Proof.
  induction TRACE as [x IN | x y trace EDGE TRACE IH]; ss!.
Qed.

Lemma digraph_walk_trace {A : Type} (seed : X -> list A) (deps : X -> list X) (x : X) (a : A) (x' : X) (trace : list X)
  (WALK : x ~~~[ trace ]~~>*( digraph_graph deps ) x')
  (IN : a ∈ seed x')
  : trace \in digraph_trace seed deps a x.
Proof.
  induction WALK as [ | v0 v1 w EDGE WALK IH]; now constructor.
Qed.

Lemma digraph_trace_simple {A : Type} `{X_hasEqDec : hasEqDec X} (seed : X -> list A) (deps : X -> list X) (x : X) (a : A) (trace : list X)
  (TRACE : trace \in digraph_trace seed deps a x)
  : exists simple, digraph_trace seed deps a x simple /\ NoDup simple.
Proof.
  pose proof (digraph_trace_walk seed deps x a trace TRACE) as WALK.
  pose proof (digraph_trace_seed_at_last seed deps x a trace TRACE) as SEED.
  assert (exists simple, x ---[ simple ]-->*( digraph_graph deps ) last trace x) as [simple PATH].
  { eapply walk_finds_path with (w := trace); auto. intros v vs.
    now pose proof (@L.in_dec X X_hasEqDec v vs) as [YES | NO]; [left | right].
  }
  rewrite path_iff_no_dup_walk in PATH. destruct PATH as [WALK' NO_DUP].
  exists simple; split; [eapply digraph_walk_trace; eauto | exact NO_DUP].
Qed.

Lemma digraph_trace_simple_bounded {A : Type} `{X_hasEqDec : hasEqDec X} (nodes : list X) (seed : X -> list A) (deps : X -> list X) (x : X) (a : A) (trace : list X)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  (TRACE : trace \in digraph_trace seed deps a x)
  : exists simple, simple \in digraph_trace seed deps a x /\ length simple <= length nodes.
Proof.
  pose proof (digraph_trace_simple seed deps x a trace TRACE) as (simple & TRACE' & NO_DUP).
  pose proof (digraph_trace_in_nodes nodes seed deps x a simple deps_CLOSED TRACE') as IN_NODES.
  exists simple. split; trivial. eapply L.NoDup_incl_length; [exact NO_DUP | intros y IN].
  rewrite Forall_forall in IN_NODES. now eapply IN_NODES.
Qed.

Definition digraph_equation {A : Type} (seed : X -> list A) (deps : X -> list X) (value : X -> list A) : Prop :=
  forall x, forall a, a ∈ value x <-> ⟪ UNFOLD : a ∈ seed x \/ (exists y, y ∈ deps x /\ a ∈ value y) ⟫.

Lemma digraph_value_seed {A : Type} `{EQ_DEC : hasEqDec A} (fuel : nat) (seed : X -> list A) (deps : X -> list X) (x : X) (a : A)
  (IN : a ∈ seed x)
  : a ∈ digraph_value fuel seed deps x.
Proof.
  destruct fuel as [ | fuel]; simpl; eapply normalize_complete; auto. now eapply union_complete; left.
Qed.

Lemma digraph_value_propagated {A : Type} `{EQ_DEC : hasEqDec A} (fuel : nat) (seed : X -> list A) (deps : X -> list X) (x : X) (y : X) (a : A)
  (EDGE : y ∈ deps x)
  (IN : a ∈ digraph_value fuel seed deps y)
  : a ∈ digraph_value (S fuel) seed deps x.
Proof.
  simpl. eapply normalize_complete. eapply union_complete. right. rewrite in_flat_map. now exists y.
Qed.

Theorem digraph_value_sound {A : Type} `{EQ_DEC : hasEqDec A} (fuel : nat) (seed : X -> list A) (deps : X -> list X) (x : X) (a : A)
  (IN : a ∈ digraph_value fuel seed deps x)
  : digraph_closure seed deps a x.
Proof.
  revert x a IN. induction fuel as [ | fuel IH]; intros x a IN; simpl in IN.
  - eapply digraph_closure_seed. eapply normalize_sound. exact IN.
  - pose proof (normalize_sound _ _ IN) as IN'.
    pose proof (union_sound (seed x) (flat_map (digraph_value fuel seed deps) (deps x)) a IN') as [IN_SEED | IN_DEPS].
    + now eapply digraph_closure_seed.
    + rewrite in_flat_map in IN_DEPS. destruct IN_DEPS as (y & EDGE & IN_Y).
      eapply digraph_closure_step with (y := y); ss!.
Qed.

Lemma digraph_value_monotone_step {A : Type} `{EQ_DEC : hasEqDec A} (fuel : nat) (seed : X -> list A) (deps : X -> list X) (x : X) (a : A)
  (IN : a ∈ digraph_value fuel seed deps x)
  : a ∈ digraph_value (S fuel) seed deps x.
Proof.
  revert x a IN. induction fuel as [ | fuel IH]; intros x a IN; simpl in IN |- *.
  - eapply normalize_complete. eapply union_complete. left. now eapply normalize_sound.
  - pose proof (normalize_sound _ _ IN) as IN'.
    pose proof (union_sound (seed x) (flat_map (digraph_value fuel seed deps) (deps x)) a IN') as [IN_SEED | IN_DEPS].
    + eapply normalize_complete. eapply union_complete. left. exact IN_SEED.
    + rewrite in_flat_map in IN_DEPS. destruct IN_DEPS as (y & EDGE & IN_Y).
      eapply normalize_complete. eapply union_complete. right.
      rewrite in_flat_map. exists y. split; [exact EDGE | eapply IH; exact IN_Y].
Qed.

Lemma digraph_value_monotone {A : Type} `{EQ_DEC : hasEqDec A} (fuel1 : nat) (fuel2 : nat) (seed : X -> list A) (deps : X -> list X) (x : X) (a : A)
  (LE : fuel1 <= fuel2)
  (IN : a ∈ digraph_value fuel1 seed deps x)
  : a ∈ digraph_value fuel2 seed deps x.
Proof.
  revert fuel1 x a LE IN; induction fuel2 as [ | fuel2 IH]; intros fuel1 x a LE IN.
  - assert (fuel1 = O) as EQ by lia.
    subst fuel1. exact IN.
  - pose proof (Nat.eq_dec fuel1 (S fuel2)) as [EQ | NE].
    + subst fuel1. exact IN.
    + eapply digraph_value_monotone_step. eapply IH with (fuel1 := fuel1) (x := x) (a := a); done!.
Qed.

Theorem digraph_trace_value {A : Type} `{EQ_DEC : hasEqDec A} (seed : X -> list A) (deps : X -> list X) (x : X) (a : A) (trace : list X) (fuel : nat)
  (TRACE : trace \in digraph_trace seed deps a x)
  (LE : length trace <= fuel)
  : a ∈ digraph_value fuel seed deps x.
Proof.
  revert fuel LE; induction TRACE as [x IN | x y trace EDGE TRACE IH]; intros fuel LE.
  - now eapply digraph_value_seed.
  - destruct fuel as [ | fuel]; simpl in LE; [lia | eapply digraph_value_propagated]; done!.
Qed.

Theorem digraph_closure_complete {A : Type} `{EQ_DEC : hasEqDec A} (seed : X -> list A) (deps : X -> list X) (x : X) (a : A)
  (IN : digraph_closure seed deps a x)
  : exists fuel, a ∈ digraph_value fuel seed deps x.
Proof.
  induction IN as [x SEED_IN | x y EDGE CLOSURE IH].
  - exists O. eapply digraph_value_seed. exact SEED_IN.
  - destruct IH as [fuel VALUE_IN]. exists (S fuel). eapply digraph_value_propagated; eauto.
Qed.

Theorem digraph_closure_least {A : Type} (seed : X -> list A) (deps : X -> list X) (value : X -> list A) (x : X) (a : A)
  (EQUATION : digraph_equation seed deps value)
  (IN : digraph_closure seed deps a x)
  : a ∈ value x.
Proof.
  induction IN as [x SEED_IN | x y EDGE CLOSURE IH].
  - exact (proj2 (EQUATION x a) (or_introl SEED_IN)).
  - exact (proj2 (EQUATION x a) (or_intror (@ex_intro _ _ y (conj EDGE IH)))).
Qed.

#[local] Open Scope function_scope.

Definition digraph_fixedpoint {A : Type} (seed : X -> list A) (deps : X -> list X) (value' : X -> ensemble A) : Prop :=
  forall x, forall a, a \in value' x <-> ⟪ STEP : a ∈ seed x \/ (exists y, y ∈ deps x /\ a \in value' y) ⟫.

Theorem digraph_closure_fixedpoint {A : Type} (seed : X -> list A) (deps : X -> list X)
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

Theorem digraph_closure_least_fixedpoint {A : Type} (seed : X -> list A) (deps : X -> list X) (value : X -> ensemble A)
  (FIXPOINT : digraph_fixedpoint seed deps value)
  : forall x, { a : A | digraph_closure seed deps a x } \subseteq value x.
Proof.
  intros x a CLOSURE; induction CLOSURE as [x SEED_IN | x y EDGE CLOSURE IH]; ss!.
Qed.

Theorem digraph_closure_complete_bounded {A : Type} `{EQ_DEC : hasEqDec A} `{X_hasEqDec : hasEqDec X} (fuel : nat) (nodes : list X) (seed : X -> list A) (deps : X -> list X) (x : X) (a : A)
  (fuel_ENOUGH : length nodes <= fuel)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  (IN : digraph_closure seed deps a x)
  : a ∈ digraph_value fuel seed deps x.
Proof.
  rewrite digraph_closure_iff_trace in IN. destruct IN as [trace TRACE].
  pose proof (digraph_trace_simple_bounded nodes seed deps x a trace deps_CLOSED TRACE) as (simple & TRACE' & LENGTH).
  eapply digraph_trace_value with (trace := simple); ss!.
Qed.

Theorem digraph_value_iff_closure_bounded {A : Type} `{EQ_DEC : hasEqDec A} `{X_hasEqDec : hasEqDec X} (fuel : nat) (nodes : list X) (seed : X -> list A) (deps : X -> list X) (x : X) (a : A)
  (fuel_ENOUGH : length nodes <= fuel)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  : a ∈ digraph_value fuel seed deps x <-> digraph_closure seed deps a x.
Proof.
  split.
  - exact (digraph_value_sound fuel seed deps x a).
  - intros IN. eapply digraph_closure_complete_bounded; eauto.
Qed.

End DIGRAPH.

End DigraphFixedpoint.

Module API.

Infix "=~=" := is_similar_to.

#[projections(primitive)]
Class FiniteGraph : Type :=
  { G : GRAPH.t
  ; V_dec : hasEqDec G.(GRAPH.vertices)
  ; E_dec v v' : B.Decision ((v, v') \in G.(GRAPH.edges)) 
  ; enum_vertices : list G.(GRAPH.vertices)
  ; enum_vertices_all : enum_vertices =~= E.full
  } as GRAPH.

#[global] Existing Instance G.
#[global] Existing Instance V_dec.
#[global] Existing Instance E_dec.

Notation " src '~~~[' w ']~~>*('  GRAPH  ')' tgt " := (@walk GRAPH.(G) tgt src w).
Notation " src '---[' p ']-->*('  GRAPH  ')' tgt " := (@path GRAPH.(G) tgt src p).
Notation " src '===[' t ']==>*('  GRAPH  ')' tgt " := (@trail GRAPH.(G) tgt src t).

Notation gmu := (DigraphFixedpoint.gmu (G := G)).

Section EXPORT.

Context `{GRAPH : !FiniteGraph}.

#[local] Notation V := GRAPH.(G).(GRAPH.vertices).
#[local] Notation E := GRAPH.(G).(GRAPH.edges).

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
  eapply (Graph.path_implies_trail v v' p PATH).
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

Fixpoint reachableb_accum (fuel : nat) (v : V) (v' : V) {struct fuel} : bool :=
  match fuel with
  | O => eqb v v'
  | S fuel' => eqb v v' || L.existsb (fun v1 => if E_dec v v1 then reachableb_accum fuel' v1 v' else false) enum_vertices
  end.

Lemma reachableb_accum_sound (fuel : nat) (v : V) (v' : V)
  (REACHABLE : reachableb_accum fuel v v' = true)
  : exists w, L.length w <= fuel /\ v ~~~[ w ]~~>*( GRAPH ) v'.
Proof.
  exact (DigraphFixedpoint.reachableb_sound enum_vertices fuel v v' REACHABLE).
Qed.

Lemma reachableb_accum_complete (fuel : nat) (v : V) (v' : V) (w : list V)
  (WALK : v ~~~[ w ]~~>*( GRAPH ) v')
  (LENGTH : L.length w <= fuel)
  : reachableb_accum fuel v v' = true.
Proof.
  exact (DigraphFixedpoint.reachableb_complete enum_vertices enum_vertices_all fuel v v' w WALK LENGTH).
Qed.

Definition reachableb : forall v : V, forall v' : V, bool :=
  reachableb_accum (L.length enum_vertices).

Theorem reachableb_spec (v : V) (v' : V)
  : reachableb v v' = true <-> v' \in reachable v.
Proof.
  exact (DigraphFixedpoint.reachableb_iff_reachable enum_vertices enum_vertices_all v v').
Qed.

Definition reachable_impl (v : V) : list V :=
  L.filter (reachableb v) enum_vertices.

Theorem reachable_sim
  : forall v, reachable_impl v =~= reachable v.
Proof.
  exact (DigraphFixedpoint.reachable_sim enum_vertices enum_vertices_all).
Qed.

Section DIGRAPH.

#[local] Infix "\subseteq" := E.isSubsetOf.

Context {A : Type}.

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

Variable seed' : V -> list A.

Definition gmu' (v : V) : list A :=
  L.flat_map seed' (reachable_impl v).

Hypothesis seed_sim : forall v, seed' v =~= seed v.

Theorem gmu_sim
  : forall v, gmu' v =~= gmu seed v.
Proof.
  exact (DigraphFixedpoint.gmu_sim seed seed' seed_sim enum_vertices enum_vertices_all).
Qed.

End DIGRAPH.

End EXPORT.

Section DIGRAPH_FIXEDPOINT.

#[local] Infix "\subseteq" := E.isSubsetOf.

Context `{GRAPH : !FiniteGraph}.

#[local] Notation V := GRAPH.(G).(GRAPH.vertices).
#[local] Notation E := GRAPH.(G).(GRAPH.edges).

Definition deps (v : V) : list V :=
  L.filter (fun v' => if E_dec v v' then true else false) enum_vertices.

Lemma in_deps_iff (v : V) (v' : V)
  : In v' (deps v) <-> (v, v') \in G.(GRAPH.edges).
Proof.
  unfold deps. pose proof enum_vertices_all. rewrite L.filter_In. destruct (E_dec _ _) as [YES | NO]; ss!.
Qed.

#[local] Hint Rewrite in_deps_iff : simplication_hints.

Context {A : Type}.

Variable seed : V -> list A.

Definition digraph_cl (v : V) : ensemble A :=
  fun a => DigraphFixedpoint.digraph_closure seed deps a v.

Definition digraph_trace (v : V) : A -> list V -> Prop :=
  fun a => DigraphFixedpoint.digraph_trace seed deps a v.

Theorem digraph_cl_iff_digraph_trace (v : V) (a : A)
  : a \in digraph_cl v <-> (exists trace, trace \in digraph_trace v a).
Proof.
  exact (DigraphFixedpoint.digraph_closure_iff_trace seed deps v a).
Qed.

Lemma digraph_trace_seed_at_last (v : V) (a : A) (trace : list V)
  (TRACE : trace \in digraph_trace v a)
  : L.In a (seed (last trace v)).
Proof.
  eapply DigraphFixedpoint.digraph_trace_seed_at_last; eauto.
Qed.

#[local] Hint Constructors walk : core.
#[local] Hint Rewrite @L.last_cons : simplication_hints.

Lemma digraph_trace_walk (v : V) (a : A) (trace : list V)
  (TRACE : trace \in digraph_trace v a)
  : v ~~~[ trace ]~~>*( GRAPH ) L.last trace v.
Proof.
  induction TRACE as [x IN | x y trace EDGE TRACE IH]; ss!.
Qed.

Lemma digraph_trace_simple (v : V) (a : A) (trace : list V)
  (TRACE : trace \in digraph_trace v a)
  : exists simple, simple \in digraph_trace v a /\ NoDup simple.
Proof.
  eapply DigraphFixedpoint.digraph_trace_simple; eauto.
Qed.

#[local] Infix "∈" := L.In.

Lemma digraph_trace_in_nodes (nodes : list V) (v : V) (a : A) (trace : list V)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  (TRACE : trace \in digraph_trace v a)
  : Forall (fun y => y ∈ nodes) trace.
Proof.
  induction TRACE as [x IN | x y trace EDGE TRACE IH]; [econs 1 | econs 2]; eauto.
Qed.

Lemma digraph_trace_simple_bounded (nodes : list V) (v : V) (a : A) (trace : list V)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  (TRACE : trace \in digraph_trace v a)
  : exists simple, simple \in digraph_trace v a /\ length simple <= length nodes.
Proof.
  pose proof (digraph_trace_simple v a trace TRACE) as (simple & TRACE' & NO_DUP).
  pose proof (digraph_trace_in_nodes nodes v a simple deps_CLOSED TRACE') as IN_NODES.
  exists simple. split; trivial. eapply L.NoDup_incl_length; [exact NO_DUP | intros y IN].
  rewrite Forall_forall in IN_NODES. now eapply IN_NODES.
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

Fixpoint digraph_cl_accum (fuel : nat) (v : V) : list A :=
  match fuel with
  | O => normalize (seed v)
  | S fuel' => normalize (union (seed v) (flat_map (digraph_cl_accum fuel') (deps v)))
  end.

Lemma seed_incl_digraph_cl_accum (fuel : nat) (v : V) (a : A)
  (IN : a ∈ seed v)
  : a ∈ digraph_cl_accum fuel v.
Proof.
  destruct fuel as [ | fuel]; simpl; eapply normalize_complete; auto.
  now eapply union_complete; left.
Qed.

Lemma digraph_cl_accum_propagated (fuel : nat) (v : V) (v' : V) (a : A)
  (EDGE : v' ∈ deps v)
  (IN : a ∈ digraph_cl_accum fuel v')
  : a ∈ digraph_cl_accum (S fuel) v.
Proof.
  simpl. eapply normalize_complete. eapply union_complete. right. rewrite in_flat_map. now exists v'.
Qed.

Theorem digraph_cl_accum_sound (fuel : nat) (v : V) (a : A)
  (IN : a ∈ digraph_cl_accum fuel v)
  : a \in digraph_cl v.
Proof.
  revert v a IN. induction fuel as [ | fuel IH]; intros x a IN; simpl in IN.
  - eapply DigraphFixedpoint.digraph_closure_seed. eapply normalize_sound. exact IN.
  - pose proof (normalize_sound _ _ IN) as IN'.
    pose proof (union_sound (seed x) (flat_map (digraph_cl_accum fuel) (deps x)) a IN') as [IN_SEED | IN_DEPS].
    + now eapply DigraphFixedpoint.digraph_closure_seed.
    + rewrite in_flat_map in IN_DEPS. destruct IN_DEPS as (y & EDGE & IN_Y).
      eapply DigraphFixedpoint.digraph_closure_step with (y := y); ss!.
Qed.

Lemma digraph_cl_accum_monotone_1 (fuel : nat) (v : V) (a : A)
  (IN : a ∈ digraph_cl_accum fuel v)
  : a ∈ digraph_cl_accum (S fuel) v.
Proof.
  revert v a IN. induction fuel as [ | fuel IH]; intros x a IN; simpl in IN |- *.
  - eapply normalize_complete. eapply union_complete. left. now eapply normalize_sound.
  - pose proof (normalize_sound _ _ IN) as IN'.
    pose proof (union_sound (seed x) (flat_map (digraph_cl_accum fuel) (deps x)) a IN') as [IN_SEED | IN_DEPS].
    + eapply normalize_complete. eapply union_complete. left. exact IN_SEED.
    + rewrite in_flat_map in IN_DEPS. destruct IN_DEPS as (y & EDGE & IN_Y).
      eapply normalize_complete. eapply union_complete. right.
      rewrite in_flat_map. exists y. split; [exact EDGE | eapply IH; exact IN_Y].
Qed.

Lemma digraph_cl_accum_monotone (fuel : nat) (fuel' : nat) (v : V) (a : A)
  (LE : fuel <= fuel')
  (IN : a ∈ digraph_cl_accum fuel v)
  : a ∈ digraph_cl_accum fuel' v.
Proof.
  revert fuel v a LE IN; induction fuel' as [ | fuel2 IH]; intros fuel1 x a LE IN.
  - assert (fuel1 = O) as EQ by lia.
    subst fuel1. exact IN.
  - pose proof (Nat.eq_dec fuel1 (S fuel2)) as [EQ | NE].
    + subst fuel1. exact IN.
    + eapply digraph_cl_accum_monotone_1. eapply IH with (fuel := fuel1) (v := x) (a := a); done!.
Qed.

Theorem digraph_trace_value (v : V) (a : A) (trace : list V) (fuel : nat)
  (TRACE : trace \in digraph_trace v a)
  (LE : length trace <= fuel)
  : a ∈ digraph_cl_accum fuel v.
Proof.
  revert fuel LE; induction TRACE as [x IN | x y trace EDGE TRACE IH]; intros fuel LE.
  - now eapply seed_incl_digraph_cl_accum.
  - destruct fuel as [ | fuel]; simpl in LE; [lia | eapply digraph_cl_accum_propagated]; done!.
Qed.

Theorem digraph_cl_complete (v : V) (a : A)
  (IN : a \in digraph_cl v)
  : exists fuel, a ∈ digraph_cl_accum fuel v.
Proof.
  induction IN as [x SEED_IN | x y EDGE CLOSURE IH].
  - exists O. eapply seed_incl_digraph_cl_accum. exact SEED_IN.
  - destruct IH as [fuel VALUE_IN]. exists (S fuel). eapply digraph_cl_accum_propagated; eauto.
Qed.

Theorem digraph_cl_complete_bounded (fuel : nat) (nodes : list V) (v : V) (a : A)
  (fuel_ENOUGH : length nodes <= fuel)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  (IN : a \in digraph_cl v)
  : a ∈ digraph_cl_accum fuel v.
Proof.
  rewrite digraph_cl_iff_digraph_trace in IN. destruct IN as [trace TRACE].
  pose proof (digraph_trace_simple_bounded nodes v a trace deps_CLOSED TRACE) as (simple & TRACE' & LENGTH).
  eapply digraph_trace_value with (trace := simple); ss!.
Qed.

Corollary digraph_cl_accum_spec (fuel : nat) (nodes : list V) (v : V) (a : A)
  (fuel_ENOUGH : length nodes <= fuel)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  : a ∈ digraph_cl_accum fuel v <-> a \in digraph_cl v.
Proof.
  split.
  - exact (digraph_cl_accum_sound fuel v a).
  - intros IN. eapply digraph_cl_complete_bounded; eauto.
Qed.

Definition digraph_cl_impl (v : V) : list A :=
  digraph_cl_accum (length enum_vertices) v.

Theorem digraph_cl_impl_spec (v : V)
  : forall a, a ∈ digraph_cl_impl v <-> a \in digraph_cl v.
Proof.
  i. eapply digraph_cl_accum_spec with (nodes := enum_vertices).
  - lia.
  - ii; pose proof enum_vertices_all; ss!.
Qed.

Corollary digraph_cl_sim
  : forall v, digraph_cl_impl v =~= digraph_cl v.
Proof.
  i. s!. eapply digraph_cl_impl_spec with (v := v).
Qed.

End DIGRAPH_FIXEDPOINT.

End API.
