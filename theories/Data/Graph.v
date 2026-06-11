Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Category.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Data.FiniteMap.

#[local] Notation In := L.In.
#[local] Infix "\in" := E.In : type_scope.

Module GRAPH.

#[projections(primitive)]
Record t : Type :=
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
  (PATH1 : v1 ~~~[ vs1 ]~~> v2)
  (PATH2 : v2 ~~~[ vs2 ]~~> v)
  : v1 ~~~[ vs1 ++ vs2 ]~~> v.
Proof.
  revert v1 v2 v vs2 PATH1 PATH2. induction vs1 as [ | v vs1 IH]; simpl; i; inv PATH1; eauto.
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

Fixpoint labeledWalk {G} {G_labeled : Labeled G} {v} {v'} (H_Walk : `[ v -> v' ]) : ensemble (list G_labeled.(labels)) :=
  match H_Walk with
  | Walk_nil => pure (@L.nil G_labeled.(labels))
  | Walk_cons H_edge H_Walk' => liftM2 (@L.cons G_labeled.(labels)) (G_labeled.(labeling) H_edge) (labeledWalk H_Walk')
  end.

Module DigraphFixedpoint.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.

Section DIGRAPH_FIXEDPOINT.

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

Hypothesis seed_sim : forall v : V, seed' v =~= seed v.

Variable vertices' : list V.

Hypothesis vertices_sim : vertices' =~= E.full.

Lemma vertices'_complete (v : V)
  : L.In v vertices'.
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
    + rewrite L.existsb_exists in REACH.
      destruct REACH as [z [z_in REACH]].
      destruct (E_dec x z) as [EDGE | NO_EDGE]; try discriminate.
      pose proof (IH z y REACH) as [w [LENGTH WALK]].
      exists (z :: w). split; [simpl; lia | econstructor; eauto].
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
    pose proof (reachableb_sound _ _ _ REACH) as [w [_ WALK]].
    exists w. exact WALK.
  - intros [w WALK].
    pose proof (@walk_finds_path G (fun v => fun vs => match @L.in_dec V V_dec v vs with left H_in => or_introl H_in | right H_not_in => or_intror H_not_in end) x y w WALK) as [p PATH].
    rewrite path_iff_no_dup_walk in PATH.
    destruct PATH as [WALK' NO_DUP].
    eapply reachableb_complete; [exact WALK' | ].
    eapply L.NoDup_incl_length; [exact NO_DUP | ].
    intros z z_in. eapply vertices'_complete.
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
  induction WALK as [ | v0 v1 w EDGE WALK IH]; intros a IN; eauto.
  eapply gmu_propagated; eauto.
Qed.

Lemma reachable_seed_gmu (x : V) (y : V) (a : A)
  (REACH : y \in reachable x)
  (SEED : a \in seed y)
  : a \in gmu x.
Proof.
  destruct REACH as [w WALK].
  eapply walk_gmu; [exact WALK | ].
  eapply gmu_seed. exact SEED.
Qed.

Lemma reachable_step (x : V) (y : V) (z : V)
  (EDGE : (x, y) \in E)
  (REACH : z \in reachable y)
  : z \in reachable x.
Proof.
  destruct REACH as [w WALK].
  exists (y :: w). econstructor; eauto.
Qed.

Lemma gmu_reachable_seed (x : V) (a : A)
  (IN : a \in gmu x)
  : exists y, y \in reachable x /\ a \in seed y.
Proof.
  induction IN as [x a SEED | x y EDGE a IN IH].
  - exists x. split; [exists []; econstructor 1 | exact SEED].
  - destruct IH as [z [REACH SEED]].
    exists z. split; [eapply reachable_step; eauto | exact SEED].
Qed.

Lemma gmu_iff_reachable_seed (x : V) (a : A)
  : a \in gmu x <-> a \in (reachable x >>= seed).
Proof.
  split.
  - eapply gmu_reachable_seed.
  - intros [y [REACH SEED]]. eapply reachable_seed_gmu; eauto.
Qed.

Definition gmu' (x : V) : list A :=
  L.flat_map seed' (reachable' x).

Theorem gmu_sim (v : V)
  : gmu' v =~= gmu v.
Proof.
  pose proof (list_corresponds_to_finite_ensemble_flat_map (reachable' v) (reachable v) seed' seed (reachable_sim v) seed_sim) as FLAT_MAP.
  rewrite list_corresponds_to_finite_ensemble_iff in FLAT_MAP |- *.
  intros a. rewrite FLAT_MAP. symmetry. eapply gmu_iff_reachable_seed.
Qed.

End DIGRAPH_FIXEDPOINT.

Section DIGRAPH.

#[local] Infix "\in" := E.In.
#[local] Infix "∈" := L.In.

Context {X : Type}.

Fixpoint digraph_value {A : Type} `{EQ_DEC : hasEqDec A} (fuel : nat) (seed : X -> list A) (deps : X -> list X) (x : X) : list A :=
  match fuel with
  | O => normalize (seed x)
  | S fuel' => normalize (union (seed x) (flat_map (digraph_value fuel' seed deps) (deps x)))
  end.

Inductive digraph_closure {A : Type} (seed : X -> list A) (deps : X -> list X) (x : X) : A -> Prop :=
  | digraph_closure_seed a
    (IN : a ∈ seed x)
    : digraph_closure seed deps x a
  | digraph_closure_step y a
    (EDGE : y ∈ deps x)
    (IN : digraph_closure seed deps y a)
    : digraph_closure seed deps x a.

Inductive digraph_trace {A : Type} (seed : X -> list A) (deps : X -> list X) : X -> A -> list X -> Prop :=
  | digraph_trace_seed x a
    (IN : a ∈ seed x)
    : digraph_trace seed deps x a []
  | digraph_trace_step x y a trace
    (EDGE : y ∈ deps x)
    (TRACE : digraph_trace seed deps y a trace)
    : digraph_trace seed deps x a (y :: trace).

Lemma digraph_trace_sound {A : Type} (seed : X -> list A) (deps : X -> list X) (x : X) (a : A) (trace : list X)
  (TRACE : digraph_trace seed deps x a trace)
  : digraph_closure seed deps x a.
Proof.
  induction TRACE as [x a IN | x y a trace EDGE TRACE IH].
  - eapply digraph_closure_seed. exact IN.
  - eapply digraph_closure_step; eauto.
Qed.

Lemma digraph_closure_trace {A : Type} (seed : X -> list A) (deps : X -> list X) (x : X) (a : A)
  (IN : digraph_closure seed deps x a)
  : exists trace, digraph_trace seed deps x a trace.
Proof.
  induction IN as [x a IN | x y a EDGE IN IH].
  - exists []. eapply digraph_trace_seed. exact IN.
  - destruct IH as [trace TRACE]. exists (y :: trace).
    eapply digraph_trace_step; eauto.
Qed.

Theorem digraph_closure_iff_trace {A : Type} (seed : X -> list A) (deps : X -> list X) (x : X) (a : A)
  : digraph_closure seed deps x a <-> (exists trace, digraph_trace seed deps x a trace).
Proof.
  split.
  - eapply digraph_closure_trace.
  - intros [trace TRACE]. eapply digraph_trace_sound. exact TRACE.
Qed.

Lemma digraph_trace_in_nodes {A : Type} (nodes : list X) (seed : X -> list A) (deps : X -> list X) (x : X) (a : A) (trace : list X)
  (DEPS_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  (TRACE : digraph_trace seed deps x a trace)
  : Forall (fun y => y ∈ nodes) trace.
Proof.
  induction TRACE as [x a IN | x y a trace EDGE TRACE IH].
  - constructor.
  - constructor; [eapply DEPS_CLOSED; exact EDGE | exact IH].
Qed.

Definition digraph_graph (deps : X -> list X) : GRAPH.t :=
  {|
    GRAPH.vertices := X;
    GRAPH.edges := fun '(x, y) => y ∈ deps x;
  |}.

Lemma digraph_trace_seed_at_last {A : Type} (seed : X -> list A) (deps : X -> list X) (x : X) (a : A) (trace : list X)
  (TRACE : digraph_trace seed deps x a trace)
  : a ∈ seed (last trace x).
Proof.
  induction TRACE as [x a IN | x y a trace EDGE TRACE IH].
  - exact IN.
  - rewrite L.last_cons. exact IH.
Qed.

Lemma digraph_trace_walk {A : Type} (seed : X -> list A) (deps : X -> list X) (x : X) (a : A) (trace : list X)
  (TRACE : digraph_trace seed deps x a trace)
  : @walk (digraph_graph deps) (last trace x) x trace.
Proof.
  induction TRACE as [x a IN | x y a trace EDGE TRACE IH].
  - constructor.
  - rewrite L.last_cons. econstructor; eauto.
Qed.

Lemma digraph_walk_trace {A : Type} (seed : X -> list A) (deps : X -> list X) (x : X) (a : A) (target : X) (trace : list X)
  (WALK : @walk (digraph_graph deps) target x trace)
  (IN : a ∈ seed target)
  : digraph_trace seed deps x a trace.
Proof.
  induction WALK as [ | v0 v1 w EDGE WALK IH].
  - constructor. exact IN.
  - econstructor; [exact EDGE | exact IH].
Qed.

Lemma digraph_trace_simple {A : Type} `{X_hasEqDec : hasEqDec X} (seed : X -> list A) (deps : X -> list X) (x : X) (a : A) (trace : list X)
  (TRACE : digraph_trace seed deps x a trace)
  : exists simple, digraph_trace seed deps x a simple /\ NoDup simple.
Proof.
  pose proof (digraph_trace_walk seed deps x a trace TRACE) as WALK.
  pose proof (digraph_trace_seed_at_last seed deps x a trace TRACE) as SEED.
  pose proof (@walk_finds_path (digraph_graph deps) (fun v => fun vs => match @L.in_dec X X_hasEqDec v vs with left H => or_introl H | right H => or_intror H end) x (last trace x) trace WALK) as [simple PATH].
  rewrite path_iff_no_dup_walk in PATH. destruct PATH as [WALK' NO_DUP].
  exists simple. split; [ | exact NO_DUP].
  eapply digraph_walk_trace; eauto.
Qed.

Lemma digraph_trace_simple_bounded {A : Type} `{X_hasEqDec : hasEqDec X} (nodes : list X) (seed : X -> list A) (deps : X -> list X) (x : X) (a : A) (trace : list X)
  (DEPS_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  (TRACE : digraph_trace seed deps x a trace)
  : exists simple, digraph_trace seed deps x a simple /\ length simple <= length nodes.
Proof.
  destruct (digraph_trace_simple seed deps x a trace TRACE) as [simple [TRACE' NO_DUP]].
  exists simple. split; [exact TRACE' | ].
  pose proof (digraph_trace_in_nodes nodes seed deps x a simple DEPS_CLOSED TRACE') as IN_NODES.
  eapply L.NoDup_incl_length; [exact NO_DUP | ].
  intros y IN. rewrite Forall_forall in IN_NODES. eapply IN_NODES. exact IN.
Qed.

Definition digraph_equation {A : Type} (seed : X -> list A) (deps : X -> list X) (value : X -> list A) : Prop :=
  forall x, forall a, a ∈ value x <-> (a ∈ seed x \/ (exists y, y ∈ deps x /\ a ∈ value y)).

Definition digraph_least_solution {A : Type} (seed : X -> list A) (deps : X -> list X) (value : X -> list A) : Prop :=
  digraph_equation seed deps value /\ (forall value', digraph_equation seed deps value' -> forall x, forall a, a ∈ value x -> a ∈ value' x).

Variant DIGRAPH_SPEC {A : Type} (seed : X -> list A) (deps : X -> list X) (value : X -> list A) : Prop :=
  | DIGRAPH_SPEC_intro
    (EQUATION : digraph_equation seed deps value)
    (LEAST : forall value', digraph_equation seed deps value' -> forall x, forall a, a ∈ value x -> a ∈ value' x).

Lemma digraph_value_seed {A : Type} `{EQ_DEC : hasEqDec A} (fuel : nat) (seed : X -> list A) (deps : X -> list X) (x : X) (a : A)
  (IN : a ∈ seed x)
  : a ∈ digraph_value fuel seed deps x.
Proof.
  destruct fuel as [ | fuel]; simpl.
  - eapply normalize_complete. exact IN.
  - eapply normalize_complete. eapply union_complete. left. exact IN.
Qed.

Lemma digraph_value_propagated {A : Type} `{EQ_DEC : hasEqDec A} (fuel : nat) (seed : X -> list A) (deps : X -> list X) (x : X) (y : X) (a : A)
  (EDGE : y ∈ deps x)
  (IN : a ∈ digraph_value fuel seed deps y)
  : a ∈ digraph_value (S fuel) seed deps x.
Proof.
  simpl. eapply normalize_complete. eapply union_complete. right.
  rewrite in_flat_map. exists y. split; eauto.
Qed.

Theorem digraph_value_sound {A : Type} `{EQ_DEC : hasEqDec A} (fuel : nat) (seed : X -> list A) (deps : X -> list X) (x : X) (a : A)
  (IN : a ∈ digraph_value fuel seed deps x)
  : digraph_closure seed deps x a.
Proof.
  revert x a IN. induction fuel as [ | fuel IH]; intros x a IN; simpl in IN.
  - eapply digraph_closure_seed. eapply normalize_sound. exact IN.
  - pose proof (normalize_sound _ _ IN) as IN'.
    pose proof (union_sound (seed x) (flat_map (digraph_value fuel seed deps) (deps x)) a IN') as [IN_SEED | IN_DEPS].
    + eapply digraph_closure_seed. exact IN_SEED.
    + rewrite in_flat_map in IN_DEPS. destruct IN_DEPS as (y & EDGE & IN_Y).
      eapply digraph_closure_step; eauto.
Qed.

Lemma digraph_value_monotone_step {A : Type} `{EQ_DEC : hasEqDec A} (fuel : nat) (seed : X -> list A) (deps : X -> list X) (x : X) (a : A)
  (IN : a ∈ digraph_value fuel seed deps x)
  : a ∈ digraph_value (S fuel) seed deps x.
Proof.
  revert x a IN. induction fuel as [ | fuel IH]; intros x a IN; simpl in IN |- *.
  - eapply normalize_complete. eapply union_complete. left.
    eapply normalize_sound. exact IN.
  - pose proof (normalize_sound _ _ IN) as IN'.
    pose proof (union_sound (seed x) (flat_map (digraph_value fuel seed deps) (deps x)) a IN') as [IN_SEED | IN_DEPS].
    + eapply normalize_complete. eapply union_complete. left. exact IN_SEED.
    + rewrite in_flat_map in IN_DEPS. destruct IN_DEPS as (y & EDGE & IN_Y).
      eapply normalize_complete. eapply union_complete. right.
      rewrite in_flat_map. exists y. split; [exact EDGE | ].
      eapply IH. exact IN_Y.
Qed.

Lemma digraph_value_monotone {A : Type} `{EQ_DEC : hasEqDec A} (fuel1 : nat) (fuel2 : nat) (seed : X -> list A) (deps : X -> list X) (x : X) (a : A)
  (LE : fuel1 <= fuel2)
  (IN : a ∈ digraph_value fuel1 seed deps x)
  : a ∈ digraph_value fuel2 seed deps x.
Proof.
  revert fuel1 x a LE IN. induction fuel2 as [ | fuel2 IH]; intros fuel1 x a LE IN.
  - assert (fuel1 = O) by lia. subst fuel1. exact IN.
  - destruct (Nat.eq_dec fuel1 (S fuel2)) as [EQ | NE].
    + subst fuel1. exact IN.
    + eapply digraph_value_monotone_step. eapply (IH fuel1 x a).
      * lia.
      * exact IN.
Qed.

Theorem digraph_trace_value {A : Type} `{EQ_DEC : hasEqDec A} (seed : X -> list A) (deps : X -> list X) (x : X) (a : A) (trace : list X) (fuel : nat)
  (TRACE : digraph_trace seed deps x a trace)
  (LE : length trace <= fuel)
  : a ∈ digraph_value fuel seed deps x.
Proof.
  revert fuel LE. induction TRACE as [x a IN | x y a trace EDGE TRACE IH]; intros fuel LE.
  - eapply digraph_value_seed. exact IN.
  - destruct fuel as [ | fuel]; simpl in LE; [lia | ].
    eapply digraph_value_propagated; [exact EDGE | ].
    eapply IH. lia.
Qed.

Theorem digraph_closure_complete {A : Type} `{EQ_DEC : hasEqDec A} (seed : X -> list A) (deps : X -> list X) (x : X) (a : A)
  (IN : digraph_closure seed deps x a)
  : exists fuel, a ∈ digraph_value fuel seed deps x.
Proof.
  induction IN as [x a SEED_IN | x y a EDGE CLOSURE IH].
  - exists O. eapply digraph_value_seed. exact SEED_IN.
  - destruct IH as [fuel VALUE_IN]. exists (S fuel).
    eapply digraph_value_propagated; eauto.
Qed.

Theorem digraph_closure_least {A : Type} (seed : X -> list A) (deps : X -> list X) (value : X -> list A)
  (EQUATION : digraph_equation seed deps value)
  : forall x, forall a, digraph_closure seed deps x a -> a ∈ value x.
Proof.
  intros x a IN. induction IN as [x a SEED_IN | x y a EDGE CLOSURE IH].
  - apply (proj2 (EQUATION x a)). left. exact SEED_IN.
  - apply (proj2 (EQUATION x a)). right. exists y. split; [exact EDGE | exact IH].
Qed.

End DIGRAPH.

End DigraphFixedpoint.
