Require Import Stdlib.NArith.BinNat.
Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Category.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Data.FiniteMap.
Require Import PnV.Prelude.X.

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
  - find* (p'&PATH1&p''&PATH2&EQ) by IH.
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
    + find* (p'&PATH'&_) by (mk_subpath _ _ _ _ PATH). ss!.
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

Definition Similarity_list_ensemble {A : Type} {A' : Type} (Sim_A_A' : Similarity A A') : Similarity (list A) (ensemble A') :=
  fun xs : list A => fun X' : ensemble A' => forall x : A, forall x' : A', is_similar_to (Similarity := Sim_A_A') x x' -> (In x xs <-> x' \in X').

#[local]
Instance list_corresponds_to_finite_ensemble {A : Type} : Similarity (list A) (ensemble A) :=
  Similarity_list_ensemble eq.

Lemma list_corresponds_to_finite_ensemble_iff {A : Type} (xs : list A) (X : ensemble A)
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) xs X <-> (forall x : A, In x xs <-> x \in X).
Proof.
  split.
  - intros SIM x. exact (SIM x x eq_refl).
  - intros H_iff x x' x_eq_x'. change (x = x') in x_eq_x'. subst x'. exact (H_iff x).
Qed.

Lemma in_ensemble_bind_iff {A : Type} {B : Type} (X : ensemble A) (F : A -> ensemble B) (b : B)
  : b \in (X >>= F) <-> (exists x : A, x \in X /\ b \in F x).
Proof.
  reflexivity.
Qed.

Theorem list_corresponds_to_finite_ensemble_flat_map {A : Type} {B : Type} (xs : list A) (X : ensemble A) (f : A -> list B) (F : A -> ensemble B)
  (xs_sim : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) xs X)
  (f_sim : forall x : A, In x xs -> is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (f x) (F x))
  : is_similar_to (Similarity := list_corresponds_to_finite_ensemble) (L.flat_map f xs) (X >>= F).
Proof.
  pose proof (proj1 (list_corresponds_to_finite_ensemble_iff xs X) xs_sim) as xs_iff.
  eapply (proj2 (list_corresponds_to_finite_ensemble_iff (L.flat_map f xs) (X >>= F))).
  intros b. rewrite L.in_flat_map, in_ensemble_bind_iff. split.
  - intros (x & x_in & b_in).
    pose proof (proj1 (list_corresponds_to_finite_ensemble_iff (f x) (F x)) (f_sim x x_in)) as fx_iff.
    exists x. split; [rewrite <- xs_iff | rewrite <- fx_iff]; assumption.
  - intros (x & x_in & b_in).
    assert (x_in' : In x xs) by now rewrite xs_iff.
    pose proof (proj1 (list_corresponds_to_finite_ensemble_iff (f x) (F x)) (f_sim x x_in')) as fx_iff.
    exists x. split; [exact x_in' | rewrite fx_iff; exact b_in].
Qed.

#[local] Hint Rewrite @L.last_cons : simplication_hints.
#[local] Hint Constructors walk : simplication_hints.
#[local] Hint Constructors path : simplication_hints.

Section DIGRAPH.

#[local] Notation " src '~~~[' w ']~~>*('  G  ')' tgt " := (@walk G tgt src w).
#[local] Notation " src '---[' p ']-->*('  G  ')' tgt " := (@path G tgt src p).
#[local] Notation " src '===[' t ']==>*('  G  ')' tgt " := (@trail G tgt src t).

#[local] Infix "\in" := E.In.
#[local] Notation "x '∈' X" := (L.In x X.(FSet.data)) (at level 70, no associativity) : type_scope.

Context {X : Type} {POSET_X : isPoset X} {HsOrd_X : HsOrd X (POSET := POSET_X)}.
Context {A : Type} {POSET_A : isPoset A} {HsOrd_A : HsOrd A (POSET := POSET_A)}.

Definition propagate_graph (deps : X -> fset X) : GRAPH.t :=
  {|
    GRAPH.vertices := X;
    GRAPH.edges := fun '(x, x') => x' ∈ deps x;
  |}.

Variable seed : X -> fset A.
Variable deps : X -> fset X.

Inductive propagate_closure (a : A) (x : X) : Prop :=
  | propagate_closure_seed
    (IN : a ∈ seed x)
    : x \in propagate_closure a
  | propagate_closure_step y
    (EDGE : y ∈ deps x)
    (IN : y \in propagate_closure a)
    : x \in propagate_closure a.

Inductive propagate_trace (a : A) (x : X) : list X -> Prop :=
  | propagate_trace_seed
    (IN : a ∈ seed x)
    : propagate_trace a x []
  | propagate_trace_step y tr
    (EDGE : y ∈ deps x)
    (TRACE : propagate_trace a y tr)
    : propagate_trace a x (y :: tr).

Theorem propagate_closure_iff_trace (x : X) (a : A)
  : x \in propagate_closure a <-> (exists tr, propagate_trace a x tr).
Proof.
  split.
  - intros IN. induction IN as [x IN | x y EDGE IN IH].
    + exists []. eapply propagate_trace_seed. exact IN.
    + destruct IH as [tr TRACE]. exists (y :: tr). eapply propagate_trace_step; eauto.
  - intros [tr TRACE]. induction TRACE as [x IN | x y tr EDGE TRACE IH].
    + eapply propagate_closure_seed; eauto.
    + eapply propagate_closure_step; eauto.
Qed.

Lemma propagate_trace_in_nodes (nodes : fset X) (x : X) (a : A) (tr : list X)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  (TRACE : propagate_trace a x tr)
  : Forall (fun y => y ∈ nodes) tr.
Proof.
  induction TRACE as [x IN | x y tr EDGE TRACE IH]; [econs 1 | econs 2]; eauto.
Qed.

Lemma propagate_trace_seed_at_last (x : X) (a : A) (tr : list X)
  (TRACE : propagate_trace a x tr)
  : a ∈ seed (last tr x).
Proof.
  induction TRACE as [x IN | x y tr EDGE TRACE IH]; ss!.
Qed.

Lemma propagate_trace_walk (x : X) (a : A) (tr : list X)
  (TRACE : propagate_trace a x tr)
  : x ~~~[ tr ]~~>*( propagate_graph deps ) last tr x.
Proof.
  induction TRACE as [x IN | x y tr EDGE TRACE IH]; ss!.
Qed.

Lemma propagate_walk_trace (x : X) (a : A) (x' : X) (tr : list X)
  (WALK : x ~~~[ tr ]~~>*( propagate_graph deps ) x')
  (IN : a ∈ seed x')
  : propagate_trace a x tr.
Proof.
  induction WALK as [ | v0 v1 w EDGE WALK IH]; now constructor.
Qed.

Lemma propagate_trace_simple (x : X) (a : A) (tr : list X)
  (TRACE : propagate_trace a x tr)
  : exists simple, propagate_trace a x simple /\ NoDup simple.
Proof.
  pose proof (propagate_trace_walk x a tr TRACE) as WALK.
  pose proof (propagate_trace_seed_at_last x a tr TRACE) as SEED.
  assert (exists simple : list GRAPH.vertices, x ---[ simple ]-->*( propagate_graph deps ) last tr x) as [simple PATH].
  { eapply walk_finds_path with (w := tr); auto. intros v vs.
    now pose proof (@L.in_dec X (HsOrd_implies_EqDec HsOrd_X) v vs) as [YES | NO]; [left | right].
  }
  rewrite path_iff_no_dup_walk in PATH. destruct PATH as [WALK' NO_DUP].
  find* ? by (propagate_walk_trace _ _ _ simple). ss!.
Qed.

Lemma propagate_trace_simple_bounded (nodes : fset X) (x : X) (a : A) (tr : list X)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  (TRACE : propagate_trace a x tr)
  : exists simple, propagate_trace a x simple /\ length simple <= length nodes.(FSet.data).
Proof.
  pose proof (propagate_trace_simple x a tr TRACE) as (simple & TRACE' & NO_DUP).
  pose proof (propagate_trace_in_nodes nodes x a simple deps_CLOSED TRACE') as IN_NODES.
  exists simple. split; trivial. eapply L.NoDup_incl_length; [exact NO_DUP | intros y IN].
  rewrite Forall_forall in IN_NODES. now eapply IN_NODES.
Qed.

Definition propagate_equation (value : X -> fset A) : Prop :=
  forall x, forall a, a ∈ value x <-> ⟪ UNFOLD : a ∈ seed x \/ (exists y, y ∈ deps x /\ a ∈ value y) ⟫.

#[local] Open Scope function_scope.

Definition propagate_fixedpoint (value' : X -> ensemble A) : Prop :=
  forall x, forall a, a \in value' x <-> ⟪ STEP : a ∈ seed x \/ (exists y, y ∈ deps x /\ a \in value' y) ⟫.

Theorem propagate_closure_fixedpoint
  : propagate_fixedpoint (fun x => { a : A | x \in propagate_closure a }).
Proof.
  intros x a. unfold E.In; unnw. split.
  - intros CLOSURE. destruct CLOSURE as [SEED_IN | y EDGE CLOSURE].
    + now left.
    + now right; exists y.
  - intros [SEED_IN | (y & EDGE & CLOSURE)].
    + now eapply propagate_closure_seed.
    + now eapply propagate_closure_step with (y := y).
Qed.

Theorem propagate_closure_least_fixedpoint (value : X -> ensemble A)
  (FIXPOINT : propagate_fixedpoint value)
  : forall x, { a : A | propagate_closure a x } \subseteq value x.
Proof.
  intros x a CLOSURE; induction CLOSURE as [x SEED_IN | x y EDGE CLOSURE IH]; ss!.
Qed.

Theorem propagate_closure_least (value : X -> fset A) (x : X) (a : A)
  (EQUATION : propagate_equation value)
  (IN : x \in propagate_closure a)
  : a ∈ value x.
Proof.
  induction IN as [x SEED_IN | x y EDGE CLOSURE IH].
  - exact (proj2 (EQUATION x a) (or_introl SEED_IN)).
  - exact (proj2 (EQUATION x a) (or_intror (@ex_intro _ _ y (conj EDGE IH)))).
Qed.

Section KLEENE.

Definition table : Type :=
  fpmap X (fset A).

Definition tableGet (m : table) (x : X) : fset A :=
  match lookup x m with
  | Some Y => Y
  | None => FS.empty
  end.

Definition tableStep (m : table) (x : X) : fset A :=
  FS.union (seed x) (FS.bind (deps x) (tableGet m)).

Fixpoint tableBuild (F : X -> fset A) (xs : list X) {struct xs} : table :=
  match xs with
  | [] => empty
  | x :: xs' => insert x (F x) (tableBuild F xs')
  end.

Lemma tableBuild_fold (F : X -> fset A) (xs : list X)
  : tableBuild F xs =
    L.fold_right (fun x => fun m => insert x (F x) m) empty xs.
Proof.
  induction xs as [ | x xs IH]; cbn [tableBuild L.fold_right];
    [reflexivity | now rewrite IH].
Qed.

Lemma lookup_tableBuild_in (F : X -> fset A) (xs : list X) (x : X)
  (IN : L.In x xs)
  : lookup x (tableBuild F xs) = Some (F x).
Proof.
  induction xs as [ | x' xs IH]; simpl in IN; [contradiction | ].
  simpl. pose proof (B.decide (x = x')) as [EQ | NE].
  - subst x'. eapply lookup_insert_eq.
  - rewrite lookup_insert_ne by exact NE. eapply IH.
    destruct IN as [EQ | IN]; [contradiction NE; congruence | exact IN].
Qed.

Variable nodes : fset X.

Definition propagateRow (snapshot : table) (binding : X * fset A)
  : X * fset A :=
  let '(x, old) := binding in
  (x, FS.union old (FS.bind (deps x) (tableGet snapshot))).

Fixpoint propagateRowsKeys (snapshot : table) (rows : list (X * fset A))
  : map fst (map (propagateRow snapshot) rows) = map fst rows.
Proof.
  destruct rows as [ | [x old] rows]; cbn [map propagateRow];
    [reflexivity | ].
  f_equal. eapply propagateRowsKeys.
Qed.

Definition propagateSweep (m : table) : table.
Proof.
  refine (FiniteMap.mk (map (propagateRow m) m.(FiniteMap.data)) _).
  rewrite propagateRowsKeys. exact m.(FiniteMap.data_isSorted).
Defined.

Local Definition propagateRowsSubset (universe : fset A) (m : table)
  : Prop :=
  forall (x : X) (row : fset A), lookup x m = Some row ->
    forall a : A, a ∈ row -> a ∈ universe.

Lemma propagateTableGet_subset (universe : fset A) (m : table)
  (ROWS : propagateRowsSubset universe m) (x : X) (a : A)
  (IN : a ∈ tableGet m x)
  : a ∈ universe.
Proof.
  unfold tableGet in IN. destruct (lookup x m) as [row | ] eqn:LOOK.
  - exact (ROWS x row LOOK a IN).
  - contradiction IN.
Qed.

Lemma propagateSweep_lookup (m : table) (x : X) (old : fset A)
  (LOOK : lookup x m = Some old)
  : lookup x (propagateSweep m) =
      Some (FS.union old (FS.bind (deps x) (tableGet m))).
Proof.
  rewrite lookup_spec in LOOK |- *.
  cbn [propagateSweep FiniteMap.data].
  rewrite L.in_map_iff. exists (x, old). split; [reflexivity | exact LOOK].
Qed.

Lemma propagateSweep_lookup_inv (m : table) (x : X) (next : fset A)
  (LOOK : lookup x (propagateSweep m) = Some next)
  : exists old : fset A,
      lookup x m = Some old /\
      next = FS.union old (FS.bind (deps x) (tableGet m)).
Proof.
  rewrite lookup_spec in LOOK.
  cbn [propagateSweep FiniteMap.data] in LOOK.
  rewrite L.in_map_iff in LOOK. destruct LOOK as [[y old] [EQ IN]].
  cbn [propagateRow] in EQ. inversion EQ; subst y next.
  exists old. split; [now rewrite lookup_spec | reflexivity].
Qed.

Lemma propagateSweep_rows_subset (universe : fset A) (m : table)
  (ROWS : propagateRowsSubset universe m)
  : propagateRowsSubset universe (propagateSweep m).
Proof.
  intros x next LOOK a IN.
  destruct (propagateSweep_lookup_inv m x next LOOK)
    as (old & LOOK_OLD & EQ). subst next.
  rewrite FS.in_union_iff in IN. destruct IN as [IN | IN].
  - exact (ROWS x old LOOK_OLD a IN).
  - rewrite FS.in_bind_iff in IN. destruct IN as (y & _ & IN).
    exact (propagateTableGet_subset universe m ROWS y a IN).
Qed.

Local Fixpoint propagateMassData (rows : list (X * fset A)) : nat :=
  match rows with
  | [] => O
  | (_, row) :: rows' => length row.(FSet.data) + propagateMassData rows'
  end.

Local Definition propagateMass (m : table) : nat :=
  propagateMassData m.(FiniteMap.data).

Local Definition propagateMeasure (universe : fset A) (m : table) : nat :=
  length m.(FiniteMap.data) * length universe.(FSet.data) -
    propagateMass m.

Lemma propagateUnion_length_le (old extra : fset A)
  : length old.(FSet.data) <= length (FS.union old extra).(FSet.data).
Proof.
  eapply fset_length_le. intros a IN. rewrite FS.in_union_iff. now left.
Qed.

Lemma propagateUnion_length_lt (old extra : fset A)
  (NE : FS.union old extra <> old)
  : length old.(FSet.data) < length (FS.union old extra).(FSet.data).
Proof.
  pose proof (propagateUnion_length_le old extra) as LE.
  assert (NE_LENGTH :
    length old.(FSet.data) <>
    length (FS.union old extra).(FSet.data)).
  { intros EQ. apply NE. rewrite fset_eq_spec. intros a. split.
    - intros IN.
      assert (REV : forall z : A,
        z ∈ (FS.union old extra) -> z ∈ old).
      { eapply L.NoDup_length_incl.
        - exact (fset_NoDup old).
        - lia.
        - intros z z_IN. rewrite FS.in_union_iff. now left. }
      exact (REV a IN).
    - intros IN. apply FS.in_union_iff. now left. }
  lia.
Qed.

Lemma propagateSweep_mass_facts (m : table)
  : propagateMass m <= propagateMass (propagateSweep m) /\
    (propagateSweep m <> m ->
      propagateMass m < propagateMass (propagateSweep m)).
Proof.
  unfold propagateMass. cbn [propagateSweep FiniteMap.data].
  assert (FACTS : forall rows : list (X * fset A),
    propagateMassData rows <=
      propagateMassData (map (propagateRow m) rows) /\
    (map (propagateRow m) rows <> rows ->
      propagateMassData rows <
        propagateMassData (map (propagateRow m) rows))).
  { induction rows as [ | [x old] rows IH].
    - cbn [map propagateMassData]. split;
        [lia | intros NE; exfalso; apply NE; reflexivity].
    - cbn [map propagateRow propagateMassData].
      destruct IH as [TAIL_LE TAIL_LT].
      set (extra := FS.bind (deps x) (tableGet m)).
      pose proof (propagateUnion_length_le old extra) as HERE_LE.
      split; [lia | ]. intros NE.
      destruct (B.decide (FS.union old extra = old))
        as [HERE_EQ | HERE_NE].
      + assert (TAIL_NE : map (propagateRow m) rows <> rows).
        { intros TAIL_EQ. apply NE. rewrite HERE_EQ, TAIL_EQ. reflexivity. }
        pose proof (TAIL_LT TAIL_NE). lia.
      + pose proof (propagateUnion_length_lt old extra HERE_NE). lia. }
  destruct (FACTS m.(FiniteMap.data)) as [MASS_LE MASS_LT].
  split; [exact MASS_LE | ]. intros CHANGED.
  eapply MASS_LT. intros DATA_EQ. apply CHANGED.
  apply (proj2 (FiniteMap.t_eq_iff (propagateSweep m) m)).
  cbn [propagateSweep FiniteMap.data]. exact DATA_EQ.
Qed.

Lemma propagateMass_bound (universe : fset A) (m : table)
  (ROWS : propagateRowsSubset universe m)
  : propagateMass m <=
      length m.(FiniteMap.data) * length universe.(FSet.data).
Proof.
  unfold propagateMass. remember m.(FiniteMap.data) as rows eqn:EQ_ROWS.
  assert (IN_M : forall x row,
    L.In (x, row) rows -> lookup x m = Some row).
  { intros x row IN. rewrite lookup_spec. now rewrite <- EQ_ROWS. }
  clear EQ_ROWS. induction rows as [ | [x row] rows IH].
  - cbn [propagateMassData length]. lia.
  - cbn [propagateMassData length].
    assert (ROW_LE : length row.(FSet.data) <= length universe.(FSet.data)).
    { eapply fset_length_le. intros a IN.
      eapply ROWS; [eapply IN_M; now left | exact IN]. }
    assert (TAIL : forall y row',
      L.In (y, row') rows -> lookup y m = Some row').
    { intros y row' IN. eapply IN_M. now right. }
    specialize (IH TAIL). lia.
Qed.

Lemma propagateSweep_length (m : table)
  : length (propagateSweep m).(FiniteMap.data) =
    length m.(FiniteMap.data).
Proof.
  cbn [propagateSweep FiniteMap.data]. now rewrite L.length_map.
Qed.

Lemma propagateSweep_measure_lt (universe : fset A) (m : table)
  (ROWS : propagateRowsSubset universe m)
  (CHANGED : propagateSweep m <> m)
  : propagateMeasure universe (propagateSweep m) <
    propagateMeasure universe m.
Proof.
  pose proof (proj2 (propagateSweep_mass_facts m) CHANGED) as MASS_LT.
  pose proof
    (propagateMass_bound universe (propagateSweep m)
      (propagateSweep_rows_subset universe m ROWS)) as BOUND.
  unfold propagateMeasure. rewrite propagateSweep_length in BOUND |- *.
  lia.
Qed.

Definition propagateStepRel (next current : table) : Prop :=
  next = propagateSweep current /\ next <> current.

Definition propagateRelAcc (universe : fset A)
  : forall m : table,
      propagateRowsSubset universe m ->
      Acc Nat.lt (propagateMeasure universe m) ->
      Acc propagateStepRel m.
Proof.
  refine (fix go (m : table) (ROWS : propagateRowsSubset universe m)
    (H_Acc : Acc Nat.lt (propagateMeasure universe m)) {struct H_Acc}
    : Acc propagateStepRel m := _).
  constructor. intros next STEP. destruct STEP as [EQ CHANGED]. subst next.
  exact (go (propagateSweep m) (propagateSweep_rows_subset universe m ROWS)
    (Acc_inv H_Acc
      (propagateSweep_measure_lt universe m ROWS CHANGED))).
Defined.

Definition propagateRun
  : forall m : table, Acc propagateStepRel m -> table.
Proof.
  refine (fix go (m : table) (H_Acc : Acc propagateStepRel m)
    {struct H_Acc} : table := _).
  set (next := propagateSweep m).
  destruct (B.decide (next = m)) as [SAME | CHANGED].
  - exact m.
  - exact (go next (Acc_inv H_Acc (conj eq_refl CHANGED))).
Defined.

Fixpoint propagateRun_fixed (m : table)
  (H_Acc : Acc propagateStepRel m) {struct H_Acc}
  : propagateSweep (propagateRun m H_Acc) = propagateRun m H_Acc.
Proof.
  destruct H_Acc as [H_Acc_inv].
  cbn [propagateRun]. destruct (B.decide (propagateSweep m = m)).
  - assumption.
  - eapply propagateRun_fixed.
Qed.

Local Definition propagateUniverse : fset A :=
  FS.bind nodes seed.

Definition propagateInitial : table :=
  tableBuild seed nodes.(FSet.data).

Lemma propagateInitial_rows_subset
  : propagateRowsSubset propagateUniverse propagateInitial.
Proof.
  intros x row LOOK a IN.
  unfold propagateInitial, propagateUniverse in *.
  rewrite tableBuild_fold in LOOK.
  pose proof (lookup_tabulated_inv seed nodes.(FSet.data) x row LOOK)
    as [IN_X EQ]. subst row.
  rewrite FS.in_bind_iff. exists x. split; assumption.
Qed.

Local Definition propagateDomain (m : table) : Prop :=
  forall x : X, x ∈ nodes -> exists row : fset A, lookup x m = Some row.

Local Definition propagateKeysIn (m : table) : Prop :=
  forall (x : X) (row : fset A), lookup x m = Some row -> x ∈ nodes.

Local Definition propagateSeedIncluded (m : table) : Prop :=
  forall (x : X) (a : A), x ∈ nodes -> a ∈ seed x ->
    a ∈ tableGet m x.

Local Definition propagateSound (m : table) : Prop :=
  forall (x : X) (a : A), a ∈ tableGet m x ->
    x \in propagate_closure a.

Inductive propagate_closure_on (a : A) (x : X) : Prop :=
  | propagate_closure_on_seed
    (IN : a ∈ seed x)
    : propagate_closure_on a x
  | propagate_closure_on_step y
    (EDGE : y ∈ deps x)
    (IN_Y : y ∈ nodes)
    (IN : propagate_closure_on a y)
    : propagate_closure_on a x.

Local Definition propagateSoundIn (m : table) : Prop :=
  forall (x : X) (a : A), a ∈ tableGet m x ->
    propagate_closure_on a x.

Local Definition propagateInvariant (m : table) : Prop :=
  propagateRowsSubset propagateUniverse m /\
  propagateKeysIn m /\
  propagateDomain m /\
  propagateSeedIncluded m /\
  propagateSound m /\
  propagateSoundIn m.

Lemma propagateInitial_invariant : propagateInvariant propagateInitial.
Proof.
  repeat split.
  - exact propagateInitial_rows_subset.
  - intros x row LOOK. unfold propagateInitial in LOOK.
    rewrite tableBuild_fold in LOOK.
    exact (proj1 (lookup_tabulated_inv seed nodes.(FSet.data) x row LOOK)).
  - intros x IN_X. exists (seed x).
    unfold propagateInitial. eapply lookup_tableBuild_in. exact IN_X.
  - intros x a IN_X IN.
    unfold tableGet, propagateInitial.
    rewrite lookup_tableBuild_in by exact IN_X. exact IN.
  - intros x a IN.
    unfold tableGet, propagateInitial in IN.
    destruct (lookup x (tableBuild seed nodes.(FSet.data)))
      as [row | ] eqn:LOOK; [ | contradiction IN].
    rewrite tableBuild_fold in LOOK.
    pose proof (lookup_tabulated_inv seed nodes.(FSet.data) x row LOOK)
      as [_ EQ]. subst row. now eapply propagate_closure_seed.
  - intros x a IN.
    unfold tableGet, propagateInitial in IN.
    destruct (lookup x (tableBuild seed nodes.(FSet.data)))
      as [row | ] eqn:LOOK; [ | contradiction IN].
    rewrite tableBuild_fold in LOOK.
    pose proof (lookup_tabulated_inv seed nodes.(FSet.data) x row LOOK)
      as [_ EQ]. subst row. now eapply propagate_closure_on_seed.
Qed.

Lemma propagateSweep_invariant (m : table)
  (INV : propagateInvariant m)
  : propagateInvariant (propagateSweep m).
Proof.
  destruct INV as [ROWS [KEYS [DOMAIN [SEEDS [SOUND SOUND_IN]]]]].
  repeat split.
  - now apply propagateSweep_rows_subset.
  - intros x next LOOK.
    destruct (propagateSweep_lookup_inv m x next LOOK)
      as (old & LOOK_OLD & _). exact (KEYS x old LOOK_OLD).
  - intros x IN_X. destruct (DOMAIN x IN_X) as [old LOOK].
    exists (FS.union old (FS.bind (deps x) (tableGet m))).
    now apply propagateSweep_lookup.
  - intros x a IN_X IN.
    destruct (DOMAIN x IN_X) as [old LOOK].
    unfold tableGet.
    rewrite (propagateSweep_lookup m x old LOOK).
    apply FS.in_union_iff. left.
    pose proof (SEEDS x a IN_X IN) as IN_OLD.
    unfold tableGet in IN_OLD. now rewrite LOOK in IN_OLD.
  - intros x a IN.
    unfold tableGet in IN.
    destruct (lookup x (propagateSweep m)) as [next | ] eqn:LOOK;
      [ | contradiction IN].
    destruct (propagateSweep_lookup_inv m x next LOOK)
      as (old & LOOK_OLD & EQ). subst next.
    rewrite FS.in_union_iff in IN. destruct IN as [IN | IN].
    + eapply SOUND. unfold tableGet. now rewrite LOOK_OLD.
    + rewrite FS.in_bind_iff in IN. destruct IN as (y & EDGE & IN).
      eapply propagate_closure_step with (y := y); [exact EDGE | ].
      now eapply SOUND.
  - intros x a IN.
    unfold tableGet in IN.
    destruct (lookup x (propagateSweep m)) as [next | ] eqn:LOOK;
      [ | contradiction IN].
    destruct (propagateSweep_lookup_inv m x next LOOK)
      as (old & LOOK_OLD & EQ). subst next.
    rewrite FS.in_union_iff in IN. destruct IN as [IN | IN].
    + eapply SOUND_IN. unfold tableGet. now rewrite LOOK_OLD.
    + rewrite FS.in_bind_iff in IN. destruct IN as (y & EDGE & IN).
      eapply propagate_closure_on_step with (y := y).
      * exact EDGE.
      * unfold tableGet in IN. destruct (lookup y m) as [row | ] eqn:LOOK_Y;
          [ | contradiction IN].
        exact (KEYS y row LOOK_Y).
      * now eapply SOUND_IN.
Qed.

Fixpoint propagateRun_invariant (m : table)
  (H_Acc : Acc propagateStepRel m) (INV : propagateInvariant m)
  {struct H_Acc}
  : propagateInvariant (propagateRun m H_Acc).
Proof.
  destruct H_Acc as [H_Acc_inv].
  cbn [propagateRun]. destruct (B.decide (propagateSweep m = m)).
  - exact INV.
  - eapply propagateRun_invariant. now apply propagateSweep_invariant.
Qed.

Definition propagateTable : table :=
  propagateRun propagateInitial
    (propagateRelAcc propagateUniverse propagateInitial
      propagateInitial_rows_subset
      (accLt (propagateMeasure propagateUniverse propagateInitial))).

Lemma propagateTable_fixed
  : propagateSweep propagateTable = propagateTable.
Proof.
  unfold propagateTable. apply propagateRun_fixed.
Qed.

Lemma propagateTable_invariant : propagateInvariant propagateTable.
Proof.
  unfold propagateTable. apply propagateRun_invariant.
  exact propagateInitial_invariant.
Qed.

Definition propagate_kleene : X -> fset A :=
  let m := propagateTable in
  fun x => tableStep m x.

Lemma propagateFixed_step (m : table)
  (DOMAIN : propagateDomain m)
  (FIXED : propagateSweep m = m)
  (x y : X) (a : A)
  (IN_X : x ∈ nodes)
  (EDGE : y ∈ deps x)
  (IN : a ∈ tableGet m y)
  : a ∈ tableGet m x.
Proof.
  destruct (DOMAIN x IN_X) as [old LOOK].
  pose proof (propagateSweep_lookup m x old LOOK) as NEXT.
  rewrite FIXED, LOOK in NEXT. injection NEXT as EQ.
  unfold tableGet. rewrite LOOK, EQ.
  apply FS.in_union_iff. right. rewrite FS.in_bind_iff.
  exists y. split; assumption.
Qed.

Lemma propagateTable_complete (x : X) (a : A)
  (IN_X : x ∈ nodes)
  (CLOSURE : x \in propagate_closure a)
  (deps_CLOSED : forall x : X, forall y : X, y ∈ deps x -> y ∈ nodes)
  : a ∈ tableGet propagateTable x.
Proof.
  pose proof propagateTable_invariant as
    [_ [_ [DOMAIN [SEEDS _]]]].
  revert IN_X. induction CLOSURE as
    [x SEED | x y EDGE CLOSURE IH]; intros IN_X.
  - exact (SEEDS x a IN_X SEED).
  - eapply propagateFixed_step with (y := y).
    + exact DOMAIN.
    + exact propagateTable_fixed.
    + exact IN_X.
    + exact EDGE.
    + eapply IH. exact (deps_CLOSED x y EDGE).
Qed.

Lemma propagateTable_complete_on (x : X) (a : A)
  (IN_X : x ∈ nodes)
  (CLOSURE : propagate_closure_on a x)
  : a ∈ tableGet propagateTable x.
Proof.
  pose proof propagateTable_invariant as
    [_ [_ [DOMAIN [SEEDS _]]]].
  revert IN_X. induction CLOSURE as
    [x SEED | x y EDGE IN_Y CLOSURE IH]; intros IN_X.
  - exact (SEEDS x a IN_X SEED).
  - eapply propagateFixed_step with (y := y).
    + exact DOMAIN.
    + exact propagateTable_fixed.
    + exact IN_X.
    + exact EDGE.
    + exact (IH IN_Y).
Qed.

Theorem propagate_kleene_iff_closure_on (x : X) (a : A)
  : a ∈ propagate_kleene x <-> propagate_closure_on a x.
Proof.
  unfold propagate_kleene, tableStep. rewrite FS.in_union_iff, FS.in_bind_iff.
  pose proof propagateTable_invariant as
    [_ [_ [_ [_ [_ SOUND_IN]]]]]. split.
  - intros [SEED | (y & EDGE & IN)].
    + now eapply propagate_closure_on_seed.
    + eapply propagate_closure_on_step with (y := y).
      * exact EDGE.
      * unfold tableGet in IN.
        destruct (lookup y propagateTable) as [row | ] eqn:LOOK;
          [ | contradiction IN].
        pose proof propagateTable_invariant as [_ [KEYS _]].
        exact (KEYS y row LOOK).
      * now eapply SOUND_IN.
  - intros CLOSURE. destruct CLOSURE as [SEED | y EDGE IN_Y CLOSURE].
    + now left.
    + right. exists y. split; [exact EDGE | ].
      exact (propagateTable_complete_on y a IN_Y CLOSURE).
Qed.

Theorem propagate_kleene_iff_closure (x : X) (a : A)
  (deps_CLOSED : forall x : X, forall y : X, y ∈ deps x -> y ∈ nodes)
  : a ∈ propagate_kleene x <-> x \in propagate_closure a.
Proof.
  unfold propagate_kleene, tableStep. rewrite FS.in_union_iff, FS.in_bind_iff.
  pose proof propagateTable_invariant as [_ [_ [_ [_ [SOUND _]]]]]. split.
  - intros [SEED | (y & EDGE & IN)].
    + now eapply propagate_closure_seed.
    + eapply propagate_closure_step with (y := y); [exact EDGE | ].
      now eapply SOUND.
  - intros CLOSURE. destruct CLOSURE as [SEED | y EDGE CLOSURE].
    + now left.
    + right. exists y. split; [exact EDGE | ].
      exact (propagateTable_complete y a
        (deps_CLOSED x y EDGE) CLOSURE deps_CLOSED).
Qed.

Corollary propagate_kleene_equation
  (deps_CLOSED : forall x : X, forall y : X, y ∈ deps x -> y ∈ nodes)
  : propagate_equation propagate_kleene.
Proof.
  intros x a. unnw. rewrite propagate_kleene_iff_closure by exact deps_CLOSED. split.
  - intros CLOSURE. destruct CLOSURE as [SEED_IN | y EDGE CLOSURE].
    + now left.
    + right. exists y. split; [exact EDGE | ].
      rewrite propagate_kleene_iff_closure by exact deps_CLOSED. exact CLOSURE.
  - intros [SEED_IN | (y & EDGE & IN)].
    + now eapply propagate_closure_seed.
    + rewrite propagate_kleene_iff_closure in IN by exact deps_CLOSED.
      now eapply propagate_closure_step with (y := y).
Qed.

Corollary propagate_kleene_least (value : X -> fset A) (x : X) (a : A)
  (deps_CLOSED : forall x : X, forall y : X, y ∈ deps x -> y ∈ nodes)
  (EQUATION : propagate_equation value)
  (IN : a ∈ propagate_kleene x)
  : a ∈ value x.
Proof.
  eapply propagate_closure_least; [exact EQUATION | ].
  rewrite <- propagate_kleene_iff_closure by exact deps_CLOSED. exact IN.
Qed.

End KLEENE.

End DIGRAPH.

Section KLEENE_EXT.

Context {X : Type} {POSET_X : isPoset X} {HsOrd_X : HsOrd X (POSET := POSET_X)}.
Context {A : Type} {POSET_A : isPoset A} {HsOrd_A : HsOrd A (POSET := POSET_A)}.

Lemma propagate_kleene_ext (seed : X -> fset A) (deps : X -> fset X) (deps' : X -> fset X) (nodes : fset X)
  (EXT : forall x : X, deps x = deps' x)
  : forall x : X, propagate_kleene seed deps nodes x = propagate_kleene seed deps' nodes x.
Proof.
  intros x. rewrite fset_eq_spec. intro a.
  rewrite !propagate_kleene_iff_closure_on. split.
  - intro CLOSURE. induction CLOSURE as
      [x SEED | x y EDGE IN_Y CLOSURE IH].
    + now eapply propagate_closure_on_seed.
    + eapply propagate_closure_on_step with (y := y).
      * rewrite <- (EXT x). exact EDGE.
      * exact IN_Y.
      * exact IH.
  - intro CLOSURE. induction CLOSURE as
      [x SEED | x y EDGE IN_Y CLOSURE IH].
    + now eapply propagate_closure_on_seed.
    + eapply propagate_closure_on_step with (y := y).
      * rewrite (EXT x). exact EDGE.
      * exact IN_Y.
      * exact IH.
Qed.

Lemma propagate_kleene_ext_on (seed : X -> fset A) (deps : X -> fset X) (deps' : X -> fset X) (nodes : fset X)
  (EXT : forall x : X, L.In x nodes.(FSet.data) -> deps x = deps' x)
  : forall x : X, L.In x nodes.(FSet.data) -> (propagate_kleene seed deps nodes x = propagate_kleene seed deps' nodes x).
Proof.
  intros x IN_X. rewrite fset_eq_spec. intro a.
  rewrite !propagate_kleene_iff_closure_on. split.
  - intro CLOSURE. revert IN_X. induction CLOSURE as
      [x SEED | x y EDGE IN_Y CLOSURE IH]; intros IN_X.
    + now eapply propagate_closure_on_seed.
    + eapply propagate_closure_on_step with (y := y).
      * rewrite <- (EXT x IN_X). exact EDGE.
      * exact IN_Y.
      * exact (IH IN_Y).
  - intro CLOSURE. revert IN_X. induction CLOSURE as
      [x SEED | x y EDGE IN_Y CLOSURE IH]; intros IN_X.
    + now eapply propagate_closure_on_seed.
    + eapply propagate_closure_on_step with (y := y).
      * rewrite (EXT x IN_X). exact EDGE.
      * exact IN_Y.
      * exact (IH IN_Y).
Qed.

Lemma propagate_kleene_seed_ext_on
  (seed seed' : X -> fset A) (deps : X -> fset X) (nodes : fset X)
  (CLOSED : forall x y : X,
    L.In y (deps x).(FSet.data) -> L.In y nodes.(FSet.data))
  (EXT : forall x : X,
    L.In x nodes.(FSet.data) -> seed x = seed' x)
  (x : X) (IN_X : L.In x nodes.(FSet.data))
  : propagate_kleene seed deps nodes x =
    propagate_kleene seed' deps nodes x.
Proof.
  rewrite fset_eq_spec. intro a.
  rewrite !propagate_kleene_iff_closure by exact CLOSED.
  split.
  - intro CLOSURE. revert IN_X.
    induction CLOSURE as [x SEED | x y EDGE CLOSURE IH]; intro IN_X.
    + eapply propagate_closure_seed.
      rewrite <- (EXT x IN_X). exact SEED.
    + eapply propagate_closure_step with (y := y).
      * exact EDGE.
      * apply IH. eapply CLOSED. exact EDGE.
  - intro CLOSURE. revert IN_X.
    induction CLOSURE as [x SEED | x y EDGE CLOSURE IH]; intro IN_X.
    + eapply propagate_closure_seed.
      rewrite (EXT x IN_X). exact SEED.
    + eapply propagate_closure_step with (y := y).
      * exact EDGE.
      * apply IH. eapply CLOSED. exact EDGE.
Qed.

End KLEENE_EXT.

End DigraphFixedpoint.

#[local] Notation "x '∈f' X" :=
  (L.In x X.(FSet.data))
  (at level 70, no associativity) : type_scope.

Section FINITE_REACHABILITY.

Context {A : Type} {A_isPoset : isPoset A}
  {HsOrd_A : HsOrd A (POSET := A_isPoset)}.

Variable V : fset A.
Variable succ : A -> fset A.

Definition succV (x : A) : fset A :=
  inter (succ x) V.

Lemma succV_sub (x : A) (z : A)
  (IN : z ∈f succV x)
  : z ∈f V.
Proof.
  unfold succV in IN.
  exact (proj2 (proj1 (in_inter_iff (succ x) V z) IN)).
Qed.

#[local] Abbreviation RConfig := (list A * fset A)%type.

Definition rok (c : RConfig) : Prop :=
  (forall z : A, z ∈f snd c -> z ∈f V) /\
  (forall z : A, L.In z (fst c) -> z ∈f V).

Definition rstep (c : RConfig) : RConfig :=
  match fst c with
  | [] => c
  | x :: xs =>
    if FS.mem x (snd c) then
      (xs, snd c)
    else
      (xs ++ (succV x).(FSet.data), FS.add x (snd c))
  end.

Definition rho (c : RConfig) : nat :=
  (length V.(FSet.data) - length (snd c).(FSet.data)) *
    (length V.(FSet.data) + 1) + length (fst c).

Lemma rstep_rok (c : RConfig)
  (H : rok c)
  : rok (rstep c).
Proof.
  destruct c as [todo seen]. destruct H as [H_seen H_todo].
  unfold rstep. cbn [fst snd] in *.
  destruct todo as [ | x xs]; [split; assumption | ].
  destruct (FS.mem x seen) as [ | ].
  - split; cbn [fst snd]; [exact H_seen | ].
    intros z z_in. eapply H_todo. now right.
  - split; cbn [fst snd].
    + intros z z_in. rewrite FS.in_add_iff in z_in.
      destruct z_in as [EQ | z_in].
      * subst z. eapply H_todo. now left.
      * exact (H_seen z z_in).
    + intros z z_in. rewrite L.in_app_iff in z_in.
      destruct z_in as [z_in | z_in].
      * eapply H_todo. now right.
      * exact (succV_sub x z z_in).
Qed.

Lemma rstep_lt (c : RConfig) (x : A) (xs : list A)
  (H : rok c)
  (TODO : fst c = x :: xs)
  : rho (rstep c) < rho c.
Proof.
  destruct c as [todo seen]. destruct H as [H_seen H_todo].
  cbn [fst snd] in TODO. subst todo.
  unfold rho, rstep. cbn [fst snd].
  assert (SEEN_LE :
    length seen.(FSet.data) <= length V.(FSet.data)).
  { eapply fset_length_le. exact H_seen. }
  destruct (FS.mem x seen) as [ | ] eqn: MEM.
  - cbn [fst snd length]. lia.
  - pose proof (proj1 (FS.mem_spec x seen false) MEM) as NOTIN.
    clear MEM.
    assert (X_IN : x ∈f V) by (eapply H_todo; now left).
    assert (SEEN_LT :
      length seen.(FSet.data) < length V.(FSet.data)).
    { enough (WTS :
        length (FS.add x seen).(FSet.data) <= length V.(FSet.data)).
      { cbn [FS.add FSet.data] in WTS.
        rewrite FS.length_insert in WTS by exact NOTIN. lia. }
      eapply fset_length_le. intros z z_in.
      rewrite FS.in_add_iff in z_in.
      destruct z_in as [EQ | z_in];
        [subst z; exact X_IN | exact (H_seen z z_in)].
    }
    assert (SUCC_LE :
      length (succV x).(FSet.data) <= length V.(FSet.data)).
    { eapply fset_length_le. exact (succV_sub x). }
    cbn [fst snd]. rewrite L.length_app.
    change (FS.add x seen).(FSet.data) with
      (FS.insert x seen.(FSet.data)).
    rewrite FS.length_insert by exact NOTIN.
    cbn [length].
    remember (length V.(FSet.data)) as v eqn: Hv.
    remember (length seen.(FSet.data)) as s eqn: Hs.
    remember (length (succV x).(FSet.data)) as k eqn: Hk.
    destruct (v - s) as [ | d] eqn: HD; [lia | ].
    replace (v - S s) with d by lia.
    rewrite Nat.mul_succ_l. lia.
Qed.

Definition reachRun
  : forall c : RConfig, rok c -> Acc Nat.lt (rho c) -> fset A.
Proof.
  refine (fix go (c : RConfig) (H : rok c)
    (H_Acc : Acc Nat.lt (rho c)) {struct H_Acc} : fset A := _).
  destruct (fst c) as [ | x xs] eqn: TODO.
  - exact (snd c).
  - exact (go (rstep c) (rstep_rok c H)
      (Acc_inv H_Acc (rstep_lt c x xs H TODO))).
Defined.

Fixpoint reachRun_pirrel (c : RConfig)
  (H1 : rok c) (H2 : rok c)
  (H_Acc : Acc Nat.lt (rho c)) (H_Acc' : Acc Nat.lt (rho c)) {struct H_Acc}
  : reachRun c H1 H_Acc = reachRun c H2 H_Acc'.
Proof.
  destruct c as [todo seen], todo as [ | x xs];
    destruct H_Acc as [H_Acc_inv], H_Acc' as [H_Acc_inv']; cbn [reachRun].
  - reflexivity.
  - eapply reachRun_pirrel.
Qed.

Lemma reach_impl_rok (S0 : fset A)
  : rok ((inter S0 V).(FSet.data), FS.empty).
Proof.
  split; cbn [fst snd].
  - intros z z_in. destruct z_in.
  - intros z z_in.
    exact (proj2 (proj1 (in_inter_iff S0 V z) z_in)).
Qed.

Definition reach_impl (S0 : fset A) : fset A :=
  reachRun ((inter S0 V).(FSet.data), FS.empty) (reach_impl_rok S0)
    (accLt (rho ((inter S0 V).(FSet.data), FS.empty))).

Fixpoint reachRun_sub (c : RConfig) (H : rok c)
  (H_Acc : Acc Nat.lt (rho c)) {struct H_Acc}
  : forall z : A, z ∈f reachRun c H H_Acc -> z ∈f V.
Proof.
  destruct c as [todo seen], todo as [ | x xs];
    destruct H_Acc as [H_Acc_inv]; cbn [reachRun].
  - exact (proj1 H).
  - eapply reachRun_sub.
Qed.

Lemma reach_impl_sub (S0 : fset A) (z : A)
  (IN : z ∈f reach_impl S0)
  : z ∈f V.
Proof.
  exact (reachRun_sub _ _ _ z IN).
Qed.

Definition rstepStack (c : RConfig) : RConfig :=
  match fst c with
  | [] => c
  | x :: xs =>
    if FS.mem x (snd c) then
      (xs, snd c)
    else
      ((succV x).(FSet.data) ++ xs, FS.add x (snd c))
  end.

Lemma rstepStack_rok (c : RConfig)
  (H : rok c)
  : rok (rstepStack c).
Proof.
  destruct c as [todo seen]. destruct H as [H_seen H_todo].
  unfold rstepStack. cbn [fst snd] in *.
  destruct todo as [ | x xs]; [split; assumption | ].
  destruct (FS.mem x seen) as [ | ].
  - split; cbn [fst snd]; [exact H_seen | ].
    intros z z_in. eapply H_todo. now right.
  - split; cbn [fst snd].
    + intros z z_in. rewrite FS.in_add_iff in z_in.
      destruct z_in as [EQ | z_in].
      * subst z. eapply H_todo. now left.
      * exact (H_seen z z_in).
    + intros z z_in. rewrite L.in_app_iff in z_in.
      destruct z_in as [z_in | z_in].
      * exact (succV_sub x z z_in).
      * eapply H_todo. now right.
Qed.

Lemma rstepStack_rho (c : RConfig)
  : rho (rstepStack c) = rho (rstep c).
Proof.
  destruct c as [todo seen], todo as [ | x xs]; [reflexivity | ].
  unfold rstepStack, rstep, rho. cbn [fst snd].
  destruct (FS.mem x seen); [reflexivity | ].
  cbn [fst snd]. rewrite !L.length_app. lia.
Qed.

Lemma rstepStack_lt (c : RConfig) (x : A) (xs : list A)
  (H : rok c)
  (TODO : fst c = x :: xs)
  : rho (rstepStack c) < rho c.
Proof.
  rewrite rstepStack_rho. exact (rstep_lt c x xs H TODO).
Qed.

Definition reachRunStack
  : forall c : RConfig, rok c -> Acc Nat.lt (rho c) -> fset A.
Proof.
  refine (fix go (c : RConfig) (H : rok c)
    (H_Acc : Acc Nat.lt (rho c)) {struct H_Acc} : fset A := _).
  destruct (fst c) as [ | x xs] eqn: TODO.
  - exact (snd c).
  - exact (go (rstepStack c) (rstepStack_rok c H)
      (Acc_inv H_Acc (rstepStack_lt c x xs H TODO))).
Defined.

Fixpoint reachRunStack_sub (c : RConfig) (H : rok c)
  (H_Acc : Acc Nat.lt (rho c)) {struct H_Acc}
  : forall z : A, z ∈f reachRunStack c H H_Acc -> z ∈f V.
Proof.
  destruct c as [todo seen], todo as [ | x xs];
    destruct H_Acc as [H_Acc_inv]; cbn [reachRunStack].
  - exact (proj1 H).
  - eapply reachRunStack_sub.
Qed.

Definition reach_impl_fast (S0 : fset A) : fset A :=
  let c0 : RConfig := ((inter S0 V).(FSet.data), FS.empty) in
  reachRunStack c0 (reach_impl_rok S0) (accLt (rho c0)).

Lemma reach_impl_fast_sub (S0 : fset A) (z : A)
  (IN : z ∈f reach_impl_fast S0)
  : z ∈f V.
Proof.
  exact (reachRunStack_sub _ _ _ z IN).
Qed.

End FINITE_REACHABILITY.

#[global] Arguments succV {A} {A_isPoset} {HsOrd_A} V succ x.
#[global] Arguments rok {A} {A_isPoset} {HsOrd_A} V c.
#[global] Arguments rstep {A} {A_isPoset} {HsOrd_A} V succ c.
#[global] Arguments rho {A} {A_isPoset} {HsOrd_A} V c.
#[global] Arguments reachRun {A} {A_isPoset} {HsOrd_A} V succ c H H_Acc.
#[global] Arguments reach_impl {A} {A_isPoset} {HsOrd_A} V succ S0.
#[global] Arguments rstepStack {A} {A_isPoset} {HsOrd_A} V succ c.
#[global] Arguments rstepStack_rok
  {A} {A_isPoset} {HsOrd_A} V succ c H.
#[global] Arguments rstepStack_rho
  {A} {A_isPoset} {HsOrd_A} V succ c.
#[global] Arguments rstepStack_lt
  {A} {A_isPoset} {HsOrd_A} V succ c x xs H TODO.
#[global] Arguments reachRunStack
  {A} {A_isPoset} {HsOrd_A} V succ c H H_Acc.
#[global] Arguments reachRunStack_sub
  {A} {A_isPoset} {HsOrd_A} V succ c H H_Acc z IN.
#[global] Arguments reach_impl_fast
  {A} {A_isPoset} {HsOrd_A} V succ S0.
#[global] Arguments reach_impl_fast_sub
  {A} {A_isPoset} {HsOrd_A} V succ S0 z IN.
