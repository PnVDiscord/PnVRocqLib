Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Category.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Data.FiniteMap.
Require Import PnV.Prelude.X.

Module GRAPH.

#[projections(primitive)]
Class t : Type :=
  mk
  { vertices : Type
  ; edges : ensemble (vertices * vertices)
  } as G.

End GRAPH.

#[local] Abbreviation In := L.In.
#[local] Infix "\in" := E.In : type_scope.

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
    (NOT_IN : ~ In v0 (v1 :: p))
    : v0 ---[ v1 :: p ]--> v
  where " src ---[ p ]--> tgt " := (path tgt src p) : type_scope.

#[local] Hint Constructors path : core.

Lemma path_vertices_no_dup (v0 : V) (v : V) (p : list V)
  (H_path : v0 ---[ p ]--> v)
  : NoDup (v0 :: p).
Proof.
  induction H_path as [ | v0 v1 p H_edge H_path IH NOT_IN]; econs; eauto. econs.
Qed.

Lemma no_dup_walk_is_path (v0 : V) (v : V) (w : list V)
  (NO_DUP : NoDup (v0 :: w))
  (H_walk : v0 ~~~[ w ]~~> v)
  : v0 ---[ w ]--> v.
Proof.
  induction H_walk as [ | v0 v1 w H_edge H_walk IH]; i; econs.
  - exact H_edge.
  - eapply IH. now inv NO_DUP.
  - now inv NO_DUP.
Qed.

Theorem path_iff_no_dup_walk (v0 : V) (v : V) (vs : list V)
  : v0 ---[ vs ]--> v <-> (v0 ~~~[ vs ]~~> v /\ NoDup (v0 :: vs)).
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
  revert v0 v' vs2 PATH. induction vs1 as [ | v1 vs1 IH]; simpl; i.
  - exists v0. split; eauto.
  - inv PATH. find* (v & PATH1 & PATH2) by IH.
    exists v. split; eauto. econstructor 2; eauto. ii. contradiction NOT_IN. ss!.
Qed.

Section Walk_finds_Path.

Lemma mk_subpath (v0 : V) (v1 : V) (v : V) (p : list V)
  (PATH : v0 ---[ p ]--> v)
  (ELEM : In v1 p)
  : exists p', v0 ---[ p' ]--> v1 /\ (exists p'', v1 ---[ p'' ]--> v /\ p = p' ++ p'').
Proof.
  revert v1 ELEM. induction PATH as [ | v0 v1 p H_edge PATH IH NOT_IN]; i; inv ELEM.
  - exists [v2]. split; eauto. econstructor 2; eauto. ii. contradiction NOT_IN. ss!.
  - find* (p'&PATH1&p''&PATH2&EQ) by IH.
    exists (v1 :: p'). split.
    + econstructor 2; eauto. subst p. ii. apply NOT_IN. ss!.
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
    pose proof (In_dec v' (v0 :: p)) as [ELEM | NOT_IN].
    + inv ELEM.
      * exists []. econstructor 1.
      * find* (p'&PATH'&_) by (mk_subpath _ _ _ _ PATH). ss!.
    + exists (p ++ [v']). rewrite -> path_iff_no_dup_walk. split.
      * rewrite -> walk_app_iff. exists v1. split.
        { now eapply path_iff_no_dup_walk. }
        { econstructor 2; eauto. }
      * change (NoDup ((v0 :: p) ++ [v'])).
        rewrite <- rev_involutive. eapply NoDup_rev.
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
  - eapply L.no_dup_mk_edge_seq. now inv NO_DUP.
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

Variable seed' : V -> list A.

Hypothesis seed_sim : forall v, seed' v =~= seed v.

Variable vertices' : list V.

Definition reachable (x : V) : ensemble V :=
  fun y => exists w, x ~~~[ w ]~~> y.

Context `{V_dec : hasEqDec V} `{E_dec : forall x : V, forall y : V, B.Decision ((x, y) \in E)}.

Fixpoint reachableb (fuel : nat) (x : V) (y : V) {struct fuel} : bool :=
  match fuel with
  | O => eqb x y
  | S fuel' => eqb x y || L.existsb (fun z => if E_dec x z then reachableb fuel' z y else false) vertices'
  end.

Definition reachable' (x : V) : list V :=
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
      find (w & LENGTH & WALK) by (IH z y).
      exists (z :: w). split; [simpl; lia | econstructor 2; eauto].
Qed.

Definition gmu' (x : V) : list A :=
  L.flat_map seed' (reachable' x).

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
  revert fuel LENGTH. induction WALK as [ | v0 v1 w EDGE WALK IH]; i.
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
  - i.
    find* (w & _ & WALK) by reachableb_elim.
    now exists w.
  - intros [w WALK].
    assert (exists p, x ---[ p ]-->*( G ) y) as [p PATH].
    { eapply @walk_finds_path with (G := G) (w := w); eauto.
      now intros v vs; pose proof (L.in_dec V_dec v vs) as [YES | NO]; [left | right].
    }
    rewrite path_iff_no_dup_walk in PATH.
    clear WALK. destruct PATH as [WALK NO_DUP].
    eapply reachableb_intro; eauto.
    eapply L.NoDup_incl_length; [now inv NO_DUP | ii].
    eapply walk_elem_in_vertices; eauto.
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
  destruct REACH as [w WALK]. exists (y :: w). econs 2; eauto.
Qed.

Lemma gmu_reachable_seed (x : V) (a : A)
  (IN : a \in gmu x)
  : exists y, y \in reachable x /\ a \in seed y.
Proof.
  induction IN as [x a SEED | x y EDGE a IN (z & REACH & SEED)].
  - exists x. split; [exists []; econs 1 | auto].
  - exists z. split; [eapply reachable_step; eauto | auto].
Qed.

Lemma gmu_iff_reachable_seed (x : V) (a : A)
  : a \in gmu x <-> a \in (reachable x >>= seed).
Proof.
  split.
  - eapply gmu_reachable_seed.
  - intros (y & REACH & SEED). eapply reachable_seed_gmu; eauto.
Qed.

Theorem gmu_sim (x : V)
  : gmu' x =~= gmu x.
Proof.
  find* H by (list_corresponds_to_finite_ensemble_flat_map (reachable' x) (reachable x)).
  - eapply reachable_sim.
  - rewrite list_corresponds_to_finite_ensemble_iff in H |- *.
    i. rewrite H. symmetry. eapply gmu_iff_reachable_seed.
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
  rewrite path_iff_no_dup_walk in PATH. destruct PATH as [WALK' NO_DUP]. inv NO_DUP.
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

Fixpoint propagate_value (fuel : nat) (x : X) : fset A :=
  match fuel with
  | O => seed x
  | S fuel' => FS.union (seed x) (FS.bind (deps x) (propagate_value fuel'))
  end.

Lemma propagate_value_seed (fuel : nat) (x : X) (a : A)
  (IN : a ∈ seed x)
  : a ∈ propagate_value fuel x.
Proof.
  destruct fuel as [ | fuel]; cbn [propagate_value].
  - exact IN.
  - rewrite FS.in_union_iff. left. exact IN.
Qed.

Lemma propagate_value_propagated (fuel : nat) (x : X) (y : X) (a : A)
  (EDGE : y ∈ deps x)
  (IN : a ∈ propagate_value fuel y)
  : a ∈ propagate_value (S fuel) x.
Proof.
  cbn [propagate_value]. rewrite FS.in_union_iff. right.
  rewrite FS.in_bind_iff. exists y. split; assumption.
Qed.

Theorem propagate_value_elim (fuel : nat) (x : X) (a : A)
  (IN : a ∈ propagate_value fuel x)
  : x \in propagate_closure a.
Proof.
  revert x a IN. induction fuel as [ | fuel IH]; intros x a IN; cbn [propagate_value] in IN.
  - eapply propagate_closure_seed. exact IN.
  - rewrite FS.in_union_iff in IN. destruct IN as [SEED_IN | BIND_IN].
    + eapply propagate_closure_seed. exact SEED_IN.
    + rewrite FS.in_bind_iff in BIND_IN. destruct BIND_IN as (y & EDGE & IN').
      eapply propagate_closure_step; [exact EDGE | exact (IH y a IN')].
Qed.

Lemma propagate_value_monotone_step (fuel : nat) (x : X) (a : A)
  (IN : a ∈ propagate_value fuel x)
  : a ∈ propagate_value (S fuel) x.
Proof.
  revert x a IN. induction fuel as [ | fuel IH]; intros x a IN; cbn [propagate_value] in IN |- *.
  - rewrite FS.in_union_iff. left. exact IN.
  - rewrite FS.in_union_iff in IN |- *. destruct IN as [SEED_IN | BIND_IN]; [now left | right].
    rewrite FS.in_bind_iff in BIND_IN |- *. destruct BIND_IN as (y & EDGE & IN').
    exists y. split; [exact EDGE | exact (IH y a IN')].
Qed.

Lemma propagate_value_monotone (fuel1 : nat) (fuel2 : nat) (x : X) (a : A)
  (LE : fuel1 <= fuel2)
  (IN : a ∈ propagate_value fuel1 x)
  : a ∈ propagate_value fuel2 x.
Proof.
  revert fuel1 x a LE IN; induction fuel2 as [ | fuel2 IH]; intros fuel1 x a LE IN.
  - assert (fuel1 = O) as EQ by lia. subst fuel1. exact IN.
  - pose proof (Nat.eq_dec fuel1 (S fuel2)) as [EQ | NE].
    + subst fuel1. exact IN.
    + eapply propagate_value_monotone_step.
      eapply IH with (fuel1 := fuel1) (x := x) (a := a); [lia | exact IN].
Qed.

Theorem propagate_trace_value (x : X) (a : A) (tr : list X) (fuel : nat)
  (TRACE : propagate_trace a x tr)
  (LE : length tr <= fuel)
  : a ∈ propagate_value fuel x.
Proof.
  revert fuel LE; induction TRACE as [x IN | x y tr EDGE TRACE IH]; intros fuel LE.
  - now eapply propagate_value_seed.
  - destruct fuel as [ | fuel]; simpl in LE; [lia | ].
    eapply propagate_value_propagated; [exact EDGE | eapply IH; lia].
Qed.

Theorem propagate_closure_intro (x : X) (a : A)
  (IN : x \in propagate_closure a)
  : exists fuel, a ∈ propagate_value fuel x.
Proof.
  induction IN as [x SEED_IN | x y EDGE CLOSURE IH].
  - exists O. eapply propagate_value_seed. exact SEED_IN.
  - destruct IH as [fuel VALUE_IN]. exists (S fuel). eapply propagate_value_propagated; eauto.
Qed.

Theorem propagate_closure_intro_bounded (fuel : nat) (nodes : fset X) (x : X) (a : A)
  (fuel_ENOUGH : length nodes.(FSet.data) <= fuel)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  (IN : x \in propagate_closure a)
  : a ∈ propagate_value fuel x.
Proof.
  rewrite propagate_closure_iff_trace in IN. destruct IN as [tr TRACE].
  pose proof (propagate_trace_simple_bounded nodes x a tr deps_CLOSED TRACE) as (simple & TRACE' & LENGTH).
  eapply propagate_trace_value with (tr := simple); [exact TRACE' | lia].
Qed.

Theorem propagate_value_iff_closure_bounded (fuel : nat) (nodes : fset X) (x : X) (a : A)
  (fuel_ENOUGH : length nodes.(FSet.data) <= fuel)
  (deps_CLOSED : forall x, forall y, y ∈ deps x -> y ∈ nodes)
  : a ∈ propagate_value fuel x <-> x \in propagate_closure a.
Proof.
  split.
  - exact (propagate_value_elim fuel x a).
  - intros IN. eapply propagate_closure_intro_bounded; eauto.
Qed.

End DIGRAPH.

End DigraphFixedpoint.
