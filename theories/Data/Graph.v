Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.X.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Data.FiniteMap.
Require Import PnV.Control.Worklist.

#[local] Abbreviation In := L.In.
#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "\subseteq" := E.isSubsetOf : type_scope.

Universe U_vertices.

Module DIGRAPH.

#[projections(primitive)]
Class t : Type :=
  mk
  { vertices : Type@{U_vertices}
  ; arcs : ensemble@{U_vertices} (vertices * vertices)
  } as G.

End DIGRAPH.

Module Digraph1.

Section Digraph.

#[local] Abbreviation vertices := DIGRAPH.vertices.
#[local] Abbreviation arcs := DIGRAPH.arcs.

Context {G : DIGRAPH.t}.

#[local] Abbreviation V := G.(vertices).
#[local] Abbreviation E := G.(arcs).

Inductive walk (v : V) : V -> ensemble (list V) :=
  | walk_refl
    : v ~~~[ [] ]~~> v
  | walk_step (v0 : V) (v1 : V) (w : list V)
    (H_edge : (v0, v1) \in E)
    (H_walk : v1 ~~~[ w ]~~> v)
    : v0 ~~~[ v1 :: w ]~~> v
  where " src ~~~[ w ]~~> tgt " := (w \in walk tgt src) : type_scope.

#[local] Hint Constructors walk : core.

Inductive path (v : V) : V -> ensemble (list V) :=
  | path_refl
    : v ---[ [] ]--> v
  | path_step (v0 : V) (v1 : V) (p : list V)
    (H_edge : (v0, v1) \in E)
    (H_path : v1 ---[ p ]--> v)
    (NOT_IN : ~ In v0 (v1 :: p))
    : v0 ---[ v1 :: p ]--> v
  where " src ---[ p ]--> tgt " := (p \in path tgt src) : type_scope.

#[local] Hint Constructors path : core.

Definition trail (v : V) : V -> ensemble (list V) :=
  fun v0 : V => fun t : list V => v0 ~~~[ t ]~~> v /\ NoDup (L.mk_edge_seq v0 t).

#[local] Notation " src ===[ t ]==> tgt " := (t \in trail tgt src) : type_scope.

Variant Walks (v_s : V) (v_t : V) : ensemble (list V) :=
  | inWalks (w : list V)
    (H_walk : v_s ~~~[ w ]~~> v_t)
    : v_s :: w \in Walks v_s v_t.

Variant Paths (v_s : V) (v_t : V) : ensemble (list V) :=
  | inPaths (p : list V)
    (H_path : v_s ---[ p ]--> v_t)
    : v_s :: p \in Paths v_s v_t.

Variant Trails (v_s : V) (v_t : V) : ensemble (list V) :=
  | inTrails (t : list V)
    (H_path : v_s ===[ t ]==> v_t)
    : v_s :: t \in Trails v_s v_t.

Definition isAcyclic : Prop :=
  forall v : V, forall w : list V, v ~~~[ w ]~~> v -> w = [].

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
  - find* (p' & PATH1 & p'' & PATH2 & EQ) by IH.
    exists (v1 :: p'). split.
    + econstructor 2; eauto. subst p. ii. contradiction NOT_IN. ss!.
    + exists p''. split; [exact PATH2 | now rewrite EQ].
Qed.

Hypothesis In_dec : forall v : V, forall vs : list V, In v vs \/ ~ In v vs.

Theorem walk_finds_path (v0 : V) (v : V) (w : list V)
  (WALK : v0 ~~~[ w ]~~> v)
  : exists p, v0 ---[ p ]--> v.
Proof.
  revert v0 v WALK. induction w as [ | v' w IH] using List.rev_ind; i.
  - inv WALK. exists []. econstructor 1.
  - rewrite -> walk_app_iff in WALK. destruct WALK as (v1 & WALK1 & WALK2).
    inv WALK2. inv H_walk. find* [p PATH] by IH.
    find* [ELEM | NOT_IN] by (In_dec v' (v0 :: p)).
    + inv ELEM.
      * exists []. econstructor 1.
      * find* (p' & PATH' & _) by mk_subpath. ss!.
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

Lemma path_implies_trail (v0 : V) (v : V) (p : list V)
  (PATH : v0 ---[ p ]--> v)
  : v0 ===[ p ]==> v.
Proof.
  rewrite path_iff_no_dup_walk in PATH.
  destruct PATH as [WALK NO_DUP]. split.
  - exact WALK.
  - eapply L.no_dup_mk_edge_seq. now inv NO_DUP.
Qed.

Section deterministic_walk_to_sink_guarantees_sn.

Let beta (v : V) (v' : V) : Prop :=
  (v, v') \in E.

#[local] Infix "~>β" := beta.

Variable next : V -> V.

Lemma deterministic_walk_to_sink_guarantees_sn (v_s : V) (v_t : V)
  (H_beta : forall v : V, forall v' : V, forall E_v_v' : v ~>β v', next v = v' /\ v' ≠ v_s)
  (CLOSED : next v_t = v_s)
  : forall v : V, ⟪ walk_to_sink : exists w, v ~~~[ w ]~~> v_t ⟫ -> SN.sn beta v.
Proof.
  intros v [w H_walk]. induction H_walk as [ | v0 v1 w EDGE H_walk IH]; econs; intros v' EDGE'.
  - obtain [Hv' H_ne] with EDGE' by H_beta.
    congruence.
  - obtain [Hv1 _] with EDGE by H_beta.
    obtain [Hv' _] with EDGE' by H_beta.
    congruence.
Defined.

End deterministic_walk_to_sink_guarantees_sn.

Section REACHABILITY.

#[local] Notation "x ∈ xs" := (L.In x (FSet.data xs)).

Context {V_isPoset : isPoset V} {HsOrd_V : HsOrd V}.

Variable nodes : fset V.

Variable adjacency : V -> fin_ensemble V.

Hypothesis adjacency_correct : forall v, forall v', In v' (adjacency v) <-> (v, v') \in E.

Hypothesis nodes_closed : forall v, v ∈ nodes -> forall v', (v, v') \in E -> v' ∈ nodes.

Lemma reachables_domain_closed (x : V)
  (IN : x ∈ nodes)
  : forall y, In y (adjacency x) -> y ∈ nodes.
Proof.
  intros y EDGE. rewrite adjacency_correct in EDGE. eauto.
Qed.

Lemma reachables_domain_finite
  : exists bound, forall xs : fset V, (forall x, x ∈ xs -> x ∈ nodes) -> length (FSet.data xs) <= bound.
Proof.
  exists (length (FSet.data nodes)). intros xs SUBSET.
  eapply NoDup_incl_length; [eapply fset_NoDup | exact SUBSET].
Qed.

Lemma reachables_initial_in_domain (v : V)
  (IN : FS.mem v nodes = true)
  : forall x, x ∈ FS.add v FS.empty -> x ∈ nodes.
Proof.
  rewrite FS.mem_eq_spec in IN. intros x H_x.
  rewrite FS.in_add_eq_iff, FS.in_empty_eq_iff in H_x.
  find* [EQ | []] by H_x. subst x. exact IN.
Qed.

Definition reachables (v : V) : fset V.
Proof.
  destruct (Bool.bool_dec (FS.mem v nodes) true) as [IN | OUT].
  - exact (Worklist.closure adjacency (fun x => x ∈ nodes) reachables_domain_closed reachables_domain_finite (FS.add v FS.empty) (reachables_initial_in_domain v IN)).
  - exact (FS.add v FS.empty).
Defined.

Lemma walk_in_nodes (v : V) (v' : V) (w : list V)
  (H_walk : v ~~~[ w ]~~> v')
  (IN : v ∈ nodes)
  : v' ∈ nodes.
Proof.
  induction H_walk; eauto.
Qed.

Lemma reachables_closed (v : V)
  (IN : v ∈ nodes)
  : v ∈ reachables v /\ (forall x, x ∈ reachables v -> forall y, (x, y) \in E -> y ∈ reachables v).
Proof.
  assert (MEM : FS.mem v nodes = true) by now rewrite FS.mem_eq_spec.
  unfold reachables. destruct (Bool.bool_dec (FS.mem v nodes) true) as [OBS | OBS]; [ | contradiction].
  find* [INIT STEP] by (Worklist.closure_complete adjacency (fun x => x ∈ nodes) reachables_domain_closed reachables_domain_finite (FS.add v FS.empty) (reachables_initial_in_domain v OBS)).
  split.
  - eapply INIT. rewrite FS.in_add_eq_iff. auto.
  - i. eapply STEP; eauto. now rewrite adjacency_correct.
Qed.

Theorem reachables_correct (v : V)
  (IN : v ∈ nodes)
  : forall v' : V, v' ∈ reachables v <-> (exists w, w \in Walks v v').
Proof.
  split.
  - intros REACHABLE. unfold reachables in REACHABLE.
    destruct (Bool.bool_dec (FS.mem v nodes) true) as [OBS | OBS].
    + enough (exists w, v ~~~[ w ]~~> v') as [w H_walk] by now exists (v :: w); econs.
      eapply Worklist.closure_sound with (P := fun v' => exists w, v ~~~[ w ]~~> v'); eauto.
      * intros x y [w WALK] EDGE. rewrite adjacency_correct in EDGE.
        exists (w ++ [y]). eapply walk_app; eauto.
      * intros x H_x. rewrite FS.in_add_eq_iff, FS.in_empty_eq_iff in H_x.
        find* [EQ | []] by H_x. subst x. exists []. econs.
    + contradiction OBS. now rewrite FS.mem_eq_spec.
  - intros [w WALK]. inv WALK.
    obtain [INIT STEP] with IN by reachables_closed.
    set (reached := reachables v) in *. clearbody reached. clear IN.
    induction H_walk; eauto.
Qed.

End REACHABILITY.

Section PROPAGATION.

#[local] Notation "x ∈ xs" := (L.In x (FSet.data xs)).

Context {X : Type} {V_isPoset : isPoset V} {X_isPoset : isPoset X} {HsOrd_V : HsOrd V} {HsOrd_X : HsOrd X}.

Variable seed : fpmap V (fset X).

Definition lookup_seed (v : V) : fset X :=
  match FPM.lookup v seed with
  | None => FS.empty
  | Some xs => xs
  end.

Inductive propagate_trace (v : V) (x : X) : ensemble (list V) :=
  | propagate_trace_init
    (H_in_seed : x ∈ lookup_seed v)
    : [] \in propagate_trace v x
  | propagate_trace_step (v' : V) (w : list V)
    (H_edge : (v, v') \in E)
    (H_in_closure : w \in propagate_trace v' x)
    : v' :: w \in propagate_trace v x.

#[local] Hint Constructors propagate_trace : core.

Lemma propagate_trace_iff (v : V) (x : X) (w : list V)
  : w \in propagate_trace v x <-> (exists v', v ~~~[ w ]~~> v' /\ x ∈ lookup_seed v').
Proof.
  split.
  - intros H_trace. induction H_trace; des; eauto.
  - intros (v' & H_walk & H_in_seed). induction H_walk; eauto.
Qed.

Variable nodes : fset V.

Definition recursive_equation (F : V -> ensemble X) : Prop :=
  forall v : V, forall IN : v ∈ nodes, forall x : X, x \in F v <-> ⟪ UNFOLD : x ∈ lookup_seed v \/ (exists v', x \in F v' /\ (v, v') \in E) ⟫.

Variable adjacency : V -> fin_ensemble V.

Definition reverse_adjacency : fpmap V (fset V) :=
  FS.fold (fun table => fun v => fold_left (fun table => fun v' => FPM.add v' v table) (adjacency v) table) nodes FPM.empty.

Lemma lookup_reverse_edges (v : V) (vs : list V) (table : fpmap V (fset V)) (x : V) (y : V)
  : FS.In x (FPM.lookup_set (fold_left (fun table => fun v' => FPM.add v' v table) vs table) y) <-> (FS.In x (FPM.lookup_set table y) \/ (x = v /\ L.In y vs)).
Proof.
  revert table. induction vs as [ | v' vs IH]; cbn [fold_left]; i.
  - simpl. tauto.
  - rewrite IH, FPM.in_add_iff, !Poset_eqProp_spec. simpl. intuition congruence.
Qed.

Lemma lookup_reverse_nodes (vs : list V) (table : fpmap V (fset V)) (x : V) (y : V)
  : FS.In x (FPM.lookup_set (fold_left (fun table => fun v => fold_left (fun table => fun v' => FPM.add v' v table) (adjacency v) table) vs table) y) <-> (FS.In x (FPM.lookup_set table y) \/ (L.In x vs /\ L.In y (adjacency x))).
Proof.
  revert table. induction vs as [ | v vs IH]; cbn [fold_left]; i.
  - simpl. tauto.
  - rewrite IH, lookup_reverse_edges. simpl. intuition congruence.
Qed.

Lemma lookup_reverse_correct (v : V) (v' : V)
  : v ∈ FPM.lookup_set reverse_adjacency v' <-> (v ∈ nodes /\ L.In v' (adjacency v)).
Proof.
  unfold reverse_adjacency. rewrite FS.fold_spec, <- FS.In_eq_iff, lookup_reverse_nodes.
  unfold FPM.lookup_set. rewrite FPM.lookup_empty, FS.in_empty_iff. tauto.
Qed.

Definition propagation_initial : fset (V * X) :=
  FPM.initial_facts nodes seed.

Lemma in_propagation_initial_iff (v : V) (x : X)
  : (v, x) ∈ propagation_initial <-> (v ∈ nodes /\ x ∈ lookup_seed v).
Proof.
  eapply FPM.in_initial_facts_eq_iff.
Qed.

Definition propagation_values : fset X :=
  FS.map (@snd V X) propagation_initial.

Definition propagation_next (reversed : fpmap V (fset V)) (p : V * X) : fin_ensemble (V * X) :=
  FS.fold (fun next => fun v => (v, snd p) :: next) (FPM.lookup_set reversed (fst p)) [].

Lemma in_propagation_next_iff (v : V) (v' : V) (x : X) (x' : X)
  : L.In (v, x) (propagation_next reverse_adjacency (v', x')) <-> (v ∈ nodes /\ L.In v' (adjacency v) /\ x' = x).
Proof.
  unfold propagation_next. rewrite FS.fold_spec, <- fold_left_rev_right.
  change (L.In (v, x) (map (fun u => (u, x')) (rev (FSet.data (FPM.lookup_set reverse_adjacency v')))) <-> (v ∈ nodes /\ L.In v' (adjacency v) /\ x' = x)).
  rewrite in_map_iff. split.
  - intros (u & EQ & H_u). inv EQ. rewrite <- In_rev, lookup_reverse_correct in H_u. tauto.
  - intros (H_v & H_edge & EQ). subst x'. exists v. split; auto.
    rewrite <- In_rev, lookup_reverse_correct; auto.
Qed.

Definition propagation_domain (p : V * X) : Prop :=
  fst p ∈ nodes /\ snd p ∈ propagation_values.

Lemma propagation_domain_closed
  : forall p, propagation_domain p -> forall q, L.In q (propagation_next reverse_adjacency p) -> propagation_domain q.
Proof.
  intros [v' x'] H_domain [v x] H_next. rewrite in_propagation_next_iff in H_next.
  unfold propagation_domain in *. simpl in *. des; subst; auto.
Qed.

Lemma propagation_domain_finite
  : exists bound, forall facts : fset (V * X), (forall p, p ∈ facts -> propagation_domain p) -> length (FSet.data facts) <= bound.
Proof.
  exists (length (FSet.data nodes) * length (FSet.data propagation_values)).
  intros facts H_facts. rewrite <- length_prod.
  eapply NoDup_incl_length; [eapply fset_NoDup | ].
  intros [v x] H_in. rewrite in_prod_iff. exact (H_facts (v, x) H_in).
Qed.

Lemma propagation_initial_in_domain
  : forall p, p ∈ propagation_initial -> propagation_domain p.
Proof.
  intros [v x] H_in. change (v ∈ nodes /\ x ∈ propagation_values). split.
  - rewrite in_propagation_initial_iff in H_in. tauto.
  - unfold propagation_values. rewrite FS.in_map_eq_iff. exists (v, x); auto.
Qed.

Definition propagation_facts : fset (V * X) :=
  let initial := propagation_initial in
  if FS.is_empty initial then
    initial
  else
    let reversed := reverse_adjacency in
    Worklist.closure (propagation_next reversed) propagation_domain propagation_domain_closed propagation_domain_finite initial propagation_initial_in_domain.

Definition propagation : fpmap V (fset X) :=
  FPM.fromFSet propagation_facts.

Definition least_solution : V -> fset X :=
  let solution := propagation in
  FPM.lookup_set solution.

Lemma propagation_facts_complete
  : (forall v, forall x, v ∈ nodes -> x ∈ lookup_seed v -> (v, x) ∈ propagation_facts) /\ (forall v, forall v', forall x, v ∈ nodes -> L.In v' (adjacency v) -> (v', x) ∈ propagation_facts -> (v, x) ∈ propagation_facts).
Proof.
  assert (SPEC : (forall p, p ∈ propagation_initial -> p ∈ propagation_facts) /\ (forall p, forall q, p ∈ propagation_facts -> L.In q (propagation_next reverse_adjacency p) -> q ∈ propagation_facts)).
  { unfold propagation_facts. destruct (FS.is_empty propagation_initial) eqn: EMPTY.
    - rewrite FS.is_empty_spec in EMPTY. rewrite EMPTY. simpl. tauto.
    - eapply Worklist.closure_complete.
  }
  find* [INITIAL CLOSED] by SPEC. split; i.
  - eapply INITIAL. rewrite in_propagation_initial_iff; auto.
  - eapply CLOSED; eauto. rewrite in_propagation_next_iff; auto.
Qed.

Hypothesis adjacency_correct : forall v, forall v', L.In v' (adjacency v) <-> (v, v') \in E.

Lemma propagation_facts_sound (v : V) (x : X)
  (H_fact : (v, x) ∈ propagation_facts)
  : v ∈ nodes /\ (exists w, w \in propagate_trace v x).
Proof.
  unfold propagation_facts in H_fact.
  destruct (FS.is_empty propagation_initial) eqn: EMPTY.
  { rewrite FS.is_empty_spec in EMPTY. rewrite EMPTY in H_fact. contradiction. }
  eapply Worklist.closure_sound with (P := fun p : V * X => fst p ∈ nodes /\ (exists w, w \in propagate_trace (fst p) (snd p))) in H_fact.
  - exact H_fact.
  - intros [v' x'] [v0 x0] H_trace H_next. rewrite in_propagation_next_iff in H_next.
    simpl in *. find* [H_v' [w H_trace']] by H_trace. find* (H_v0 & H_edge & EQ) by H_next.
    subst x0. split; auto. exists (v' :: w). econs; eauto. now rewrite <- adjacency_correct.
  - intros [v0 x0] H_in. rewrite in_propagation_initial_iff in H_in. simpl. des; split; eauto.
Qed.

Hypothesis nodes_closed : forall v, v ∈ nodes -> forall v', (v, v') \in E -> v' ∈ nodes.

Lemma least_solution_correct (v : V)
  (IN : v ∈ nodes)
  : forall x : X, x ∈ least_solution v <-> (exists w, w \in propagate_trace v x).
Proof.
  intros x. unfold least_solution, propagation. rewrite FPM.fromFSet_correct_eq. split.
  - intros H_fact. obtain [_ H_trace] with H_fact by propagation_facts_sound. exact H_trace.
  - intros [w H_trace]. find* [INITIAL CLOSED] by propagation_facts_complete.
    induction H_trace; eauto. eapply CLOSED; eauto. now rewrite adjacency_correct.
Qed.

Theorem least_solution_of_recursive_equation
  : recursive_equation (fun v : V => { x : X | x ∈ least_solution v }%function) /\ ⟪ LEAST : forall F, recursive_equation F -> forall v, v ∈ nodes -> E.fromList (FSet.data (least_solution v)) \subseteq F v ⟫.
Proof.
  split.
  - intros v IN x. unnw. unfold E.In at 1 2. rewrite least_solution_correct by eauto. split.
    + intros [w H_trace]. inv H_trace; auto. right. esplits; eauto. rewrite least_solution_correct; eauto.
    + intros [H_in_seed | (v' & H_in_solution & H_edge)]; eauto.
      rewrite least_solution_correct in H_in_solution by eauto.
      destruct H_in_solution as [w H_trace]. exists (v' :: w). econs; eauto.
  - intros F H_rec v IN x H_x. rewrite E.in_fromList_iff in H_x.
    rewrite least_solution_correct in H_x by eauto.
    destruct H_x as [w H_trace]. induction H_trace; eapply H_rec; eauto. right; esplits; eauto.
Qed.

End PROPAGATION.

End Digraph.

#[global] Arguments isAcyclic : clear implicits.

End Digraph1.
