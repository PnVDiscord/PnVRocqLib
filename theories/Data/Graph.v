Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Category.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Data.FiniteMap.
Require Import PnV.Prelude.X.

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
    pose proof (In_dec v' (v0 :: p)) as [ELEM | NOT_IN].
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

#[local] Notation "x ∈ xs" := (L.In x xs.(FSet.data)).

Context {V_isPoset : isPoset V} {HsOrd_V : HsOrd V}.

Variable nodes : fset V.

Hypothesis arc_dec : forall v : V, forall v' : V, B.Decision ((v, v') \in E).

Definition successors (v : V) : list V :=
  filter (fun v' => decideb ((v, v') \in E)) nodes.(FSet.data).

Lemma in_successors_iff (v : V) (v' : V)
  : In v' (successors v) <-> v' ∈ nodes /\ (v, v') \in E.
Proof.
  unfold successors. rewrite filter_In. simpl; des_ifs; intuition congruence.
Qed.

Fixpoint reachables_worklist (fuel : nat) (seen : fset V) {struct fuel} : list V -> fset V :=
  match fuel with
  | O => fun _ => seen
  | S fuel' =>
    fix go (todo : list V) {struct todo} : fset V :=
    match todo with
    | [] => seen
    | v :: todo' => if FS.mem v seen then go todo' else reachables_worklist fuel' (FS.add v seen) (successors v ++ todo')
    end
  end.

Definition reachables (v : V) : fset V :=
  reachables_worklist (length nodes.(FSet.data)) FS.empty [v].

Lemma reachables_worklist_sound (P : V -> Prop) (fuel : nat) (seen : fset V) (todo : list V)
  (CLOSED : forall v, forall v', P v -> (v, v') \in E -> P v')
  (H_seen : forall v, v ∈ seen -> P v)
  (H_todo : forall v, L.In v todo -> P v)
  : forall v : V, forall IN : v ∈ reachables_worklist fuel seen todo, P v.
Proof.
  revert_until fuel. induction fuel as [ | fuel IH]; ii; auto.
  revert_until todo. induction todo as [ | v todo IH_todo]; simpl; ii; auto. des_ifs.
  - eapply IH_todo; auto.
  - eapply IH with (seen := FS.add v seen) (todo := successors v ++ todo); auto.
    + intros y H_y. rewrite FS.in_add_iff in H_y. des; ss; eauto.
    + intros y H_y. rewrite in_app_iff in H_y. des; ss; auto.
      eapply CLOSED with (v := v); ss; auto. now rewrite in_successors_iff in H_y.
Qed.

Hypothesis nodes_closed : forall v, v ∈ nodes -> forall v', (v, v') \in E -> v' ∈ nodes.

Lemma walk_in_nodes (v : V) (v' : V) (w : list V)
  (WALK : v ~~~[ w ]~~> v')
  (IN : v ∈ nodes)
  : v' ∈ nodes.
Proof.
  induction WALK; eauto.
Qed.

Lemma reachables_worklist_complete (fuel : nat) (seen : fset V) (todo : list V) (remaining : list V)
  (H_seen : forall v, v ∈ seen -> v ∈ nodes)
  (H_todo : forall v, L.In v todo -> v ∈ nodes)
  (CLOSED : forall v, forall v', v ∈ seen -> (v, v') \in E -> (v' ∈ seen \/ In v' todo))
  (COVER : forall v, v ∈ nodes -> (v ∈ seen \/ L.In v remaining))
  (BOUND : length remaining <= fuel)
  : forall v : V, forall v' : V, forall w : list V, forall FRONT : v ∈ seen \/ In v todo, forall H_walk : v ~~~[ w ]~~> v', v' ∈ reachables_worklist fuel seen todo.
Proof.
  revert_until fuel; induction fuel as [ | fuel IH]; simpl; i.
  - assert (IN : v' ∈ nodes).
    { eapply walk_in_nodes with (v := v) (w := w); auto. des; auto. }
    obtain [YES | NO] with IN by COVER; auto.
    destruct remaining; ss; lia.
  - revert_until todo; induction todo as [ | v todo IH_todo]; simpl; i.
    { des; [induction H_walk as [ | v0 v1 w EDGE WALK IH_walk] | tauto]; [auto | eapply IH_walk].
      now find* [YES | []] by CLOSED.
    }
    { des_ifs.
      - rewrite FS.mem_spec in Heq. eapply IH_todo with (remaining := remaining) (v := v0) (w := w); eauto.
        + intros x y H_x H_edge. find* [YES | [EQ | YES]] by CLOSED; done.
        + des; auto. left; congruence.
      - rewrite FS.mem_spec in Heq.
        assert (v_in_nodes : v ∈ nodes) by now eapply H_todo; left.
        assert (v_in_remaining : L.In v remaining).
        { find* [? | ?] by COVER; tauto. }
        eapply IH with (remaining := remove (fun x => fun y => B.decide (x = y)) v remaining) (v := v0) (w := w); eauto.
        + intros x x_in. rewrite FS.in_add_iff in x_in. destruct x_in; eauto.
        + intros x x_in. rewrite L.in_app_iff in x_in. destruct x_in as [x_in | x_in].
          * now rewrite in_successors_iff in x_in.
          * eapply H_todo. now right.
        + intros x y x_in H_edge. rewrite FS.in_add_iff in x_in. destruct x_in as [EQ | IN].
          * subst x. right. rewrite in_app_iff. left. rewrite in_successors_iff; eauto.
          * rewrite FS.in_add_iff. rewrite L.in_app_iff.
            find* [YES | [EQ | YES]] by CLOSED; tauto.
        + intros x x_in. destruct (FS.mem x (FS.add v seen)) eqn: H_OBS.
          * left. now rewrite FS.mem_spec in H_OBS.
          * right. rewrite FS.mem_spec in H_OBS. rewrite FS.in_add_iff in H_OBS. rewrite L.in_remove_iff.
            find* ? by COVER; split; intuition congruence.
        + obtain ? with v_in_remaining by (remove_length_lt (EQ_DEC := fun x => fun y => B.decide (x = y))).
          lia.
        + rewrite FS.in_add_iff. rewrite L.in_app_iff. done.
    }
Qed.

Theorem reachables_correct (v : V)
  (IN : v ∈ nodes)
  : forall v' : V, v' ∈ reachables v <-> (exists w, w \in Walks v v').
Proof.
  split.
  - intros REACHABLE. unfold reachables in REACHABLE.
    enough (exists w, v ~~~[ w ]~~> v') as [w H_walk] by now exists (v :: w); econs.
    eapply reachables_worklist_sound with (P := fun x => exists w, v ~~~[ w ]~~> x) (fuel := length nodes.(FSet.data)) (seen := FS.empty) (todo := [v]).
    + intros x y [w WALK] EDGE. exists (w ++ [y]). eapply walk_app; eauto.
    + intros x. rewrite FS.in_empty_iff. tauto.
    + simpl. intros x [EQ | []]. subst x. exists []. econs 1.
    + exact REACHABLE.
  - intros [w WALK]. inversion WALK as [w' H_walk]; subst; clear WALK.
    eapply reachables_worklist_complete with (remaining := nodes.(FSet.data)) (v := v) (w := w'); simpl; done.
Qed.

End REACHABILITY.

Section PROPAGATION.

#[local] Notation "x ∈ xs" := (L.In x xs.(FSet.data)).

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

Hypothesis arc_dec : forall v : V, forall v' : V, B.Decision ((v, v') \in E).

Definition least_solution (v : V) : fset X :=
  FS.bind (reachables nodes arc_dec v) lookup_seed.

Hypothesis nodes_closed : forall v, v ∈ nodes -> forall v', (v, v') \in E -> v' ∈ nodes.

Theorem least_solution_correct (v : V)
  (IN : v ∈ nodes)
  : forall x : X, x ∈ least_solution v <-> (exists w, w \in propagate_trace v x).
Proof.
  intros x. unfold least_solution. rewrite FS.in_bind_iff. split.
  - intros (v' & H_reachable & H_in_seed).
    rewrite reachables_correct in H_reachable by eauto.
    destruct H_reachable as [w H_walks]. inv H_walks.
    eexists. rewrite propagate_trace_iff. eauto.
  - intros [w H_trace]. rewrite propagate_trace_iff in H_trace.
    destruct H_trace as (v' & H_walk & H_in_seed). exists v'. split; auto.
    rewrite reachables_correct by eauto. exists (v :: w). econs; eauto.
Qed.

Theorem least_solution_of_recursive_equation
  : recursive_equation (fun v : V => { x : X | x ∈ least_solution v }%function) /\ ⟪ LEAST : forall F, recursive_equation F -> forall v, v ∈ nodes -> E.fromList (least_solution v).(FSet.data) \subseteq F v ⟫.
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
