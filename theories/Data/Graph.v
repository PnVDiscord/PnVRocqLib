Require Import PnV.Prelude.Prelude.
Require Import PnV.Control.Category.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Data.FiniteMap.
Require Import PnV.Prelude.X.

#[local] Abbreviation In := L.In.
#[local] Infix "\in" := E.In : type_scope.

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

Section Finite_NoDup_Path.

Let beta (v : V) (v' : V) : Prop :=
  (v, v') \in E.

#[local] Infix "~>β" := beta.

Variable next : V -> V.

Lemma finite_path_sn (v_s : V) (v_t : V) (v : V) (p : list V)
  (H_beta : forall v : V, forall v' : V, v ~>β v' -> (next v = v' /\ v' ≠ v_s))
  (CLOSED : next v_t = v_s)
  (H_path : v ---[ p ]--> v_t)
  : SN.sn beta v.
Proof.
  induction H_path as [ | v0 v1 p EDGE H_path IH NOT_IN].
  - econs; intros v' EDGE.
    find* [NEXT NOT_START] by H_beta.
    congruence.
  - econs; intros v' EDGE'.
    obtain [Hv1 _] with EDGE by H_beta.
    obtain [Hv' _] with EDGE' by H_beta.
    congruence.
Defined.

Theorem finite_nodup_path_sn (v_s : V) (v_t : V) (w : list V)
  (H_beta : forall v : V, forall v' : V, v ~>β v' -> (next v = v' /\ v' ≠ v_s))
  (NO_DUP : NoDup (v_s :: w))
  (H_walk : v_s ~~~[ w ]~~> v_t)
  (CLOSED : next v_t = v_s)
  : SN.sn beta v_s.
Proof.
  eapply finite_path_sn with (p := w).
  - exact H_beta.
  - exact CLOSED.
  - eapply no_dup_walk_is_path; eauto.
Defined.

End Finite_NoDup_Path.

Variant Walk (v_s : V) (v_t : V) : ensemble (list V) :=
  | Walk_intro (w : list V)
    (H_walk : v_s ~~~[ w ]~~> v_t)
    : v_s :: w \in Walk v_s v_t.

Variant Path (v_s : V) (v_t : V) : ensemble (list V) :=
  | Path_intro (p : list V)
    (H_path : v_s ---[ p ]--> v_t)
    : v_s :: p \in Path v_s v_t.

Definition isAcyclic : Prop :=
  forall v : V, forall w : list V, v ~~~[ w ]~~> v -> w = [].

End Digraph.

#[global] Arguments isAcyclic : clear implicits.

End Digraph1.
