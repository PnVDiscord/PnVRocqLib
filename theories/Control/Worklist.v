Require Import PnV.Prelude.Prelude.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Prelude.X.

Module Worklist.

Section Worklist.

Context {A : Type} {A_isPoset : isPoset A} {HsOrd_A : HsOrd A}.

#[local] Notation "x ∈ xs" := (L.In x (FSet.data xs)).

Fixpoint schedule (next : fin_ensemble A) (seen : fset A) (todo : list A) {struct next} : fset A * list A :=
  match next with
  | [] => (seen, todo)
  | x :: next' => if FS.mem x seen then schedule next' seen todo else schedule next' (FS.add x seen) (x :: todo)
  end.

Theorem schedule_spec (next : fin_ensemble A) (seen : fset A) (todo : list A) seen' todo'
  (H_OBS : schedule next seen todo = (seen', todo'))
  : (forall x, x ∈ seen' <-> (x ∈ seen \/ L.In x next)) /\ (forall x, L.In x todo' <-> (L.In x todo \/ (L.In x next /\ ~ x ∈ seen))).
Proof.
  revert_until next. induction next as [ | v next IH]; simpl; i.
  - splits; intuition congruence.
  - des_ifs.
    + rewrite FS.mem_eq_spec in Heq.
      find* [H_seen H_todo] by IH.
      splits; i.
      * rewrite H_seen. intuition congruence.
      * rewrite H_todo. intuition congruence.
    + rewrite FS.mem_eq_spec in Heq.
      find* [H_seen H_todo] by IH.
      splits; i.
      * rewrite H_seen, FS.in_add_eq_iff. intuition congruence.
      * rewrite H_todo, FS.in_add_eq_iff. simpl.
        destruct (B.decide (v = x)); intuition congruence.
Qed.

Lemma schedule_no_dup (next : fin_ensemble A) (seen : fset A) (todo : list A)
  (H_todo : forall x, L.In x todo -> x ∈ seen)
  (NO_DUP : NoDup todo)
  : NoDup (snd (schedule next seen todo)).
Proof.
  revert_until next. induction next as [ | v next IH]; simpl; i; auto; des_ifs; eapply IH; auto.
  - intros x [EQ | IN]; rewrite FS.in_add_eq_iff; eauto.
  - econs; auto. rewrite FS.mem_eq_spec in Heq. ii. eauto.
Qed.

Lemma schedule_progress (next : fin_ensemble A) (seen : fset A) (todo : list A) seen' todo'
  (H_OBS : schedule next seen todo = (seen', todo'))
  : (seen' = seen /\ todo' = todo) \/ length (FSet.data seen) < length (FSet.data seen').
Proof.
  revert_until next. induction next as [ | v next IH]; simpl; i; des_ifs.
  - left. split; congruence.
  - eapply IH. exact H_OBS.
  - right. rewrite FS.mem_eq_spec in Heq.
    obtain [SEEN _] with H_OBS by schedule_spec.
    assert (FRESH : ~ FS.In v seen) by now rewrite FS.In_eq_iff.
    assert (INCL : incl (FSet.data (FS.add v seen)) (FSet.data seen')) by (intros y IN; rewrite SEEN; auto).
    obtain LE with (fset_NoDup (FS.add v seen)) INCL by NoDup_incl_length.
    rewrite FS.length_add in LE by exact FRESH. lia.
Qed.

Lemma schedule_seen (next : fin_ensemble A) (seen : fset A) (todo : list A) (x : A)
  : x ∈ fst (schedule next seen todo) <-> (x ∈ seen \/ L.In x next).
Proof.
  destruct (schedule next seen todo) as [seen' todo'] eqn: H_OBS; simpl.
  now obtain [? _] with H_OBS by schedule_spec.
Qed.

Lemma schedule_pending (next : fin_ensemble A) (seen : fset A) (todo : list A) (x : A)
  : L.In x (snd (schedule next seen todo)) <-> (L.In x todo \/ (L.In x next /\ ~ x ∈ seen)).
Proof.
  destruct (schedule next seen todo) as [seen' todo'] eqn: H_OBS; simpl.
  now obtain [? ?] with H_OBS by schedule_spec.
Qed.

Variable next : A -> fin_ensemble A.

Variable domain : A -> Prop.

Hypothesis domain_closed : forall x, domain x -> forall y, L.In y (next x) -> domain y.

Hypothesis domain_finite : exists bound : nat, forall xs : fset A, forall INCL : forall x, x ∈ xs -> domain x, length (FSet.data xs) <= bound.

Let State : Type :=
  fset A * list A.

Definition valid (st : State) : Prop :=
  (forall x, x ∈ fst st -> domain x) /\ (forall x, L.In x (snd st) -> x ∈ fst st).

Lemma schedule_valid (seen : fset A) (x : A) (todo : list A)
  (VALID : valid (seen, x :: todo))
  : valid (schedule (next x) seen todo).
Proof.
  destruct VALID as [DOMAIN TODO]. cbn in DOMAIN, TODO.
  destruct (schedule (next x) seen todo) as [seen' todo'] eqn: H_OBS; simpl.
  obtain [SEEN PENDING] with H_OBS by schedule_spec.
  split; cbn; i.
  - rewrite SEEN in H. destruct H; eauto.
  - rewrite PENDING in H. rewrite SEEN. intuition eauto.
Qed.

Inductive beta : State -> State -> Prop :=
  | beta_intro (seen : fset A) (x : A) (todo : list A)
    (VALID : valid (seen, x :: todo))
    : (seen, x :: todo) ~>β schedule (next x) seen todo
  where "st ~>β st'" := (beta st st').

Lemma beta_hasSN
  : SN.hasSN beta.
Proof.
  destruct domain_finite as [bound BOUND].
  enough (SLACK : forall n : nat, forall seen : fset A, bound <= n + length (FSet.data seen) -> forall todo : list A, SN.sn beta (seen, todo)).
  { intros [seen todo]. eapply SLACK with (n := bound). lia. }
  induction n as [ | n IH]; intros seen ROOM todo; induction todo as [ | x todo IH_todo]; econs; intros st' STEP; inv STEP.
  - destruct (schedule (next x) seen todo) as [seen' todo'] eqn: H_OBS.
    obtain [[? ?] | GROW] with H_OBS by schedule_progress; intuition try congruence.
    obtain [DOMAIN' _] with VALID by schedule_valid; rewrite H_OBS in DOMAIN'; cbn [fst] in DOMAIN'.
    obtain LE with DOMAIN' by BOUND. lia.
  - destruct (schedule (next x) seen todo) as [seen' todo'] eqn: H_OBS.
    obtain [[? ?] | GROW] with H_OBS by schedule_progress; intuition try congruence.
    obtain [DOMAIN' _] with VALID by schedule_valid; rewrite H_OBS in DOMAIN'; cbn [fst] in DOMAIN'.
    obtain LE with DOMAIN' by BOUND. eapply IH. lia.
Qed.

Fixpoint run (st : State) (VALID : valid st) (NORMAL : SN.sn beta st) {struct NORMAL} : fset A.
Proof.
  destruct st as [seen [ | x todo]].
  - exact seen.
  - exact (run (schedule (next x) seen todo) (schedule_valid seen x todo VALID) (SN.sn_inv (seen, x :: todo) NORMAL (schedule (next x) seen todo) (beta_intro seen x todo VALID))).
Defined.

Fixpoint run_sound (P : A -> Prop) (st : State)
  (CLOSED : forall x, P x -> forall y, L.In y (next x) -> P y)
  (sn_st : SN.sn beta st)
  (H_valid : valid st)
  (INITIAL : forall x, x ∈ fst st -> P x)
  : forall x, x ∈ run st H_valid sn_st -> P x.
Proof.
  destruct sn_st as [sn_st_inv]. destruct st as [seen [ | x todo]]; simpl.
  - exact INITIAL.
  - set (st' := schedule (next x) seen todo).
    assert (PRESERVED : forall y, y ∈ fst st' -> P y).
    { subst st'. intros y H_y. rewrite schedule_seen in H_y. destruct H_y; eauto.
      eapply CLOSED; eauto. eapply INITIAL. eapply H_valid. cbn; auto.
    }
    exact (run_sound P st' CLOSED (sn_st_inv st' (beta_intro seen x todo H_valid)) (schedule_valid seen x todo H_valid) PRESERVED).
Qed.

Fixpoint run_complete (st : State)
  (sn_st : SN.sn beta st)
  (VALID : valid st)
  (CLOSED : forall x, x ∈ fst st -> forall y, L.In y (next x) -> (y ∈ fst st \/ L.In x (snd st)))
  : (forall x, x ∈ fst st -> x ∈ run st VALID sn_st) /\ (forall x, forall y, x ∈ run st VALID sn_st -> L.In y (next x) -> y ∈ run st VALID sn_st).
Proof.
  destruct sn_st as [sn_st_inv]. destruct st as [seen [ | v todo]]; cbn [run].
  - split; i; auto. find* [IN | []] by CLOSED. exact IN.
  - enough (NEXT_CLOSED : forall x, x ∈ fst (schedule (next v) seen todo) -> forall y, L.In y (next x) -> (y ∈ fst (schedule (next v) seen todo) \/ L.In x (snd (schedule (next v) seen todo)))).
    { obtain [MONOTONE CLOSED_out] with (sn_st_inv _ (beta_intro seen v todo VALID)) (schedule_valid seen v todo VALID) NEXT_CLOSED by run_complete.
      split; auto. i. eapply MONOTONE. rewrite schedule_seen. auto.
    }
    intros x IN y EDGE. rewrite schedule_seen in IN. simpl in *. destruct IN as [IN | IN].
    + find* [IN' | [EQ | IN_todo]] by CLOSED.
      * left. rewrite schedule_seen. auto.
      * subst x. left. rewrite schedule_seen. auto.
      * right. rewrite schedule_pending. auto.
    + destruct (FS.mem x seen) eqn: OBS.
      * rewrite FS.mem_eq_spec in OBS. find* [IN_y | [EQ | IN_todo]] by CLOSED.
        { left. rewrite schedule_seen. auto. }
        { subst x. left. rewrite schedule_seen. auto. }
        { right. rewrite schedule_pending. auto. }
      * rewrite FS.mem_eq_spec in OBS. right. rewrite schedule_pending. auto.
Qed.

Definition closure (initial : fset A) (H_initial : forall x : A, forall IN : x ∈ initial, domain x) : fset A :=
  run (initial, FSet.data initial) (conj H_initial (fun x : A => fun IN : x ∈ initial => IN)) (SN.sn_intro_generator 1000 beta_hasSN (initial, FSet.data initial)).

Corollary closure_sound (P : A -> Prop) (initial : fset A)
  (H_initial : forall x, x ∈ initial -> domain x)
  (CLOSED_P : forall x, forall y, P x -> L.In y (next x) -> P y)
  (INITIAL_P : forall x, x ∈ initial -> P x)
  : forall x, x ∈ closure initial H_initial -> P x.
Proof.
  eapply run_sound; i; eauto.
Qed.

Corollary closure_complete (initial : fset A)
  (H_initial : forall x, x ∈ initial -> domain x)
  : (forall x, x ∈ initial -> x ∈ closure initial H_initial) /\ (forall x, forall y, x ∈ closure initial H_initial -> L.In y (next x) -> y ∈ closure initial H_initial).
Proof.
  eapply run_complete with (st := (initial, FSet.data initial)); cbn; i; auto.
Qed.

End Worklist.

End Worklist.
