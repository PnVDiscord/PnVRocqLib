Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.Data.Vector.
Require Import Coq.Arith.Wf_nat.
Require Import PnV.Logic.BasicFol.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.
#[local] Notation In := List.In.

#[global] Hint Rewrite L.forallb_forall : simplication_hints.

Import FolNotations.

Section HENKIN.

Import ListNotations.

#[local] Infix "=~=" := is_similar_to : type_scope.

Definition Henkin_constants : Set := nat.

Context {L : language}.

Let L' : language := augmented_language L Henkin_constants.

Fixpoint HC_occurs_in_trm (hc : Henkin_constants) (t : trm L') : bool :=
  match t with
  | Var_trm x => false
  | Fun_trm f ts => HC_occurs_in_trms hc ts
  | Con_trm c =>
    match c with
    | inl cc => false
    | inr hc' => Nat.eqb hc hc'
    end
  end
with HC_occurs_in_trms {n : nat} (hc : Henkin_constants) (ts : trms L' n) : bool :=
  match ts with
  | O_trms => false
  | S_trms n t ts => HC_occurs_in_trm hc t || HC_occurs_in_trms (n := n) hc ts
  end.

#[local] Opaque HC_occurs_in_trm HC_occurs_in_trms.

Lemma HC_occurs_in_trm_Var_trm hc x
  : HC_occurs_in_trm hc (Var_trm x) = false.
Proof.
  reflexivity.
Defined.

Lemma HC_occurs_in_trm_Fun_trm hc f ts
  : HC_occurs_in_trm hc (Fun_trm f ts) = HC_occurs_in_trms hc ts.
Proof.
  reflexivity.
Defined.

Lemma HC_occurs_in_trm_Con_trm hc c
  : HC_occurs_in_trm hc (Con_trm c) = (match c with inl cc => false | inr hc' => Nat.eqb hc hc' end).
Proof.
  reflexivity.
Defined.

#[local] Hint Rewrite HC_occurs_in_trm_Var_trm HC_occurs_in_trm_Fun_trm HC_occurs_in_trm_Con_trm : simplication_hints.

Lemma HC_occurs_in_trms_O_trms hc
  : HC_occurs_in_trms hc O_trms = false.
Proof.
  reflexivity.
Defined.

Lemma HC_occurs_in_trms_S_trms hc n t ts
  : HC_occurs_in_trms hc (S_trms n t ts) = HC_occurs_in_trm hc t || HC_occurs_in_trms hc ts.
Proof.
  reflexivity.
Defined.

#[local] Hint Rewrite HC_occurs_in_trms_O_trms HC_occurs_in_trms_S_trms : simplication_hints.

Fixpoint HC_occurs_in_frm (hc : Henkin_constants) (p : frm L') : bool :=
  match p with
  | Rel_frm R ts => HC_occurs_in_trms hc ts
  | Eqn_frm t1 t2 => HC_occurs_in_trm hc t1 || HC_occurs_in_trm hc t2
  | Neg_frm p1 => HC_occurs_in_frm hc p1
  | Imp_frm p1 p2 => HC_occurs_in_frm hc p1 || HC_occurs_in_frm hc p2
  | All_frm y p1 => HC_occurs_in_frm hc p1
  end.

Fixpoint accum_HCs_trm (t : trm L') : list Henkin_constants :=
  match t with
  | Var_trm x => []
  | Fun_trm f ts => accum_HCs_trms ts
  | Con_trm c =>
    match c with
    | inl cc => []
    | inr hc => [hc]
    end
  end
with accum_HCs_trms {n : nat} (ts : trms L' n) : list Henkin_constants :=
  match ts with
  | O_trms => []
  | S_trms n t ts => accum_HCs_trm t ++ accum_HCs_trms (n := n) ts
  end.

#[local] Opaque accum_HCs_trm accum_HCs_trms.

Lemma accum_HCs_trm_Var_trm x
  : accum_HCs_trm (Var_trm x) = [].
Proof.
  reflexivity.
Defined.

Lemma accum_HCs_trm_Fun_trm f ts
  : accum_HCs_trm (Fun_trm f ts) = accum_HCs_trms ts.
Proof.
  reflexivity.
Defined.

Lemma accum_HCs_trm_Con_trm c
  : accum_HCs_trm (Con_trm c) = (match c with inl cc => [] | inr hc => [hc] end).
Proof.
  reflexivity.
Defined.

#[local] Hint Rewrite accum_HCs_trm_Var_trm accum_HCs_trm_Fun_trm accum_HCs_trm_Con_trm : simplication_hints.

Lemma accum_HCs_trms_O_trms
  : accum_HCs_trms O_trms = [].
Proof.
  reflexivity.
Defined.

Lemma accum_HCs_trms_S_trms n t ts
  : accum_HCs_trms (S_trms n t ts) = accum_HCs_trm t ++ accum_HCs_trms ts.
Proof.
  reflexivity.
Defined.

#[local] Hint Rewrite accum_HCs_trms_O_trms accum_HCs_trms_S_trms : simplication_hints.

Fixpoint accum_HCs_frm (p : frm L') : list Henkin_constants :=
  match p with
  | Rel_frm R ts => accum_HCs_trms ts
  | Eqn_frm t1 t2 => accum_HCs_trm t1 ++ accum_HCs_trm t2
  | Neg_frm p1 => accum_HCs_frm p1
  | Imp_frm p1 p2 => accum_HCs_frm p1 ++ accum_HCs_frm p2
  | All_frm y p1 => accum_HCs_frm p1
  end.

<<<<<<< HEAD
Lemma HC_occurs_in_trm_iff_in_accumHCs_trm (t : trm L')
  : forall hc, HC_occurs_in_trm hc t = true <-> In hc (accum_HCs_trm t)
with HC_occurs_in_trms_iff_in_accumHCs_trms n (ts : trms L' n)
  : forall hc, HC_occurs_in_trms hc ts = true <-> In hc (accum_HCs_trms ts).
Proof.
  - clear HC_occurs_in_trm_iff_in_accumHCs_trm. trm_ind t; ss!; destruct c as [hc' | cc]; ss!.
  - clear HC_occurs_in_trms_iff_in_accumHCs_trms. trms_ind ts; done!.
Qed.

#[local] Hint Rewrite <- HC_occurs_in_trm_iff_in_accumHCs_trm HC_occurs_in_trms_iff_in_accumHCs_trms : simplication_hints.

Lemma HC_occurs_in_frm_iff_in_accumHCs_frm (p : frm L')
  : forall hc, HC_occurs_in_frm hc p = true <-> In hc (accum_HCs_frm p).
Proof.
  frm_ind p; done!.
Qed.

#[local] Hint Rewrite <- HC_occurs_in_frm_iff_in_accumHCs_frm.

Lemma last_HC_gt_frm (hc : Henkin_constants)
  : forall p : frm L', hc > maxs (accum_HCs_frm p) -> HC_occurs_in_frm hc p = false.
Proof.
  intros p IN. destruct (HC_occurs_in_frm hc p) as [ | ] eqn: H_OBS; trivial.
  rewrite HC_occurs_in_frm_iff_in_accumHCs_frm in H_OBS. enough (WTS : hc <= maxs (accum_HCs_frm p)) by lia.
  eapply in_maxs_ge. exact H_OBS.
Qed.

Lemma last_HC_for_finite_formulae (ps : list (frm L')) (hc : Henkin_constants)
  : forall p : frm L', In p ps -> hc > maxs (map (maxs ∘ accum_HCs_frm)%prg ps) -> HC_occurs_in_frm hc p = false.
Proof.
  induction ps as [ | p ps IH]; simpl in *.
  - tauto.
  - intros p' [<- | IN] H.
    + eapply last_HC_gt_frm. unfold "∘"%prg in H. lia.
    + eapply IH; trivial. lia.
Qed.

Context {enum_function_symbols : isEnumerable L.(function_symbols)} {enum_constant_symbols : isEnumerable L.(constant_symbols)} {enum_relation_symbols : isEnumerable L.(relation_symbols)}.

Fixpoint Henkin (n : nat) {struct n} : Vector.t (frm L') n -> Vector.t Henkin_constants n -> Prop :=
  match n with
  | O => fun thetas => fun cs => thetas = VNil /\ cs = VNil
  | S n' => fun thetas => fun cs =>
    let x : ivar := fst (cp n') in
    let phi : frm L' := enum (isEnumerable := frm_isEnumerable (L := L') enum_function_symbols (@sum_isEnumerable L.(constant_symbols) Henkin_constants enum_constant_symbols nat_isEnumerable) enum_relation_symbols) (snd (cp n')) in
    let P (c : Henkin_constants) : Prop := HC_occurs_in_frm c phi = false /\ V.forallb (fun theta_k => negb (HC_occurs_in_frm c theta_k)) (V.tail thetas) = true in
    V.head thetas = Imp_frm (subst_frm (one_subst x (@Con_trm L' (inr (V.head cs)))) phi) (All_frm x phi) /\ Henkin n' (V.tail thetas) (V.tail cs) /\ P (V.head cs) /\ ⟪ MIN : forall c, P c -> c >= V.head cs ⟫
  end.

#[local] Opaque enum.

Lemma Henkin_unique n thetas thetas' cs cs'
  (HENKIN : Henkin n thetas cs)
  (HENKIN' : Henkin n thetas' cs')
  : thetas = thetas' /\ cs = cs'.
Proof.
  revert thetas thetas' cs cs' HENKIN HENKIN'. induction n as [ | n IH].
  - introVNil; introVNil; introVNil; introVNil; trivial.
  - introVCons theta thetas; introVCons theta' thetas'; introVCons c cs; introVCons c' cs'; intros HENKIN HENKIN'. exploit (IH thetas thetas' cs cs').
    + simpl Henkin in HENKIN. tauto.
    + simpl Henkin in HENKIN'. tauto.
    + intros [<- <-]. simpl Henkin in HENKIN, HENKIN'.
      assert (claim : c = c').
      { enough (WTS : c >= c' /\ c' >= c) by lia. split.
        - des. eapply MIN. split; trivial.
        - des. eapply MIN0. split; trivial.
      }
      split.
      * f_equal. destruct HENKIN as [-> ?], HENKIN' as [-> ?]. congruence.
      * congruence.
Qed.

Lemma Henkin_exists n
  : { RET : Vector.t (frm L') n * Vector.t Henkin_constants n | Henkin n (fst RET) (snd RET) }.
Proof.
  induction n as [ | n [[thetas cs] IH]].
  - exists (VNil, VNil). simpl; split; trivial.
  - simpl in *. set (x := fst (cp n)). set (phi := enum (isEnumerable := (frm_isEnumerable (L := L') enum_function_symbols (@sum_isEnumerable L.(constant_symbols) Henkin_constants enum_constant_symbols nat_isEnumerable) enum_relation_symbols)) (snd (cp n))).
    exploit (@dec_finds_minimum_if_exists (fun c : Henkin_constants => andb (negb (HC_occurs_in_frm c phi)) (V.forallb (fun theta_k => negb (HC_occurs_in_frm c theta_k)) thetas) = true)).
    { intros m. destruct (negb (HC_occurs_in_frm m phi) && V.forallb (fun theta_k : frm L' => negb (HC_occurs_in_frm m theta_k)) thetas) as [ | ]; [left | right]; done!. }
    { exists (1 + max (maxs (accum_HCs_frm phi)) (maxs (map (maxs ∘ accum_HCs_frm)%prg (V.to_list thetas)))). s!. split.
      - eapply last_HC_gt_frm. lia.
      - rewrite V.forallb_forall. intros i. s!. eapply last_HC_for_finite_formulae with (ps := V.to_list thetas).
        + clear cs IH x phi. revert i. induction thetas as [ | n theta thetas IH].
          * Fin.case0.
          * Fin.caseS i; simpl; [left | right]; trivial.
        + unfold "∘"%prg. lia.
    }
    intros [c c_spec]. exists (VCons n (Imp_frm (subst_frm (one_subst x (@Con_trm L' (inr c))) phi) (All_frm x phi)) thetas, VCons n c cs); simpl. split; trivial. split; trivial.
    s!. destruct c_spec as [[NOT_OCCUR NOT_OCCUR'] MIN]; unnw. split.
    + split; trivial.
    + intros c' [NOT_OCCUR1 NOT_OCCUR1']. eapply MIN; trivial. s!. split; trivial.
Qed.

=======
>>>>>>> update
End HENKIN.

#[global] Opaque HC_occurs_in_trm.

#[global] Hint Rewrite @HC_occurs_in_trm_Var_trm @HC_occurs_in_trm_Fun_trm @HC_occurs_in_trm_Con_trm : simplication_hints.

#[global] Opaque HC_occurs_in_trms.

#[global] Hint Rewrite @HC_occurs_in_trms_O_trms @HC_occurs_in_trms_S_trms : simplication_hints.

#[global] Opaque accum_HCs_trm.

#[global] Hint Rewrite @accum_HCs_trm_Var_trm @accum_HCs_trm_Fun_trm @accum_HCs_trm_Con_trm : simplication_hints.

#[global] Opaque accum_HCs_trms.

#[global] Hint Rewrite @accum_HCs_trms_O_trms @accum_HCs_trms_S_trms : simplication_hints.

<<<<<<< HEAD
#[global] Hint Rewrite <- @HC_occurs_in_trm_iff_in_accumHCs_trm @HC_occurs_in_trms_iff_in_accumHCs_trms @HC_occurs_in_frm_iff_in_accumHCs_frm : simplication_hints.
=======
>>>>>>> update
