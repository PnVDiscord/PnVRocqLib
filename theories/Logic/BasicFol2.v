Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.Data.Vector.
Require Import Coq.Arith.Wf_nat.
Require Import PnV.Logic.BasicFol.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.
#[local] Notation In := L.In.

#[local] Hint Rewrite @L.forallb_forall @Prelude.eqb_spec : simplication_hints.

Import FolNotations.

Section HENKIN.

Import ListNotations.

#[local] Infix "=~=" := is_similar_to : type_scope.

Definition augmented_language (L : language) (constant_symbols' : Set) : language :=
  {|
    function_symbols := L.(function_symbols);
    constant_symbols := L.(constant_symbols) + constant_symbols';
    relation_symbols := L.(relation_symbols);
    function_arity_table := L.(function_arity_table);
    relation_arity_table := L.(relation_arity_table);
  |}.

Definition Henkin_constants : Set := nat.

Context {L : language}.

Notation L' := (augmented_language L Henkin_constants).

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
  intros p IN. destruct (HC_occurs_in_frm hc p) as [ | ] eqn : H_OBS; trivial.
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

#[local] Notation hatom := (ivar + Henkin_constants)%type.

#[local] Notation hsubst := (hatom -> trm L').

Section HSUBST.

#[local] Open Scope list_scope.

Definition to_hsubst (s : subst L') : hsubst :=
  fun z : hatom =>
  match z with
  | inl x => s x
  | inr c => @Con_trm L' (inr c)
  end.

Definition from_hsubst (sigma : hsubst) : subst L' :=
  fun z : ivar => sigma (inl z).

Fixpoint accum_hatom_in_trm (t : trm L') : list hatom :=
  match t with
  | Var_trm x => [inl x]
  | Fun_trm f ts => accum_hatom_in_trms ts
  | Con_trm c =>
    match c with
    | inl cc => []
    | inr hc => [inr hc]
    end
  end
with accum_hatom_in_trms {n : nat} (ts : trms L' n) : list hatom :=
  match ts with
  | O_trms => []
  | S_trms n t ts => accum_hatom_in_trm t ++ accum_hatom_in_trms ts
  end.

Lemma in_accum_hatom_in_trm_iff_is_free_in_trm x (t : trm L')
  : L.In (inl x) (accum_hatom_in_trm t) <-> is_free_in_trm x t = true
with in_accum_hatom_in_trms_iff_is_free_in_trms n x (ts : trms L' n)
  : L.In (inl x) (accum_hatom_in_trms ts) <-> is_free_in_trms x ts = true.
Proof.
  - clear in_accum_hatom_in_trm_iff_is_free_in_trm; revert x. trm_ind t; intros z.
    + s!. firstorder congruence.
    + simpl. rewrite is_free_in_trm_unfold. eapply in_accum_hatom_in_trms_iff_is_free_in_trms.
    + destruct c as [cc | hc]; ss!.
  - clear in_accum_hatom_in_trms_iff_is_free_in_trms; revert x. trms_ind ts; intros z.
    + s!. firstorder congruence.
    + simpl. rewrite is_free_in_trms_unfold. rewrite orb_true_iff. rewrite <- IH with (x := z). rewrite L.in_app_iff. rewrite in_accum_hatom_in_trm_iff_is_free_in_trm. reflexivity.
Qed.

Lemma in_accum_hatom_in_trm_iff_HC_occurs_in_trm hc (t : trm L')
  : L.In (inr hc) (accum_hatom_in_trm t) <-> HC_occurs_in_trm hc t = true
with in_accum_hatom_in_trms_iff_HC_occurs_in_trms n hc (ts : trms L' n)
  : L.In (inr hc) (accum_hatom_in_trms ts) <-> HC_occurs_in_trms hc ts = true.
Proof.
  - clear in_accum_hatom_in_trm_iff_HC_occurs_in_trm; revert hc. trm_ind t; intros z.
    + s!. firstorder congruence.
    + s!. eapply in_accum_hatom_in_trms_iff_HC_occurs_in_trms.
    + destruct c as [hc | cc]; ss!.
  - clear in_accum_hatom_in_trms_iff_HC_occurs_in_trms; revert hc. trms_ind ts; intros z.
    + s!. firstorder congruence.
    + s!. rewrite IH. rewrite in_accum_hatom_in_trm_iff_HC_occurs_in_trm. reflexivity.
Qed.

Fixpoint accum_hatom_in_frm (p : frm L') : list hatom :=
  match p with
  | Rel_frm R ts => accum_hatom_in_trms ts
  | Eqn_frm t1 t2 => accum_hatom_in_trm t1 ++ accum_hatom_in_trm t2
  | Neg_frm p1 => accum_hatom_in_frm p1
  | Imp_frm p1 p2 => accum_hatom_in_frm p1 ++ accum_hatom_in_frm p2
  | All_frm y p1 => L.remove eq_dec (inl y) (accum_hatom_in_frm p1)
  end.

Lemma in_accum_hatom_in_frm_iff_is_free_in_frm x (p : frm L')
  : L.In (inl x) (accum_hatom_in_frm p) <-> is_free_in_frm x p = true.
Proof.
  revert x. frm_ind p; i.
  - simpl. eapply in_accum_hatom_in_trms_iff_is_free_in_trms.
  - simpl. rewrite orb_true_iff. do 2 rewrite <- in_accum_hatom_in_trm_iff_is_free_in_trm. rewrite L.in_app_iff. reflexivity.
  - ss!.
  - ss!.
  - ss!.
Qed.

#[local] Hint Rewrite in_accum_hatom_in_trm_iff_HC_occurs_in_trm in_accum_hatom_in_trms_iff_HC_occurs_in_trms : simplication_hints.

Lemma in_accum_hatom_in_frm_iff_HC_occurs_in_frm hc (p : frm L')
  : L.In (inr hc) (accum_hatom_in_frm p) <-> HC_occurs_in_frm hc p = true.
Proof.
  revert hc. frm_ind p; done!.
Qed.

#[local] Hint Rewrite in_accum_hatom_in_frm_iff_HC_occurs_in_frm : simplication_hints.

Definition hchi_frm (sigma : hsubst) (p : frm L') : ivar :=
  1 + maxs (L.map (last_ivar_trm ∘ sigma)%prg (accum_hatom_in_frm p)).

Definition nil_hsubst : hsubst :=
  fun z : hatom =>
  match z with
  | inl x => Var_trm x
  | inr c => @Con_trm L' (inr c)
  end.

Lemma to_hsubst_nil_subst
  : forall z, to_hsubst nil_subst z = nil_hsubst z.
Proof.
  intros [z | z]; reflexivity.
Qed.

Definition cons_hsubst (x : hatom) (t : trm L') (sigma : hsubst) : hsubst :=
  fun z : hatom => if Prelude.eqb z x then t else sigma z.

Lemma to_hsubst_cons_subst (x : ivar) (t : trm L') (s : subst L')
  : forall z, to_hsubst (cons_subst x t s) z = cons_hsubst (inl x) t (to_hsubst s) z.
Proof.
  intros [z | z]; unfold to_hsubst, cons_hsubst, nil_hsubst, cons_subst, nil_subst.
  - destruct (eq_dec z x) as [EQ | NE], (eqb (inl z) (inl x)) as [ | ] eqn: H_OBS; done!.
  - destruct (eqb (inr z) (inl x)) as [ | ] eqn: H_OBS; done!.
Qed.

Definition one_hsubst (x : hatom) (t : trm L') : hsubst :=
  cons_hsubst x t nil_hsubst.

Lemma to_hsubst_one_subst (x : ivar) (t : trm L')
  : forall z, to_hsubst (one_subst x t) z = one_hsubst (inl x) t z.
Proof.
  intros [z | z]; unfold to_hsubst, one_hsubst, cons_hsubst, nil_hsubst, one_subst, cons_subst, nil_subst.
  - destruct (eq_dec z x) as [EQ | NE], (eqb (inl z) (inl x)) as [ | ] eqn: H_OBS; done!.
  - destruct (eqb (inr z) (inl x)) as [ | ] eqn: H_OBS; done!.
Qed.

Fixpoint hsubst_trm (sigma : hsubst) (t : trm L') : trm L' :=
  match t with
  | Var_trm x => sigma (inl x)
  | Fun_trm f ts => Fun_trm f (hsubst_trms sigma ts)
  | Con_trm c =>
    match c with
    | inl cc => Con_trm c
    | inr hc => sigma (inr hc)
    end
  end
with hsubst_trms {n : nat} (sigma : hsubst) (ts : trms L' n) : trms L' n :=
  match ts with
  | O_trms => O_trms
  | S_trms n t ts => S_trms n (hsubst_trm sigma t) (hsubst_trms sigma ts)
  end.

Fixpoint hsubst_frm (sigma : hsubst) (p : frm L') : frm L' :=
  let chi : ivar := hchi_frm sigma p in
  match p with
  | Rel_frm R ts => Rel_frm R (hsubst_trms sigma ts)
  | Eqn_frm t1 t2 => Eqn_frm (hsubst_trm sigma t1) (hsubst_trm sigma t2)
  | Neg_frm p1 => Neg_frm (hsubst_frm sigma p1)
  | Imp_frm p1 p2 => Imp_frm (hsubst_frm sigma p1) (hsubst_frm sigma p2)
  | All_frm y p1 => All_frm chi (hsubst_frm (cons_hsubst (inl y) (Var_trm chi) sigma) p1)
  end.

Lemma hsubst_trm_unfold (sigma : hsubst) (t : trm L') :
  hsubst_trm sigma t =
  match t with
  | Var_trm x => sigma (inl x)
  | Fun_trm f ts => Fun_trm f (hsubst_trms sigma ts)
  | Con_trm c =>
    match c with
    | inl cc => Con_trm c
    | inr hc => sigma (inr hc)
    end
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma hsubst_trms_unfold n (sigma : hsubst) (ts : trms L' n) :
  hsubst_trms sigma ts =
  match ts with
  | O_trms => O_trms
  | S_trms n t ts => S_trms n (hsubst_trm sigma t) (hsubst_trms sigma ts)
  end.
Proof.
  destruct ts; reflexivity.
Defined.

Lemma hsubst_frm_unfold (sigma : hsubst) (p : frm L') :
  hsubst_frm sigma p =
  match p with
  | Rel_frm R ts => Rel_frm R (hsubst_trms sigma ts)
  | Eqn_frm t1 t2 => Eqn_frm (hsubst_trm sigma t1) (hsubst_trm sigma t2)
  | Neg_frm p1 => Neg_frm (hsubst_frm sigma p1)
  | Imp_frm p1 p2 => Imp_frm (hsubst_frm sigma p1) (hsubst_frm sigma p2)
  | All_frm y p1 =>
    let z : ivar := hchi_frm sigma p in
    All_frm z (hsubst_frm (cons_hsubst (inl y) (Var_trm z) sigma) p1)
  end.
Proof.
  destruct p; reflexivity.
Defined.

Definition hsubst_compose (sigma : hsubst) (sigma' : hsubst) : hsubst :=
  fun z : hatom => hsubst_trm sigma' (sigma z).

Fixpoint occurs_free_in_trm (z : hatom) (t : trm L') : bool :=
  match t with
  | Var_trm x => Prelude.eqb z (inl x)
  | Fun_trm f ts => occurs_free_in_trms z ts
  | Con_trm c =>
    match c with
    | inl cc => false
    | inr hc => Prelude.eqb z (inr hc)
    end
  end
with occurs_free_in_trms {n : nat} (z : hatom) (ts : trms L' n) : bool :=
  match ts with
  | O_trms => false
  | S_trms n t ts => occurs_free_in_trm z t || occurs_free_in_trms z ts
  end.

Fixpoint occurs_free_in_frm (z : hatom) (p : frm L') : bool :=
  match p with
  | Rel_frm R ts => occurs_free_in_trms z ts
  | Eqn_frm t1 t2 => occurs_free_in_trm z t1 || occurs_free_in_trm z t2
  | Neg_frm p1 => occurs_free_in_frm z p1
  | Imp_frm p1 p2 => occurs_free_in_frm z p1 || occurs_free_in_frm z p2
  | All_frm y p1 => occurs_free_in_frm z p1 && negb (Prelude.eqb z (inl y))
  end.

Lemma occurs_free_in_trm_unfold (z : hatom) (t : trm L') :
  occurs_free_in_trm z t =
  match t with
  | Var_trm x => Prelude.eqb z (inl x)
  | Fun_trm f ts => occurs_free_in_trms z ts
  | Con_trm c =>
    match c with
    | inl cc => false
    | inr hc => Prelude.eqb z (inr hc)
    end
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma occurs_free_in_trms_unfold n (z : hatom) (ts : trms L' n) :
  occurs_free_in_trms z ts =
  match ts with
  | O_trms => false
  | S_trms n t ts => occurs_free_in_trm z t || occurs_free_in_trms z ts
  end.
Proof.
  destruct ts; reflexivity.
Defined.

Lemma occurs_free_in_frm_unfold (z : hatom) (p : frm L') :
  occurs_free_in_frm z p =
  match p with
  | Rel_frm R ts => occurs_free_in_trms z ts
  | Eqn_frm t1 t2 => occurs_free_in_trm z t1 || occurs_free_in_trm z t2
  | Neg_frm p1 => occurs_free_in_frm z p1
  | Imp_frm p1 p2 => occurs_free_in_frm z p1 || occurs_free_in_frm z p2
  | All_frm y p1 => occurs_free_in_frm z p1 && negb (Prelude.eqb z (inl y))
  end.
Proof.
  destruct p; reflexivity.
Defined.

Lemma occurs_free_in_trm_iff (z : hatom) (t : trm L')
  : occurs_free_in_trm z t = true <-> In z (accum_hatom_in_trm t)
with occurs_free_in_trms_iff n (z : hatom) (ts : trms L' n)
  : occurs_free_in_trms z ts = true <-> In z (accum_hatom_in_trms ts).
Proof.
  - clear occurs_free_in_trm_iff. revert z; trm_ind t; simpl; i.
    + rewrite eqb_eq. done!.
    + eapply occurs_free_in_trms_iff.
    + destruct c as [cc | hc]; simpl.
      * firstorder congruence.
      * rewrite eqb_eq. firstorder.
  - clear occurs_free_in_trms_iff. revert z; trms_ind ts; simpl; i.
    + done!.
    + done!.
Qed.

#[local] Hint Rewrite occurs_free_in_trm_iff occurs_free_in_trms_iff : simplication_hints.

Lemma occurs_free_in_frm_iff (z : hatom) (p : frm L')
  : occurs_free_in_frm z p = true <-> In z (accum_hatom_in_frm p).
Proof.
  revert z. frm_ind p; done!.
Qed.

Lemma hchi_frm_not_free (sigma : hsubst) (p : frm L') (z : hatom)
  (OCCURS : occurs_free_in_frm z p = true)
  : is_free_in_trm (hchi_frm sigma p) (sigma z) = false.
Proof.
  eapply last_ivar_trm_gt. unfold hchi_frm.
  enough (WTS : last_ivar_trm (sigma z) <= maxs (L.map (last_ivar_trm ∘ sigma)%prg (accum_hatom_in_frm p))) by lia.
  eapply in_maxs_ge. unfold "∘"%prg. eapply in_map_iff.
  rewrite occurs_free_in_frm_iff in OCCURS. done!.
Qed.

Definition trm_is_fresh_in_hsubst (x : ivar) (sigma : hsubst) (t : trm L') : bool :=
  L.forallb (negb ∘ is_free_in_trm x ∘ sigma)%prg (accum_hatom_in_trm t).

Definition trms_is_fresh_in_hsubst {n : nat} (x : ivar) (sigma : hsubst) (ts : trms L' n) : bool :=
  L.forallb (negb ∘ is_free_in_trm x ∘ sigma)%prg (accum_hatom_in_trms ts).

Definition frm_is_fresh_in_hsubst (x : ivar) (sigma : hsubst) (p : frm L') : bool :=
  L.forallb (negb ∘ is_free_in_trm x ∘ sigma)%prg (accum_hatom_in_frm p).

Lemma trm_is_fresh_in_hsubst_iff (t : trm L') (z : ivar) (sigma : hsubst)
  : trm_is_fresh_in_hsubst z sigma t = true <-> is_free_in_trm z (hsubst_trm sigma t) = false
with trms_is_fresh_in_hsubst_iff n (ts : trms L' n) (z : ivar) (sigma : hsubst)
  : trms_is_fresh_in_hsubst z sigma ts = true <-> is_free_in_trms z (hsubst_trms sigma ts) = false.
Proof.
  - unfold trm_is_fresh_in_hsubst. unfold "∘"%prg. clear trm_is_fresh_in_hsubst_iff. revert z sigma. trm_ind t; simpl; i.
    + split; intros H; [rewrite andb_true_iff in H; destruct H as [H _]; rewrite negb_true_iff in H; done| rewrite andb_true_iff; split; [rewrite negb_true_iff; done | done]].
    + eapply trms_is_fresh_in_hsubst_iff.
    + destruct c as [cc | hc].
      * ss!. 
      * simpl. split.
        { rewrite andb_true_iff. intros [H _]. rewrite negb_true_iff in H. done!. }
        { rewrite andb_true_iff. rewrite negb_true_iff. done!. }
  - unfold trms_is_fresh_in_hsubst. clear trms_is_fresh_in_hsubst_iff. revert z sigma. trms_ind ts; simpl; i.
    + done.
    + rewrite forallb_app. rewrite is_free_in_trms_unfold. rewrite orb_false_iff. rewrite andb_true_iff. rewrite IH. rewrite <- trm_is_fresh_in_hsubst_iff. reflexivity.
Qed.

Lemma frm_is_fresh_in_hsubst_iff (p : frm L') (z : ivar) (sigma : hsubst)
  : frm_is_fresh_in_hsubst z sigma p = true <-> is_free_in_frm z (hsubst_frm sigma p) = false.
Proof.
  revert z sigma. unfold frm_is_fresh_in_hsubst. frm_ind p; simpl; ii.
  - eapply trms_is_fresh_in_hsubst_iff.
  - rewrite orb_false_iff. do 2 rewrite <- trm_is_fresh_in_hsubst_iff.
    unfold "∘"%prg. rewrite forallb_app. rewrite andb_true_iff. done.
  - done.
  - rewrite forallb_app. rewrite orb_false_iff. rewrite andb_true_iff. rewrite IH1, IH2. done.
  - split.
    + intros H_forallb. rewrite andb_false_iff.
      destruct (z =? hchi_frm sigma (All_frm y p1))%nat as [ | ] eqn : OBS.
      { simpl. right. done. }
      { left. rewrite Nat.eqb_neq in OBS. eapply IH1. rewrite forallb_forall.
        intros x x_in. unfold "∘"%prg. rewrite negb_true_iff. unfold cons_hsubst.
        unfold Prelude.eqb. destruct (Prelude.eq_dec x (inl y)) as [H_eq | H_ne].
        - destruct (is_free_in_trm z (Var_trm (hchi_frm sigma (All_frm y p1)))) as [ | ] eqn : EQ.
          + contradiction OBS. symmetry. subst x. rewrite <- fv_is_free_in_trm in EQ.
            simpl in EQ. done!.
          + done!.
        - rewrite forallb_forall in H_forallb. unfold "∘"%prg in H_forallb.
          rewrite <- negb_true_iff. eapply H_forallb. eapply L.in_remove_iff. done.
      }
    + rewrite andb_false_iff. rewrite negb_false_iff. rewrite Nat.eqb_eq. unfold "∘"%prg in *. intros [NOT_FREE | ->].
      { eapply IH1 in NOT_FREE. rewrite forallb_forall in NOT_FREE. rewrite forallb_forall.
        intros x x_in. rewrite negb_true_iff. rewrite L.in_remove_iff in x_in. destruct x_in as [x_in x_ne_y].
        apply NOT_FREE in x_in. rewrite negb_true_iff in x_in. unfold cons_hsubst in x_in.
        unfold Prelude.eqb in *. destruct (Prelude.eq_dec x (inl y)) as [H_eq | H_ne]; try done.
      }
      { rewrite forallb_forall. intros x x_in. apply L.in_remove_iff in x_in. destruct x_in as [x_in x_ne_y].
        rewrite negb_true_iff. eapply hchi_frm_not_free. simpl. rewrite andb_true_iff.
        split; [rewrite <- occurs_free_in_frm_iff in x_in | rewrite negb_true_iff; unfold Prelude.eqb; destruct (eq_dec x (inl y))]; try done.
      }
Qed.

Theorem hchi_frm_is_fresh_in_hsubst (p : frm L') (sigma : hsubst)
  : frm_is_fresh_in_hsubst (hchi_frm sigma p) sigma p = true.
Proof.
  unfold frm_is_fresh_in_hsubst. rewrite forallb_forall. ii.
  unfold "∘"%prg. rewrite negb_true_iff. eapply hchi_frm_not_free.
  rewrite occurs_free_in_frm_iff. done.
Qed.

Lemma hchi_frm_nil (p : frm L')
  : is_free_in_frm (hchi_frm nil_hsubst p) p = false.
Proof.
  pose proof (hchi_frm_is_fresh_in_hsubst p nil_hsubst) as claim1.
  unfold frm_is_fresh_in_hsubst in claim1.
  rewrite <- not_true_iff_false. intros CONTRA. 
  rewrite forallb_forall in claim1. unfold "∘"%prg in claim1.
  rewrite <- in_accum_hatom_in_frm_iff_is_free_in_frm in CONTRA.
  apply claim1 in CONTRA. rewrite negb_true_iff in CONTRA.
  unfold nil_hsubst in CONTRA at 2. rewrite is_free_in_trm_unfold in CONTRA.
  rewrite Nat.eqb_neq in CONTRA. contradiction.
Qed.

Definition equiv_hsubst_in_frm (sigma1 : hsubst) (sigma2 : hsubst) (p : frm L') : Prop :=
  forall z : hatom, forall FREE : occurs_free_in_frm z p = true, sigma1 z = sigma2 z.

Theorem hchi_frm_compat_equiv_hsubst (sigma1 : hsubst) (sigma2 : hsubst) (p : frm L')
  (EQUIV : equiv_hsubst_in_frm sigma1 sigma2 p)
  : hchi_frm sigma1 p = hchi_frm sigma2 p.
Proof.
  unfold hchi_frm. f_equal. eapply maxs_ext. intros n. unfold "∘"%prg.
  split; intros H_in; eapply in_map_iff; apply in_map_iff in H_in; destruct H_in as [x [<- H_in]].
  - exists x. rewrite -> EQUIV. try done!.
    rewrite occurs_free_in_frm_iff. done!.
  - exists x. rewrite -> EQUIV. try done!.
    rewrite occurs_free_in_frm_iff. done!.
Qed.

Lemma equiv_hsubst_in_trm_implies_hsubst_trm_same (sigma1 : hsubst) (sigma2 : hsubst) (t : trm L')
  (EQUIV : forall z : hatom, forall FREE : occurs_free_in_trm z t = true, sigma1 z = sigma2 z)
  : hsubst_trm sigma1 t = hsubst_trm sigma2 t
with equiv_hsubst_in_trms_implies_hsubst_trms_same n (sigma1 : hsubst) (sigma2 : hsubst) (ts : trms L' n)
  (EQUIV : forall z : hatom, forall FREE : occurs_free_in_trms z ts = true, sigma1 z = sigma2 z)
  : hsubst_trms sigma1 ts = hsubst_trms sigma2 ts.
Proof.
  - clear equiv_hsubst_in_trm_implies_hsubst_trm_same. revert sigma1 sigma2 EQUIV. trm_ind t; simpl; ii.
    + eapply EQUIV. rewrite eqb_eq. done.
    + f_equal. eapply equiv_hsubst_in_trms_implies_hsubst_trms_same. exact EQUIV.
    + destruct c as [cc | hc].
      * reflexivity.
      * eapply EQUIV. rewrite eqb_eq. done!.
  - clear equiv_hsubst_in_trms_implies_hsubst_trms_same. revert sigma1 sigma2 EQUIV. trms_ind ts; simpl; ii.
    + reflexivity.
    + f_equal.
      * eapply equiv_hsubst_in_trm_implies_hsubst_trm_same. ii. eapply EQUIV. rewrite orb_true_iff. left. exact FREE.
      * eapply IH. ii. eapply EQUIV. rewrite orb_true_iff. right. exact FREE.
Qed.

Lemma equiv_hsubst_in_frm_implies_hsubst_frm_same (sigma1 : hsubst) (sigma2 : hsubst) (p : frm L')
  (EQUIV : equiv_hsubst_in_frm sigma1 sigma2 p)
  : hsubst_frm sigma1 p = hsubst_frm sigma2 p.
Proof.
  revert sigma1 sigma2 EQUIV. unfold equiv_hsubst_in_frm. frm_ind p; simpl; ii.
  - simpl in EQUIV. f_equal.
    eapply equiv_hsubst_in_trms_implies_hsubst_trms_same. done.
  - simpl in EQUIV. f_equal.
    + eapply equiv_hsubst_in_trm_implies_hsubst_trm_same. ii.
      eapply EQUIV. rewrite orb_true_iff. done!.
    + eapply equiv_hsubst_in_trm_implies_hsubst_trm_same. ii.
      eapply EQUIV. rewrite orb_true_iff. done!.
  - f_equal. eapply IH1. done.
  - f_equal.
    + eapply IH1. ii. eapply EQUIV. rewrite orb_true_iff. done!.
    + eapply IH2. ii. eapply EQUIV. rewrite orb_true_iff. done!.
  - f_equal.
    + eapply hchi_frm_compat_equiv_hsubst. unfold equiv_hsubst_in_frm. simpl. done.
    + eapply IH1. ii. unfold cons_hsubst. unfold eqb in *. destruct (eq_dec z (inl y)) as [H_yes | H_no].
      { f_equal. subst z. eapply hchi_frm_compat_equiv_hsubst. unfold equiv_hsubst_in_frm. simpl. done. }
      { eapply EQUIV. rewrite andb_true_iff. split. done. eapply negb_true_iff. unfold Prelude.eqb. destruct (eq_dec z (inl y)); done. }
Qed.

Lemma distr_hcompose_one (sigma1 : hsubst) (sigma2 : hsubst) (x : hatom) (y : ivar) (z : hatom) (t : trm L') (p : frm L')
  (FRESH : forallb (negb ∘ occurs_free_in_trm (inl y) ∘ sigma1)%prg (remove eq_dec x (accum_hatom_in_frm p)) = true)
  (FREE : occurs_free_in_frm z p = true)
  : cons_hsubst x t (hsubst_compose sigma1 sigma2) z = hsubst_compose (cons_hsubst x (Var_trm y) sigma1) (cons_hsubst (inl y) t sigma2) z.
Proof.
  unfold hsubst_compose, cons_hsubst. unfold Prelude.eqb. destruct (eq_dec z x) as [H_eq | H_ne].
  - subst z. simpl. destruct (eq_dec (inl y) (inl y)); done.
  - rewrite forallb_forall in FRESH. unfold "∘"%prg in FRESH.
    assert (NOT_FREE : occurs_free_in_trm (inl y) (sigma1 z) = false).
    { rewrite <- negb_true_iff. eapply FRESH. rewrite L.in_remove_iff. rewrite <- occurs_free_in_frm_iff. done!. }
    eapply equiv_hsubst_in_trm_implies_hsubst_trm_same. intros z' FREE'. destruct (eq_dec z' (inl y)) as [EQ | NE]; try done!.
Qed.

#[local] Tactic Notation "done" :=
  first [now firstorder | done!].

Definition occurs_free_in_trm_wrt (z : hatom) (sigma : hsubst) (t : trm L') : Prop :=
  exists x : hatom, occurs_free_in_trm x t = true /\ occurs_free_in_trm z (sigma x) = true.

Definition occurs_free_in_trms_wrt {n : nat} (z : hatom) (sigma : hsubst) (ts : trms L' n) : Prop :=
  exists x : hatom, occurs_free_in_trms x ts = true /\ occurs_free_in_trm z (sigma x) = true.

Definition occurs_free_in_frm_wrt (z : hatom) (sigma : hsubst) (p : frm L') : Prop :=
  exists x : hatom, occurs_free_in_frm x p = true /\ occurs_free_in_trm z (sigma x) = true.

Fixpoint occurs_free_in_trm_wrt_iff (t : trm L') (z : hatom) (sigma : hsubst) {struct t}
  : occurs_free_in_trm_wrt z sigma t <-> occurs_free_in_trm z (hsubst_trm sigma t) = true
with occurs_free_in_trms_wrt_iff n (ts : trms L' n) (z : hatom) (sigma : hsubst) {struct ts}
  : occurs_free_in_trms_wrt z sigma ts <-> occurs_free_in_trms z (hsubst_trms sigma ts) = true.
Proof.
  - clear occurs_free_in_trm_wrt_iff. destruct t as [x | f ts | [cc | hc]]; simpl; i.
    + clear occurs_free_in_trms_wrt_iff. split.
      * intros [y [FREE FREE']]. unfold Prelude.eqb in FREE. destruct (eq_dec y (inl x)); done.
      * unfold occurs_free_in_trm_wrt. intros FREE. exists (inl x). simpl. rewrite eqb_eq. done.
    + pose proof (occurs_free_in_trms_wrt_iff (L.(function_arity_table) f) ts z sigma) as H. clear occurs_free_in_trms_wrt_iff. split.
      * intros [y [FREE FREE']]. done.
      * intros FREE. done.
    + clear occurs_free_in_trms_wrt_iff. done.
    + clear occurs_free_in_trms_wrt_iff. split.
      * intros [y [FREE FREE']]. unfold Prelude.eqb in FREE. destruct (eq_dec y (inr hc)); done.
      * unfold occurs_free_in_trm_wrt. intros FREE. exists (inr hc). simpl. rewrite eqb_eq. split; trivial.
  - destruct ts as [ | n t ts]; simpl; i.
    + clear occurs_free_in_trm_wrt_iff occurs_free_in_trms_wrt_iff. done.
    + pose proof (occurs_free_in_trm_wrt_iff t z sigma) as H. clear occurs_free_in_trm_wrt_iff. pose proof (occurs_free_in_trms_wrt_iff n ts z sigma) as H'. clear occurs_free_in_trms_wrt_iff. split.
      * intros [x [FREE FREE']]. rewrite orb_true_iff. simpl in FREE. rewrite orb_true_iff in FREE. destruct FREE as [FREE | FREE].
        { left. rewrite <- H. exists x. split; trivial. }
        { right. rewrite <- H'. exists x. split; trivial. }
      * rewrite orb_true_iff. intros [FREE | FREE].
        { rewrite <- H in FREE. destruct FREE as [x [FREE FREE']]. exists x. simpl. rewrite orb_true_iff. split; [left; exact FREE | exact FREE']. }
        { rewrite <- H' in FREE. destruct FREE as [x [FREE FREE']]. exists x. simpl. rewrite orb_true_iff. split; [right; exact FREE | exact FREE']. }
Qed.

Lemma occurs_free_in_frm_wrt_iff (p : frm L') (z : hatom) (sigma : hsubst)
  : occurs_free_in_frm_wrt z sigma p <-> occurs_free_in_frm z (hsubst_frm sigma p) = true.
Proof.
  revert z sigma. unfold occurs_free_in_frm_wrt. frm_ind p; simpl; i.
  - split.
    + intros [y [FREE FREE']]. eapply occurs_free_in_trms_wrt_iff. done.
    + intros FREE. apply occurs_free_in_trms_wrt_iff in FREE. done.
  - split.
    + intros [y [FREE FREE']]. rewrite orb_true_iff in FREE. rewrite orb_true_iff. destruct FREE as [FREE | FREE].
      * left. eapply occurs_free_in_trm_wrt_iff. done.
      * right. eapply occurs_free_in_trm_wrt_iff. done.
    + intros FREE. rewrite orb_true_iff in FREE. destruct FREE as [FREE | FREE].
      * apply occurs_free_in_trm_wrt_iff in FREE. destruct FREE as [y [FREE FREE']].
        exists y. rewrite orb_true_iff. done.
      * apply occurs_free_in_trm_wrt_iff in FREE. destruct FREE as [y [FREE FREE']].
        exists y. rewrite orb_true_iff. done.
  - done.
  - split.
    + intros [y [FREE FREE']]. rewrite orb_true_iff in FREE. rewrite orb_true_iff. destruct FREE as [FREE | FREE].
      * left. eapply IH1. done.
      * right. eapply IH2. done.
    + intros FREE. rewrite orb_true_iff in FREE. destruct FREE as [FREE | FREE].
      * apply IH1 in FREE. destruct FREE as [y [FREE FREE']].
        exists y. rewrite orb_true_iff. done.
      * apply IH2 in FREE. destruct FREE as [y [FREE FREE']].
        exists y. rewrite orb_true_iff. done.
  - split.
    + intros [w [FREE FREE']]. rewrite andb_true_iff in FREE. rewrite negb_true_iff in FREE. rewrite eqb_neq in FREE.
      destruct FREE as [FREE w_ne_y]. rewrite andb_true_iff. rewrite negb_true_iff. split.
      * eapply IH1. exists w. split; trivial. unfold cons_hsubst.
        unfold Prelude.eqb. destruct (eq_dec w (inl y)) as [EQ | NE]; done.
      * rewrite eqb_neq. intros CONTRA.
        assert (claim1 : frm_is_fresh_in_hsubst (hchi_frm sigma (All_frm y p1)) sigma (All_frm y p1) = true).
        { exact (hchi_frm_is_fresh_in_hsubst (All_frm y p1) sigma). }
        unfold frm_is_fresh_in_hsubst in claim1. rewrite forallb_forall in claim1.
        assert (claim2 : In w (accum_hatom_in_frm (All_frm y p1))).
        { rewrite <- occurs_free_in_frm_iff. simpl. rewrite andb_true_iff. rewrite negb_true_iff. rewrite eqb_neq. done. }
        apply claim1 in claim2. unfold "∘"%prg in claim2. rewrite negb_true_iff in claim2.
        subst z. rewrite occurs_free_in_trm_iff in FREE'. rewrite in_accum_hatom_in_trm_iff_is_free_in_trm in FREE'. done.
    + rewrite andb_true_iff. rewrite negb_true_iff. rewrite eqb_neq.
      set (w := hchi_frm sigma (All_frm y p1)). intros [FREE NE].
      apply IH1 in FREE. destruct FREE as [x [FREE FREE']].
      unfold cons_hsubst in FREE'. unfold eqb in FREE'. destruct (eq_dec x (inl y)) as [x_eq_y | x_ne_y].
      * subst x. contradiction NE. apply occurs_free_in_trm_iff in FREE'. simpl in FREE'. done.
      * exists x. rewrite andb_true_iff. rewrite negb_true_iff. rewrite eqb_neq. done.
Qed.

Lemma hchi_frm_ext (sigma1 : hsubst) (sigma2 : hsubst) (p1 : frm L') (p2 : frm L')
  (EQUIV : forall z : hatom, occurs_free_in_frm_wrt z sigma1 p1 <-> occurs_free_in_frm_wrt z sigma2 p2)
  : hchi_frm sigma1 p1 = hchi_frm sigma2 p2.
Proof.
  assert (ENOUGH : forall xs : list hatom, forall f : hatom -> list ivar, maxs (L.map (maxs ∘ f)%prg xs) = maxs (L.flat_map f xs)).
  { induction xs; simpl; i; eauto. unfold "∘"%prg. rewrite maxs_app. f_equal. eauto. }
  unfold hchi_frm. f_equal. unfold last_ivar_trm.
  change (maxs (L.map (maxs ∘ (fvs_trm ∘ sigma1))%prg (accum_hatom_in_frm p1)) = maxs (L.map (maxs ∘ (fvs_trm ∘ sigma2))%prg (accum_hatom_in_frm p2))).
  do 2 rewrite ENOUGH. eapply maxs_ext. intros z. do 2 rewrite in_flat_map.
  unfold "∘"%prg. split; intros (y&IN&IN').
  - assert (claim : occurs_free_in_frm_wrt (inl z) sigma1 p1).
    { exists y. split.
      - rewrite occurs_free_in_frm_iff; trivial.
      - rewrite occurs_free_in_trm_iff, in_accum_hatom_in_trm_iff_is_free_in_trm; done.
    }
    rewrite -> EQUIV in claim. destruct claim as (x&OCCURS&OCCURS'). exists x. split.
    + rewrite occurs_free_in_frm_iff in OCCURS. done.
    + rewrite fv_is_free_in_trm, <- in_accum_hatom_in_trm_iff_is_free_in_trm, <- occurs_free_in_trm_iff. done.
  - assert (claim : occurs_free_in_frm_wrt (inl z) sigma2 p2).
    { exists y. split.
      - rewrite occurs_free_in_frm_iff; trivial.
      - rewrite occurs_free_in_trm_iff, in_accum_hatom_in_trm_iff_is_free_in_trm; done.
    }
    rewrite <- EQUIV in claim. destruct claim as (x&OCCURS&OCCURS'). exists x. split.
    + rewrite occurs_free_in_frm_iff in OCCURS. done.
    + rewrite fv_is_free_in_trm, <- in_accum_hatom_in_trm_iff_is_free_in_trm, <- occurs_free_in_trm_iff. done.
Qed.

Theorem hsubst_compose_trm_spec (t : trm L') (sigma : hsubst) (sigma': hsubst)
  : hsubst_trm (hsubst_compose sigma sigma') t = hsubst_trm sigma' (hsubst_trm sigma t)
with hsubst_compose_trms_spec n (ts : trms L' n) (sigma : hsubst) (sigma': hsubst)
  : hsubst_trms (hsubst_compose sigma sigma') ts = hsubst_trms sigma' (hsubst_trms sigma ts).
Proof.
  - revert sigma sigma'. trm_ind t; simpl; i.
    + done.
    + f_equal. eapply hsubst_compose_trms_spec.
    + destruct c as [cc | hc]; done.
  - revert sigma sigma'. trms_ind ts; simpl; i.
    + done.
    + f_equal.
      * eapply hsubst_compose_trm_spec.
      * eapply IH.
Qed.

Theorem hsubst_compose_frm_spec (p : frm L') (sigma : hsubst) (sigma': hsubst)
  : hsubst_frm (hsubst_compose sigma sigma') p = hsubst_frm sigma' (hsubst_frm sigma p).
Proof.
  revert sigma sigma'. frm_ind p; simpl; i.
  - f_equal; eapply hsubst_compose_trms_spec.
  - f_equal; eapply hsubst_compose_trm_spec.
  - done.
  - done.
  - enough (ENOUGH : hchi_frm sigma' (hsubst_frm sigma (All_frm y p1)) = hchi_frm (hsubst_compose sigma sigma') (All_frm y p1)).
    { revert ENOUGH.
      set (x := hchi_frm sigma (All_frm y p1)).
      set (z := hchi_frm (hsubst_compose sigma sigma') (All_frm y p1)).
      set (w := hchi_frm sigma' (All_frm x (hsubst_frm (cons_hsubst (inl y) (Var_trm x) sigma) p1))).
      i. rewrite <- IH1. assert (EQ: z = w) by done. subst z. f_equal; trivial.
      eapply equiv_hsubst_in_frm_implies_hsubst_frm_same.
      unfold equiv_hsubst_in_frm. ii.
      rewrite <- distr_hcompose_one with (p := p1).
      - done.
      - pose proof (claim1 := hchi_frm_is_fresh_in_hsubst). unfold frm_is_fresh_in_hsubst in claim1.
        eapply forallb_forall. intros u u_in. rewrite L.in_remove_iff in u_in. destruct u_in as [u_in NE].
        unfold "∘"%prg. rewrite negb_true_iff.
        enough (WTS : occurs_free_in_trm (inl x) (sigma u) <> true) by now destruct (occurs_free_in_trm (inl x) (sigma u)).
        intros CONTRA. rewrite occurs_free_in_trm_iff in CONTRA. rewrite in_accum_hatom_in_trm_iff_is_free_in_trm in CONTRA.
        specialize claim1 with (p := All_frm y p1) (sigma := sigma). unfold "∘"%prg in claim1. rewrite forallb_forall in claim1.
        assert (claim2: In u (accum_hatom_in_frm (All_frm y p1))).
        { simpl. rewrite L.in_remove_iff. done. }
        apply claim1 in claim2. rewrite negb_true_iff in claim2. done.
      - done.
    }
    eapply hchi_frm_ext. intros z. split.
    + simpl. unfold occurs_free_in_frm_wrt. intros [x [FREE FREE']]. simpl in FREE.
      rewrite andb_true_iff in FREE. rewrite negb_true_iff in FREE. rewrite eqb_neq in FREE.
      destruct FREE as [FREE NE]. apply occurs_free_in_frm_wrt_iff in FREE. unfold free_in_frm_wrt in FREE.
      destruct FREE as [w [FREE1 FREE2]]. unfold cons_hsubst in FREE2. unfold eqb in FREE2. destruct (eq_dec w (inl y)) as [w_eq_y | w_ne_y].
      * unfold occurs_free_in_trm in FREE2. rewrite eqb_eq in FREE2. subst. done.
      * exists w. simpl. rewrite andb_true_iff. rewrite negb_true_iff. rewrite eqb_neq. split; try tauto.
        eapply occurs_free_in_trm_wrt_iff. done.
    + intros [x [FREE FREE']]. simpl in FREE. rewrite andb_true_iff in FREE. rewrite negb_true_iff in FREE. rewrite eqb_neq in FREE. destruct FREE as [FREE NE].
      apply occurs_free_in_trm_wrt_iff in FREE'. destruct FREE' as [u [FREE' FREE'']]. exists u. split.
      * eapply occurs_free_in_frm_wrt_iff. exists x. simpl. rewrite andb_true_iff. rewrite negb_true_iff. rewrite eqb_neq. done.
      * done.
Qed.

Lemma hcompose_one_hsubst_frm (x1 : hatom) (t1 : trm L') (sigma : hsubst) (p : frm L')
  : hsubst_frm sigma (hsubst_frm (one_hsubst x1 t1) p) = hsubst_frm (cons_hsubst x1 (hsubst_trm sigma t1) sigma) p.
Proof.
  unfold one_hsubst. rewrite <- hsubst_compose_frm_spec. eapply equiv_hsubst_in_frm_implies_hsubst_frm_same. ii.
  unfold cons_hsubst, hsubst_compose, eqb. destruct (eq_dec z x1) as [z_eq_x1 | z_ne_x1]; try done.
  unfold nil_hsubst. destruct z; try done.
Qed.

Lemma cons_hsubst_hsubst_frm (x1 : hatom) (t1 : trm L') (y : hatom) (p : frm L') (sigma : hsubst)
  (NOT_FREE : occurs_free_in_frm y p = false \/ y = x1)
  : hsubst_frm (cons_hsubst x1 t1 sigma) p = hsubst_frm (cons_hsubst y t1 sigma) (hsubst_frm (one_hsubst x1 (nil_hsubst y)) p).
Proof.
  unfold one_hsubst. rewrite <- hsubst_compose_frm_spec. eapply equiv_hsubst_in_frm_implies_hsubst_frm_same.
  ii. unfold cons_hsubst, hsubst_compose, eqb. destruct (eq_dec z x1) as [z_eq_x1 | z_ne_x1].
  - subst z. unfold nil_hsubst. destruct y as [x | c]; simpl.
    + destruct (eq_dec (inl x) (inl x)); try done.
    + destruct (eq_dec (inr c) (inr c)); try done.
  - destruct z as [x | c]; simpl.
    + destruct (eq_dec (inl x) y) as [z_eq_y | z_ne_y]; try done.
    + destruct (eq_dec (inr c) y) as [z_eq_y | z_ne_y]; try done.
Qed.

Lemma nil_hsubst_trm (t : trm L')
  : hsubst_trm nil_hsubst t = t
with nil_hsubst_trms n (ts : trms L' n)
  : hsubst_trms nil_hsubst ts = ts.
Proof.
  - clear nil_hsubst_trm. trm_ind t; simpl.
    + reflexivity.
    + f_equal. eapply nil_hsubst_trms.
    + destruct c as [cc | hc]; reflexivity.
  - clear nil_hsubst_trms. trms_ind ts; simpl.
    + reflexivity.
    + f_equal.
      * eapply nil_hsubst_trm.
      * eapply IH.
Qed.

Lemma trivial_hsubst (x : hatom) (p : frm L')
  : hsubst_frm (one_hsubst x (nil_hsubst x)) p = hsubst_frm nil_hsubst p.
Proof.
  eapply equiv_hsubst_in_frm_implies_hsubst_frm_same. ii. unfold one_hsubst, cons_hsubst.
  unfold eqb. destruct (eq_dec z x); try done.
Qed.

Theorem subst_hsubst_compat_in_trm (s : subst L') (sigma : hsubst) (t : trm L')
  (SIM : forall z : hatom, to_hsubst s z = sigma z)
  : subst_trm s t = hsubst_trm sigma t
with subst_hsubst_compat_in_trms n (s : subst L') (sigma : hsubst) (ts : trms L' n)
  (SIM : forall z : hatom, to_hsubst s z = sigma z)
  : subst_trms s ts = hsubst_trms sigma ts.
Proof.
  - clear subst_hsubst_compat_in_trm. revert s sigma SIM. trm_ind t; simpl; i.
    + rewrite subst_trm_unfold. exact (SIM (inl x)).
    + rewrite <- subst_hsubst_compat_in_trms with (s := s); trivial.
    + destruct c as [cc | hc]; [reflexivity | exact (SIM (inr hc))].
  - clear subst_hsubst_compat_in_trms. revert s sigma SIM. trms_ind ts; simpl; i.
    + reflexivity.
    + rewrite <- subst_hsubst_compat_in_trm with (s := s); trivial. rewrite <- IH with (s := s); trivial.
Qed.

Theorem subst_hsubst_compat_in_frm (s : subst L') (sigma : hsubst) (p : frm L')
  (SIM : forall z : hatom, to_hsubst s z = sigma z)
  : subst_frm s p = hsubst_frm sigma p.
Proof.
  revert s sigma SIM. revert p.
  assert (LEMMA : forall A : Set, forall xs : list A, forall f: A -> list ivar, maxs (L.map (maxs ∘ f)%prg xs) = maxs (L.flat_map f xs)).
  { intros A. induction xs; simpl; i; eauto. unfold "∘"%prg. rewrite maxs_app. f_equal. eauto. }
  frm_ind p; simpl; i.
  - f_equal. eapply subst_hsubst_compat_in_trms. done.
  - f_equal; eapply subst_hsubst_compat_in_trm; done.
  - f_equal. done.
  - f_equal; done.
  - assert (claim : chi_frm s (All_frm y p1) = hchi_frm sigma (All_frm y p1)).
    { unfold hchi_frm, chi_frm. f_equal.
      change (maxs (L.map (maxs ∘ (fvs_trm ∘ s))%prg (fvs_frm (All_frm y p1))) = maxs (L.map (maxs ∘ (fvs_trm ∘ sigma))%prg (accum_hatom_in_frm (All_frm y p1)))).
      do 2 rewrite LEMMA. eapply maxs_ext. intros z. do 2 rewrite in_flat_map. unfold "∘"%prg.
      split; intros (x&IN&IN').
      - rewrite fv_is_free_in_frm in IN. simpl in IN. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq in IN. destruct IN as [IN NE].
        specialize SIM with (z := inl x). simpl in SIM.
        exists (inl x). rewrite <- SIM. split; trivial.
        rewrite in_accum_hatom_in_frm_iff_is_free_in_frm. done.
      - destruct x as [x | c].
        + rewrite in_accum_hatom_in_frm_iff_is_free_in_frm in IN. specialize SIM with (z := inl x). simpl in SIM.
          exists x. rewrite SIM. split; done.
        + specialize SIM with (z := inr c). simpl in SIM.
          rewrite <- SIM in IN'. simpl in IN'. done. 
    }
    f_equal; trivial. rewrite claim. eapply IH1. intros [x | c]; simpl.
    + unfold cons_hsubst, cons_subst. destruct (eqb (inl x) (inl y)) as [ | ] eqn : H_OBS.
      { rewrite eqb_eq in H_OBS. inv H_OBS. destruct (eq_dec y y); try done. }
      { rewrite eqb_neq in H_OBS. destruct (eq_dec x y); try done. eapply SIM with (z := inl x). }
    + unfold cons_hsubst, cons_subst. unfold eqb.
      destruct (eq_dec (inr c) (inl y)) as [EQ | NE].
      { inv EQ. }
      { eapply SIM with (z := inr c). }
Qed.

Definition replace_constant_in_trm (c : Henkin_constants) (ct : trm L') (t : trm L') : trm L' :=
  hsubst_trm (one_hsubst (inr c) ct) t.

Definition replace_constant_in_trms {n : nat} (c : Henkin_constants) (ct : trm L') (ts : trms L' n) : trms L' n :=
  hsubst_trms (one_hsubst (inr c) ct) ts.

Definition replace_constant_in_frm (c : Henkin_constants) (ct : trm L') (p : frm L') : frm L' :=
  hsubst_frm (one_hsubst (inr c) ct) p.

Theorem replace_constant_in_frm_compat_subst (c : Henkin_constants) (ct : trm L') (s : subst L') (p : frm L')
  (FRESH : forall x : ivar, is_free_in_trm x ct = true -> hsubst_trm (one_hsubst (inr c) ct) (s x) = Var_trm x)
  : replace_constant_in_frm c ct (subst_frm s p) = subst_frm (replace_constant_in_trm c ct ∘ s)%prg (replace_constant_in_frm c ct p).
Proof.
  unfold replace_constant_in_frm at 2. symmetry. erewrite subst_hsubst_compat_in_frm. 2:{ ii. reflexivity. }
  rewrite <- hsubst_compose_frm_spec. unfold replace_constant_in_frm.
  erewrite subst_hsubst_compat_in_frm. 2:{ ii. reflexivity. }
  rewrite <- hsubst_compose_frm_spec. eapply equiv_hsubst_in_frm_implies_hsubst_frm_same.
  ii. unfold hsubst_compose. unfold "∘"%prg. destruct z as [x | c'].
  - unfold one_hsubst. simpl. unfold replace_constant_in_trm. reflexivity.
  - unfold one_hsubst. simpl. unfold cons_hsubst, nil_hsubst.
    destruct (Prelude.eqb (inr c') (inr c)) as [ | ] eqn : H_OBS.
    + rewrite eqb_eq in H_OBS. inv H_OBS. unfold replace_constant_in_trm.
      rewrite <- nil_hsubst_trm. eapply equiv_hsubst_in_trm_implies_hsubst_trm_same.
      intros [x | c'] OCCURS.
      * apply occurs_free_in_trm_iff, in_accum_hatom_in_trm_iff_is_free_in_trm, fv_is_free_in_trm in OCCURS. simpl. eapply FRESH. done.
      * done.
    + simpl. reflexivity.
Qed.

Theorem replace_constant_with_fresh_ivar_in_frm (c : Henkin_constants) (s : subst L') (p : frm L') (z : ivar)
  (FRESH : s z = Var_trm z)
  : replace_constant_in_frm c (Var_trm z) (subst_frm s p) = subst_frm (replace_constant_in_trm c (Var_trm z) ∘ s)%prg (replace_constant_in_frm c (Var_trm z) p).
Proof.
  eapply replace_constant_in_frm_compat_subst. intros x FREE.
  rewrite is_free_in_trm_unfold in FREE. rewrite Nat.eqb_eq in FREE. subst z.
  now rewrite FRESH.
Qed.

Lemma quick_draw_constant (c : Henkin_constants) (x : ivar) (t : trm L') (y : ivar) (p : frm L')
  (NE : y <> x)
  : replace_constant_in_frm c (Var_trm y) (subst_frm (one_subst x t) p) = subst_frm (one_subst x (replace_constant_in_trm c (Var_trm y) t)) (replace_constant_in_frm c (Var_trm y) p).
Proof.
  rewrite replace_constant_in_frm_compat_subst.
  - eapply equiv_subst_in_frm_implies_subst_frm_same. unfold "∘"%prg. ii.
    unfold replace_constant_in_trm, one_hsubst, one_subst, cons_hsubst, cons_subst.
    destruct (eq_dec z x); try done.
  - intros z FREE. apply fv_is_free_in_trm in FREE. simpl in FREE. destruct FREE as [-> | []].
    unfold one_subst, nil_subst, cons_subst. unfold one_hsubst, cons_hsubst, nil_hsubst.
    destruct (eq_dec z x); try done.
Qed.

End HSUBST.

Section TWILIGHT.

Definition twilight (sigma : hsubst) : subst L' :=
  fun z : ivar => sigma (enum (isEnumerable := @sum_isEnumerable ivar Henkin_constants nat_isEnumerable nat_isEnumerable) z).

Fixpoint twilight_trm (t : trm L') : trm L' :=
  match t with
  | Var_trm x => Var_trm (x * 2)
  | Fun_trm f ts => Fun_trm f (twilight_trms ts)
  | Con_trm c =>
    match c with
    | inl cc => Con_trm c
    | inr hc => Var_trm (hc * 2 + 1)
    end
  end
with twilight_trms {n : nat} (ts : trms L' n) : trms L' n :=
  match ts with
  | O_trms => O_trms
  | S_trms n t ts => S_trms n (twilight_trm t) (twilight_trms ts)
  end.

Lemma twilight_trm_unfold (t : trm L') :
  twilight_trm t =
  match t with
  | Var_trm x => Var_trm (x * 2)
  | Fun_trm f ts => Fun_trm f (twilight_trms ts)
  | Con_trm c =>
    match c with
    | inl cc => Con_trm c
    | inr hc => Var_trm (hc * 2 + 1)
    end
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma twilight_trms_unfold n (ts : trms L' n) :
  twilight_trms ts =
  match ts with
  | O_trms => O_trms
  | S_trms n t ts => S_trms n (twilight_trm t) (twilight_trms ts)
  end.
Proof.
  destruct ts; reflexivity.
Defined.

#[local] Opaque Nat.mul Nat.div "mod".

Lemma twilight_trm_fvs z (t : trm L')
  : is_free_in_trm z t = is_free_in_trm (z * 2) (twilight_trm t)
with twilight_trms_fvs n z (ts : trms L' n)
  : is_free_in_trms z ts = is_free_in_trms (z * 2) (twilight_trms ts).
Proof.
  - trm_ind t; simpl.
    + do 2 rewrite is_free_in_trm_unfold. obs_eqb x z; obs_eqb (x * 2) (z * 2); trivial; lia.
    + do 2 rewrite is_free_in_trm_unfold. eapply twilight_trms_fvs.
    + destruct c as [cc | hc]; do 2 rewrite is_free_in_trm_unfold; trivial.
      obs_eqb (hc * 2 + 1) (z * 2); trivial. lia.
  - trms_ind ts; simpl.
    + do 2 rewrite is_free_in_trms_unfold. reflexivity.
    + rewrite is_free_in_trms_unfold. rewrite twilight_trm_fvs. rewrite IH. reflexivity.
Qed.

Lemma twilight_trm_HC z (t : trm L')
  : HC_occurs_in_trm z t = is_free_in_trm (z * 2 + 1) (twilight_trm t)
with twilight_trms_HC n z (ts : trms L' n)
  : HC_occurs_in_trms z ts = is_free_in_trms (z * 2 + 1) (twilight_trms ts).
Proof.
  - trm_ind t; simpl.
    + rewrite is_free_in_trm_unfold. obs_eqb x z; obs_eqb (x * 2) (z * 2 + 1); trivial; lia.
    + rewrite is_free_in_trm_unfold. rewrite HC_occurs_in_trm_Fun_trm. eapply twilight_trms_HC.
    + destruct c as [cc | hc]; rewrite is_free_in_trm_unfold; rewrite HC_occurs_in_trm_Con_trm; trivial. obs_eqb z hc; obs_eqb (hc * 2 + 1) (z * 2 + 1); trivial; lia.
  - trms_ind ts; simpl.
    + rewrite is_free_in_trms_unfold. reflexivity.
    + rewrite is_free_in_trms_unfold. rewrite HC_occurs_in_trms_S_trms. rewrite twilight_trm_HC. rewrite IH. reflexivity.
Qed.

Lemma twilight_trm_lemma sigma (t : trm L')
  : hsubst_trm sigma t = subst_trm (twilight sigma) (twilight_trm t)
with twilight_trms_lemma n sigma (ts : trms L' n)
  : hsubst_trms sigma ts = subst_trms (twilight sigma) (twilight_trms ts).
Proof.
  - trm_ind t; simpl.
    + rewrite subst_trm_unfold. unfold twilight. unfold enum. simpl.
      exploit (@div_mod_uniqueness (x * 2) 2 x 0). rewrite Nat.mul_comm. lia. lia.
      intros [-> ->]. simpl. reflexivity.
    + rewrite subst_trm_unfold. f_equal. eapply twilight_trms_lemma.
    + destruct c as [cc | hc].
      * rewrite subst_trm_unfold. reflexivity.
      * rewrite subst_trm_unfold. unfold twilight. unfold enum. simpl.
        exploit (@div_mod_uniqueness (hc * 2 + 1) 2 hc 1). rewrite Nat.mul_comm. lia. lia.
        intros [-> ->]. simpl. reflexivity.
  - trms_ind ts; simpl.
    + rewrite subst_trms_unfold. reflexivity.
    + rewrite subst_trms_unfold. f_equal.
      * eapply twilight_trm_lemma.
      * eapply IH.
Qed.

Fixpoint twilight_frm (p : frm L') : frm L' :=
  match p with
  | Rel_frm R ts => Rel_frm R (twilight_trms ts)
  | Eqn_frm t1 t2 => Eqn_frm (twilight_trm t1) (twilight_trm t2)
  | Neg_frm p1 => Neg_frm (twilight_frm p1)
  | Imp_frm p1 p2 => Imp_frm (twilight_frm p1) (twilight_frm p2)
  | All_frm y p1 => All_frm (2 * y) (twilight_frm p1)
  end.

Lemma twilight_frm_fvs z (p : frm L')
  : is_free_in_frm z p = is_free_in_frm (z * 2) (twilight_frm p).
Proof.
  frm_ind p; simpl.
  - eapply twilight_trms_fvs.
  - f_equal; eapply twilight_trm_fvs.
  - eapply IH1.
  - f_equal; [eapply IH1 | eapply IH2].
  - f_equal; [eapply IH1 | f_equal]. rewrite Nat.mul_comm. obs_eqb z y; obs_eqb (2 * z) (2 * y); trivial; lia.
Qed.

Lemma twilight_frm_HC z (p : frm L')
  : HC_occurs_in_frm z p = is_free_in_frm (z * 2 + 1) (twilight_frm p).
Proof.
  frm_ind p; simpl.
  - eapply twilight_trms_HC.
  - f_equal; eapply twilight_trm_HC.
  - eapply IH1.
  - f_equal; [eapply IH1 | eapply IH2].
  - rewrite IH1. clear IH1. replace (negb (z * 2 + 1 =? 2 * y)) with true.
    + destruct (is_free_in_frm (z * 2 + 1) (twilight_frm p1)) as [ | ]; trivial.
    + symmetry. s!. lia.
Qed.

Lemma twilight_chi_frm sigma (p : frm L')
  : hchi_frm sigma p = chi_frm (twilight sigma) (twilight_frm p).
Proof.
  unfold hchi_frm, chi_frm, twilight. f_equal. eapply maxs_ext. intros n. split.
  - s!. intros [[x | hc] [EQ IN]].
    + exists (x * 2). exploit (@div_mod_uniqueness (x * 2) 2 x 0). rewrite Nat.mul_comm. lia. lia.
      intros [-> ->]. simpl. unfold id. rewrite EQ. split; trivial. s!. rewrite <- twilight_frm_fvs. now rewrite in_accum_hatom_in_frm_iff_is_free_in_frm in IN.
    + exists (hc * 2 + 1). exploit (@div_mod_uniqueness (hc * 2 + 1) 2 hc 1). rewrite Nat.mul_comm. lia. lia.
      intros [-> ->]. simpl. unfold id. rewrite EQ. split; trivial. s!. rewrite <- twilight_frm_HC. now rewrite in_accum_hatom_in_frm_iff_HC_occurs_in_frm in IN.
  - s!. intros [x [EQ IN]]. exists (if x mod 2 =? 0 then inl (id (x / 2)) else inr (id (x / 2))). split; trivial. obs_eqb (x mod 2) 0.
    + rewrite in_accum_hatom_in_frm_iff_is_free_in_frm. s!. rewrite twilight_frm_fvs. unfold id. replace (x / 2 * 2) with x; trivial. exploit (@Nat.div_mod x 2); lia.
    + rewrite in_accum_hatom_in_frm_iff_HC_occurs_in_frm. s!. rewrite twilight_frm_HC. unfold id. replace (x / 2 * 2 + 1) with x; trivial. exploit (@Nat.div_mod x 2). lia. enough (WTS : x mod 2 = 1) by lia. exploit (Nat.mod_bound_pos x 2); lia.
Qed.

Lemma twilight_frm_lemma sigma (p : frm L')
  : hsubst_frm sigma p = subst_frm (twilight sigma) (twilight_frm p).
Proof.
  revert sigma. frm_ind p; simpl; i.
  - f_equal; eapply twilight_trms_lemma.
  - f_equal; eapply twilight_trm_lemma.
  - f_equal; eapply IH1.
  - f_equal; [eapply IH1 | eapply IH2].
  - rewrite IH1. rewrite twilight_chi_frm. f_equal. eapply equiv_subst_in_frm_implies_subst_frm_same.
    intros u u_free. unfold twilight, cons_hsubst, cons_subst. simpl. obs_eqb (u mod 2) 0.
    + destruct (eqb _ _) as [ | ] eqn: H_OBS'; rewrite eqb_spec in H_OBS'.
      * destruct (eq_dec _ _) as [EQ | NE]; trivial. contradiction NE. hinv H_OBS'. unfold id. transitivity (2 * (u / 2) + u mod 2). eapply Nat.div_mod. lia. lia.
      * destruct (eq_dec _ _) as [EQ | NE]; trivial. contradiction H_OBS'. f_equal. unfold id. rewrite EQ. symmetry. eapply Nat.div_unique with (r := 0). lia. lia.
    + destruct (eqb _ _) as [ | ] eqn: H_OBS'; rewrite eqb_spec in H_OBS'.
      * destruct (eq_dec _ _) as [EQ | NE]; trivial. congruence.
      * destruct (eq_dec _ _) as [EQ | NE]; trivial. contradiction H_OBS. rewrite EQ. symmetry. eapply Nat.mod_unique with (q := y). lia. lia.
Qed.

Lemma untwilight_trm (t : trm L')
  (HENKIN_FREE : forall c, HC_occurs_in_trm c t = false)
  : twilight_trm t = subst_trm (fun z : ivar => Var_trm (z * 2)) t
with untwilight_trms n (ts : trms L' n)
  (HENKIN_FREE : forall c, HC_occurs_in_trms c ts = false)
  : twilight_trms ts = subst_trms (fun z : ivar => Var_trm (z * 2)) ts.
Proof.
  - trm_ind t; simpl; ii.
    + rewrite subst_trm_unfold. reflexivity.
    + rewrite subst_trm_unfold. f_equal. eapply untwilight_trms. exact HENKIN_FREE.
    + destruct c as [cc | hc].
      * rewrite subst_trm_unfold. reflexivity.
      * pose proof (HENKIN_FREE hc) as claim. rewrite HC_occurs_in_trm_Con_trm in claim. obs_eqb hc hc; [discriminate claim | contradiction].
  - trms_ind ts; simpl; ii.
    + rewrite subst_trms_unfold. reflexivity.
    + rewrite subst_trms_unfold. f_equal.
      * eapply untwilight_trm. intros c. specialize HENKIN_FREE with (c := c). s!. exact (proj1 HENKIN_FREE).
      * eapply IH. intros c. specialize HENKIN_FREE with (c := c). s!. exact (proj2 HENKIN_FREE).
Qed.

Lemma untwilight_frm (p : frm L')
  (HENKIN_FREE : forall c, HC_occurs_in_frm c p = false)
  : twilight_frm p ≡ subst_frm (fun z : ivar => Var_trm (z * 2)) p.
Proof.
  frm_ind p.
  - simpl. econs. eapply untwilight_trms. intros c. exact (HENKIN_FREE c).
  - simpl. econs; eapply untwilight_trm; intros c; specialize HENKIN_FREE with (c := c); ss!.
  - simpl. econs. eapply IH1; intros c; exact (HENKIN_FREE c).
  - simpl. econs; [eapply IH1 | eapply IH2]; intros c; specialize HENKIN_FREE with (c := c); ss!.
  - simpl. rewrite IH1. 2:{ intros c. exact (HENKIN_FREE c). } eapply alpha_All_frm with (z := 2 * y).
    + rewrite Nat.mul_comm. eapply alpha_equiv_eq_intro. do 2 rewrite <- subst_compose_frm_spec. eapply equiv_subst_in_frm_implies_subst_frm_same.
      intros u u_free. unfold subst_compose, one_subst, cons_subst, nil_subst. rewrite subst_trm_unfold with (t := Var_trm _). destruct (eq_dec u y) as [EQ1 | NE1].
      * destruct (eq_dec _ _) as [EQ2 | NE2]; try lia. rewrite subst_trm_unfold. destruct (eq_dec _ _); done.
      * destruct (eq_dec _ _) as [EQ2 | NE2]; try lia. rewrite subst_trm_unfold. destruct (eq_dec _ _) as [EQ3 | NE3]; try done.
        exploit (@chi_frm_not_free L' (fun z : ivar => Var_trm (z * 2)) (All_frm y p1) u).
        { s!. split; trivial. }
        intros claim. rewrite <- EQ3 in claim. rewrite is_free_in_trm_unfold in claim. rewrite Nat.eqb_neq in claim. contradiction.
    + ss!.
    + set (s := fun z : ivar => Var_trm (z * 2)). set (chi := (chi_frm s (All_frm y p1))). s!. destruct (eq_dec (2 * y) chi) as [EQ1 | NE1]; [right | left]; trivial.
      eapply frm_is_fresh_in_subst_iff. unfold frm_is_fresh_in_subst. s!. intros u u_free. destruct (eq_dec u y) as [EQ2 | NE2]; s!; lia.
Qed.

Lemma twilight_trm_spec (t : trm L')
  : twilight_trm t = hsubst_trm (fun z : hatom => match z with inl x => Var_trm (x * 2) | inr hc => Var_trm (hc * 2 + 1) end) t
with twilight_trms_spec n (ts : trms L' n)
  : twilight_trms ts = hsubst_trms (fun z : hatom => match z with inl x => Var_trm (x * 2) | inr hc => Var_trm (hc * 2 + 1) end) ts.
Proof.
  - trm_ind t; simpl.
    + reflexivity.
    + f_equal. eapply twilight_trms_spec.
    + destruct c as [cc | hc]; reflexivity.
  - trms_ind ts; simpl.
    + reflexivity.
    + f_equal.
      * eapply twilight_trm_spec.
      * eapply IH.
Qed.

#[local] Hint Rewrite twilight_trm_spec twilight_trms_spec : simplication_hints.
#[local] Hint Constructors alpha_equiv : core.

Lemma twilight_frm_spec (p : frm L')
  : twilight_frm p ≡ hsubst_frm (fun z : hatom => match z with inl x => Var_trm (x * 2) | inr hc => Var_trm (hc * 2 + 1) end) p.
Proof.
  set (s := fun z : hatom => match z with inl x => Var_trm (x * 2) | inr hc => Var_trm (hc * 2 + 1) end).
  frm_ind p; simpl.
  - unfold s in *; ss!.
  - unfold s in *; ss!.
  - ss!.
  - ss!.
  - simpl. rewrite IH1. eapply alpha_All_frm with (z := 2 * y).
    + rewrite Nat.mul_comm. rewrite subst_nil_frm with (s := one_subst (y * 2) (Var_trm (y * 2))).
      2:{ ii. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec x (y * 2)); done!. }
      erewrite subst_hsubst_compat_in_frm. 2: ii; reflexivity. symmetry. eapply alpha_equiv_eq_intro.
      rewrite <- hsubst_compose_frm_spec. eapply equiv_hsubst_in_frm_implies_hsubst_frm_same. intros u u_free.
      unfold hsubst_compose, one_subst, cons_hsubst, cons_subst, nil_subst. destruct (eqb _ _) as [ | ] eqn: H_OBS1.
      * rewrite eqb_eq in H_OBS1. rewrite hsubst_trm_unfold. subst u. simpl. destruct (eq_dec _ _) as [EQ1 | NE1]; done!.
      * rewrite eqb_neq in H_OBS1. erewrite <- subst_hsubst_compat_in_trm. 2: ii; reflexivity.
        eapply subst_nil_trm. intros x x_free. destruct (eq_dec _ _) as [EQ1 | NE1]; trivial.
        subst x. exploit (hchi_frm_not_free s (All_frm y p1) u).
        { simpl. rewrite andb_true_iff, negb_true_iff, eqb_neq. split; trivial. }
        intros claim. rewrite claim in x_free. discriminate.
    + ss!.
    + s!. set (hchi := hchi_frm s (All_frm y p1)). destruct (eq_dec (2 * y) hchi) as [EQ1 | NE1]; [right | left]; trivial.
      eapply frm_is_fresh_in_hsubst_iff. unfold frm_is_fresh_in_hsubst. s!. intros u u_free. rewrite negb_true_iff.
      unfold cons_hsubst. destruct (eqb _ _) as [ | ] eqn: H_OBS.
      * ss!.
      * rewrite eqb_neq in H_OBS. unfold s. destruct u as [x | hc]; ss!.
Qed.

Lemma twilight_frm_one_hsubst (x : ivar) (t : trm L') (p : frm L')
  : twilight_frm (hsubst_frm (one_hsubst (inl x) t) p) ≡ subst_frm (one_subst (2 * x) (twilight_trm t)) (twilight_frm p).
Proof.
  rewrite twilight_frm_spec. set (fun z : hatom => match z with inl x => Var_trm (x * 2) | inr hc => Var_trm (hc * 2 + 1) end) as eta.
  rewrite twilight_frm_spec. fold eta. erewrite subst_hsubst_compat_in_frm. 2: ii; reflexivity.
  rewrite twilight_trm_spec. fold eta. do 2 rewrite <- hsubst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_hsubst_in_frm_implies_hsubst_frm_same.
  ii. unfold hsubst_compose, to_hsubst, one_hsubst, cons_hsubst, nil_subst. destruct z as [z | z]; simpl.
  - destruct (eqb _ _) as [ | ] eqn: H_OBS1; rewrite eqb_spec in H_OBS1.
    + hinv H_OBS1. unfold one_subst, cons_subst, nil_subst. rewrite Nat.mul_comm. destruct (eq_dec _ _) as [EQ2 | NE2]; done.
    + unfold one_subst, cons_subst, nil_subst. rewrite Nat.mul_comm. destruct (eq_dec _ _) as [EQ2 | NE2].
      * assert (EQ : x = z) by lia. congruence.
      * simpl. rewrite Nat.mul_comm. reflexivity.
  - unfold one_subst, cons_subst, nil_subst. destruct (eq_dec _ _) as [EQ2 | NE2]; trivial. lia.
Qed.

End TWILIGHT.

Section SIM.

#[global]
Instance constant_symbols_sim : Similarity L.(constant_symbols) L'.(constant_symbols) :=
  fun c : L.(constant_symbols) => fun c' : L'.(constant_symbols) => inl c = c'.

#[global]
Instance trm_sim : Similarity (trm L) (trm L') :=
  trm_similarity_instance L.(function_symbols) L.(relation_symbols) L.(function_arity_table) L.(relation_arity_table) L.(constant_symbols) (L.(constant_symbols) + Henkin_constants) constant_symbols_sim.

#[global]
Instance trms_sim (n : nat) : Similarity (trms L n) (trms L' n) :=
  trms_similarity_instance L.(function_symbols) L.(relation_symbols) L.(function_arity_table) L.(relation_arity_table) L.(constant_symbols) (L.(constant_symbols) + Henkin_constants) constant_symbols_sim n.

#[global]
Instance frm_sim : Similarity (frm L) (frm L') :=
  frm_similarity_instance L.(function_symbols) L.(relation_symbols) L.(function_arity_table) L.(relation_arity_table) L.(constant_symbols) (L.(constant_symbols) + Henkin_constants) constant_symbols_sim.

#[global]
Instance frms_sim : Similarity (ensemble (frm L)) (ensemble (frm L')) :=
  frms_similarity_instance L.(function_symbols) L.(relation_symbols) L.(function_arity_table) L.(relation_arity_table) L.(constant_symbols) (L.(constant_symbols) + Henkin_constants) constant_symbols_sim.

Fixpoint embed_trm (t : trm L) : trm L' :=
  match t with
  | Var_trm x => @Var_trm L' x
  | Fun_trm f ts => @Fun_trm L' f (embed_trms ts)
  | Con_trm c => @Con_trm L' (inl c)
  end
with embed_trms {n : nat} (ts : trms L n) : trms L' n :=
  match ts with
  | O_trms => @O_trms L'
  | S_trms n t ts => @S_trms L' n (embed_trm t) (embed_trms ts)
  end.

Lemma embed_trm_unfold (t : trm L) :
  embed_trm t =
  match t with
  | Var_trm x => @Var_trm L' x
  | Fun_trm f ts => @Fun_trm L' f (embed_trms ts)
  | Con_trm c => @Con_trm L' (inl c)
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma embed_trms_unfold n (ts : trms L n) :
  embed_trms ts =
  match ts with
  | O_trms => @O_trms L'
  | S_trms n t ts => @S_trms L' n (embed_trm t) (embed_trms ts)
  end.
Proof.
  destruct ts; reflexivity.
Defined.

Fixpoint embed_frm (p : frm L) : frm L' :=
  match p with
  | Rel_frm R ts => @Rel_frm L' R (embed_trms ts)
  | Eqn_frm t1 t2 => @Eqn_frm L' (embed_trm t1) (embed_trm t2)
  | Neg_frm p1 => @Neg_frm L' (embed_frm p1)
  | Imp_frm p1 p2 => @Imp_frm L' (embed_frm p1) (embed_frm p2)
  | All_frm y p1 => @All_frm L' y (embed_frm p1)
  end.

Lemma embed_trm_from (t : trm L)
  : t =~= embed_trm t
with embed_trms_from n (ts : trms L n)
  : ts =~= embed_trms ts.
Proof.
  - trm_ind t; simpl.
    + econs.
    + econs. eapply embed_trms_from.
    + econs. reflexivity.
  - trms_ind ts; simpl.
    + econs.
    + econs.
      * eapply embed_trm_from.
      * eapply IH.
Qed.

Lemma embed_trm_to (t : trm L) (t' : trm L')
  (SIM : t =~= t')
  : embed_trm t = t'
with embed_trms_to n (ts : trms L n) (ts' : trms L' n)
  (SIM : ts =~= ts')
  : embed_trms ts = ts'.
Proof.
  - induction SIM.
    + reflexivity.
    + simpl. f_equal. eapply embed_trms_to. exact ts_SIM.
    + hinv c_SIM.
  - induction SIM.
    + reflexivity.
    + simpl; f_equal.
      * eapply embed_trm_to. exact t_SIM.
      * eapply IHSIM.
Qed.

Lemma embed_frm_from (p : frm L)
  : p =~= embed_frm p.
Proof.
  frm_ind p; simpl.
  - econs. eapply embed_trms_from.
  - econs; eapply embed_trm_from.
  - econs. eapply IH1.
  - econs; [eapply IH1 | eapply IH2].
  - econs; eapply IH1.
Qed.

Lemma embed_frm_to (p : frm L) (p' : frm L')
  (SIM : p =~= p')
  : embed_frm p = p'.
Proof.
  induction SIM; simpl.
  - f_equal; eapply embed_trms_to; trivial.
  - f_equal; eapply embed_trm_to; trivial.
  - f_equal; trivial.
  - f_equal; trivial.
  - f_equal; trivial.
Qed.

Theorem embed_trm_spec (t : trm L) (t' : trm L')
  : embed_trm t = t' <-> t =~= t'.
Proof.
  split; [intros <- | intros SIM]; [eapply embed_trm_from | eapply embed_trm_to]; trivial.
Qed.

Theorem embed_trms_spec n (ts : trms L n) (ts' : trms L' n)
  : embed_trms ts = ts' <-> ts =~= ts'.
Proof.
  split; [intros <- | intros SIM]; [eapply embed_trms_from | eapply embed_trms_to]; trivial.
Qed.

Theorem embed_frm_spec (p : frm L) (p' : frm L')
  : embed_frm p = p' <-> p =~= p'.
Proof.
  split; [intros <- | intros SIM]; [eapply embed_frm_from | eapply embed_frm_to]; trivial.
Qed.

Theorem embed_frms_spec (Gamma : ensemble (frm L)) (Gamma' : ensemble (frm L'))
  : E.image embed_frm Gamma == Gamma' <-> Gamma =~= Gamma'.
Proof.
  split.
  - intros EQ. split.
    + ii. exists (embed_frm p). split.
      * eapply embed_frm_from.
      * rewrite <- EQ. exists p; trivial.
    + ii. rewrite <- EQ in H. s!. destruct H as [p [-> IN]].
      exists p. split; trivial. eapply embed_frm_from.
  - intros EQ p. destruct EQ as [? ?]. split.
    + ii. s!. destruct H as [q [-> IN]]. pose proof (FWD q IN) as [q' [SIM IN']].
      rewrite <- embed_frm_spec in SIM. subst q'; trivial.
    + ii. s!. pose proof (BWD p H) as [q' [SIM IN']].
      rewrite <- embed_frm_spec in SIM. subst p. exists q'; split; trivial.
Qed.

Fixpoint embed_trm_graph (t' : trm L') : forall t : trm L, Prop :=
  match t' with
  | Var_trm x => fun t => @Var_trm L x = t
  | Fun_trm f ts' => fun t => exists ts, embed_trms_graph ts' ts /\ @Fun_trm L f ts = t
  | Con_trm c => fun t => match c with inl cc => @Con_trm L cc = t | inr hc => False end
  end
with embed_trms_graph {n : nat} (ts' : trms L' n) : forall ts : trms L n, Prop :=
  match ts' with
  | O_trms => fun ts => O_trms = ts
  | S_trms n t' ts' => fun ts => embed_trm_graph t' (head ts) /\ embed_trms_graph ts' (tail ts)
  end.

Fixpoint embed_frm_graph (p' : frm L') : forall p : frm L, Prop :=
  match p' with
  | Rel_frm R ts' => fun p => exists ts, embed_trms_graph ts' ts /\ @Rel_frm L R ts = p
  | Eqn_frm t1' t2' => fun p => exists t1, exists t2, embed_trm_graph t1' t1 /\ embed_trm_graph t2' t2 /\ @Eqn_frm L t1 t2 = p
  | Neg_frm p1' => fun p => exists p1, embed_frm_graph p1' p1 /\ @Neg_frm L p1 = p
  | Imp_frm p1' p2' => fun p => exists p1, exists p2, embed_frm_graph p1' p1 /\ embed_frm_graph p2' p2 /\ @Imp_frm L p1 p2 = p
  | All_frm y p1' => fun p => exists p1, embed_frm_graph p1' p1 /\ @All_frm L y p1 = p
  end.

Lemma embed_trm_graph_sound t' (t : trm L)
  (GRAPH : embed_trm_graph t' t)
  : t =~= t'
with embed_trms_graph_sound n ts' (ts : trms L n)
  (GRAPH : embed_trms_graph ts' ts)
  : ts =~= ts'.
Proof.
  - revert t GRAPH; trm_ind t'; simpl; i.
    + subst t. econs.
    + des. subst t. econs. eapply embed_trms_graph_sound. exact GRAPH.
    + destruct c as [cc | hc].
      * subst t. econs. reflexivity.
      * tauto.
  - revert ts GRAPH; trms_ind ts'; simpl; i.
    + subst ts. econs.
    + revert GRAPH. pattern ts. revert ts. eapply trms_caseS. intros t' ts [GRAPH GRAPH']. econs.
      * eapply embed_trm_graph_sound. exact GRAPH.
      * eapply IH. exact GRAPH'.
Qed.

Lemma embed_trm_graph_complete (t : trm L) t'
  (SIM : t =~= t')
  : embed_trm_graph t' t
with embed_trms_graph_complete n (ts : trms L n) ts'
  (SIM : ts =~= ts')
  : embed_trms_graph ts' ts.
Proof.
  - induction SIM; simpl.
    + reflexivity.
    + exists ts. split.
      * eapply embed_trms_graph_complete. exact ts_SIM.
      * reflexivity.
    + inv c_SIM. reflexivity.
  - induction SIM; simpl.
    + reflexivity.
    + split.
      * eapply embed_trm_graph_complete. exact t_SIM.
      * eapply embed_trms_graph_complete. exact ts_SIM.
Qed.

Lemma embed_frm_graph_sound (p : frm L) p'
  (GRAPH : embed_frm_graph p' p)
  : p =~= p'.
Proof.
  revert p GRAPH. frm_ind p'; simpl; ii.
  - des. subst p. econs. eapply embed_trms_graph_sound; trivial.
  - des. subst p. econs; eapply embed_trm_graph_sound; trivial.
  - des. subst p. econs; eauto.
  - des. subst p. econs; eauto.
  - des. subst p. econs; eauto.
Qed.

Lemma embed_frm_graph_complete (p : frm L) p'
  (SIM : p =~= p')
  : embed_frm_graph p' p.
Proof.
  induction SIM; simpl.
  - exists ts. split; trivial. eapply embed_trms_graph_complete; trivial.
  - exists t1, t2. split. eapply embed_trm_graph_complete; trivial. split; trivial. eapply embed_trm_graph_complete; trivial.
  - exists p1. split; eauto.
  - exists p1, p2. split; eauto.
  - exists p1. split; eauto.
Qed.

Lemma embed_trm_inj_aux (t : trm L) t'
  (GRAPH : embed_trm_graph (embed_trm t') t)
  : t' = t
with embed_trms_inj_aux n (ts : trms L n) ts'
  (GRAPH : embed_trms_graph (embed_trms ts') ts)
  : ts' = ts.
Proof.
  - revert t GRAPH. trm_ind t'; simpl; i.
    + exact GRAPH.
    + des. rewrite <- GRAPH0. f_equal. eapply embed_trms_inj_aux; exact GRAPH.
    + exact GRAPH.
  - revert ts GRAPH. trms_ind ts'; simpl; i.
    + exact GRAPH.
    + revert GRAPH. pattern ts. revert ts. eapply trms_caseS. intros t' ts [GRAPH GRAPH']. f_equal.
      * eapply embed_trm_inj_aux. exact GRAPH.
      * eapply IH. exact GRAPH'.
Qed.

Lemma embed_frm_inj_aux (p : frm L) p'
  (GRAPH : embed_frm_graph (embed_frm p') p)
  : p' = p.
Proof.
  revert p GRAPH; frm_ind p'; simpl; i.
  - des. rewrite <- GRAPH0. f_equal. eapply embed_trms_inj_aux. exact GRAPH.
  - des. rewrite <- GRAPH1. f_equal; eapply embed_trm_inj_aux; trivial.
  - des. rewrite <- GRAPH0. f_equal. eapply IH1; trivial.
  - des. rewrite <- GRAPH1. f_equal; eauto.
  - des. rewrite <- GRAPH0. f_equal; eauto.
Qed.

Theorem embed_trm_inj (t1 : trm L) (t2 : trm L)
  (EQ : embed_trm t1 = embed_trm t2)
  : t1 = t2.
Proof.
  symmetry. eapply embed_trm_inj_aux. rewrite <- EQ. eapply embed_trm_graph_complete. eapply embed_trm_spec. reflexivity.
Qed.

Theorem embed_trms_inj n (ts1 : trms L n) (ts2 : trms L n)
  (EQ : embed_trms ts1 = embed_trms ts2)
  : ts1 = ts2.
Proof.
  symmetry. eapply embed_trms_inj_aux. rewrite <- EQ. eapply embed_trms_graph_complete. eapply embed_trms_spec. reflexivity.
Qed.

Theorem embed_frm_inj (p1 : frm L) (p2 : frm L)
  (EQ : embed_frm p1 = embed_frm p2)
  : p1 = p2.
Proof.
  symmetry. eapply embed_frm_inj_aux. rewrite <- EQ. eapply embed_frm_graph_complete. eapply embed_frm_spec. reflexivity.
Qed.

Lemma embed_fvs_trm (t : trm L)
  : forall z, is_free_in_trm z (embed_trm t) = is_free_in_trm z t
with embed_fvs_trms n (ts : trms L n)
  : forall z, is_free_in_trms z (embed_trms ts) = is_free_in_trms z ts.
Proof.
  - trm_ind t; simpl; i.
    + do 2 rewrite is_free_in_trm_unfold with (t := Var_trm _). reflexivity.
    + do 2 rewrite is_free_in_trm_unfold with (t := Fun_trm _ _). eapply embed_fvs_trms.
    + reflexivity.
  - trms_ind ts; simpl; i.
    + reflexivity.
    + do 2 rewrite is_free_in_trms_unfold with (ts := S_trms _ _ _).
      rewrite embed_fvs_trm; rewrite IH; reflexivity.
Qed.

#[local] Hint Rewrite embed_fvs_trm embed_fvs_trms : simplication_hints.

Lemma embed_fvs_frm (p : frm L)
  : forall z, is_free_in_frm z (embed_frm p) = is_free_in_frm z p.
Proof.
  frm_ind p; done!.
Qed.

#[local] Hint Rewrite embed_fvs_frm : simplication_hints.

Lemma embed_subst_trm (s : subst L) (t : trm L)
  : embed_trm (subst_trm s t) = subst_trm (embed_trm ∘ s)%prg (embed_trm t)
with embed_subst_trms n (s : subst L) (ts : trms L n)
  : embed_trms (subst_trms s ts) = subst_trms (embed_trm ∘ s)%prg (embed_trms ts).
Proof.
  - trm_ind t; simpl; i.
    + reflexivity.
    + do 2 rewrite subst_trm_unfold with (t := Fun_trm _ _). simpl. f_equal. eapply embed_subst_trms.
    + reflexivity.
  - trms_ind ts; simpl; i.
    + reflexivity.
    + do 2 rewrite subst_trms_unfold with (ts := S_trms _ _ _). simpl. f_equal.
      * eapply embed_subst_trm.
      * eapply IH.
Qed.

#[local] Hint Rewrite embed_subst_trm embed_subst_trms : simplication_hints.

Lemma embed_chi_frm (s : subst L) (p : frm L)
  : chi_frm s p = chi_frm (embed_trm ∘ s)%prg (embed_frm p).
Proof.
  unfold chi_frm. f_equal. eapply maxs_ext. i; s!. split; intros [x [<- IN]]; exists x; split; ss!; unfold last_ivar_trm; eapply maxs_ext; i; now do 2 rewrite fv_is_free_in_trm; rewrite embed_fvs_trm.
Qed.

#[local] Hint Rewrite embed_chi_frm : simplication_hints.

Lemma embed_subst_frm (s : subst L) (p : frm L)
  : embed_frm (subst_frm s p) = subst_frm (embed_trm ∘ s)%prg (embed_frm p).
Proof.
  revert s; frm_ind p; try done!. simpl; ii. rewrite embed_chi_frm. f_equal.
  rewrite IH1. eapply equiv_subst_in_frm_implies_subst_frm_same. ii. s!. destruct (eq_dec z y) as [EQ1 | NE1]; done!.
Qed.

Lemma embed_trm_HC_free (t : trm L)
  : forall c : Henkin_constants, HC_occurs_in_trm c (embed_trm t) = false
with embed_trms_HC_free n (ts : trms L n)
  : forall c : Henkin_constants, HC_occurs_in_trms c (embed_trms ts) = false.
Proof.
  - trm_ind t; simpl; i.
    + reflexivity.
    + s!. eapply embed_trms_HC_free.
    + reflexivity.
  - trms_ind ts; simpl; i.
    + reflexivity.
    + s!. split.
      * eapply embed_trm_HC_free.
      * eapply IH.
Qed.

#[local] Hint Rewrite embed_trm_HC_free embed_trms_HC_free : simplication_hints.

Lemma embed_frm_HC_free (p : frm L)
  : forall c : Henkin_constants, HC_occurs_in_frm c (embed_frm p) = false.
Proof.
  frm_ind p; done!.
Qed.

Lemma embed_trm_inv (t' : trm L')
  (HC_free : forall c, HC_occurs_in_trm c t' = false)
  : exists t, embed_trm t = t'
with embed_trms_inv (n : nat) (ts' : trms L' n)
  (HC_free : forall c, HC_occurs_in_trms c ts' = false)
  : exists ts, embed_trms ts = ts'.
Proof.
  - revert HC_free. trm_ind t'; simpl; i.
    + exists (Var_trm x). reflexivity.
    + exploit (embed_trms_inv _ ts). exact HC_free. intros [ts' <-]. exists (@Fun_trm L f ts'). reflexivity.
    + destruct c as [cc | hc].
      * exists (Con_trm cc). reflexivity.
      * specialize HC_free with (c := hc). s!. contradiction.
  - revert HC_free. trms_ind ts'; simpl; i.
    + exists O_trms. reflexivity.
    + exploit (embed_trm_inv t).
      { ii. specialize HC_free with (c := c). ss!. }
      exploit IH.
      { ii. specialize HC_free with (c := c). ss!. }
      intros [ts <-] [t' <-]. exists (@S_trms L n t' ts). reflexivity.
Qed.

Lemma embed_frm_inv (p' : frm L')
  (HC_free : forall c, HC_occurs_in_frm c p' = false)
  : exists p, embed_frm p = p'.
Proof.
  revert HC_free; frm_ind p'; simpl; i.
  - exploit (embed_trms_inv _ ts). done!. intros [ts' <-]. exists (@Rel_frm L R ts'). reflexivity.
  - exploit (embed_trm_inv t1).
    { ii. specialize HC_free with (c := c). ss!. }
    exploit (embed_trm_inv t2).
    { ii. specialize HC_free with (c := c). ss!. }
    intros [t2' <-] [t1' <-]. exists (Eqn_frm t1' t2'). reflexivity.
  - exploit IH1. done!. intros [p1' <-]. exists (Neg_frm p1'). reflexivity.
  - exploit IH1.
    { ii. specialize HC_free with (c := c). ss!. }
    exploit IH2.
    { ii. specialize HC_free with (c := c). ss!. }
    intros [p2' <-] [p1' <-]. exists (Imp_frm p1' p2'). reflexivity.
  - exploit IH1. done!. intros [p1' <-]. exists (All_frm y p1'). reflexivity.
Qed.

Lemma embed_frm_alpha p1 p2
  : p1 ≡ p2 <-> embed_frm p1 ≡ embed_frm p2.
Proof.
  split; intros ALPHA.
  - induction ALPHA; simpl.
    + econs; congruence.
    + econs; congruence.
    + econs; congruence.
    + econs; congruence.
    + do 2 rewrite embed_subst_frm in IHALPHA. eapply alpha_All_frm with (z := z).
      * etransitivity. etransitivity. 2: exact IHALPHA.
        { eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
          intros u u_free. unfold compose. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec u y) as [EQ1 | NE1]; done!.
        }
        { eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
          intros u u_free. unfold compose. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec u y') as [EQ1 | NE1]; done!.
        }
      * change (is_free_in_frm z (embed_frm (All_frm y p1)) = false). rewrite embed_fvs_frm; trivial.
      * change (is_free_in_frm z (embed_frm (All_frm y' p1')) = false). rewrite embed_fvs_frm; trivial.
  - remember (embed_frm p1) as p1' eqn: H_p1'; remember (embed_frm p2) as p2' eqn: H_p2'. revert p1 p2 H_p1' H_p2'. induction ALPHA; i.
    + subst ts'. rewrite H_p1' in H_p2'. apply embed_frm_inj in H_p2'. subst p2. reflexivity.
    + subst t1' t2'. rewrite H_p1' in H_p2'. apply embed_frm_inj in H_p2'. subst p2. reflexivity.
    + destruct p0; simpl in H_p1'; try congruence. destruct p2; simpl in H_p2'; try congruence.
      inv H_p1'. inv H_p2'. econs. eapply IHALPHA; trivial.
    + destruct p0; simpl in H_p1'; try congruence. destruct p3; simpl in H_p2'; try congruence.
      inv H_p1'. inv H_p2'. econs; eauto.
    + destruct p0; simpl in H_p1'; try congruence. destruct p2; simpl in H_p2'; try congruence.
      inv H_p1'. inv H_p2'. eapply alpha_All_frm with (z := z).
      * etransitivity. etransitivity.
        2:{ eapply IHALPHA; [rewrite embed_subst_frm with (p := p0) (s := one_subst y0 (Var_trm z)) | rewrite embed_subst_frm with (p := p2) (s := one_subst y1 (Var_trm z))].
          - eapply equiv_subst_in_frm_implies_subst_frm_same. intros u u_free. unfold compose, one_subst, cons_subst, nil_subst. destruct (eq_dec u y0) as [EQ1 | NE1]; done!.
          - eapply equiv_subst_in_frm_implies_subst_frm_same. intros u u_free. unfold compose, one_subst, cons_subst, nil_subst. destruct (eq_dec u y1) as [EQ1 | NE1]; done!.
        }
        { eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
          intros u u_free. unfold compose. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec u y0) as [EQ1 | NE1]; done!.
        }
        { eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
          intros u u_free. unfold compose. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec u y1) as [EQ1 | NE1]; done!.
        }
      * change (is_free_in_frm z (embed_frm (All_frm y0 p0)) = false) in LFRESH. rewrite embed_fvs_frm in LFRESH; trivial.
      * change (is_free_in_frm z (embed_frm (All_frm y1 p2)) = false) in RFRESH. rewrite embed_fvs_frm in RFRESH; trivial.
Qed.

Fixpoint twilight_trm' (t : trm L') : trm L :=
  match t with
  | Var_trm x => @Var_trm L (x * 2)
  | Fun_trm f ts => @Fun_trm L f (twilight_trms' ts)
  | Con_trm c =>
    match c with
    | inl cc => @Con_trm L cc
    | inr hc => @Var_trm L (hc * 2 + 1)
    end
  end
with twilight_trms' {n : nat} (ts : trms L' n) : trms L n :=
  match ts with
  | O_trms => @O_trms L
  | S_trms n t ts => @S_trms L n (twilight_trm' t) (twilight_trms' ts)
  end.

Lemma twilight_trm'_unfold (t : trm L') :
  twilight_trm' t =
  match t with
  | Var_trm x => @Var_trm L (x * 2)
  | Fun_trm f ts => @Fun_trm L f (twilight_trms' ts)
  | Con_trm c =>
    match c with
    | inl cc => @Con_trm L cc
    | inr hc => @Var_trm L (hc * 2 + 1)
    end
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma twilight_trms'_unfold n (ts : trms L' n) :
  twilight_trms' ts =
  match ts with
  | O_trms => @O_trms L
  | S_trms n t ts => @S_trms L n (twilight_trm' t) (twilight_trms' ts)
  end.
Proof.
  destruct ts; reflexivity.
Defined.

Fixpoint twilight_frm' (p : frm L') : frm L :=
  match p with
  | Rel_frm R ts => @Rel_frm L R (twilight_trms' ts)
  | Eqn_frm t1 t2 => @Eqn_frm L (twilight_trm' t1) (twilight_trm' t2)
  | Neg_frm p1 => @Neg_frm L (twilight_frm' p1)
  | Imp_frm p1 p2 => @Imp_frm L (twilight_frm' p1) (twilight_frm' p2)
  | All_frm y p1 => @All_frm L (2 * y) (twilight_frm' p1)
  end.

Lemma twilight_trm_decomposition (t : trm L')
  : twilight_trm t = embed_trm (twilight_trm' t)
with twilight_trms_decomposition n (ts : trms L' n)
  : twilight_trms ts = embed_trms (twilight_trms' ts).
Proof.
  - trm_ind t; simpl.
    + reflexivity.
    + f_equal. eapply twilight_trms_decomposition.
    + destruct c as [cc | hc]; reflexivity.
  - trms_ind ts; simpl.
    + reflexivity.
    + f_equal.
      * eapply twilight_trm_decomposition.
      * eapply IH.
Qed.

#[local] Hint Rewrite twilight_trm_decomposition twilight_trms_decomposition : simplication_hints.

Lemma twilight_frm_decomposition (p : frm L')
  : twilight_frm p = embed_frm (twilight_frm' p).
Proof.
  frm_ind p; done!.
Qed.

#[local] Hint Rewrite twilight_frm_decomposition.

Lemma twilight_frm'_embed (p : frm L)
  : twilight_frm' (embed_frm p) ≡ subst_frm (fun z : ivar => Var_trm (z * 2)) p.
Proof.
  rewrite embed_frm_alpha. rewrite <- twilight_frm_decomposition.
  rewrite embed_subst_frm. erewrite subst_hsubst_compat_in_frm. 2: ii; reflexivity.
  rewrite twilight_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_hsubst_in_frm_implies_hsubst_frm_same.
  unfold to_hsubst, compose. intros [z | z] FREE.
  - reflexivity.
  - rewrite occurs_free_in_frm_iff in FREE. rewrite in_accum_hatom_in_frm_iff_HC_occurs_in_frm in FREE.
    pose proof (embed_frm_HC_free p z). congruence.
Qed.

Fixpoint unembed_trm (t : trm L') : trm L :=
  match t with
  | Var_trm x => @Var_trm L x
  | Fun_trm f ts => @Fun_trm L f (unembed_trms ts)
  | Con_trm c =>
    match c with
    | inl cc => @Con_trm L cc
    | inr hc => @Var_trm L hc
    end
  end
with unembed_trms {n : nat} (ts : trms L' n) : trms L n :=
  match ts with
  | O_trms => @O_trms L
  | S_trms n t ts => @S_trms L n (unembed_trm t) (unembed_trms ts)
  end.

Lemma unembed_trm_unfold (t : trm L') :
  unembed_trm t =
  match t with
  | Var_trm x => @Var_trm L x
  | Fun_trm f ts => @Fun_trm L f (unembed_trms ts)
  | Con_trm c =>
    match c with
    | inl cc => @Con_trm L cc
    | inr hc => @Var_trm L hc
    end
  end.
Proof.
  destruct t; reflexivity.
Qed.

Lemma unembed_trms_unfold n (ts : trms L' n) :
  unembed_trms ts =
  match ts with
  | O_trms => @O_trms L
  | S_trms n t ts => @S_trms L n (unembed_trm t) (unembed_trms ts)
  end.
Proof.
  destruct ts; reflexivity.
Qed.

Fixpoint unembed_frm (p : frm L') : frm L :=
  match p with
  | Rel_frm R ts => @Rel_frm L R (unembed_trms ts)
  | Eqn_frm t1 t2 => @Eqn_frm L (unembed_trm t1) (unembed_trm t2)
  | Neg_frm p1 => @Neg_frm L (unembed_frm p1)
  | Imp_frm p1 p2 => @Imp_frm L (unembed_frm p1) (unembed_frm p2)
  | All_frm y p1 => @All_frm L y (unembed_frm p1)
  end.

Lemma unembed_trm_lemma (t : trm L)
  : unembed_trm (embed_trm t) = t
with unembed_trms_lemma n (ts : trms L n)
  : unembed_trms (embed_trms ts) = ts.
Proof.
  - trm_ind t; simpl.
    + reflexivity.
    + f_equal; eapply unembed_trms_lemma.
    + reflexivity.
  - trms_ind ts; simpl.
    + reflexivity.
    + f_equal; [eapply unembed_trm_lemma | eapply IH].
Qed.

#[local] Hint Rewrite unembed_trm_lemma unembed_trms_lemma : simplication_hints.

Lemma unembed_frm_lemma (p : frm L)
  : unembed_frm (embed_frm p) = p.
Proof.
  frm_ind p; done!.
Qed.

Lemma unembed_trm_fvs z (t : trm L')
  (HC_free : forall c, HC_occurs_in_trm c t = false)
  : is_free_in_trm z t = is_free_in_trm z (unembed_trm t)
with unembed_trms_fvs n z (ts : trms L' n)
  (HC_free : forall c, HC_occurs_in_trms c ts = false)
  : is_free_in_trms z ts = is_free_in_trms z (unembed_trms ts).
Proof.
  - revert z HC_free. trm_ind t; simpl; i.
    + do 2 rewrite is_free_in_trm_unfold. obs_eqb x z; obs_eqb (x * 2) (z * 2); trivial; lia.
    + do 2 rewrite is_free_in_trm_unfold. eapply unembed_trms_fvs; trivial.
    + destruct c as [cc | hc]; do 2 rewrite is_free_in_trm_unfold; trivial.
      obs_eqb hc z; trivial. specialize HC_free with (c := hc). s!. contradiction.
  - revert z HC_free. trms_ind ts; simpl; i.
    + do 2 rewrite is_free_in_trms_unfold. reflexivity.
    + rewrite is_free_in_trms_unfold. rewrite unembed_trm_fvs. rewrite IH. reflexivity.
      i. specialize HC_free with (c := c). ss!. i. specialize HC_free with (c := c). ss!.
Qed.

Lemma unembed_frm_fvs z (p : frm L')
  (HC_free : forall c, HC_occurs_in_frm c p = false)
  : is_free_in_frm z p = is_free_in_frm z (unembed_frm p).
Proof.
  revert z HC_free. frm_ind p; simpl; i.
  - eapply unembed_trms_fvs. done.
  - f_equal; eapply unembed_trm_fvs; i; specialize HC_free with (c := c); ss!.
  - eapply IH1; i; specialize HC_free with (c := c); ss!.
  - f_equal; [eapply IH1 | eapply IH2]; i; specialize HC_free with (c := c); ss!.
  - f_equal. eapply IH1; i; specialize HC_free with (c := c); ss!.
Qed.

Lemma unembed_chi_frm s (p : frm L')
  (HC_free : forall c, HC_occurs_in_frm c p = false)
  : chi_frm (embed_trm ∘ s)%prg p = chi_frm s (unembed_frm p).
Proof.
  unfold chi_frm, twilight. f_equal. eapply maxs_ext. intros n. split.
  - s!. intros [x [EQ IN]]. exists x. split.
    + unfold last_ivar_trm in *. rewrite <- EQ. eapply maxs_ext. intros z. do 2 rewrite fv_is_free_in_trm. rewrite embed_fvs_trm. reflexivity.
    + rewrite fv_is_free_in_frm.  rewrite fv_is_free_in_frm in IN. rewrite <- unembed_frm_fvs; trivial. 
  - s!. intros [x [EQ IN]]. exists x. split.
    + unfold last_ivar_trm in *. rewrite <- EQ. eapply maxs_ext. intros z. do 2 rewrite fv_is_free_in_trm. rewrite embed_fvs_trm. reflexivity.
    + rewrite fv_is_free_in_frm. rewrite fv_is_free_in_frm in IN. rewrite <- unembed_frm_fvs in IN; trivial. 
Qed.

Lemma unembed_trm_subst s (t : trm L')
  (HC_free : forall c, HC_occurs_in_trm c t = false)
  : unembed_trm (subst_trm s t) = subst_trm (unembed_trm ∘ s)%prg (unembed_trm t)
with unembed_trms_subst n s (ts : trms L' n)
  (HC_free : forall c, HC_occurs_in_trms c ts = false)
  : unembed_trms (subst_trms s ts) = subst_trms (unembed_trm ∘ s)%prg (unembed_trms ts).
Proof.
  - trm_ind t; simpl.
    + do 2 rewrite subst_trm_unfold. reflexivity.
    + do 2 rewrite subst_trm_unfold. simpl. f_equal. eapply unembed_trms_subst. eapply HC_free.
    + destruct c as [cc | hc].
      * reflexivity.
      * specialize HC_free with (c := hc). s!. contradiction.
  - trms_ind ts; simpl.
    + reflexivity.
    + do 2 rewrite subst_trms_unfold with (ts := S_trms _ _ _). simpl. f_equal.
      * eapply unembed_trm_subst. ii. specialize HC_free with (c := c). done!.
      * eapply IH. ii. specialize HC_free with (c := c). done!.
Qed.

Lemma unembed_frm_subst s (p : frm L')
  (s_HC_free : forall z, forall u, is_free_in_trm z (unembed_trm (s u)) = is_free_in_trm z (s u))
  (HC_free : forall c, HC_occurs_in_frm c p = false)
  : unembed_frm (subst_frm s p) = subst_frm (unembed_trm ∘ s)%prg (unembed_frm p).
Proof.
  revert s HC_free s_HC_free. frm_ind p; simpl; i.
  - f_equal. eapply unembed_trms_subst. eapply HC_free.
  - f_equal; eapply unembed_trm_subst; i; specialize HC_free with (c := c); ss!.
  - f_equal; eapply IH1; trivial; i; specialize HC_free with (c := c); ss!.
  - f_equal; [eapply IH1 | eapply IH2]; trivial; i; specialize HC_free with (c := c); ss!.
  - assert (claim : chi_frm s (All_frm y p1) = chi_frm (unembed_trm ∘ s)%prg (All_frm y (unembed_frm p1))).
    { exploit (unembed_chi_frm (unembed_trm ∘ s)%prg (All_frm y p1)).
      - simpl. exact HC_free.
      - intros EQ. transitivity (chi_frm (embed_trm ∘ (unembed_trm ∘ s))%prg (All_frm y p1)).
        + eapply chi_frm_ext. unfold "∘"%prg. intros z. unfold free_in_frm_wrt. split; intros [u [u_free FREE']].
          * exists u. split; trivial. rewrite embed_fvs_trm; trivial. rewrite s_HC_free; trivial.
          * exists u. split; trivial. rewrite embed_fvs_trm in FREE'; trivial. rewrite s_HC_free in FREE'; trivial.
        + change (chi_frm (embed_trm ∘ (unembed_trm ∘ s))%prg (All_frm y p1) = chi_frm (unembed_trm ∘ s)%prg (unembed_frm (All_frm y p1))).
          remember (All_frm y p1) as q eqn: H_q. unfold chi_frm. f_equal. eapply maxs_ext. i; split; intros IN; ss!.
          * exists x. split.
            { rewrite <- H. unfold last_ivar_trm. eapply maxs_ext. intros z; split; intros FREE'.
              - do 2 rewrite fv_is_free_in_trm in *. rewrite embed_fvs_trm; trivial.
              - do 2 rewrite fv_is_free_in_trm in *. rewrite embed_fvs_trm in FREE'; trivial.
            }
            { do 2 rewrite fv_is_free_in_frm in *. rewrite <- unembed_frm_fvs; trivial. }
          * exists x. split.
            { rewrite <- H. unfold last_ivar_trm. eapply maxs_ext. intros z; split; intros FREE'.
              - do 2 rewrite fv_is_free_in_trm in *. rewrite embed_fvs_trm in FREE'; trivial.
              - do 2 rewrite fv_is_free_in_trm in *. rewrite embed_fvs_trm; trivial.
            }
            { do 2 rewrite fv_is_free_in_frm in *. rewrite -> unembed_frm_fvs; trivial. }
    }
    rewrite claim. rewrite IH1; trivial. f_equal.
    + unfold "∘"%prg. eapply equiv_subst_in_frm_implies_subst_frm_same. ii.
      unfold cons_subst. destruct (eq_dec _ _) as [EQ1 | NE1]; reflexivity.
    + ii. unfold cons_subst. destruct (eq_dec _ _) as [EQ1 | NE2]; trivial.
Qed.

Lemma unembed_frm_one_subst x t p
  (t_HC_free : forall c, HC_occurs_in_trm c t = false)
  (p_HC_free : forall c, HC_occurs_in_frm c p = false)
  : unembed_frm (subst_frm (one_subst x t) p) = subst_frm (one_subst x (unembed_trm t)) (unembed_frm p).
Proof.
  rewrite unembed_frm_subst; trivial.
  - eapply equiv_subst_in_frm_implies_subst_frm_same.
    ii. unfold one_subst, cons_subst, nil_subst. unfold "∘"%prg. destruct (eq_dec z x) as [EQ1 | NE1]; trivial.
  - ii. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec _ _) as [EQ1 | NE1]; trivial. rewrite unembed_trm_fvs; trivial.
Qed.

Fixpoint frm_corr (p : frm L) (p' : frm L') {struct p'} : Prop :=
  match p' with
  | Rel_frm R ts' => embed_frm p = hsubst_frm (fun z : hatom => match z with inl x => Var_trm (x * 2) | inr hc => Var_trm (hc * 2 + 1) end) p'
  | Eqn_frm t1' t2' => embed_frm p = hsubst_frm (fun z : hatom => match z with inl x => Var_trm (x * 2) | inr hc => Var_trm (hc * 2 + 1) end) p'
  | Neg_frm p1' => exists p1, p = Neg_frm p1 /\ frm_corr p1 p1'
  | Imp_frm p1' p2' => exists p1, exists p2, p = Imp_frm p1 p2 /\ frm_corr p1 p1' /\ frm_corr p2 p2'
  | All_frm y p1' => exists p1, p = All_frm (y * 2) p1 /\ frm_corr p1 p1'
  end.

Lemma frm_corr_unique (p' : frm L') (p1 : frm L) (p2 : frm L)
  (SIM1 : frm_corr p1 p')
  (SIM2 : frm_corr p2 p')
  : p1 = p2.
Proof.
  revert p1 p2 SIM1 SIM2. frm_ind p'; simpl.
  - intros p1 p2 ? ?. eapply embed_frm_inj. congruence.
  - intros p1 p2 ? ?. eapply embed_frm_inj. congruence.
  - rename p1 into p1'. intros p1 p2 ? ?. destruct SIM1 as [q1 [-> SIM1]], SIM2 as [q2 [-> SIM2]].
    f_equal; eauto.
  - rename p1 into p1', p2 into p2'. intros p1 p2 ? ?. destruct SIM1 as [q1 [q1' [-> [SIM1 SIM1']]]], SIM2 as [q2 [q2' [-> [SIM2 SIM2']]]].
    f_equal; eauto.
  - rename p1 into p1'. intros p1 p2 ? ?. destruct SIM1 as [q1 [-> SIM1]], SIM2 as [q2 [-> SIM2]].
    f_equal; eauto.
Qed.

Lemma frm_corr_twilight_frm' (p' : frm L')
  : frm_corr (twilight_frm' p') p'.
Proof.
  frm_ind p'.
  - simpl. f_equal. rewrite <- twilight_trms_decomposition. eapply twilight_trms_spec.
  - simpl. f_equal; rewrite <- twilight_trm_decomposition; eapply twilight_trm_spec.
  - simpl; eauto.
  - simpl; eauto.
  - simpl. replace (y + (y + 0)) with (y * 2) by lia. eauto.
Qed.

End SIM.

Context {enum_function_symbols : isEnumerable L.(function_symbols)} {enum_constant_symbols : isEnumerable L.(constant_symbols)} {enum_relation_symbols : isEnumerable L.(relation_symbols)}.

Fixpoint Henkin (n : nat) {struct n} : Vector.t (frm L') n -> Vector.t Henkin_constants n -> Prop :=
  match n with
  | O => fun thetas => fun cs => thetas = VNil /\ cs = VNil
  | S n' => fun thetas => fun cs =>
    let x : ivar := fst (cp n') in
    let phi : frm L' := enum (isEnumerable := frm_isEnumerable (L := L') enum_function_symbols (@sum_isEnumerable L.(constant_symbols) Henkin_constants enum_constant_symbols nat_isEnumerable) enum_relation_symbols) (snd (cp n')) in
    let PROP (c : Henkin_constants) : Prop := HC_occurs_in_frm c phi = false /\ V.forallb (fun theta_k => negb (HC_occurs_in_frm c theta_k)) (V.tail thetas) = true in
    V.head thetas = (Imp_frm (subst_frm (one_subst x (@Con_trm L' (inr (V.head cs)))) phi) (All_frm x phi)) /\ Henkin n' (V.tail thetas) (V.tail cs) /\ PROP (V.head cs) /\ ⟪ MIN : forall c, PROP c -> c >= V.head cs ⟫
  end.

#[local] Opaque enum.
#[local] Opaque cp.

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
        + eapply V.to_list_In.
        + unfold "∘"%prg. lia.
    }
    intros [c c_spec]. exists (VCons n (Imp_frm (subst_frm (one_subst x (@Con_trm L' (inr c))) phi) (All_frm x phi)) thetas, VCons n c cs); simpl. split; trivial. split; trivial.
    s!. destruct c_spec as [[NOT_OCCUR NOT_OCCUR'] MIN]; unnw. split.
    + split; trivial.
    + intros c' [NOT_OCCUR1 NOT_OCCUR1']. eapply MIN; trivial. s!. split; trivial.
Qed.

#[local] Open Scope vec_scope.

Lemma Henkin_seq (k : nat) (n : nat) theta_k theta_n c_k c_n
  (LT : k < n)
  (HENKIN_k : Henkin (S k) theta_k c_k)
  (HENKIN_n : Henkin n theta_n c_n)
  : L.In (V.head theta_k) (V.to_list theta_n) /\ L.In (V.head c_k) (V.to_list c_n).
Proof.
  revert theta_k theta_n c_k c_n HENKIN_k HENKIN_n. induction LT as [ | n LT IH].
  - introVCons theta' thetas'; introVCons theta thetas; introVCons c' cs'; introVCons c cs. i.
    pose proof (Henkin_unique _ _ _ _ _ HENKIN_k HENKIN_n) as [theta_eq c_eq]. simpl. split; left; congruence.
  - introVCons theta' thetas'; introVCons theta thetas; introVCons c' cs'; introVCons c cs. i.
    simpl. exploit (IH (theta' :: thetas') thetas (c' :: cs') cs); trivial.
    + simpl in HENKIN_n. des; trivial.
    + intros [? ?]; split; right; trivial.
Qed.

Definition nth_Henkin_axiom (n : nat) : frm L' :=
  V.head (fst (proj1_sig (Henkin_exists (S n)))).

Definition nth_Henkin_constant (n : nat) : Henkin_constants :=
  V.head (snd (proj1_sig (Henkin_exists (S n)))).

Lemma Henkin_constant_does_not_occur_in_any_former_Henkin_axioms k n
  (LT : k < n)
  : HC_occurs_in_frm (nth_Henkin_constant n) (nth_Henkin_axiom k) = false.
Proof.
  unfold nth_Henkin_constant, nth_Henkin_axiom. destruct (Henkin_exists (S n)) as [[theta_n c_n] H_n]. destruct (Henkin_exists (S k)) as [[theta_k c_k] H_k].
  simpl fst in *; simpl snd in *. pose proof H_k as [? [? [[? ?] ?]]]; unnw. rewrite <- negb_true_iff. revert theta_n c_n H_n. introVCons theta thetas; introVCons c cs.
  intros [? [HENKIN_n [[? ?] ?]]]. simpl in *. rewrite V.forallb_forall in H6. pose proof (Henkin_seq k n theta_k thetas c_k cs LT H_k HENKIN_n) as [IN _].
  rewrite V.in_to_list_iff in IN. destruct IN as [i <-]. eapply H6.
Qed.

Lemma Henkin_constant_does_not_occur_in_enum n
  : HC_occurs_in_frm (nth_Henkin_constant n) (enum (isEnumerable := frm_isEnumerable (L := L') enum_function_symbols (@sum_isEnumerable L.(constant_symbols) Henkin_constants enum_constant_symbols nat_isEnumerable) enum_relation_symbols) (snd (cp n))) = false.
Proof.
  unfold nth_Henkin_constant. destruct (Henkin_exists (S n)) as [[theta_n c_n] HENKIN_n]; simpl in *. des; trivial.
Qed.

Lemma Henkin_axiom_is_of_form n
  (x := fst (cp n))
  (phi := enum (isEnumerable := frm_isEnumerable (L := L') enum_function_symbols (@sum_isEnumerable L.(constant_symbols) Henkin_constants enum_constant_symbols nat_isEnumerable) enum_relation_symbols) (snd (cp n)))
  : nth_Henkin_axiom n = (Imp_frm (subst_frm (one_subst x (@Con_trm L' (inr (nth_Henkin_constant n)))) phi) (All_frm x phi)).
Proof.
  unfold nth_Henkin_axiom, nth_Henkin_constant. destruct (Henkin_exists (S n)) as [[theta c] HENKIN]; simpl in *.
  destruct HENKIN as [-> [HENKIN [[NOT_OCCUR NOT_OCCUR'] MIN]]]. reflexivity.
Qed.

End HENKIN.

#[global] Opaque HC_occurs_in_trm.

#[global] Hint Rewrite @HC_occurs_in_trm_Var_trm @HC_occurs_in_trm_Fun_trm @HC_occurs_in_trm_Con_trm : simplication_hints.

#[global] Opaque HC_occurs_in_trms.

#[global] Hint Rewrite @HC_occurs_in_trms_O_trms @HC_occurs_in_trms_S_trms : simplication_hints.

#[global] Opaque accum_HCs_trm.

#[global] Hint Rewrite @accum_HCs_trm_Var_trm @accum_HCs_trm_Fun_trm @accum_HCs_trm_Con_trm : simplication_hints.

#[global] Opaque accum_HCs_trms.

#[global] Hint Rewrite @accum_HCs_trms_O_trms @accum_HCs_trms_S_trms : simplication_hints.

#[global] Hint Rewrite <- @HC_occurs_in_trm_iff_in_accumHCs_trm @HC_occurs_in_trms_iff_in_accumHCs_trms @HC_occurs_in_frm_iff_in_accumHCs_frm : simplication_hints.
