Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.System.P.
Require Import PnV.Data.Vector.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.

Module StlcLang.

#[projections(primitive)]
Class language : Type :=
  { basic_types : Set
  ; constants : Set
  }.

Inductive typ (L : language) : Set :=
  | bty (B : L.(basic_types)) : typ L
  | arr (D : typ L) (C : typ L) : typ L.

Class signature (L : language) : Set :=
  typ_of_constant (c : L.(constants)) : typ L.

End StlcLang.

#[global] Bind Scope typ_scope with StlcLang.typ.
#[global] Notation "D -> C" := (@StlcLang.arr _ D C) : typ_scope.

Module ChurchStyleStlc.

Include StlcLang.

#[local] Open Scope name_scope.

#[global]
Instance typ_hasEqDec (L : language)
  (bty_hasEqDec : hasEqDec L.(basic_types))
  : hasEqDec (typ L).
Proof.
  red in bty_hasEqDec |- *. decide equality.
Defined.

Section STLC.

#[local] Hint Resolve Name.ne_pirrel : core.

#[local] Notation bty := (bty _).

Context `{L : !language}.

#[local] Notation typ := (typ L).

Inductive trm : Set :=
  | Var_trm (x : name)
  | App_trm (e1 : trm) (e2 : trm)
  | Lam_trm (y : name) (ty : typ) (e1 : trm)
  | Con_trm (c : L.(constants)).

Section FreeVariables.

Fixpoint FVs (e : trm) : list name :=
  match e with
  | Var_trm x => [x]
  | App_trm e1 e2 => FVs e1 ++ FVs e2
  | Lam_trm y ty e1 => L.remove eq_dec y (FVs e1)
  | Con_trm c => []
  end.

End FreeVariables.

Section Substitution.

Definition subst : Set :=
  name -> trm.

Definition nil_subst : subst :=
  fun z : name => Var_trm z.

Definition cons_subst (x : name) (e : trm) (s : subst) : subst :=
  fun z : name => if eq_dec z x then e else s z.

Definition one_subst (x : name) (e : trm) : subst :=
  cons_subst x e nil_subst.

Definition chi (s : subst) (e : trm) : name :=
  next_name (Name.maxs (FVs e >>= fun x : name => FVs (s x))).

Fixpoint subst_trm (s : subst) (e : trm) : trm :=
  let z : name := chi s e in
  match e with
  | Var_trm x => s x
  | App_trm e1 e2 => App_trm (subst_trm s e1) (subst_trm s e2)
  | Lam_trm y ty e1 => Lam_trm z ty (subst_trm (cons_subst y (Var_trm z) s) e1)
  | Con_trm c => Con_trm c
  end.

End Substitution.

Section BASIC_THEORY1_ON_SYNTAX.

#[local] Open Scope program_scope.

Fixpoint is_free_in (x : Name.t) (e : trm) : bool :=
  match e with
  | Var_trm x' => Prelude.eqb x x'
  | App_trm e1 e2 => is_free_in x e1 || is_free_in x e2
  | Lam_trm x' ty e1 => negb (Prelude.eqb x x') && is_free_in x e1
  | Con_trm c => false
  end.

#[local] Hint Rewrite @eqb_spec : simplication_hints.
#[local] Hint Rewrite andb_true_iff : simplication_hints.
#[local] Hint Rewrite orb_true_iff : simplication_hints.
#[local] Hint Rewrite negb_true_iff : simplication_hints.
#[local] Hint Rewrite Name.maxs_app : simplication_hints.
#[local] Hint Rewrite @L.in_remove_iff : simplication_hints.
#[local] Hint Rewrite @L.in_concat : simplication_hints.

Lemma is_free_in_iff x e
  : is_free_in x e = true <-> L.In x (FVs e).
Proof.
  split; intros H_free.
  - revert x e H_free; induction e; ss!.
  - revert x H_free; induction e; done!.
Qed.

#[local] Hint Rewrite <- is_free_in_iff : simplication_hints.

Lemma last_ivar_trm_gt z e
  (GT : un_name z > un_name (Name.maxs (FVs e)))
  : is_free_in z e = false.
Proof.
  enough (ENOUGH : ~ L.In z (FVs e)) by ss!.
  pose proof (Name.in_le_maxs (FVs e)) as claim1.
  intros CONTRA. apply claim1 in CONTRA. ss!.
Qed.

Lemma chi_not_free s e x
  (FREE : L.In x (FVs e))
  : is_free_in (chi s e) (s x) = false.
Proof.
  enough (ENOUGH : un_name (Name.maxs (FVs (s x))) < un_name (chi s e)) by now eapply last_ivar_trm_gt.
  unfold chi. unfold "<". unfold next_name. set (36 * _) as z. simpl un_name.
  enough (un_name (Name.maxs (FVs (s x))) <= z) by lia.
  enough (un_name (Name.maxs (FVs (s x))) <= un_name (Name.maxs (FVs e >>= (fun x : Name.t => FVs (s x))))) by lia.
  eapply Name.maxs_subset. clear z. i; s!. exists (FVs (s x)). ss!. exists x; done!.
Qed.

Definition is_fresh_in_subst x s e : bool :=
  L.forallb (negb ∘ is_free_in x ∘ s) (FVs e).

Theorem chi_is_fresh_in_subst e s
  : is_fresh_in_subst (chi s e) s e = true.
Proof.
  unfold is_fresh_in_subst. rewrite forallb_forall. ii.
  unfold "∘". rewrite negb_true_iff. eapply chi_not_free. done!.
Qed.

Lemma chi_nil_subst e
  : is_free_in (chi nil_subst e) e = false.
Proof.
  pose proof (chi_is_fresh_in_subst e nil_subst) as claim1.
  unfold is_fresh_in_subst in claim1.
  eapply not_true_iff_false. intros CONTRA. 
  rewrite forallb_forall in claim1. unfold "∘" in claim1. simpl in claim1.
  rewrite -> is_free_in_iff in CONTRA. apply claim1 in CONTRA. ss!.
Qed.

#[local] Hint Unfold compose : simplication_hints.
#[local] Hint Unfold one_subst : simplication_hints.
#[local] Hint Unfold cons_subst : simplication_hints.
#[local] Hint Unfold nil_subst : simplication_hints.

Theorem is_fresh_in_subst_iff e z s
  : is_fresh_in_subst z s e = true <-> is_free_in z (subst_trm s e) = false.
Proof.
  unfold is_fresh_in_subst; revert z s. induction e; simpl; ii; s!.
  - done!.
  - done!.
  - split.
    + intros H_forallb.
      pose proof (eq_dec z (chi s (Lam_trm y ty e))) as [YES | NO]; [left; ss! | right].
      eapply IHe. rewrite L.forallb_forall. intros x x_in. s!. destruct (eq_dec x y) as [H_eq | H_ne].
      * subst y. ss!.
      * rewrite forallb_forall in H_forallb. rewrite <- negb_true_iff. eapply H_forallb. ss!.
    + intros [-> | NOT_FREE].
      * rewrite forallb_forall. intros x x_in. ss!. eapply chi_not_free. ss!.
      * apply IHe in NOT_FREE. rewrite forallb_forall in NOT_FREE. rewrite forallb_forall. intros x x_in; s!.
        exploit (NOT_FREE x). ss!. destruct (eq_dec x y) as [EQ | NE]; ss!.
  - done!.
Qed.

Definition equiv_subst (s1 : subst) (s2 : subst) (e : trm) : Prop :=
  forall z : Name.t, forall FREE : is_free_in z e = true, s1 z = s2 z.

Lemma chi_compat_equiv_subst s1 s2 e
  (EQUIV : equiv_subst s1 s2 e)
  : chi s1 e = chi s2 e.
Proof.
  red in EQUIV. unfold chi. f_equal. eapply Name.maxs_ext. i; ss!; exists x; ss!; exists x0; ss!.
Qed.

Lemma equiv_subst_implies_subst_same s1 s2 e
  (EQUIV : equiv_subst s1 s2 e)
  : subst_trm s1 e = subst_trm s2 e.
Proof.
  red in EQUIV. revert s1 s2 EQUIV. induction e; ii; s!.
  - eapply EQUIV. ss!.
  - f_equal; [eapply IHe1 | eapply IHe2]; ss!.
  - assert (claim1 : chi s1 (Lam_trm y ty e) = chi s2 (Lam_trm y ty e)) by now eapply chi_compat_equiv_subst.
    f_equal; trivial. eapply IHe; ii; destruct (eq_dec z y) as [EQ | NE]; ss!. ii; eapply EQUIV; ss!.
  - reflexivity.
Qed.

Definition subst_compose (s1 : subst) (s2 : subst) : subst :=
  fun z => subst_trm s2 (s1 z).

Lemma distr_compose_one (s1 : subst) (s2 : subst) (x : Name.t) (x' : Name.t) (e : trm) (z : Name.t) (e' : trm)
  (FRESH : forallb (negb ∘ is_free_in x ∘ s1) (remove eq_dec x' (FVs e')) = true)
  (FREE : is_free_in z e' = true)
  : cons_subst x' e (subst_compose s1 s2) z = subst_compose (cons_subst x' (Var_trm x) s1) (cons_subst x e s2) z.
Proof.
  unfold subst_compose, cons_subst. destruct (eq_dec z x') as [H_eq | H_ne].
  - subst z. simpl. destruct (eq_dec x x); [reflexivity | contradiction].
  - rewrite forallb_forall in FRESH. unfold "∘" in FRESH.
    assert (NOT_FREE : is_free_in x (s1 z) = false).
    { rewrite <- negb_true_iff. eapply FRESH. ss!. }
    eapply equiv_subst_implies_subst_same.
    intros z' FREE'. destruct (eq_dec z' x) as [EQ | NE]; [congruence | reflexivity].
Qed.

Definition free_in_wrt (x : Name.t) (s : subst) (e : trm) : Prop :=
  exists y : Name.t, is_free_in y e = true /\ is_free_in x (s y) = true.

Theorem free_in_wrt_iff e z s
  : free_in_wrt z s e <-> is_free_in z (subst_trm s e) = true.
Proof.
  revert z s. unfold free_in_wrt. induction e; simpl; i.
  - split.
    + intros [y [EQ FREE]]. ss!.
    + intros FREE. exists x. ss!.
  - split.
    + intros [y [FREE FREE']]. rewrite orb_true_iff in FREE. rewrite orb_true_iff. destruct FREE as [FREE | FREE].
      { left. done!. }
      { right. done!. }
    + rewrite orb_true_iff. intros [FREE | FREE].
      { rewrite <- IHe1 in FREE. destruct FREE as [y [FREE FREE']]. exists y. done!. }
      { rewrite <- IHe2 in FREE. destruct FREE as [y [FREE FREE']]. exists y. done!. }
  - split.
    + intros (w & FREE & FREE'). s!. split.
      * intros CONTRA. subst z.
        assert (claim1 : is_fresh_in_subst (chi s (Lam_trm y ty e)) s (Lam_trm y ty e) = true).
        { eapply chi_is_fresh_in_subst. }
        unfold is_fresh_in_subst in claim1. rewrite forallb_forall in claim1.
        assert (claim2 : In w (FVs (Lam_trm y ty e))).
        { done!. }
        apply claim1 in claim2. done!.
      * eapply IHe. exists w. ss!. destruct (eq_dec w y) as [? | ?]; ss!.
    + rewrite andb_true_iff. rewrite negb_true_iff. rewrite eqb_spec.
      set (w := chi s (Lam_trm y ty e)). intros [NE FREE].
      rewrite <- IHe in FREE. destruct FREE as [x [FREE FREE']].
      unfold cons_subst in FREE'. destruct (eq_dec x y) as [x_eq_y | x_ne_y].
      * subst x. contradiction NE. done!.
      * exists x. done!.
  - ss!.
Qed.

Lemma chi_frm_ext s1 s2 e1 e2
  (EQUIV : forall z, free_in_wrt z s1 e1 <-> free_in_wrt z s2 e2)
  : chi s1 e1 = chi s2 e2.
Proof.
  assert (claim : forall z, In z (flat_map (FVs ∘ s1) (FVs e1)) <-> In z (flat_map (FVs ∘ s2) (FVs e2))).
  { unfold free_in_wrt in EQUIV. intros z. do 2 rewrite in_flat_map.
    split; intros [x [H_IN1 H_IN2]]; s!.
    - assert (claim1 : exists y, is_free_in y e1 = true /\ is_free_in z (s1 y) = true) by done!.
      apply EQUIV in claim1. destruct claim1 as [y [FREE FREE']]. rewrite -> is_free_in_iff in FREE. rewrite -> is_free_in_iff in FREE'. exists y. done!.
    - assert (claim2 : exists y, is_free_in y e2 = true /\ is_free_in z (s2 y) = true) by done!.
      apply EQUIV in claim2. destruct claim2 as [y [FREE FREE']]. rewrite -> is_free_in_iff in FREE. rewrite -> is_free_in_iff in FREE'. exists y. done!.
  }
  apply Name.maxs_ext in claim. unfold chi. f_equal.
  assert (ENOUGH : forall xs, forall f : Name.t -> list Name.t, Name.maxs (xs >>= f) = Name.maxs (List.flat_map f xs)).
  { induction xs; simpl; i; eauto. eapply un_name_inj. rewrite Name.maxs_app; ss!. }
  do 2 rewrite <- ENOUGH in claim. done!.
Qed.

#[local] Hint Unfold subst_compose : simplication_hints.

Theorem subst_compose_spec e s s'
  : subst_trm (subst_compose s s') e = subst_trm s' (subst_trm s e).
Proof.
  revert s s'. induction e; simpl; i.
  - done!.
  - done!.
  - enough (ENOUGH : chi s' (subst_trm s (Lam_trm y ty e)) = chi (subst_compose s s') (Lam_trm y ty e)).
    { revert ENOUGH.
      set (x := chi s (Lam_trm y ty e)).
      set (z := chi (subst_compose s s') (Lam_trm y ty e)).
      set (w := chi s' (Lam_trm x ty (subst_trm (cons_subst y (Var_trm x) s) e))).
      i. rewrite <- IHe. assert (EQ : z = w) by done. subst z. f_equal; trivial.
      eapply equiv_subst_implies_subst_same. red. ii.
      rewrite <- distr_compose_one with (e' := e).
      - now rewrite EQ.
      - change (is_fresh_in_subst x s (Lam_trm y ty e) = true). eapply chi_is_fresh_in_subst.
      - done.
    }
    eapply chi_frm_ext. intros z. split.
    + simpl. unfold free_in_wrt. intros [x [FREE FREE']]. simpl in FREE.
      rewrite andb_true_iff in FREE. rewrite negb_true_iff in FREE. rewrite eqb_spec in FREE.
      destruct FREE as [NE FREE]. rewrite <- free_in_wrt_iff in FREE. unfold free_in_wrt in FREE.
      destruct FREE as [w [FREE1 FREE2]]. unfold cons_subst in FREE2. destruct (eq_dec w y) as [w_eq_y | w_ne_y].
      * unfold is_free_in in FREE2. subst w. exists x. done!.
      * exists w. split; ss!. rewrite <- free_in_wrt_iff. red. exists x. ss!.
    + intros [x [FREE FREE']]. s!. destruct FREE as [NE FREE].
      rewrite <- free_in_wrt_iff in FREE'. destruct FREE' as [u [FREE' FREE'']]. exists u. split.
      * change (is_free_in u (subst_trm s (Lam_trm y ty e)) = true). rewrite <- free_in_wrt_iff with (z := u).
        exists x. split; s!; done!.
      * done!.
  - done!.
Qed.

Lemma subst_cons_lemma_aux1 N M gamma x y ty
  (x_EQ : x = chi gamma (Lam_trm y ty M))
  : subst_trm nil_subst (subst_trm (one_subst x N) (subst_trm (cons_subst y (Var_trm x) gamma) M)) = subst_trm nil_subst (subst_trm (cons_subst y N gamma) M).
Proof.
  repeat rewrite <- subst_compose_spec. eapply equiv_subst_implies_subst_same.
  red; i. set (iota := nil_subst). s!. destruct (eq_dec _ _) as [EQ1 | NE1]; s!.
  - destruct (eq_dec _ _) as [EQ2 | NE2]; ss!.
  - eapply equiv_subst_implies_subst_same. red; intros u FREE'. s!.
    destruct (eq_dec u x) as [EQ3 | NE3]; trivial. subst u x.
    assert (claim1 : is_free_in z (Lam_trm y ty M) = true) by ss!.
    pose proof (chi_is_fresh_in_subst (Lam_trm y ty M) gamma) as claim2.
    set (u := chi gamma (Lam_trm y ty M)) in *. unfold is_fresh_in_subst in claim2.
    rewrite L.forallb_forall in claim2. rewrite -> is_free_in_iff in claim1.
    pose proof (claim2 z claim1) as claim3. ss!.
Qed.

Inductive alphaEquiv : trm -> trm -> Set :=
  | alphaEquiv_Var x x'
    (x_EQ : x = x')
    : alphaEquiv (Var_trm x) (Var_trm x')
  | alphaEquiv_App M M' N N'
    (ALPHA1 : alphaEquiv M M')
    (ALPHA2 : alphaEquiv N N')
    : alphaEquiv (App_trm M N) (App_trm M' N')
  | alphaEquiv_Lam x'' x x' ty M M'
    (FRESH1 : is_free_in x'' (Lam_trm x ty M) = false)
    (FRESH2 : is_free_in x'' (Lam_trm x' ty M') = false)
    (ALPHA1 : alphaEquiv (subst_trm (one_subst x (Var_trm x'')) M) (subst_trm (one_subst x' (Var_trm x'')) M'))
    : alphaEquiv (Lam_trm x ty M) (Lam_trm x' ty M')
  | alphaEquiv_con c
    : alphaEquiv (Con_trm c) (Con_trm c).

End BASIC_THEORY1_ON_SYNTAX.

Section TypingRule.

Definition ctx : Set :=
  list (name * typ).

Section LOOKUP.

Inductive Lookup (x : name) (ty : typ) : ctx -> Set :=
  | Lookup_Z Gamma x' ty'
    (x_eq : x = x')
    (ty_eq : ty = ty')
    : Lookup x ty ((x', ty') :: Gamma)
  | Lookup_S Gamma x' ty'
    (x_ne : x ≠ x')
    (LOOKUP : Lookup x ty Gamma)
    : Lookup x ty ((x', ty') :: Gamma)
  where "Gamma '∋' x '⦂' A" := (Lookup x A Gamma).

Lemma Lookup_nil x ty (Phi : Lookup x ty [] -> Type)
  : forall LOOKUP, Phi LOOKUP.
Proof.
  intros LOOKUP.
  refine (
    match LOOKUP as LOOKUP in Lookup _ _ Gamma return (match Gamma as Gamma return Lookup x ty Gamma -> Type with [] => Phi | (x', ty') :: Gamma' => fun _ => unit end) LOOKUP with
    | Lookup_Z _ _ _ x' ty' x_eq ty_eq => _
    | Lookup_S _ _ _ x' ty' x_ne LOOKUP => _
    end
  ).
  - econs.
  - econs.
Defined.

Lemma Lookup_cons x ty Gamma x' ty' (Phi : Lookup x ty ((x', ty') :: Gamma) -> Type)
  (Phi_Z : forall x_eq : x = x', forall ty_eq : ty = ty', Phi (Lookup_Z x ty Gamma x' ty' x_eq ty_eq))
  (Phi_S : forall x_ne : x ≠ x', forall LOOKUP : Lookup x ty Gamma, Phi (Lookup_S x ty Gamma x' ty' x_ne LOOKUP))
  : forall LOOKUP, Phi LOOKUP.
Proof.
  intros LOOKUP. revert Phi Phi_Z Phi_S.
  refine (
    match LOOKUP as LOOKUP in Lookup _ _ Gamma return (match Gamma as Gamma return Lookup x ty Gamma -> Type with [] => fun _ => unit | (x', ty') :: Gamma' => fun LOOKUP => forall Phi, forall Phi_Z, forall Phi_S, Phi LOOKUP end) LOOKUP with
    | Lookup_Z _ _ _ x' ty' x_eq ty_eq => _
    | Lookup_S _ _ _ x' ty' x_ne LOOKUP => _
    end
  ).
  - intros. eapply Phi_Z.
  - intros. eapply Phi_S.
Defined.

Fixpoint Lookup_from_lookup_eq (Gamma : ctx) {struct Gamma} : forall x, forall ty, Some ty = L.lookup x Gamma -> Lookup x ty Gamma.
Proof.
  destruct Gamma as [ | [x' ty'] Gamma]; simpl; intros ? ? E; [congruence | destruct (eq_dec x x') as [EQ | NE]].
  - pose proof (f_equal (B.fromMaybe ty') E) as E'. simpl in E'. econs 1; eassumption.
  - pose proof (Lookup_from_lookup_eq Gamma _ _ E) as LOOKUP. rewrite <- Name.ne_iff in NE. econs 2; eassumption.
Defined.

Theorem Lookup_iff x ty Gamma
  : inhabited (Lookup x ty Gamma) <-> L.lookup x Gamma = Some ty.
Proof.
  split.
  - intros [X]. induction X; simpl; destruct (eq_dec x x') as [EQ | NE]; try congruence.
    rewrite Name.ne_iff in x_ne. contradiction.
  - intros E. econs. now eapply Lookup_from_lookup_eq.
Qed.

Fixpoint LookupProp (x : name) (ty : typ) (Gamma : ctx) {struct Gamma} : Prop :=
  match Gamma with
  | [] => False
  | (x', ty') :: Gamma' => if eq_dec x x' then ty = ty' else LookupProp x ty Gamma'
  end.

Lemma Lookup_to_LookupProp x ty Gamma
  (LOOKUP : Lookup x ty Gamma)
  : LookupProp x ty Gamma.
Proof.
  induction LOOKUP; simpl; destruct (eq_dec _ _) as [EQ | NE]; eauto.
  - contradiction.
  - rewrite Name.ne_iff in x_ne. contradiction.
Defined.

Lemma LookupProp_to_Lookup x ty Gamma
  (LOOKUP : LookupProp x ty Gamma)
  : Lookup x ty Gamma.
Proof.
  induction Gamma as [ | [x' ty'] Gamma IH]; simpl in *.
  - exact (False_rec _ LOOKUP).
  - destruct (eq_dec x x') as [EQ | NE].
    + econs 1; eassumption.
    + econs 2; [rewrite <- Name.ne_iff in NE; eassumption | exact (IH LOOKUP)].
Defined.

Lemma LookupProp_Lookup_LookupProp x ty Gamma
  (X : Lookup x ty Gamma)
  : LookupProp_to_Lookup x ty Gamma (Lookup_to_LookupProp x ty Gamma X) = X.
Proof.
  induction X; simpl.
  - destruct (eq_dec x x') as [EQ | NE].
    + f_equal. eapply eq_pirrel_fromEqDec.
    + contradiction.
  - destruct (eq_dec x x') as [EQ | NE].
    + pose proof (COPY := x_ne). rewrite -> Name.ne_iff in COPY. contradiction.
    + f_equal; try eapply Name.ne_pirrel. congruence.
Qed.

Lemma Lookup_unique x ty ty' Gamma
  (LOOKUP : Lookup x ty Gamma)
  (LOOKUP' : Lookup x ty' Gamma)
  : ty = ty'.
Proof.
  revert LOOKUP'; induction LOOKUP; eapply Lookup_cons; intros.
  - congruence.
  - pose proof (COPY := x_ne). rewrite -> Name.ne_iff in COPY. contradiction.
  - pose proof (COPY := x_ne). rewrite -> Name.ne_iff in COPY. contradiction.
  - eauto.
Qed.

Context {bty_hasEqDec : hasEqDec L.(basic_types)}.

Lemma LookupProp_pirrel x ty Gamma
  (LOOKUP : LookupProp x ty Gamma)
  (LOOKUP' : LookupProp x ty Gamma)
  : LOOKUP = LOOKUP'.
Proof.
  revert LOOKUP LOOKUP'; induction Gamma as [ | [x' ty'] Gamma IH]; simpl; intros.
  - tauto.
  - destruct (eq_dec x x') as [EQ | NE].
    + eapply eq_pirrel_fromEqDec.
    + eapply IH.
Qed.

#[global, program]
Instance Lookup_retracts x ty Gamma : B.retracts (Lookup x ty Gamma) (LookupProp x ty Gamma) :=
  { section := Lookup_to_LookupProp x ty Gamma
  ; retraction := LookupProp_to_Lookup x ty Gamma
  ; retraction_section X := LookupProp_Lookup_LookupProp x ty Gamma X
  }.
Next Obligation.
  eapply LookupProp_pirrel.
Qed.

Lemma Lookup_proof_unique x ty Gamma
  (LOOKUP : Lookup x ty Gamma)
  (LOOKUP' : Lookup x ty Gamma)
  : LOOKUP = LOOKUP'.
Proof.
  revert LOOKUP'; induction LOOKUP; eapply Lookup_cons; intros.
  - f_equal; eapply eq_pirrel_fromEqDec.
  - pose proof (COPY := x_ne). rewrite -> Name.ne_iff in COPY. contradiction.
  - pose proof (COPY := x_ne). rewrite -> Name.ne_iff in COPY. contradiction.
  - f_equal; eauto.
Qed.

End LOOKUP.

Context `{Sigma : !signature L}.

Inductive Typing (Gamma : ctx) : trm -> typ -> Set :=
  | Var_typ (x : name) (ty : typ)
    (LOOKUP : Lookup x ty Gamma)
    : Gamma ⊢ Var_trm x ⦂ ty
  | App_typ (e1 : trm) (e2 : trm) (ty1 : typ) (ty2 : typ)
    (TYPING1 : Gamma ⊢ e1 ⦂ (ty1 -> ty2)%typ)
    (TYPING2 : Gamma ⊢ e2 ⦂ ty1)
    : Gamma ⊢ (App_trm e1 e2) ⦂ ty2
  | Lam_typ (y : name) (e1 : trm) (ty1 : typ) (ty2 : typ)
    (TYPING1 : (y, ty1) :: Gamma ⊢ e1 ⦂ ty2)
    : Gamma ⊢ Lam_trm y ty1 e1 ⦂ (ty1 -> ty2)%typ
  | Con_typ (c : L.(constants))
    : Gamma ⊢ Con_trm c ⦂ typ_of_constant (signature := Sigma) c
  where "Gamma '⊢' M '⦂' A" := (Typing Gamma M A) : type_scope.

Definition Typing_code (Gamma : ctx) (e : trm) (ty : typ) : Set :=
  match e with
  | Var_trm x => Lookup x ty Gamma
  | App_trm e1 e2 => { ty1 : typ & (Typing Gamma e1 (ty1 -> ty)%typ * Typing Gamma e2 ty1)%type }
  | Lam_trm y ty1 e1 => { ty2 : typ & (Typing ((y, ty1) :: Gamma) e1 ty2 * B.Prop_to_Set (ty = (ty1 -> ty2)%typ))%type }
  | Con_trm c => B.Prop_to_Set (ty = typ_of_constant c)
  end.

Definition Typing_encode {Gamma} {e} {ty} (TYPING : Typing Gamma e ty) : Typing_code Gamma e ty :=
  match TYPING with
  | Var_typ _ x ty LOOKUP => LOOKUP
  | App_typ _ e1 e2 ty1 ty2 TYPING1 TYPING2 => @existT _ _ ty1 (TYPING1, TYPING2)
  | Lam_typ _ y e1 ty1 ty2 TYPING1 => @existT _ _ ty2 (TYPING1, eq_refl)
  | Con_typ _ c => eq_refl
  end.

Lemma Typing_decode {Gamma} {e} {ty}
  (TYPING : Typing_code Gamma e ty)
  : Typing Gamma e ty.
Proof.
  destruct e; simpl in *.
  - econs 1; eassumption.
  - destruct TYPING as [ty1 [TYPING1 TYPING2]]. econs 2; eassumption.
  - destruct TYPING as [ty2 [TYPING1 EQ]]. red in EQ. subst ty. econs 3; eassumption.
  - red in TYPING. subst ty. econs 4.
Defined.

Lemma Typing_encode_decode Gamma e ty
  (TYPING : Typing_code Gamma e ty)
  : (Typing_encode (Typing_decode TYPING)) = TYPING.
Proof.
  destruct e; simpl in *.
  - reflexivity.
  - destruct TYPING as [ty1 [TYPING1 TYPING2]]. reflexivity.
  - destruct TYPING as [ty1 [TYPING EQ]]. red in EQ. subst ty. reflexivity.
  - red in TYPING. subst ty. reflexivity.
Qed.

Lemma Typing_decode_encode Gamma e ty
  (TYPING : Typing Gamma e ty)
  : (Typing_decode (Typing_encode TYPING)) = TYPING.
Proof.
  destruct TYPING; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Lemma Typing_unique Gamma e ty ty'
  (TYPING : Typing Gamma e ty)
  (TYPING' : Typing Gamma e ty')
  : ty = ty'.
Proof.
  revert ty' TYPING'. induction TYPING; simpl; intros ty'.
  - intros TYPING'. inversion TYPING'. subst. eapply Lookup_unique; eauto.
  - intros TYPING'. inversion TYPING'. subst.
    specialize (IHTYPING1 _ TYPING0). congruence.
  - intros TYPING'. inversion TYPING'. subst.
    f_equal. eapply IHTYPING; eauto.
  - intros TYPING'. inversion TYPING'. congruence.
Qed.

Lemma Typing_proof_unique {bty_hasEqDec : hasEqDec L.(basic_types)} Gamma e ty
  (TYPING : Typing Gamma e ty)
  (TYPING' : Typing Gamma e ty)
  : TYPING = TYPING'.
Proof.
  revert TYPING'. induction TYPING; simpl.
  - intros TYPING'. rewrite <- Typing_decode_encode.
    remember (Typing_encode TYPING') as code eqn: E.
    apply f_equal with (f := Typing_decode) in E.
    rewrite Typing_decode_encode in E. simpl in *.
    f_equal. eapply Lookup_proof_unique.
  - intros TYPING'. rewrite <- Typing_decode_encode.
    remember (Typing_encode TYPING') as code eqn: E.
    apply f_equal with (f := Typing_decode) in E.
    rewrite Typing_decode_encode in E. simpl in *.
    f_equal. destruct code as [ty1' [TYPING1' TYPING2']].
    assert (ty1 = ty1') as EQ.
    { eapply Typing_unique; eauto. }
    subst ty1'. f_equal; eauto.
  - intros TYPING'. rewrite <- Typing_decode_encode.
    remember (Typing_encode TYPING') as code eqn: E.
    apply f_equal with (f := Typing_decode) in E.
    rewrite Typing_decode_encode in E. simpl in *.
    f_equal. destruct code as [ty1' [TYPING1' EQ']].
    assert (ty1' = ty2) as EQ'' by congruence.
    subst ty2.
    rewrite eq_pirrel_fromEqDec with (EQ1 := EQ') (EQ2 := eq_refl).
    cbv. f_equal; eauto.
  - intros TYPING'. rewrite <- Typing_decode_encode.
    remember (Typing_encode TYPING') as code eqn: E.
    apply f_equal with (f := Typing_decode) in E.
    rewrite Typing_decode_encode in E. simpl in *.
    rewrite eq_pirrel_fromEqDec with (EQ1 := code) (EQ2 := eq_refl).
    reflexivity.
Qed.

Fixpoint TypeInfer {bty_hasEqDec : hasEqDec L.(basic_types)} (Gamma : ctx) (e : trm) {struct e} : option typ :=
  match e with
  | Var_trm x => L.lookup x Gamma
  | App_trm e1 e2 =>
    match TypeInfer Gamma e1, TypeInfer Gamma e2 with
    | Some (ty1 -> ty2)%typ, Some ty1' => if eqb ty1 ty1' then Some ty2 else None
    | _, _ => None
    end
  | Lam_trm y ty1 e1 =>
    match TypeInfer ((y, ty1) :: Gamma) e1 with
    | Some ty2 => Some (ty1 -> ty2)%typ
    | _ => None
    end
  | Con_trm c => Some (typ_of_constant c)
  end.

Lemma TypeInfer_eq_Some_intro {bty_hasEqDec : hasEqDec L.(basic_types)} Gamma e ty
  (TYPING : Typing Gamma e ty)
  : TypeInfer Gamma e = Some ty.
Proof.
  induction TYPING; simpl.
  - rewrite <- Lookup_iff. econs; eassumption.
  - rewrite IHTYPING1. rewrite IHTYPING2. unfold eqb. destruct (eq_dec _ _) as [EQ | NE]; [reflexivity | contradiction].
  - rewrite IHTYPING. reflexivity.
  - reflexivity.
Defined.

Lemma TypeInfer_eq_Some_elim {bty_hasEqDec : hasEqDec L.(basic_types)}
  : forall e, forall Gamma, forall ty, Some ty = TypeInfer Gamma e -> Typing Gamma e ty.
Proof.
  fix IH 1. intros e. destruct e as [x | e1 e2 | y ty1 e1 | c]; simpl; intros Gamma ty E.
  - eapply Var_typ; eapply Lookup_from_lookup_eq; eassumption.
  - destruct (TypeInfer Gamma e1) as [[b | ty1' ty2'] | ] eqn: VIEW1; try congruence.
    destruct (TypeInfer Gamma e2) as [ty' | ] eqn: VIEW2; try congruence.
    unfold eqb in E. destruct (eq_dec ty1' ty') as [EQ | NE]; try congruence.
    eapply App_typ with (ty1 := ty'); eapply IH; congruence.
  - destruct (TypeInfer ((y, ty1) :: Gamma) e1) as [ty2 | ] eqn: VIEW1; try congruence.
    apply f_equal with (f := B.fromMaybe ty) in E. simpl in E. subst ty.
    eapply Lam_typ; eapply IH; congruence.
  - apply f_equal with (f := B.fromMaybe ty) in E. simpl in E. subst ty.
    eapply Con_typ.
Defined.

Lemma Typing_retraction {bty_hasEqDec : hasEqDec L.(basic_types)} Gamma e ty
  (TYPING : inhabited (Typing Gamma e ty))
  : Typing Gamma e ty.
Proof.
  eapply TypeInfer_eq_Some_elim. destruct TYPING as [TYPING]. symmetry. eapply TypeInfer_eq_Some_intro. exact TYPING.
Defined.

#[global, program]
Instance Typing_retracts {bty_hasEqDec : hasEqDec L.(basic_types)} Gamma e ty : B.retracts (Typing Gamma e ty) (inhabited (Typing Gamma e ty)) :=
  { section := @inhabits (Typing Gamma e ty)
  ; retraction := Typing_retraction (bty_hasEqDec := bty_hasEqDec) Gamma e ty
  }.
Next Obligation.
  eapply Typing_proof_unique.
Qed.
Next Obligation.
  destruct H. f_equal. eapply Typing_proof_unique.
Qed.

Inductive equality (Gamma : ctx) : trm -> trm -> typ -> Prop :=
  | equality_refl A M
    (TYPING : Gamma ⊢ M ⦂ A)
    : Gamma ⊢ M = M ⦂ A
  | equality_sym A M M'
    (TYPING : Gamma ⊢ M ⦂ A)
    (TYPING' : Gamma ⊢ M' ⦂ A)
    (EQUAL : Gamma ⊢ M = M' ⦂ A)
    : Gamma ⊢ M' = M ⦂ A
  | equality_trans A M M' M''
    (TYPING : Gamma ⊢ M ⦂ A)
    (TYPING' : Gamma ⊢ M' ⦂ A)
    (TYPING'' : Gamma ⊢ M'' ⦂ A)
    (EQUAL1 : Gamma ⊢ M = M' ⦂ A)
    (EQUAL2 : Gamma ⊢ M' = M'' ⦂ A)
    : Gamma ⊢ M = M'' ⦂ A
  | equality_App A B M M' N N'
    (EQUAL1 : Gamma ⊢ M = M' ⦂ (A -> B)%typ)
    (EQUAL2 : Gamma ⊢ N = N' ⦂ A)
    : Gamma ⊢ App_trm M N = App_trm M' N' ⦂ B
  | equality_Lam A B x y y' M M'
    (NOT_FV1 : ~ L.In x (FVs (Lam_trm y A M)))
    (NOT_FV2 : ~ L.In x (FVs (Lam_trm y' A M')))
    (EQUAL1 : (x, A) :: Gamma ⊢ subst_trm (one_subst y (Var_trm x)) M = subst_trm (one_subst y' (Var_trm x)) M' ⦂ B)
    : Gamma ⊢ Lam_trm y A M = Lam_trm y' A M' ⦂ (A -> B)%typ
  | equality_beta A B x M N
    (TYPING : (x, A) :: Gamma ⊢ M ⦂ B)
    (TYPING' : Gamma ⊢ N ⦂ A)
    : Gamma ⊢ App_trm (Lam_trm x A M) N = subst_trm (one_subst x N) M ⦂ B
  | equality_eta A B x M
    (NOT_FV : ~ L.In x (FVs M))
    (TYPING : Gamma ⊢ M ⦂ (A -> B)%typ)
    : Gamma ⊢ Lam_trm x A (App_trm M (Var_trm x)) = M ⦂ (A -> B)%typ
  where "Gamma '⊢' M '=' N '⦂' A" := (equality Gamma M N A).

End TypingRule.

Section AUX1.

Fixpoint typ_height (ty : typ) : nat :=
  match ty with
  | bty b => 0%nat
  | (ty1 -> ty2)%typ => 1 + max (typ_height ty1) (typ_height ty2)
  end.

Definition le_ctx (Gamma : ctx) (Delta : ctx) : Set :=
  forall x, forall ty, Lookup x ty Gamma -> Lookup x ty Delta.

Context `{Sigma : !signature L}.

Lemma Typing_weakening {Gamma : ctx} {Delta : ctx} {e : trm} {ty : typ}
  (TYPING : Typing Gamma e ty)
  (LE : le_ctx Gamma Delta)
  : Typing Delta e ty.
Proof.
  revert Delta LE. induction TYPING; simpl; intros.
  - econs 1. eapply LE. exact LOOKUP.
  - econs 2; eauto.
  - econs 3; eapply IHTYPING. intros x ty LOOKUP. pattern LOOKUP. revert LOOKUP. eapply Lookup_cons.
    + intros x_EQ ty_EQ. subst x ty. econs 1; reflexivity.
    + intros x_NE LOOKUP. econs 2; eauto.
  - econs 4.
Defined.

Definition TypingSubst (Gamma : ctx) (gamma : subst) (Delta : ctx) : Set :=
  forall x, forall ty, Lookup x ty Delta -> Typing Gamma (gamma x) ty.

Definition alpha_equiv (M : trm) (N : trm) : Prop :=
  subst_trm nil_subst M = subst_trm nil_subst N.

End AUX1.

Section BASIC_THEORY2_ON_SYNTAX.

Context `{Sigma : !signature L}.

End BASIC_THEORY2_ON_SYNTAX.

Section SN.

Inductive fullBetaOnce : trm -> trm -> Prop :=
  | fullBetaOnce_beta x ty M N
    : fullBetaOnce (App_trm (Lam_trm x ty M) N) (subst_trm (one_subst x N) M)
  | fullBetaOnce_appl M M' N
    (BETA' : fullBetaOnce M M')
    : fullBetaOnce (App_trm M N) (App_trm M' N)
  | fullBetaOnce_appr M N N'
    (BETA' : fullBetaOnce N N')
    : fullBetaOnce (App_trm M N) (App_trm M N')
  | fullBetaOnce_lam x ty M M'
    (BETA' : fullBetaOnce M M')
    : fullBetaOnce (Lam_trm x ty M) (Lam_trm x ty M')
  where "M ~>β N" := (fullBetaOnce M N).

Inductive fullBetaMany (N : trm) : trm -> Prop :=
  | fullBetaMany_init
    : N ~>β* N
  | fullBetaMany_step M M'
    (STEP : M ~>β M')
    (STEPS : M' ~>β* N)
    : M ~>β* N
  where "M ~>β* N" := (fullBetaMany N M).

#[local] Hint Constructors fullBetaMany : core.

Lemma fullBetaOnce_dec (M : trm)
  : B.sig trm (fun N => fullBetaOnce M N) + B.Prop_to_Set (forall N : trm, ~ fullBetaOnce M N).
Proof.
  induction M.
  - right. red. intros N BETA. inv BETA.
  - destruct M1 as [x | M N | x ty M | c].
    + destruct IHM1 as [[N BETA1] | NOT_BETA1].
      { left. exists (App_trm N M2). econs 2. exact BETA1. }
      destruct IHM2 as [[N BETA2] | NOT_BETA2].
      { left. exists (App_trm (Var_trm x) N). econs 3. exact BETA2. }
      right. red in NOT_BETA1, NOT_BETA2 |- *. intros N BETA. inv BETA.
      { eapply NOT_BETA1. exact BETA'. }
      { eapply NOT_BETA2. exact BETA'. }
    + destruct IHM1 as [[N' BETA1] | NOT_BETA1].
      { left. exists (App_trm N' M2). econs 2. exact BETA1. }
      destruct IHM2 as [[N' BETA2] | NOT_BETA2].
      { left. exists (App_trm (App_trm M N) N'). econs 3. exact BETA2. }
      right. red in NOT_BETA1, NOT_BETA2 |- *. intros N' BETA. inv BETA.
      { eapply NOT_BETA1. exact BETA'. }
      { eapply NOT_BETA2. exact BETA'. }
    + left. exists (subst_trm (one_subst x M2) M). econs 1.
    + destruct IHM1 as [[N BETA1] | NOT_BETA1].
      { left. exists (App_trm N M2). econs 2. exact BETA1. }
      destruct IHM2 as [[N BETA2] | NOT_BETA2].
      { left. exists (App_trm (Con_trm c) N). econs 3. exact BETA2. }
      right. red in NOT_BETA1, NOT_BETA2 |- *. intros N BETA. inv BETA.
      { eapply NOT_BETA1. exact BETA'. }
      { eapply NOT_BETA2. exact BETA'. }
  - destruct IHM as [[N' BETA] | NOT_BETA1].
    + left. exists (Lam_trm y ty N'). econs 4. exact BETA.
    + right. red in NOT_BETA1 |- *. intros N BETA. inv BETA.
      eapply NOT_BETA1. exact BETA'.
  - right. red. intros N BETA. inv BETA.
Defined.

Inductive sn (M : trm) : Prop :=
  | sn_intro
    (sn_inv : forall N, fullBetaOnce M N -> sn N)
    : sn M.

Definition sn_inv {M : trm} (H_sn : sn M) : forall N, fullBetaOnce M N -> sn N :=
  match H_sn with
  | @sn_intro _ sn_inv => sn_inv
  end.

Fixpoint normalize_with_sn (M : trm) (H_sn : sn M) {struct H_sn} : trm :=
  match fullBetaOnce_dec M with
  | inl YES => let N : trm := B.proj1_sig YES in normalize_with_sn N (sn_inv H_sn N (B.proj2_sig YES))
  | inr NO => M
  end.

Lemma normalize_with_sn_unfold M H_sn :
  normalize_with_sn M H_sn =
  match fullBetaOnce_dec M with
  | inl YES => let N : trm := B.proj1_sig YES in normalize_with_sn N (sn_inv H_sn N (B.proj2_sig YES))
  | inr NO => M
  end.
Proof.
  destruct H_sn; reflexivity.
Defined.

Fixpoint normalize_with_sn_pirrel (M : trm) (H_sn : sn M) (H_sn' : sn M) {struct H_sn} : normalize_with_sn M H_sn = normalize_with_sn M H_sn'.
Proof.
  destruct H_sn, H_sn'; simpl. destruct (fullBetaOnce_dec M) as [YES | NO]; simpl.
  - eapply normalize_with_sn_pirrel.
  - reflexivity.
Qed.

Fixpoint normalize_with_sn_normalized (M : trm) (N : trm) (H_sn : sn M) {struct H_sn} : ~ fullBetaOnce (normalize_with_sn M H_sn) N.
Proof.
  destruct H_sn; simpl. intros BETA. destruct (fullBetaOnce_dec M) as [YES | NO].
  - eapply normalize_with_sn_normalized. exact BETA.
  - red in NO. exact (NO N BETA).
Qed.

End SN.

End STLC.

#[global] Arguments trm : clear implicits.
#[global] Arguments ctx : clear implicits.
#[global] Arguments subst : clear implicits.
#[global] Coercion bty : basic_types >-> typ.

End ChurchStyleStlc.
