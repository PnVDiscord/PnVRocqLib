Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.System.P.
Require Import PnV.Data.Vector.
Require Import PnV.System.Lambda1.

Module ChurchStyleSTLC.

Export ChurchStyleStlc.

Notation "Gamma '∋' x '⦂' A" := (Lookup x A Gamma) : type_scope.
Notation "Gamma '⊢' M '=' N '⦂' A" := (equality Gamma M N A) : type_scope.

Section STLC_META.

Context {L : language}.

Lemma le_ctx_cons_intro_var1 (Gamma : ctx L) (e : trm L) (ty' : typ L)
  (y := Name.fresh_nm (map fst Gamma ++ FVs e))
  : le_ctx Gamma ((y, ty') :: Gamma).
Proof.
  intros x ty LOOKUP. econs 2.
  - assert (H_IN : L.In x (map fst Gamma)).
    { apply Lookup_to_LookupProp in LOOKUP.
      subst y. induction Gamma as [ | [x1 ty1] Gamma IH]; simpl in *.
      - exact LOOKUP.
      - destruct (eq_dec x x1) as [EQ | NE].
        + left. symmetry. exact EQ.
        + right. eapply IH. exact LOOKUP. 
    }
    pose proof (Name.fresh_nm_notin (map fst Gamma ++ FVs e)) as claim1.
    rewrite L.in_app_iff in claim1. fold y in claim1.
    rewrite Name.ne_iff. intros EQ. subst y. contradiction claim1.
    left. congruence.
  - exact LOOKUP.
Qed.

Inductive whBeta : trm L -> trm L -> Prop :=
  | whBeta_app_lam y ty M N
    : App_trm (Lam_trm y ty M) N ~>β subst_trm (one_subst y N) M
  | whBeta_ksi M M' N
    (WHBETA : M ~>β M')
    : App_trm M N ~>β App_trm M' N
  where "M ~>β N" := (whBeta M N).

Inductive whBetaStar (N : trm L) : trm L -> Set :=
  | whBetaStar_O
    : N ~>β* N
  | whBetaStar_S M M'
    (WHBETA : M ~>β M')
    (WHBETA' : M' ~>β* N)
    : M ~>β* N
  where "M ~>β* N" := (whBetaStar N M).

Inductive whEta (N : trm L) : trm L -> Prop :=
  | whEta_intro x ty
    (FRESH : ~ L.In x (FVs N))
    : Lam_trm x ty (App_trm N (Var_trm x)) ~>η N
  where "M ~>η N" := (whEta N M).

Lemma whEta_intro_var1 (Gamma : ctx L) (e : trm L) (ty : typ L)
  (y := Name.fresh_nm (map fst Gamma ++ FVs e))
  : Lam_trm y ty (App_trm e (Var_trm y)) ~>η e.
Proof.
  econs 1. pose proof (Name.fresh_nm_notin (map fst Gamma ++ FVs e)) as claim1.
  rewrite L.in_app_iff in claim1. fold y in claim1. intros H_contra.
  contradiction claim1. right. exact H_contra.
Defined.

Context {Sigma : signature L}.

Inductive TypingProp (Gamma : ctx L) : trm L -> typ L -> Prop :=
  | TypingProp_Var x ty
    (LOOKUP : Gamma ∋ x ⦂ ty)
    : Gamma ⊢ Var_trm x ⦂ ty
  | TypingProp_App M N ty1 ty2
    (TYPING1 : Gamma ⊢ M ⦂ (ty1 -> ty2))
    (TYPING2 : Gamma ⊢ N ⦂ ty1)
    : Gamma ⊢ App_trm M N ⦂ ty2
  | TypingProp_Lam y M ty1 ty2
    (TYPING : (y, ty1) :: Gamma ⊢ M ⦂ ty2)
    : Gamma ⊢ Lam_trm y ty1 M ⦂ (ty1 -> ty2)
  | TypingProp_Con c
    : Gamma ⊢ Con_trm c ⦂ typ_of_constant c
  where "Gamma '⊢' M '⦂' A" := (TypingProp Gamma M A).

#[local] Hint Constructors TypingProp : core.

Lemma TypingProp_iff Gamma e ty
  : Gamma ⊢ e ⦂ ty <-> inhabited (Typing Gamma e ty).
Proof.
  split; intros TYPING.
  - induction TYPING; simpl.
    + econs. econs 1; eassumption.
    + destruct IHTYPING1, IHTYPING2. econs. econs 2; eassumption.
    + destruct IHTYPING. econs. econs 3; eassumption.
    + econs. econs 4.
  - destruct TYPING as [TYPING]. induction TYPING; simpl; eauto.
Qed.

Section WEAK_NORMALISATION.

Inductive wnNe (Gamma : ctx L) : typ L -> trm L -> Set :=
  | wnNe_Var x ty
    (LOOKUP : Gamma ∋ x ⦂ ty)
    : Gamma ⊢ Var_trm x ⇉ ty
  | wnNe_App u v ty ty'
    (u_wnNe : Gamma ⊢ u ⇉ (ty -> ty')%typ)
    (v_wnNf : Gamma ⊢ v ⇇ ty)
    : Gamma ⊢ App_trm u v ⇉ ty'
  | wnNe_Con c ty
    (ty_EQ : ty = Sigma c)
    : Gamma ⊢ Con_trm c ⇉ ty
  where "Gamma '⊢' M '⇉' A" := (wnNe Gamma A M)
with wnNf (Gamma : ctx L) : typ L -> trm L -> Set :=
  | wnNf_of_wnNe u ty
    (u_wnNe : Gamma ⊢ u ⇉ ty)
    : Gamma ⊢ u ⇇ ty
  | wnNf_Lam x v ty ty'
    (v_wnNf : (x, ty) :: Gamma ⊢ v ⇇ ty')
    : Gamma ⊢ Lam_trm x ty v ⇇ (ty -> ty')%typ
  | wnNf_whBetaReduce_wnNf v v' ty
    (WHBETA : v ~>β v')
    (v_wnNf : Gamma ⊢ v' ⇇ ty)
    : Gamma ⊢ v ⇇ ty
  | wnNf_whEtaExpand_wnNf v v' ty
    (WHETA : v' ~>η v)
    (v_wnNf : Gamma ⊢ v' ⇇ ty)
    : Gamma ⊢ v ⇇ ty
  where "Gamma '⊢' M '⇇' A" := (wnNf Gamma A M).

Fixpoint le_ctx_wnNe (Gamma : ctx L) (ty : typ L) (u : trm L) (u_wnNe : Gamma ⊢ u ⇉ ty) {struct u_wnNe} : forall Gamma', le_ctx Gamma Gamma' -> Gamma' ⊢ u ⇉ ty
with le_ctx_wnNf (Gamma : ctx L) (ty : typ L) (v : trm L) (v_wnNf : Gamma ⊢ v ⇇ ty) {struct v_wnNf} : forall Gamma', le_ctx Gamma Gamma' -> Gamma' ⊢ v ⇇ ty.
Proof.
  - destruct u_wnNe; simpl; intros Gamma' LE.
    + econs 1. eapply LE; eassumption.
    + econs 2.
      * eapply le_ctx_wnNe; eassumption.
      * eapply le_ctx_wnNf; eassumption.
    + econs 3; eassumption.
  - destruct v_wnNf; simpl; intros Gamma' LE.
    + econs 1. eapply le_ctx_wnNe; eassumption.
    + econs 2. eapply le_ctx_wnNf.
      * eassumption.
      * red in LE |- *. intros x1 ty1 LOOKUP1. pattern LOOKUP1. revert LOOKUP1. eapply Lookup_cons.
        { intros. econs 1; eassumption. }
        { intros. econs 2.
          - eassumption.
          - eapply LE; eassumption.
        }
    + econs 3.
      * eassumption.
      * eapply le_ctx_wnNf; eassumption.
    + econs 4.
      * eassumption.
      * eapply le_ctx_wnNf; eassumption.
Defined.

Lemma wnNf_whBetaStar_wnNf Gamma M N ty
  (v_wnNf : Gamma ⊢ N ⇇ ty)
  (WHBETA' : M ~>β* N)
  : Gamma ⊢ M ⇇ ty.
Proof.
  induction WHBETA'; simpl in *.
  - eassumption.
  - econs 3; eassumption.
Defined.

Lemma App_Var_wnNf_inv Gamma ty ty' v
  (y := Name.fresh_nm (map fst Gamma ++ FVs v))
  (v_wnNf : (y, ty) :: Gamma ⊢ App_trm v (Var_trm y) ⇇ ty')
  : Gamma ⊢ v ⇇ (ty -> ty')%typ.
Proof.
  econs 4.
  - eapply whEta_intro_var1 with (Gamma := Gamma) (ty := ty).
  - econs 2. fold y. exact v_wnNf.
Defined.

Fixpoint eval_typ (Gamma : ctx L) (ty : typ L) {struct ty} : trm L -> Set :=
  match ty with
  | bty _ b => fun M => B.sigT (trm L) (fun N => (Gamma ⊢ N ⇉ bty _ b) * (M ~>β* N))%type
  | (ty1 -> ty2)%typ => fun M => forall Gamma', le_ctx Gamma Gamma' -> forall N, eval_typ Gamma' ty1 N -> eval_typ Gamma' ty2 (App_trm M N)
  end.

Lemma eval_typ_alpha (e : trm L) (e' : trm L)
  (ALPHA : subst_trm nil_subst e = subst_trm nil_subst e')
  : forall Gamma, forall ty, eval_typ Gamma ty e -> eval_typ Gamma ty e'.
Admitted.

Fixpoint eval_typ_le_ctx Gamma ty {struct ty} : forall M, eval_typ Gamma ty M -> forall Gamma', le_ctx Gamma Gamma' -> eval_typ Gamma' ty M.
Proof.
  destruct ty as [b | ty1 ty2]; simpl; intros M H_M Gamma' LE.
  - exists H_M.(B.projT1). split.
    + eapply le_ctx_wnNe. exact (fst H_M.(B.projT2)). exact LE.
    + exact (snd H_M.(B.projT2)).
  - intros Delta LE' N H_N. eapply eval_typ_le_ctx.
    + eapply H_M with (Gamma' := Delta).
      * intros x ty LOOKUP. eapply LE'. eapply LE. exact LOOKUP.
      * exact H_N.
    + intros x ty LOOKUP. exact LOOKUP.
Defined.

Fixpoint reflect (Gamma : ctx L) (ty : typ L) {struct ty} : forall e, wnNe Gamma ty e -> eval_typ Gamma ty e
with reify (Gamma : ctx L) (ty : typ L) {struct ty} : forall e, eval_typ Gamma ty e -> wnNf Gamma ty e.
Proof.
  - destruct ty as [b | ty1 ty2]; simpl; intros M H_M.
    + exists M. split.
      * eassumption.
      * econs 1.
    + intros Gamma' LE N H_N. eapply reflect. econs 2.
      * eapply le_ctx_wnNe; [exact H_M | exact LE].
      * eapply reify. exact H_N.
  - destruct ty as [b | ty1 ty2]; simpl; intros M H_M.
    + eapply wnNf_whBetaStar_wnNf with (N := H_M.(B.projT1)).
      * econs 1. exact (fst (B.projT2 H_M)).
      * exact (snd (B.projT2 H_M)).
    + eapply App_Var_wnNf_inv. eapply reify. eapply H_M.
      * eapply le_ctx_cons_intro_var1.
      * eapply reflect. econs 1. econs 1; reflexivity.
Defined.

Fixpoint head_expand (Gamma : ctx L) M M' (ty : typ L) (WHBETA : M ~>β M') {struct ty} : eval_typ Gamma ty M' -> eval_typ Gamma ty M.
Proof.
  destruct ty as [b | ty1 ty2]; simpl; intros H_M.
  - exists H_M.(B.projT1). split.
    + exact (fst H_M.(B.projT2)).
    + econs 2.
      * eassumption.
      * exact (snd H_M.(B.projT2)).
  - intros N Gamma' LE H_N. eapply head_expand.
    + econs 2. eassumption.
    + eapply H_M; eassumption.
Defined.

Definition eval_ctx (Gamma : ctx L) (Delta : ctx L) : subst L -> Set :=
  fun gamma => forall x, forall ty, Lookup x ty Delta -> eval_typ Gamma ty (gamma x).

Lemma eval_ctx_nil_subst {Gamma : ctx L}
  : eval_ctx Gamma Gamma nil_subst.
Proof.
  intros x ty LOOKUP. eapply reflect. econs 1. exact LOOKUP.
Defined.

Definition eval_ctx_cons_subst {Gamma : ctx L} {Gamma' : ctx L} y ty N gamma
  (H_N : eval_typ Gamma' ty N)
  (H_gamma : eval_ctx Gamma' Gamma gamma)
  : eval_ctx Gamma' ((y, ty) :: Gamma) (cons_subst y N gamma).
Proof.
  intros x1 ty1. unfold cons_subst. eapply Lookup_cons.
  - intros x_EQ ty_EQ. destruct (eq_dec x1 y) as [EQ | NE].
    + rewrite -> ty_EQ. eapply H_N.
    + contradiction.
  - intros x_NE. destruct (eq_dec x1 y) as [EQ | NE].
    + rewrite Name.ne_iff in x_NE. contradiction.
    + intros LOOKUP. eapply H_gamma. exact LOOKUP.
Defined.

Lemma eval_ctx_le_ctx {Delta} {Gamma} {Gamma'} {gamma}
  (H_gamma : eval_ctx Delta Gamma gamma)
  (LE : le_ctx Delta Gamma')
  : eval_ctx Gamma' Gamma gamma.
Proof.
  intros x ty LOOKUP. eapply eval_typ_le_ctx.
  - eapply H_gamma. exact LOOKUP.
  - exact LE.
Defined.

Definition semanticTyping (Gamma : ctx L) (e : trm L) (ty : typ L) : Set :=
  forall Delta, forall gamma, eval_ctx Delta Gamma gamma -> eval_typ Delta ty (subst_trm gamma e).

Theorem semanticTyping_sound Gamma e ty
  (TYPING : Typing Gamma e ty)
  : semanticTyping Gamma e ty.
Proof.
  red; induction TYPING; simpl in *; intros Delta gamma rho.
  - eapply rho. exact LOOKUP.
  - eapply IHTYPING1.
    { eassumption. }
    { intros x ty LOOKUP. exact LOOKUP. }
    eapply IHTYPING2.
    { eassumption. }
  - intros N Gamma' LE a. eapply head_expand.
    { econs 1. }
    set (x := chi gamma (Lam_trm y ty1 e1)).
    eapply eval_typ_alpha.
    { symmetry. eapply subst_cons_lemma_aux1 with (ty := ty1); reflexivity. }
    eapply IHTYPING. eapply eval_ctx_cons_subst; [exact a | eapply eval_ctx_le_ctx]; eassumption.
  - eapply reflect. econs 3. reflexivity.
Defined.

Inductive wnStep (Gamma : ctx L) : trm L -> trm L -> typ L -> Prop :=
  | wnStep_refl M ty
    (TYPING : Typing Gamma M ty)
    : wnStep Gamma M M ty
  | wnStep_App M M' N N' ty ty'
    (H_M : wnStep Gamma M M' (ty -> ty')%typ)
    (H_N : wnStep Gamma N N' ty)
    : wnStep Gamma (App_trm M N) (App_trm M' N') ty'
  | wnStep_Lam x M M' ty ty'
    (H_M : wnStep ((x, ty) :: Gamma) M M' ty')
    : wnStep Gamma (Lam_trm x ty M) (Lam_trm x ty M') (ty -> ty')%typ
  | wnStep_whBetaReduce v v' e ty
    (H_M : wnStep Gamma v' e ty)
    (WHBETA : v ~>β v')
    : wnStep Gamma v e ty
  | wnStep_whEtaExpand v v' e ty
    (H_M : wnStep Gamma v' e ty)
    (WHETA : v' ~>η v)
    : wnStep Gamma v e ty.

Theorem wnNe_wnStep_typNe (Gamma : ctx L) u ty
  (u_wnNe : Gamma ⊢ u ⇉ ty)
  : B.sig (trm L) (fun e => wnStep Gamma u e ty /\ typNe Gamma e ty)
with wnNf_wnStep_typNf (Gamma : ctx L) v ty
  (v_wnNf : Gamma ⊢ v ⇇ ty)
  : B.sig (trm L) (fun e => wnStep Gamma v e ty /\ typNf Gamma e ty).
Proof.
  - destruct u_wnNe.
    + exists (Var_trm x). split.
      * eapply wnStep_refl. econs 1. eapply LOOKUP.
      * econs 1. exact LOOKUP.
    + pose proof (wnNe_wnStep_typNe Gamma u (ty -> ty')%typ u_wnNe) as H_M.
      pose proof (wnNf_wnStep_typNf Gamma v ty v_wnNf) as H_N.
      exists (App_trm H_M.(B.proj1_sig) H_N.(B.proj1_sig)). split.
      * eapply wnStep_App; [exact (proj1 H_M.(B.proj2_sig)) | exact (proj1 H_N.(B.proj2_sig))].
      * econs 2; [exact (proj2 H_M.(B.proj2_sig)) | exact (proj2 H_N.(B.proj2_sig))].
    + exists (Con_trm c). split.
      * eapply wnStep_refl. subst ty. econs 4.
      * econs 3. exact ty_EQ.
  - destruct v_wnNf.
    + pose proof (wnNe_wnStep_typNe Gamma u ty u_wnNe) as H_e.
      exists H_e.(B.proj1_sig). split.
      * exact (proj1 H_e.(B.proj2_sig)).
      * econs 1. exact (proj2 H_e.(B.proj2_sig)).
    + pose proof (wnNf_wnStep_typNf ((x, ty) :: Gamma) v ty' v_wnNf) as H_M.
      exists (Lam_trm x ty H_M.(B.proj1_sig)). split.
      * eapply wnStep_Lam. exact (proj1 H_M.(B.proj2_sig)).
      * econs 2. exact (proj2 H_M.(B.proj2_sig)).
    + pose proof (wnNf_wnStep_typNf Gamma v' ty v_wnNf) as H_e.
      exists H_e.(B.proj1_sig). split.
      * eapply wnStep_whBetaReduce; [exact (proj1 H_e.(B.proj2_sig)) | exact WHBETA].
      * exact (proj2 H_e.(B.proj2_sig)).
    + pose proof (wnNf_wnStep_typNf Gamma v' ty v_wnNf) as H_e.
      exists H_e.(B.proj1_sig). split.
      * eapply wnStep_whEtaExpand; [exact (proj1 H_e.(B.proj2_sig)) | exact WHETA].
      * exact (proj2 H_e.(B.proj2_sig)).
Defined.

Corollary Normalisation_by_Evaluation (Gamma : ctx L) (M : trm L) (ty : typ L)
  (TYPING : Typing Gamma M ty)
  : B.sig (trm L) (fun e => wnStep Gamma (subst_trm nil_subst M) e ty /\ typNf Gamma e ty).
Proof.
  exact (wnNf_wnStep_typNf Gamma (subst_trm nil_subst M) ty (reify Gamma ty (subst_trm nil_subst M) (semanticTyping_sound Gamma M ty TYPING Gamma nil_subst eval_ctx_nil_subst))).
Defined.

Definition NbE {Gamma} {M} {ty} (TYPING : Typing Gamma M ty) : trm L :=
  (Normalisation_by_Evaluation Gamma M ty TYPING).(B.proj1_sig).

Lemma NbE_wnStep (Gamma : ctx L) (M : trm L) (ty : typ L) (TYPING : Typing Gamma M ty)
  : wnStep Gamma (subst_trm nil_subst M) (NbE TYPING) ty.
Proof.
  exact (proj1 (Normalisation_by_Evaluation Gamma M ty TYPING).(B.proj2_sig)).
Qed.

Lemma NbE_typNf (Gamma : ctx L) (M : trm L) (ty : typ L) (TYPING : Typing Gamma M ty)
  : typNf Gamma (NbE TYPING) ty.
Proof.
  exact (proj2 (Normalisation_by_Evaluation Gamma M ty TYPING).(B.proj2_sig)).
Qed.

End WEAK_NORMALISATION.

End STLC_META.

End ChurchStyleSTLC.
