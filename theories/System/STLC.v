Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.System.P.
Require Import PnV.Data.Vector.
Require Import PnV.System.Lambda1.

Module ChurchStyleStlc1.

Export ChurchStyleStlc.

Notation "Gamma '∋' x '⦂' A" := (Lookup x A Gamma) : type_scope.
Notation "Gamma '⊢' M '=' N '⦂' A" := (equality Gamma M N A) : type_scope.

Section AUX1.

Context {L : language}.

Definition is_lambda (e : trm L) : Prop :=
  match e with
  | Lam_trm _ _ _ => True
  | _ => False
  end.

Fixpoint typ_ord (ty : typ L) : nat :=
  match ty with
  | bty _ b => 0
  | (ty1 -> ty2)%typ => Nat.max (typ_ord ty1 + 1) (typ_ord ty2)
  end.

Inductive typNe (Gamma : ctx L) : trm L -> typ L -> Prop :=
  | typNe_Var x ty
    (LOOKUP : Lookup x ty Gamma)
    : typNe Gamma (Var_trm x) ty
  | typNe_App u v ty ty'
    (u_typNe : typNe Gamma u (ty -> ty')%typ)
    (v_typNf : typNf Gamma v ty)
    : typNe Gamma (App_trm u v) ty'
  | typNe_Con c ty
    (ty_eq : ty = signature c)
    : typNe Gamma (Con_trm c) ty
  where "Gamma '⊢' M '⇉' A" := (typNe Gamma M A)
with typNf (Gamma : ctx L) : trm L -> typ L -> Prop :=
  | typNf_of_typNe u ty
    (u_typNe : typNe Gamma u ty)
    (ty_basic : typ_ord ty = 0)
    : typNf Gamma u ty
  | typNf_Lam x v ty ty'
    (v_typNf : typNf ((x, ty) :: Gamma) v ty')
    : typNf Gamma (Lam_trm x ty v) (ty -> ty')%typ
  where "Gamma '⊢' M '⇇' A" := (typNf Gamma M A).

Lemma typNe_Typing Gamma u ty
  (u_typNe : typNe Gamma u ty)
  : inhabited (Typing Gamma u ty)
with typNf_Typing Gamma v ty
  (v_typNf : typNf Gamma v ty)
  : inhabited (Typing Gamma v ty).
Proof.
  - destruct u_typNe.
    + split. econs 1. exact LOOKUP.
    + pose proof (typNe_Typing _ _ _ u_typNe) as [H_M].
      pose proof (typNf_Typing _ _ _ v_typNf) as [H_N].
      split. econs 2; [exact H_M | exact H_N].
    + subst ty. split. econs 4.
  - destruct v_typNf.
    + pose proof (typNe_Typing _ _ _ u_typNe) as [H_M].
      split. exact H_M.
    + pose proof (typNf_Typing _ _ _ v_typNf) as [H_N].
      split. econs 3. exact H_N.
Defined.

Lemma typNe_betaNf Gamma u ty
  (u_typNe : typNe Gamma u ty)
  : (~ is_lambda u) /\ (forall e, ~ fullBetaOnce u e)
with typNf_betaNf Gamma v ty
  (v_typNf : typNf Gamma v ty)
  : (forall e, ~ fullBetaOnce v e).
Proof.
  - destruct u_typNe; simpl.
    + split; [tauto | eapply Var_stuck].
    + pose proof (typNe_betaNf Gamma u (ty -> ty')%typ u_typNe) as [claim1 claim2].
      pose proof (typNf_betaNf Gamma v ty v_typNf) as claim3.
      split; [tauto | eapply App_stuck].
      * ii. subst u. contradiction claim1. red. tauto.
      * exact claim2.
      * exact claim3.
    + split; [tauto | eapply Con_stuck].
  - destruct v_typNf; simpl.
    + intros e BETA.
      pose proof (typNe_betaNf Gamma u ty u_typNe) as [claim1 claim2].
      contradiction (claim2 e BETA).
    + pose proof (typNf_betaNf ((x, ty) :: Gamma) v ty' v_typNf) as claim1.
      eapply Lam_stuck. exact claim1.
Qed.

Lemma le_ctx_cons Gamma Delta x ty
  (LE : le_ctx Gamma Delta)
  : le_ctx ((x, ty) :: Gamma) ((x, ty) :: Delta).
Proof.
  red in LE |- *. intros x1 ty1 LOOKUP1. pattern LOOKUP1. revert LOOKUP1. eapply Lookup_cons.
  - intros. econs 1; try eassumption.
  - intros. econs 2; try eassumption. eapply LE; try eassumption.
Defined.

Lemma le_ctx_preserves_typNe (Gamma : ctx L) (u : trm L) (ty : typ L)
  (u_typNe : typNe Gamma u ty)
  : forall Delta, le_ctx Gamma Delta -> typNe Delta u ty
with le_ctx_preserves_typNf (Gamma : ctx L) (v : trm L) (ty : typ L)
  (v_typNf : typNf Gamma v ty)
  : forall Delta, le_ctx Gamma Delta -> typNf Delta v ty.
Proof.
  - destruct u_typNe; intros Delta LE.
    + econs 1. eapply LE; eassumption.
    + econs 2.
      * eapply le_ctx_preserves_typNe; eassumption.
      * eapply le_ctx_preserves_typNf; eassumption.
    + econs 3; eassumption.
  - destruct v_typNf; intros Delta LE.
    + econs 1; try eassumption. eapply le_ctx_preserves_typNe; eassumption.
    + econs 2. eapply le_ctx_preserves_typNf; try eassumption. eapply le_ctx_cons; eassumption.
Defined.

Inductive TypingProp (Gamma : ctx L) : trm L -> typ L -> Prop :=
  | TypingProp_Var x ty
    (LOOKUP : Gamma ∋ x ⦂ ty)
    : Gamma ⊢ Var_trm x ⦂ ty
  | TypingProp_App M N ty1 ty2
    (TYPING1 : Gamma ⊢ M ⦂ (ty1 -> ty2)%typ)
    (TYPING2 : Gamma ⊢ N ⦂ ty1)
    : Gamma ⊢ App_trm M N ⦂ ty2
  | TypingProp_Lam y M ty1 ty2
    (TYPING : (y, ty1) :: Gamma ⊢ M ⦂ ty2)
    : Gamma ⊢ Lam_trm y ty1 M ⦂ (ty1 -> ty2)%typ
  | TypingProp_Con c
    : Gamma ⊢ Con_trm c ⦂ signature c
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

End AUX1.

Section STLC_META.

Let powerset (A : Set) : Type :=
  A -> Set.

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

#[local] Infix "≡" := alpha_equiv : type_scope.

Inductive whBeta : trm L -> trm L -> Prop :=
  | whBeta_Beta y ty M N
    : App_trm (Lam_trm y ty M) N ~>β subst_trm (one_subst y N) M
  | whBeta_AppL M M' N
    (WHBETA : M ~>β M')
    : App_trm M N ~>β App_trm M' N
  | whBeta_alpha M N N'
    (WHBETA : M ~>β N)
    (ALPHA : N ≡ N')
    : M ~>β N'
  where "M ~>β N" := (whBeta M N).

Inductive whBetaStar (M : trm L) (N : trm L) : Set :=
  | whBetaStar_alpha
    (ALPHA : M ≡ N)
    : M ~>β* N
  | whBetaStar_beta
    (WHBETA : M ~>β N)
    : M ~>β* N
  | whBetaStar_trans M'
    (WHBETAs1 : M ~>β* M')
    (WHBETAs2 : M' ~>β* N)
    : M ~>β* N
  where "M ~>β* N" := (whBetaStar M N).

Inductive whEta (N : trm L) : trm L -> Prop :=
  | whEta_intro y ty
    (FRESH : ~ L.In y (FVs N))
    : Lam_trm y ty (App_trm N (Var_trm y)) ~>η N
  where "M ~>η N" := (whEta N M).

Lemma whEta_intro_var1 (Gamma : ctx L) (e : trm L) (ty : typ L)
  (y := Name.fresh_nm (map fst Gamma ++ FVs e))
  : Lam_trm y ty (App_trm e (Var_trm y)) ~>η e.
Proof.
  econs 1. pose proof (Name.fresh_nm_notin (map fst Gamma ++ FVs e)) as claim1.
  rewrite L.in_app_iff in claim1. fold y in claim1. intros H_contra.
  contradiction claim1. right. exact H_contra.
Defined.

Section WEAK_NORMALISATION.

Inductive wnNe (Gamma : ctx L) : typ L -> powerset (trm L) :=
  | wnNe_Var x ty
    (LOOKUP : Gamma ∋ x ⦂ ty)
    : Gamma ⊢ Var_trm x ⇉ ty
  | wnNe_App u v ty ty'
    (u_wnNe : Gamma ⊢ u ⇉ (ty -> ty')%typ)
    (v_wnNf : Gamma ⊢ v ⇇ ty)
    : Gamma ⊢ App_trm u v ⇉ ty'
  | wnNe_Con c ty
    (ty_EQ : ty = signature c)
    : Gamma ⊢ Con_trm c ⇉ ty
  where "Gamma '⊢' M '⇉' A" := (wnNe Gamma A M)
with wnNf (Gamma : ctx L) : typ L -> powerset (trm L) :=
  | wnNf_of_wnNe u ty
    (u_wnNe : Gamma ⊢ u ⇉ ty)
    (ty_basic : typ_ord ty = 0)
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
    (ty_arrow : typ_ord ty > 0)
    (v_wnNf : Gamma ⊢ v' ⇇ ty)
    : Gamma ⊢ v ⇇ ty
  | wnNf_alphaConvert_wnNf v v' ty
    (ALPHA : v ≡ v')
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
    + econs 1; [eapply le_ctx_wnNe; eassumption | exact ty_basic].
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
      * eassumption.
      * eapply le_ctx_wnNf; eassumption.
    + econs 5.
      * eassumption.
      * eapply le_ctx_wnNf; eassumption.
Defined.

Lemma wnNf_whBetaStar_wnNf Gamma M N ty
  (v_wnNf : Gamma ⊢ N ⇇ ty)
  (WHBETA' : M ~>β* N)
  : Gamma ⊢ M ⇇ ty.
Proof.
  revert Gamma v_wnNf; induction WHBETA'; i; simpl in *.
  - econs 5; eauto.
  - econs 3; eauto.
  - eauto.
Defined.

Lemma App_Var_wnNf_inv Gamma ty ty' v
  (y := Name.fresh_nm (map fst Gamma ++ FVs v))
  (v_wnNf : (y, ty) :: Gamma ⊢ App_trm v (Var_trm y) ⇇ ty')
  : Gamma ⊢ v ⇇ (ty -> ty')%typ.
Proof.
  econs 4.
  - eapply whEta_intro_var1 with (Gamma := Gamma) (ty := ty).
  - simpl. eapply le_transitivity; [eapply le_intro_plus_r | eapply n1_le_max_n1_n2].
  - econs 2. fold y. exact v_wnNf.
Defined.

Fixpoint eval_typ (Gamma : ctx L) (ty : typ L) {struct ty} : powerset (trm L) :=
  match ty with
  | bty _ b => fun M => B.sigT (trm L) (fun N => (Gamma ⊢ N ⇉ bty _ b) * (M ~>β* N))%type
  | (ty1 -> ty2)%typ => fun M => forall Gamma', le_ctx Gamma Gamma' -> forall N, eval_typ Gamma' ty1 N -> eval_typ Gamma' ty2 (App_trm M N)
  end.

Lemma eval_typ_alpha (e : trm L) (e' : trm L)
  (ALPHA : alpha_equiv e e')
  : forall Gamma, forall ty, eval_typ Gamma ty e -> eval_typ Gamma ty e'.
Proof.
  intros Gamma ty; revert e e' ALPHA Gamma. induction ty as [b | ty1 IH1 ty2 IH2]; simpl; intros ? ? ? ? H_e.
  - exists H_e.(B.projT1). split.
    + exact (fst H_e.(B.projT2)).
    + econs 3.
      * econs 1. red in ALPHA |- *. symmetry. exact ALPHA.
      * exact (snd H_e.(B.projT2)).
  - intros Gamma' LE N H_N. eapply IH2 with (e := App_trm e N).
    + red in ALPHA |- *. simpl. congruence.
    + eapply H_e; eauto.
Defined.

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
      * econs 1. red; reflexivity.
    + intros Gamma' LE N H_N. eapply reflect. econs 2.
      * eapply le_ctx_wnNe; [exact H_M | exact LE].
      * eapply reify. exact H_N.
  - destruct ty as [b | ty1 ty2]; simpl; intros M H_M.
    + eapply wnNf_whBetaStar_wnNf with (N := H_M.(B.projT1)).
      * econs 1; [exact (fst (B.projT2 H_M)) | reflexivity].
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
    + econs 3.
      * econs 2. eassumption.
      * exact (snd H_M.(B.projT2)).
  - intros N Gamma' LE H_N. eapply head_expand.
    + econs 2. eassumption.
    + eapply H_M; eassumption.
Defined.

Definition eval_ctx (Gamma : ctx L) (Delta : ctx L) : powerset (subst L) :=
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

#[local] Notation "Gamma ⊢ M ⦂ A" := (Typing Gamma M A) : type_scope.
#[local] Notation "Gamma ⊧ M ⦂ A" := (semanticTyping Gamma M A) : type_scope.

Theorem semanticTyping_sound Gamma e ty
  (TYPING : Gamma ⊢ e ⦂ ty)
  : Gamma ⊧ e ⦂ ty.
Proof.
  red; induction TYPING; simpl in *; intros Delta gamma rho.
  - eapply rho. exact LOOKUP.
  - eapply IHTYPING1.
    { eassumption. }
    { intros x ty LOOKUP. exact LOOKUP. }
    eapply IHTYPING2.
    { eassumption. }
  - intros Gamma' LE N a. eapply head_expand.
    { econs 1. }
    set (x := chi gamma (Lam_trm y ty1 e1)).
    eapply eval_typ_alpha.
    { red. symmetry. eapply subst_cons_lemma_aux1 with (ty := ty1); reflexivity. }
    eapply IHTYPING. eapply eval_ctx_cons_subst; [exact a | eapply eval_ctx_le_ctx]; eassumption.
  - eapply reflect. econs 3. reflexivity.
Defined.

Inductive wnStep (Gamma : ctx L) : trm L -> trm L -> typ L -> Prop :=
  | wnStep_Var x ty
    (LOOKUP : Gamma ∋ x ⦂ ty)
    : Gamma ⊢ Var_trm x ~~> Var_trm x ⦂ ty
  | wnStep_App M M' N N' ty ty'
    (H_M : Gamma ⊢ M ~~> M' ⦂ (ty -> ty')%typ)
    (H_N : Gamma ⊢ N ~~> N' ⦂ ty)
    : Gamma ⊢ App_trm M N ~~> App_trm M' N' ⦂ ty'
  | wnStep_Lam x M M' ty ty'
    (H_M : (x, ty) :: Gamma ⊢ M ~~> M' ⦂ ty')
    : Gamma ⊢ Lam_trm x ty M ~~> Lam_trm x ty M' ⦂ (ty -> ty')%typ
  | wnStep_Con c
    : Gamma ⊢ Con_trm c ~~> Con_trm c ⦂ signature c
  | wnStep_whBetaReduce v v' e ty
    (H_M : Gamma ⊢ v' ~~> e ⦂ ty)
    (WHBETA : v ~>β v')
    : Gamma ⊢ v ~~> e ⦂ ty
  | wnStep_whEtaExpand v v' e ty
    (H_M : Gamma ⊢ v' ~~> e ⦂ ty)
    (WHETA : v' ~>η v)
    (ty_arrow : typ_ord ty > 0)
    : Gamma ⊢ v ~~> e ⦂ ty
  | wnStep_alpha v v' e ty
    (H_M : Gamma ⊢ v' ~~> e ⦂ ty)
    (ALPHA : v ≡ v')
    : Gamma ⊢ v ~~> e ⦂ ty
  where "Gamma ⊢ M ~~> N ⦂ A" := (wnStep Gamma M N A).

Theorem wnNe_wnStep_typNe Gamma u ty
  (u_wnNe : Gamma ⊢ u ⇉ ty)
  : B.sig (trm L) (fun e => wnStep Gamma u e ty /\ typNe Gamma e ty)
with wnNf_wnStep_typNf Gamma v ty
  (v_wnNf : Gamma ⊢ v ⇇ ty)
  : B.sig (trm L) (fun e => wnStep Gamma v e ty /\ typNf Gamma e ty).
Proof.
  - destruct u_wnNe.
    + exists (Var_trm x). split.
      * eapply wnStep_Var. eapply LOOKUP.
      * econs 1. exact LOOKUP.
    + pose proof (wnNe_wnStep_typNe Gamma u (ty -> ty')%typ u_wnNe) as H_M.
      pose proof (wnNf_wnStep_typNf Gamma v ty v_wnNf) as H_N.
      exists (App_trm H_M.(B.proj1_sig) H_N.(B.proj1_sig)). split.
      * eapply wnStep_App; [exact (proj1 H_M.(B.proj2_sig)) | exact (proj1 H_N.(B.proj2_sig))].
      * econs 2; [exact (proj2 H_M.(B.proj2_sig)) | exact (proj2 H_N.(B.proj2_sig))].
    + exists (Con_trm c). split.
      * subst ty. eapply wnStep_Con.
      * econs 3. exact ty_EQ.
  - destruct v_wnNf.
    + pose proof (wnNe_wnStep_typNe Gamma u ty u_wnNe) as H_e.
      exists H_e.(B.proj1_sig). split.
      * exact (proj1 H_e.(B.proj2_sig)).
      * econs 1; [exact (proj2 H_e.(B.proj2_sig)) | exact ty_basic].
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
      * eapply wnStep_whEtaExpand; [exact (proj1 H_e.(B.proj2_sig)) | exact WHETA | exact ty_arrow].
      * exact (proj2 H_e.(B.proj2_sig)).
    + pose proof (wnNf_wnStep_typNf Gamma v' ty v_wnNf) as H_e.
      exists H_e.(B.proj1_sig). split.
      * eapply wnStep_alpha; [exact (proj1 H_e.(B.proj2_sig)) | exact ALPHA].
      * exact (proj2 H_e.(B.proj2_sig)).
Defined.

Corollary Normalisation_by_Evaluation (Gamma : ctx L) (M : trm L) (ty : typ L)
  (TYPING : Gamma ⊢ M ⦂ ty)
  : B.sig (trm L) (fun e => wnStep Gamma (subst_trm nil_subst M) e ty /\ typNf Gamma e ty).
Proof.
  exact (wnNf_wnStep_typNf Gamma (subst_trm nil_subst M) ty (reify Gamma ty (subst_trm nil_subst M) (semanticTyping_sound Gamma M ty TYPING Gamma nil_subst eval_ctx_nil_subst))).
Defined.

Definition NbE {Gamma} {ty} (M : trm L) (TYPING : Typing Gamma M ty) : trm L :=
  (Normalisation_by_Evaluation Gamma M ty TYPING).(B.proj1_sig).

Lemma NbE_wnStep (Gamma : ctx L) (M : trm L) (ty : typ L)
  (TYPING : Gamma ⊢ M ⦂ ty)
  : Gamma ⊢ M ~~> NbE M TYPING ⦂ ty.
Proof.
  eapply wnStep_alpha.
  - exact (proj1 (Normalisation_by_Evaluation Gamma M ty TYPING).(B.proj2_sig)).
  - red. rewrite <- subst_compose_spec. eapply equiv_subst_implies_subst_same. ii. reflexivity.
Qed.

Lemma NbE_typNf (Gamma : ctx L) (M : trm L) (ty : typ L)
  (TYPING : Gamma ⊢ M ⦂ ty)
  : typNf Gamma (NbE M TYPING) ty.
Proof.
  exact (proj2 (Normalisation_by_Evaluation Gamma M ty TYPING).(B.proj2_sig)).
Qed.

Lemma NbE_preservesTyping (Gamma : ctx L) (M : trm L) (ty : typ L)
  (TYPING : Gamma ⊢ M ⦂ ty)
  : Gamma ⊢ NbE M TYPING ⦂ ty.
Proof.
  eapply Typing_retraction. eapply typNf_Typing. eapply NbE_typNf.
Qed.

End WEAK_NORMALISATION.

Section STLC_SN.

#[local] Opaque chi.

#[local] Notation bty := (bty _).
#[local] Infix "≡ₐ" := alpha_equiv : type_scope.
#[local] Infix "~>β₁" := fullBetaOnce : type_scope.
#[local] Infix "~>β*" := fullBetaMany : type_scope.
#[local] Notation "Gamma ⊢ e ⦂ ty" := (Typing Gamma e ty).

Inductive jmSN : trm L -> Prop :=
  | jmSN_ne M
    (NE : jmSNe M)
    : jmSN M
  | jmSN_lam x ty M
    (BODY : jmSN M)
    : jmSN (Lam_trm x ty M)
  | jmSN_exp M N
    (STEP : jmStep M N)
    (N_SN : jmSN N)
    : jmSN M
with jmSNe : trm L -> Prop :=
  | jmSNe_var x
    : jmSNe (Var_trm x)
  | jmSNe_con c
    : jmSNe (Con_trm c)
  | jmSNe_app M N
    (M_NE : jmSNe M)
    (N_SN : jmSN N)
    : jmSNe (App_trm M N)
with jmStep : trm L -> trm L -> Prop :=
  | jmStep_beta x ty M N Q
    (N_SN : jmSN N)
    (ALPHA : subst_trm (one_subst x N) M ≡ₐ Q)
    : jmStep (App_trm (Lam_trm x ty M) N) Q
  | jmStep_appl M M' N
    (STEP : jmStep M M')
    : jmStep (App_trm M N) (App_trm M' N).

Fixpoint jmRed (ty : typ L) : trm L -> Prop :=
  match ty with
  | bty b => jmSN
  | (ty1 -> ty2)%typ => fun M => jmSN M /\ forall N, jmRed ty1 N -> jmRed ty2 (App_trm M N)
  end.

Fixpoint jmRed_jmSN (ty : typ L) {struct ty} : forall M, jmRed ty M -> jmSN M.
Proof.
  destruct ty as [b | ty1 ty2]; simpl; intros M H.
  - exact H.
  - exact (proj1 H).
Defined.

Fixpoint jmRed_ne (ty : typ L) : forall M, jmSNe M -> jmRed ty M.
Proof.
  destruct ty as [b | ty1 ty2]; simpl; intros M NE.
  - eapply jmSN_ne. exact NE.
  - split.
    + eapply jmSN_ne. exact NE.
    + intros N HN. eapply jmRed_ne.
      eapply jmSNe_app.
      * exact NE.
      * eapply jmRed_jmSN. exact HN.
Defined.

Fixpoint jmRed_exp (ty : typ L) {struct ty}
  : forall M, forall N, jmStep M N -> jmRed ty N -> jmRed ty M.
Proof.
  destruct ty as [b | ty1 ty2]; simpl; intros M N STEP HN.
  - eapply jmSN_exp; eassumption.
  - split.
    + eapply jmSN_exp.
      * exact STEP.
      * exact (proj1 HN).
    + intros P HP. eapply jmRed_exp.
      * eapply jmStep_appl. exact STEP.
      * exact (proj2 HN P HP).
Defined.

Definition jmRedSubst (Gamma : ctx L) (gamma : subst L) : Prop :=
  forall x, forall ty, Lookup x ty Gamma -> jmRed ty (gamma x).

Lemma jmRedSubst_cons Gamma gamma x ty N
  (N_RED : jmRed ty N)
  (GAMMA_RED : jmRedSubst Gamma gamma)
  : jmRedSubst ((x, ty) :: Gamma) (cons_subst x N gamma).
Proof.
  intros y ty'. unfold cons_subst. eapply Lookup_cons.
  - intros y_eq ty_eq. subst y ty'. destruct (eq_dec x x) as [_ | NE].
    + exact N_RED.
    + contradiction.
  - intros y_ne LOOKUP. destruct (eq_dec y x) as [EQ | NE].
    + subst y. rewrite -> Name.ne_iff in y_ne. contradiction.
    + eapply GAMMA_RED. exact LOOKUP.
Defined.

Lemma jmRedSubst_nil Gamma
  : jmRedSubst Gamma nil_subst.
Proof.
  intros x ty LOOKUP. eapply jmRed_ne. eapply jmSNe_var.
Defined.

Theorem Typing_implies_jmRed Gamma e ty
  (TYPING : Gamma ⊢ e ⦂ ty)
  : forall gamma, jmRedSubst Gamma gamma -> jmRed ty (subst_trm gamma e).
Proof.
  induction TYPING; simpl; intros gamma GAMMA_RED.
  - eapply GAMMA_RED. exact LOOKUP.
  - eapply IHTYPING1.
    { exact GAMMA_RED. }
    eapply IHTYPING2. exact GAMMA_RED.
  - set (z := chi gamma (Lam_trm y ty1 e1)).
    split.
    + eapply jmSN_lam. eapply jmRed_jmSN.
      eapply IHTYPING. eapply jmRedSubst_cons.
      * eapply jmRed_ne. eapply jmSNe_var.
      * exact GAMMA_RED.
    + intros N N_RED. eapply jmRed_exp.
      * eapply jmStep_beta.
        { eapply jmRed_jmSN. exact N_RED. }
        { red. eapply subst_cons_lemma_aux1 with (ty := ty1). reflexivity. }
      * eapply IHTYPING. eapply jmRedSubst_cons.
        { exact N_RED. }
        { exact GAMMA_RED. }
  - eapply jmRed_ne. eapply jmSNe_con.
Defined.

Lemma alpha_equiv_lam_rename x ty M z
  (NOT_FREE : is_free_in z (Lam_trm x ty M) = false)
  : Lam_trm x ty M ≡ₐ Lam_trm z ty (subst_trm (one_subst x (Var_trm z)) M).
Proof.
  red. simpl.
  set (w := chi nil_subst (Lam_trm x ty M)).
  enough (H_chi : chi nil_subst (Lam_trm z ty (subst_trm (one_subst x (Var_trm z)) M)) = w).
  { rewrite H_chi. unfold w. f_equal.
    rewrite <- subst_compose_spec.
    eapply equiv_subst_implies_subst_same. intros u FREE_u.
    unfold subst_compose, one_subst, cons_subst, nil_subst.
    destruct (eq_dec u x) as [u_eq_x | u_ne_x].
    - subst u. simpl. destruct (eq_dec z z) as [_ | z_ne_z].
      + reflexivity.
      + contradiction.
    - destruct (eq_dec u z) as [u_eq_z | u_ne_z].
      + subst u. exfalso. simpl in NOT_FREE.
        rewrite andb_false_iff in NOT_FREE. destruct NOT_FREE as [NOT_FREE | NOT_FREE].
        * rewrite negb_false_iff in NOT_FREE. rewrite eqb_spec in NOT_FREE.
          contradiction.
        * rewrite <- not_true_iff_false in NOT_FREE. eapply NOT_FREE. exact FREE_u.
      + simpl. destruct (eq_dec u z) as [u_eq_z | u_ne_z']; [contradiction | reflexivity].
  }
  subst w. eapply chi_frm_ext. intros u.
  unfold free_in_wrt, nil_subst. split.
  - intros (v & FREE_v & FREE_u). simpl in FREE_u.
    rewrite eqb_spec in FREE_u. subst u. exists v. split; [| simpl; rewrite eqb_spec; reflexivity].
    simpl in FREE_v. rewrite andb_true_iff in FREE_v.
    destruct FREE_v as [v_ne_x FREE_v].
    simpl. rewrite andb_true_iff. split.
    + rewrite negb_true_iff. rewrite eqb_spec. intros v_eq_z.
      subst v. rewrite <- free_in_wrt_iff in FREE_v.
      destruct FREE_v as (u & FREE_u & FREE_v).
      unfold one_subst, cons_subst, nil_subst in FREE_v.
      destruct (eq_dec u x) as [u_eq_x | u_ne_x].
      * subst u. simpl in FREE_v. rewrite eqb_spec in FREE_v.
        rewrite negb_true_iff in v_ne_x. rewrite eqb_spec in v_ne_x.
        contradiction.
      * simpl in FREE_v. rewrite eqb_spec in FREE_v. subst u.
        contradiction.
    + rewrite <- free_in_wrt_iff in FREE_v.
      destruct FREE_v as (u & FREE_u & FREE_v).
      unfold one_subst, cons_subst, nil_subst in FREE_v.
      destruct (eq_dec u x) as [u_eq_x | u_ne_x].
      * subst u. simpl in FREE_v. rewrite eqb_spec in FREE_v. subst v.
        rewrite negb_true_iff in v_ne_x. rewrite eqb_spec in v_ne_x.
        contradiction.
      * simpl in FREE_v. rewrite eqb_spec in FREE_v. subst v. exact FREE_u.
  - intros (v & FREE_v & FREE_u). simpl in FREE_u.
    rewrite eqb_spec in FREE_u. subst u.
    simpl in FREE_v. rewrite andb_true_iff in FREE_v.
    destruct FREE_v as [v_ne_z FREE_v].
    exists v. split; [| simpl; rewrite eqb_spec; reflexivity].
    simpl. rewrite andb_true_iff. split.
    + rewrite negb_true_iff. rewrite eqb_spec. intros v_eq_z.
      subst v. simpl in NOT_FREE. rewrite andb_false_iff in NOT_FREE.
      destruct NOT_FREE as [NOT_FREE | NOT_FREE].
      * rewrite negb_false_iff in NOT_FREE. rewrite eqb_spec in NOT_FREE.
        rewrite negb_true_iff in v_ne_z. rewrite eqb_spec in v_ne_z.
        contradiction.
      * rewrite <- not_true_iff_false in NOT_FREE. eapply NOT_FREE.
        exact FREE_v.
    + rewrite <- free_in_wrt_iff. exists v. split.
      * exact FREE_v.
      * unfold one_subst, cons_subst, nil_subst.
        destruct (eq_dec v x) as [v_eq_x | v_ne_x].
        { subst v. rewrite negb_true_iff in v_ne_z. rewrite eqb_spec in v_ne_z. contradiction. }
        { simpl. rewrite eqb_spec. reflexivity. }
Qed.

Lemma fullBetaOnce_is_free_in M N z
  (BETA : M ~>β₁ N)
  (FREE : is_free_in z N = true)
  : is_free_in z M = true.
Proof.
  induction BETA; simpl in *.
  - rewrite <- free_in_wrt_iff in FREE.
    destruct FREE as (y & FREE_M & FREE_s).
    unfold one_subst, cons_subst, nil_subst in FREE_s.
    destruct (eq_dec y x) as [y_eq_x | y_ne_x].
    + subst y. rewrite orb_true_iff. right. exact FREE_s.
    + simpl in FREE_s. rewrite eqb_spec in FREE_s. subst z.
      rewrite orb_true_iff. left. rewrite andb_true_iff. split.
      * rewrite negb_true_iff. rewrite eqb_spec. intros z_eq_x.
        contradiction y_ne_x.
      * exact FREE_M.
  - rewrite orb_true_iff in FREE |- *. destruct FREE as [FREE | FREE].
    + left. eapply IHBETA. exact FREE.
    + right. exact FREE.
  - rewrite orb_true_iff in FREE |- *. destruct FREE as [FREE | FREE].
    + left. exact FREE.
    + right. eapply IHBETA. exact FREE.
  - rewrite andb_true_iff in FREE |- *. destruct FREE as [FREE1 FREE2].
    split.
    + exact FREE1.
    + eapply IHBETA. exact FREE2.
  - eapply IHBETA.
    rewrite alpha_equiv_is_free_in with (M := N) (M' := N'); eassumption.
Qed.

Lemma fullBetaOnce_preserves_is_fresh_in_subst s M N z
  (BETA : M ~>β₁ N)
  (FRESH : is_fresh_in_subst z s M = true)
  : is_fresh_in_subst z s N = true.
Proof.
  unfold is_fresh_in_subst in *. rewrite forallb_forall in FRESH |- *.
  intros x x_in. eapply FRESH.
  rewrite <- is_free_in_iff in x_in. rewrite <- is_free_in_iff.
  eapply fullBetaOnce_is_free_in; eassumption.
Qed.

Lemma alpha_equiv_subst_lam_fresh s x ty M z
  (FRESH : is_fresh_in_subst z s (Lam_trm x ty M) = true)
  : subst_trm s (Lam_trm x ty M) ≡ₐ Lam_trm z ty (subst_trm (cons_subst x (Var_trm z) s) M).
Proof.
  simpl. set (w := chi s (Lam_trm x ty M)).
  transitivity (Lam_trm z ty (subst_trm (one_subst w (Var_trm z)) (subst_trm (cons_subst x (Var_trm w) s) M))).
  - eapply alpha_equiv_lam_rename.
    change (is_free_in z (subst_trm s (Lam_trm x ty M)) = false).
    rewrite <- is_fresh_in_subst_iff. exact FRESH.
  - eapply alpha_equiv_Lam_same. red.
    unfold w. eapply subst_cons_lemma_aux1 with (ty := ty). reflexivity.
Qed.

#[local] Reserved Infix "~>β₀" (at level 70).

#[local] Reserved Infix "~>β₀*" (at level 70).

Inductive rawBetaOnce : trm L -> trm L -> Prop :=
  | rawBetaOnce_beta x ty M N
    : App_trm (Lam_trm x ty M) N ~>β₀ subst_trm (one_subst x N) M
  | rawBetaOnce_appl M M' N
    (BETA : M ~>β₀ M')
    : App_trm M N ~>β₀ App_trm M' N
  | rawBetaOnce_appr M N N'
    (BETA : N ~>β₀ N')
    : App_trm M N ~>β₀ App_trm M N'
  | rawBetaOnce_lam x ty M M'
    (BETA : M ~>β₀ M')
    : Lam_trm x ty M ~>β₀ Lam_trm x ty M'
  where "M ~>β₀ N" := (rawBetaOnce M N).

Inductive rawBetaMany (M : trm L) (N : trm L) : Prop :=
  | rawBetaMany_alpha
    (ALPHA : M ≡ₐ N)
    : M ~>β₀* N
  | rawBetaMany_beta
    (STEP : M ~>β₀ N)
    : M ~>β₀* N
  | rawBetaMany_trans M'
    (STEPS1 : M ~>β₀* M')
    (STEPS2 : M' ~>β₀* N)
    : M ~>β₀* N
  where "M ~>β₀* N" := (rawBetaMany M N).

Inductive raw_sn (M : trm L) : Prop :=
  | raw_sn_intro
    (raw_sn_inv : forall N, M ~>β₀ N -> raw_sn N).

Definition raw_sn_inv {M : trm L} (H_sn : raw_sn M) : forall N, M ~>β₀ N -> raw_sn N :=
  match H_sn with
  | @raw_sn_intro _ raw_sn_inv => raw_sn_inv
  end.

Lemma rawBetaOnce_fullBetaOnce M N
  (BETA : M ~>β₀ N)
  : M ~>β₁ N.
Proof.
  induction BETA; eauto using fullBetaOnce.
Qed.

Lemma fullBetaOnce_rawBetaOnce M N
  (BETA : M ~>β₁ N)
  : exists P, M ~>β₀ P /\ P ≡ₐ N.
Proof.
  induction BETA.
  - exists (subst_trm (one_subst x N) M). split; [econs 1 | reflexivity].
  - destruct IHBETA as (P & STEP & ALPHA).
    exists (App_trm P N). split; [econs 2; exact STEP | ].
    eapply alpha_equiv_App; [exact ALPHA | reflexivity].
  - destruct IHBETA as (P & STEP & ALPHA).
    exists (App_trm M P). split; [econs 3; exact STEP | ].
    eapply alpha_equiv_App; [reflexivity | exact ALPHA].
  - destruct IHBETA as (P & STEP & ALPHA).
    exists (Lam_trm x ty P). split; [econs 4; exact STEP | ].
    eapply alpha_equiv_Lam_same. exact ALPHA.
  - destruct IHBETA as (P & STEP & ALPHA').
    exists P. split; [exact STEP | ].
    transitivity N; eassumption.
Qed.

Lemma rawBetaOnce_preserves_is_fresh_in_subst s M N z
  (BETA : M ~>β₀ N)
  (FRESH : is_fresh_in_subst z s M = true)
  : is_fresh_in_subst z s N = true.
Proof.
  eapply fullBetaOnce_preserves_is_fresh_in_subst.
  - eapply rawBetaOnce_fullBetaOnce. exact BETA.
  - exact FRESH.
Qed.

Lemma rawBetaOnce_subst_compat s M N
  (BETA : M ~>β₀ N)
  : exists P, subst_trm s M ~>β₀ P /\ P ≡ₐ subst_trm s N.
Proof.
  revert s. induction BETA; intros s; simpl.
  - set (z := chi s (Lam_trm x ty M)).
    exists (subst_trm (one_subst z (subst_trm s N)) (subst_trm (cons_subst x (Var_trm z) s) M)).
    split.
    + econs 1.
    + transitivity (subst_trm (cons_subst x (subst_trm s N) s) M).
      * red. unfold z. eapply subst_cons_lemma_aux1 with (ty := ty). reflexivity.
      * eapply alpha_equiv_subst_cons_compose.
  - pose proof (IHBETA s) as (P & STEP & ALPHA).
    exists (App_trm P (subst_trm s N)). split.
    + econs 2. exact STEP.
    + eapply alpha_equiv_App; [exact ALPHA | reflexivity].
  - pose proof (IHBETA s) as (P & STEP & ALPHA).
    exists (App_trm (subst_trm s M) P). split.
    + econs 3. exact STEP.
    + eapply alpha_equiv_App; [reflexivity | exact ALPHA].
  - set (z := chi s (Lam_trm x ty M)).
    destruct IHBETA with (s := cons_subst x (Var_trm z) s) as (P & STEP & ALPHA).
    exists (Lam_trm z ty P). split.
    + econs 4. exact STEP.
    + transitivity (Lam_trm z ty (subst_trm (cons_subst x (Var_trm z) s) M')).
      * eapply alpha_equiv_Lam_same. exact ALPHA.
      * symmetry. eapply alpha_equiv_subst_lam_fresh.
        unfold z. eapply rawBetaOnce_preserves_is_fresh_in_subst.
        { econs 4. exact BETA. }
        { eapply chi_is_fresh_in_subst. }
Qed.

Lemma alpha_equiv_one_subst_self x M
  : subst_trm (one_subst x (Var_trm x)) M ≡ₐ M.
Proof.
  transitivity (subst_trm nil_subst M).
  - eapply alpha_equiv_subst_ext. intros z FREE.
    unfold one_subst, cons_subst, nil_subst.
    destruct (eq_dec z x) as [z_eq_x | z_ne_x]; subst; reflexivity.
  - symmetry. eapply alpha_equiv_nil_subst.
Qed.

Lemma alpha_equiv_Lam_inv_body_left x y ty M N
  (ALPHA : Lam_trm x ty M ≡ₐ Lam_trm y ty N)
  : M ≡ₐ subst_trm (one_subst y (Var_trm x)) N.
Proof.
  transitivity (subst_trm (one_subst x (Var_trm x)) M).
  - symmetry. eapply alpha_equiv_one_subst_self.
  - eapply alpha_equiv_beta_contract.
    + exact ALPHA.
    + reflexivity.
Qed.

Lemma alpha_rawBetaOnce_comm M
  : forall N, forall P, M ≡ₐ N -> N ~>β₀ P -> exists Q, M ~>β₀ Q /\ Q ≡ₐ P.
Proof.
  induction M as [x | M1 IH1 M2 IH2 | x ty M IH | c]; intros N P ALPHA BETA.
  - pose proof (alpha_equiv_Var_inv x N ALPHA) as N_eq.
    subst N. inversion BETA.
  - pose proof (alpha_equiv_App_inv M1 M2 N ALPHA) as (N1 & N2 & N_eq & ALPHA1 & ALPHA2).
    subst N. inversion BETA; subst.
    + assert (ALPHA1' : Lam_trm x ty M ≡ₐ M1) by (symmetry; exact ALPHA1).
      pose proof (alpha_equiv_Lam_inv x ty M M1 ALPHA1') as (x' & M' & z & M1_eq & BODY_ALPHA).
      subst M1. exists (subst_trm (one_subst x' M2) M'). split.
      * econs 1.
      * assert (ALPHA_ARG : N2 ≡ₐ M2) by (symmetry; exact ALPHA2).
        symmetry. exact (alpha_equiv_beta_contract x x' ty M M' N2 M2 ALPHA1' ALPHA_ARG).
    + pose proof (IH1 N1 M' ALPHA1 BETA0) as (Q & STEP & ALPHA_Q).
      exists (App_trm Q M2). split.
      * econs 2. exact STEP.
      * eapply alpha_equiv_App; [exact ALPHA_Q | exact ALPHA2].
    + pose proof (IH2 N2 N' ALPHA2 BETA0) as (Q & STEP & ALPHA_Q).
      exists (App_trm M1 Q). split.
      * econs 3. exact STEP.
      * eapply alpha_equiv_App; [exact ALPHA1 | exact ALPHA_Q].
  - pose proof (alpha_equiv_Lam_inv x ty M N ALPHA) as (y & N' & z & N_eq & BODY_ALPHA).
    subst N. inversion BETA; subst.
    pose proof (rawBetaOnce_subst_compat (one_subst y (Var_trm x)) _ _ BETA0) as (R & STEP & ALPHA_R).
    pose proof (alpha_equiv_Lam_inv_body_left x y ty M N' ALPHA) as BODY_ALPHA'.
    pose proof (IH _ _ BODY_ALPHA' STEP) as (Q & STEP_Q & ALPHA_Q).
    exists (Lam_trm x ty Q). split.
    + econs 4. exact STEP_Q.
    + transitivity (Lam_trm x ty R).
      { eapply alpha_equiv_Lam_same. exact ALPHA_Q. }
      transitivity (Lam_trm x ty (subst_trm (one_subst y (Var_trm x)) M')).
      { eapply alpha_equiv_Lam_same. exact ALPHA_R. }
      assert (NOT_FREE_SOURCE : is_free_in x (Lam_trm x ty M) = false).
      { simpl. unfold eqb. destruct (eq_dec x x) as [_ | NE].
        - reflexivity.
        - contradiction.
      }
      assert (NOT_FREE_N : is_free_in x (Lam_trm y ty N') = false).
      { rewrite <- alpha_equiv_is_free_in with (M := Lam_trm x ty M) (M' := Lam_trm y ty N'); eassumption. }
      symmetry. eapply alpha_equiv_lam_rename.
      destruct (is_free_in x (Lam_trm y ty M')) eqn: FREE; [ | reflexivity].
      pose proof (fullBetaOnce_is_free_in _ _ x (rawBetaOnce_fullBetaOnce _ _ (rawBetaOnce_lam y ty N' M' BETA0)) FREE) as FREE_N.
      congruence.
  - pose proof (alpha_equiv_Con_inv c N ALPHA) as N_eq.
    subst N. inversion BETA.
Qed.

Fixpoint raw_sn_alpha (M : trm L) (M_SN : raw_sn M) {struct M_SN} : forall N, M ≡ₐ N -> raw_sn N.
Proof.
  destruct M_SN as [M_SN]. intros N ALPHA. econs. intros P BETA.
  pose proof (alpha_rawBetaOnce_comm M N P ALPHA BETA) as (Q & STEP & ALPHA_Q).
  eapply raw_sn_alpha.
  - eapply M_SN. exact STEP.
  - exact ALPHA_Q.
Defined.

Lemma rawBetaMany_preserves_raw_sn M N
  (STEPS : M ~>β₀* N)
  (M_SN : raw_sn M)
  : raw_sn N.
Proof.
  induction STEPS.
  - eapply raw_sn_alpha; eassumption.
  - eapply raw_sn_inv; eassumption.
  - eapply IHSTEPS2. eapply IHSTEPS1. exact M_SN.
Qed.

Lemma rawBetaMany_app_l M M' N
  (STEPS : M ~>β₀* M')
  : App_trm M N ~>β₀* App_trm M' N.
Proof.
  induction STEPS.
  - econs 1. eapply alpha_equiv_App; [exact ALPHA | reflexivity].
  - econs 2. econs 2. exact STEP.
  - econs 3; eassumption.
Qed.

Lemma rawBetaMany_app_r M N N'
  (STEPS : N ~>β₀* N')
  : App_trm M N ~>β₀* App_trm M N'.
Proof.
  induction STEPS.
  - econs 1. eapply alpha_equiv_App; [reflexivity | exact ALPHA].
  - econs 2. econs 3. exact STEP.
  - econs 3; eassumption.
Qed.

Lemma rawBetaMany_lam x ty M M'
  (STEPS : M ~>β₀* M')
  : Lam_trm x ty M ~>β₀* Lam_trm x ty M'.
Proof.
  induction STEPS.
  - econs 1. eapply alpha_equiv_Lam_same. exact ALPHA.
  - econs 2. econs 4. exact STEP.
  - econs 3; eassumption.
Qed.

Lemma alpha_equiv_subst_shadow x A gamma M
  : subst_trm (cons_subst x A (cons_subst x A gamma)) M ≡ₐ subst_trm (cons_subst x A gamma) M.
Proof.
  eapply alpha_equiv_subst_ext. intros z FREE.
  unfold cons_subst. destruct (eq_dec z x); reflexivity.
Qed.

Lemma alpha_equiv_subst_swap x y A B gamma M
  (NE : y ≠ x)
  : subst_trm (cons_subst y B (cons_subst x A gamma)) M ≡ₐ subst_trm (cons_subst x A (cons_subst y B gamma)) M.
Proof.
  eapply alpha_equiv_subst_ext. intros z FREE.
  unfold cons_subst.
  destruct (eq_dec z y) as [z_eq_y | z_ne_y].
  - subst z. destruct (eq_dec y x) as [y_eq_x | y_ne_x].
    + rewrite Name.ne_iff in NE. contradiction.
    + reflexivity.
  - destruct (eq_dec z x) as [z_eq_x | z_ne_x].
    + reflexivity.
    + destruct (eq_dec z y) as [z_eq_y | z_ne_y']; [contradiction | reflexivity].
Qed.

Lemma rawBetaOnce_preserves_is_fresh_in_subst_update gamma x N N' z M
  (BETA : N ~>β₀ N')
  (FRESH : is_fresh_in_subst z (cons_subst x N gamma) M = true)
  : is_fresh_in_subst z (cons_subst x N' gamma) M = true.
Proof.
  unfold is_fresh_in_subst in *. rewrite forallb_forall in FRESH |- *. intros y y_in.
  pose proof (FRESH y y_in) as H. unfold "∘" in H |- *. unfold cons_subst in H |- *.
  destruct (eq_dec y x) as [y_eq_x | y_ne_x]; [rewrite negb_true_iff in H |- * | exact H].
  destruct (is_free_in z N') eqn: FREE; [ | trivial].
  enough (is_free_in z N = true) by congruence.
  exact (fullBetaOnce_is_free_in _ _ z (rawBetaOnce_fullBetaOnce _ _ BETA) FREE).
Qed.

Lemma rawBetaMany_subst_update gamma x N N' M
  (BETA : N ~>β₀ N')
  : subst_trm (cons_subst x N gamma) M ~>β₀* subst_trm (cons_subst x N' gamma) M.
Proof.
  revert gamma x N N' BETA. induction M; intros gamma x0 N N' BETA; simpl.
  - unfold cons_subst. destruct (eq_dec x x0) as [x_eq | x_ne].
    + subst x. econs 2. exact BETA.
    + econs 1. reflexivity.
  - eapply rawBetaMany_trans with (M' := App_trm (subst_trm (cons_subst x0 N' gamma) M1) (subst_trm (cons_subst x0 N gamma) M2)).
    + eapply rawBetaMany_app_l. eapply IHM1. exact BETA.
    + eapply rawBetaMany_app_r. eapply IHM2. exact BETA.
  - set (s := cons_subst x0 N gamma).
    set (s' := cons_subst x0 N' gamma).
    set (z := chi s (Lam_trm y ty M)).
    eapply rawBetaMany_trans with (M' := Lam_trm z ty (subst_trm (cons_subst y (Var_trm z) s') M)).
    + eapply rawBetaMany_lam.
      destruct (eq_dec y x0) as [y_eq_x | y_ne_x].
      * subst y. econs 1.
        unfold s, s'. eapply alpha_equiv_subst_ext. intros u FREE.
        unfold cons_subst. destruct (eq_dec u x0); reflexivity.
      * eapply rawBetaMany_trans with (M' := subst_trm (cons_subst x0 N (cons_subst y (Var_trm z) gamma)) M).
        { econs 1. unfold s. eapply alpha_equiv_subst_swap. rewrite Name.ne_iff. exact y_ne_x. }
        eapply rawBetaMany_trans with (M' := subst_trm (cons_subst x0 N' (cons_subst y (Var_trm z) gamma)) M).
        { eapply IHM. exact BETA. }
        { econs 1. symmetry. unfold s'. eapply alpha_equiv_subst_swap. rewrite Name.ne_iff. exact y_ne_x. }
    + econs 1. symmetry. eapply alpha_equiv_subst_lam_fresh.
      unfold z, s, s'. eapply rawBetaOnce_preserves_is_fresh_in_subst_update.
      * exact BETA.
      * eapply chi_is_fresh_in_subst.
  - econs 1. reflexivity.
Qed.

Lemma rawBetaMany_one_subst_arg x M N N'
  (BETA : N ~>β₀ N')
  : subst_trm (one_subst x N) M ~>β₀* subst_trm (one_subst x N') M.
Proof.
  unfold one_subst. eapply rawBetaMany_subst_update. exact BETA.
Qed.

Inductive neutral : trm L -> Prop :=
  | neutral_var x
    : neutral (Var_trm x)
  | neutral_con c
    : neutral (Con_trm c)
  | neutral_app M N
    (NE : neutral M)
    : neutral (App_trm M N).

Lemma neutral_not_lam M x ty N
  (NE : neutral M)
  (EQ : M = Lam_trm x ty N)
  : False.
Proof.
  revert EQ; induction NE; intros EQ; inv EQ.
Qed.

Lemma neutral_rawBetaOnce M N
  (NE : neutral M)
  (BETA : M ~>β₀ N)
  : neutral N.
Proof.
  revert N BETA. induction NE; intros P BETA; inversion BETA; subst; eauto using neutral.
  contradiction (neutral_not_lam _ _ _ _ NE eq_refl).
Qed.

Lemma raw_sn_var x
  : raw_sn (Var_trm x).
Proof.
  econs. intros N BETA. inversion BETA.
Qed.

Lemma raw_sn_con c
  : raw_sn (Con_trm c).
Proof.
  econs. intros N BETA. inversion BETA.
Qed.

Fixpoint raw_sn_lam (M : trm L) (M_SN : raw_sn M) {struct M_SN} : forall x, forall ty, raw_sn (Lam_trm x ty M).
Proof.
  destruct M_SN as [M_SN]. econs. intros N BETA.
  inversion BETA; subst. eapply raw_sn_lam. eapply M_SN. exact BETA0.
Defined.

Lemma raw_sn_app_neutral M N
  (NE : neutral M)
  (M_SN : raw_sn M)
  (N_SN : raw_sn N)
  : raw_sn (App_trm M N).
Proof.
  revert N NE N_SN. induction M_SN as [M M_SN IHM]; intros N NE N_SN.
  induction N_SN as [N N_SN IHN]. econs. intros P BETA.
  inversion BETA; subst.
  - contradiction (neutral_not_lam _ _ _ _ NE eq_refl).
  - eapply IHM.
    + exact BETA0.
    + eapply neutral_rawBetaOnce; eassumption.
    + econs. exact N_SN.
  - eapply IHN. exact BETA0.
Qed.

Lemma raw_wkh_exp_alpha x ty M N Q
  (N_SN : raw_sn N)
  (Q_SN : raw_sn Q)
  (ALPHA : Q ≡ₐ subst_trm (one_subst x N) M)
  : raw_sn (App_trm (Lam_trm x ty M) N).
Proof.
  revert M Q Q_SN ALPHA. induction N_SN as [N N_SN IHN].
  intros M Q Q_SN ALPHA.
  revert M ALPHA. induction Q_SN as [Q Q_SN IHQ].
  intros M ALPHA. econs. intros P BETA. inversion BETA; subst.
  - eapply raw_sn_alpha.
    + econs. exact Q_SN.
    + exact ALPHA.
  - inversion BETA0; subst.
    pose proof (rawBetaOnce_subst_compat (one_subst x N) _ _ BETA1) as (R & STEP_R & ALPHA_R).
    pose proof (alpha_rawBetaOnce_comm Q (subst_trm (one_subst x N) M) R ALPHA STEP_R) as (S & STEP_S & ALPHA_S).
    eapply IHQ.
    + exact STEP_S.
    + transitivity R; [exact ALPHA_S | exact ALPHA_R].
  - eapply IHN.
    + exact BETA0.
    + eapply rawBetaMany_preserves_raw_sn.
      * eapply rawBetaMany_one_subst_arg. exact BETA0.
      * eapply raw_sn_alpha.
        { econs. exact Q_SN. }
        { exact ALPHA. }
    + reflexivity.
Qed.

Lemma raw_wkh_exp x ty M N
  (N_SN : raw_sn N)
  (BODY_SN : raw_sn (subst_trm (one_subst x N) M))
  : raw_sn (App_trm (Lam_trm x ty M) N).
Proof.
  eapply raw_wkh_exp_alpha; [exact N_SN | exact BODY_SN | reflexivity].
Qed.

Inductive rawHeadStep : trm L -> trm L -> Prop :=
  | rawHeadStep_beta x ty M N Q
    (N_SN : raw_sn N)
    (ALPHA : Q ≡ₐ subst_trm (one_subst x N) M)
    : rawHeadStep (App_trm (Lam_trm x ty M) N) Q
  | rawHeadStep_appl M M' N
    (STEP : rawHeadStep M M')
    : rawHeadStep (App_trm M N) (App_trm M' N).

Lemma rawHeadStep_not_lam M N x ty P
  (STEP : rawHeadStep M N)
  (EQ : M = Lam_trm x ty P)
  : False.
Proof.
  revert EQ; induction STEP; intros EQ; inv EQ.
Qed.

Lemma rawHead_confluence M N P
  (STEP : rawHeadStep M N)
  (BETA : M ~>β₀ P)
  : N ≡ₐ P \/ (exists Q, rawHeadStep P Q /\ N ~>β₀* Q).
Proof.
  revert P BETA. induction STEP; intros P BETA; inversion BETA; subst.
  - left. exact ALPHA.
  - inversion BETA0; subst.
    pose proof (rawBetaOnce_subst_compat (one_subst x N) _ _ BETA1) as (R & STEP_R & ALPHA_R).
    right. exists (subst_trm (one_subst x N) M'0). split.
    + econs 1; [exact N_SN | reflexivity].
    + eapply rawBetaMany_trans with (M' := subst_trm (one_subst x N) M).
      * econs 1. exact ALPHA.
      * eapply rawBetaMany_trans with (M' := R).
        { econs 2. exact STEP_R. }
        { econs 1. exact ALPHA_R. }
  - right. exists (subst_trm (one_subst x N') M). split.
    + econs 1.
      * eapply raw_sn_inv; eassumption.
      * reflexivity.
    + eapply rawBetaMany_trans with (M' := subst_trm (one_subst x N) M).
      * econs 1. exact ALPHA.
      * eapply rawBetaMany_one_subst_arg. exact BETA0.
  - contradiction (rawHeadStep_not_lam _ _ _ _ _ STEP eq_refl).
  - pose proof (IHSTEP M'0 BETA0) as [ALPHA_STEP | (Q & STEP_Q & MANY_Q)].
    + left. eapply alpha_equiv_App; [exact ALPHA_STEP | reflexivity].
    + right. exists (App_trm Q N). split.
      * econs 2. exact STEP_Q.
      * eapply rawBetaMany_app_l. exact MANY_Q.
  - right. exists (App_trm M' N'). split.
    + econs 2. exact STEP.
    + eapply rawBetaMany_app_r. econs 2. exact BETA0.
Qed.

Fixpoint raw_sn_app_inv M N (MN_SN : raw_sn (App_trm M N)) {struct MN_SN} : raw_sn M /\ raw_sn N.
Proof.
  destruct MN_SN as [MN_SN]. split.
  - econs. intros M' BETA. exact (proj1 (raw_sn_app_inv M' N (MN_SN (App_trm M' N) (rawBetaOnce_appl M M' N BETA)))).
  - econs. intros N' BETA. exact (proj2 (raw_sn_app_inv M N' (MN_SN (App_trm M N') (rawBetaOnce_appr M N N' BETA)))).
Defined.

Lemma rawHead_backward_aux M N M'
  (M_SN : raw_sn M)
  (N_SN : raw_sn N)
  (STEP : rawHeadStep M M')
  (M'N_SN : raw_sn (App_trm M' N))
  : raw_sn (App_trm M N).
Proof.
  revert N M' N_SN STEP M'N_SN.
  induction M_SN as [M M_SN IHM]; intros N M' N_SN STEP M'N_SN.
  revert M' STEP M'N_SN.
  induction N_SN as [N N_SN IHN]; intros M' STEP M'N_SN.
  econs. intros Q BETA. inversion BETA; subst.
  - contradiction (rawHeadStep_not_lam _ _ _ _ _ STEP eq_refl).
  - pose proof (rawHead_confluence M M' M'0 STEP BETA0) as [ALPHA_STEP | (P & STEP_P & MANY_P)].
    + eapply raw_sn_alpha.
      * exact M'N_SN.
      * eapply alpha_equiv_App; [exact ALPHA_STEP | reflexivity].
    + eapply IHM.
      * exact BETA0.
      * econs. exact N_SN.
      * exact STEP_P.
      * eapply rawBetaMany_preserves_raw_sn.
        { eapply rawBetaMany_app_l. exact MANY_P. }
        { exact M'N_SN. }
  - eapply IHN.
    + exact BETA0.
    + exact STEP.
    + eapply raw_sn_inv.
      * exact M'N_SN.
      * econs 3. exact BETA0.
Qed.

Lemma rawHead_backward M M'
  (STEP : rawHeadStep M M')
  (M'_SN : raw_sn M')
  : raw_sn M.
Proof.
  induction STEP.
  - eapply raw_wkh_exp_alpha; eassumption.
  - pose proof (raw_sn_app_inv M' N M'_SN) as (M'_HEAD_SN & N_SN).
    eapply rawHead_backward_aux; eauto.
Qed.

Fixpoint jmSNe_neutral (M : trm L) (NE : jmSNe M) {struct NE} : neutral M.
Proof.
  destruct NE.
  - econs 1.
  - econs 2.
  - econs 3. eapply jmSNe_neutral. exact NE.
Defined.

Fixpoint jmSN_raw_sn (M : trm L) (M_SN : jmSN M) {struct M_SN} : raw_sn M
with jmSNe_raw_sn (M : trm L) (M_NE : jmSNe M) {struct M_NE} : raw_sn M
with jmStep_rawHead (M : trm L) (N : trm L) (STEP : jmStep M N) {struct STEP} : rawHeadStep M N.
Proof.
  - destruct M_SN.
    + eapply jmSNe_raw_sn. exact NE.
    + eapply raw_sn_lam. eapply jmSN_raw_sn. exact M_SN.
    + eapply rawHead_backward.
      * eapply jmStep_rawHead. exact STEP.
      * eapply jmSN_raw_sn. exact M_SN.
  - destruct M_NE.
    + eapply raw_sn_var.
    + eapply raw_sn_con.
    + eapply raw_sn_app_neutral.
      * eapply jmSNe_neutral. exact M_NE.
      * eapply jmSNe_raw_sn. exact M_NE.
      * eapply jmSN_raw_sn. exact N_SN.
  - destruct STEP.
    + econs 1.
      * eapply jmSN_raw_sn. exact N_SN.
      * symmetry. exact ALPHA.
    + econs 2. eapply jmStep_rawHead. exact STEP.
Defined.

Fixpoint raw_sn_to_sn_alpha (M : trm L) (M_SN : raw_sn M) {struct M_SN} : forall N, M ≡ₐ N -> sn N.
Proof.
  destruct M_SN as [M_SN]. intros N ALPHA. econs. intros P BETA.
  pose proof (fullBetaOnce_rawBetaOnce N P BETA) as (R & STEP_R & ALPHA_R).
  pose proof (alpha_rawBetaOnce_comm M N R ALPHA STEP_R) as (Q & STEP_Q & ALPHA_Q).
  eapply raw_sn_to_sn_alpha.
  - eapply M_SN. exact STEP_Q.
  - transitivity R; eassumption.
Defined.

Definition raw_sn_to_sn (M : trm L) (M_SN : raw_sn M) : sn M :=
  raw_sn_to_sn_alpha M M_SN M eq_refl.

Theorem Typing_implies_StrongNormalisation {Gamma} {e} {ty}
  (TYPING : Gamma ⊢ e ⦂ ty)
  : sn e.
Proof.
  pose proof (Typing_implies_jmRed Gamma e ty TYPING nil_subst (jmRedSubst_nil Gamma)) as e_RED.
  pose proof (jmRed_jmSN ty _ e_RED) as e_JMSN.
  eapply raw_sn_to_sn_alpha.
  - eapply jmSN_raw_sn. exact e_JMSN.
  - symmetry. eapply alpha_equiv_nil_subst.
Qed.

End STLC_SN.

End STLC_META.

End ChurchStyleStlc1.
