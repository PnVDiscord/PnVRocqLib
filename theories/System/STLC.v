Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.System.P.
Require Import PnV.Data.Vector.
Require Import PnV.System.Lambda1.

Reserved Infix "~>β" (at level 70, no associativity).
Reserved Infix "~>η" (at level 70, no associativity).
Reserved Infix "~>β*" (at level 70, no associativity).
Reserved Infix "~>η*" (at level 70, no associativity).

Module ChurchStyleSTLC.

Export ChurchStyleStlc.

Notation "Gamma '∋' x '⦂' A" := (Lookup x A Gamma) : type_scope.
Notation "Gamma '⊢' M '=' N '⦂' A" := (equality Gamma M N A) : type_scope.

Section STLC_META.

Context {L : language}.

Fixpoint typ_height (ty : typ L) : nat :=
  match ty with
  | bty _ b => 0%nat
  | (ty1 -> ty2)%typ => 1 + max (typ_height ty1) (typ_height ty2)
  end.

Corollary subst_cons_lemma N M gamma x y (ty : typ L)
  (x_EQ : x = chi gamma (Lam_trm y ty M))
  : subst_trm (one_subst x N) (subst_trm (cons_subst y (Var_trm x) gamma) M) = subst_trm (cons_subst y N gamma) M.
Proof.
Admitted.

Context {Sigma : signature L}.

Lemma Typing_weakening {Gamma : ctx L} {Delta : ctx L} {e : trm L} {ty : typ L}
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

Let wp (A : Set) : Type :=
  A -> Prop.

Definition In {A : Set} (x : A) (X : wp A) : Prop :=
  X x.

#[local] Infix "\in" := In.

Definition subseteq {A : Set} (X : wp A) (X' : wp A) : Prop :=
  forall x, x \in X -> x \in X'.

#[local] Infix "\subseteq" := subseteq.

Inductive whBeta : trm L -> trm L -> Prop :=
  | whBeta_app_lam y ty M N
    : App_trm (Lam_trm y ty M) N ~>β subst_trm (one_subst y N) M
  | whBeta_ksi M M' N
    (WHBETA : M ~>β M')
    : App_trm M N ~>β App_trm M' N
  where "M ~>β N" := (whBeta M N).

Inductive whBetaStar (N : trm L) : trm L -> Prop :=
  | whBetaStar_O
    : N ~>β* N
  | whBetaStar_S M M'
    (WHBETA' : M' ~>β* N)
    (WHBETA : M ~>β M')
    : M ~>β* N
  where "M ~>β* N" := (whBetaStar N M).

Inductive whEta (M : trm L) : trm L -> Prop :=
  | whEta_intro x ty
    (FRESH : ~ L.In x (FVs M))
    : Lam_trm x ty (App_trm M (Var_trm x)) ~>η M
  where "M ~>η N" := (whEta N M).

Inductive wnNe (Gamma : ctx L) : typ L -> wp (trm L) :=
  | wnNe_Var x ty
    (LOOKUP : Gamma ∋ x ⦂ ty)
    : Var_trm x \in wnNe Gamma ty
  | wnNe_App u v ty ty'
    (u_wnNe : Gamma ⊢ u ⇉ (ty -> ty')%typ)
    (v_wnNf : Gamma ⊢ v ⇇ ty)
    : App_trm u v \in wnNe Gamma ty'
  | wnNe_Con c ty
    (ty_EQ : ty = Sigma c)
    : Con_trm c \in wnNe Gamma ty
  where "Gamma '⊢' M '⇉' A" := (wnNe Gamma A M)
with wnNf (Gamma : ctx L) : typ L -> wp (trm L) :=
  | wnNf_of_wnNe u ty
    (u_wnNe : Gamma ⊢ u ⇉ ty)
    : u \in wnNf Gamma ty
  | wnNf_Lam x v ty ty'
    (v_wnNf : (x, ty) :: Gamma ⊢ v ⇇ ty')
    : Lam_trm x ty v \in wnNf Gamma (ty -> ty')%typ
  | wnNf_beta_wnNf v v' ty
    (WHBETA : v ~>β v')
    (v_wnNf : Gamma ⊢ v' ⇇ ty)
    : v \in wnNf Gamma ty
  where "Gamma '⊢' M '⇇' A" := (wnNf Gamma A M).

Fixpoint le_ctx_wnNe (Gamma : ctx L) (ty : typ L) (u : trm L) (u_wnNe : Gamma ⊢ u ⇉ ty) {struct u_wnNe}
  : forall Gamma', le_ctx Gamma Gamma' -> Gamma' ⊢ u ⇉ ty
with le_ctx_wnNf (Gamma : ctx L) (ty : typ L) (v : trm L) (v_wnNf : Gamma ⊢ v ⇇ ty) {struct v_wnNf}
  : forall Gamma', le_ctx Gamma Gamma' -> Gamma' ⊢ v ⇇ ty.
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
  (y := Name.fresh_nm (map fst Gamma))
  (v_wnNf : (y, ty) :: Gamma ⊢ App_trm v (Var_trm y) ⇇ ty')
  : Gamma ⊢ v ⇇ (ty -> ty')%typ.
Proof.
Admitted.

Fixpoint eval_typ (Gamma : ctx L) (ty : typ L) {struct ty} : trm L -> Set :=
  match ty with
  | bty _ b => fun M => B.sig (trm L) (fun N => Gamma ⊢ N ⇉ bty _ b /\ M ~>β* N)
  | (ty1 -> ty2)%typ => fun M => forall Gamma', le_ctx Gamma Gamma' -> forall N, eval_typ Gamma' ty1 N -> eval_typ Gamma' ty2 (App_trm M N)
  end.

Fixpoint eval_typ_le_ctx Gamma ty {struct ty} : forall M, eval_typ Gamma ty M -> forall Gamma', le_ctx Gamma Gamma' -> eval_typ Gamma' ty M.
Proof.
  destruct ty as [b | ty1 ty2]; simpl; intros M H_M Gamma' LE.
  - exists H_M.(B.proj1_sig). split.
    + eapply le_ctx_wnNe. exact (proj1 H_M.(B.proj2_sig)). exact LE.
    + exact (proj2 H_M.(B.proj2_sig)).
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
    + eapply wnNf_whBetaStar_wnNf with (N := H_M.(B.proj1_sig)).
      * econs 1. exact (proj1 (B.proj2_sig H_M)).
      * exact (proj2 (B.proj2_sig H_M)).
    + eapply App_Var_wnNf_inv. eapply reify. eapply H_M.
      * eapply le_ctx_cons.
      * eapply reflect. econs 1. econs 1; reflexivity.
Defined.

Fixpoint head_expand (Gamma : ctx L) M M' (ty : typ L) (WHBETA : M ~>β M') {struct ty} : eval_typ Gamma ty M' -> eval_typ Gamma ty M.
Proof.
  revert Gamma ty. destruct ty as [b | ty1 ty2]; simpl; intros H_M.
  - exists H_M.(B.proj1_sig). split.
    + exact (proj1 H_M.(B.proj2_sig)).
    + econs 2.
      * exact (proj2 H_M.(B.proj2_sig)).
      * eassumption.
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
    rewrite subst_cons_lemma with (ty := ty1); [eapply IHTYPING | reflexivity].
    eapply eval_ctx_cons_subst; [exact a | eapply eval_ctx_le_ctx]; eassumption.
  - eapply reflect. econs 3. reflexivity.
Defined.

Corollary NbE_aux1 {Gamma : ctx L} {M : trm L} {ty : typ L}
  (TYPING : Typing Gamma M ty)
  : wnNf Gamma ty (subst_trm nil_subst M).
Proof.
  eapply reify. eapply semanticTyping_sound.
  - exact TYPING.
  - eapply eval_ctx_nil_subst.
Defined.

End WEAK_NORMALISATION.

End STLC_META.

End ChurchStyleSTLC.
