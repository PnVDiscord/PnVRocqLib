Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.System.P.
Require Import PnV.Data.Vector.
Require Import PnV.System.Lambda1.

Reserved Infix "->β" (at level 70, no associativity).
Reserved Infix "->η" (at level 70, no associativity).
Reserved Infix "~>β" (at level 70, no associativity).
Reserved Infix "~>η" (at level 70, no associativity).
Reserved Infix "~>β*" (at level 70, no associativity).
Reserved Infix "~>η*" (at level 70, no associativity).

Module ChurchStyleSTLC.

Export ChurchStyleStlc.

Notation "Gamma '∋' x '⦂' A" := (Lookup x A Gamma) : type_scope.
Notation "Gamma '⊢' M '⦂' A" := (Typing Gamma M A) : type_scope.
Notation "Gamma '⊢' M '=' N '⦂' A" := (equality Gamma M N A) : type_scope.

Section STLC_META.

Context {L : language}.

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

Definition substTyping (Gamma : ctx L) (s : subst L) (Delta : ctx L) : Set :=
  forall x : name, forall ty : typ L, Lookup x ty Delta -> Typing Gamma (s x) ty.

Lemma substTyping_Lookup {Gamma : ctx L} {x : Name.t} {ty : typ L} {s : subst L} {Delta : ctx L}
  (LOOKUP : Gamma ∋ x ⦂ ty)
  (SUBST_TYPING : substTyping Delta s Gamma)
  : Delta ⊢ s x ⦂ ty.
Proof.
  eapply SUBST_TYPING; exact LOOKUP.
Defined.

Lemma substTyping_Typing {Gamma : ctx L} {e : trm L} {ty : typ L} {s : subst L} {Delta : ctx L}
  (TYPING : Gamma ⊢ e ⦂ ty)
  (SUBST_TYPING : substTyping Delta s Gamma)
  : Delta ⊢ subst_trm s e ⦂ ty.
Proof.
Admitted.

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
    : App_trm (Lam_trm y ty M) N ->β subst_trm (one_subst y N) M
  | whBeta_ksi M M' N
    (WHBETA : M ->β M')
    : App_trm M N ->β App_trm M' N
  where "M ->β N" := (whBeta M N).

Inductive whBetaStar (M : trm L) : trm L -> Prop :=
  | whBetaStar_O
    : M ~>β* M
  | whBetaStar_S N N'
    (WHBETA' : M ~>β* N)
    (WHBETA : N ->β N')
    : M ~>β* N'
  where "M ~>β* N" := (whBetaStar M N).

Lemma whBeta_FVs M N
  (WHBETA : M ->β N)
  : forall x, L.In x (FVs N) -> L.In x (FVs M).
Proof.
Admitted.

Inductive whEta (M : trm L) : trm L -> Prop :=
  | whEta_intro x ty
    (FRESH : ~ L.In x (FVs M))
    : Lam_trm x ty (App_trm M (Var_trm x)) ->η M
  where "M ->η N" := (whEta N M).

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
    (WHBETA : v ->β v')
    (v_wnNf : Gamma ⊢ v' ⇇ ty)
    : v \in wnNf Gamma ty
  where "Gamma '⊢' M '⇇' A" := (wnNf Gamma A M).

Lemma le_ctx_wnNe (Gamma : ctx L) (ty : typ L) (u : trm L)
  (u_wnNe : Gamma ⊢ u ⇉ ty)
  : forall Gamma', le_ctx Gamma Gamma' -> Gamma' ⊢ u ⇉ ty
with le_ctx_wnNf (Gamma : ctx L) (ty : typ L) (v : trm L)
  (u_wnNe : Gamma ⊢ v ⇇ ty)
  : forall Gamma', le_ctx Gamma Gamma' -> Gamma' ⊢ v ⇇ ty.
Admitted.

Fixpoint eval_typ (Gamma : ctx L) (ty : typ L) : trm L -> Set :=
  match ty with
  | bty _ b => fun M =>
    B.sig (trm L) (fun N => Gamma ⊢ N ⇉ bty _ b /\ M ~>β* N)
  | (ty1 -> ty2)%typ => fun M =>
    forall N, forall Gamma', le_ctx Gamma Gamma' -> eval_typ Gamma' ty1 N -> eval_typ Gamma' ty2 (App_trm M N)
  end.

Lemma wnNf_whBetaStar_wnNf Gamma M N ty
  (v_wnNf : Gamma ⊢ N ⇇ ty)
  (WHBETA' : M ~>β* N)
  : Gamma ⊢ M ⇇ ty.
Proof.
  induction WHBETA'; simpl in *.
  - eassumption.
  - eapply IHWHBETA'.
    econs 3; eauto.
Qed.

Lemma App_Var_wnNf_inv Gamma ty ty' v
  (y := Name.fresh_nm (map fst Gamma))
  (v_wnNf : (y, ty) :: Gamma ⊢ (App_trm v (Var_trm y)) ⇇ ty')
  : Gamma ⊢ v ⇇ (ty -> ty')%typ.
Admitted.

Fixpoint reflect (Gamma : ctx L) (ty : typ L) {struct ty} : forall e, wnNe Gamma ty e -> eval_typ Gamma ty e
with reify (Gamma : ctx L) (ty : typ L) {struct ty} : forall e, eval_typ Gamma ty e -> wnNf Gamma ty e.
Proof.
  - destruct ty as [b | ty1 ty2]; simpl; intros M H_M.
    + exists M. split.
      * eassumption.
      * econs 1.
    + intros N Gamma' LE H_N. eapply reflect. econs 2.
      * eapply le_ctx_wnNe; [exact H_M | exact LE].
      * eapply reify. exact H_N.
  - destruct ty as [b | ty1 ty2]; simpl; intros M H_M.
    + destruct H_M as [N [N_wnNe WHBETA']].
      eapply wnNf_whBetaStar_wnNf with (N := N).
      * econs 1; eassumption.
      * eassumption.
    + eapply App_Var_wnNf_inv. eapply reify. eapply H_M.
      * eapply le_ctx_cons.
      * eapply reflect. econs 1. econs 1; reflexivity.
Defined.

Definition eval_ctx (Gamma : ctx L) (Delta : ctx L) : subst L -> Set :=
  fun gamma => forall x, forall ty, Lookup x ty Delta -> eval_typ Gamma ty (gamma x).

Definition semanticTyping (Gamma : ctx L) (e : trm L) (ty : typ L) : Set :=
  forall Delta, forall gamma, eval_ctx Delta Gamma gamma -> eval_typ Delta ty (subst_trm gamma e).

Theorem semanticTyping_sound Gamma e ty
  (TYPING : Typing Gamma e ty)
  : semanticTyping Gamma e ty.
Proof.
Admitted.

End WEAK_NORMALISATION.

End STLC_META.

End ChurchStyleSTLC.
