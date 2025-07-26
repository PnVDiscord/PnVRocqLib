Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.System.P.
Require Import PnV.Data.Vector.
Require Import PnV.System.Lambda1.

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

Inductive typNe (Gamma : ctx L) : trm L -> typ L -> Prop :=
  | typNe_Var x ty
    (LOOKUP : Lookup x ty Gamma)
    : typNe Gamma (Var_trm x) ty
  | typNe_App u v ty ty'
    (u_typNe : typNe Gamma u (ty -> ty')%typ)
    (v_typNf : typNf Gamma v ty)
    : typNe Gamma (App_trm u v) ty'
  | typNe_Con c ty
    (ty_eq : ty = Sigma c)
    : typNe Gamma (Con_trm c) ty
  where "Gamma '⊢' M '⇉' A" := (typNe Gamma M A)
with typNf (Gamma : ctx L) : trm L -> typ L -> Prop :=
  | typNf_of_typNe u v ty
    (u_typNe : typNe Gamma u ty)
    (ALPHA : alphaEquiv v u)
    : typNf Gamma v ty
  | typNf_Lam x v ty ty'
    (v_typNf : typNf ((x, ty) :: Gamma) v ty')
    : typNf Gamma (Lam_trm x ty v) (ty -> ty')%typ
  | typNf_beta_typNf v v' ty
    (BETA : betaOnce v v')
    (v_typNf : typNf Gamma v' ty)
    : typNf Gamma v ty
  where "Gamma '⊢' M '⇇' A" := (typNf Gamma M A).

Fixpoint eval_typ (Gamma : ctx L) (ty : typ L) : trm L -> Set :=
  match ty with
  | bty _ b => fun M =>
    B.sig (trm L) (fun N => Gamma ⊢ N ⇉ bty _ b /\ betaStar M N)
  | (ty1 -> ty2)%typ => fun M =>
    forall N, forall Gamma', le_ctx Gamma Gamma' -> eval_typ Gamma' ty1 N -> eval_typ Gamma' ty2 (App_trm M N)
  end.

(*
Fixpoint reflect (Gamma : ctx L) (ty : typ L) {struct ty} : forall e, typNe Gamma e ty -> eval_typ Gamma ty e
with reify (Gamma : ctx L) (ty : typ L) {struct ty} : forall e, eval_typ Gamma ty e -> typNf Gamma e ty.
Proof.
Admitted.
*)

Definition eval_ctx (Gamma : ctx L) (Delta : ctx L) : subst L -> Set :=
  fun gamma => forall x, forall ty, Lookup x ty Delta -> eval_typ Gamma ty (gamma x).

Definition semanticTyping (Gamma : ctx L) (e : trm L) (ty : typ L) : Set :=
  forall Delta, forall gamma, eval_ctx Delta Gamma gamma -> eval_typ Delta ty (subst_trm gamma e).

(*
Theorem semanticTyping_sound Gamma e ty
  (TYPING : Typing Gamma e ty)
  : semanticTyping Gamma e ty.
Proof.
Admitted.
*)

End WEAK_NORMALISATION.

End STLC_META.

End ChurchStyleSTLC.
