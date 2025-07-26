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
Notation "Gamma '⊢' M '⇉' A" := (typNe Gamma M A) : type_scope.
Notation "Gamma '⊢' M '⇇' A" := (typNf Gamma M A) : type_scope.

Section STLC_META.

Context {L : language}.

Section Soundness_of_NbE.

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

Fixpoint interpret_typ (Gamma : ctx L) (ty : typ L) {struct ty} : eval_typ Gamma ty -> trm L -> Prop :=
  match ty as ty return eval_typ Gamma ty -> trm L -> Prop with
  | bty _ b => fun d : B.sig (trm L) (fun u => typNe Gamma u (bty _ b)) => fun e : trm L =>
    Gamma ⊢ d.(B.proj1_sig) = e ⦂ bty _ b
  | (ty1 -> ty2)%typ => fun d : forall Gamma' : ctx L, le_ctx Gamma Gamma' -> eval_typ Gamma' ty1 -> eval_typ Gamma' ty2 => fun e1 : trm L =>
    forall Gamma' : ctx L, forall LE : le_ctx Gamma Gamma', forall a : eval_typ Gamma' ty1, forall e2 : trm L, interpret_typ Gamma' ty1 a e2 -> interpret_typ Gamma' ty2 (d Gamma' LE a) (App_trm e1 e2)
  end.

Definition interpret_ctx (Gamma : ctx L) (Delta : ctx L) : eval_ctx Gamma Delta -> subst L -> Prop :=
  fun rho : eval_ctx Gamma Delta => fun gamma : subst L =>
  forall x : name, forall ty : typ L, forall LOOKUP : Lookup x ty Gamma, interpret_typ Delta ty (rho x ty LOOKUP) (gamma x).

End Soundness_of_NbE.

End STLC_META.

End ChurchStyleSTLC.
