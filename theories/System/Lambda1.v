Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.System.P.
Require Import PnV.Data.Vector.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.

Reserved Notation "Gamma '⊢' M '⦂' A" (at level 70, no associativity).

Module ChurchStyleStlc.

#[local] Open Scope name_scope.

#[projections(primitive)]
Record language : Type :=
  { basic_types : Set
  ; constants : Set
  }.

Inductive typ (L : language) : Set :=
  | bty (B : L.(basic_types)) : typ L
  | arr (D : typ L) (C : typ L) : typ L.

#[global] Bind Scope typ_scope with typ.
#[global] Notation "D -> C" := (@arr _ D C) : typ_scope.

#[global]
Instance typ_hasEqDec (L : language)
  (bty_hasEqDec : hasEqDec L.(basic_types))
  : hasEqDec (typ L).
Proof.
  red in bty_hasEqDec |- *. decide equality.
Defined.

Class signature (L : language) : Set :=
  typ_of_constant (c : L.(constants)) : typ L.

Section STLC.

#[local] Hint Resolve Name.ne_pirrel : core.

Context {L : language}.

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

(* TODO *)

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

(* TODO *)

End Substitution.

Section alphaEquivalence.

Inductive alphaEquiv : trm -> trm -> Prop :=
  | alphaEquiv_Var x
    : alphaEquiv (Var_trm x) (Var_trm x)
  | alphaEquiv_App M M' N N'
    (ALPHA1 : alphaEquiv M M')
    (ALPHA2 : alphaEquiv N N')
    : alphaEquiv (App_trm M N) (App_trm M' N')
  | alphaEquiv_Lam x x' x'' ty M M'
    (ALPHA1 : alphaEquiv (subst_trm (one_subst x (Var_trm x'')) M) (subst_trm (one_subst x' (Var_trm x'')) M'))
    : alphaEquiv (Lam_trm x ty M) (Lam_trm x' ty M').

(* TODO *)

End alphaEquivalence.

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
    : Lookup x ty ((x', ty') :: Gamma).

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

#[global, program]
Instance Lookup_retracts x ty Gamma : B.retracts (Lookup x ty Gamma) (LookupProp x ty Gamma) :=
  { section := Lookup_to_LookupProp x ty Gamma
  ; retraction := LookupProp_to_Lookup x ty Gamma
  }.
Next Obligation.
  rename x0 into X. induction X; simpl.
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

Lemma Lookup_proof_unique {bty_hasEqDec : hasEqDec L.(basic_types)} x ty Gamma
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

Context {Sigma : signature L}.

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
  | Lam_trm y ty1 e1 => { ty2 : typ & (Typing ((y, ty1) :: Gamma) e1 ty2 * (ty = (ty1 -> ty2)%typ))%type }
  | Con_trm c => ty = typ_of_constant c
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
  - destruct TYPING as [ty2 [TYPING1 EQ]]. subst ty. econs 3; eassumption.
  - subst ty. econs 4.
Defined.

Lemma Typing_encode_decode Gamma e ty
  (TYPING : Typing_code Gamma e ty)
  : (Typing_encode (Typing_decode TYPING)) = TYPING.
Proof.
  destruct e; simpl in *.
  - reflexivity.
  - destruct TYPING as [ty1 [TYPING1 TYPING2]]. reflexivity.
  - destruct TYPING as [ty1 [TYPING EQ]]. subst ty. reflexivity.
  - subst ty. reflexivity.
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

Fixpoint TypingProp (Gamma : ctx) (e : trm) (ty : typ) {struct e} : Prop :=
  match e with
  | Var_trm x => LookupProp x ty Gamma
  | App_trm e1 e2 => exists ty1, TypingProp Gamma e1 (ty1 -> ty)%typ /\ TypingProp Gamma e2 ty1
  | Lam_trm y ty1 e1 => exists ty2, TypingProp ((y, ty1) :: Gamma) e1 ty2 /\ ty = (ty1 -> ty2)%typ
  | Con_trm c => ty = typ_of_constant c
  end.

Lemma Typing_to_TypingProp Gamma e ty
  (TYPING : Typing Gamma e ty)
  : TypingProp Gamma e ty.
Proof.
  induction TYPING; simpl.
  - eapply Lookup_to_LookupProp. exact LOOKUP.
  - exists ty1. split; [exact IHTYPING1 | exact IHTYPING2].
  - exists ty2. split; [exact IHTYPING | reflexivity].
  - reflexivity.
Defined.

(* TODO *)

End TypingRule.

Section INTERPRET.

Context {Sigma : signature L}.

Variable eval_bty : L.(basic_types) -> Set.

Fixpoint eval_typ (ty : typ) : Set :=
  match ty with
  | bty _ b => eval_bty b
  | (ty1 -> ty2)%typ => eval_typ ty1 -> eval_typ ty2
  end.

Definition eval_ctx (Gamma : ctx) : Set :=
  forall i : Fin.t (length Gamma), eval_typ (snd (nth_list Gamma i)).

Fixpoint evalLookup {x : name} {ty : typ} {Gamma : ctx} (LOOKUP : Lookup x ty Gamma) {struct LOOKUP} : Fin.t (length Gamma) :=
  match LOOKUP with
  | Lookup_Z _ _ _ _ _ _ _ => Fin.FZ
  | Lookup_S _ _ _ _ _ _ LOOKUP => Fin.FS (evalLookup LOOKUP)
  end.

Lemma nth_list_evalLookup_snd x ty Gamma
  (LOOKUP : Lookup x ty Gamma)
  : ty = snd (nth_list Gamma (evalLookup LOOKUP)).
Proof.
  induction LOOKUP; simpl.
  - exact ty_eq.
  - exact IHLOOKUP.
Defined.

Definition evalLookup' {x : name} {ty : typ} {Gamma : ctx} (LOOKUP : Lookup x ty Gamma) (rho : eval_ctx Gamma) : eval_typ ty.
Proof.
  assert (eval_typ ty = eval_typ (snd (nth_list Gamma (evalLookup LOOKUP)))) as EQ by exact (f_equal eval_typ (nth_list_evalLookup_snd x ty Gamma LOOKUP)).
  rewrite -> EQ. exact (rho (evalLookup LOOKUP)).
Defined.

Variable eval_con : forall c : L.(constants), eval_typ (typ_of_constant c).

Fixpoint evalTyping Gamma e ty (TYPING : Typing Gamma e ty) {struct TYPING} : eval_ctx Gamma -> eval_typ ty.
Proof.
  destruct TYPING.
  - exact (evalLookup' LOOKUP).
  - exact (fun rho : eval_ctx Gamma => evalTyping _ _ _ TYPING1 rho (evalTyping _ _ _ TYPING2 rho)).
  - exact (fun rho : eval_ctx Gamma => fun a : eval_typ ty1 => evalTyping _ _ _ TYPING (Fin.caseS a rho)).
  - exact (fun _ : eval_ctx Gamma => eval_con c).
Defined.

End INTERPRET.

End STLC.

#[global] Arguments trm : clear implicits.
#[global] Arguments ctx : clear implicits.
#[global] Coercion bty : basic_types >-> typ.

End ChurchStyleStlc.
