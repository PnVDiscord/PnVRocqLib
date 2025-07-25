Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.System.P.
Require Import PnV.Data.Vector.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.

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

#[local] Notation bty := (bty _).

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

Section alphaEquivalence.

Inductive alphaEquiv : trm -> trm -> Prop :=
  | alphaEquiv_Var x
    : alphaEquiv (Var_trm x) (Var_trm x)
  | alphaEquiv_App M M' N N'
    (ALPHA1 : alphaEquiv M M')
    (ALPHA2 : alphaEquiv N N')
    : alphaEquiv (App_trm M N) (App_trm M' N')
  | alphaEquiv_Lam x x' x'' ty M M'
    (FRESH1 : ~ L.In x'' (FVs (Lam_trm x ty M)))
    (FRESH2 : ~ L.In x'' (FVs (Lam_trm x' ty M')))
    (ALPHA1 : alphaEquiv (subst_trm (one_subst x (Var_trm x'')) M) (subst_trm (one_subst x' (Var_trm x'')) M'))
    : alphaEquiv (Lam_trm x ty M) (Lam_trm x' ty M')
  | alphaEquiv_con c
    : alphaEquiv (Con_trm c) (Con_trm c).

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

Section NORMALISATION_BY_EVALUATION.

Definition le_ctx (Gamma : ctx) (Delta : ctx) : Set :=
  forall x : name, forall ty : typ, Lookup x ty Gamma -> Lookup x ty Delta.

Lemma le_ctx_cons Gamma ty'
  (y := Name.fresh_nm (map fst Gamma))
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
    pose proof (Name.fresh_nm_notin (map fst Gamma)) as claim1.
    fold y in claim1. rewrite Name.ne_iff. intros EQ. congruence.
  - exact LOOKUP.
Defined.

Context {Sigma : signature L}.

Inductive typNe (Gamma : ctx) : trm -> typ -> Prop :=
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
with typNf (Gamma : ctx) : trm -> typ -> Prop :=
  | typNf_of_typNe u ty
    (u_typNe : typNe Gamma u ty)
    : typNf Gamma u ty
  | typNf_Lam x v ty ty'
    (v_typNf : typNf ((x, ty) :: Gamma) v ty')
    : typNf Gamma (Lam_trm x ty v) (ty -> ty')%typ
  where "Gamma '⊢' M '⇇' A" := (typNf Gamma M A).

Lemma le_ctx_preserves_typNe (Gamma : ctx) (u : trm) (ty : typ)
  (u_typNe : typNe Gamma u ty)
  : forall Delta, le_ctx Gamma Delta -> typNe Delta u ty
with le_ctx_preserves_typNf (Gamma : ctx) (v : trm) (ty : typ)
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
    + econs 1. eapply le_ctx_preserves_typNe; eassumption.
    + econs 2. eapply le_ctx_preserves_typNf; try eassumption.
      red in LE |- *. intros x1 ty1 LOOKUP1. pattern LOOKUP1. revert LOOKUP1.
      eapply Lookup_cons.
      * intros. econs 1; eassumption.
      * intros. econs 2; try eassumption. eapply LE; eassumption.
Defined.

Lemma le_ctx_preserves_Typing {Gamma} {e} {ty}
  (TYPING : Typing Gamma e ty)
  : forall Delta : ctx, le_ctx Gamma Delta -> Typing Delta e ty.
Proof.
  induction TYPING; simpl; intros Delta LE.
  - econs 1. eapply LE. exact LOOKUP.
  - econs 2.
    + eapply IHTYPING1. exact LE.
    + eapply IHTYPING2. exact LE.
  - econs 3. eapply IHTYPING.
    intros x ty LOOKUP. pattern LOOKUP. revert LOOKUP. eapply Lookup_cons.
    + intros x_EQ ty_EQ. subst x ty. econs 1; reflexivity.
    + intros x_NE LOOKUP. econs 2.
      * exact x_NE.
      * eapply LE; eassumption.
  - econs 4.
Defined.

Fixpoint eval_typ (Gamma : ctx) (ty : typ) {struct ty} : Set :=
  match ty with
  | bty b => B.sig trm (fun u => typNe Gamma u (bty b))
  | (ty1 -> ty2)%typ => forall Gamma' : ctx, le_ctx Gamma Gamma' -> eval_typ Gamma' ty1 -> eval_typ Gamma' ty2
  end.

Lemma le_ctx_preserves_eval_typ {Gamma} {ty}
  (d : eval_typ Gamma ty)
  : forall Delta : ctx, le_ctx Gamma Delta -> eval_typ Delta ty.
Proof.
  induction ty; simpl in *; intros Delta LE.
  - exists d.(B.proj1_sig). eapply le_ctx_preserves_typNe; [exact d.(B.proj2_sig) | exact LE].
  - intros Gamma' LE' a; eapply d.
    + intros x ty LOOKUP. eapply LE'. eapply LE. exact LOOKUP.
    + exact a.
Defined.

Fixpoint reflect (Gamma : ctx) (ty : typ) {struct ty} : B.sig trm (fun u => typNe Gamma u ty) -> eval_typ Gamma ty
with reify (Gamma : ctx) (ty : typ) {struct ty} : eval_typ Gamma ty -> B.sig trm (fun v => typNf Gamma v ty).
Proof.
  - destruct ty as [b | ty1 ty2]; simpl; intros u_hat.
    + eapply u_hat.
    + intros Delta LE a. set (v_hat := reify Delta ty1 a).
      eapply reflect. exists (App_trm (u_hat).(B.proj1_sig) (v_hat).(B.proj1_sig)). econs 2.
      * eapply le_ctx_preserves_typNe; [exact (u_hat).(B.proj2_sig) | exact LE].
      * exact (v_hat).(B.proj2_sig).
  - destruct ty as [b | ty1 ty2]; simpl; intros d.
    + exists d.(B.proj1_sig). econs 1. exact d.(B.proj2_sig).
    + set (y := Name.fresh_nm (map fst Gamma)).
      pose proof (le_ctx_cons Gamma ty1) as claim1. simpl in claim1. fold y in claim1.
      assert (y_hat : B.sig trm (fun u : trm => typNe ((y, ty1) :: Gamma) u ty1)).
      { exists (Var_trm y). econs 1. econs 1; reflexivity. }
      set (a := reflect ((y, ty1) :: Gamma) ty1 y_hat).
      set (body := reify ((y, ty1) :: Gamma) ty2 (d ((y, ty1) :: Gamma) claim1 a)).
      exists (Lam_trm y ty1 body.(B.proj1_sig)). econs 2. exact (body).(B.proj2_sig).
Defined.

Definition eval_ctx (Gamma : ctx) (Delta : ctx) : Set :=
  forall x : name, forall ty : typ, Lookup x ty Gamma -> eval_typ Delta ty.

Fixpoint evalTyping Gamma e ty (TYPING : Typing Gamma e ty) {struct TYPING} : forall Delta : ctx, eval_ctx Gamma Delta -> eval_typ Delta ty.
Proof.
  destruct TYPING; simpl; intros Delta rho.
  - refine (rho x ty LOOKUP).
  - refine (evalTyping Gamma e1 (ty1 -> ty2)%typ TYPING1 Delta rho _ _ (evalTyping Gamma e2 ty1 TYPING2 Delta rho)).
    intros x ty LOOKUP. exact LOOKUP.
  - intros Gamma' LE a.
    eapply evalTyping with (Gamma := (y, ty1) :: Gamma) (e := e1).
    { exact TYPING. }
    intros x ty LOOKUP. pattern LOOKUP. revert LOOKUP. eapply Lookup_cons.
    + intros x_EQ ty_EQ. subst ty1. exact a.
    + intros NE LOOKUP.
      pose proof (rho_x := rho x ty LOOKUP).
      exact (le_ctx_preserves_eval_typ rho_x Gamma' LE).
  - eapply reflect. exists (Con_trm c). econs 3. reflexivity.
Defined.

Lemma eval_ctx_Gamma_Gamma {Gamma : ctx}
  : eval_ctx Gamma Gamma.
Proof.
  intros x ty LOOKUP. eapply reflect.
  exists (Var_trm x). econs 1. exact LOOKUP.
Defined.

Definition NbE (Gamma : ctx) (e : trm) (ty : typ) (TYPING : Typing Gamma e ty) : B.sig trm (fun v => typNf Gamma v ty) :=
  reify Gamma ty (evalTyping Gamma e ty TYPING Gamma eval_ctx_Gamma_Gamma).

End NORMALISATION_BY_EVALUATION.

Section SN.

Inductive betaOnce : trm -> trm -> Prop :=
  | betaOnce_beta x ty M N
    : betaOnce (App_trm (Lam_trm x ty M) N) (subst_trm (one_subst x N) M)
  | betaOnce_appl M M' N
    (BETA' : betaOnce M M')
    : betaOnce (App_trm M N) (App_trm M' N)
  | betaOnce_appr M N N'
    (BETA' : betaOnce N N')
    : betaOnce (App_trm M N) (App_trm M N')
  | betaOnce_lam x ty M M'
    (BETA' : betaOnce M M')
    : betaOnce (Lam_trm x ty M) (Lam_trm x ty M').

Lemma betaOnce_dec (M : trm)
  : B.sig trm (fun N => betaOnce M N) + B.Prop_to_Set (forall N : trm, ~ betaOnce M N).
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
    (sn_inv : forall N, betaOnce M N -> sn N)
    : sn M.

Definition sn_inv {M : trm} (H_sn : sn M) : forall N, betaOnce M N -> sn N :=
  match H_sn with
  | @sn_intro _ sn_inv => sn_inv
  end.

Fixpoint normalize_with_sn (M : trm) (H_sn : sn M) {struct H_sn} : trm :=
  match betaOnce_dec M with
  | inl YES => let N : trm := B.proj1_sig YES in normalize_with_sn N (sn_inv H_sn N (B.proj2_sig YES))
  | inr NO => M
  end.

Lemma normalize_with_sn_unfold M H_sn :
  normalize_with_sn M H_sn =
  match betaOnce_dec M with
  | inl YES => let N : trm := B.proj1_sig YES in normalize_with_sn N (sn_inv H_sn N (B.proj2_sig YES))
  | inr NO => M
  end.
Proof.
  destruct H_sn; reflexivity.
Defined.

Fixpoint normalize_with_sn_pirrel (M : trm) (H_sn : sn M) (H_sn' : sn M) {struct H_sn} : normalize_with_sn M H_sn = normalize_with_sn M H_sn'.
Proof.
  destruct H_sn, H_sn'; simpl. destruct (betaOnce_dec M) as [YES | NO]; simpl.
  - eapply normalize_with_sn_pirrel.
  - reflexivity.
Qed.

Fixpoint normalize_with_sn_normalized (M : trm) (N : trm) (H_sn : sn M) {struct H_sn} : ~ betaOnce (normalize_with_sn M H_sn) N.
Proof.
  destruct H_sn; simpl. intros BETA. destruct (betaOnce_dec M) as [YES | NO].
  - eapply normalize_with_sn_normalized. exact BETA.
  - red in NO. exact (NO N BETA).
Qed.

End SN.

Inductive betaStar (M : trm) (N : trm) : Prop :=
  | betaStar_refl
    (ALPHA : alphaEquiv M N)
  | betaStar_step N'
    (BETA1 : betaOnce N' N)
    (BETA : betaStar M N').

End STLC.

#[global] Arguments trm : clear implicits.
#[global] Arguments ctx : clear implicits.
#[global] Arguments subst : clear implicits.
#[global] Coercion bty : basic_types >-> typ.

End ChurchStyleStlc.
