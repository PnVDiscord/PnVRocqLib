Require Import PnV.Prelude.Prelude.
Require Import PnV.System.P.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.

Reserved Notation "Gamma '⊢' M '⦂' A" (at level 70, no associativity).

Module ChurchStyleStlc.

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

Class signature (L : language) : Set :=
  typ_of_constant (c : L.(constants)) : typ L.

Section STLC.

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

Section betaReduction.

Inductive betaStep : trm -> trm -> Prop :=
  | betaStep_beta x ty M N
    : betaStep (App_trm (Lam_trm x ty M) N) (subst_trm (one_subst x N) M)
  | betaStep_appL M M' N
    (BETA : betaStep M M')
    : betaStep (App_trm M N) (App_trm M' N)
  | betaStep_appR M N N'
    (BETA : betaStep N N')
    : betaStep (App_trm M N) (App_trm M N')
  | betaStep_lam x ty M M'
    (BETA : betaStep M M')
    : betaStep (Lam_trm x ty M) (Lam_trm x ty M').

Inductive betaMultiStep (M : trm) (N : trm) : Prop :=
  | betaMultiStep_alpha
    (ALPHA : alphaEquiv M N)
    : betaMultiStep M N
  | betaMultiStep_beta
    (BETA : betaStep M N)
    : betaMultiStep M N
  | betaMultiStep_trans P
    (STEP1 : betaMultiStep M P)
    (STEP2 : betaMultiStep P N)
    : betaMultiStep M N.

End betaReduction.

Section etaExpansion.

End etaExpansion.

Section TypingRule.

Definition ctx : Set :=
  list (name * typ).

Inductive Lookup (x : name) (ty : typ) : ctx -> Set :=
  | Lookup_Z Gamma x' ty'
    (x_eq : x = x')
    (ty_eq : ty = ty')
    : Lookup x ty ((x', ty') :: Gamma)
  | Lookup_S Gamma x' ty'
    (x_ne : x <> x')
    (LOOKUP : Lookup x ty Gamma)
    : Lookup x ty ((x', ty') :: Gamma).

Lemma Lookup_lookup x ty Gamma
  (LOOKUP : Lookup x ty Gamma)
  : Some ty = L.lookup x Gamma.
Proof.
  induction LOOKUP; simpl in *; destruct (eq_dec x x'); contradiction || congruence.
Defined.

Definition lookup_Lookup (x : name) (ty : typ) : forall Gamma : ctx, Some ty = L.lookup x Gamma -> Lookup x ty Gamma :=
  fix IH (Gamma : list (name * typ)) {struct Gamma} : Some ty = L.lookup x Gamma -> Lookup x ty Gamma :=
  match Gamma as Gamma return Some ty = L.lookup x Gamma -> Lookup x ty Gamma with
  | [] => fun LOOKUP : Some ty = None => False_rec _ (B.Some_ne_None ty LOOKUP)
  | (x', ty') :: Gamma' =>
    match eq_dec x x' as b return Some ty = (if b then Some ty' else L.lookup x Gamma') -> Lookup x ty ((x', ty') :: Gamma') with
    | left EQ => fun LOOKUP : Some ty = Some ty' => Lookup_Z x ty Gamma' x' ty' EQ (f_equal (B.fromMaybe ty') LOOKUP)
    | right NE => fun LOOKUP : Some ty = L.lookup x Gamma' => Lookup_S x ty Gamma' x' ty' NE (IH Gamma' LOOKUP)
    end
  end.

Context {Sigma : signature L}.

Inductive treeOfTyping (Gamma : ctx) : trm -> typ -> Set :=
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
  where "Gamma '⊢' M '⦂' A" := (treeOfTyping Gamma M A) : type_scope.

(* TODO *)

End TypingRule.

End STLC.

#[global] Arguments trm : clear implicits.
#[global] Arguments ctx : clear implicits.
#[global] Coercion bty : basic_types >-> typ.

End ChurchStyleStlc.
