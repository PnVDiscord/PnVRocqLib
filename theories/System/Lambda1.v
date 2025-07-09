Require Import PnV.Prelude.Prelude.
Require Import PnV.System.P.
Require Import PnV.Data.Vector.

Declare Scope typ_scope.
Delimit Scope typ_scope with typ.

Fixpoint nth_list {A : Type} (xs : list A) {struct xs} : Fin.t (length xs) -> A :=
  match xs with
  | [] => Fin.case0
  | x :: xs => Fin.caseS x (nth_list xs)
  end.

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
    (x_ne : x <> x')
    (LOOKUP : Lookup x ty Gamma)
    : Lookup x ty ((x', ty') :: Gamma).

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
