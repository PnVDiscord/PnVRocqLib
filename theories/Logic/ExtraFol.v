Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.Data.Vector.
Require Import PnV.Logic.BasicFol.
Require Import PnV.Logic.BasicFol2.
Require Import PnV.Logic.HilbertFol.

Section SCOPED.

Context {L : language}.

Definition scoped_trm (xs : list ivar) : Set :=
  { t : trm L | forall z, is_free_in_trm z t = true -> In z xs }.

Definition scoped_trms (n : nat) (xs : list ivar) : Set :=
  { ts : trms L n | forall z, is_free_in_trms z ts = true -> In z xs }.

Definition scoped_frm (xs : list ivar) : Set :=
  { p : frm L | forall z, is_free_in_frm z p = true -> In z xs }.

#[program]
Definition sRel {xs : list ivar} (R : L.(relation_symbols)) (ts : scoped_trms (L.(relation_arity_table) R) xs) : scoped_frm xs :=
  @exist _ _ (Rel_frm R (proj1_sig ts)) (fun z : ivar => fun H => _).
Next Obligation.
  exact (proj2_sig ts z H).
Qed.

#[program]
Definition sEqn {xs : list ivar} (t1 : scoped_trm xs) (t2 : scoped_trm xs) : scoped_frm xs :=
  @exist _ _ (Eqn_frm t1 t2) (fun z : ivar => fun H => _).
Next Obligation.
  rewrite orb_true_iff in H. destruct H as [H | H].
  - exact (proj2_sig t1 z H).
  - exact (proj2_sig t2 z H).
Qed.

#[program]
Definition sNeg {xs : list ivar} (s1 : scoped_frm xs) : scoped_frm xs :=
  @exist _ _ (Neg_frm (proj1_sig s1)) (fun z : ivar => fun H => _).
Next Obligation.
  exact (proj2_sig s1 z H).
Qed.

#[program]
Definition sImp {xs : list ivar} (s1 : scoped_frm xs) (s2 : scoped_frm xs) : scoped_frm xs :=
  @exist _ _ (Imp_frm (proj1_sig s1) (proj1_sig s2)) (fun z : ivar => fun H => _).
Next Obligation.
  rewrite orb_true_iff in H. destruct H as [H | H].
  - exact (proj2_sig s1 z H).
  - exact (proj2_sig s2 z H).
Qed.

#[program]
Definition sAll {xs : list ivar} (y : ivar) (s1 : scoped_frm (y :: xs)) : scoped_frm xs :=
  @exist _ _ (All_frm y (proj1_sig s1)) (fun z : ivar => fun H => _).
Next Obligation.
  s!. destruct H as [FREE NE]. pose proof (proj2_sig s1 z FREE) as claim. simpl in claim.
  destruct claim as [EQ | IN]; [now contradiction NE | exact IN].
Qed.

#[program]
Definition Con_trm_nil_scoped (c : L.(constant_symbols)) : scoped_trm [] :=
  @exist _ _ (Con_trm c) _.

#[program]
Definition subst_one_frm_nil_scoped (y : ivar) (t : scoped_trm []) (p : scoped_frm [y]) : scoped_frm [] :=
  @exist _ _ (subst_frm (one_subst y (proj1_sig t)) (proj1_sig p)) _.
Next Obligation.
  revert z H.
  assert (claim1 : forall z : ivar, is_free_in_frm z (proj1_sig p) = true -> z = y).
  { intros z FREE. now pose proof (proj2_sig p z FREE) as [EQ | []]. }
  assert (claim2 : forall z : ivar, is_not_free_in_trm z (proj1_sig t)).
  { intros z. red. pose proof (proj2_sig t z). destruct (is_free_in_trm z (proj1_sig t)) as [ | ]; [now contradiction H | reflexivity]. }
  intros z H. pose proof (one_fv_frm_subst_closed_term_close_formula y (proj1_sig t) (proj1_sig p) claim1 claim2 z) as claim3. red in claim3.
  enough (WTS : true = false) by discriminate. rewrite <- H. rewrite <- claim3. reflexivity.
Qed.

Lemma closed_frm_is_sentence (p : frm L)
  : L.null (fvs_frm (closed_frm p)) = true.
Proof.
  rewrite L.null_spec. destruct (fvs_frm (closed_frm p)) as [ | z zs] eqn: H_OBS; trivial.
  contradiction (closed_frm_closed p z). rewrite <- fv_is_free_in_frm. rewrite H_OBS; simpl; left; trivial.
Qed.

Definition sentence : Set :=
  { p : frm L | L.null (fvs_frm p) = true }.

#[program]
Definition sentence_isEnumerable (enum_frm_L : isEnumerable (frm L)) : isEnumerable sentence :=
  {| enum n := @exist _ _ (closed_frm (enum n)) (closed_frm_is_sentence (enum n)) |}.
Next Obligation.
  unfold closed_frm. destruct x as [p p_eq]; simpl in *.
  assert (EQ : (close_ivars p (nodup eq_dec (fvs_frm p))) = p). 
  { enough (WTS : (nodup eq_dec (fvs_frm p)) = []) by now rewrite WTS.
    destruct (nodup eq_dec (fvs_frm p)) as [ | z zs] eqn: H_OBS.
    - reflexivity.
    - assert (claim : L.In z (fvs_frm p)).
      { rewrite <- L.nodup_In with (decA := eq_dec). rewrite H_OBS. simpl. left. reflexivity. }
      rewrite L.null_spec in p_eq. rewrite p_eq in claim. contradiction claim.
  }
  exists (proj1_sig (enum_spec p)). destruct (enum_spec p) as [n n_eq]; simpl.
  rewrite <- n_eq in EQ. rewrite @exist_eq_bool with (A := frm L) (P := fun p => L.null (fvs_frm p)).
  rewrite EQ. exact n_eq.
Qed.

End SCOPED.

#[global] Arguments scoped_trm : clear implicits.
#[global] Arguments scoped_trms : clear implicits.
#[global] Arguments scoped_frm : clear implicits.
#[global] Arguments sentence : clear implicits.

Module ND.

Section NATURAL_DEDUCTION.

#[local] Infix " \in " := E.In.
#[local] Infix " \subseteq " := E.isSubsetOf.
#[local] Notation In := List.In.

Context {L : language}.

Inductive infers (Gamma : list (frm L)) : frm L -> Set :=
  | ByAssumption C
    (IN : In C Gamma)
    : Gamma ⊢ C
  | EquationI t
    : Gamma ⊢ Eqn_frm t t
  | EquationE A x t1 t2
    (INFERS1 : Gamma ⊢ Eqn_frm t1 t2)
    (INFERS2 : Gamma ⊢ subst_frm (one_subst x t1) A)
    : Gamma ⊢ subst_frm (one_subst x t2) A
  | UniversalI x y A
    (FRESH1 : forall p, In p Gamma -> is_free_in_frm y p = false)
    (FRESH2 : is_free_in_frm y (All_frm x A) = false)
    (INFERS1 : Gamma ⊢ subst_frm (one_subst x (Var_trm y)) A)
    : Gamma ⊢ All_frm x A
  | UniversalE x t A
    (INFERS1 : Gamma ⊢ All_frm x A)
    : Gamma ⊢ subst_frm (one_subst x t) A
  | ExistentialI x t A
    (INFERS1 : Gamma ⊢ subst_frm (one_subst x t) A)
    : Gamma ⊢ Exs_frm x A
  | ExistentialE x y A B
    (FRESH1 : forall p, In p Gamma -> is_free_in_frm y p = false)
    (FRESH2 : is_free_in_frm y (Exs_frm x A) = false)
    (FRESH3 : is_free_in_frm y B = false)
    (INFERS1 : Gamma ⊢ Exs_frm x A)
    (INFERS2 : subst_frm (one_subst x (Var_trm y)) A :: Gamma ⊢ B)
    : Gamma ⊢ B
  | ContradictionI A
    (INFERS1 : Gamma ⊢ A)
    (INFERS2 : Gamma ⊢ Neg_frm A)
    : Gamma ⊢ Bot_frm
  | ContradictionE A
    (INFERS1 : Gamma ⊢ Bot_frm)
    : Gamma ⊢ A
  | NegationI A
    (INFERS1 : A :: Gamma ⊢ Bot_frm)
    : Gamma ⊢ Neg_frm A
  | NegationE A
    (INFERS1 : Neg_frm A :: Gamma ⊢ Bot_frm)
    : Gamma ⊢ A
  | ConjunctionI A B
    (INFERS1 : Gamma ⊢ A)
    (INFERS2 : Gamma ⊢ B)
    : Gamma ⊢ Con_frm A B
  | ConjunctionE1 A B
    (INFERS1 : Gamma ⊢ Con_frm A B)
    : Gamma ⊢ A
  | ConjunctionE2 A B
    (INFERS1 : Gamma ⊢ Con_frm A B)
    : Gamma ⊢ B
  | DisjunctionI1 A B
    (INFERS1 : Gamma ⊢ A)
    : Gamma ⊢ Dis_frm A B
  | DisjunctionI2 A B
    (INFERS1 : Gamma ⊢ B)
    : Gamma ⊢ Dis_frm A B
  | DisjunctionE A B C
    (INFERS1 : Gamma ⊢ Dis_frm A B)
    (INFERS2 : A :: Gamma ⊢ C)
    (INFERS2 : B :: Gamma ⊢ C)
    : Gamma ⊢ Dis_frm A B
  | ImplicationI A B
    (INFERS1 : A :: Gamma ⊢ B)
    : Gamma ⊢ Imp_frm A B
  | ImplicationE A B
    (INFERS1 : Gamma ⊢ Imp_frm A B)
    (INFERS2 : Gamma ⊢ A)
    : Gamma ⊢ B
  | BiconditionalI A B
    (INFERS1 : A :: Gamma ⊢ B)
    (INFERS2 : B :: Gamma ⊢ A)
    : Gamma ⊢ Iff_frm A B
  | BiconditionalE1 A B
    (INFERS1 : Gamma ⊢ Iff_frm A B)
    (INFERS2 : Gamma ⊢ A)
    : Gamma ⊢ B
  | BiconditionalE2 A B
    (INFERS1 : Gamma ⊢ Iff_frm A B)
    (INFERS2 : Gamma ⊢ B)
    : Gamma ⊢ A
  where "Gamma ⊢ C" := (infers Gamma C) : type_scope.

End NATURAL_DEDUCTION.

End ND.

Declare Custom Entry trm_view.
Declare Custom Entry trms_view.
Declare Custom Entry frm_view.
Declare Custom Entry subst_view.
Reserved Notation "'$' EXPR '$'" (EXPR custom frm_view at level 10, no associativity, format "'$' EXPR '$'", at level 0).

Module FolViewer.

#[global] Declare Scope trm_scope.
#[global] Declare Scope trms_scope.
#[global] Declare Scope frm_scope.
#[global] Declare Scope subst_scope.

Notation "'$' EXPR '$'" := EXPR : frm_scope.
Notation "'$' EXPR '$'" := (EXPR : frm _).

#[global] Bind Scope trm_scope with trm.
Notation "'`[' s ']' t" := (subst_trm s t) (s custom subst_view at level 10, t custom trm_view at level 5, in custom trm_view at level 5, format "`[ s ] t").
Notation "'V' x" := (Var_trm x) (x constr at level 0, in custom trm_view at level 5).
Notation "'F' f ts" := (Fun_trm f ts) (f constr, ts custom trms_view at level 0, in custom trm_view at level 5).
Notation "'C' c" := (Con_trm c) (c constr, in custom trm_view at level 5).
Notation "t" := t (t ident, in custom trm_view at level 0).
Notation "'(' t ')'" := t (t custom trm_view at level 5, no associativity, in custom trm_view at level 0).

#[global] Bind Scope trms_scope with trms.
Notation "'`[' s ']' ts" := (subst_trms s ts) (s custom subst_view at level 10, ts custom trms_view at level 5, in custom trms_view at level 5, format "`[ s ] ts").
Notation "'[' ']'" := (O_trms) (no associativity, in custom trms_view at level 0).
Notation "t '::' ts" := (S_trms _ t ts) (right associativity, t custom trm_view, ts custom trms_view, in custom trms_view at level 5).
Notation "ts" := ts (ts ident, in custom trms_view at level 0).
Notation "'(' ts ')'" := ts (ts custom trms_view at level 5, no associativity, in custom trms_view at level 0).

#[global] Bind Scope frm_scope with frm.
Notation "'`[' s ']' p" := (subst_frm s p) (s custom subst_view at level 10, p custom frm_view at level 0, in custom frm_view at level 10, format "`[ s ] p").
Notation "'`(' p ')' '[' 'V' x := t ']'" := (subst1 x t p) (x constr, t custom trm_view at level 10, p custom frm_view at level 7, in custom frm_view at level 10, format "`( p ) [  V  x  :=  t  ]").
Notation "'⊥'" := (Bot_frm) (in custom frm_view at level 0).
Notation "t1 '=' t2" := (Eqn_frm t1 t2) (t1 custom trm_view at level 5, t2 custom trm_view at level 5, in custom frm_view at level 6).
Notation "'¬' p" := (Neg_frm p) (p custom frm_view at level 7, in custom frm_view at level 7).
Notation "'∀' 'V' x ',' p" := (All_frm x p) (x constr at level 0, p custom frm_view at level 7, in custom frm_view at level 7).
Notation "'∃' 'V' x ',' p" := (Exs_frm x p) (x constr at level 0, p custom frm_view at level 7, in custom frm_view at level 7).
Notation "p '∧' q" := (Con_frm p q) (p custom frm_view, q custom frm_view, no associativity, in custom frm_view at level 8).
Notation "p '∨' q" := (Dis_frm p q) (p custom frm_view, q custom frm_view, no associativity, in custom frm_view at level 9).
Notation "p '→' q" := (Imp_frm p q) (p custom frm_view, q custom frm_view, no associativity, in custom frm_view at level 10).
Notation "p '↔' q" := (Iff_frm p q) (p custom frm_view, q custom frm_view, no associativity, in custom frm_view at level 10).
Notation "p" := p (p ident, in custom frm_view at level 0).
Notation "'(' p ')'" := p (p custom frm_view at level 10, no associativity, in custom frm_view at level 0).

Bind Scope subst_scope with subst.
Notation "s2 '∘' s1" := (subst_compose s1 s2) (right associativity, in custom subst_view at level 4) : subst_scope.
Notation "s ';' t '/' 'V' x" := (cons_subst x t s) (left associativity, x constr at level 0, t custom trm_view at level 5, in custom subst_view at level 10).
Notation "t '/' 'V' x" := (one_subst x t) (no associativity, x constr at level 0, t custom trm_view at level 5, in custom subst_view at level 10).
Notation "'ι'" := (nil_subst) (no associativity, in custom subst_view at level 0).

Notation "p '≡α' q" := (alpha_equiv p q) (no associativity, at level 70) : type_scope.

End FolViewer.

Module Example1.

Import FolViewer.

Variant L_in_relation_symbols : Set :=
  | symbol_IN : L_in_relation_symbols.

Definition L_in : language :=
  {|
    function_symbols := Empty_set;
    relation_symbols := L_in_relation_symbols;
    constant_symbols := Empty_set;
    function_arity_table := Empty_set_rect (fun _ => nat);
    relation_arity_table := fun _ => 2;
    function_arity_gt_0 := Empty_set_ind _;
    relation_arity_gt_0 := fun _ => (@le_S 1 1 (@le_n 1));
  |}.

Notation "t1 '∈' t2" := (@Rel_frm L_in symbol_IN (@S_trms L_in 1 t1 (@S_trms L_in 0 t2 (@O_trms L_in)))) (t1 custom trm_view at level 5, t2 custom trm_view at level 5, in custom frm_view at level 6).

Example fol_viewer_example1
  : $`[V 0 / V 1](∀ V 0, V 0 ∈ V 1)$ = $∀ V 1, V 1 ∈ V 0$.
Proof.
  reflexivity.
Qed.

Example fol_viewer_example2
  : $`(∀ V 0, V 0 ∈ V 1)[ V 1 := V 0 ]$ = $∀ V 2, V 2 ∈ V 0$.
Proof.
  rewrite subst1_unfold. simpl.
  replace (is_free_in_trm 0 (Var_trm 0)) with true by reflexivity.
  replace (fresh_var 1 (Var_trm 0) $V 0 ∈ V 1$) with 2 by reflexivity.
  rewrite subst1_unfold. f_equal.
  rewrite subst1_unfold. reflexivity.
Qed.

End Example1.
