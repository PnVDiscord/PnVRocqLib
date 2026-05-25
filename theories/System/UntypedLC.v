Require Import PnV.Prelude.Prelude.

Module AbelChapter3.

Import ListNotations.

#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "\subseteq" := E.isSubsetOf : type_scope.

Inductive exp : Set :=
  | EVar (i : nat)
  | ELam (t : exp)
  | EApp (r : exp) (s : exp)
  | ESub (t : exp) (sigma : subst)
with subst : Set :=
  | SShift
  | SId
  | SComp (sigma : subst) (tau : subst)
  | SCons (sigma : subst) (s : exp).

Inductive ne : Set :=
  | NeVar (i : nat)
  | NeApp (u : ne) (v : nf)
with nf : Set :=
  | NfNe (u : ne)
  | NfLam (v : nf).

Inductive val : Set :=
  | VClos (t : exp) (rho : list val)
  | VNeu (e : neu)
with neu : Set :=
  | NLevel (k : nat)
  | NApp (e : neu) (d : val).

Definition env : Set :=
  list val.

Inductive env_lookup {A : Type} : list A -> nat -> A -> Prop :=
  | EnvLookup_here (rho : list A) (a : A)
    : env_lookup (a :: rho) O a
  | EnvLookup_there (rho : list A) (a : A) (b : A) (i : nat)
    (LOOKUP : env_lookup rho i a)
    : env_lookup (b :: rho) (S i) a.

Inductive app : val -> val -> val -> Prop :=
  | App_clos (t : exp) (rho : env) (a : val) (b : val)
    (EVAL : eval (a :: rho) t b)
    : app (VClos t rho) a b
  | App_neu (e : neu) (a : val)
    : app (VNeu e) a (VNeu (NApp e a))
with eval : env -> exp -> val -> Prop :=
  | Eval_var (rho : env) (i : nat) (a : val)
    (LOOKUP : env_lookup rho i a)
    : eval rho (EVar i) a
  | Eval_lam (rho : env) (t : exp)
    : eval rho (ELam t) (VClos t rho)
  | Eval_app (rho : env) (r : exp) (s : exp) (f : val) (a : val) (b : val)
    (EVAL1 : eval rho r f)
    (EVAL2 : eval rho s a)
    (APP : app f a b)
    : eval rho (EApp r s) b
  | Eval_sub (rho : env) (t : exp) (sigma : subst) (rho' : env) (a : val)
    (ESUBST : eval_subst rho sigma rho')
    (EVAL : eval rho' t a)
    : eval rho (ESub t sigma) a
with eval_subst : env -> subst -> env -> Prop :=
  | EvalSubst_shift (rho : env) (a : val)
    : eval_subst (a :: rho) SShift rho
  | EvalSubst_id (rho : env)
    : eval_subst rho SId rho
  | EvalSubst_comp (rho : env) (sigma : subst) (tau : subst) (rho' : env) (rho'' : env)
    (EVAL2 : eval_subst rho tau rho')
    (EVAL1 : eval_subst rho' sigma rho'')
    : eval_subst rho (SComp sigma tau) rho''
  | EvalSubst_cons (rho : env) (sigma : subst) (s : exp) (rho' : env) (a : val)
    (ESUBST : eval_subst rho sigma rho')
    (EVAL : eval rho s a)
    : eval_subst rho (SCons sigma s) (a :: rho').

Inductive read_nf : nat -> val -> nf -> Prop :=
  | Read_clos (n : nat) (t : exp) (rho : env) (b : val) (v : nf)
    (EVAL : eval (VNeu (NLevel n) :: rho) t b)
    (READ : read_nf (S n) b v)
    : read_nf n (VClos t rho) (NfLam v)
  | Read_neu (n : nat) (e : neu) (u : ne)
    (READ : read_ne n e u)
    : read_nf n (VNeu e) (NfNe u)
with read_ne : nat -> neu -> ne -> Prop :=
  | Read_level (n : nat) (k : nat)
    : read_ne n (NLevel k) (NeVar (n - S k))
  | Read_app (n : nat) (e : neu) (d : val) (u : ne) (v : nf)
    (READ1 : read_ne n e u)
    (READ2 : read_nf n d v)
    : read_ne n (NApp e d) (NeApp u v).

#[local] Hint Constructors env_lookup app eval eval_subst read_nf read_ne : core.

Fixpoint initial_env (n : nat) : env :=
  match n with
  | O => []
  | S n => VNeu (NLevel n) :: initial_env n
  end.

Lemma env_lookup_initial_env (n : nat) (i : nat)
  (LT : i < n)
  : env_lookup (initial_env n) i (VNeu (NLevel (n - S i))).
Proof.
  revert i LT. induction n as [ | n IH]; intros i LT; simpl in *; try lia.
  destruct i as [ | i].
  - replace (n - O) with n by lia. econs.
  - replace (n - S i) with (n - S i) by lia.
    econs. eapply IH. lia.
Qed.

Definition nbe (n : nat) (t : exp) (v : nf) : Prop :=
  exists d, eval (initial_env n) t d /\ read_nf n d v.

Definition readable_val : ensemble val :=
  fun d => forall n, exists v, read_nf n d v.

Definition readable_neu : ensemble neu :=
  fun e => forall n, exists u, read_ne n e u.

Definition readable_neu_val : ensemble val :=
  fun d => exists e, d = VNeu e /\ e \in readable_neu.

Lemma readable_level (k : nat)
  : NLevel k \in readable_neu.
Proof.
  intros n. exists (NeVar (n - S k)). eauto.
Qed.

Lemma readable_neutral_value
  : readable_neu_val \subseteq readable_val.
Proof.
  intros d (e & ? & READABLE) n; subst d.
  pose proof (READABLE n) as (u & READ).
  exists (NfNe u). eauto.
Qed.

Lemma readable_app (e : neu) (d : val)
  (READABLE1 : e \in readable_neu)
  (READABLE2 : d \in readable_val)
  : NApp e d \in readable_neu.
Proof.
  intros n. pose proof (READABLE1 n) as (u & READ1).
  pose proof (READABLE2 n) as (v & READ2).
  exists (NeApp u v). eauto.
Qed.

Definition single_subst (s : exp) : subst :=
  SCons SId s.

Lemma eval_single_subst (rho : env) (t : exp) (s : exp) (a : val) (b : val)
  (EVALS : eval rho s a)
  (EVALT : eval (a :: rho) t b)
  : eval rho (ESub t (single_subst s)) b.
Proof.
  unfold single_subst.
  eapply Eval_sub with (rho' := a :: rho).
  - eapply EvalSubst_cons with (rho' := rho); eauto.
  - exact EVALT.
Qed.

Lemma eval_beta_intro (rho : env) (t : exp) (s : exp) (a : val) (b : val)
  (EVALS : eval rho s a)
  (EVALT : eval (a :: rho) t b)
  : eval rho (EApp (ELam t) s) b.
Proof.
  eapply Eval_app with (f := VClos t rho) (a := a).
  - eauto.
  - exact EVALS.
  - eapply App_clos. exact EVALT.
Qed.

Theorem beta_explicit_subst (rho : env) (t : exp) (s : exp) (b : val)
  : eval rho (EApp (ELam t) s) b <-> eval rho (ESub t (single_subst s)) b.
Proof.
  split; intros H_eval.
  - inversion H_eval; subst. inversion EVAL1; subst. inversion APP; subst.
    eapply eval_single_subst; eauto.
  - unfold single_subst in H_eval. inversion H_eval; subst.
    inversion ESUBST; subst. inversion ESUBST0; subst.
    eapply eval_beta_intro; eauto.
Qed.

Lemma eval_shift (rho : env) (a : val)
  : eval_subst (a :: rho) SShift rho.
Proof.
  eauto.
Qed.

Lemma eval_id (rho : env)
  : eval_subst rho SId rho.
Proof.
  eauto.
Qed.

Lemma eval_comp (rho : env) (sigma : subst) (tau : subst) (rho' : env) (rho'' : env)
  (EVAL2 : eval_subst rho tau rho')
  (EVAL1 : eval_subst rho' sigma rho'')
  : eval_subst rho (SComp sigma tau) rho''.
Proof.
  eauto.
Qed.

Lemma eval_cons (rho : env) (sigma : subst) (s : exp) (rho' : env) (a : val)
  (ESUBST : eval_subst rho sigma rho')
  (EVAL : eval rho s a)
  : eval_subst rho (SCons sigma s) (a :: rho').
Proof.
  eauto.
Qed.

Lemma eval_sub_intro (rho : env) (t : exp) (sigma : subst) (rho' : env) (a : val)
  (ESUBST : eval_subst rho sigma rho')
  (EVAL : eval rho' t a)
  : eval rho (ESub t sigma) a.
Proof.
  eauto.
Qed.

Lemma read_closure_intro (n : nat) (t : exp) (rho : env) (b : val) (v : nf)
  (EVAL : eval (VNeu (NLevel n) :: rho) t b)
  (READ : read_nf (S n) b v)
  : read_nf n (VClos t rho) (NfLam v).
Proof.
  eauto.
Qed.

Lemma nbe_intro (n : nat) (t : exp) (d : val) (v : nf)
  (EVAL : eval (initial_env n) t d)
  (READ : read_nf n d v)
  : nbe n t v.
Proof.
  exists d. eauto.
Qed.

Lemma env_lookup_functional (A : Type) (rho : list A) (i : nat) (a1 : A)
  (LOOKUP1 : env_lookup rho i a1)
  : forall a2 : A, env_lookup rho i a2 -> a1 = a2.
Proof.
  induction LOOKUP1; intros a2 LOOKUP2; inv LOOKUP2; eauto.
Qed.

Theorem app_functional (f : val) (a : val) (b1 : val)
  (APP1 : app f a b1)
  : forall b2 : val, app f a b2 -> b1 = b2
with eval_functional (rho : env) (t : exp) (a1 : val)
  (EVAL1 : eval rho t a1)
  : forall a2 : val, eval rho t a2 -> a1 = a2
with eval_subst_functional (rho : env) (sigma : subst) (rho1 : env)
  (EVAL1 : eval_subst rho sigma rho1)
  : forall rho2 : env, eval_subst rho sigma rho2 -> rho1 = rho2.
Proof.
  - destruct APP1; intros b2 APP2; inv APP2.
    + eapply eval_functional; eauto.
    + reflexivity.
  - destruct EVAL1; intros a2 EVAL2'; inv EVAL2'.
    + eapply env_lookup_functional; eauto.
    + reflexivity.
    + match goal with
      | [ H : eval rho r ?f' |- _ ] => assert (EQ_f : f = f') by (eapply eval_functional; eauto); subst f'
      end.
      match goal with
      | [ H : eval rho s ?a' |- _ ] => assert (EQ_a : a = a') by (eapply eval_functional; eauto); subst a'
      end.
      eapply app_functional; eauto.
    + match goal with
      | [ H : eval_subst rho sigma ?rho'' |- _ ] => assert (EQ_rho : rho' = rho'') by (eapply eval_subst_functional; eauto); subst rho''
      end.
      eapply eval_functional; eauto.
  - destruct EVAL1; intros rho2 EVAL2'; inv EVAL2'.
    + reflexivity.
    + reflexivity.
    + match goal with
      | [ H : eval_subst rho tau ?rho0 |- _ ] => assert (EQ_rho : rho' = rho0) by (eapply eval_subst_functional; eauto); subst rho0
      end.
      eapply eval_subst_functional; eauto.
    + match goal with
      | [ H : eval_subst rho sigma ?rho0 |- _ ] => assert (EQ_rho : rho' = rho0) by (eapply eval_subst_functional; eauto); subst rho0
      end.
      match goal with
      | [ H : eval rho s ?a' |- _ ] => assert (EQ_a : a = a') by (eapply eval_functional; eauto); subst a'
      end.
      reflexivity.
Qed.

Theorem read_nf_functional (n : nat) (d : val) (v1 : nf)
  (READ1 : read_nf n d v1)
  : forall v2 : nf, read_nf n d v2 -> v1 = v2
with read_ne_functional (n : nat) (e : neu) (u1 : ne)
  (READ1 : read_ne n e u1)
  : forall u2 : ne, read_ne n e u2 -> u1 = u2.
Proof.
  - destruct READ1; intros v2 READ_OTHER; inv READ_OTHER.
    + match goal with
      | [ H : eval (VNeu (NLevel n) :: rho) t ?b' |- _ ] => assert (EQ_b : b = b') by (eapply eval_functional; eauto); subst b'
      end.
      f_equal. eapply read_nf_functional; eauto.
    + f_equal. eapply read_ne_functional; eauto.
  - destruct READ1; intros u2 READ_OTHER; inv READ_OTHER.
    + reflexivity.
    + match goal with
      | [ H : read_ne n e ?u' |- _ ] => assert (EQ_u : u = u') by (eapply read_ne_functional; eauto); subst u'
      end.
      match goal with
      | [ H : read_nf n d ?v' |- _ ] => assert (EQ_v : v = v') by (eapply read_nf_functional; eauto); subst v'
      end.
      reflexivity.
Qed.

Theorem nbe_functional (n : nat) (t : exp) (v1 : nf)
  (NBE1 : nbe n t v1)
  : forall v2 : nf, nbe n t v2 -> v1 = v2.
Proof.
  intros v2 (d2 & EVAL2 & READ2).
  destruct NBE1 as (d1 & EVAL1 & READ1).
  assert (EQ_d : d1 = d2) by (eapply eval_functional; eauto).
  subst d2. eapply read_nf_functional; eauto.
Qed.

Lemma eval_subst_single_inv (rho : env) (s : exp) (rho' : env)
  (ESUBST : eval_subst rho (single_subst s) rho')
  : exists a : val, eval rho s a /\ rho' = a :: rho.
Proof.
  unfold single_subst in ESUBST. inv ESUBST. inv ESUBST0.
  exists a. eauto.
Qed.

Lemma eval_subst_comp_inv (rho : env) (sigma : subst) (tau : subst) (rho'' : env)
  (ESUBST : eval_subst rho (SComp sigma tau) rho'')
  : exists rho' : env, eval_subst rho tau rho' /\ eval_subst rho' sigma rho''.
Proof.
  inv ESUBST. exists rho'. eauto.
Qed.

Theorem nbe_beta_explicit_subst (n : nat) (t : exp) (s : exp) (v : nf)
  : nbe n (EApp (ELam t) s) v <-> nbe n (ESub t (single_subst s)) v.
Proof.
  split; intros [d [EVAL READ]]; exists d; split; eauto.
  - exact (proj1 (beta_explicit_subst (initial_env n) t s d) EVAL).
  - exact (proj2 (beta_explicit_subst (initial_env n) t s d) EVAL).
Qed.

Lemma eval_initial_var (n : nat) (i : nat)
  (LT : i < n)
  : eval (initial_env n) (EVar i) (VNeu (NLevel (n - S i))).
Proof.
  eauto using env_lookup_initial_env.
Qed.

Lemma read_initial_level (n : nat) (i : nat)
  (LT : i < n)
  : read_ne n (NLevel (n - S i)) (NeVar i).
Proof.
  assert (EQ_i : NeVar i = NeVar (n - S (n - S i))) by (f_equal; lia).
  rewrite EQ_i. eapply Read_level.
Qed.

Lemma read_fresh_level (n : nat)
  : read_ne (S n) (NLevel n) (NeVar O).
Proof.
  assert (EQ_i : NeVar O = NeVar (S n - S n)) by (f_equal; lia).
  rewrite EQ_i. eapply Read_level.
Qed.

Lemma nbe_var (n : nat) (i : nat)
  (LT : i < n)
  : nbe n (EVar i) (NfNe (NeVar i)).
Proof.
  exists (VNeu (NLevel (n - S i))). split.
  - eauto using eval_initial_var.
  - eauto using read_initial_level.
Qed.

Theorem nbe_identity (n : nat)
  : nbe n (ELam (EVar O)) (NfLam (NfNe (NeVar O))).
Proof.
  exists (VClos (EVar O) (initial_env n)). split.
  - eauto.
  - eapply Read_clos with (b := VNeu (NLevel n)).
    + eauto.
    + eauto using read_fresh_level.
Qed.

Corollary nbe_closed_identity
  : nbe O (ELam (EVar O)) (NfLam (NfNe (NeVar O))).
Proof.
  eapply nbe_identity.
Qed.

Theorem nbe_app_vars (n : nat) (i : nat) (j : nat)
  (LT_i : i < n)
  (LT_j : j < n)
  : nbe n (EApp (EVar i) (EVar j))
      (NfNe (NeApp (NeVar i) (NfNe (NeVar j)))).
Proof.
  exists (VNeu (NApp (NLevel (n - S i)) (VNeu (NLevel (n - S j))))).
  split.
  - eapply Eval_app with (f := VNeu (NLevel (n - S i))) (a := VNeu (NLevel (n - S j))).
    + eauto using eval_initial_var.
    + eauto using eval_initial_var.
    + eauto.
  - eapply Read_neu. eapply Read_app.
    + eauto using read_initial_level.
    + eauto using read_initial_level.
Qed.

Theorem nbe_identity_app_var (n : nat) (i : nat)
  (LT : i < n)
  : nbe n (EApp (ELam (EVar O)) (EVar i)) (NfNe (NeVar i)).
Proof.
  enough (NBE_SUB : nbe n (ESub (EVar O) (single_subst (EVar i))) (NfNe (NeVar i))).
  { exact (proj2 (nbe_beta_explicit_subst n (EVar O) (EVar i) (NfNe (NeVar i))) NBE_SUB). }
  exists (VNeu (NLevel (n - S i))). split.
  - eapply Eval_sub with (rho' := VNeu (NLevel (n - S i)) :: initial_env n).
    + eapply EvalSubst_cons with (rho' := initial_env n).
      * eauto.
      * eauto using eval_initial_var.
    + eauto.
  - eauto using read_initial_level.
Qed.

Inductive typ : Set :=
  | TyBase
  | TyArr (T_dom : typ) (T_cod : typ).

Definition ctx : Set :=
  list typ.

Fixpoint lookup_ctx (Gamma : ctx) (i : nat) : option typ :=
  match Gamma, i with
  | [], _ => None
  | T :: _, O => Some T
  | _ :: Gamma, S i => lookup_ctx Gamma i
  end.

Lemma lookup_ctx_lt (Gamma : ctx) (i : nat) (T : typ)
  (LOOKUP : lookup_ctx Gamma i = Some T)
  : i < length Gamma.
Proof.
  revert i T LOOKUP. induction Gamma as [ | S Gamma IH]; intros i T LOOKUP; simpl in *.
  - destruct i; congruence.
  - destruct i as [ | i]; simpl in *.
    + lia.
    + specialize (IH i T LOOKUP). lia.
Qed.

Definition function_space (A : ensemble val) (B : ensemble val) : ensemble val :=
  fun f => forall a : val, a \in A -> (exists b : val, app f a b /\ b \in B).

Definition is_candidate (A : ensemble val) : Prop :=
  readable_neu_val \subseteq A /\ A \subseteq readable_val.

Lemma readable_val_candidate
  : is_candidate readable_val.
Proof.
  split.
  - eapply readable_neutral_value.
  - intros d READABLE. exact READABLE.
Qed.

Lemma read_nf_neu_inv (n : nat) (e : neu) (v : nf)
  (READ : read_nf n (VNeu e) v)
  : exists u : ne, v = NfNe u /\ read_ne n e u.
Proof.
  inv READ. eauto.
Qed.

Lemma read_ne_app_inv (n : nat) (e : neu) (d : val) (u : ne)
  (READ : read_ne n (NApp e d) u)
  : exists u' : ne, exists v : nf, u = NeApp u' v /\ read_ne n e u' /\ read_nf n d v.
Proof.
  inv READ. eauto.
Qed.

Lemma function_space_candidate (A : ensemble val) (B : ensemble val)
  (CAND_A : is_candidate A)
  (CAND_B : is_candidate B)
  : is_candidate (function_space A B).
Proof.
  destruct CAND_A as [A_LOW A_HIGH].
  destruct CAND_B as [B_LOW B_HIGH].
  split.
  - intros f (e & ? & READABLE) a A_a; subst f.
    exists (VNeu (NApp e a)). split.
    + eauto.
    + eapply B_LOW. exists (NApp e a). split.
      * reflexivity.
      * eapply readable_app.
        { exact READABLE. }
        { eapply A_HIGH. exact A_a. }
  - intros f F n.
    assert (A_arg : VNeu (NLevel n) \in A).
    { eapply A_LOW. exists (NLevel n). split; eauto using readable_level. }
    pose proof (F (VNeu (NLevel n)) A_arg) as [b [APP B_b]].
    inversion APP; subst.
    + pose proof (B_HIGH b B_b (S n)) as [v READ]. exists (NfLam v). eauto.
    + pose proof (B_HIGH (VNeu (NApp e (VNeu (NLevel n)))) B_b n) as [v READ].
      pose proof (read_nf_neu_inv n (NApp e (VNeu (NLevel n))) v READ) as [u [-> READ_NE]].
      pose proof (read_ne_app_inv n e (VNeu (NLevel n)) u READ_NE) as [u' [v' [-> [READ_E READ_ARG]]]].
      exists (NfNe u'). eauto.
Qed.

Fixpoint sem_type (T : typ) : ensemble val :=
  match T with
  | TyBase => readable_val
  | TyArr T_dom T_cod => function_space (sem_type T_dom) (sem_type T_cod)
  end.

Theorem sem_type_candidate (T : typ)
  : is_candidate (sem_type T).
Proof.
  induction T as [ | T_dom IH_dom T_cod IH_cod]; simpl.
  - eapply readable_val_candidate.
  - eapply function_space_candidate; eauto.
Qed.

Inductive typing : ctx -> exp -> typ -> Prop :=
  | Ty_var (Gamma : ctx) (i : nat) (T : typ)
    (LOOKUP : lookup_ctx Gamma i = Some T)
    : typing Gamma (EVar i) T
  | Ty_lam (Gamma : ctx) (T_dom : typ) (T_cod : typ) (t : exp)
    (TYPING : typing (T_dom :: Gamma) t T_cod)
    : typing Gamma (ELam t) (TyArr T_dom T_cod)
  | Ty_app (Gamma : ctx) (r : exp) (s : exp) (T_dom : typ) (T_cod : typ)
    (TYPING1 : typing Gamma r (TyArr T_dom T_cod))
    (TYPING2 : typing Gamma s T_dom)
    : typing Gamma (EApp r s) T_cod
  | Ty_sub (Gamma : ctx) (Delta : ctx) (t : exp) (sigma : subst) (T : typ)
    (TYPING : typing Delta t T)
    (SUBST : subst_typing Gamma sigma Delta)
    : typing Gamma (ESub t sigma) T
with subst_typing : ctx -> subst -> ctx -> Prop :=
  | STy_shift (Gamma : ctx) (T_head : typ)
    : subst_typing (T_head :: Gamma) SShift Gamma
  | STy_id (Gamma : ctx)
    : subst_typing Gamma SId Gamma
  | STy_comp (Gamma1 : ctx) (Gamma2 : ctx) (Gamma3 : ctx) (sigma : subst) (tau : subst)
    (TYPING2 : subst_typing Gamma1 tau Gamma2)
    (TYPING1 : subst_typing Gamma2 sigma Gamma3)
    : subst_typing Gamma1 (SComp sigma tau) Gamma3
  | STy_cons (Gamma : ctx) (Delta : ctx) (sigma : subst) (s : exp) (T_head : typ)
    (SUBST : subst_typing Gamma sigma Delta)
    (TYPING : typing Gamma s T_head)
    : subst_typing Gamma (SCons sigma s) (T_head :: Delta).

#[local] Hint Constructors typing subst_typing : core.

Definition env_in (rho : env) (Gamma : ctx) : Prop :=
  forall i : nat, forall T : typ, lookup_ctx Gamma i = Some T -> (exists d : val, env_lookup rho i d /\ d \in sem_type T).

Lemma env_in_cons (rho : env) (Gamma : ctx) (a : val) (T : typ)
  (A : a \in sem_type T)
  (ENV : env_in rho Gamma)
  : env_in (a :: rho) (T :: Gamma).
Proof.
  intros i U LOOKUP. destruct i as [ | i]; simpl in LOOKUP.
  - inversion LOOKUP; subst. exists a. eauto.
  - pose proof (ENV i U LOOKUP) as (d & LOOKUP_D & D). exists d. eauto.
Qed.

Lemma env_in_cons_inv (rho : env) (Gamma : ctx) (T : typ)
  (ENV : env_in rho (T :: Gamma))
  : exists a : val, exists rho' : env, rho = a :: rho' /\ a \in sem_type T /\ env_in rho' Gamma.
Proof.
  pose proof (ENV O T eq_refl) as [a [LOOKUP A]].
  destruct rho as [ | a' rho']; inv LOOKUP.
  exists a. exists rho'. splits; eauto.
  intros i U LOOKUP_U.
  pose proof (ENV (S i) U LOOKUP_U) as [d [LOOKUP_D D]].
  inv LOOKUP_D. exists d. eauto.
Qed.

Theorem env_in_initial_env (Gamma : ctx)
  : env_in (initial_env (length Gamma)) Gamma.
Proof.
  intros i T LOOKUP.
  exists (VNeu (NLevel (length Gamma - S i))). split.
  - eapply env_lookup_initial_env. eapply lookup_ctx_lt; eauto.
  - pose proof (sem_type_candidate T) as [LOW HIGH].
    eapply LOW. exists (NLevel (length Gamma - S i)).
    split; eauto using readable_level.
Qed.

Definition sem_typing (Gamma : ctx) (t : exp) (T : typ) : Prop :=
  forall rho : env, env_in rho Gamma -> (exists d : val, eval rho t d /\ d \in sem_type T).

Definition sem_subst_typing (Gamma : ctx) (sigma : subst) (Delta : ctx) : Prop :=
  forall rho : env, env_in rho Gamma -> (exists rho' : env, eval_subst rho sigma rho' /\ env_in rho' Delta).

Theorem typing_sound (Gamma : ctx) (t : exp) (T : typ)
  (TYPING : typing Gamma t T)
  : sem_typing Gamma t T
with subst_typing_sound (Gamma : ctx) (sigma : subst) (Delta : ctx)
  (TYPING : subst_typing Gamma sigma Delta)
  : sem_subst_typing Gamma sigma Delta.
Proof.
  - induction TYPING; intros rho ENV.
    + pose proof (ENV i T LOOKUP) as [d [LOOKUP_D D]].
      exists d. eauto.
    + exists (VClos t rho). split; eauto. simpl.
      intros a A.
      pose proof (IHTYPING (a :: rho) (env_in_cons rho Gamma a T_dom A ENV)) as [b [EVAL B]].
      exists b. eauto.
    + pose proof (IHTYPING1 rho ENV) as [f [EVAL1 F]].
      pose proof (IHTYPING2 rho ENV) as [a [EVAL2 A]].
      pose proof (F a A) as [b [APP B]].
      exists b. eauto.
    + pose proof (subst_typing_sound Gamma sigma Delta SUBST rho ENV) as [rho' [ESUBST ENV']].
      pose proof (IHTYPING rho' ENV') as [d [EVAL D]].
      exists d. eauto.
  - induction TYPING; intros rho ENV.
    + pose proof (env_in_cons_inv rho Gamma T_head ENV) as [a [rho' [-> [A ENV']]]].
      exists rho'. eauto.
    + exists rho. eauto.
    + pose proof (subst_typing_sound Gamma1 tau Gamma2 TYPING1 rho ENV) as [rho' [ESUBST1 ENV1]].
      pose proof (subst_typing_sound Gamma2 sigma Gamma3 TYPING2 rho' ENV1) as [rho'' [ESUBST2 ENV2]].
      exists rho''. eauto.
    + match goal with
      | [ IH : sem_subst_typing Gamma sigma Delta |- _ ] => pose proof (IH rho ENV) as [rho' [ESUBST ENV']]
      end.
      match goal with
      | [ H : typing Gamma s T_head |- _ ] => pose proof (typing_sound Gamma s T_head H rho ENV) as [a [EVAL A]]
      end.
      exists (a :: rho'). split; eauto using env_in_cons.
Qed.

Theorem type_assignment_normalizes (Gamma : ctx) (t : exp) (T : typ)
  (TYPING : typing Gamma t T)
  : exists v : nf, nbe (length Gamma) t v.
Proof.
  pose proof (typing_sound Gamma t T TYPING (initial_env (length Gamma)) (env_in_initial_env Gamma)) as [d [EVAL D]].
  pose proof (sem_type_candidate T) as [LOW HIGH].
  pose proof (HIGH d D (length Gamma)) as [v READ].
  exists v. exists d. eauto.
Qed.

Definition sem_value_eq (T : typ) (d : val) (d' : val) : Prop :=
  d = d' /\ d \in sem_type T /\ d' \in sem_type T.

Definition sem_term_eq (Gamma : ctx) (t : exp) (t' : exp) (T : typ) : Prop :=
  forall rho : env, env_in rho Gamma -> forall d : val, forall d' : val, eval rho t d -> eval rho t' d' -> sem_value_eq T d d'.

Definition sem_subst_eq (Gamma : ctx) (sigma : subst) (sigma' : subst) (Delta : ctx) : Prop :=
  forall rho : env, env_in rho Gamma -> forall rho1 : env, forall rho2 : env, eval_subst rho sigma rho1 -> eval_subst rho sigma' rho2 -> rho1 = rho2 /\ env_in rho1 Delta /\ env_in rho2 Delta.

Theorem sem_term_eq_refl (Gamma : ctx) (t : exp) (T : typ)
  (TYPING : typing Gamma t T)
  : sem_term_eq Gamma t t T.
Proof.
  intros rho ENV d d' EVAL EVAL'.
  pose proof (typing_sound Gamma t T TYPING rho ENV) as [d0 [EVAL0 D0]].
  assert (EQ1 : d = d0) by (eapply eval_functional; eauto).
  assert (EQ2 : d' = d0) by (eapply eval_functional; eauto).
  subst d. subst d'. repeat split; eauto.
Qed.

Theorem sem_subst_eq_refl (Gamma : ctx) (sigma : subst) (Delta : ctx)
  (TYPING : subst_typing Gamma sigma Delta)
  : sem_subst_eq Gamma sigma sigma Delta.
Proof.
  intros rho ENV rho1 rho2 EVAL1 EVAL2.
  pose proof (subst_typing_sound Gamma sigma Delta TYPING rho ENV) as [rho0 [EVAL0 ENV0]].
  assert (EQ1 : rho1 = rho0) by (eapply eval_subst_functional; eauto).
  assert (EQ2 : rho2 = rho0) by (eapply eval_subst_functional; eauto).
  subst rho1. subst rho2. repeat split; eauto.
Qed.

Theorem beta_semantic_equality (Gamma : ctx) (t : exp) (s : exp) (T_dom : typ) (T_cod : typ)
  (TYPING1 : typing (T_dom :: Gamma) t T_cod)
  (TYPING2 : typing Gamma s T_dom)
  : sem_term_eq Gamma (EApp (ELam t) s) (ESub t (single_subst s)) T_cod.
Proof.
  intros rho ENV d d' EVAL EVAL'.
  assert (EVAL_SUB : eval rho (ESub t (single_subst s)) d).
  { eapply beta_explicit_subst. exact EVAL. }
  pose proof (eval_functional rho (ESub t (single_subst s)) d EVAL_SUB d' EVAL') as EQ.
  pose proof (typing_sound Gamma (EApp (ELam t) s) T_cod (Ty_app Gamma (ELam t) s T_dom T_cod (Ty_lam Gamma T_dom T_cod t TYPING1) TYPING2) rho ENV) as [d0 [EVAL0 D0]].
  pose proof (eval_functional rho (EApp (ELam t) s) d EVAL d0 EVAL0) as EQ0.
  subst d'. subst d0. repeat split; exact D0.
Qed.

Theorem sem_term_eq_sym (Gamma : ctx) (t : exp) (t' : exp) (T : typ)
  (EQ : sem_term_eq Gamma t t' T)
  : sem_term_eq Gamma t' t T.
Proof.
  intros rho ENV d d' EVAL EVAL'.
  pose proof (EQ rho ENV d' d EVAL' EVAL) as (? & ? & ?).
  subst d'. repeat split; eauto.
Qed.

Theorem sem_subst_eq_sym (Gamma : ctx) (sigma : subst) (sigma' : subst) (Delta : ctx)
  (EQ : sem_subst_eq Gamma sigma sigma' Delta)
  : sem_subst_eq Gamma sigma' sigma Delta.
Proof.
  intros rho ENV rho1 rho2 EVAL1 EVAL2.
  pose proof (EQ rho ENV rho2 rho1 EVAL2 EVAL1) as (? & ? & ?).
  subst rho2. repeat split; eauto.
Qed.

Theorem sem_term_eq_trans (Gamma : ctx) (t1 : exp) (t2 : exp) (t3 : exp) (T : typ)
  (TYPING2 : typing Gamma t2 T)
  (EQ12 : sem_term_eq Gamma t1 t2 T)
  (EQ23 : sem_term_eq Gamma t2 t3 T)
  : sem_term_eq Gamma t1 t3 T.
Proof.
  intros rho ENV d1 d3 EVAL1 EVAL3.
  pose proof (typing_sound Gamma t2 T TYPING2 rho ENV) as (d2 & EVAL2 & D2).
  pose proof (EQ12 rho ENV d1 d2 EVAL1 EVAL2) as (? & ? & ?).
  pose proof (EQ23 rho ENV d2 d3 EVAL2 EVAL3) as (? & ? & ?).
  subst d1. subst d3. repeat split; eauto.
Qed.

Theorem sem_subst_eq_trans (Gamma : ctx) (sigma1 : subst) (sigma2 : subst) (sigma3 : subst) (Delta : ctx)
  (TYPING2 : subst_typing Gamma sigma2 Delta)
  (EQ12 : sem_subst_eq Gamma sigma1 sigma2 Delta)
  (EQ23 : sem_subst_eq Gamma sigma2 sigma3 Delta)
  : sem_subst_eq Gamma sigma1 sigma3 Delta.
Proof.
  intros rho ENV rho1 rho3 EVAL1 EVAL3.
  pose proof (subst_typing_sound Gamma sigma2 Delta TYPING2 rho ENV) as (rho2 & EVAL2 & ENV2).
  pose proof (EQ12 rho ENV rho1 rho2 EVAL1 EVAL2) as (? & ? & ?).
  pose proof (EQ23 rho ENV rho2 rho3 EVAL2 EVAL3) as (? & ? & ?).
  subst rho1. subst rho3. repeat split; eauto.
Qed.

Theorem sem_term_eq_var (Gamma : ctx) (i : nat) (T : typ)
  (LOOKUP : lookup_ctx Gamma i = Some T)
  : sem_term_eq Gamma (EVar i) (EVar i) T.
Proof.
  eapply sem_term_eq_refl. eauto.
Qed.

Theorem sem_term_eq_app (Gamma : ctx) (r : exp) (r' : exp) (s : exp) (s' : exp) (T_dom : typ) (T : typ)
  (EQ1 : sem_term_eq Gamma r r' (TyArr T_dom T))
  (EQ2 : sem_term_eq Gamma s s' T_dom)
  : sem_term_eq Gamma (EApp r s) (EApp r' s') T.
Proof.
  intros rho ENV d d' EVAL EVAL'.
  inv EVAL. inv EVAL'.
  pose proof (EQ1 rho ENV f f0 EVAL1 EVAL0) as (? & F & ?).
  pose proof (EQ2 rho ENV a a0 EVAL2 EVAL3) as (? & A & ?).
  subst f0. subst a0.
  simpl in F. pose proof (F a A) as (b & APP_F & B).
  assert (EQ_b : b = d) by (eapply app_functional; eauto).
  assert (EQ_d : d = d') by (eapply app_functional; eauto).
  subst b. subst d'. repeat split; eauto.
Qed.

Theorem sem_term_eq_sub (Gamma : ctx) (Delta : ctx) (t : exp) (t' : exp) (sigma : subst) (sigma' : subst) (T : typ)
  (EQ1 : sem_subst_eq Gamma sigma sigma' Delta)
  (EQ2 : sem_term_eq Delta t t' T)
  : sem_term_eq Gamma (ESub t sigma) (ESub t' sigma') T.
Proof.
  intros rho ENV d d' EVAL EVAL'.
  inv EVAL. inv EVAL'.
  pose proof (EQ1 rho ENV rho' rho'0 ESUBST ESUBST0) as (? & ENV1 & ?).
  subst rho'0. eapply EQ2; eauto.
Qed.

Theorem sem_term_eq_sub_id (Gamma : ctx) (t : exp) (T : typ)
  (TYPING : typing Gamma t T)
  : sem_term_eq Gamma (ESub t SId) t T.
Proof.
  intros rho ENV d d' EVAL EVAL'.
  inv EVAL. inv ESUBST.
  assert (EQ_d : d = d') by (eapply eval_functional; eauto).
  pose proof (typing_sound Gamma t T TYPING _ ENV) as (d0 & EVAL0' & D0).
  assert (EQ_d0 : d = d0) by (eapply eval_functional; eauto).
  subst d'. subst d0. repeat split; eauto.
Qed.

Theorem sem_term_eq_shift_var (Gamma : ctx) (T_head : typ) (i : nat) (T : typ)
  (LOOKUP : lookup_ctx Gamma i = Some T)
  : sem_term_eq (T_head :: Gamma) (ESub (EVar i) SShift) (EVar (S i)) T.
Proof.
  intros rho ENV d d' EVAL EVAL'.
  inv EVAL. inv ESUBST. inv EVAL0. inv EVAL'.
  match goal with
  | [ H : env_lookup ?rho0 i d, H' : env_lookup ?rho1 (S i) d' |- _ ] => assert (LOOKUP_D : env_lookup rho1 (S i) d) by eauto; pose proof (env_lookup_functional val rho1 (S i) d' H' d LOOKUP_D) as EQ_d
  end.
  subst d'.
  pose proof (ENV (S i) T LOOKUP) as (d0 & LOOKUP_ENV & D).
  match goal with
  | [ H : env_lookup ?rho0 (S i) d |- _ ] => pose proof (env_lookup_functional val rho0 (S i) d H d0 LOOKUP_ENV) as EQ_d0
  end.
  subst d0. repeat split; eauto.
Qed.

Theorem sem_term_eq_cons_var_zero (Gamma : ctx) (Delta : ctx) (sigma : subst) (s : exp)
  (T_head : typ)
  (SUBST : subst_typing Gamma sigma Delta)
  (TYPING : typing Gamma s T_head)
  : sem_term_eq Gamma (ESub (EVar O) (SCons sigma s)) s T_head.
Proof.
  intros rho ENV d d' EVAL_SUB EVAL_S.
  inversion EVAL_SUB as [ | | | rho0 t0 sigma0 rho_sub d_sub ESUBST0 EVAL_VAR ]; subst; clear EVAL_SUB.
  inversion ESUBST0 as [ | | | rho1 sigma1 s1 rho_sigma a0 ESUBST1 EVAL_S0 ]; subst; clear ESUBST0.
  inversion EVAL_VAR; subst; clear EVAL_VAR.
  match goal with
  | [ H : env_lookup _ O d |- _ ] => inv H
  end.
  pose proof (eval_functional rho s d EVAL_S0 d' EVAL_S) as EQ_d.
  pose proof (typing_sound Gamma s T_head TYPING rho ENV) as (d0 & EVAL0 & D0).
  pose proof (eval_functional rho s d EVAL_S0 d0 EVAL0) as EQ_d0.
  subst d'. subst d0. repeat split; eauto.
Qed.

Theorem sem_term_eq_cons_var_succ (Gamma : ctx) (Delta : ctx) (sigma : subst) (s : exp)
  (i : nat) (T_head : typ) (T : typ)
  (SUBST : subst_typing Gamma sigma Delta)
  (TYPING : typing Gamma s T_head)
  (LOOKUP : lookup_ctx Delta i = Some T)
  : sem_term_eq Gamma (ESub (EVar (S i)) (SCons sigma s)) (ESub (EVar i) sigma) T.
Proof.
  intros rho ENV d d' EVAL_LEFT EVAL_RIGHT.
  inversion EVAL_LEFT as [ | | | rho_l t_l sigma_l rho_left d_l ESUBST_LEFT EVAL_VAR_LEFT ]; subst; clear EVAL_LEFT.
  inversion EVAL_RIGHT as [ | | | rho_r t_r sigma_r rho_right d_r ESUBST_RIGHT EVAL_VAR_RIGHT ]; subst; clear EVAL_RIGHT.
  inversion ESUBST_LEFT as [ | | | rho_c sigma_c s_c rho_sigma a_c ESUBST_SIGMA EVAL_S ]; subst; clear ESUBST_LEFT.
  inversion EVAL_VAR_LEFT; subst; clear EVAL_VAR_LEFT.
  match goal with
  | [ H : env_lookup (_ :: _) (S i) d |- _ ] => inv H
  end.
  inversion EVAL_VAR_RIGHT; subst; clear EVAL_VAR_RIGHT.
  pose proof (eval_subst_functional rho sigma rho_sigma ESUBST_SIGMA rho_right ESUBST_RIGHT) as ?.
  subst rho_right.
  pose proof (env_lookup_functional val rho_sigma i d LOOKUP1 d' LOOKUP0) as ?.
  pose proof (subst_typing_sound Gamma sigma Delta SUBST rho ENV) as (rho0 & ESUBST_T & ENV0).
  pose proof (eval_subst_functional rho sigma rho_sigma ESUBST_SIGMA rho0 ESUBST_T) as ?.
  subst rho0.
  pose proof (ENV0 i T LOOKUP) as (d0 & LOOKUP_D & D).
  pose proof (env_lookup_functional val rho_sigma i d LOOKUP1 d0 LOOKUP_D) as ?.
  subst d'. subst d0. repeat split; eauto.
Qed.

Theorem sem_term_eq_app_subst (Gamma : ctx) (Delta : ctx) (r : exp) (s : exp)
  (sigma : subst) (T_dom : typ) (T : typ)
  (SUBST : subst_typing Gamma sigma Delta)
  (TYPING1 : typing Delta r (TyArr T_dom T))
  (TYPING2 : typing Delta s T_dom)
  : sem_term_eq Gamma (ESub (EApp r s) sigma) (EApp (ESub r sigma) (ESub s sigma)) T.
Proof.
  intros rho ENV d d' EVAL_LEFT EVAL_RIGHT.
  inversion EVAL_LEFT as [ | | | rho_l t_l sigma_l rho_left d_l ESUBST_LEFT EVAL_APP_LEFT ]; subst; clear EVAL_LEFT.
  inversion EVAL_APP_LEFT as [ | | rho_app r_l s_l f_left a_left d_left EVAL_R_LEFT EVAL_S_LEFT APP_LEFT | ]; subst; clear EVAL_APP_LEFT.
  inversion EVAL_RIGHT as [ | | rho_r app_l app_r f_right a_right d_right EVAL_R_SUB EVAL_S_SUB APP_RIGHT | ]; subst; clear EVAL_RIGHT.
  inversion EVAL_R_SUB as [ | | | rho_rs t_rs sigma_rs rho_rsubst f_rsubst ESUBST_R EVAL_R_RIGHT ]; subst; clear EVAL_R_SUB.
  inversion EVAL_S_SUB as [ | | | rho_ss t_ss sigma_ss rho_ssubst a_ssubst ESUBST_S EVAL_S_RIGHT ]; subst; clear EVAL_S_SUB.
  pose proof (eval_subst_functional rho sigma rho_left ESUBST_LEFT rho_rsubst ESUBST_R) as ?.
  pose proof (eval_subst_functional rho sigma rho_left ESUBST_LEFT rho_ssubst ESUBST_S) as ?.
  subst rho_rsubst. subst rho_ssubst.
  pose proof (eval_functional rho_left r f_left EVAL_R_LEFT f_right EVAL_R_RIGHT) as ?.
  pose proof (eval_functional rho_left s a_left EVAL_S_LEFT a_right EVAL_S_RIGHT) as ?.
  subst f_right. subst a_right.
  pose proof (subst_typing_sound Gamma sigma Delta SUBST rho ENV) as (rho0 & ESUBST0 & ENV0).
  pose proof (eval_subst_functional rho sigma rho_left ESUBST_LEFT rho0 ESUBST0) as ?.
  subst rho0.
  pose proof (typing_sound Delta r (TyArr T_dom T) TYPING1 rho_left ENV0) as (f0 & EVAL_R & F).
  pose proof (eval_functional rho_left r f_left EVAL_R_LEFT f0 EVAL_R) as ?.
  subst f0. simpl in F.
  pose proof (typing_sound Delta s T_dom TYPING2 rho_left ENV0) as (a1 & EVAL_S & A).
  pose proof (eval_functional rho_left s a_left EVAL_S_LEFT a1 EVAL_S) as ?.
  subst a1. pose proof (F a_left A) as (b & APP0 & B).
  assert (EQ_b : b = d) by (eapply app_functional; eauto).
  assert (EQ_d : d = d') by (eapply app_functional; eauto).
  subst b. subst d'. repeat split; eauto.
Qed.

Theorem sem_term_eq_sub_comp (Gamma1 : ctx) (Gamma2 : ctx) (Gamma3 : ctx)
  (t : exp) (sigma : subst) (tau : subst) (T : typ)
  (TYPING : typing Gamma3 t T)
  (TYPING1 : subst_typing Gamma2 sigma Gamma3)
  (TYPING2 : subst_typing Gamma1 tau Gamma2)
  : sem_term_eq Gamma1 (ESub (ESub t sigma) tau) (ESub t (SComp sigma tau)) T.
Proof.
  intros rho ENV d d' EVAL_LEFT EVAL_RIGHT.
  inversion EVAL_LEFT as [ | | | rho_l t_l tau_l rho_tau d_l ESUBST_TAU EVAL_SUB_LEFT ]; subst; clear EVAL_LEFT.
  inversion EVAL_SUB_LEFT as [ | | | rho_sl t_sl sigma_l rho_sigma d_sl ESUBST_SIGMA EVAL_T_LEFT ]; subst; clear EVAL_SUB_LEFT.
  inversion EVAL_RIGHT as [ | | | rho_r t_r comp_l rho_right d_r ESUBST_COMP EVAL_T_RIGHT ]; subst; clear EVAL_RIGHT.
  inversion ESUBST_COMP as [ | | rho_c sigma_c tau_c rho_tau2 rho_sigma2 ESUBST_TAU2 ESUBST_SIGMA2 | ]; subst; clear ESUBST_COMP.
  pose proof (eval_subst_functional rho tau rho_tau ESUBST_TAU rho_tau2 ESUBST_TAU2) as ?.
  subst rho_tau2.
  pose proof (eval_subst_functional rho_tau sigma rho_sigma ESUBST_SIGMA rho_right ESUBST_SIGMA2) as ?.
  subst rho_right.
  pose proof (eval_functional rho_sigma t d EVAL_T_LEFT d' EVAL_T_RIGHT) as ?.
  pose proof (subst_typing_sound Gamma1 tau Gamma2 TYPING2 rho ENV) as (rho2 & EVAL_TAU & ENV2).
  pose proof (eval_subst_functional rho tau rho_tau ESUBST_TAU rho2 EVAL_TAU) as ?.
  subst rho2.
  pose proof (subst_typing_sound Gamma2 sigma Gamma3 TYPING1 rho_tau ENV2) as (rho3 & EVAL_SIGMA & ENV3).
  pose proof (eval_subst_functional rho_tau sigma rho_sigma ESUBST_SIGMA rho3 EVAL_SIGMA) as ?.
  subst rho3.
  pose proof (typing_sound Gamma3 t T TYPING rho_sigma ENV3) as (d0 & EVAL0' & D0).
  pose proof (eval_functional rho_sigma t d EVAL_T_LEFT d0 EVAL0') as ?.
  subst d'. subst d0. repeat split; eauto.
Qed.

Theorem sem_subst_eq_shift (Gamma : ctx) (T_head : typ)
  : sem_subst_eq (T_head :: Gamma) SShift SShift Gamma.
Proof.
  eapply sem_subst_eq_refl. eauto.
Qed.

Theorem sem_subst_eq_id (Gamma : ctx)
  : sem_subst_eq Gamma SId SId Gamma.
Proof.
  eapply sem_subst_eq_refl. eauto.
Qed.

Theorem sem_subst_eq_comp (Gamma1 : ctx) (Gamma2 : ctx) (Gamma3 : ctx)
  (sigma : subst) (sigma' : subst) (tau : subst) (tau' : subst)
  (EQ1 : sem_subst_eq Gamma2 sigma sigma' Gamma3)
  (EQ2 : sem_subst_eq Gamma1 tau tau' Gamma2)
  : sem_subst_eq Gamma1 (SComp sigma tau) (SComp sigma' tau') Gamma3.
Proof.
  intros rho ENV rho1 rho2 EVAL1 EVAL2.
  inv EVAL1. inv EVAL2.
  pose proof (EQ2 rho ENV rho' rho'0 EVAL0 EVAL1) as (? & ENV1 & ?).
  subst rho'0. eapply EQ1; eauto.
Qed.

Theorem sem_subst_eq_cons (Gamma : ctx) (Delta : ctx)
  (sigma : subst) (sigma' : subst) (s : exp) (s' : exp) (T_head : typ)
  (EQ1 : sem_subst_eq Gamma sigma sigma' Delta)
  (EQ2 : sem_term_eq Gamma s s' T_head)
  : sem_subst_eq Gamma (SCons sigma s) (SCons sigma' s') (T_head :: Delta).
Proof.
  intros rho ENV rho1 rho2 EVAL1 EVAL2.
  inv EVAL1. inv EVAL2.
  pose proof (EQ1 rho ENV rho' rho'0 ESUBST ESUBST0) as (? & ENV1 & ?).
  pose proof (EQ2 rho ENV a a0 EVAL EVAL0) as (? & A & ?).
  subst rho'0. subst a0. repeat split; eauto using env_in_cons.
Qed.

Theorem sem_subst_eq_shift_cons (Gamma : ctx) (Delta : ctx) (sigma : subst) (s : exp)
  (T_head : typ)
  (SUBST : subst_typing Gamma sigma Delta)
  (TYPING : typing Gamma s T_head)
  : sem_subst_eq Gamma (SComp SShift (SCons sigma s)) sigma Delta.
Proof.
  intros rho ENV rho1 rho2 EVAL_LEFT EVAL_RIGHT.
  inversion EVAL_LEFT as [ | | rho_c sigma_c tau_c rho_mid rho_out EVAL_CONS EVAL_SHIFT | ]; subst; clear EVAL_LEFT.
  inversion EVAL_CONS as [ | | | rho_cons sigma_cons s_cons rho_sigma a_cons ESUBST_SIGMA EVAL_S ]; subst; clear EVAL_CONS.
  inversion EVAL_SHIFT; subst; clear EVAL_SHIFT.
  pose proof (subst_typing_sound Gamma sigma Delta SUBST rho ENV) as (rho0 & ESUBST0 & ENV0).
  match goal with
  | [ H : eval_subst rho sigma ?rho_sigma |- _ ] => pose proof (eval_subst_functional rho sigma rho_sigma H rho0 ESUBST0) as EQ_rho0; subst rho0; pose proof (eval_subst_functional rho sigma rho2 EVAL_RIGHT rho_sigma H) as EQ_rho2
  end.
  subst rho2. repeat split; eauto.
Qed.

Theorem sem_subst_eq_id_left (Gamma : ctx) (Delta : ctx) (sigma : subst)
  (SUBST : subst_typing Gamma sigma Delta)
  : sem_subst_eq Gamma (SComp SId sigma) sigma Delta.
Proof.
  intros rho ENV rho1 rho2 EVAL_LEFT EVAL_RIGHT.
  inversion EVAL_LEFT as [ | | rho_c sigma_c tau_c rho_mid rho_out EVAL_SIGMA EVAL_ID | ]; subst; clear EVAL_LEFT.
  inversion EVAL_ID; subst; clear EVAL_ID.
  pose proof (subst_typing_sound Gamma sigma Delta SUBST rho ENV) as (rho3 & ESUBST & ENV3).
  pose proof (eval_subst_functional rho sigma rho1 EVAL_SIGMA rho2 EVAL_RIGHT) as ?.
  pose proof (eval_subst_functional rho sigma rho1 EVAL_SIGMA rho3 ESUBST) as ?.
  subst rho2. subst rho3. repeat split; eauto.
Qed.

Theorem sem_subst_eq_id_right (Gamma : ctx) (Delta : ctx) (sigma : subst)
  (SUBST : subst_typing Gamma sigma Delta)
  : sem_subst_eq Gamma (SComp sigma SId) sigma Delta.
Proof.
  intros rho ENV rho1 rho2 EVAL_LEFT EVAL_RIGHT.
  inversion EVAL_LEFT as [ | | rho_c sigma_c tau_c rho_mid rho_out EVAL_ID EVAL_SIGMA | ]; subst; clear EVAL_LEFT.
  inversion EVAL_ID; subst; clear EVAL_ID.
  match goal with
  | [ H : eval_subst ?rho0 sigma rho1 |- _ ] => pose proof (eval_subst_functional rho0 sigma rho1 H rho2 EVAL_RIGHT) as EQ_rho2
  end.
  subst rho2.
  pose proof (subst_typing_sound Gamma sigma Delta SUBST _ ENV) as (rho3 & ESUBST & ENV3).
  match goal with
  | [ H : eval_subst ?rho0 sigma rho1 |- _ ] => pose proof (eval_subst_functional rho0 sigma rho1 H rho3 ESUBST) as EQ_rho3
  end.
  subst rho3. repeat split; eauto.
Qed.

Theorem sem_subst_eq_assoc (Gamma1 : ctx) (Gamma2 : ctx) (Gamma3 : ctx)
  (Gamma4 : ctx)
  (sigma1 : subst) (sigma2 : subst) (sigma3 : subst)
  (TYPING1 : subst_typing Gamma2 sigma1 Gamma1)
  (TYPING2 : subst_typing Gamma3 sigma2 Gamma2)
  (TYPING3 : subst_typing Gamma4 sigma3 Gamma3)
  : sem_subst_eq Gamma4 (SComp (SComp sigma1 sigma2) sigma3) (SComp sigma1 (SComp sigma2 sigma3)) Gamma1.
Proof.
  intros rho ENV rho1 rho2 EVAL_LEFT EVAL_RIGHT.
  inversion EVAL_LEFT as [ | | rho_l sigma_l tau_l rho_after3 rho_left EVAL3_LEFT EVAL12_LEFT | ]; subst; clear EVAL_LEFT.
  inversion EVAL12_LEFT as [ | | rho_12 sigma_12 tau_12 rho_after2 rho_after1 EVAL2_LEFT EVAL1_LEFT | ]; subst; clear EVAL12_LEFT.
  inversion EVAL_RIGHT as [ | | rho_r sigma_r tau_r rho_after23 rho_right EVAL23_RIGHT EVAL1_RIGHT | ]; subst; clear EVAL_RIGHT.
  inversion EVAL23_RIGHT as [ | | rho_23 sigma_23 tau_23 rho_after3_right rho_after2_right EVAL3_RIGHT EVAL2_RIGHT | ]; subst; clear EVAL23_RIGHT.
  pose proof (eval_subst_functional rho sigma3 rho_after3 EVAL3_LEFT rho_after3_right EVAL3_RIGHT) as ?.
  subst rho_after3_right.
  pose proof (eval_subst_functional rho_after3 sigma2 rho_after2 EVAL2_LEFT rho_after23 EVAL2_RIGHT) as ?.
  subst rho_after23.
  pose proof (eval_subst_functional rho_after2 sigma1 rho1 EVAL1_LEFT rho2 EVAL1_RIGHT) as ?.
  subst rho2.
  pose proof (subst_typing_sound Gamma4 sigma3 Gamma3 TYPING3 rho ENV) as (rho3 & ESUBST3 & ENV3).
  pose proof (eval_subst_functional rho sigma3 rho_after3 EVAL3_LEFT rho3 ESUBST3) as ?.
  subst rho3.
  pose proof (subst_typing_sound Gamma3 sigma2 Gamma2 TYPING2 rho_after3 ENV3) as (rho4 & ESUBST2 & ENV2).
  pose proof (eval_subst_functional rho_after3 sigma2 rho_after2 EVAL2_LEFT rho4 ESUBST2) as ?.
  subst rho4.
  pose proof (subst_typing_sound Gamma2 sigma1 Gamma1 TYPING1 rho_after2 ENV2) as (rho5 & ESUBST1 & ENV1).
  pose proof (eval_subst_functional rho_after2 sigma1 rho1 EVAL1_LEFT rho5 ESUBST1) as ?.
  subst rho5. repeat split; eauto.
Qed.

Theorem sem_subst_eq_cons_comp (Gamma : ctx) (Gamma' : ctx) (Delta : ctx)
  (tau : subst) (sigma : subst) (s : exp) (T_head : typ)
  (TYPING1 : subst_typing Gamma tau Gamma')
  (TYPING2 : subst_typing Gamma' sigma Delta)
  (TYPING3 : typing Gamma' s T_head)
  : sem_subst_eq Gamma (SComp (SCons sigma s) tau) (SCons (SComp sigma tau) (ESub s tau)) (T_head :: Delta).
Proof.
  intros rho ENV rho1 rho2 EVAL_LEFT EVAL_RIGHT.
  inversion EVAL_LEFT as [ | | rho_l sigma_l tau_l rho_tau rho_left EVAL_TAU_LEFT EVAL_CONS_LEFT | ]; subst; clear EVAL_LEFT.
  inversion EVAL_CONS_LEFT as [ | | | rho_c sigma_c s_c rho_sigma a_left ESUBST_SIGMA_LEFT EVAL_S_LEFT ]; subst; clear EVAL_CONS_LEFT.
  inversion EVAL_RIGHT as [ | | | rho_r sigma_r s_r rho_cons a_right ESUBST_CONS_RIGHT EVAL_SUB_RIGHT ]; subst; clear EVAL_RIGHT.
  inversion ESUBST_CONS_RIGHT as [ | | rho_comp sigma_comp tau_comp rho_tau_right rho_sigma_right EVAL_TAU_RIGHT EVAL_SIGMA_RIGHT | ]; subst; clear ESUBST_CONS_RIGHT.
  inversion EVAL_SUB_RIGHT as [ | | | rho_sub t_sub tau_sub rho_tau_s a_sub EVAL_TAU_S EVAL_S_RIGHT ]; subst; clear EVAL_SUB_RIGHT.
  pose proof (eval_subst_functional rho tau rho_tau EVAL_TAU_LEFT rho_tau_right EVAL_TAU_RIGHT) as ?.
  pose proof (eval_subst_functional rho tau rho_tau EVAL_TAU_LEFT rho_tau_s EVAL_TAU_S) as ?.
  subst rho_tau_right. subst rho_tau_s.
  pose proof (eval_subst_functional rho_tau sigma rho_sigma ESUBST_SIGMA_LEFT rho_cons EVAL_SIGMA_RIGHT) as ?.
  subst rho_cons.
  pose proof (eval_functional rho_tau s a_left EVAL_S_LEFT a_right EVAL_S_RIGHT) as ?.
  subst a_right.
  pose proof (subst_typing_sound Gamma tau Gamma' TYPING1 rho ENV) as (rho3 & ESUBST_TAU & ENV3).
  pose proof (eval_subst_functional rho tau rho_tau EVAL_TAU_LEFT rho3 ESUBST_TAU) as ?.
  subst rho3.
  pose proof (subst_typing_sound Gamma' sigma Delta TYPING2 rho_tau ENV3) as (rho4 & ESUBST_SIGMA & ENV4).
  pose proof (eval_subst_functional rho_tau sigma rho_sigma ESUBST_SIGMA_LEFT rho4 ESUBST_SIGMA) as ?.
  subst rho4.
  pose proof (typing_sound Gamma' s T_head TYPING3 rho_tau ENV3) as (a0 & EVAL_S & A).
  pose proof (eval_functional rho_tau s a_left EVAL_S_LEFT a0 EVAL_S) as ?.
  subst a0. repeat split; eauto using env_in_cons.
Qed.

Theorem sem_subst_eq_eta (Gamma : ctx) (T_head : typ)
  : sem_subst_eq (T_head :: Gamma) SId (SCons SShift (EVar O)) (T_head :: Gamma).
Proof.
  intros rho ENV rho1 rho2 EVAL1 EVAL2.
  inv EVAL1. inv EVAL2. inv EVAL. inv LOOKUP.
  inv ESUBST.
  repeat split; eauto.
Qed.

Definition normal_eq (d : val) (d' : val) : Prop :=
  forall n : nat, forall v : nf, forall v' : nf, read_nf n d v -> read_nf n d' v' -> v = v'.

Definition neutral_eq (e : neu) (e' : neu) : Prop :=
  forall n : nat, forall u : ne, forall u' : ne, read_ne n e u -> read_ne n e' u' -> u = u'.

Lemma normal_eq_refl (d : val)
  : normal_eq d d.
Proof.
  intros n v v' READ READ'. eapply read_nf_functional; eauto.
Qed.

Lemma normal_eq_sym (d : val) (d' : val)
  (EQ : normal_eq d d')
  : normal_eq d' d.
Proof.
  intros n v v' READ READ'. symmetry. eapply EQ; eauto.
Qed.

Lemma neutral_eq_refl (e : neu)
  : neutral_eq e e.
Proof.
  intros n u u' READ READ'. eapply read_ne_functional; eauto.
Qed.

Lemma neutral_eq_sym (e : neu) (e' : neu)
  (EQ : neutral_eq e e')
  : neutral_eq e' e.
Proof.
  intros n u u' READ READ'. symmetry. eapply EQ; eauto.
Qed.

Definition lower_candidate (T : typ) (d : val) (d' : val) : Prop :=
  exists e : neu, exists e' : neu, d = VNeu e /\ d' = VNeu e' /\ neutral_eq e e'.

Definition upper_candidate (T : typ) (d : val) (d' : val) : Prop :=
  normal_eq d d'.

Theorem lower_candidate_in_upper (T : typ) (d : val) (d' : val)
  (LOWER : lower_candidate T d d')
  : upper_candidate T d d'.
Proof.
  destruct LOWER as [e [e' [? [? EQ]]]]; subst.
  intros n v v' READ READ'.
  pose proof (read_nf_neu_inv n e v READ) as [u [? READ_U]]; subst.
  pose proof (read_nf_neu_inv n e' v' READ') as [? [-> READ_U']]; subst.
  f_equal. eapply EQ; eauto.
Qed.

Theorem lower_candidate_refl (T : typ) (e : neu)
  : lower_candidate T (VNeu e) (VNeu e).
Proof.
  exists e. exists e. splits; eauto. eapply neutral_eq_refl.
Qed.

Theorem lower_candidate_sym (T : typ) (d : val) (d' : val)
  (LOWER : lower_candidate T d d')
  : lower_candidate T d' d.
Proof.
  destruct LOWER as [e [e' [? [? EQ]]]]; subst.
  exists e'. exists e. splits; eauto. eapply neutral_eq_sym. exact EQ.
Qed.

Theorem upper_candidate_refl (T : typ) (d : val)
  : upper_candidate T d d.
Proof.
  eapply normal_eq_refl.
Qed.

Theorem upper_candidate_sym (T : typ) (d : val) (d' : val)
  (UPPER : upper_candidate T d d')
  : upper_candidate T d' d.
Proof.
  eapply normal_eq_sym. exact UPPER.
Qed.

Definition realizes (T : typ) (A : val -> val -> Prop) : Prop :=
  (forall d : val, forall d' : val, lower_candidate T d d' -> A d d') /\ (forall d : val, forall d' : val, A d d' -> upper_candidate T d d').

Theorem upper_candidate_realizes_itself (T : typ)
  : realizes T (upper_candidate T).
Proof.
  split.
  - intros d d' LOWER. eapply lower_candidate_in_upper. exact LOWER.
  - intros d d' UPPER. exact UPPER.
Qed.

Record is_per (R : val -> val -> Prop) : Prop :=
  { per_sym : forall x : val, forall y : val, R x y -> R y x
  ; per_trans : forall x : val, forall y : val, forall z : val, R x y -> R y z -> R x z
  }.

Definition per_member (R : val -> val -> Prop) (x : val) : Prop :=
  R x x.

Definition per_fun_member (A : val -> val -> Prop) (B : val -> val -> Prop) (f : val) : Prop :=
  forall a : val, per_member A a -> (exists b : val, app f a b /\ per_member B b).

Definition per_fun (A : val -> val -> Prop) (B : val -> val -> Prop) (f : val) (f' : val) : Prop :=
  per_fun_member A B f /\ per_fun_member A B f' /\ (forall a : val, forall a' : val, forall b : val, forall b' : val, A a a' -> app f a b -> app f' a' b' -> B b b').

Theorem per_fun_is_per (A : val -> val -> Prop) (B : val -> val -> Prop)
  (PER_A : is_per A)
  (PER_B : is_per B)
  : is_per (per_fun A B).
Proof.
  destruct PER_A as [A_sym A_trans].
  destruct PER_B as [B_sym B_trans].
  split.
  - intros f f' (F & F' & EXT). split; eauto.
  - intros f1 f2 f3 H12 H23.
    destruct H12 as (F1 & F2 & EXT12).
    destruct H23 as (_ & F3 & EXT23). split; eauto.
    split; eauto. intros a a' b1 b3 A_EQ APP1 APP3.
    assert (A_MEM : per_member A a').
    { eapply A_trans with (y := a); eauto. }
    pose proof (F2 a' A_MEM) as (b2 & APP2 & B2).
    eapply B_trans with (y := b2).
    + eapply EXT12.
      * exact A_EQ.
      * exact APP1.
      * exact APP2.
    + eapply EXT23.
      * exact A_MEM.
      * exact APP2.
      * exact APP3.
Qed.

Definition base_per (d : val) (d' : val) : Prop :=
  sem_value_eq TyBase d d'.

Fixpoint type_per (T : typ) : val -> val -> Prop :=
  match T with
  | TyBase => base_per
  | TyArr T_dom T_cod => per_fun (type_per T_dom) (type_per T_cod)
  end.

Theorem type_per_is_per (T : typ)
  : is_per (type_per T).
Proof.
  induction T as [ | T_dom IH_dom T_cod IH_cod]; simpl.
  - split.
    + intros d d' (? & D & D'). subst d'. repeat split; eauto.
    + intros d1 d2 d3 (? & D1 & D2) (? & D2' & D3).
      subst d2. subst d3. repeat split; eauto.
  - eapply per_fun_is_per; eauto.
Qed.

Lemma type_per_refl_left (T : typ) (d : val) (d' : val)
  (PER : type_per T d d')
  : type_per T d d.
Proof.
  pose proof (type_per_is_per T) as [SYM TRANS].
  eapply TRANS with (y := d').
  - exact PER.
  - eapply SYM. exact PER.
Qed.

Lemma type_per_refl_right (T : typ) (d : val) (d' : val)
  (PER : type_per T d d')
  : type_per T d' d'.
Proof.
  pose proof (type_per_is_per T) as [SYM TRANS].
  eapply TRANS with (y := d).
  - eapply SYM. exact PER.
  - exact PER.
Qed.

Definition per_env (Gamma : ctx) (rho : env) (rho' : env) : Prop :=
  forall i : nat, forall T : typ, lookup_ctx Gamma i = Some T -> (exists d : val, exists d' : val, env_lookup rho i d /\ env_lookup rho' i d' /\ type_per T d d').

Lemma per_env_cons (Gamma : ctx) (rho : env) (rho' : env) (a : val) (a' : val) (T : typ)
  (PER : type_per T a a')
  (ENV : per_env Gamma rho rho')
  : per_env (T :: Gamma) (a :: rho) (a' :: rho').
Proof.
  intros i U LOOKUP. destruct i as [ | i]; simpl in LOOKUP.
  - inversion LOOKUP; subst. exists a. exists a'. splits; eauto.
  - pose proof (ENV i U LOOKUP) as (d & d' & LOOKUP1 & LOOKUP2 & PER_D).
    exists d. exists d'. splits; eauto.
Qed.

Lemma per_env_refl_left (Gamma : ctx) (rho : env) (rho' : env)
  (ENV : per_env Gamma rho rho')
  : per_env Gamma rho rho.
Proof.
  intros i T LOOKUP.
  pose proof (ENV i T LOOKUP) as (d & d' & LOOKUP1 & LOOKUP2 & PER_D).
  exists d. exists d. splits; eauto using type_per_refl_left.
Qed.

Lemma per_env_refl_right (Gamma : ctx) (rho : env) (rho' : env)
  (ENV : per_env Gamma rho rho')
  : per_env Gamma rho' rho'.
Proof.
  intros i T LOOKUP.
  pose proof (ENV i T LOOKUP) as (d & d' & LOOKUP1 & LOOKUP2 & PER_D).
  exists d'. exists d'. splits; eauto using type_per_refl_right.
Qed.

Lemma per_env_cons_inv (Gamma : ctx) (rho : env) (rho' : env) (T : typ)
  (ENV : per_env (T :: Gamma) rho rho')
  : exists a : val, exists a' : val, exists rho0 : env, exists rho0' : env,
      rho = a :: rho0 /\ rho' = a' :: rho0' /\ type_per T a a' /\ per_env Gamma rho0 rho0'.
Proof.
  pose proof (ENV O T eq_refl) as (a & a' & LOOKUP1 & LOOKUP2 & PER).
  destruct rho as [ | b rho0]; inv LOOKUP1.
  destruct rho' as [ | b' rho0']; inv LOOKUP2.
  exists a. exists a'. exists rho0. exists rho0'. splits; eauto.
  intros i U LOOKUP.
  pose proof (ENV (S i) U LOOKUP) as (d & d' & LOOKUP_D & LOOKUP_D' & PER_D).
  inv LOOKUP_D. inv LOOKUP_D'. exists d. exists d'. splits; eauto.
Qed.

Definition per_sem_typing (Gamma : ctx) (t : exp) (T : typ) : Prop :=
  forall rho : env, forall rho' : env, per_env Gamma rho rho' -> (exists d : val, exists d' : val, eval rho t d /\ eval rho' t d' /\ type_per T d d').

Definition per_sem_subst_typing (Gamma : ctx) (sigma : subst) (Delta : ctx) : Prop :=
  forall rho : env, forall rho' : env, per_env Gamma rho rho' -> (exists rho1 : env, exists rho2 : env, eval_subst rho sigma rho1 /\ eval_subst rho' sigma rho2 /\ per_env Delta rho1 rho2).

Theorem typing_per_sound (Gamma : ctx) (t : exp) (T : typ)
  (TYPING : typing Gamma t T)
  : per_sem_typing Gamma t T
with subst_typing_per_sound (Gamma : ctx) (sigma : subst) (Delta : ctx)
  (TYPING : subst_typing Gamma sigma Delta)
  : per_sem_subst_typing Gamma sigma Delta.
Proof.
  - induction TYPING; intros rho rho' ENV.
    + pose proof (ENV i T LOOKUP) as (d & d' & LOOKUP1 & LOOKUP2 & PER).
      exists d. exists d'. splits; eauto.
    + exists (VClos t rho). exists (VClos t rho'). splits; eauto. simpl.
      split.
      * intros a A.
        pose proof (IHTYPING (a :: rho) (a :: rho) (per_env_cons Gamma rho rho a a T_dom A (per_env_refl_left Gamma rho rho' ENV))) as (b & b' & EVAL1 & EVAL2 & PER_B).
        exists b. split; eauto.
        eapply type_per_refl_left. exact PER_B.
      * split.
        { intros a A.
          pose proof (IHTYPING (a :: rho') (a :: rho') (per_env_cons Gamma rho' rho' a a T_dom A (per_env_refl_right Gamma rho rho' ENV))) as (b & b' & EVAL1 & EVAL2 & PER_B).
          exists b. split; eauto.
          eapply type_per_refl_left. exact PER_B.
        }
        { intros a a' b b' PER_A APP1 APP2.
          inv APP1. inv APP2.
          pose proof (IHTYPING (a :: rho) (a' :: rho') (per_env_cons Gamma rho rho' a a' T_dom PER_A ENV)) as (c & c' & EVAL1 & EVAL2 & PER_B).
          assert (EQ1 : b = c) by (eapply eval_functional; eauto).
          assert (EQ2 : b' = c') by (eapply eval_functional; eauto).
          subst b. subst b'. exact PER_B.
        }
    + pose proof (IHTYPING1 rho rho' ENV) as (f & f' & EVAL1 & EVAL1' & PER_F).
      pose proof (IHTYPING2 rho rho' ENV) as (a & a' & EVAL2 & EVAL2' & PER_A).
      destruct PER_F as (MEM_F & MEM_F' & EXT).
      pose proof (type_per_refl_left T_dom a a' PER_A) as MEM_A.
      pose proof (type_per_refl_right T_dom a a' PER_A) as MEM_A'.
      pose proof (MEM_F a MEM_A) as (b & APP & B).
      pose proof (MEM_F' a' MEM_A') as (b' & APP' & B').
      exists b. exists b'. splits; eauto.
    + pose proof (subst_typing_per_sound Gamma sigma Delta SUBST rho rho' ENV) as (rho1 & rho2 & ESUBST1 & ESUBST2 & ENV12).
      pose proof (IHTYPING rho1 rho2 ENV12) as (d & d' & EVAL1 & EVAL2 & PER).
      exists d. exists d'. splits; eauto.
  - induction TYPING; intros rho rho' ENV.
    + pose proof (per_env_cons_inv Gamma rho rho' T_head ENV) as (a & a' & rho0 & rho0' & -> & -> & PER_A & ENV0).
      exists rho0. exists rho0'. splits; eauto.
    + exists rho. exists rho'. splits; eauto.
    + pose proof (subst_typing_per_sound Gamma1 tau Gamma2 TYPING1 rho rho' ENV) as (rho1 & rho2 & ESUBST1 & ESUBST2 & ENV12).
      pose proof (subst_typing_per_sound Gamma2 sigma Gamma3 TYPING2 rho1 rho2 ENV12) as (rho3 & rho4 & ESUBST3 & ESUBST4 & ENV34).
      exists rho3. exists rho4. splits; eauto.
    + pose proof (IHTYPING rho rho' ENV) as (rho1 & rho2 & ESUBST1 & ESUBST2 & ENV12).
      pose proof (typing_per_sound Gamma s T_head TYPING0 rho rho' ENV) as (a & a' & EVAL1 & EVAL2 & PER_A).
      exists (a :: rho1). exists (a' :: rho2). splits; eauto using per_env_cons.
Qed.

Definition ext_sem_term_eq (Gamma : ctx) (t : exp) (t' : exp) (T : typ) : Prop :=
  forall rho : env, forall rho' : env, per_env Gamma rho rho' -> forall d : val, forall d' : val, eval rho t d -> eval rho' t' d' -> type_per T d d'.

Definition ext_sem_subst_eq (Gamma : ctx) (sigma : subst) (sigma' : subst) (Delta : ctx) : Prop :=
  forall rho : env, forall rho' : env, per_env Gamma rho rho' -> forall rho1 : env, forall rho2 : env,
    eval_subst rho sigma rho1 -> eval_subst rho' sigma' rho2 -> per_env Delta rho1 rho2.

Theorem ext_sem_term_eq_refl (Gamma : ctx) (t : exp) (T : typ)
  (TYPING : typing Gamma t T)
  : ext_sem_term_eq Gamma t t T.
Proof.
  intros rho rho' ENV d d' EVAL1 EVAL2.
  pose proof (typing_per_sound Gamma t T TYPING rho rho' ENV) as (d0 & d0' & EVAL0 & EVAL0' & PER).
  assert (EQ1 : d = d0) by (eapply eval_functional; eauto).
  assert (EQ2 : d' = d0') by (eapply eval_functional; eauto).
  subst d. subst d'. exact PER.
Qed.

Theorem ext_sem_subst_eq_refl (Gamma : ctx) (sigma : subst) (Delta : ctx)
  (TYPING : subst_typing Gamma sigma Delta)
  : ext_sem_subst_eq Gamma sigma sigma Delta.
Proof.
  intros rho rho' ENV rho1 rho2 EVAL1 EVAL2.
  pose proof (subst_typing_per_sound Gamma sigma Delta TYPING rho rho' ENV) as (rho0 & rho0' & EVAL0 & EVAL0' & ENV0).
  assert (EQ1 : rho1 = rho0) by (eapply eval_subst_functional; eauto).
  assert (EQ2 : rho2 = rho0') by (eapply eval_subst_functional; eauto).
  subst rho1. subst rho2. exact ENV0.
Qed.

Theorem ext_sem_term_eq_lam (Gamma : ctx) (t : exp) (t' : exp) (T_dom : typ) (T_cod : typ)
  (TYPING1 : typing (T_dom :: Gamma) t T_cod)
  (TYPING2 : typing (T_dom :: Gamma) t' T_cod)
  (EQ : ext_sem_term_eq (T_dom :: Gamma) t t' T_cod)
  : ext_sem_term_eq Gamma (ELam t) (ELam t') (TyArr T_dom T_cod).
Proof.
  intros rho rho' ENV d d' EVAL1 EVAL2.
  inv EVAL1. inv EVAL2. simpl.
  split.
  - intros a A.
    pose proof (typing_per_sound (T_dom :: Gamma) t T_cod TYPING1 (a :: rho) (a :: rho) (per_env_cons Gamma rho rho a a T_dom A (per_env_refl_left Gamma rho rho' ENV))) as (b & b' & EVAL_B & EVAL_B' & PER_B).
    exists b. split; eauto.
    eapply type_per_refl_left. exact PER_B.
  - split.
    + intros a A.
      pose proof (typing_per_sound (T_dom :: Gamma) t' T_cod TYPING2 (a :: rho') (a :: rho') (per_env_cons Gamma rho' rho' a a T_dom A (per_env_refl_right Gamma rho rho' ENV))) as (b & b' & EVAL_B & EVAL_B' & PER_B).
      exists b. split; eauto.
      eapply type_per_refl_left. exact PER_B.
    + intros a a' b b' PER_A APP1 APP2.
      inv APP1. inv APP2.
      eapply EQ; eauto using per_env_cons.
Qed.

Theorem ext_sem_term_eq_eta (Gamma : ctx) (t : exp) (T_dom : typ) (T_cod : typ)
  (TYPING : typing Gamma t (TyArr T_dom T_cod))
  : ext_sem_term_eq Gamma t (ELam (EApp (ESub t SShift) (EVar O))) (TyArr T_dom T_cod).
Proof.
  intros rho rho' ENV d d' EVAL1 EVAL2.
  inv EVAL2.
  pose proof (typing_per_sound Gamma t (TyArr T_dom T_cod) TYPING rho rho' ENV) as (f & f' & EVAL_F & EVAL_F' & PER_F).
  assert (EQ_f : d = f) by (eapply eval_functional; eauto).
  subst f. simpl in PER_F. destruct PER_F as (MEM_D & MEM_F' & EXT).
  split.
  - exact MEM_D.
  - split.
    + intros a A.
      pose proof (MEM_F' a A) as (b & APP & B).
      exists b. split.
      * eapply App_clos.
        eapply Eval_app with (f := f') (a := a).
        { eapply Eval_sub with (rho' := rho').
          - eauto.
          - exact EVAL_F'.
        }
        { eauto. }
        { exact APP. }
      * exact B.
    + intros a a' b b' PER_A APP1 APP2.
      inversion APP2 as [t_body rho_body a_body b_body EVAL_BODY | ]; subst; clear APP2.
      inversion EVAL_BODY as [ | | rho_body2 r_body s_body f_body arg_body res_body EVAL_FUN EVAL_ARG APP_BODY | ]; subst; clear EVAL_BODY.
      inversion EVAL_FUN as [ | | | rho_fun t_fun sigma_fun rho_shift f_shift ESUBST_SHIFT EVAL_T ]; subst; clear EVAL_FUN.
      inversion ESUBST_SHIFT; subst; clear ESUBST_SHIFT.
      inversion EVAL_ARG; subst; clear EVAL_ARG.
      match goal with
      | [ H : env_lookup _ O arg_body |- _ ] => inv H
      end.
      assert (EQ_f' : f_body = f') by (eapply eval_functional; eauto).
      subst f_body.
      eapply EXT.
      * exact PER_A.
      * exact APP1.
      * exact APP_BODY.
Qed.

Theorem ext_sem_term_eq_lam_subst (Gamma : ctx) (Delta : ctx) (sigma : subst) (t : exp) (T_dom : typ) (T_cod : typ)
  (SUBST : subst_typing Gamma sigma Delta)
  (TYPING : typing (T_dom :: Delta) t T_cod)
  : ext_sem_term_eq Gamma (ESub (ELam t) sigma) (ELam (ESub t (SCons (SComp sigma SShift) (EVar O)))) (TyArr T_dom T_cod).
Proof.
  intros rho rho' ENV d d' EVAL1 EVAL2.
  inversion EVAL1 as [ | | | rho_left t_left sigma_left rho_sigma d_left ESUBST_LEFT EVAL_LEFT ]; subst; clear EVAL1.
  inversion EVAL_LEFT; subst; clear EVAL_LEFT.
  inversion EVAL2; subst; clear EVAL2.
  pose proof (subst_typing_per_sound Gamma sigma Delta SUBST rho rho' ENV) as (rho_sigma0 & rho_sigma' & ESUBST0 & ESUBST' & ENV_SIGMA).
  pose proof (eval_subst_functional rho sigma rho_sigma ESUBST_LEFT rho_sigma0 ESUBST0) as ?.
  subst rho_sigma0. simpl.
  assert (EVAL_EXT : forall a : val, eval_subst (a :: rho') (SCons (SComp sigma SShift) (EVar O)) (a :: rho_sigma')).
  { intros a. eapply EvalSubst_cons.
    - eapply EvalSubst_comp with (rho' := rho').
      + eauto.
      + exact ESUBST'.
    - eauto.
  }
  split.
  - intros a A.
    pose proof (typing_per_sound (T_dom :: Delta) t T_cod TYPING (a :: rho_sigma) (a :: rho_sigma) (per_env_cons Delta rho_sigma rho_sigma a a T_dom A (per_env_refl_left Delta rho_sigma rho_sigma' ENV_SIGMA))) as (b & b' & EVAL_B & EVAL_B' & PER_B).
    exists b. split.
    + eauto.
    + eapply type_per_refl_left. exact PER_B.
  - split.
    + intros a A.
      pose proof (typing_per_sound (T_dom :: Delta) t T_cod TYPING (a :: rho_sigma') (a :: rho_sigma') (per_env_cons Delta rho_sigma' rho_sigma' a a T_dom A (per_env_refl_right Delta rho_sigma rho_sigma' ENV_SIGMA))) as (b & b' & EVAL_B & EVAL_B' & PER_B).
      exists b. split.
      * eapply App_clos. eapply Eval_sub with (rho' := a :: rho_sigma').
        { eapply EVAL_EXT. }
        { exact EVAL_B. }
      * eapply type_per_refl_left. exact PER_B.
    + intros a a' b b' PER_A APP1 APP2.
      inversion APP1 as [t_app rho_app a_app b_app EVAL_APP_LEFT | ]; subst; clear APP1.
      inversion APP2 as [t_app' rho_app' a_app' b_app' EVAL_APP_RIGHT | ]; subst; clear APP2.
      inversion EVAL_APP_RIGHT as [ | | | rho_arg t_sub subst_ext rho_ext b_ext ESUBST_EXT EVAL_T_RIGHT ]; subst; clear EVAL_APP_RIGHT.
      pose proof (EVAL_EXT a') as ESUBST_EXPECTED.
      pose proof (eval_subst_functional (a' :: rho') (SCons (SComp sigma SShift) (EVar O)) rho_ext ESUBST_EXT (a' :: rho_sigma') ESUBST_EXPECTED) as ?.
      subst rho_ext.
      pose proof (typing_per_sound (T_dom :: Delta) t T_cod TYPING (a :: rho_sigma) (a' :: rho_sigma') (per_env_cons Delta rho_sigma rho_sigma' a a' T_dom PER_A ENV_SIGMA)) as (c & c' & EVAL_C & EVAL_C' & PER_C).
      assert (EQ1 : b = c) by (eapply eval_functional; eauto).
      assert (EQ2 : b' = c') by (eapply eval_functional; eauto).
      subst b. subst b'. exact PER_C.
Qed.

Definition typed_reflect (T : typ) (n : nat) : val :=
  VNeu (NLevel n).

Lemma typed_reflect_sem_type (T : typ) (n : nat)
  : typed_reflect T n \in sem_type T.
Proof.
  pose proof (sem_type_candidate T) as (LOW & HIGH).
  eapply LOW. exists (NLevel n). split; eauto using readable_level.
Qed.

Inductive typed_read : nat -> typ -> val -> nf -> Prop :=
  | TypedRead_base (n : nat) (d : val) (v : nf)
    (READ : read_nf n d v)
    : typed_read n TyBase d v
  | TypedRead_arr (n : nat) (T_dom : typ) (T_cod : typ) (f : val) (b : val) (v : nf)
    (APP : app f (typed_reflect T_dom n) b)
    (READ : typed_read (S n) T_cod b v)
    : typed_read n (TyArr T_dom T_cod) f (NfLam v).

#[local] Hint Constructors typed_read : core.

Theorem sem_type_typed_read (T : typ)
  : forall d : val, d \in sem_type T -> forall n : nat, exists v : nf, typed_read n T d v.
Proof.
  induction T as [ | T_dom IH_dom T_cod IH_cod]; intros d D n; simpl in D.
  - pose proof (D n) as (v & READ). exists v. eauto.
  - pose proof (typed_reflect_sem_type T_dom n) as ARG.
    pose proof (D (typed_reflect T_dom n) ARG) as (b & APP & B).
    pose proof (IH_cod b B (S n)) as (v & READ).
    exists (NfLam v). eauto.
Qed.

Definition typed_nbe (Gamma : ctx) (t : exp) (T : typ) (v : nf) : Prop :=
  exists d : val, eval (initial_env (length Gamma)) t d /\ typed_read (length Gamma) T d v.

Theorem type_assignment_typed_normalizes (Gamma : ctx) (t : exp) (T : typ)
  (TYPING : typing Gamma t T)
  : exists v : nf, typed_nbe Gamma t T v.
Proof.
  pose proof (typing_sound Gamma t T TYPING (initial_env (length Gamma)) (env_in_initial_env Gamma)) as (d & EVAL & D).
  pose proof (sem_type_typed_read T d D (length Gamma)) as (v & READ).
  exists v. exists d. eauto.
Qed.

Theorem typed_nbe_beta_explicit_subst (Gamma : ctx) (t : exp) (s : exp) (T_dom : typ) (T_cod : typ) (v : nf)
  (TYPING1 : typing (T_dom :: Gamma) t T_cod)
  (TYPING2 : typing Gamma s T_dom)
  : typed_nbe Gamma (EApp (ELam t) s) T_cod v <-> typed_nbe Gamma (ESub t (single_subst s)) T_cod v.
Proof.
  split; intros [d [EVAL READ]]; exists d; split; eauto.
  - exact (proj1 (beta_explicit_subst (initial_env (length Gamma)) t s d) EVAL).
  - exact (proj2 (beta_explicit_subst (initial_env (length Gamma)) t s d) EVAL).
Qed.

Theorem typed_read_functional (T : typ) (n : nat) (d : val) (v1 : nf)
  (READ1 : typed_read n T d v1)
  : forall v2 : nf, typed_read n T d v2 -> v1 = v2.
Proof.
  revert n d v1 READ1. induction T as [ | T_dom IH_dom T_cod IH_cod]; intros n d v1 READ1 v2 READ2.
  - inv READ1. inv READ2. eapply read_nf_functional; eauto.
  - inv READ1. inv READ2.
    assert (EQ_b : b = b0) by (eapply app_functional; eauto).
    subst b0. f_equal. eapply IH_cod; eauto.
Qed.

Theorem typed_nbe_functional (Gamma : ctx) (t : exp) (T : typ) (v1 : nf)
  (NBE1 : typed_nbe Gamma t T v1)
  : forall v2 : nf, typed_nbe Gamma t T v2 -> v1 = v2.
Proof.
  intros v2 (d2 & EVAL2 & READ2).
  destruct NBE1 as (d1 & EVAL1 & READ1).
  assert (EQ_d : d1 = d2) by (eapply eval_functional; eauto).
  subst d2. eapply typed_read_functional; eauto.
Qed.

Theorem typed_read_neutral_eta (n : nat) (e : neu) (T_dom : typ) (T_cod : typ) (v : nf)
  (READ : typed_read (S n) T_cod (VNeu (NApp e (typed_reflect T_dom n))) v)
  : typed_read n (TyArr T_dom T_cod) (VNeu e) (NfLam v).
Proof.
  eauto.
Qed.

Inductive ne_exp : exp -> Prop :=
  | NeExp_var (i : nat)
    : ne_exp (EVar i)
  | NeExp_app (u : exp) (v : exp)
    (NE : ne_exp u)
    (NF : nf_exp v)
    : ne_exp (EApp u v)
with nf_exp : exp -> Prop :=
  | NfExp_ne (u : exp)
    (NE : ne_exp u)
    : nf_exp u
  | NfExp_lam (v : exp)
    (NF : nf_exp v)
    : nf_exp (ELam v).

Fixpoint ne_to_exp (u : ne) : exp :=
  match u with
  | NeVar i => EVar i
  | NeApp u v => EApp (ne_to_exp u) (nf_to_exp v)
  end
with nf_to_exp (v : nf) : exp :=
  match v with
  | NfNe u => ne_to_exp u
  | NfLam v => ELam (nf_to_exp v)
  end.

Theorem ne_to_exp_is_ne (u : ne)
  : ne_exp (ne_to_exp u)
with nf_to_exp_is_nf (v : nf)
  : nf_exp (nf_to_exp v).
Proof.
  - destruct u; simpl.
    + eauto using ne_exp.
    + eauto using ne_exp.
  - destruct v; simpl.
    + eauto using nf_exp.
    + eauto using nf_exp.
Qed.

Inductive future : ctx -> ctx -> subst -> Prop :=
  | Future_id (Gamma : ctx)
    : future Gamma Gamma SId
  | Future_shift (Gamma' : ctx) (Gamma : ctx) (sigma : subst) (S : typ)
    (FUTURE : future Gamma' Gamma sigma)
    : future (S :: Gamma') Gamma (SComp sigma SShift).

Theorem future_subst_typing (Gamma' : ctx) (Gamma : ctx) (sigma : subst)
  (FUTURE : future Gamma' Gamma sigma)
  : subst_typing Gamma' sigma Gamma.
Proof.
  induction FUTURE; eauto.
Qed.

Theorem future_initial_env (Gamma' : ctx) (Gamma : ctx) (sigma : subst)
  (FUTURE : future Gamma' Gamma sigma)
  : eval_subst (initial_env (length Gamma')) sigma (initial_env (length Gamma)).
Proof.
  induction FUTURE; simpl.
  - eauto.
  - eapply EvalSubst_comp with (rho' := initial_env (length Gamma')).
    + eauto.
    + exact IHFUTURE.
Qed.

Definition kripke_readback_sound (Gamma : ctx) (t : exp) (T : typ) (d : val) : Prop :=
  typing Gamma t T /\ d \in sem_type T /\ (forall Gamma' : ctx, forall sigma : subst, future Gamma' Gamma sigma -> (exists v : nf, eval (initial_env (length Gamma')) (ESub t sigma) d /\ typed_read (length Gamma') T d v)).

Theorem initial_semantic_values_have_kripke_readback (Gamma : ctx) (t : exp) (T : typ) (d : val)
  (TYPING : typing Gamma t T)
  (EVAL : eval (initial_env (length Gamma)) t d)
  : kripke_readback_sound Gamma t T d.
Proof.
  pose proof (typing_sound Gamma t T TYPING (initial_env (length Gamma)) (env_in_initial_env Gamma)) as (d0 & EVAL0 & D0).
  assert (EQ_d : d = d0) by (eapply eval_functional; eauto).
  subst d0. repeat split; eauto.
  intros Gamma' sigma FUTURE.
  pose proof (future_initial_env Gamma' Gamma sigma FUTURE) as ESUBST.
  pose proof (sem_type_typed_read T d D0 (length Gamma')) as (v & READ).
  exists v. split; eauto.
Qed.

Theorem typed_nbe_kripke_sound (Gamma' : ctx) (Gamma : ctx) (sigma : subst) (t : exp) (T : typ)
  (FUTURE : future Gamma' Gamma sigma)
  (TYPING : typing Gamma t T)
  : exists v : nf, typed_nbe Gamma' (ESub t sigma) T v.
Proof.
  eapply type_assignment_typed_normalizes.
  eapply Ty_sub; eauto using future_subst_typing.
Qed.

Theorem kripke_readback_produces_normal_exp (Gamma : ctx) (t : exp) (T : typ) (d : val)
  (SOUND : kripke_readback_sound Gamma t T d)
  : forall Gamma' : ctx, forall sigma : subst, future Gamma' Gamma sigma -> (exists v : nf, eval (initial_env (length Gamma')) (ESub t sigma) d /\ typed_read (length Gamma') T d v /\ nf_exp (nf_to_exp v)).
Proof.
  intros Gamma' sigma FUTURE.
  destruct SOUND as (TYPING & D & SOUND).
  pose proof (SOUND Gamma' sigma FUTURE) as (v & EVAL & READ).
  exists v. splits; eauto using nf_to_exp_is_nf.
Qed.

End AbelChapter3.
