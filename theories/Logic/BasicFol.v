Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Math.ThN.
Require Import PnV.Data.Vector.
Require Import Coq.Arith.Wf_nat.

#[local] Infix "\in" := E.In.
#[local] Infix "\subseteq" := E.isSubsetOf.
#[local] Notation In := List.In.

#[projections(primitive)]
Record language : Type :=
  { function_symbols : Set
  ; constant_symbols : Set
  ; relation_symbols : Set
  ; function_arity_table : function_symbols -> nat
  ; relation_arity_table : relation_symbols -> nat
  }.

Section FOL_DEF.

Definition ivar : Set := nat.

Definition renaming : Set := ivar -> ivar.

Context {L : language}.

Inductive trm : Set :=
  | Var_trm (x : ivar) : trm
  | Fun_trm (f : L.(function_symbols)) (ts : trms (L.(function_arity_table) f)) : trm
  | Con_trm (c : L.(constant_symbols)) : trm
with trms : forall arity : nat, Set :=
  | O_trms : trms O
  | S_trms (n : nat) (t : trm) (ts : trms n) : trms (S n).

Inductive frm : Set :=
  | Rel_frm (R : L.(relation_symbols)) (ts : trms (L.(relation_arity_table) R)) : frm
  | Eqn_frm (t1 : trm) (t2 : trm) : frm
  | Neg_frm (p1 : frm) : frm
  | Imp_frm (p1 : frm) (p2 : frm) : frm
  | All_frm (y : ivar) (p1 : frm) : frm.

Let cast (n : nat) (m : nat) (EQ : n = m) : trms n -> trms m :=
  match EQ with
  | eq_refl => fun xs => xs
  end.

Lemma trms_case0 (phi : trms O -> Type)
  (phi_nil : phi O_trms)
  : forall ts, phi ts.
Proof.
  refine (
    let claim1 (xs : trms O) : forall H_eq : O = O, phi (cast O O H_eq xs) :=
      match xs in trms m return forall H_eq : m = O, phi (cast m O H_eq xs) with
      | O_trms => fun H_eq : O = O => _
      | S_trms n x' xs' => fun H_eq : S n = O => _
      end
    in _
  ).
  { intros xs. exact (claim1 xs eq_refl). }
Unshelve.
  - rewrite eq_pirrel_fromEqDec with (EQ1 := H_eq) (EQ2 := eq_refl).
    exact (phi_nil).
  - inversion H_eq.
Qed.

Lemma trms_caseS {n' : nat} (phi : trms (S n') -> Type)
  (phi_cons : forall t', forall ts', phi (S_trms n' t' ts'))
  : forall ts, phi ts.
Proof.
  refine (
    let claim1 (xs : trms (S n')) : forall H_eq : S n' = S n', phi (cast (S n') (S n') H_eq xs) :=
      match xs in trms m return forall H_eq : m = S n', phi (cast m (S n') H_eq xs) with
      | O_trms => fun H_eq : O = S n' => _
      | S_trms n x' xs' => fun H_eq : S n = S n' => _
      end
    in _
  ).
  { intros xs. exact (claim1 xs eq_refl). }
Unshelve.
  - inversion H_eq.
  - pose proof (f_equal Nat.pred H_eq) as n_eq_n'. simpl in n_eq_n'. subst n'.
    rewrite eq_pirrel_fromEqDec with (EQ1 := H_eq) (EQ2 := eq_refl).
    exact (phi_cons x' xs').
Qed.

Definition head {n : nat} (ts : trms (S n)) : trm :=
  match ts in trms n' return (match n' as n' return Type with O => unit | S n => trm end) with
  | O_trms => tt
  | S_trms _ t _ => t
  end.

Definition tail {n : nat} (ts : trms (S n)) : trms n :=
  match ts in trms n' return (match n' as n' return Type with O => unit | S n => trms n end) with
  | O_trms => tt
  | S_trms _ _ ts => ts
  end.

Lemma trms_rec2 (phi : forall arity, trms arity -> trms arity -> Type)
  (phi_O : phi O O_trms O_trms)
  (phi_S : forall n, forall t, forall t', forall ts, forall ts', phi n ts ts' -> phi (S n) (S_trms n t ts) (S_trms n t' ts'))
  : forall n, forall ts, forall ts', phi n ts ts'.
Proof.
  induction ts as [ | n t ts IH].
  - eapply trms_case0. exact phi_O.
  - eapply trms_caseS. intros t' ts'. exact (phi_S n t t' ts ts' (IH ts')).
Qed.

Fixpoint trms_to_vec {n : nat} (ts : trms n) : Vector.t trm n :=
  match ts with
  | O_trms => []
  | S_trms n' t ts => t :: trms_to_vec ts
  end.

Lemma trms_to_vec_eq_iff arity (ts : trms arity) (ts' : trms arity)
  : trms_to_vec ts = trms_to_vec ts' <-> ts = ts'.
Proof.
  split; intros EQ.
  - revert EQ. pattern arity, ts, ts'. revert arity ts ts'.
    eapply trms_rec2 with (phi := fun n => fun ts => fun ts' => @trms_to_vec n ts = @trms_to_vec n ts' -> ts = ts'); ii.
    + reflexivity.
    + simpl in H0. f_equal.
      * apply f_equal with (f := V.head) in H0. do 2 rewrite V.head_unfold in H0; eauto.
      * apply f_equal with (f := V.tail) in H0. do 2 rewrite V.tail_unfold in H0; eauto.
  - f_equal; eauto.
Qed.

End FOL_DEF.

#[global] Arguments trm : clear implicits.
#[global] Arguments trms : clear implicits.
#[global] Arguments frm : clear implicits.

Tactic Notation "trm_ind" ident( t ) :=
  induction t as [x | f ts | c].

Tactic Notation "trms_ind" ident( ts ) :=
  induction ts as [ | n t ts IH].

Tactic Notation "frm_ind" ident( p ) :=
  induction p as [R ts | t1 t2 | p1 IH1 | p1 IH1 p2 IH2 | y p1 IH1].

Tactic Notation "trm_ind2" ident( t ) ident( t' ) :=
  revert t'; induction t as [x | f ts | c]; intros [x' | f' ts' | c'].

Tactic Notation "trms_ind2" ident( ts ) ident( ts' ) :=
  revert ts'; induction ts as [ | n t ts IH]; [intros ts'; pattern ts'; revert ts'; apply trms_case0 | intros ts'; pattern ts'; revert ts'; apply trms_caseS; intros t' ts'].

Tactic Notation "frm_ind2" ident( p ) ident( p' ) :=
  revert p'; induction p as [R ts | t1 t2 | p1 IH1 | p1 IH1 p2 IH2 | y p1 IH1]; intros [R' ts' | t1' t2' | p1' | p1' p2' | y' p1'].

Section EQ_DEC.

#[global]
Instance ivar_hasEqDec : hasEqDec ivar :=
  Nat.eq_dec.

Context {L : language}.

Hypothesis function_symbols_hasEqDec : hasEqDec L.(function_symbols).

Hypothesis constant_symbols_hasEqDec : hasEqDec L.(constant_symbols).

Lemma trm_eq_dec (t1 : trm L) (t2 : trm L)
  : {t1 = t2} + {t1 <> t2}
with trms_eq_dec n (ts1 : trms L n) (ts2 : trms L n)
  : {ts1 = ts2} + {ts1 <> ts2}.
Proof with try first [now right; congruence | now left; congruence].
  - pose proof ivar_hasEqDec as ivar_hasEqDec.
    red in ivar_hasEqDec, function_symbols_hasEqDec, constant_symbols_hasEqDec.
    clear trm_eq_dec. trm_ind2 t1 t2...
    + pose proof (ivar_hasEqDec x x') as [? | ?]...
    + pose proof (function_symbols_hasEqDec f f') as [f_eq_f' | f_ne_f']...
      subst f'. pose proof (trms_eq_dec (L.(function_arity_table) f) ts ts') as [EQ | NE]...
      right. intros CONTRA. eapply NE. inv CONTRA.
      apply @projT2_eq_fromEqDec with (B := fun f : L.(function_symbols) => trms L (function_arity_table L f)) in H0.
      * exact H0.
      * exact function_symbols_hasEqDec.
    + pose proof (constant_symbols_hasEqDec c c') as [? | ?]...
  - clear trms_eq_dec. trms_ind2 ts1 ts2...
    pose proof (trm_eq_dec t t') as [? | ?]; pose proof (IH ts2) as [EQ | NE]...
    right. intros CONTRA. eapply NE. inv CONTRA.
    apply @projT2_eq_fromEqDec with (B := fun n : nat => trms L n) in H1.
    + exact H1.
    + exact nat_hasEqDec.
Defined.

#[global]
Instance trm_hasEqDec : hasEqDec (trm L) :=
  trm_eq_dec.

#[global]
Instance trms_hasEqDec (n : nat) : hasEqDec (trms L n) :=
  trms_eq_dec n.

Hypothesis relation_symbols_hasEqDec : hasEqDec L.(relation_symbols).

Lemma frm_eq_dec (p : frm L) (p' : frm L)
  : {p = p'} + {p <> p'}.
Proof with try first [now right; congruence | now left; congruence].
  pose proof ivar_hasEqDec as ivar_hasEqDec. red in ivar_hasEqDec. frm_ind2 p p'...
  - pose proof (relation_symbols_hasEqDec R R') as [R_eq_R' | R_ne_R']...
    subst R'. pose proof (trms_eq_dec (L.(relation_arity_table) R) ts ts') as [EQ | NE]...
    right. intros CONTRA. eapply NE. inv CONTRA.
    apply @projT2_eq_fromEqDec with (B := fun R : L.(relation_symbols) => trms L (relation_arity_table L R)) in H0.
    + exact H0.
    + exact relation_symbols_hasEqDec.
  - pose proof (trm_eq_dec t1 t1') as [? | ?]; pose proof (trm_eq_dec t2 t2') as [? | ?]...
  - pose proof (IH1 p1') as [? | ?]...
  - pose proof (IH1 p1') as [? | ?]; pose proof (IH2 p2') as [? | ?]...
  - pose proof (ivar_hasEqDec y y') as [? | ?]; pose proof (IH1 p1') as [? | ?]...
Defined.

#[global] Instance frm_hasEqDec : hasEqDec (frm L) :=
  frm_eq_dec.

End EQ_DEC.

Section ENUMERATION.

Context {L : language}.

Let rank : Set := nat.

Fixpoint trm_depth (t : trm L) : rank :=
  match t with
  | Var_trm x => 0
  | Fun_trm f ts => 1 + trms_depth ts
  | Con_trm c => 1
  end
with trms_depth {n : nat} (ts : trms L n) : rank :=
  match ts with
  | O_trms => 0
  | S_trms n t ts => 1 + max (trm_depth t) (trms_depth ts)
  end.

Lemma trm_depth_unfold (t : trm L) :
  trm_depth t =
  match t with
  | Var_trm x => 0
  | Fun_trm f ts => 1 + trms_depth ts
  | Con_trm c => 1
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma trms_depth_unfold n (ts : trms L n) :
  trms_depth ts =
  match ts with
  | O_trms => 0
  | S_trms n t ts => 1 + max (trm_depth t) (trms_depth ts)
  end.
Proof.
  destruct ts; reflexivity.
Defined.

Fixpoint frm_depth (p : frm L) : rank :=
  match p with
  | Rel_frm R ts => 0
  | Eqn_frm t1 t2 => 0
  | Neg_frm p1 => 1 + frm_depth p1
  | Imp_frm p1 p2 => 1 + max (frm_depth p1) (frm_depth p2)
  | All_frm y p1 => 1 + frm_depth p1
  end.

Lemma frm_depth_unfold (p : frm L) :
  frm_depth p =
  match p with
  | Rel_frm R ts => 0
  | Eqn_frm t1 t2 => 0
  | Neg_frm p1 => 1 + frm_depth p1
  | Imp_frm p1 p2 => 1 + max (frm_depth p1) (frm_depth p2)
  | All_frm y p1 => 1 + frm_depth p1
  end.
Proof.
  destruct p; reflexivity.
Defined.

Lemma frm_depth_lt_ind (P : frm L -> Type)
  (IND : forall p : frm L, forall IH : forall p' : frm L, forall RANK_LT : frm_depth p' < frm_depth p, P p', P p)
  : forall p : frm L, P p.
Proof.
  intros p. induction (relation_on_image_liftsWellFounded Nat.lt frm_depth lt_wf p) as [p _ IH]. exact (IND p IH).
Defined.

Hypothesis enum_function_symbols : isEnumerable L.(function_symbols).

Hypothesis enum_constant_symbols : isEnumerable L.(constant_symbols).

Fixpoint gen_trm (seed : nat) (rk : nat) {struct rk} : trm L :=
  match rk with
  | O => Var_trm seed
  | S rk' =>
    let '(seed1, seed') := cp seed in
    let '(seed2, seed3) := cp seed' in
    match seed1 with
    | 0 => Con_trm (enum seed')
    | 1 => Fun_trm (enum seed2) (gen_trms seed3 rk')
    | S (S i) => Var_trm i
    end
  end
with gen_trms {n : nat} (seed : nat) (rk : nat) {struct rk} : trms L n :=
  match n with
  | O => O_trms
  | S n' =>
    match rk with
    | O => nat_rec (trms L) O_trms (fun x => S_trms x (Var_trm seed)) (S n')
    | S rk' =>
      let '(seed1, seed2) := cp seed in
      S_trms n' (gen_trm seed1 rk') (gen_trms seed2 rk')
    end
  end.

Lemma gen_trm_unfold (seed : nat) (rk : nat) :
  gen_trm seed rk =
  match rk with
  | O => Var_trm seed
  | S rk' =>
    let '(seed1, seed') := cp seed in
    let '(seed2, seed3) := cp seed' in
    match seed1 with
    | 0 => Con_trm (enum seed')
    | 1 => Fun_trm (enum seed2) (gen_trms seed3 rk')
    | S (S i) => Var_trm i
    end
  end.
Proof.
  destruct rk; reflexivity.
Defined.

Lemma gen_trms_unfold (n : nat) (seed : nat) (rk : nat) :
  gen_trms seed rk =
  match n with
  | O => O_trms
  | S n' =>
    match rk with
    | O => nat_rec (trms L) O_trms (fun x => S_trms x (Var_trm seed)) (S n')
    | S rk' =>
      let '(seed1, seed2) := cp seed in
      S_trms n' (gen_trm seed1 rk') (gen_trms seed2 rk')
    end
  end.
Proof.
  destruct rk, n; reflexivity.
Defined.

Lemma gen_trm_good (t : trm L) (rk : nat)
  (RANK_LE : trm_depth t <= rk)
  : { seed : nat | gen_trm seed rk = t }
with gen_trms_good n (ts : trms L n) (rk : nat)
  (RANK_LE : trms_depth ts <= rk)
  : { seed : nat | gen_trms seed rk = ts }.
Proof.
  - revert rk RANK_LE. trm_ind t; simpl; i.
    + destruct rk as [ | rk'].
      * exists x. reflexivity.
      * simpl. exists (cpInv (2 + x) 0).
        destruct (cp (cpInv (2 + x) 0)) as [x1 x2] eqn: H_OBS.
        rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
        simpl. reflexivity.
    + destruct rk as [ | rk']; [lia | assert (RANK_LE' : trms_depth ts <= rk') by lia].
      pose proof (gen_trms_good _ ts rk' RANK_LE') as [seed2 H_OBS].
      exists (cpInv 1 (cpInv (proj1_sig (enum_spec f)) seed2)). rewrite gen_trm_unfold.
      destruct (cp (cpInv 1 (cpInv (proj1_sig (enum_spec f)) seed2))) as [x1 x2] eqn: H_OBS'.
      rewrite cp_spec in H_OBS'. apply cpInv_inj in H_OBS'. destruct H_OBS' as [<- <-].
      destruct (cp (cpInv (proj1_sig (enum_spec f)) seed2)) as [x2 y2] eqn: H_OBS''.
      rewrite cp_spec in H_OBS''. apply cpInv_inj in H_OBS''. destruct H_OBS'' as [<- <-].
      assert (claim : (enum (proj1_sig (enum_spec f))) = f) by now destruct (enum_spec f). rewrite claim. rewrite H_OBS. reflexivity.
    + destruct rk as [ | rk']; [lia | assert (RANK_LE' : 0 <= rk') by lia].
      exists (cpInv 0 (proj1_sig (enum_spec c))). rewrite gen_trm_unfold.
      destruct (cp (cpInv 0 (proj1_sig (enum_spec c)))) as [x1 x2] eqn: H_OBS'.
      assert (claim : enum (proj1_sig (enum_spec c)) = c) by now destruct (enum_spec c).
      rewrite cp_spec in H_OBS'. apply cpInv_inj in H_OBS'. destruct H_OBS' as [<- <-]. rewrite claim.
      destruct (cp (proj1_sig (enum_spec c))) as [x1 x2] eqn: H_OBS'. reflexivity.
  - revert rk RANK_LE. trms_ind ts; simpl; i.
    + simpl. exists 0. rewrite gen_trms_unfold. reflexivity.
    + destruct rk as [ | rk'].
      * lia.
      * assert (claim1 : trm_depth t <= rk') by lia.
        assert (claim2 : trms_depth ts <= rk') by lia.
        apply gen_trm_good in claim1. apply IH in claim2.
        destruct claim1 as [seed1 P_t'], claim2 as [seed2 P_ts'].
        exists (cpInv seed1 seed2). rewrite <- P_t' at 1; rewrite <- P_ts' at 1. rewrite gen_trms_unfold.
        destruct (cp (cpInv seed1 seed2)) as [x y] eqn: H_OBS. rewrite cp_spec in H_OBS.
        apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-]. reflexivity.
Qed.

Definition enum_trm (x : nat) : trm L :=
  let rk := fst (cp x) in
  let seed := snd (cp x) in
  gen_trm seed rk.

Theorem trm_is_enumerable (t : trm L)
  : { x : nat | enum_trm x = t }.
Proof.
  epose proof (gen_trm_good t (trm_depth t) _) as [seed H_EQ].
  exists (cpInv (trm_depth t) seed). unfold enum_trm. destruct (cp (cpInv (trm_depth t) seed)) as [x y] eqn: H_OBS.
  rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-]. simpl. done.
Unshelve.
  reflexivity.
Qed.

Definition enum_trms {n : nat} (x : nat) : trms L n :=
  let rk := fst (cp x) in
  let seed := snd (cp x) in
  gen_trms seed rk.

Theorem trms_is_enumerable n (ts : trms L n)
  : { x : nat | enum_trms x = ts }.
Proof.
  epose proof (gen_trms_good n ts (trms_depth ts) _) as [seed H_EQ].
  exists (cpInv (trms_depth ts) seed). unfold enum_trms. destruct (cp (cpInv (trms_depth ts) seed)) as [x y] eqn: H_OBS.
  rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-]. simpl. done.
Unshelve.
  reflexivity.
Qed.

#[local]
Instance trm_isEnumerable : isEnumerable (trm L) :=
  { enum := enum_trm
  ; enum_spec := trm_is_enumerable
  }.

#[local]
Instance trms_isRecursivelyEnumerable (n : nat) : isEnumerable (trms L n) :=
  { enum := enum_trms
  ; enum_spec := trms_is_enumerable n
  }.

Hypothesis enum_relation_symbols : isEnumerable L.(relation_symbols).

Fixpoint gen_frm (seed : nat) (rk : nat) {struct rk} : frm L :=
  match rk with
  | O =>
    let '(seed1, seed') := cp seed in
    let '(seed2, seed3) := cp seed' in
    match seed1 with
    | 0 => Eqn_frm (enum seed2) (enum seed3)
    | _ => Rel_frm (enum seed2) (enum seed3)
    end
  | S rk' =>
    let '(seed1, seed') := cp seed in
    let '(seed2, seed3) := cp seed' in
    match seed1 with
    | 0 => Neg_frm (gen_frm seed' rk')
    | 1 => Imp_frm (gen_frm seed2 rk') (gen_frm seed3 rk')
    | 2 => All_frm seed2 (gen_frm seed3 rk')
    | S (S (S i)) =>
      match i with
      | 0 => Eqn_frm (enum seed2) (enum seed3)
      | _ => Rel_frm (enum seed2) (enum seed3)
      end
    end
  end.

Lemma gen_frm_unfold (seed : nat) (rk : nat) :
  gen_frm seed rk =
  match rk with
  | O =>
    let '(seed1, seed') := cp seed in
    let '(seed2, seed3) := cp seed' in
    match seed1 with
    | 0 => Eqn_frm (enum seed2) (enum seed3)
    | _ => Rel_frm (enum seed2) (enum seed3)
    end
  | S rk' =>
    let '(seed1, seed') := cp seed in
    let '(seed2, seed3) := cp seed' in
    match seed1 with
    | 0 => Neg_frm (gen_frm seed' rk')
    | 1 => Imp_frm (gen_frm seed2 rk') (gen_frm seed3 rk')
    | 2 => All_frm seed2 (gen_frm seed3 rk')
    | S (S (S i)) =>
      match i with
      | 0 => Eqn_frm (enum seed2) (enum seed3)
      | _ => Rel_frm (enum seed2) (enum seed3)
      end
    end
  end.
Proof.
  destruct rk; reflexivity.
Defined.

Lemma gen_frm_spec (p : frm L) (rk : nat)
  (LE : frm_depth p <= rk)
  : { seed : nat | gen_frm seed rk = p }.
Proof.
  revert rk LE. frm_ind p; simpl; i.
  - destruct rk as [ | rk'].
    + exists (cpInv 1 (cpInv (proj1_sig (enum_spec R)) (proj1_sig (enum_spec ts)))).
      rewrite gen_frm_unfold. destruct (cp (cpInv 1 (cpInv (proj1_sig (enum_spec R)) (proj1_sig (enum_spec ts))))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp (cpInv (proj1_sig (enum_spec R)) (proj1_sig (enum_spec ts)))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (enum_spec R) as [R_n H_R], (enum_spec ts) as [ts_n H_ts]; subst R ts. reflexivity.
    + exists (cpInv 4 (cpInv (proj1_sig (enum_spec R)) (proj1_sig (enum_spec ts)))).
      rewrite gen_frm_unfold. destruct (cp (cpInv 4 (cpInv (proj1_sig (enum_spec R)) (proj1_sig (enum_spec ts))))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp (cpInv (proj1_sig (enum_spec R)) (proj1_sig (enum_spec ts)))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (enum_spec R) as [R_n H_R], (enum_spec ts) as [ts_n H_ts]; subst R ts. reflexivity.
  - destruct rk as [ | rk'].
    + exists (cpInv 0 (cpInv (proj1_sig (enum_spec t1)) (proj1_sig (enum_spec t2)))).
      rewrite gen_frm_unfold. destruct (cp (cpInv 0 (cpInv (proj1_sig (enum_spec t1)) (proj1_sig (enum_spec t2))))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp (cpInv (proj1_sig (enum_spec t1)) (proj1_sig (enum_spec t2)))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (enum_spec t1) as [t1_n H_t1], (enum_spec t2) as [t2_n H_t2]; subst t1 t2. reflexivity.
    + exists (cpInv 3 (cpInv (proj1_sig (enum_spec t1)) (proj1_sig (enum_spec t2)))).
      rewrite gen_frm_unfold. destruct (cp (cpInv 3 (cpInv (proj1_sig (enum_spec t1)) (proj1_sig (enum_spec t2))))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp (cpInv (proj1_sig (enum_spec t1)) (proj1_sig (enum_spec t2)))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (enum_spec t1) as [t1_n H_t1], (enum_spec t2) as [t2_n H_t2]; subst t1 t2. reflexivity.
  - destruct rk as [ | rk'].
    + lia.
    + assert (claim1 : frm_depth p1 <= rk') by lia.
      apply IH1 in claim1. destruct claim1 as [seed1 H_seed1]. exists (cpInv 0 seed1).
      rewrite gen_frm_unfold. destruct (cp (cpInv 0 seed1)) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp seed1) as [x y]. f_equal; done.
  - destruct rk as [ | rk'].
    + lia.
    + assert (claim1 : frm_depth p1 <= rk') by lia.
      assert (claim2 : frm_depth p2 <= rk') by lia.
      apply IH1 in claim1. apply IH2 in claim2. destruct claim1 as [seed1 H_seed1]. destruct claim2 as [seed2 H_seed2]. exists (cpInv 1 (cpInv seed1 seed2)).
      rewrite gen_frm_unfold. destruct (cp (cpInv 1 (cpInv seed1 seed2))) as [x y] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp (cpInv seed1 seed2)) as [x y] eqn: H_OBS. rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-]. f_equal; done.
  - destruct rk as [ | rk'].
    + lia.
    + assert (claim1 : frm_depth p1 <= rk') by lia.
      apply IH1 in claim1. destruct claim1 as [seed1 H_seed1]. exists (cpInv 2 (cpInv y seed1)).
      rewrite gen_frm_unfold. destruct (cp (cpInv 2 (cpInv y seed1))) as [x z] eqn: H_OBS.
      rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-].
      destruct (cp (cpInv y seed1)) as [x z] eqn: H_OBS. rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-]. f_equal; done.
Qed.

Definition enum_frm (x : nat) : frm L :=
  let rk := fst (cp x) in
  let seed := snd (cp x) in
  gen_frm seed rk.

Theorem frm_is_enumerable (p : frm L)
  : { x : nat | enum_frm x = p }.
Proof.
  epose proof (gen_frm_spec p (frm_depth p) _) as [seed H_EQ].
  exists (cpInv (frm_depth p) seed). unfold enum_frm. destruct (cp (cpInv (frm_depth p) seed)) as [x y] eqn: H_OBS.
  rewrite cp_spec in H_OBS. apply cpInv_inj in H_OBS. destruct H_OBS as [<- <-]. simpl. done.
Unshelve.
  reflexivity.
Qed.

#[local]
Instance frm_isEnumerable : isEnumerable (frm L) :=
  { enum := enum_frm
  ; enum_spec := frm_is_enumerable
  }.

End ENUMERATION.

Section FOL_SYNTAX. (* Reference: "https://github.com/ernius/formalmetatheory-stoughton" *)

#[local] Hint Unfold compose : simplication_hints.

#[local] Open Scope program_scope.

Import ListNotations.

Definition subst (L : language) : Set :=
  ivar -> trm L.

Context {L : language}.

Fixpoint fvs_trm (t : trm L) : list ivar :=
  match t with
  | Var_trm x => [x]
  | Fun_trm f ts => fvs_trms ts
  | Con_trm c => []
  end
with fvs_trms {n : nat} (ts : trms L n) : list ivar :=
  match ts with
  | O_trms => []
  | S_trms n t ts => fvs_trm t ++ fvs_trms ts
  end.

Fixpoint fvs_frm (p : frm L) : list ivar :=
  match p with
  | Rel_frm r ts => fvs_trms ts
  | Eqn_frm t1 t2 => fvs_trm t1 ++ fvs_trm t2
  | Neg_frm p1 => fvs_frm p1
  | Imp_frm p1 p2 => fvs_frm p1 ++ fvs_frm p2
  | All_frm y p1 => List.remove eq_dec y (fvs_frm p1)
  end.

Lemma fvs_trm_unfold (t : trm L) :
  fvs_trm t =
  match t with
  | Var_trm x => [x]
  | Fun_trm f ts => fvs_trms ts
  | Con_trm c => []
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma fvs_trms_unfold (n : nat) (ts : trms L n) :
  fvs_trms ts =
  match ts with
  | O_trms => []
  | S_trms n t ts => fvs_trm t ++ fvs_trms (n := n) ts
  end.
Proof.
  destruct ts; reflexivity.
Defined.

Lemma fvs_frm_unfold (p : frm L) :
  fvs_frm p =
  match p with
  | Rel_frm r ts => fvs_trms ts
  | Eqn_frm t1 t2 => fvs_trm t1 ++ fvs_trm t2
  | Neg_frm p1 => fvs_frm p1
  | Imp_frm p1 p2 => fvs_frm p1 ++ fvs_frm p2
  | All_frm y p1 => List.remove eq_dec y (fvs_frm p1)
  end.
Proof.
  destruct p; reflexivity.
Defined.

Fixpoint is_free_in_trm (z : ivar) (t : trm L) : bool :=
  match t with
  | Var_trm x => Nat.eqb x z
  | Fun_trm f ts => is_free_in_trms (n := L.(function_arity_table) f) z ts
  | Con_trm c => false
  end
with is_free_in_trms {n : nat} (z : ivar) (ts : trms L n) : bool :=
  match ts with
  | O_trms => false
  | S_trms n t ts => is_free_in_trm z t || is_free_in_trms (n := n) z ts
  end.

Fixpoint is_free_in_frm (z : ivar) (p : frm L) : bool :=
  match p with
  | Rel_frm R ts => is_free_in_trms (n := L.(relation_arity_table) R) z ts
  | Eqn_frm t1 t2 => is_free_in_trm z t1 || is_free_in_trm z t2
  | Neg_frm p1 => is_free_in_frm z p1
  | Imp_frm p1 p2 => is_free_in_frm z p1 || is_free_in_frm z p2
  | All_frm y p1 => is_free_in_frm z p1 && negb (Nat.eqb z y)
  end.

Lemma is_free_in_trm_unfold (z : ivar) (t : trm L) :
  is_free_in_trm z t =
  match t with
  | Var_trm x => Nat.eqb x z
  | Fun_trm f ts => is_free_in_trms z ts
  | Con_trm c => false
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma is_free_in_trms_unfold n (z : ivar) (ts : trms L n) :
  is_free_in_trms z ts =
  match ts with
  | O_trms => false
  | S_trms n t ts => is_free_in_trm z t || is_free_in_trms z ts
  end.
Proof.
  destruct ts; reflexivity.
Defined.

Lemma is_free_in_frm_unfold (z : ivar) (p : frm L) :
  is_free_in_frm z p =
  match p with
  | Rel_frm R ts => is_free_in_trms z ts
  | Eqn_frm t1 t2 => is_free_in_trm z t1 || is_free_in_trm z t2
  | Neg_frm p1 => is_free_in_frm z p1
  | Imp_frm p1 p2 => is_free_in_frm z p1 || is_free_in_frm z p2
  | All_frm y p1 => is_free_in_frm z p1 && negb (Nat.eqb z y)
  end.
Proof.
  destruct p; reflexivity.
Defined.

Lemma fv_is_free_in_trm (t : trm L)
  : forall z, In z (fvs_trm t) <-> is_free_in_trm z t = true
with fv_is_free_in_trms n (ts : trms L n)
  : forall z, In z (fvs_trms ts) <-> is_free_in_trms z ts = true.
Proof.
  - clear fv_is_free_in_trm. trm_ind t; simpl; i; ss!.
  - clear fv_is_free_in_trms. trms_ind ts; simpl; i; ss!.
Qed.

#[local] Hint Rewrite fv_is_free_in_trm fv_is_free_in_trms : simplication_hints.

Lemma fv_is_free_in_frm (p : frm L)
  : forall z, In z (fvs_frm p) <-> is_free_in_frm z p = true.
Proof.
  frm_ind p; simpl; i; ss!.
Qed.

#[local] Hint Rewrite fv_is_free_in_frm : simplication_hints.

Definition is_not_free_in_trm (x : ivar) (t : trm L) : Prop :=
  is_free_in_trm x t = false.

Definition is_not_free_in_trms {n : nat} (x : ivar) (ts : trms L n) : Prop :=
  is_free_in_trms x ts = false.

Definition is_not_free_in_frm (x : ivar) (p : frm L) : Prop :=
  is_free_in_frm x p = false.

#[local] Hint Unfold is_not_free_in_frm is_free_in_trms is_not_free_in_frm : simplication_hints.

Definition fvs_frms (ps : ensemble (frm L)) : ensemble ivar :=
  ps >>= E.fromList ∘ fvs_frm.

Lemma fvs_is_free_in_frms (ps : ensemble (frm L))
  : forall z, z \in fvs_frms ps <-> (exists p, p \in ps /\ is_free_in_frm z p = true).
Proof.
  unfold fvs_frms; ss!; exists x; done!.
Qed.

#[local] Hint Rewrite fvs_is_free_in_frms : simplication_hints.

Definition is_not_free_in_frms (x : ivar) (ps : ensemble (frm L)) : Prop :=
  forall p, p \in ps -> is_free_in_frm x p = false.

#[local] Hint Unfold is_not_free_in_frms : simplication_hints.

Definition last_ivar_trm (t : trm L) : ivar :=
  maxs (fvs_trm t).

Fixpoint last_ivar_trms {n : nat} (ts : trms L n) : ivar :=
  match ts with
  | O_trms => 0
  | S_trms n t ts => max (last_ivar_trm t) (last_ivar_trms (n := n) ts)
  end.

Definition last_ivar_frm (p : frm L) : ivar :=
  maxs (fvs_frm p).

Lemma last_ivar_trms_eq_maxs_fvs n (ts : trms L n)
  : last_ivar_trms ts = maxs (fvs_trms ts).
Proof.
  trms_ind ts; simpl.
  - done.
  - rewrite maxs_app. done!.
Qed.

#[local] Hint Unfold last_ivar_trm last_ivar_frm : simplication_hints.
#[local] Hint Rewrite <- last_ivar_trms_eq_maxs_fvs : simplication_hints.

Lemma last_ivar_trm_gt (t : trm L) (z : ivar)
  (GT : z > last_ivar_trm t)
  : is_free_in_trm z t = false
with last_ivar_trms_gt n (ts : trms L n) (z : ivar)
  (GT : z > last_ivar_trms ts)
  : is_free_in_trms z ts = false.
Proof.
  - clear last_ivar_trm_gt; revert z GT. trm_ind t; simpl; i; ss!.
  - clear last_ivar_trms_gt; revert z GT. trms_ind ts; simpl; i; ss!.
Qed.

Lemma last_ivar_frm_gt (p : frm L) (z: ivar)
  (GT : z > last_ivar_frm p)
  : is_free_in_frm z p = false.
Proof.
  enough (ENOUGH : ~ In z (fvs_frm p)) by ss!.
  pose proof (in_maxs_ge (fvs_frm p)) as claim1.
  intros CONTRA. apply claim1 in CONTRA. ss!.
Qed.

Definition chi_frm (s : subst L) (p : frm L) : ivar :=
  1 + maxs (List.map (last_ivar_trm ∘ s) (fvs_frm p)).

Lemma chi_frm_not_free (s : subst L) (p : frm L) (x : ivar)
  (FREE : is_free_in_frm x p = true)
  : is_free_in_trm (chi_frm s p) (s x) = false.
Proof.
  enough (ENOUGH : last_ivar_trm (s x) < chi_frm s p) by now eapply last_ivar_trm_gt.
  unfold chi_frm. s!. unfold "<". apply fv_is_free_in_frm in FREE.
  enough (TO_SHOW : last_ivar_trm (s x) <= maxs (L.map (last_ivar_trm ∘ s) (fvs_frm p))) by done!.
  eapply in_maxs_ge. ss!. exists x. done!.
Qed.

Definition nil_subst : subst L :=
  fun z : ivar => Var_trm z.

Definition cons_subst (y : ivar) (t : trm L) (s : subst L) : subst L :=
  fun z : ivar => if eq_dec z y then t else s z.

Definition one_subst (x1 : ivar) (t1 : trm L) : subst L :=
  cons_subst x1 t1 nil_subst.

#[local] Hint Unfold nil_subst cons_subst one_subst : simplication_hints.

Fixpoint subst_trm (s : subst L) (t : trm L) : trm L :=
  match t with
  | Var_trm x => s x
  | Fun_trm f ts => Fun_trm f (subst_trms s ts)
  | Con_trm c => Con_trm c
  end
with subst_trms {n : nat} (s : subst L) (ts : trms L n) : trms L n :=
  match ts with
  | O_trms => O_trms
  | S_trms n t ts => S_trms n (subst_trm s t) (subst_trms (n := n) s ts) 
  end.

Fixpoint subst_frm (s : subst L) (p : frm L) : frm L :=
  let chi : ivar := chi_frm s p in
  match p with
  | Rel_frm R ts => Rel_frm R (subst_trms s ts)
  | Eqn_frm t1 t2 => Eqn_frm (subst_trm s t1) (subst_trm s t2)
  | Neg_frm p1 => Neg_frm (subst_frm s p1)
  | Imp_frm p1 p2 => Imp_frm (subst_frm s p1) (subst_frm s p2)
  | All_frm y p1 => All_frm chi (subst_frm (cons_subst y (Var_trm chi) s) p1)
  end.

Definition subst_compose (s : subst L) (s' : subst L) : subst L :=
  fun z : ivar => subst_trm s' (s z).

#[local] Hint Unfold subst_compose : simplication_hints.

Lemma subst_trm_unfold (s : subst L) (t : trm L) :
  subst_trm s t =
  match t with
  | Var_trm x => s x
  | Fun_trm f ts => Fun_trm f (subst_trms s ts)
  | Con_trm c => Con_trm c
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma subst_trms_unfold n (s : subst L) (ts : trms L n) :
  subst_trms s ts =
  match ts with
  | O_trms => O_trms
  | S_trms n t ts => S_trms n (subst_trm s t) (subst_trms s ts) 
  end.
Proof.
  destruct ts; reflexivity.
Defined.

Lemma subst_frm_unfold (s : subst L) (p : frm L) :
  subst_frm s p =
  let z : ivar := chi_frm s p in
  match p with
  | Rel_frm R ts => Rel_frm R (subst_trms s ts)
  | Eqn_frm t1 t2 => Eqn_frm (subst_trm s t1) (subst_trm s t2)
  | Neg_frm p1 => Neg_frm (subst_frm s p1)
  | Imp_frm p1 p2 => Imp_frm (subst_frm s p1) (subst_frm s p2)
  | All_frm y p1 => All_frm z (subst_frm (cons_subst y (Var_trm z) s) p1)
  end.
Proof.
  destruct p; reflexivity.
Defined.

Definition trm_is_fresh_in_subst (x : ivar) (s : subst L) (t : trm L) : bool :=
  L.forallb (negb ∘ is_free_in_trm x ∘ s) (fvs_trm t).

Definition trms_is_fresh_in_subst {n : nat} (x : ivar) (s : subst L) (ts : trms L n) : bool :=
  L.forallb (negb ∘ is_free_in_trm x ∘ s) (fvs_trms ts).

Definition frm_is_fresh_in_subst (x : ivar) (s : subst L) (p : frm L) : bool :=
  L.forallb (negb ∘ is_free_in_trm x ∘ s) (fvs_frm p).

Theorem chi_frm_is_fresh_in_subst (p : frm L) (s : subst L)
  : frm_is_fresh_in_subst (chi_frm s p) s p = true.
Proof.
  unfold frm_is_fresh_in_subst. rewrite forallb_forall. ii.
  unfold "∘". rewrite negb_true_iff. eapply chi_frm_not_free.
  rewrite <- fv_is_free_in_frm. done.
Qed.

Lemma chi_frm_nil (p : frm L)
  : is_free_in_frm (chi_frm nil_subst p) p = false.
Proof.
  pose proof (chi_frm_is_fresh_in_subst p nil_subst) as claim1.
  unfold frm_is_fresh_in_subst in claim1.
  eapply not_true_iff_false. intros CONTRA. 
  rewrite forallb_forall in claim1. unfold "∘" in claim1. simpl in claim1.
  rewrite <- fv_is_free_in_frm in CONTRA. apply claim1 in CONTRA.
  rewrite negb_true_iff, Nat.eqb_neq in CONTRA. contradiction.
Qed.

Theorem trm_is_fresh_in_subst_iff (t : trm L) (z : ivar) (s : subst L)
  : trm_is_fresh_in_subst z s t = true <-> is_free_in_trm z (subst_trm s t) = false
with trms_is_fresh_in_subst_iff n (ts : trms L n) (z : ivar) (s : subst L)
  : trms_is_fresh_in_subst z s ts = true <-> is_free_in_trms z (subst_trms s ts) = false.
Proof.
  - clear trm_is_fresh_in_subst_iff; unfold trm_is_fresh_in_subst. revert z s; trm_ind t; ii; ss!.
  - clear trms_is_fresh_in_subst_iff; unfold trms_is_fresh_in_subst. revert z s; trms_ind ts; ii; ss!.
Qed.

Theorem frm_is_fresh_in_subst_iff (p : frm L) (z : ivar) (s : subst L)
  : frm_is_fresh_in_subst z s p = true <-> is_free_in_frm z (subst_frm s p) = false.
Proof.
  unfold frm_is_fresh_in_subst; revert z s. frm_ind p; simpl; ii; s!.
  - now rewrite <- trms_is_fresh_in_subst_iff.
  - now do 2 rewrite <- trm_is_fresh_in_subst_iff.
  - done!.
  - done!.
  - split.
    + intros H_forallb.
      destruct (z =? chi_frm s (All_frm y p1))%nat as [ | ] eqn: OBS; [right; ss! | left].
      s!. eapply IH1. rewrite forallb_forall. intros x x_in. s!. destruct (eq_dec x y) as [H_eq | H_ne].
      * subst y. rewrite is_free_in_trm_unfold. ss!.
      * rewrite forallb_forall in H_forallb. rewrite <- negb_true_iff. eapply H_forallb. ss!.
    + intros [NOT_FREE | ->].
      * eapply IH1 in NOT_FREE. rewrite forallb_forall in NOT_FREE. rewrite forallb_forall. intros x x_in; s!.
        exploit (NOT_FREE x). ss!. destruct (eq_dec x y) as [EQ | NE]; ss!.
      * rewrite forallb_forall. intros x x_in. ss!. eapply chi_frm_not_free. rewrite is_free_in_frm_unfold; ss!.
Qed.

Definition equiv_subst_in_frm (s1 : subst L) (s2 : subst L) (p : frm L) : Prop :=
  forall z : ivar, forall FREE : is_free_in_frm z p = true, s1 z = s2 z.

Lemma chi_frm_compat_equiv_subst (s1 : subst L) (s2 : subst L) (p : frm L)
  (EQUIV : equiv_subst_in_frm s1 s2 p)
  : chi_frm s1 p = chi_frm s2 p.
Proof.
  unfold chi_frm. f_equal. eapply maxs_ext. i; ss!; exists x; ss!.
Qed.

Lemma equiv_subst_in_trm_implies_subst_trm_same (s1 : subst L) (s2 : subst L) (t : trm L)
  (EQUIV : forall z : ivar, forall FREE : is_free_in_trm z t = true, s1 z = s2 z)
  : subst_trm s1 t = subst_trm s2 t
with equiv_subst_in_trms_implies_subst_trms_same n (s1 : subst L) (s2 : subst L) (ts : trms L n)
  (EQUIV : forall z : ivar, forall FREE : is_free_in_trms z ts = true, s1 z = s2 z)
  : subst_trms s1 ts = subst_trms s2 ts.
Proof.
  - clear equiv_subst_in_trm_implies_subst_trm_same; revert s1 s2 EQUIV. trm_ind t; ii; s!.
    + eapply EQUIV; ss!.
    + ss!. eapply equiv_subst_in_trms_implies_subst_trms_same; ii. eapply EQUIV; ss!.
    + ss!.
  - clear equiv_subst_in_trms_implies_subst_trms_same; revert s1 s2 EQUIV. trms_ind ts; ii; s!.
    + ss!.
    + ss!.
      * eapply equiv_subst_in_trm_implies_subst_trm_same; ii. eapply EQUIV; ss!.
      * eapply IH; ii. eapply EQUIV; ss!.
Qed.

Lemma equiv_subst_in_frm_implies_subst_frm_same (s1 : subst L) (s2 : subst L) (p : frm L)
  (EQUIV : equiv_subst_in_frm s1 s2 p)
  : subst_frm s1 p = subst_frm s2 p.
Proof.
  unfold equiv_subst_in_frm; revert s1 s2 EQUIV. frm_ind p; ii; s!.
  - f_equal; eapply equiv_subst_in_trms_implies_subst_trms_same; ii; eapply EQUIV; rewrite is_free_in_frm_unfold; ss!.
  - f_equal; eapply equiv_subst_in_trm_implies_subst_trm_same; ii; eapply EQUIV; rewrite is_free_in_frm_unfold; ss!.
  - f_equal; eapply IH1; ii; eapply EQUIV; rewrite is_free_in_frm_unfold; ss!.
  - f_equal; [eapply IH1 | eapply IH2]; ii; eapply EQUIV; rewrite is_free_in_frm_unfold; ss!.
  - assert (claim1 : chi_frm s1 (All_frm y p1) = chi_frm s2 (All_frm y p1)) by now eapply chi_frm_compat_equiv_subst.
    f_equal; trivial. eapply IH1; ii; destruct (eq_dec z y) as [EQ | NE]; ss!. ii; eapply EQUIV; rewrite is_free_in_frm_unfold; ss!.
Qed.

Lemma distr_compose_one (s1 : subst L) (s2 : subst L) (x : ivar) (x' : ivar) (t : trm L) (z : ivar) (p : frm L)
  (FRESH : forallb (negb ∘ is_free_in_trm x ∘ s1) (remove eq_dec x' (fvs_frm p)) = true)
  (FREE : is_free_in_frm z p = true)
  : cons_subst x' t (subst_compose s1 s2) z = subst_compose (cons_subst x' (Var_trm x) s1) (cons_subst x t s2) z.
Proof.
  unfold subst_compose, cons_subst. destruct (eq_dec z x') as [H_eq | H_ne].
  - subst z. simpl. destruct (eq_dec x x); done.
  - rewrite forallb_forall in FRESH. unfold "∘" in FRESH.
    assert (NOT_FREE : is_free_in_trm x (s1 z) = false).
    { rewrite <- negb_true_iff. eapply FRESH. ss!. }
    eapply equiv_subst_in_trm_implies_subst_trm_same.
    intros z' FREE'. destruct (eq_dec z' x) as [EQ | NE]; ss!.
Qed.

Definition free_in_trm_wrt (x : ivar) (s : subst L) (t : trm L) : Prop :=
  exists y : ivar, is_free_in_trm y t = true /\ is_free_in_trm x (s y) = true.

Definition free_in_trms_wrt {n : nat} (x : ivar) (s : subst L) (ts : trms L n) : Prop :=
  exists y : ivar, is_free_in_trms y ts = true /\ is_free_in_trm x (s y) = true.

Definition free_in_frm_wrt (x : ivar) (s : subst L) (p : frm L) : Prop :=
  exists y : ivar, is_free_in_frm y p = true /\ is_free_in_trm x (s y) = true.

Theorem free_in_trm_wrt_iff (t : trm L) (z : ivar) (s : subst L)
  : free_in_trm_wrt z s t <-> is_free_in_trm z (subst_trm s t) = true
with free_in_trms_wrt_iff n (ts : trms L n) (z : ivar) (s : subst L)
  : free_in_trms_wrt z s ts <-> is_free_in_trms z (subst_trms s ts) = true.
Proof.
  - revert z s. unfold free_in_trm_wrt. trm_ind t; simpl; i.
    + split.
      * intros [y [FREE FREE']]. apply Nat.eqb_eq in FREE. subst y. done.
      * intros FREE. exists x. rewrite Nat.eqb_eq. done.
    + split.
      * intros [y [FREE FREE']]. eapply free_in_trms_wrt_iff. done!.
      * intros FREE. eapply free_in_trms_wrt_iff. done!.
    + done!.
  - revert z s. unfold free_in_trms_wrt. trms_ind ts; simpl; i.
    + done!.
    + split.
      * intros [y [FREE FREE']]. rewrite orb_true_iff in FREE. rewrite orb_true_iff. destruct FREE as [FREE | FREE].
        { left. eapply free_in_trm_wrt_iff. done!. }
        { right. eapply IH. exists y. done!. }
      * rewrite orb_true_iff. intros [FREE | FREE].
        { apply free_in_trm_wrt_iff in FREE. unfold free_in_trm_wrt in FREE.
          destruct FREE as [y [FREE FREE']]. exists y. rewrite orb_true_iff. done!.
        }
        { apply IH in FREE. destruct FREE as [y [FREE FREE']].
          exists y. rewrite orb_true_iff. done!.
        }
Qed.

#[local] Hint Rewrite <- free_in_trm_wrt_iff free_in_trms_wrt_iff : simplication_hints.

Theorem free_in_frm_wrt_iff (p : frm L) (z : ivar) (s : subst L)
  : free_in_frm_wrt z s p <-> is_free_in_frm z (subst_frm s p) = true.
Proof.
  revert z s. unfold free_in_frm_wrt. frm_ind p; simpl; i.
  - done!.
  - done!.
  - done!.
  - split; i; des; ss!.
    + rewrite <- IH1 in H. done!.
    + rewrite <- IH2 in H. done!.
  - split.
    + intros (w & FREE & FREE'). s!. split.
      * eapply IH1. exists w. ss!. destruct (eq_dec w y) as [? | ?]; ss!.
      * intros CONTRA. subst z.
        assert (claim1 : frm_is_fresh_in_subst (chi_frm s (All_frm y p1)) s (All_frm y p1) = true).
        { exact (chi_frm_is_fresh_in_subst (All_frm y p1) s). }
        unfold frm_is_fresh_in_subst in claim1. rewrite forallb_forall in claim1.
        assert (claim2 : In w (fvs_frm (All_frm y p1))).
        { eapply fv_is_free_in_frm. done!. }
        apply claim1 in claim2. done!.
    + rewrite andb_true_iff. rewrite negb_true_iff. rewrite Nat.eqb_neq.
      set (w := chi_frm s (All_frm y p1)). intros [FREE NE].
      apply IH1 in FREE. destruct FREE as [x [FREE FREE']].
      unfold cons_subst in FREE'. destruct (eq_dec x y) as [x_eq_y | x_ne_y].
      * subst x. contradiction NE. apply fv_is_free_in_trm in FREE'. simpl in FREE'. done!.
      * exists x. done!.
Qed.

Lemma chi_frm_ext (s1 : subst L) (s2 : subst L) (p1 : frm L) (p2 : frm L)
  (EQUIV : forall z : ivar, free_in_frm_wrt z s1 p1 <-> free_in_frm_wrt z s2 p2)
  : chi_frm s1 p1 = chi_frm s2 p2.
Proof.
  assert (claim : forall z : ivar, In z (flat_map (fvs_trm ∘ s1) (fvs_frm p1)) <-> In z (flat_map (fvs_trm ∘ s2) (fvs_frm p2))).
  { unfold free_in_frm_wrt in EQUIV. intros z. do 2 rewrite in_flat_map.
    split; intros [x [H_IN1 H_IN2]]; rewrite fv_is_free_in_frm in H_IN1; apply fv_is_free_in_trm in H_IN2; unfold "∘" in *. 
    - assert (claim1 : exists y : ivar, is_free_in_frm y p1 = true /\ is_free_in_trm z (s1 y) = true) by done!.
      apply EQUIV in claim1. destruct claim1 as [y [FREE FREE']]. apply fv_is_free_in_frm in FREE. apply fv_is_free_in_trm in FREE'. exists y. done!.
    - assert (claim2 : exists y : ivar, is_free_in_frm y p2 = true /\ is_free_in_trm z (s2 y) = true) by done!.
      apply EQUIV in claim2. destruct claim2 as [y [FREE FREE']]. apply fv_is_free_in_frm in FREE. apply fv_is_free_in_trm in FREE'. exists y. done!.
  }
  apply maxs_ext in claim. unfold chi_frm. f_equal. unfold last_ivar_trm.
  assert (ENOUGH: forall xs: list ivar, forall f: ivar -> list ivar, maxs (List.map (maxs ∘ f) xs) = maxs (List.flat_map f xs)).
  { induction xs; simpl; i; eauto; rewrite maxs_app; ss!. }
  do 2 rewrite <- ENOUGH in claim. done!.
Qed.

Theorem subst_compose_trm_spec (t : trm L) (s : subst L) (s' : subst L)
  : subst_trm (subst_compose s s') t = subst_trm s' (subst_trm s t)
with subst_compose_trms_spec n (ts : trms L n) (s : subst L) (s' : subst L)
  : subst_trms (subst_compose s s') ts = subst_trms s' (subst_trms s ts).
Proof.
  - clear subst_compose_trm_spec; revert s s'. trm_ind t; simpl; i; done!.
  - clear subst_compose_trms_spec; revert s s'. trms_ind ts; simpl; i; done!.
Qed.

#[local] Hint Rewrite <- subst_compose_trm_spec subst_compose_trms_spec : simplication_hints.

Theorem subst_compose_frm_spec (p : frm L) (s : subst L) (s' : subst L)
  : subst_frm (subst_compose s s') p = subst_frm s' (subst_frm s p).
Proof.
  revert s s'. frm_ind p; simpl; i.
  - done!.
  - done!.
  - done!.
  - done!.
  - enough (ENOUGH : chi_frm s' (subst_frm s (All_frm y p1)) = chi_frm (subst_compose s s') (All_frm y p1)).
    { revert ENOUGH.
      set (x := chi_frm s (All_frm y p1)).
      set (z := chi_frm (subst_compose s s') (All_frm y p1)).
      set (w := chi_frm s' (All_frm x (subst_frm (cons_subst y (Var_trm x) s) p1))).
      i. rewrite <- IH1. assert (EQ : z = w) by done. subst z. f_equal; trivial.
      eapply equiv_subst_in_frm_implies_subst_frm_same. unfold equiv_subst_in_frm. ii.
      rewrite <- distr_compose_one with (p := p1).
      - now rewrite EQ.
      - change (frm_is_fresh_in_subst x s (All_frm y p1) = true). eapply chi_frm_is_fresh_in_subst.
      - done.
    }
    eapply chi_frm_ext. intros z. split.
    + simpl. unfold free_in_frm_wrt. intros [x [FREE FREE']]. simpl in FREE.
      rewrite andb_true_iff in FREE. rewrite negb_true_iff in FREE. rewrite Nat.eqb_neq in FREE.
      destruct FREE as [FREE NE]. apply free_in_frm_wrt_iff in FREE. unfold free_in_frm_wrt in FREE.
      destruct FREE as [w [FREE1 FREE2]]. unfold cons_subst in FREE2. destruct (eq_dec w y) as [w_eq_y | w_ne_y].
      * unfold is_free_in_trm in FREE2. rewrite Nat.eqb_eq in FREE2. subst x y. done.
      * exists w. simpl. done!.
    + intros [x [FREE FREE']]. simpl in FREE. rewrite andb_true_iff in FREE. rewrite negb_true_iff in FREE. rewrite Nat.eqb_neq in FREE. destruct FREE as [FREE NE].
      apply free_in_trm_wrt_iff in FREE'. destruct FREE' as [u [FREE' FREE'']]. exists u. split.
      * eapply free_in_frm_wrt_iff. exists x. simpl. done!.
      * done!.
Qed.

#[local] Hint Rewrite <- subst_compose_frm_spec : simplication_hints.

Definition rename_trm (eta : renaming) : trm L -> trm L :=
  subst_trm (Var_trm ∘ eta)%prg.

Definition rename_trms {n : nat} (eta : renaming) : trms L n -> trms L n :=
  subst_trms (Var_trm ∘ eta)%prg.

Definition rename_frm (eta : renaming) : frm L -> frm L :=
  subst_frm (Var_trm ∘ eta)%prg.

Lemma rename_frm_subst (s : subst L) (eta : renaming) (eta' : renaming) (p : frm L)
  (eta_inj : forall z : ivar, is_free_in_frm z p = true -> eta' (eta z) = z)
  : rename_frm eta (subst_frm s p) = subst_frm (rename_trm eta ∘ s ∘ eta')%prg (rename_frm eta p).
Proof.
  unfold rename_frm. do 2 rewrite <- subst_compose_frm_spec. eapply equiv_subst_in_frm_implies_subst_frm_same.
  ii; unfold "∘"%prg in *; unfold subst_compose in *. symmetry. rewrite subst_trm_unfold. rewrite eta_inj; done.
Qed.

Lemma rename_frm_one_subst (eta : renaming) (x : ivar) (t : trm L) (p : frm L)
  (eta_inj : exists eta' : renaming, forall z : ivar, is_free_in_frm z p = true \/ z = x -> eta' (eta z) = z)
  : rename_frm eta (subst_frm (one_subst x t) p) = subst_frm (one_subst (eta x) (rename_trm eta t)) (rename_frm eta p).
Proof.
  destruct eta_inj as [eta' eta_inj].
  assert (claim1 : eta' (eta x) = x) by done!.
  assert (claim2 : forall z : ivar, is_free_in_frm z p = true -> eta' (eta z) = z) by done!.
  rewrite rename_frm_subst with (eta' := eta'); trivial.
  unfold rename_frm. do 2 rewrite <- subst_compose_frm_spec. eapply equiv_subst_in_frm_implies_subst_frm_same.
  ii. unfold subst_compose. unfold "∘"%prg. simpl. rewrite claim2; trivial.
  unfold one_subst, cons_subst, nil_subst. destruct (eq_dec (eta z) (eta x)) as [eta_EQ | eta_NE].
  - eapply f_equal with (f := eta') in eta_EQ. rewrite claim1 in eta_EQ. rewrite claim2 in eta_EQ; trivial.
    subst z. destruct (eq_dec x x); done.
  - destruct (eq_dec z x); done!.
Qed.

Lemma trivial_subst (x : ivar) (p : frm L)
  : subst_frm (one_subst x (Var_trm x)) p = subst_frm nil_subst p.
Proof.
  unfold one_subst, cons_subst, nil_subst. eapply equiv_subst_in_frm_implies_subst_frm_same.
  unfold equiv_subst_in_frm. ii. destruct (eq_dec z x) as [H_yes | H_no]; done!.
Qed.

Lemma compose_one_subst_frm (x1 : ivar) (t1 : trm L) (s : subst L) (p : frm L)
  : subst_frm s (subst_frm (one_subst x1 t1) p) = subst_frm (cons_subst x1 (subst_trm s t1) s) p.
Proof.
  unfold one_subst. rewrite <- subst_compose_frm_spec. eapply equiv_subst_in_frm_implies_subst_frm_same. ii.
  unfold cons_subst, nil_subst, subst_compose. destruct (eq_dec z x1) as [z_eq_x1 | z_ne_x1]; done!.
Qed.

Lemma cons_subst_subst_frm (x1 : ivar) (t1 : trm L) (y : ivar) (p : frm L) (s : subst L)
  (NOT_FREE: is_free_in_frm y p = false \/ y = x1)
  : subst_frm (cons_subst x1 t1 s) p = subst_frm (cons_subst y t1 s) (subst_frm (one_subst x1 (Var_trm y)) p).
Proof.
  unfold one_subst. rewrite <- subst_compose_frm_spec. eapply equiv_subst_in_frm_implies_subst_frm_same.
  ii. unfold cons_subst, subst_compose, nil_subst. destruct (eq_dec z x1) as [z_eq_x1 | z_ne_x1].
  - subst z. simpl. destruct (eq_dec y y); done!.
  - simpl. destruct (eq_dec z y) as [z_eq_y | z_ne_y]; done!.
Qed.

Lemma subst_preserves_rank (p : frm L) (s : subst L)
  : frm_depth (subst_frm s p) = frm_depth p.
Proof.
  revert s. frm_ind p; simpl; i; ss!.
Qed.

Lemma one_subst_cons_subst (p : frm L) (x : ivar) (y : ivar) (z : ivar) (s : subst L)
  (FRESH : is_free_in_frm x p = false \/ x = y)
  : subst_frm (one_subst x (Var_trm z)) (subst_frm (cons_subst y (Var_trm z) s) p) = subst_frm (cons_subst y (Var_trm z) (subst_compose s (one_subst x (Var_trm z)))) (subst_frm (one_subst x (Var_trm y)) p).
Proof.
  symmetry. do 2 rewrite <- subst_compose_frm_spec.
  eapply equiv_subst_in_frm_implies_subst_frm_same.
  intros w FREE. unfold subst_compose at 1 3. unfold one_subst. unfold cons_subst at 3 5.
  destruct (eq_dec w x) as [w_eq_x | w_ne_x], (eq_dec w y) as [w_eq_y | w_ne_y].
  - subst w. subst y. rewrite subst_trm_unfold. symmetry. rewrite subst_trm_unfold. symmetry.
    unfold subst_compose. unfold cons_subst. destruct (eq_dec x x) as [_ | CONTRA]. 2: done.
    destruct (eq_dec z x); try done.
  - subst w. simpl in FRESH. destruct FRESH; done!.
  - subst w. unfold nil_subst at 2. do 2 rewrite subst_trm_unfold; symmetry.
    unfold cons_subst. unfold subst_compose. destruct (eq_dec y y) as [_ | CONTRA]. 2: done.
    destruct (eq_dec z x); try done!.
  - unfold nil_subst at 2. rewrite subst_trm_unfold. unfold subst_compose.
    unfold cons_subst. destruct (eq_dec w y); try done!.
Qed.

Lemma one_subst_free_assoc_lemma1 (x : ivar) (t : trm L) (z : ivar) (p : frm L)
  (NE : x <> z)
  (FREE : is_free_in_frm z p = true)
  : is_free_in_frm z (subst_frm (one_subst x t) p) = true.
Proof.
  enough (ENOUGH : is_free_in_frm z (subst_frm (one_subst x t) p) <> false).
  { destruct (is_free_in_frm z (subst_frm (one_subst x t) p)) as [ | ]; done!. }
  intros CONTRA. rewrite <- frm_is_fresh_in_subst_iff in CONTRA.
  unfold frm_is_fresh_in_subst in CONTRA. rewrite forallb_forall in CONTRA.
  rewrite <- fv_is_free_in_frm in FREE. specialize (CONTRA z FREE). s!.
  destruct (eq_dec z x); rewrite is_free_in_trm_unfold in CONTRA; ss!.
Qed.

Lemma one_subst_free_assoc_lemma2 (x : ivar) (x' : ivar) (y : ivar) (z : ivar) (p : frm L) (p' : frm L)
  (FRESH : is_free_in_frm y p = false \/ y = x)
  (NE : z <> x)
  (FREE : is_free_in_frm z p = true)
  (FREE' : is_free_in_frm z (subst_frm (one_subst x' (Var_trm y)) p') = true)
  : z <> x'.
Proof.
  intros CONTRA. enough (ENOUGH : is_free_in_frm z (subst_frm (one_subst x' (Var_trm y)) p') = false) by done!.
  rewrite <- frm_is_fresh_in_subst_iff. subst x'. unfold frm_is_fresh_in_subst.
  rewrite forallb_forall. intros w FREE''. rewrite fv_is_free_in_frm in FREE''.
  unfold "∘"%prg. rewrite negb_true_iff. unfold one_subst, cons_subst, nil_subst.
  destruct FRESH as [FRESH | NE']; destruct (eq_dec w z) as [w_eq_z | w_ne_z]; done!.
Qed.

Lemma one_subst_free_assoc_lemma3 (x : ivar) (y : ivar) (z : ivar) (p : frm L)
  (NE : z <> y)
  (FREE : is_free_in_frm z (subst_frm (one_subst x (Var_trm y)) p) = true)
  : is_free_in_frm z p = true.
Proof.
  enough (ENOUGH : is_free_in_frm z p <> false) by now destruct (is_free_in_frm z p) as [ | ].
  intros CONTRA. enough (ENOUGH : is_free_in_frm z (subst_frm (one_subst x (Var_trm y)) p) = false) by done!.
  rewrite <- frm_is_fresh_in_subst_iff. unfold frm_is_fresh_in_subst.
  rewrite forallb_forall. intros w FREE'. rewrite fv_is_free_in_frm in FREE'. s!.
  destruct (eq_dec w x) as [w_eq_x | w_ne_x]; rewrite is_free_in_trm_unfold; rewrite Nat.eqb_neq; done!.
Qed.

Lemma one_subst_free_assoc_lemma3' (x : ivar) (y : ivar) (z : ivar) (p : frm L)
  (NE : z <> y)
  (FRESH : is_free_in_frm z p = false)
  : is_free_in_frm z (subst_frm (one_subst x (Var_trm y)) p) = false.
Proof.
  pose proof (one_subst_free_assoc_lemma3 x y z p NE).
  destruct (is_free_in_frm z (subst_frm (one_subst x (Var_trm y)) p)) as [ | ], (is_free_in_frm z p) as [ | ]; done!.
Qed.

Lemma one_subst_free_assoc_lemma4 (x : ivar) (y : ivar) (z : ivar) (p : frm L)
  (NE : z <> x)
  (FREE : is_free_in_frm z p = true)
  (FRESH : is_free_in_frm y p = false \/ y = x)
  : z <> y.
Proof.
  intros CONTRA. subst z. destruct FRESH as [FRESH | NE']; done!.
Qed.

Definition fvs_eq_trm (t1 : trm L) (t2 : trm L) : Prop :=
  forall x : ivar, is_free_in_trm x t1 = true <-> is_free_in_trm x t2 = true.

Definition fvs_eq_frm (p1 : frm L) (p2 : frm L) : Prop :=
  forall x : ivar, is_free_in_frm x p1 = true <-> is_free_in_frm x p2 = true.

Lemma chi_frm_ext' (s : subst L) (s' : subst L) (p : frm L) (p' : frm L)
  (FvEq1 : forall x : ivar, is_free_in_frm x p = true -> fvs_eq_trm (s x) (s' x))
  (FvEq2 : fvs_eq_frm p p')
  : chi_frm s p = chi_frm s' p'.
Proof.
  eapply chi_frm_ext. intros z. split; intros (u & FREE & FREE').
  - exists u. split.
    + eapply FvEq2. exact FREE.
    + eapply FvEq1.
      * eapply FvEq2. done!.
      * exact FREE'.
  - exists u. split.
    + eapply FvEq2. exact FREE.
    + eapply FvEq1.
      * eapply FvEq2. done!.
      * exact FREE'.
Qed.

Inductive alpha_equiv : frm L -> frm L -> Prop :=
  | alpha_Rel_frm R ts ts'
    (EQ : ts = ts')
    : Rel_frm R ts ≡ Rel_frm R ts'
  | alpha_Eqn_frm t1 t2 t1' t2'
    (EQ1 : t1 = t1')
    (EQ2 : t2 = t2')
    : Eqn_frm t1 t2 ≡ Eqn_frm t1' t2'
  | alpha_Neg_frm p1 p1'
    (ALPHA1 : p1 ≡ p1')
    : Neg_frm p1 ≡ Neg_frm p1'
  | alpha_Imp_frm p1 p2 p1' p2'
    (ALPHA1 : p1 ≡ p1')
    (ALPHA2 : p2 ≡ p2')
    : Imp_frm p1 p2 ≡ Imp_frm p1' p2'
  | alpha_All_frm z y y' p1 p1'
    (ALPHA1 : subst_frm (one_subst y (Var_trm z)) p1 ≡ subst_frm (one_subst y' (Var_trm z)) p1')
    (LFRESH : is_free_in_frm z (All_frm y p1) = false)
    (RFRESH : is_free_in_frm z (All_frm y' p1') = false)
    : All_frm y p1 ≡ All_frm y' p1'
  where " p ≡ p' " := (alpha_equiv p p') : type_scope.

#[local] Hint Constructors alpha_equiv : core.

Lemma is_free_in_frm_compat_alpha_equiv (p : frm L) (p' : frm L) (x : ivar)
  (ALPHA : p ≡ p')
  (FREE : is_free_in_frm x p = true)
  : is_free_in_frm x p' = true.
Proof.
  revert x FREE. induction ALPHA; simpl in *; i.
  - done!.
  - done!.
  - done!.
  - done!.
  - rewrite!. destruct FREE as [FREE NE]. 
    assert (claim1 : x <> y').
    { intros CONTRA. subst y'.
      eapply one_subst_free_assoc_lemma2 with (p := p1) (p' := p1').
      - exact LFRESH.
      - exact NE.
      - exact FREE.
      - eapply IHALPHA. eapply one_subst_free_assoc_lemma1; done!.
      - done!.
    }
    split; trivial. eapply one_subst_free_assoc_lemma3.
    + eapply one_subst_free_assoc_lemma4.
      * exact NE.
      * exact FREE.
      * exact LFRESH.
    + eapply IHALPHA.
      * eapply one_subst_free_assoc_lemma1; done!.
Qed.

#[global]
Instance alpha_equiv_Reflexive
  : Reflexive alpha_equiv.
Proof.
  intros p. pattern p. revert p. eapply frm_depth_lt_ind. i.
  destruct p as [R ts | t1 t2 | p1 | p1 p2 | y p1]; simpl.
  - econs; done!.
  - econs; done!.
  - econs; done!.
  - econs; done!.
  - eapply alpha_All_frm with (z := y).
    + eapply IH. rewrite subst_preserves_rank. ss!.
    + ss!.
    + ss!.
Qed.

#[global]
Instance alpha_equiv_Symmetric
  : Symmetric alpha_equiv.
Proof.
  intros p1 p2 EQ1. induction EQ1; simpl; econs; done!.
Qed.

Lemma alpha_equiv_compat_fresh (p : frm L) (p' : frm L) (x : ivar)
  (ALPHA : p ≡ p')
  : is_free_in_frm x p = false <-> is_free_in_frm x p' = false.
Proof.
  split.
  - symmetry in ALPHA.
    pose proof (is_free_in_frm_compat_alpha_equiv p' p x ALPHA).
    destruct (is_free_in_frm x p') as [ | ], (is_free_in_frm x p) as [ | ]; done!.
  - pose proof (is_free_in_frm_compat_alpha_equiv p p' x ALPHA).
    destruct (is_free_in_frm x p) as [ | ], (is_free_in_frm x p') as [ | ]; done!.
Qed.

Lemma subst_frm_compat_alpha_equiv (p : frm L) (p' : frm L) (s : subst L)
  (ALPHA : p ≡ p')
  : subst_frm s p = subst_frm s p'.
Proof.
  revert s. induction ALPHA; simpl; i.
  - done!.
  - done!.
  - done!.
  - done!.
  - assert (claim1 : chi_frm s (All_frm y p1) = chi_frm s (All_frm y' p1')).
    { eapply chi_frm_ext'.
      - ii; reflexivity.
      - red. intros x; split; intros FREE.
        + eapply is_free_in_frm_compat_alpha_equiv.
          * eapply alpha_All_frm with (z := z); done!.
          * exact FREE.
        + eapply is_free_in_frm_compat_alpha_equiv.
          * symmetry. eapply alpha_All_frm with (z := z); done!.
          * exact FREE.
    }
    f_equal; trivial. rename y into x, y' into x'.
    rewrite <- claim1. clear claim1. set (y := chi_frm s (All_frm x p1)).
    erewrite cons_subst_subst_frm with (p := p1) (y := z).
    erewrite cons_subst_subst_frm with (p := p1') (y := z).
    + eapply IHALPHA.
    + ss!.
    + ss!.
Qed.

#[global]
Instance alpha_equiv_Transitive
  : Transitive alpha_equiv.
Proof.
  intros p1 p2 p3 EQ EQ'. revert p3 EQ'. induction EQ; simpl; i.
  - done!.
  - done!.
  - inv EQ'; econs; done!.
  - inv EQ'; econs; done!.
  - inv EQ'. rename y'0 into y'', z0 into z', LFRESH0 into LFRESH', RFRESH0 into RFRESH', p1'0 into p1''.
    assert (claim : subst_frm (one_subst y (Var_trm z)) p1 ≡ subst_frm (one_subst y'' (Var_trm z)) p1'').
    { eapply IHEQ. unfold one_subst. erewrite cons_subst_subst_frm. 2:{ simpl in LFRESH'. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in LFRESH'. exact LFRESH'. }
      symmetry. erewrite cons_subst_subst_frm. 2:{ simpl in RFRESH'. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in RFRESH'. exact RFRESH'. }
      symmetry. pose proof (subst_frm_compat_alpha_equiv _ _ (cons_subst z' (Var_trm z) nil_subst) ALPHA1) as claim1. now rewrite claim1.
    }
    eapply alpha_All_frm with (z := z); trivial. erewrite <- alpha_equiv_compat_fresh.
    + exact RFRESH.
    + econstructor; eauto.
Qed.

#[global]
Instance alpha_equiv_Equivalence : Equivalence alpha_equiv :=
  { Equivalence_Reflexive := alpha_equiv_Reflexive
  ; Equivalence_Symmetric := alpha_equiv_Symmetric
  ; Equivalence_Transitive := alpha_equiv_Transitive
  }.

Lemma alpha_equiv_eq_intro (p1 : frm L) (p2 : frm L)
  (EQ : p1 = p2)
  : p1 ≡ p2.
Proof. 
  now subst p2.
Qed.

Lemma subst_nil_trm (t : trm L) (s : subst L)
  (FRESH : forall x : ivar, is_free_in_trm x t = true -> s x = Var_trm x)
  : subst_trm s t = t
with subst_nil_trms n (ts : trms L n) (s : subst L)
  (FRESH: forall x : ivar, is_free_in_trms x ts = true -> s x = Var_trm x)
  : subst_trms s ts = ts.
Proof.
  -  clear subst_nil_trm. revert s FRESH. trm_ind t; simpl; i.
    + eapply FRESH. done!.
    + f_equal. eapply subst_nil_trms with (s := s). done!.
    + done!.
  - clear subst_nil_trms. revert s FRESH. trms_ind ts; simpl; i.
    + done!.
    + f_equal; done!.
Qed.

Lemma subst_nil_frm (p : frm L) (s : subst L)
  (FRESH : forall x : ivar, is_free_in_frm x p = true -> s x = Var_trm x)
  : subst_frm s p ≡ p.
Proof.
  revert s FRESH. pattern p; revert p; eapply frm_depth_lt_ind; i. destruct p; simpl in *.
  - econstructor. eapply subst_nil_trms; done!.
  - econstructor; eapply subst_nil_trm; ii; eapply FRESH; rewrite orb_true_iff; done!.
  - econstructor. eapply IH; done!.
  - econstructor; eapply IH; done!.
  - assert (chi_fresh : is_free_in_frm (chi_frm s (All_frm y p)) (All_frm y p) = false).
    { pose proof (@chi_frm_is_fresh_in_subst (All_frm y p) s) as claim.
      unfold frm_is_fresh_in_subst in claim. rewrite forallb_forall in claim.
      unfold "∘"%prg in claim. enough (ENOUGH: is_free_in_frm (chi_frm s (All_frm y p)) (All_frm y p) <> true) by now destruct (is_free_in_frm (chi_frm s (All_frm y p)) (All_frm y p)).
      intros CONTRA. rewrite <- fv_is_free_in_frm in CONTRA. specialize (claim (chi_frm s (All_frm y p)) CONTRA).
      rewrite negb_true_iff in claim. rewrite FRESH in claim.
      * rewrite is_free_in_trm_unfold in claim. rewrite Nat.eqb_neq in claim. done.
      * rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq. rewrite fv_is_free_in_frm in CONTRA.
        rewrite is_free_in_frm_unfold in CONTRA. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq in CONTRA. done.
    }
    eapply alpha_All_frm with (z := chi_frm s (All_frm y p)).
    { transitivity (subst_frm (cons_subst y (Var_trm (chi_frm s (All_frm y p))) s) p).
      - eapply IH.
        + rewrite subst_preserves_rank. done.
        + intros x FREE. unfold one_subst, cons_subst, nil_subst.
          destruct (eq_dec x (chi_frm s (All_frm y p))); done!.
      - eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
        ii. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec z y) as [EQ | NE].
        + done.
        + eapply FRESH. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq. done!.
    }
    { rewrite is_free_in_frm_unfold, andb_false_iff, negb_false_iff, Nat.eqb_eq. done!. }
    { exact chi_fresh. }
Qed.

Lemma alpha_equiv_if_subst_nil_eq (p1 : frm L) (p2 : frm L)
  (EQ : subst_frm nil_subst p1 = subst_frm nil_subst p2)
  : p1 ≡ p2.
Proof.
  revert p2 EQ. pattern p1. revert p1. eapply frm_depth_lt_ind; i. destruct p; simpl in *.
  - rewrite subst_nil_trms in EQ. rewrite <- subst_nil_frm with (p := p2) (s := nil_subst). eapply alpha_equiv_eq_intro. done.
    { ii. reflexivity. }
    { ii. reflexivity. }
  - rewrite subst_nil_trm in EQ. rewrite subst_nil_trm in EQ. rewrite <- subst_nil_frm with (p := p2) (s := nil_subst). eapply alpha_equiv_eq_intro; done.
    { ii. reflexivity. }
    { ii. reflexivity. }
    { ii. reflexivity. }
  - transitivity (subst_frm nil_subst p2).
    { rewrite <- EQ. econstructor. symmetry. eapply subst_nil_frm. ii. reflexivity. }
    { eapply subst_nil_frm. ii. reflexivity. }
  - transitivity (subst_frm nil_subst p2).
    { rewrite <- EQ. econstructor; symmetry; eapply subst_nil_frm; ii; reflexivity. }
    { eapply subst_nil_frm. ii. reflexivity. }
  - transitivity (subst_frm nil_subst p2).
    { rewrite <- EQ. econstructor.
      - symmetry. eapply subst_nil_frm. ii. unfold one_subst, cons_subst. destruct (eq_dec x (chi_frm nil_subst (All_frm y p))); done!.
      - enough (ENOUGH : is_free_in_frm (chi_frm nil_subst (All_frm y p)) (All_frm y p) <> true) by now destruct (is_free_in_frm (chi_frm nil_subst (All_frm y p)) (All_frm y p)).
        intros CONTRA. pose proof (@chi_frm_not_free nil_subst (All_frm y p) (chi_frm nil_subst (All_frm y p)) CONTRA) as claim.
        unfold nil_subst at 2 in claim. rewrite is_free_in_trm_unfold in claim. rewrite Nat.eqb_neq in claim. done.
      - rewrite is_free_in_frm_unfold. done!.
    }
    { eapply subst_nil_frm. ii. reflexivity. }
Qed.

Lemma alpha_equiv_compath_rank (p : frm L) (p' : frm L)
  (ALPHA : p ≡ p')
  : frm_depth p = frm_depth p'.
Proof.
  erewrite <- subst_preserves_rank with (s := nil_subst). symmetry.
  erewrite <- subst_preserves_rank with (s := nil_subst). symmetry.
  f_equal. eapply subst_frm_compat_alpha_equiv. exact ALPHA.
Qed.

Lemma alpha_equiv_inv_subst (s : subst L) (p : frm L) (p' : frm L)
  (ALPHA : subst_frm s p ≡ p')
  : subst_frm s p = subst_frm nil_subst p'.
Proof.
  apply subst_frm_compat_alpha_equiv with (s := nil_subst) in ALPHA.
  rewrite <- subst_compose_frm_spec in ALPHA. rewrite <- ALPHA.
  eapply equiv_subst_in_frm_implies_subst_frm_same. ii.
  unfold subst_compose. rewrite subst_nil_trm; done!.
Qed.

Corollary alpha_equiv_iff_subst_nil_eq (p : frm L) (p' : frm L)
  : p ≡ p' <-> subst_frm nil_subst p = subst_frm nil_subst p'.
Proof.
  split; [intros EQUIV | intros EQ].
  - eapply alpha_equiv_inv_subst. rewrite <- EQUIV. eapply subst_nil_frm. done!.
  - eapply alpha_equiv_if_subst_nil_eq; done!.
Qed.

#[global]
Add Parametric Morphism
  : subst_frm with signature (eq ==> alpha_equiv ==> eq) as subst_frm_alpha_equiv_returns_eq.
Proof.
  intros s. intros p1 p2 ALPHA. etransitivity.
  - eapply subst_frm_compat_alpha_equiv. exact ALPHA.
  - eapply equiv_subst_in_frm_implies_subst_frm_same.
    ii. reflexivity.
Qed.

#[global]
Add Parametric Morphism
  : subst_frm with signature (eq ==> alpha_equiv ==> alpha_equiv) as subst_frm_alpha_equiv_returns_alpha_equiv.
Proof.
  intros s. intros p1 p2 ALPHA.
  eapply alpha_equiv_eq_intro. eapply subst_frm_alpha_equiv_returns_eq; eauto with *.
Qed.

Lemma alpha_equiv_All_frm_intro (y : ivar) (p1 : frm L) (p2 : frm L)
  (ALPHA : p1 ≡ p2)
  : All_frm y p1 ≡ All_frm y p2.
Proof.
  eapply alpha_All_frm with (z := y).
  - rewrite ALPHA. reflexivity.
  - done!.
  - done!.
Qed.

#[global]
Add Parametric Morphism
  : Neg_frm with signature (alpha_equiv ==> alpha_equiv)
  as Neg_frm_alpha_equiv_alpha_equiv.
Proof.
  ii. eapply alpha_Neg_frm; done.
Qed.

#[global]
Add Parametric Morphism
  : Imp_frm with signature (alpha_equiv ==> alpha_equiv ==> alpha_equiv)
  as Neg_frm_alpha_equiv_alpha_equiv_alpha_equiv.
Proof.
  ii. eapply alpha_Imp_frm; done.
Qed.

#[global]
Add Parametric Morphism
  : All_frm with signature (eq ==> alpha_equiv ==> alpha_equiv)
  as All_frm_eq_alpha_equiv_alpha_equiv.
Proof.
  intros y p1 p2 ALPHA. eapply alpha_equiv_All_frm_intro. exact ALPHA.
Qed.

Lemma subst_subst_alpha (p : frm L) (x1 : ivar) (x2 : ivar) (t1 : trm L) (t2 : trm L)
  (NE : x1 <> x2)
  (FRESH : is_not_free_in_trm x1 t2)
  : subst_frm (one_subst x2 t2) (subst_frm (one_subst x1 t1) p) ≡ subst_frm (one_subst x1 (subst_trm (one_subst x2 t2) t1)) (subst_frm (one_subst x2 t2) p).
Proof.
  rewrite <- subst_compose_frm_spec. rewrite <- subst_compose_frm_spec.
  eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
  unfold subst_compose. ii. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec z x1) as [EQ1 | NE1].
  - subst z. destruct (eq_dec x1 x2) as [EQ2 | NE2].
    + done.
    + symmetry. rewrite subst_trm_unfold. symmetry. destruct (eq_dec x1 x1) as [EQ3 | NE3].
      * reflexivity.
      * done.
  - rewrite subst_trm_unfold. destruct (eq_dec z x2) as [EQ2 | NE2].
    + subst z. symmetry. eapply subst_nil_trm. intros u u_free. destruct (eq_dec u x1) as [EQ3 | NE3].
      * subst u. red in FRESH. rewrite FRESH in u_free. done.
      * reflexivity.
    + symmetry. rewrite subst_trm_unfold. symmetry. destruct (eq_dec z x1) as [EQ3 | NE3].
      * done.
      * reflexivity.
Qed.

Lemma alpha_is_not_free_in_frm (p : frm L) (p' : frm L) (x : ivar)
  (ALPHA : p ≡ p')
  (NOT_FREE : is_not_free_in_frm x p)
  : is_not_free_in_frm x p'.
Proof.
  red. red in NOT_FREE. symmetry in ALPHA. pose proof (is_free_in_frm_compat_alpha_equiv p' p x ALPHA). destruct (is_free_in_frm x p') as [ | ]; done!.
Qed.

Definition close_ivars (p : frm L) : list ivar -> frm L :=
  @list_rec _ (fun _ => frm L) p (fun x => fun _ => fun q => All_frm x q).

Definition closed_frm (p : frm L) : frm L :=
  close_ivars p (nodup eq_dec (fvs_frm p)).

Definition fresh_var (x : ivar) (t : trm L) (p : frm L) : ivar :=
  1 + maxs ([x] ++ fvs_trm t ++ fvs_frm p).

Lemma fresh_var_ne_x (x : ivar) (t : trm L) (p : frm L)
  : fresh_var x t p = x <-> False.
Proof.
  unfold fresh_var. simpl. lia.
Qed.

Lemma fresh_var_is_not_free_in_trm (x : ivar) (t : trm L) (p : frm L)
  : is_free_in_trm (fresh_var x t p) t = false.
Proof.
  eapply last_ivar_trm_gt.
  unfold fresh_var. unfold last_ivar_trm.
  rewrite maxs_app. rewrite maxs_app. lia.
Qed.

Lemma fresh_var_is_not_free_in_frm (x : ivar) (t : trm L) (p : frm L)
  : is_free_in_frm (fresh_var x t p) p = false.
Proof.
  eapply last_ivar_frm_gt.
  unfold fresh_var. unfold last_ivar_frm.
  rewrite maxs_app. rewrite maxs_app. lia.
Qed.

#[local] Hint Rewrite fresh_var_ne_x fresh_var_is_not_free_in_trm fresh_var_is_not_free_in_frm : simplication_hints.

Inductive subst1_spec (x : ivar) (t : trm L) : frm L -> frm L -> Prop :=
  | subst1_All_EQ y p
    (EQ : x = y)
    : subst1_spec x t (All_frm y p) (All_frm y p)
  | subst1_All_FRESH y p1 p1'
    (NE : x <> y)
    (NOT_OCCUR : is_free_in_trm y t = false)
    (SUBST1 : subst1_spec x t p1 p1')
    : subst1_spec x t (All_frm y p1) (All_frm y p1')
  | subst1_All_RENAME y z p1 p1' p1''
    (NEW_IVAR : z = fresh_var x t p1)
    (NE : x <> y)
    (NOT_OCCUR : is_free_in_trm y t = true)
    (SUBST1 : subst1_spec y (Var_trm z) p1 p1')
    (SUBST2 : subst1_spec x t p1' p1'')
    : subst1_spec x t (All_frm y p1) (All_frm z p1'')
  | subst1_Atomic p p'
    (RANK_ZERO : frm_depth p = 0)
    (EQ : p' = subst_frm (one_subst x t) p)
    : subst1_spec x t p p'
  | subst1_Neg p1 p1'
    (SUBST1 : subst1_spec x t p1 p1')
    : subst1_spec x t (Neg_frm p1) (Neg_frm p1')
  | subst1_Imp p1 p2 p1' p2'
    (SUBST1 : subst1_spec x t p1 p1')
    (SUBST2 : subst1_spec x t p2 p2')
    : subst1_spec x t (Imp_frm p1 p2) (Imp_frm p1' p2').

Lemma subst1_uniquely_exists x t
  : forall p : frm L, { p' : frm L | subst1_spec x t p p' /\ frm_depth p = frm_depth p' /\ (forall q' : frm L, forall SUBST : subst1_spec x t p q', q' = p') }.
Proof.
  intros p. revert x t. pattern p. revert p. eapply frm_depth_lt_ind. i.
  change (forall q, frm_depth q < frm_depth p -> forall x, forall t, { p' : frm L | subst1_spec x t q p'/\ frm_depth q = frm_depth p' /\ (forall q' : frm L, forall SUBST : subst1_spec x t q q', q' = p') }) in IH.
  destruct p.
  - exists (Rel_frm R (subst_trms (one_subst x t) ts)).
    split. { eapply subst1_Atomic; reflexivity. }
    split. { simpl; reflexivity. }
    ii. inv SUBST. { reflexivity. }
  - exists (Eqn_frm (subst_trm (one_subst x t) t1) (subst_trm (one_subst x t) t2)).
    split. { eapply subst1_Atomic; reflexivity. }
    split. { simpl; reflexivity. }
    ii. inv SUBST. { reflexivity. }
  - assert (rank_LT1 : frm_depth p < frm_depth (Neg_frm p)) by now simpl; lia.
    pose proof (IH p rank_LT1 x t) as [p' [SUBST1 [RANK_EQ1 UNIQUE1]]].
    exists (Neg_frm p').
    split. { eapply subst1_Neg; trivial. }
    split. { simpl; lia. }
    ii. inv SUBST. { inv RANK_ZERO. } { f_equal. eapply UNIQUE1. trivial. }
  - assert (rank_LT1 : frm_depth p1 < frm_depth (Imp_frm p1 p2)) by now simpl; lia.
    assert (rank_LT2 : frm_depth p2 < frm_depth (Imp_frm p1 p2)) by now simpl; lia.
    pose proof (IH p1 rank_LT1 x t) as [p1' [SUBST1 [RANK_EQ1 UNIQUE1]]]. pose proof (IH p2 rank_LT2 x t) as [p2' [SUBST2 [RANK_EQ2 UNIQUE2]]].
    exists (Imp_frm p1' p2').
    split. { eapply subst1_Imp; trivial. }
    split. { simpl; lia. }
    ii. inv SUBST. { inv RANK_ZERO. } { f_equal. eapply UNIQUE1; trivial. eapply UNIQUE2; trivial. }
  - pose proof (eq_dec x y) as [EQ | NE].
    + exists (All_frm y p).
      split. { eapply subst1_All_EQ; trivial. }
      split. { simpl; lia. }
      ii. inv SUBST. { reflexivity. } { contradiction. } { contradiction. } { inv RANK_ZERO. }
    + destruct (is_free_in_trm y t) as [ | ] eqn: H_OBS.
      * set (z := fresh_var x t p).
        assert (rank_LT1 : frm_depth p < frm_depth (All_frm y p)) by now simpl; lia.
        pose proof (IH p rank_LT1 y (Var_trm z)) as [p' [SUBST1 [RANK_EQ1 UNIQUE1]]].
        assert (rank_LT2 : frm_depth p' < frm_depth (All_frm y p)) by now simpl; lia.
        pose proof (IH p' rank_LT2 x t) as [p'' [SUBST2 [RANK_EQ2 UNIQUE2]]].
        exists (All_frm z p'').
        split. { eapply subst1_All_RENAME with (p1' := p'); trivial. }
        split. { simpl; lia. }
        ii. inv SUBST. { contradiction. } { rewrite H_OBS in NOT_OCCUR; discriminate. } { f_equal; eapply UNIQUE2; apply UNIQUE1 in SUBST0; done!. } { inv RANK_ZERO. }
      * assert (rank_LT1' : frm_depth p < frm_depth (All_frm y p)) by now rewrite frm_depth_unfold with (p := All_frm y p); lia.
        pose proof (IH p rank_LT1' x t) as [p' [SUBST1 [RANK_EQ1 UNIQUE1]]].
        exists (All_frm y p').
        split. { eapply subst1_All_FRESH; trivial. }
        split. { simpl; lia. }
        ii. inv SUBST. { contradiction. } { f_equal; eapply UNIQUE1; trivial. } { rewrite H_OBS in NOT_OCCUR; discriminate. } { inv RANK_ZERO. }
Qed.

Definition subst1 (x : ivar) (t : trm L) (p : frm L) : frm L :=
  proj1_sig (subst1_uniquely_exists x t p).

Lemma subst1_preserves_rank (x : ivar) (t : trm L) (p : frm L)
  : frm_depth (subst1 x t p) = frm_depth p.
Proof.
  unfold subst1. destruct (subst1_uniquely_exists x t p) as [p' [SUBST RANK_EQ]]; simpl. lia.
Qed.

Lemma subst1_satisfies_spec (x : ivar) (t : trm L) (p : frm L)
  : subst1_spec x t p (subst1 x t p).
Proof.
  unfold subst1. destruct (subst1_uniquely_exists x t p) as [q' [SUBST [RANK_EQ UNIQUE]]]; simpl. done. 
Qed.

Lemma subst1_satisfies_spec_uniquely (x : ivar) (t : trm L) (p : frm L)
  : forall q, subst1_spec x t p q <-> q = subst1 x t p.
Proof.
  intros q. unfold subst1. destruct (subst1_uniquely_exists x t p) as [p' [SPEC [RANK_EQ UNIQUE]]]; simpl.
  split. { eapply UNIQUE. } { intros ->. exact SPEC. }
Qed.

Lemma subst1_unfold (x : ivar) (t : trm L) (p : frm L) :
  subst1 x t p =
  match p with
  | Rel_frm R ts => Rel_frm R (subst_trms (one_subst x t) ts)
  | Eqn_frm t1 t2 => Eqn_frm (subst_trm (one_subst x t) t1) (subst_trm (one_subst x t) t2)
  | Neg_frm p1 => Neg_frm (subst1 x t p1)
  | Imp_frm p1 p2 => Imp_frm (subst1 x t p1) (subst1 x t p2)
  | All_frm y p1 =>
    let z : ivar := fresh_var x t p1 in
    if eq_dec x y then All_frm y p1 else if is_free_in_trm y t then All_frm z (subst1 x t (subst1 y (Var_trm z) p1)) else All_frm y (subst1 x t p1)
  end.
Proof.
  unfold subst1 at 1. symmetry. destruct (subst1_uniquely_exists x t p) as [q' [SUBST [RANK_EQ UNIQUE]]]. simpl proj1_sig. destruct p.
  - eapply UNIQUE. simpl. eapply subst1_Atomic; trivial.
  - eapply UNIQUE. simpl. eapply subst1_Atomic; trivial.
  - eapply UNIQUE. eapply subst1_Neg; eapply subst1_satisfies_spec.
  - eapply UNIQUE. eapply subst1_Imp; eapply subst1_satisfies_spec.
  - destruct (eq_dec x y) as [EQ | NE].
    + eapply UNIQUE. eapply subst1_All_EQ; trivial.
    + destruct (is_free_in_trm y t) as [ | ] eqn: H_OBS.
      * eapply UNIQUE. eapply subst1_All_RENAME with (p1' := subst1 y (Var_trm (fresh_var x t p)) p); trivial; eapply subst1_satisfies_spec.
      * eapply UNIQUE. eapply subst1_All_FRESH; trivial. eapply subst1_satisfies_spec.
Qed.

Theorem subst1_nice x t p
  : subst1 x t p ≡ subst_frm (one_subst x t) p.
Proof.
  revert x t. pattern p. revert p. eapply frm_depth_lt_ind; ii. destruct p.
  - rewrite subst1_unfold. reflexivity.
  - rewrite subst1_unfold. reflexivity.
  - rewrite subst1_unfold. simpl. eapply alpha_Neg_frm; eapply IH; simpl; lia.
  - rewrite subst1_unfold. simpl. eapply alpha_Imp_frm; eapply IH; simpl; lia.
  - rewrite subst1_unfold. simpl.
    set (chi := chi_frm (one_subst x t) (All_frm y p)). set (z := fresh_var x t p).
    destruct (eq_dec x y) as [EQ | NE].
    { subst y. eapply alpha_All_frm with (z := chi).
      - eapply alpha_equiv_eq_intro. rewrite <- subst_compose_frm_spec. eapply equiv_subst_in_frm_implies_subst_frm_same. intros w w_free.
        unfold subst_compose. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec w x) as [EQ1 | NE1].
        + rewrite subst_trm_unfold. destruct (eq_dec chi chi) as [EQ2 | NE2]; done.
        + rewrite subst_trm_unfold. destruct (eq_dec w chi) as [EQ2 | NE2]; done!.
      - pose proof (@chi_frm_is_fresh_in_subst) as claim1.
        specialize claim1 with (p := All_frm x p) (s := one_subst x t).
        unfold frm_is_fresh_in_subst in claim1. rewrite forallb_forall in claim1. specialize (claim1 chi).
        fold chi in claim1. unfold "∘"%prg in claim1. rewrite negb_true_iff in claim1.
        rewrite fv_is_free_in_frm in claim1. destruct (is_free_in_frm chi (All_frm x p)) as [ | ] eqn: H_OBS.
        + rewrite is_free_in_frm_unfold in H_OBS. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq in H_OBS.
          specialize (claim1 eq_refl). unfold one_subst, cons_subst, nil_subst in claim1. destruct (eq_dec chi x) as [EQ | NE].
          * lia.
          * rewrite is_free_in_trm_unfold in claim1. rewrite Nat.eqb_neq in claim1. done.
        + reflexivity.
      - rewrite is_free_in_frm_unfold. done!.
    }
    destruct (is_free_in_trm y t) as [ | ] eqn: H_OBS.
    { eapply alpha_All_frm with (z := z).
      - assert (rank_LT1 : frm_depth (subst1 y (Var_trm z) p) < frm_depth (All_frm y p)).
        { rewrite subst1_preserves_rank. simpl; lia. }
        pose proof (IH _ rank_LT1 x t) as claim1.
        assert (rank_LT2 : frm_depth p < frm_depth (All_frm y p)).
        { simpl; lia. }
        pose proof (IH _ rank_LT2 y (Var_trm z)) as claim2.
        etransitivity. { eapply subst_nil_frm. intros w w_free. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec w z) as [EQ1 | NE1]; done!. }
        etransitivity. { eapply claim1. }
        apply subst_frm_compat_alpha_equiv with (s := one_subst x t) in claim2.
        rewrite claim2.
        rewrite <- subst_compose_frm_spec. rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
        intros w w_free. unfold subst_compose. unfold one_subst, cons_subst, nil_subst.
        destruct (eq_dec w y) as [EQ1 | NE1].
        { do 2 rewrite subst_trm_unfold. destruct (eq_dec z x) as [EQ2 | NE2].
          { pose proof (fresh_var_ne_x x t p). subst z. done!. }
          { destruct (eq_dec chi chi) as [EQ3 | NE3]; done!. }
        }
        { rewrite subst_trm_unfold. destruct (eq_dec w x) as [EQ2 | NE2].
          { subst w. symmetry. pose proof (@chi_frm_is_fresh_in_subst (All_frm y p) (one_subst x t)) as claim3.
            unfold frm_is_fresh_in_subst in claim3. rewrite forallb_forall in claim3. specialize (claim3 x).
            unfold "∘"%prg in claim3. rewrite negb_true_iff in claim3. fold chi in claim3.
            assert (claim4 : In x (fvs_frm (All_frm y p))).
            { rewrite fv_is_free_in_frm. simpl. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq. done. }
            apply claim3 in claim4. unfold one_subst, cons_subst, nil_subst in claim4. destruct (eq_dec x x) as [EQ' | NE'].
            - eapply subst_nil_trm. intros u u_free. destruct (eq_dec u chi) as [EQ'' | NE'']; done!.
            - done!.
          }
          { rewrite subst_trm_unfold. destruct (eq_dec w chi) as [EQ3 | NE3].
            - subst w. pose proof (@chi_frm_is_fresh_in_subst (All_frm y p) (one_subst x t)) as claim3. fold chi in claim3.
              unfold frm_is_fresh_in_subst in claim3. rewrite forallb_forall in claim3. specialize (claim3 chi).
              unfold "∘"%prg in claim3. rewrite negb_true_iff in claim3. fold chi in claim3.
              assert (claim4: In chi (fvs_frm (All_frm y p))).
              { rewrite fv_is_free_in_frm. rewrite is_free_in_frm_unfold. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq. done. }
              apply claim3 in claim4. unfold one_subst, cons_subst, nil_subst in claim4.
              destruct (eq_dec chi x) as [EQ' | NE'].
              + done.
              + rewrite is_free_in_trm_unfold in claim4. rewrite Nat.eqb_neq in claim4. done!.
            - done!.
          }
        }
      - rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. done!.
      - rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. destruct (eq_dec z chi) as [EQ' | NE'].
        + done!.
        + left. pose proof (fresh_var_ne_x x t p) as claim1. pose proof (fresh_var_is_not_free_in_trm x t p) as claim2. pose proof (fresh_var_is_not_free_in_frm x t p) as claim3.
          rewrite <- frm_is_fresh_in_subst_iff. unfold frm_is_fresh_in_subst. rewrite forallb_forall.
          intros w w_free. rewrite fv_is_free_in_frm in w_free. unfold "∘"%prg. rewrite negb_true_iff.
          unfold one_subst, cons_subst, nil_subst. fold z in claim1, claim2, claim3.
          destruct (eq_dec w y) as [EQ1 | NE1].
          { rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. done!. }
          { destruct (eq_dec w x) as [EQ2 | NE2].
            - subst w. done!.
            - rewrite is_free_in_trm_unfold. rewrite Nat.eqb_neq. intros H_contra. done!.
          }
    }
    { assert (rank_LT1 : frm_depth p < frm_depth (All_frm y p)) by now simpl; lia.
      pose proof (claim1 := IH _ rank_LT1 x t). eapply alpha_All_frm with (z := z).
      - apply subst_frm_compat_alpha_equiv with (s := one_subst y (Var_trm z)) in claim1.
        rewrite claim1. do 2 rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
        intros w w_free. unfold subst_compose. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec w x) as [EQ1 | NE1].
        { subst w. destruct (eq_dec x y) as [EQ2 | NE2].
          - done.
          - eapply equiv_subst_in_trm_implies_subst_trm_same. intros u u_free. destruct (eq_dec u y) as [EQ3 | NE3].
            + subst u. done!.
            + destruct (eq_dec u chi) as [EQ4 | NE4].
              * subst u. pose proof (@chi_frm_is_fresh_in_subst (All_frm y p) (one_subst x t)) as claim2. fold chi in claim2.
                unfold frm_is_fresh_in_subst in claim2. rewrite forallb_forall in claim2. 
                assert (claim3 : In x (fvs_frm (All_frm y p))).
                { rewrite fv_is_free_in_frm. rewrite is_free_in_frm_unfold. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq. split. done. done. }
                apply claim2 in claim3. unfold "∘"%prg in claim3. rewrite negb_true_iff in claim3.
                unfold one_subst, cons_subst, nil_subst in claim3. destruct (eq_dec x x) as [EQ5 | NE5]; done!.
              * done!.
        }
        { rewrite subst_trm_unfold. destruct (eq_dec w y) as [EQ2 | NE2].
          - rewrite subst_trm_unfold. destruct (eq_dec chi chi) as [EQ3 | NE3]; done!.
          - rewrite subst_trm_unfold. rename w into u. destruct (eq_dec u chi) as [EQ4 | NE4].
            + subst u. pose proof (@chi_frm_is_fresh_in_subst (All_frm y p) (one_subst x t)) as claim2. fold chi in claim2.
              unfold frm_is_fresh_in_subst in claim2. rewrite forallb_forall in claim2.
              assert (claim3 : In chi (fvs_frm (All_frm y p))).
              { rewrite fv_is_free_in_frm. rewrite is_free_in_frm_unfold. rewrite andb_true_iff, negb_true_iff, Nat.eqb_neq. split. done. done. }
              apply claim2 in claim3. unfold "∘"%prg in claim3. rewrite negb_true_iff in claim3.
              unfold one_subst, cons_subst, nil_subst in claim3. destruct (eq_dec chi x) as [EQ5 | NE5]. done. rewrite is_free_in_trm_unfold, Nat.eqb_neq in claim3. done.
            + done.
        }
      - rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. destruct (eq_dec z y) as [EQ1 | NE1].
        + right. done.
        + left. rewrite alpha_equiv_compat_fresh with (ALPHA := claim1).
          pose proof (@chi_frm_is_fresh_in_subst (All_frm y p) (one_subst x t)) as claim2. fold chi in claim2.
          unfold frm_is_fresh_in_subst in claim2. rewrite forallb_forall in claim2.
          destruct (is_free_in_frm z p) as [ | ] eqn: H_OBS1.
          * pose proof (fresh_var_is_not_free_in_frm x t p) as claim3. subst z. done!.
          * destruct (is_free_in_frm z (subst_frm (one_subst x t) p)) as [ | ] eqn: H_OBS2.
            { rewrite <- free_in_frm_wrt_iff in H_OBS2. unfold free_in_frm_wrt in H_OBS2.
              destruct H_OBS2 as (u&u_free&FREE). unfold one_subst, cons_subst, nil_subst in FREE. destruct (eq_dec u x) as [EQ' | NE'].
              - subst u. pose proof (fresh_var_is_not_free_in_trm x t p) as claim3. subst z. done!.
              - rewrite is_free_in_trm_unfold, Nat.eqb_eq in FREE. subst u. done!.
            }
            { done!. }
      - destruct (eq_dec z chi) as [EQ' | NE'].
        + rewrite is_free_in_frm_unfold. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq. done!.
        + assert (ALPHA : subst_frm (cons_subst y (Var_trm chi) (one_subst x t)) p ≡ subst_frm (one_subst y (Var_trm chi)) (subst1 x t p)).
          { pose proof (@subst_frm_compat_alpha_equiv (subst1 x t p) (subst_frm (one_subst x t) p) (one_subst y (Var_trm chi)) claim1) as claim2.
            rewrite claim2. rewrite <- subst_compose_frm_spec. eapply alpha_equiv_eq_intro. eapply equiv_subst_in_frm_implies_subst_frm_same.
            intros u u_free. unfold subst_compose. unfold one_subst, cons_subst, nil_subst.
            destruct (eq_dec u x) as [EQ1 | NE1].
            - subst u. destruct (eq_dec x y) as [EQ2 | NE2].
              + subst y. done.
              + symmetry. eapply subst_nil_trm. intros w w_free. destruct (eq_dec w y) as [EQ3 | NE3].
                * subst w. done!.
                * done!.
            - rewrite subst_trm_unfold. destruct (eq_dec u y) as [EQ2 | NE2]; done!.
          }
          rewrite is_free_in_frm_unfold. rewrite andb_false_iff. left.
          rewrite alpha_equiv_compat_fresh with (ALPHA := ALPHA).
          assert (claim2 : is_free_in_frm z (subst1 x t p) = false).
          { rewrite alpha_equiv_compat_fresh with (ALPHA := claim1).
            destruct (is_free_in_frm z (subst_frm (one_subst x t) p)) as [ | ] eqn: H_OBS1; trivial.
            rewrite <- free_in_frm_wrt_iff in H_OBS1. unfold free_in_frm_wrt in H_OBS1.
            destruct H_OBS1 as (u&u_free&FREE). unfold one_subst, cons_subst, nil_subst in FREE.
            destruct (eq_dec u x) as [EQ1 | NE1].
            - pose proof (fresh_var_is_not_free_in_trm x t p); subst z; done!.
            - rewrite is_free_in_trm_unfold in FREE. rewrite Nat.eqb_eq in FREE. subst u.
              pose proof (fresh_var_is_not_free_in_frm x t p); subst z; done!.
          }
          pose proof (@one_subst_free_assoc_lemma3 y chi z (subst1 x t p) NE') as claim3.
          destruct (is_free_in_frm z (subst_frm (one_subst y (Var_trm chi)) (subst1 x t p))) as [ | ] eqn: H_OBS2.
          * specialize (claim3 eq_refl). done!.
          * done!.
    }
Qed.

Lemma subst1_id x p
  : subst1 x (Var_trm x) p = p.
Proof.
  revert x. pattern p. revert p. eapply frm_depth_lt_ind.
  ii. destruct p.
  - rewrite subst1_unfold. f_equal. rewrite subst_nil_trms; trivial.
    intros u u_free. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec u x) as [EQ | NE]; done!.
  - rewrite subst1_unfold. f_equal. rewrite subst_nil_trm; trivial.
    { intros u u_free. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec u x) as [EQ | NE]; done!. }
    rewrite subst_nil_trm; trivial.
    { intros u u_free. unfold one_subst, cons_subst, nil_subst. destruct (eq_dec u x) as [EQ | NE]; done!. }
  - rewrite subst1_unfold. f_equal. eapply IH. simpl; done!.
  - rewrite subst1_unfold. f_equal; eapply IH; simpl; done!.
  - rewrite subst1_unfold. destruct (eq_dec x y) as [EQ | NE].
    + simpl. reflexivity.
    + simpl. cbn zeta. destruct (Nat.eqb x y) as [ | ] eqn: H_OBS.
      * rewrite Nat.eqb_eq in H_OBS. done!.
      * f_equal. eapply IH. simpl; lia.
Qed.

Lemma one_fv_frm_subst_closed_term_close_formula (y : ivar) (t : trm L) (p : frm L)
  (one_fv : forall z, is_free_in_frm z p = true -> z = y)
  (trm_closed : forall z, is_not_free_in_trm z t)
  : forall z, is_not_free_in_frm z (subst_frm (one_subst y t) p).
Proof.
  i. red. rewrite <- frm_is_fresh_in_subst_iff. unfold frm_is_fresh_in_subst. rewrite forallb_forall.
  intros u u_free. s!. destruct (eq_dec u y) as [EQ | NE].
  - subst u. exact (trm_closed z).
  - s!. intros ->. eapply NE. exact (one_fv z u_free).
Qed.

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
  - eapply (proj2_sig t1 z H).
  - eapply (proj2_sig t2 z H).
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
  - eapply (proj2_sig s1 z H).
  - eapply (proj2_sig s2 z H).
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

End FOL_SYNTAX.

#[global] Arguments scoped_trm : clear implicits.
#[global] Arguments scoped_trms : clear implicits.
#[global] Arguments scoped_frm : clear implicits.

Notation senetence L := (scoped_frm L []).

Section EXTEND_LANGUAGE_BY_ADDING_CONSTANTS.

#[local] Infix "=~=" := is_similar_to : type_scope.

Section SIMILARITY.

Let arity : Set := nat.

Context (_function_symbols : Set) (_relation_symbols : Set) (_function_arity_table : _function_symbols -> arity) (_relation_arity_table : _relation_symbols -> arity).

Definition mkL_with_constant_symbols (_constant_symbols : Set) : language :=
  {|
    function_symbols := _function_symbols;
    constant_symbols := _constant_symbols;
    relation_symbols := _relation_symbols;
    function_arity_table := _function_arity_table;
    relation_arity_table := _relation_arity_table;
  |}.

Context (_constant_symbols : Set) (L := mkL_with_constant_symbols _constant_symbols).

Section GENERAL_CASE.

Context (_constant_symbols' : Set) (L' := mkL_with_constant_symbols _constant_symbols').

Hypothesis constant_symbols_similarity : Similarity _constant_symbols _constant_symbols'.

Inductive trm_similarity : Similarity (trm L) (trm L') :=
  | Var_sim (x : ivar)
    : @Var_trm L x =~= @Var_trm L' x
  | Fun_sim (f : _function_symbols) (ts : trms L (L.(function_arity_table) f)) (ts' : trms L' (L'.(function_arity_table) f))
    (ts_SIM : ts =~= ts')
    : @Fun_trm L f ts =~= @Fun_trm L' f ts'
  | Con_sim (c : _constant_symbols) (c' : _constant_symbols')
    (c_SIM : c =~= c')
    : @Con_trm L c =~= @Con_trm L' c'
with trms_similarity : forall n : arity, Similarity (trms L n) (trms L' n) :=
  | O_trms_sim
    : @O_trms L =~= @O_trms L'
  | S_trms_sim (n : arity) (t : trm L) (t' : trm L') (ts : trms L n) (ts' : trms L' n)
    (t_SIM : t =~= t')
    (ts_SIM : ts =~= ts')
    : @S_trms L n t ts =~= @S_trms L' n t' ts'.

#[local] Instance trm_similarity_instance : Similarity (trm L) (trm L') :=
  trm_similarity.

#[local] Instance trms_similarity_instance (n : arity) : Similarity (trms L n) (trms L' n) :=
  trms_similarity n.

Inductive frm_similarity : Similarity (frm L) (frm L') :=
  | Rel_sim (R : _relation_symbols) (ts : trms L (L.(relation_arity_table) R)) (ts' : trms L' (L'.(relation_arity_table) R))
    (ts_SIM : ts =~= ts')
    : @Rel_frm L R ts =~= @Rel_frm L' R ts'
  | Eqn_sim (t1 : trm L) (t1' : trm L') (t2 : trm L) (t2' : trm L')
    (t1_SIM : t1 =~= t1')
    (t2_SIM : t2 =~= t2')
    : @Eqn_frm L t1 t2 =~= @Eqn_frm L' t1' t2'
  | Neg_sim (p1 : frm L) (p1' : frm L')
    (p1_SIM : p1 =~= p1')
    : @Neg_frm L p1 =~= @Neg_frm L' p1'
  | Imp_sim (p1 : frm L) (p1' : frm L') (p2 : frm L) (p2' : frm L')
    (p1_SIM : p1 =~= p1')
    (p2_SIM : p2 =~= p2')
    : @Imp_frm L p1 p2 =~= @Imp_frm L' p1' p2'
  | All_sim (y : ivar) (p1 : frm L) (p1' : frm L')
    (p1_SIM : p1 =~= p1')
    : @All_frm L y p1 =~= @All_frm L' y p1'.

#[local] Instance frm_similarity_instance : Similarity (frm L) (frm L') :=
  frm_similarity.

Lemma fvs_trm_compat_similarity (t : trm L) (t' : trm L')
  (t_SIM : t =~= t')
  : fvs_trm t = fvs_trm t'
with fvs_trms_compat_similarity n (ts : trms L n) (ts' : trms L' n)
  (ts_SIM : ts =~= ts')
  : fvs_trms ts = fvs_trms ts'.
Proof with eauto with *.
  - induction t_SIM.
    + reflexivity.
    + change (fvs_trms ts = fvs_trms ts'). eapply fvs_trms_compat_similarity. exact ts_SIM.
    + reflexivity.
  - induction ts_SIM.
    + reflexivity.
    + change (fvs_trm t ++ fvs_trms ts = fvs_trm t' ++ fvs_trms ts'). f_equal...
Qed.

Lemma fvs_frm_compat_similarity (p : frm L) (p' : frm L')
  (p_SIM : p =~= p')
  : fvs_frm p = fvs_frm p'.
Proof with try done!.
  induction p_SIM; simpl...
  - eapply fvs_trms_compat_similarity...
  - f_equal; eapply fvs_trm_compat_similarity...
Qed.

Variant frms_similarity (Gamma : ensemble (frm L)) (Gamma' : ensemble (frm L')) : Prop :=
  | frms_similarity_intro
    (FWD : forall p : frm L, p \in Gamma -> exists p' : frm L', p =~= p' /\ p' \in Gamma')
    (BWD : forall p' : frm L', p' \in Gamma' -> exists p : frm L, p =~= p' /\ p \in Gamma)
    : frms_similarity Gamma Gamma'.

#[local]
Instance frms_similarity_instance : Similarity (ensemble (frm L)) (ensemble (frm L')) :=
  frms_similarity.

Lemma fvs_trm_similarity (t : trm L) (t' : trm L')
  (t_SIM : t =~= t')
  : fvs_trm t = fvs_trm t'
with fvs_trms_similarity n (ts : trms L n) (ts' : trms L' n)
  (ts_SIM : ts =~= ts')
  : fvs_trms ts = fvs_trms ts'.
Proof.
  - induction t_SIM.
    + reflexivity.
    + do 2 rewrite fvs_trm_unfold with (t := Fun_trm _ _). eapply fvs_trms_similarity. exact ts_SIM.
    + reflexivity.
  - induction ts_SIM.
    + reflexivity.
    + do 2 rewrite fvs_trms_unfold with (ts := S_trms _ _ _). f_equal.
      * eapply fvs_trm_similarity; exact t_SIM.
      * eapply IHts_SIM; exact ts_SIM.
Qed.

#[local] Hint Resolve fvs_trm_similarity fvs_trms_similarity : core.

Lemma fvs_frm_similarity (p : frm L) (p' : frm L')
  (p_SIM : p =~= p')
  : fvs_frm p = fvs_frm p'.
Proof.
  induction p_SIM; simpl; f_equal; eauto with *.
Qed.

#[local] Hint Resolve fvs_frm_similarity : core.

Lemma chi_frm_similarity (s : subst L) (s' : subst L') (p : frm L) (p' : frm L')
  (s_SIM : s =~= s')
  (p_SIM : p =~= p')
  : chi_frm s p = chi_frm s' p'.
Proof with eauto.
  assert (ENOUGH : forall xs : list ivar, forall f : ivar -> list ivar, maxs (L.map (maxs ∘ f)%prg xs) = maxs (L.flat_map f xs)).
  { induction xs; simpl; i; eauto. unfold "∘"%prg. rewrite maxs_app. f_equal. eauto. }
  unfold chi_frm. f_equal. unfold last_ivar_trm.
  change (maxs (L.map (maxs ∘ (fvs_trm ∘ s))%prg (fvs_frm p)) = maxs (L.map (maxs ∘ (fvs_trm ∘ s'))%prg (fvs_frm p'))).
  do 2 rewrite ENOUGH. eapply maxs_ext. intros z. do 2 rewrite in_flat_map. unfold "∘"%prg. clear ENOUGH.
  split; intros [x [FREE FREE']]; exists x; split.
  - erewrite <- fvs_frm_similarity...
  - erewrite <- fvs_trm_similarity...
  - erewrite -> fvs_frm_similarity...
  - erewrite -> fvs_trm_similarity...
Qed.

Lemma subst_trm_similiarity (s : subst L) (s' : subst L') (t : trm L) (t' : trm L')
  (s_SIM : s =~= s')
  (t_SIM : t =~= t')
  : subst_trm s t =~= subst_trm s' t'
with subst_trms_similiarity n (s : subst L) (s' : subst L') (ts : trms L n) (ts' : trms L' n)
  (s_SIM : s =~= s')
  (ts_SIM : ts =~= ts')
  : subst_trms s ts =~= subst_trms s' ts'.
Proof.
  - induction t_SIM.
    + exact (s_SIM x).
    + do 2 rewrite subst_trm_unfold. econs. eapply subst_trms_similiarity; [exact s_SIM | exact ts_SIM].
    + do 2 rewrite subst_trm_unfold. econs. exact c_SIM.
  - induction ts_SIM.
    + econs.
    + do 2 rewrite subst_trms_unfold with (ts := S_trms _ _ _). econs.
      * eapply subst_trm_similiarity; [exact s_SIM | exact t_SIM].
      * assumption.
Qed.

Lemma subst_frm_similarity (s : subst L) (s' : subst L') (p : frm L) (p' : frm L')
  (s_SIM : s =~= s')
  (p_SIM : p =~= p')
  : subst_frm s p =~= subst_frm s' p'.
Proof.
  revert s s' s_SIM. induction p_SIM; i.
  - do 2 rewrite subst_frm_unfold. simpl. econs. eapply subst_trms_similiarity; trivial.
  - do 2 rewrite subst_frm_unfold. simpl. econs; eapply subst_trm_similiarity; trivial.
  - simpl. econs. done!.
  - simpl. econs; done!.
  - assert (claim : (chi_frm s (All_frm y p1)) = (chi_frm s' (All_frm y p1'))).
    { eapply chi_frm_similarity; trivial. econs; trivial. }
    simpl. rewrite claim. econs. rewrite <- claim at 1. eapply IHp_SIM.
    intros z. unfold cons_subst. destruct (eq_dec z y) as [EQ1 | NE1].
    + rewrite claim. econs.
    + exact (s_SIM z).
Qed.

End GENERAL_CASE.

End SIMILARITY.

End EXTEND_LANGUAGE_BY_ADDING_CONSTANTS.

#[global] Opaque fvs_trm fvs_trms.
#[global] Hint Rewrite @fvs_trm_unfold @fvs_trms_unfold : simplication_hints.

#[global] Opaque is_free_in_trm is_free_in_trms.
#[global] Hint Rewrite @is_free_in_trm_unfold @is_free_in_trms_unfold : simplication_hints.

#[global] Hint Rewrite @fv_is_free_in_trm @fv_is_free_in_trms @fv_is_free_in_frm @fvs_is_free_in_frms : simplication_hints.

#[global] Hint Unfold is_not_free_in_frm is_free_in_trms is_not_free_in_frm is_not_free_in_frms : simplication_hints.
#[global] Hint Unfold nil_subst cons_subst one_subst subst_compose : simplication_hints.

#[global] Opaque subst_trm subst_trms.
#[global] Hint Rewrite <- @subst_compose_trm_spec @subst_compose_trms_spec @subst_compose_frm_spec : simplication_hints.

#[global] Hint Rewrite @fresh_var_ne_x @fresh_var_is_not_free_in_trm @fresh_var_is_not_free_in_frm : simplication_hints.

#[global] Hint Unfold compose : simplication_hints.

#[local] Existing Instance V.vec_isSetoid.

Class isStructureOf (L : language) : Type :=
  { domain_of_discourse : Type
  ; equation_interpret :: isSetoid domain_of_discourse
  ; function_interpret (f : L.(function_symbols)) (vs : Vector.t domain_of_discourse (L.(function_arity_table) f)) : domain_of_discourse
  ; constant_interpret (c : L.(constant_symbols)) : domain_of_discourse
  ; relation_interpret (R : L.(relation_symbols)) (vs : Vector.t domain_of_discourse (L.(relation_arity_table) R)) : Prop
  ; domain_is_nonempty : inhabited domain_of_discourse
  ; function_interpret_preserves_eqProp (f : L.(function_symbols)) (vs1 : Vector.t domain_of_discourse (L.(function_arity_table) f)) (vs2 : Vector.t domain_of_discourse (L.(function_arity_table) f))
    (EQ : vs1 == vs2)
    : function_interpret f vs1 == function_interpret f vs2
  ; relation_interpret_preserves_eqProp (R : L.(relation_symbols)) (vs1 : Vector.t domain_of_discourse (L.(relation_arity_table) R)) (vs2 : Vector.t domain_of_discourse (L.(relation_arity_table) R))
    (EQ : vs1 == vs2)
    : relation_interpret R vs1 <-> relation_interpret R vs2
  }.

Section FOL_SEMANTICS.

Infix "≡" := alpha_equiv : type_scope.

#[local]
Tactic Notation "done" :=
  done!.

#[local] Open Scope program_scope.

Context {L : language}.

Definition upd_env {STRUCTURE : isStructureOf L} (y : ivar) (y_value : domain_of_discourse) (env : ivar -> domain_of_discourse) : ivar -> domain_of_discourse :=
  fun z : ivar => if eq_dec z y then y_value else env z.

Variable STRUCTURE : isStructureOf L.

Fixpoint interpret_trm (env : ivar -> domain_of_discourse) (t : trm L) {struct t} : domain_of_discourse :=
  match t with
  | Var_trm x => env x
  | Fun_trm f ts => function_interpret f (interpret_trms env ts)
  | Con_trm c => constant_interpret c
  end
with interpret_trms {n : nat} (env : ivar -> domain_of_discourse) (ts : trms L n) {struct ts} : Vector.t domain_of_discourse n :=
  match ts with
  | O_trms => []
  | S_trms n t ts => interpret_trm env t :: interpret_trms env ts 
  end.

Fixpoint interpret_frm (env : ivar -> domain_of_discourse) (p : frm L) {struct p} : Prop :=
  match p with
  | Eqn_frm t1 t2 => interpret_trm env t1 == interpret_trm env t2
  | Rel_frm R ts => relation_interpret R (interpret_trms env ts)
  | Neg_frm p1 => ~ interpret_frm env p1
  | Imp_frm p1 p2 => interpret_frm env p1 -> interpret_frm env p2
  | All_frm y p1 => forall y_value : domain_of_discourse, interpret_frm (upd_env y y_value env) p1
  end.

Lemma interpret_trm_unfold (env : ivar -> domain_of_discourse) (t : trm L) :
  interpret_trm env t =
  match t with
  | Var_trm x => env x
  | Fun_trm f ts => function_interpret f (interpret_trms env ts)
  | Con_trm c => constant_interpret c
  end.
Proof.
  destruct t; reflexivity.
Defined.

Lemma interpret_trms_unfold n (env : ivar -> domain_of_discourse) (ts : trms L n) :
  interpret_trms env ts =
  match ts with
  | O_trms => VNil
  | S_trms n' t ts' => VCons n' (interpret_trm env t) (interpret_trms env ts')
  end.
Proof.
  destruct ts; reflexivity.
Defined.

Lemma interpret_frm_unfold (env : ivar -> domain_of_discourse) (p : frm L) :
  interpret_frm env p =
  match p with
  | Eqn_frm t1 t2 => interpret_trm env t1 == interpret_trm env t2
  | Rel_frm R ts => relation_interpret R (interpret_trms env ts)
  | Neg_frm p1 => ~ interpret_frm env p1
  | Imp_frm p1 p2 => interpret_frm env p1 -> interpret_frm env p2
  | All_frm y p1 => forall y_value : domain_of_discourse, interpret_frm (upd_env y y_value env) p1
  end.
Proof.
  destruct p; reflexivity.
Defined.

Lemma interpret_trm_ext (env : ivar -> domain_of_discourse) (env' : ivar -> domain_of_discourse) (t : trm L)
  (EQUIV : forall z : ivar, forall FREE : is_free_in_trm z t = true, env z = env' z)
  : interpret_trm env t = interpret_trm env' t
with interpret_trms_ext n (env : ivar -> domain_of_discourse) (env' : ivar -> domain_of_discourse) (ts : trms L n)
  (EQUIV: forall z : ivar, forall FREE : is_free_in_trms z ts = true, env z = env' z)
  : interpret_trms env ts = interpret_trms env' ts.
Proof.
  - induction t as [x | f ts | c]; simpl.
    + eapply EQUIV. ss!.
    + f_equal. eapply interpret_trms_ext. ii. eapply EQUIV. ss!.
    + ss!.
  - induction ts as [ | n t ts IH]; simpl.
    + done.
    + erewrite interpret_trm_ext. erewrite IH. reflexivity.
      * ii. eapply EQUIV. ss!.
      * ii. eapply EQUIV. ss!.
Qed.

Lemma interpret_frm_ext (env : ivar -> domain_of_discourse) (env' : ivar -> domain_of_discourse) (p : frm L)
  (EQUIV : forall z : ivar, forall FREE : is_free_in_frm z p = true, env z = env' z)
  : interpret_frm env p <-> interpret_frm env' p.
Proof.
  revert env env' EQUIV. frm_ind p; simpl; i.
  - erewrite interpret_trms_ext. reflexivity. ii. eapply EQUIV. done.
  - rewrite interpret_trm_ext with (env := env) (env' := env'). rewrite interpret_trm_ext with (env := env) (env' := env'). reflexivity.
    + ii. eapply EQUIV. ss!.
    + ii. eapply EQUIV. ss!.
  - done.
  - rewrite IH1. rewrite IH2. reflexivity.
    + ii. eapply EQUIV. ss!.
    + ii. eapply EQUIV. ss!.
  - unfold upd_env. split; i.
    + rewrite IH1 with (env' := fun z : ivar => if eq_dec z y then y_value else env z). done.
      intros z FREE. destruct (eq_dec z y) as [z_eq_y | z_ne_y]. done.
      symmetry. eapply EQUIV. ss!.
    + rewrite IH1 with (env' := fun z : ivar => if eq_dec z y then y_value else env' z). done.
      intros z FREE. destruct (eq_dec z y) as [z_eq_y | z_ne_y]. ss!.
      eapply EQUIV. done!.
Qed.

Theorem substitution_lemma_trm (env : ivar -> domain_of_discourse) (s : subst L) (t : trm L)
  : interpret_trm (interpret_trm env ∘ s) t = interpret_trm env (subst_trm s t)
with substitution_lemma_trms n (env : ivar -> domain_of_discourse) (s : subst L) (ts : trms L n)
  : interpret_trms (interpret_trm env ∘ s) ts = interpret_trms env (subst_trms s ts).
Proof.
  - unfold "∘" in *. revert env s. induction t as [x | f ts | c]; i.
    + done.
    + rewrite interpret_trm_unfold. rewrite substitution_lemma_trms. done.
    + done.
  - unfold "∘" in *. revert env s. induction ts as [ | n t ts IH]; i.
    + done.
    + rewrite interpret_trms_unfold. rewrite IH. rewrite substitution_lemma_trm. done.
Qed.

Theorem substitution_lemma_frm (env : ivar -> domain_of_discourse) (s : subst L) (p : frm L)
  : interpret_frm (interpret_trm env ∘ s) p <-> interpret_frm env (subst_frm s p).
Proof.
  revert env s. frm_ind p; simpl; i.
  - f_equal. rewrite substitution_lemma_trms. done.
  - f_equal. do 2 rewrite substitution_lemma_trm. done.
  - done!.
  - rewrite IH1, IH2. done.
  - unfold "∘" in *.
    enough (ENOUGH : forall v : domain_of_discourse, interpret_frm (fun z : ivar => if eq_dec z y then v else interpret_trm env (s z)) p1 <-> interpret_frm (fun z : ivar => if eq_dec z (chi_frm s (All_frm y p1)) then v else env z) (subst_frm (cons_subst y (Var_trm (chi_frm s (All_frm y p1))) s) p1)) by ss!. i.
    assert (claim1 : forall z : ivar, is_free_in_frm z p1 = true -> interpret_trm (fun x : ivar => if eq_dec x (chi_frm s (All_frm y p1)) then v else env x) (cons_subst y (Var_trm (chi_frm s (All_frm y p1))) s z) = (if eq_dec z y then v else interpret_trm env (s z))).
    { intros z FREE. unfold cons_subst. destruct (eq_dec z y) as [z_eq_y | z_ne_y].
      - transitivity ((fun x : ivar => if eq_dec x (chi_frm s (All_frm y p1)) then v else env x) (chi_frm s (All_frm y p1))); try reflexivity.
        destruct (eq_dec (chi_frm s (All_frm y p1)) (chi_frm s (All_frm y p1))); done.
      - eapply interpret_trm_ext. intros z' FREE'. destruct (eq_dec z' (chi_frm s (All_frm y p1))) as [EQ | NE]; try done. subst z'.
        enough (CONTRA: is_free_in_trm (chi_frm s (All_frm y p1)) (s z) = false) by done.
        assert (BUT := chi_frm_is_fresh_in_subst (All_frm y p1) s).
        unfold frm_is_fresh_in_subst in BUT. rewrite forallb_forall in BUT.
        specialize BUT with (x := z). rewrite fvs_frm_unfold in BUT. rewrite L.in_remove_iff in BUT.
        rewrite fv_is_free_in_frm in BUT. specialize (BUT (conj FREE z_ne_y)).
        unfold "∘" in BUT. rewrite negb_true_iff in BUT. done.
    }
    symmetry. transitivity (interpret_frm (fun z : ivar => interpret_trm (fun w : ivar => if eq_dec w (chi_frm s (All_frm y p1)) then v else env w) (cons_subst y (Var_trm (chi_frm s (All_frm y p1))) s z)) p1). done. 
    symmetry. eapply interpret_frm_ext. ii. destruct (eq_dec z y) as [? | ?].
    + subst z. ss!. destruct (eq_dec y y) as [? | ?]. ss!. destruct (eq_dec (chi_frm s (All_frm y p1)) (chi_frm s (All_frm y p1))) as [? | ?]; ss!. ss!.
    + apply claim1 in FREE. destruct (eq_dec z y) as [? | ?]; ss!.
Qed.

Lemma interpret_trm_ext_upto (env : ivar -> domain_of_discourse) (env' : ivar -> domain_of_discourse) (t : trm L)
  (EQUIV : forall z : ivar, forall FREE : is_free_in_trm z t = true, env z == env' z)
  : interpret_trm env t == interpret_trm env' t
with interpret_trms_ext_upto n (env : ivar -> domain_of_discourse) (env' : ivar -> domain_of_discourse) (ts : trms L n)
  (EQUIV : forall z : ivar, forall FREE : is_free_in_trms z ts = true, env z == env' z)
  : interpret_trms env ts == interpret_trms env' ts.
Proof.
  - revert env env' EQUIV. induction t as [x | f ts | c]; simpl; i.
    + eapply EQUIV. rewrite is_free_in_trm_unfold. rewrite Nat.eqb_eq. done.
    + eapply function_interpret_preserves_eqProp. eapply interpret_trms_ext_upto.
      ii. eapply EQUIV. done.
    + reflexivity.
  - revert env env' EQUIV. simpl. induction ts as [ | n t ts IH].
    + intros env env' EQUIV. Fin.case0.
    + intros env env' EQUIV. Fin.caseS i.
      * simpl. eapply interpret_trm_ext_upto.
        ii. eapply EQUIV. rewrite is_free_in_trms_unfold. rewrite orb_true_iff. done.
      * simpl. eapply IH. ii. eapply EQUIV. rewrite is_free_in_trms_unfold. rewrite orb_true_iff. done.
Qed.

Lemma interpret_frm_ext_upto (env : ivar -> domain_of_discourse) (env' : ivar -> domain_of_discourse) (p : frm L)
  (EQUIV : forall z : ivar, forall FREE : is_free_in_frm z p = true, env z == env' z)
  : interpret_frm env p <-> interpret_frm env' p.
Proof.
  revert env env' EQUIV. frm_ind p; simpl; i.
  - eapply relation_interpret_preserves_eqProp. eapply interpret_trms_ext_upto. ii. now eapply EQUIV.
  - split; intros EQ.
    + rewrite interpret_trm_ext_upto. symmetry. rewrite interpret_trm_ext_upto. symmetry. exact EQ.
      * ii. symmetry. eapply EQUIV. rewrite orb_true_iff. done.
      * ii. symmetry. eapply EQUIV. rewrite orb_true_iff. done.
    + rewrite interpret_trm_ext_upto. symmetry. rewrite interpret_trm_ext_upto. symmetry. exact EQ.
      * ii. eapply EQUIV. rewrite orb_true_iff. done.
      * ii. eapply EQUIV. rewrite orb_true_iff. done.
  - done.
  - rewrite IH1. rewrite IH2. reflexivity.
    + ii. eapply EQUIV. rewrite orb_true_iff. done.
    + ii. eapply EQUIV. rewrite orb_true_iff. done.
  - unfold upd_env in *. split; intros H y_value.
    + rewrite IH1. exact (H y_value). simpl. ii.
      destruct (eq_dec z y) as [z_eq_y | z_ne_y].
      * done.
      * symmetry. eapply EQUIV. rewrite andb_true_iff. rewrite negb_true_iff. rewrite Nat.eqb_neq. done.
    + rewrite IH1. exact (H y_value). simpl. ii.
      destruct (eq_dec z y) as [z_eq_y | z_ne_y].
      * done.
      * eapply EQUIV. rewrite andb_true_iff. rewrite negb_true_iff. rewrite Nat.eqb_neq. done.
Qed.

Lemma not_free_no_effect_on_interpret_trm (env : ivar -> domain_of_discourse) (t : trm L) (y : ivar) (y_value : domain_of_discourse)
  (NOT_FREE : is_free_in_trm y t = false)
  : interpret_trm env t == interpret_trm (upd_env y y_value env) t
with not_free_no_effect_on_interpret_trms n (env : ivar -> domain_of_discourse) (ts: trms L n) (y: ivar) (y_value: domain_of_discourse)
  (NOT_FREE : is_free_in_trms y ts = false)
  : interpret_trms env ts == interpret_trms (upd_env y y_value env) ts.
Proof.
  - unfold upd_env. revert env y y_value NOT_FREE. induction t as [x | f ts | c]; simpl; i.
    + destruct (eq_dec x y) as [EQ | NE].
      * subst y. rewrite is_free_in_trm_unfold in NOT_FREE. rewrite Nat.eqb_neq in NOT_FREE. done.
      * reflexivity.
    + eapply function_interpret_preserves_eqProp. eapply not_free_no_effect_on_interpret_trms. done.
    + done.
  - unfold upd_env. revert env y y_value NOT_FREE. induction ts as [ | n t ts IH]; intros ? ? ? ?; [Fin.case0 | Fin.caseS i].
    * symmetry. rewrite interpret_trms_unfold. symmetry. simpl. eapply not_free_no_effect_on_interpret_trm. rewrite is_free_in_trms_unfold in NOT_FREE. rewrite orb_false_iff in NOT_FREE. done.
    * revert i. eapply IH. rewrite is_free_in_trms_unfold in NOT_FREE. rewrite orb_false_iff in NOT_FREE. done.
Qed.

Lemma not_free_no_effect_on_interpret_frm (env : ivar -> domain_of_discourse) (p : frm L) (y : ivar) (y_value : domain_of_discourse)
  (NOT_FREE : is_free_in_frm y p = false)
  : interpret_frm env p <-> interpret_frm (upd_env y y_value env) p.
Proof.
  unfold upd_env. revert env y y_value NOT_FREE. frm_ind p; simpl; i.
  - eapply relation_interpret_preserves_eqProp. eapply interpret_trms_ext_upto.
    ii. destruct (eq_dec z y) as [EQ | NE]. subst z. done. done.
  - enough (ENOUGH : interpret_trm env t1 == interpret_trm (fun z : ivar => if eq_dec z y then y_value else env z) t1 /\ interpret_trm env t2 == interpret_trm (fun z : ivar => if eq_dec z y then y_value else env z) t2).
    { destruct ENOUGH as [ENOUGH1 ENOUGH2]; rewrite ENOUGH1, ENOUGH2; done. }
    rewrite orb_false_iff in NOT_FREE. destruct NOT_FREE as [NOT_FREE1 NOT_FREE2]. split.
    + eapply interpret_trm_ext_upto. ii. destruct (eq_dec z y) as [EQ | NE]. subst z. done. done.
    + eapply interpret_trm_ext_upto. ii. destruct (eq_dec z y) as [EQ | NE]. subst z. done. done.
  - done.
  - rewrite orb_false_iff in NOT_FREE. rewrite IH1. rewrite IH2. reflexivity. done. done.
  - unfold upd_env in *. rename y0 into x, y_value into x_value. rewrite andb_false_iff in NOT_FREE. rewrite negb_false_iff in NOT_FREE. rewrite Nat.eqb_eq in NOT_FREE. destruct NOT_FREE as [NOT_FREE | x_eq_y].
    + specialize (IH1 env x x_value NOT_FREE). split; intros INTERPRET y_value.
      * rewrite interpret_frm_ext_upto. eapply INTERPRET. ii. simpl. destruct (eq_dec z y) as [EQ | NE].
        { reflexivity. }
        { destruct (eq_dec z x) as [z_eq_x | z_ne_x]; done. }
      * rewrite interpret_frm_ext_upto. eapply INTERPRET. ii. simpl. destruct (eq_dec z y) as [EQ | NE].
        { reflexivity. }
        { destruct (eq_dec z x) as [z_eq_x | z_ne_x]; done. }
    + subst y. split; intros INTERPRET y_value.
      * rewrite interpret_frm_ext_upto. eapply INTERPRET. simpl. ii. destruct (eq_dec z x) as [z_eq_x | z_ne_x].
        { reflexivity. }
        { destruct (eq_dec z x) as [EQ | NE]; done. }
      * rewrite interpret_frm_ext_upto. eapply INTERPRET. simpl. ii. destruct (eq_dec z x) as [z_eq_x | z_ne_x].
        { reflexivity. }
        { destruct (eq_dec z x) as [EQ | NE]; done. }
Qed.

Lemma rotate_witness (x : ivar) (y : ivar) (c : domain_of_discourse) (env : ivar -> domain_of_discourse) (p : frm L)
  (NOT_FREE : is_not_free_in_frm y p \/ y = x)
  : interpret_frm (upd_env x c env) p <-> interpret_frm (upd_env y c env) (subst_frm (one_subst x (Var_trm y)) p).
Proof.
  destruct NOT_FREE as [NOT_FREE | ->].
  - split.
    + intros INTERPRET. rewrite <- substitution_lemma_frm. eapply interpret_frm_ext_upto. 2: exact INTERPRET.
      ii. simpl. unfold one_subst, cons_subst, nil_subst, "∘", upd_env. destruct (eq_dec z x) as [z_eq_x | z_ne_x].
      * subst z. rewrite interpret_trm_unfold. destruct (eq_dec y y); try done.
      * rewrite interpret_trm_unfold. destruct (eq_dec z y) as [EQ | NE]; try done.
    + intros INTERPRET. rewrite <- substitution_lemma_frm in INTERPRET. eapply interpret_frm_ext_upto. 2: exact INTERPRET.
      ii. unfold one_subst, cons_subst, nil_subst, "∘", upd_env in *. destruct (eq_dec z x) as [z_eq_x | z_ne_x].
      * subst z. rewrite interpret_trm_unfold. destruct (eq_dec y y); try done.
      * rewrite interpret_trm_unfold. destruct (eq_dec z y) as [EQ | NE]; try done.
  - rewrite -> trivial_subst. rewrite <- substitution_lemma_frm. unfold nil_subst. split.
    + intros INTERPRET. eapply interpret_frm_ext_upto. 2: exact INTERPRET. simpl. ii. ss!.
    + intros INTERPRET. eapply interpret_frm_ext_upto. 2: exact INTERPRET. simpl. ii. done.
Qed.

Theorem alpha_equiv_compat_interpret_frm (p : frm L) (p' : frm L) (env : ivar -> domain_of_discourse)
  (ALPHA : p ≡ p')
  : interpret_frm env p <-> interpret_frm env p'.
Proof.
  revert env. induction ALPHA; simpl; i.
  - subst ts'. done.
  - subst t1' t2'. done.
  - done.
  - done.
  - split.
    { intros INTERPRET y_value. erewrite rotate_witness with (y := z).
      2:{ simpl in RFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in RFRESH. done. }
      rewrite <- IHALPHA. erewrite <- rotate_witness.
      + eapply INTERPRET.
      + simpl in LFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in LFRESH. done.
    }
    { intros INTERPRET y_value. erewrite rotate_witness with (y := z).
      2:{ simpl in LFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in LFRESH. done. }
      rewrite -> IHALPHA. erewrite <- rotate_witness.
      + eapply INTERPRET.
      + simpl in RFRESH. rewrite andb_false_iff, negb_false_iff, Nat.eqb_eq in RFRESH. done.
    }
Qed.

End FOL_SEMANTICS.

Definition satisfies_frm {L : language} (STRUCTURE : isStructureOf L) (env : ivar -> domain_of_discourse) (p : frm L) : Prop :=
  interpret_frm STRUCTURE env p.

Definition satisfies_frms {L : language} (STRUCTURE : isStructureOf L) (env : ivar -> domain_of_discourse) (ps : ensemble (frm L)) : Prop :=
  forall p : frm L, forall H_IN : p \in ps, satisfies_frm STRUCTURE env p.

Definition entails {L : language} (Gamma : ensemble (frm L)) (C : frm L) : Prop :=
  forall STRUCTURE : isStructureOf L, forall env : ivar -> domain_of_discourse, forall SATISFY : satisfies_frms STRUCTURE env Gamma, satisfies_frm STRUCTURE env C.

Module FolNotations.

Infix "≡" := alpha_equiv : type_scope.
Infix "⊨" := entails : type_scope.

End FolNotations.

Import FolNotations.

#[global]
Add Parametric Morphism {L : language}
  : (@entails L) with signature (eqProp ==> alpha_equiv ==> iff)
  as entails_compatWith_eqProp.
Proof.
  intros Gamma Gamma' EQ C C' ALPHA. transitivity (Gamma ⊨ C').
  - now split; ii; eapply alpha_equiv_compat_interpret_frm; try (eapply H; exact SATISFY).
  - split; ii; eapply H; done!.
Qed.

Lemma extend_entails {L : language} (Gamma : ensemble (@frm L)) (Gamma' : ensemble (@frm L)) (C : frm L)
  (ENTAILS : Gamma ⊨ C)
  (SUBSET : Gamma \subseteq Gamma')
  : Gamma' ⊨ C.
Proof.
  ii. eapply ENTAILS; done!.
Qed.
