Require Import PnV.Prelude.Prelude.
Require Import PnV.Prelude.ConstructiveFacts.
Require Import PnV.Prelude.X.
Require Export PnV.Math.ThN.
Require Export PnV.Math.OrderTheory.
Require Export PnV.Data.HsOrd.
Require Import PnV.Data.FiniteSet.

#[local] Infix "=~=" := is_similar_to : type_scope.
#[local] Infix "\in" := E.In.
#[local] Infix "∈" := L.In.

#[local] Hint Resolve S_lt_S_intro : core.

Module FiniteMap.

#[universes(template), projections(primitive)]
Record t {K : Type} {isSorted : list K -> bool} {V : Type} : Type :=
  mk
  { data : list (K * V)
  ; data_isSorted : isSorted (map fst data) = true
  }.

#[global] Arguments t : clear implicits.
#[global] Arguments mk {K} {isSorted} {V}.

Lemma t_eq_iff {K : Type} {V : Type} {isSorted : list K -> bool} (m : FiniteMap.t K isSorted V) (m' : FiniteMap.t K isSorted V)
  : m = m' <-> m.(data) = m'.(data).
Proof.
  split.
  - intros H_eq. subst m'. reflexivity.
  - revert m m'.
    assert (claim : forall data1 : list (K * V), forall data2 : list (K * V), forall data1_isSorted : isSorted (map fst data1) = true, forall data2_isSorted : isSorted (map fst data2) = true, data1 = data2 -> {| data := data1; data_isSorted := data1_isSorted |} = {| data := data2; data_isSorted := data2_isSorted |}).
    { ii. subst data2. enough (HH : data1_isSorted = data2_isSorted) by now rewrite HH. eapply eq_pirrel_fromEqDec. }
    intros X X' H_eq. exact (claim X.(data) X'.(data) X.(data_isSorted) X'.(data_isSorted) H_eq).
Qed.

End FiniteMap.

Abbreviation fpmap K := (FiniteMap.t K (isSorted compare)).

Section BASICS.

Context {K : Type} {V : Type} {POSET_K : isPoset K} {HsOrd_K : HsOrd K (POSET := POSET_K)}.

Definition lookup' (k0 : K) : list (K * V) -> option V :=
  fix go (kvs : list (K * V)) {struct kvs} : option V :=
  match kvs with
  | [] => None
  | (k, v) :: kvs =>
    match compare k0 k with
    | Lt => None
    | Eq => Some v
    | Gt => go kvs
    end
  end.

Definition lookup (k : K) (m : fpmap K V) : option V :=
  lookup' k m.(FiniteMap.data).

Lemma lookup'_nil (k0 : K)
  : lookup' k0 [] = None.
Proof.
  reflexivity.
Qed.

Lemma lookup'_cons (k0 : K) (k : K) (v : V) (kvs : list (K * V)) :
  lookup' k0 ((k, v) :: kvs) =
  match compare k0 k with
  | Lt => None
  | Eq => Some v
  | Gt => lookup' k0 kvs
  end.
Proof.
  reflexivity.
Qed.

Lemma lookup'_lt_None (k0 : K) (kvs : list (K * V))
  (LT : forall q : K * V, q ∈ kvs -> compare k0 (fst q) = Lt)
  : lookup' k0 kvs = None.
Proof.
  destruct kvs as [ | [k1 v1] kvs]; trivial.
  pose proof (LT (k1, v1) (or_introl eq_refl)) as LT1. simpl in LT1.
  rewrite lookup'_cons, LT1. reflexivity.
Qed.

Lemma isSorted_map_fst_cons_iff (p : K * V) (ps : list (K * V))
  : isSorted compare (map fst (p :: ps)) = true <-> ((forall q : K * V, q ∈ ps -> compare (fst p) (fst q) = Lt) /\ isSorted compare (map fst ps) = true).
Proof.
  cbn [map]. rewrite isSorted_cons_iff. split.
  - intros [SORTED_hd SORTED_tl]. split; trivial.
    intros q q_in. eapply SORTED_hd. eapply L.in_map. exact q_in.
  - intros [SORTED_hd SORTED_tl]. split; trivial.
    intros z z_in. rewrite L.in_map_iff in z_in.
    destruct z_in as (q & fst_q_eq_z & q_in). subst z. exact (SORTED_hd q q_in).
Qed.

Theorem fpmap_eq_spec (m : fpmap K V) (m' : fpmap K V)
  : m = m' <-> (forall k, lookup k m = lookup k m').
Proof.
  rewrite FiniteMap.t_eq_iff. unfold lookup. split.
  - intros H_eq k. rewrite H_eq. reflexivity.
  - intros EXT.
    pose proof (fun p : K * V => fun ps : list (K * V) => proj1 (isSorted_map_fst_cons_iff p ps)) as HD_TL.
    pose proof lookup'_lt_None as LT_None.
    pose proof (m.(FiniteMap.data_isSorted)) as kvs_isSorted.
    pose proof (m'.(FiniteMap.data_isSorted)) as kvs'_isSorted.
    set (kvs := m.(FiniteMap.data)) in *. set (kvs' := m'.(FiniteMap.data)) in *.
    clearbody kvs kvs'. clear m m'. revert kvs_isSorted kvs' kvs'_isSorted EXT.
    induction kvs as [ | [k v] kvs IH]; intros kvs_isSorted [ | [k' v'] kvs'] kvs'_isSorted EXT.
    + reflexivity.
    + pose proof (EXT k') as H. cbn [lookup'] in H. rewrite compare_refl in H. discriminate H.
    + pose proof (EXT k) as H. cbn [lookup'] in H. rewrite compare_refl in H. discriminate H.
    + pose proof (HD_TL (k, v) kvs kvs_isSorted) as [k_lt_kvs kvs_isSorted'].
      pose proof (HD_TL (k', v') kvs' kvs'_isSorted) as [k'_lt_kvs' kvs'_isSorted'].
      simpl in k_lt_kvs, k'_lt_kvs'.
      assert (k_eq_k' : k = k').
      { destruct (compare k k') as [ | | ] eqn: H_OBS.
        - exact (proj1 (compare_eq_iff k k') H_OBS).
        - exfalso. pose proof (EXT k) as H. cbn [lookup'] in H.
          rewrite compare_refl, H_OBS in H. discriminate H.
        - exfalso. pose proof (EXT k') as H. cbn [lookup'] in H.
          rewrite compare_refl, (compare_Gt_flip k k' H_OBS) in H. discriminate H.
      }
      subst k'.
      assert (v_eq_v' : v = v').
      { pose proof (EXT k) as H. cbn [lookup'] in H. rewrite compare_refl in H. now inversion H. }
      subst v'. f_equal. eapply IH; trivial. intros k0.
      destruct (compare k0 k) as [ | | ] eqn: H_OBS.
      * rewrite compare_eq_iff in H_OBS. subst k0.
        rewrite (LT_None k kvs k_lt_kvs), (LT_None k kvs' k'_lt_kvs'). reflexivity.
      * assert (H1 : lookup' k0 kvs = None).
        { eapply LT_None. intros q q_in. exact (compare_Lt_trans k0 k (fst q) H_OBS (k_lt_kvs q q_in)). }
        assert (H2 : lookup' k0 kvs' = None).
        { eapply LT_None. intros q q_in. exact (compare_Lt_trans k0 k (fst q) H_OBS (k'_lt_kvs' q q_in)). }
        rewrite H1, H2. reflexivity.
      * pose proof (EXT k0) as H. cbn [lookup'] in H. rewrite H_OBS in H. exact H.
Qed.

Lemma lookup'_spec (kvs : list (K * V))
  (kvs_isSorted : isSorted compare (map fst kvs) = true)
  : forall k : K, forall v : V, lookup' k kvs = Some v <-> (k, v) ∈ kvs.
Proof.
  revert kvs_isSorted. induction kvs as [ | [k1 v1] kvs IH]; intros kvs_isSorted k v.
  - rewrite lookup'_nil. simpl. split; [intros H_eq; discriminate H_eq | tauto].
  - rewrite isSorted_map_fst_cons_iff in kvs_isSorted.
    destruct kvs_isSorted as [k1_lt_kvs kvs_isSorted]. simpl in k1_lt_kvs.
    pose proof (IH kvs_isSorted k v) as IH'. rewrite lookup'_cons. simpl.
    destruct (compare k k1) as [ | | ] eqn: H_OBS.
    + rewrite compare_eq_iff in H_OBS. subst k1. split.
      * intros H_eq. left. congruence.
      * intros [H_eq | H_in]; [congruence | ].
        exfalso. pose proof (k1_lt_kvs (k, v) H_in) as LT. simpl in LT.
        rewrite compare_refl in LT. discriminate LT.
    + split; [intros H_eq; discriminate H_eq | ]. intros [H_eq | H_in].
      * exfalso. inversion H_eq; subst k1 v1. rewrite compare_refl in H_OBS. discriminate H_OBS.
      * exfalso. pose proof (k1_lt_kvs (k, v) H_in) as LT. simpl in LT.
        pose proof (compare_Lt_trans k k1 k H_OBS LT) as LT'.
        rewrite compare_refl in LT'. discriminate LT'.
    + rewrite IH'. split; [intros H_in; right; exact H_in | ].
      intros [H_eq | H_in]; trivial.
      exfalso. inversion H_eq; subst k1 v1. rewrite compare_refl in H_OBS. discriminate H_OBS.
Qed.

Theorem lookup_spec (m : fpmap K V) (k : K) (v : V)
  : lookup k m = Some v <-> (k, v) ∈ m.(FiniteMap.data).
Proof.
  exact (lookup'_spec m.(FiniteMap.data) m.(FiniteMap.data_isSorted) k v).
Qed.

Definition empty : fpmap K V :=
  FiniteMap.mk [] eq_refl.

Theorem lookup_empty (k : K)
  : lookup k empty = None.
Proof.
  reflexivity.
Qed.

Definition insert' (k0 : K) (v0 : V) : list (K * V) -> list (K * V) :=
  fix go (kvs : list (K * V)) {struct kvs} : list (K * V) :=
  match kvs with
  | [] => [(k0, v0)]
  | (k, v) :: kvs =>
    match compare k0 k with
    | Lt => (k0, v0) :: (k, v) :: kvs
    | Eq => (k0, v0) :: kvs
    | Gt => (k, v) :: go kvs
    end
  end.

Lemma insert'_nil (k0 : K) (v0 : V)
  : insert' k0 v0 [] = [(k0, v0)].
Proof.
  reflexivity.
Qed.

Lemma insert'_cons (k0 : K) (v0 : V) (k : K) (v : V) (kvs : list (K * V)) :
  insert' k0 v0 ((k, v) :: kvs) =
  match compare k0 k with
  | Lt => (k0, v0) :: (k, v) :: kvs
  | Eq => (k0, v0) :: kvs
  | Gt => (k, v) :: insert' k0 v0 kvs
  end.
Proof.
  reflexivity.
Qed.

Lemma map_fst_insert' (k0 : K) (v0 : V) (kvs : list (K * V))
  : map fst (insert' k0 v0 kvs) = FS.insert k0 (map fst kvs).
Proof.
  induction kvs as [ | [k v] kvs IH]; trivial.
  rewrite insert'_cons.
  change (FS.insert k0 (map fst ((k, v) :: kvs)))
    with (match compare k0 k with Lt => k0 :: k :: map fst kvs | Eq => k :: map fst kvs | Gt => k :: FS.insert k0 (map fst kvs) end).
  destruct (compare k0 k) as [ | | ] eqn: H_OBS.
  - cbn [map fst]. f_equal. exact (proj1 (compare_eq_iff k0 k) H_OBS).
  - reflexivity.
  - cbn [map fst]. f_equal. exact IH.
Qed.

Lemma isSorted_insert' (k0 : K) (v0 : V) (kvs : list (K * V))
  (kvs_isSorted : isSorted compare (map fst kvs) = true)
  : isSorted compare (map fst (insert' k0 v0 kvs)) = true.
Proof.
  rewrite map_fst_insert'. exact (FS.isSorted_insert k0 (map fst kvs) kvs_isSorted).
Qed.

Definition insert (k : K) (v : V) (m : fpmap K V) : fpmap K V :=
  FiniteMap.mk (insert' k v m.(FiniteMap.data)) (isSorted_insert' k v m.(FiniteMap.data) m.(FiniteMap.data_isSorted)).

Theorem lookup_insert_eq (k : K) (v : V) (m : fpmap K V)
  : lookup k (insert k v m) = Some v.
Proof.
  unfold lookup, insert. cbn [FiniteMap.data].
  generalize m.(FiniteMap.data) as kvs. clear m.
  induction kvs as [ | [k1 v1] kvs IH].
  - rewrite insert'_nil, lookup'_cons, compare_refl. reflexivity.
  - rewrite insert'_cons. destruct (compare k k1) as [ | | ] eqn: H_OBS.
    + rewrite lookup'_cons, compare_refl. reflexivity.
    + rewrite lookup'_cons, compare_refl. reflexivity.
    + rewrite lookup'_cons, H_OBS. exact IH.
Qed.

Theorem lookup_insert_ne (k : K) (v : V) (m : fpmap K V) (k0 : K)
  (NE : k0 ≠ k)
  : lookup k0 (insert k v m) = lookup k0 m.
Proof.
  unfold lookup, insert. cbn [FiniteMap.data].
  generalize m.(FiniteMap.data) as kvs. clear m.
  induction kvs as [ | [k1 v1] kvs IH].
  - rewrite insert'_nil, !lookup'_cons, lookup'_nil.
    destruct (compare k0 k) as [ | | ] eqn: H_OBS; trivial.
    exfalso. rewrite compare_eq_iff in H_OBS. contradiction.
  - rewrite insert'_cons. destruct (compare k k1) as [ | | ] eqn: H_OBS1.
    + rewrite compare_eq_iff in H_OBS1. subst k1. rewrite !lookup'_cons.
      destruct (compare k0 k) as [ | | ] eqn: H_OBS2; trivial.
      exfalso. rewrite compare_eq_iff in H_OBS2. contradiction.
    + rewrite lookup'_cons. destruct (compare k0 k) as [ | | ] eqn: H_OBS2.
      * exfalso. rewrite compare_eq_iff in H_OBS2. contradiction.
      * rewrite lookup'_cons, (compare_Lt_trans k0 k k1 H_OBS2 H_OBS1). reflexivity.
      * reflexivity.
    + rewrite !lookup'_cons. destruct (compare k0 k1) as [ | | ]; trivial.
Qed.

Definition remove' (k0 : K) : list (K * V) -> list (K * V) :=
  fix go (kvs : list (K * V)) {struct kvs} : list (K * V) :=
  match kvs with
  | [] => []
  | (k, v) :: kvs =>
    match compare k0 k with
    | Lt => (k, v) :: kvs
    | Eq => kvs
    | Gt => (k, v) :: go kvs
    end
  end.

Lemma remove'_nil (k0 : K)
  : remove' k0 [] = [].
Proof.
  reflexivity.
Qed.

Lemma remove'_cons (k0 : K) (k : K) (v : V) (kvs : list (K * V)) :
  remove' k0 ((k, v) :: kvs) =
  match compare k0 k with
  | Lt => (k, v) :: kvs
  | Eq => kvs
  | Gt => (k, v) :: remove' k0 kvs
  end.
Proof.
  reflexivity.
Qed.

Lemma in_remove'_incl (k0 : K) (kvs : list (K * V))
  : forall q : K * V, q ∈ remove' k0 kvs -> q ∈ kvs.
Proof.
  induction kvs as [ | [k v] kvs IH]; trivial.
  intros q. rewrite remove'_cons. destruct (compare k0 k) as [ | | ].
  - intros H_in. right. exact H_in.
  - intros H_in. exact H_in.
  - intros [H_eq | H_in]; [left; exact H_eq | right; exact (IH q H_in)].
Qed.

Lemma isSorted_remove' (k0 : K) (kvs : list (K * V))
  (kvs_isSorted : isSorted compare (map fst kvs) = true)
  : isSorted compare (map fst (remove' k0 kvs)) = true.
Proof.
  revert kvs_isSorted. induction kvs as [ | [k v] kvs IH]; intros kvs_isSorted; trivial.
  pose proof (proj1 (isSorted_map_fst_cons_iff (k, v) kvs) kvs_isSorted) as [k_lt_kvs kvs_isSorted'].
  simpl in k_lt_kvs. rewrite remove'_cons. destruct (compare k0 k) as [ | | ].
  - exact kvs_isSorted'.
  - exact kvs_isSorted.
  - rewrite isSorted_map_fst_cons_iff. simpl. split; [ | exact (IH kvs_isSorted')].
    intros q q_in. exact (k_lt_kvs q (in_remove'_incl k0 kvs q q_in)).
Qed.

Definition remove (k : K) (m : fpmap K V) : fpmap K V :=
  FiniteMap.mk (remove' k m.(FiniteMap.data)) (isSorted_remove' k m.(FiniteMap.data) m.(FiniteMap.data_isSorted)).

Theorem lookup_remove_eq (k : K) (m : fpmap K V)
  : lookup k (remove k m) = None.
Proof.
  unfold lookup, remove. cbn [FiniteMap.data].
  pose proof (m.(FiniteMap.data_isSorted)) as kvs_isSorted.
  generalize dependent m.(FiniteMap.data). intros kvs. clear m.
  induction kvs as [ | [k1 v1] kvs IH]; intros kvs_isSorted; trivial.
  pose proof (proj1 (isSorted_map_fst_cons_iff (k1, v1) kvs) kvs_isSorted) as [k1_lt_kvs kvs_isSorted'].
  simpl in k1_lt_kvs. rewrite remove'_cons. destruct (compare k k1) as [ | | ] eqn: H_OBS.
  - eapply lookup'_lt_None. intros q q_in.
    rewrite compare_eq_iff in H_OBS. subst k1. exact (k1_lt_kvs q q_in).
  - rewrite lookup'_cons, H_OBS. reflexivity.
  - rewrite lookup'_cons, H_OBS. exact (IH kvs_isSorted').
Qed.

Theorem lookup_remove_ne (k : K) (m : fpmap K V) (k0 : K)
  (NE : k0 ≠ k)
  : lookup k0 (remove k m) = lookup k0 m.
Proof.
  unfold lookup, remove. cbn [FiniteMap.data].
  pose proof (m.(FiniteMap.data_isSorted)) as kvs_isSorted.
  generalize dependent m.(FiniteMap.data). intros kvs. clear m.
  induction kvs as [ | [k1 v1] kvs IH]; intros kvs_isSorted; trivial.
  pose proof (proj1 (isSorted_map_fst_cons_iff (k1, v1) kvs) kvs_isSorted) as [k1_lt_kvs kvs_isSorted'].
  simpl in k1_lt_kvs. rewrite remove'_cons. destruct (compare k k1) as [ | | ] eqn: H_OBS1.
  - rewrite compare_eq_iff in H_OBS1. subst k1.
    rewrite lookup'_cons. destruct (compare k0 k) as [ | | ] eqn: H_OBS2.
    + exfalso. rewrite compare_eq_iff in H_OBS2. contradiction.
    + eapply lookup'_lt_None. intros q q_in.
      exact (compare_Lt_trans k0 k (fst q) H_OBS2 (k1_lt_kvs q q_in)).
    + reflexivity.
  - reflexivity.
  - rewrite !lookup'_cons. destruct (compare k0 k1) as [ | | ]; trivial.
    exact (IH kvs_isSorted').
Qed.

Definition keys (m : fpmap K V) : fset K :=
  FSet.mk (map fst m.(FiniteMap.data)) m.(FiniteMap.data_isSorted).

Theorem in_keys_iff (m : fpmap K V) (k : K)
  : k ∈ (keys m).(FSet.data) <-> (exists v : V, lookup k m = Some v).
Proof.
  cbv [keys]; simpl. rewrite L.in_map_iff. split.
  - intros ([k1 v1] & fst_eq & p_in). simpl in fst_eq. subst k1.
    exists v1. rewrite lookup_spec. exact p_in.
  - intros [v H_eq]. rewrite lookup_spec in H_eq. exists (k, v). split; auto.
Qed.

End BASICS.

Section SIMILARITY.

#[local] Existing Instance Similarity_option_option.

Definition Similarity_fpmap_partial_map {K : Type} {V : Type} {POSET_K : isPoset K} {HsOrd_K : HsOrd K (POSET := POSET_K)} {K' : Type} {V' : Type} (Similarity_K_K' : Similarity K K') (Similarity_V_V' : Similarity V V') : Similarity (fpmap K V) (K' -> option V') :=
  fun m : fpmap K V => fun m' : K' -> option V' => forall k : K, forall k' : K', k =~= k' -> lookup k m =~= m' k'.

Context {K : Type} {V : Type} {POSET_K : isPoset K} {HsOrd_K : HsOrd K (POSET := POSET_K)}.

#[global]
Instance fpmap_corresponds_to_partial_map : Similarity (fpmap K V) (K -> option V) :=
  Similarity_fpmap_partial_map eq eq.

Theorem fpmap_corresponds_to_partial_map_iff (m : fpmap K V) (m' : K -> option V)
  : m =~= m' <-> (forall x : K, lookup x m = m' x).
Proof.
  split.
  - intros H_sim. do 4 red in H_sim. intros x. pose proof (H_sim x x eq_refl) as H. destruct H; f_equal; auto.
  - intros H_eq. do 4 red. intros x x' x_eq_x'. change (x = x') in x_eq_x'. subst x'.
    pose proof (H_eq x) as H. revert H. generalize (lookup x m) as o. generalize (m' x) as o'. clear.
    intros [x' | ] [x | ] H; try congruence; econs; red; congruence.
Qed.

End SIMILARITY.

Section HsOrd_fpmap.

#[local] Obligation Tactic := idtac.

Context {K : Type} {V : Type} {POSET_K : isPoset K} {HsOrd_K : HsOrd K (POSET := POSET_K)} {POSET_V : isPoset V} {HsOrd_V : HsOrd V (POSET := POSET_V)}.

#[local, program]
Instance fpmap_isProset : isProset (fpmap K V) :=
  { leProp (m : fpmap K V) (m' : fpmap K V) := m.(FiniteMap.data) =< m'.(FiniteMap.data)
  ; Proset_isSetoid := mkSetoid_from_eq
  }.
Next Obligation.
  split.
  - intros m. reflexivity.
  - intros m m' m'' m_le_m' m'_le_m''. now transitivity m'.(FiniteMap.data).
Qed.
Next Obligation.
  intros m m'. unfold flip. split.
  - intros m_eq_m'. change (m = m') in m_eq_m'. subst m'. split; reflexivity.
  - intros [m_le_m' m'_le_m]. change (m = m'). rewrite FiniteMap.t_eq_iff. rewrite <- Poset_eqProp_spec.
    exact (leProp_antisymmetry m.(FiniteMap.data) m'.(FiniteMap.data) m_le_m' m'_le_m).
Qed.

#[global]
Instance fpmap_isPoset : isPoset (fpmap K V) :=
  { Poset_isProset := fpmap_isProset
  ; Poset_eqProp_spec (m : fpmap K V) (m' : fpmap K V) := conj (fun H : m = m' => H) (fun H : m = m' => H)
  }.

#[local, program]
Instance fpmap_hsOrd : hsOrd (fpmap K V) (PROSET := Poset_isProset) :=
  { compare (m : fpmap K V) (m' : fpmap K V) := compare m.(FiniteMap.data) m'.(FiniteMap.data) }.
Next Obligation.
  intros m m' OBS_Lt. pose proof (compare_Lt m.(FiniteMap.data) m'.(FiniteMap.data) OBS_Lt) as [LE NE]. split.
  - exact LE.
  - intros m_eq_m'. contradiction NE. do 6 red in m_eq_m' |- *.
    rewrite -> FiniteMap.t_eq_iff in m_eq_m'. rewrite m_eq_m'. reflexivity.
Qed.
Next Obligation.
  intros m m' OBS_Eq. pose proof (compare_Eq m.(FiniteMap.data) m'.(FiniteMap.data) OBS_Eq) as H_eq.
  rewrite Poset_eqProp_spec in H_eq. exact (proj2 (FiniteMap.t_eq_iff m m') H_eq).
Qed.
Next Obligation.
  intros m m' OBS_Gt. pose proof (compare_Gt m.(FiniteMap.data) m'.(FiniteMap.data) OBS_Gt) as [LE NE]. split.
  - exact LE.
  - intros m_eq_m'. contradiction NE. do 6 red in m_eq_m' |- *.
    rewrite -> FiniteMap.t_eq_iff in m_eq_m'. rewrite m_eq_m'. reflexivity.
Qed.

#[global]
Instance HsOrd_fpmap : HsOrd (fpmap K V) (POSET := fpmap_isPoset) :=
  { HsOrd_hsOrd := fpmap_hsOrd }.

End HsOrd_fpmap.

#[global, refine]
Instance fpmap_isFunctor {K : Type} {POSET_K : isPoset K} (HsOrd_K : HsOrd K (POSET := POSET_K)) : isFunctor (fpmap K) :=
  fun V : Type => fun V' : Type => fun v_to_v' : V -> V' => fun m : fpmap K V => {| FiniteMap.data := map (fun '(k, v) => (k, v_to_v' v)) m.(FiniteMap.data); FiniteMap.data_isSorted := _ |}.
Proof.
  replace (map fst (map (fun '(k, v) => (k, v_to_v' v)) m.(FiniteMap.data))) with (map fst m.(FiniteMap.data)).
  - exact m.(FiniteMap.data_isSorted).
  - generalize (FiniteMap.data m) as xs; clear. induction xs as [ | [k v] xs IH]; simpl; f_equal; auto.
Defined.

Lemma lookup_tabulated_in {Key : Type} {POSET_K : isPoset Key} {HsOrd_K : HsOrd Key} {V : Type} (f : Key -> V) (l : list Key) (c : Key)
  (IN : L.In c l)
  : lookup c (L.fold_right (fun x => fun m => insert x (f x) m) empty l) = Some (f c).
Proof.
  induction l as [ | c1 l IH]; [contradiction IN | ]. cbn [L.fold_right].
  destruct (eqb c c1) as [ | ] eqn: E.
  - rewrite eqb_eq in E. subst c1. eapply lookup_insert_eq.
  - rewrite eqb_neq in E. rewrite (lookup_insert_ne c1 (f c1) _ c E).
    eapply IH. destruct IN as [EQ | IN]; [exfalso; exact (E (eq_sym EQ)) | exact IN].
Qed.

Lemma lookup_tabulated_inv {Key : Type} {POSET_K : isPoset Key} {HsOrd_K : HsOrd Key} {V : Type} (f : Key -> V) (l : list Key) (c : Key) (v : V)
  (LOOK : lookup c (L.fold_right (fun x => fun m => insert x (f x) m) empty l) = Some v)
  : L.In c l /\ v = f c.
Proof.
  induction l as [ | c1 l IH]; cbn [L.fold_right] in LOOK.
  - rewrite lookup_empty in LOOK. discriminate LOOK.
  - destruct (eqb c c1) as [ | ] eqn: E.
    + rewrite eqb_eq in E. subst c1. rewrite lookup_insert_eq in LOOK.
      injection LOOK as EQV. split; [now left | symmetry; exact EQV].
    + rewrite eqb_neq in E. rewrite (lookup_insert_ne c1 (f c1) _ c E) in LOOK.
      pose proof (IH LOOK) as [IN EQ]. split; [now right | exact EQ].
Qed.

Lemma lookup_fold_right_insert_iff
  {Key : Type} {POSET_K : isPoset Key} {HsOrd_K : HsOrd Key}
  {V : Type} (es : list (Key * V))
  (FUN : forall (k : Key) (v v' : V),
    L.In (k, v) es -> L.In (k, v') es -> v = v')
  (k : Key) (v : V)
  : lookup k
      (L.fold_right
        (fun e => fun m => insert (fst e) (snd e) m) empty es) = Some v
    <-> L.In (k, v) es.
Proof.
  revert FUN. induction es as [|[k0 v0] es IH]; intro FUN.
  - cbn [L.fold_right]. rewrite lookup_empty. split.
    + intro BAD. discriminate BAD.
    + intro BAD. contradiction BAD.
  - cbn [L.fold_right fst snd]. destruct (eqb k k0) eqn:E.
    + rewrite eqb_eq in E. subst k0. rewrite lookup_insert_eq. split.
      * intro EQ. injection EQ as EQV. subst v. now left.
      * intro IN. assert (v = v0) as EQV.
        { eapply FUN; [exact IN | now left]. }
        subst v. reflexivity.
    + rewrite eqb_neq in E.
      rewrite (lookup_insert_ne k0 v0 _ k E).
      assert (FUN_T : forall (k1 : Key) (v1 v2 : V),
        L.In (k1, v1) es -> L.In (k1, v2) es -> v1 = v2).
      { intros k1 v1 v2 IN1 IN2.
        exact (FUN k1 v1 v2 (or_intror IN1) (or_intror IN2)). }
      rewrite (IH FUN_T). split.
      * intro IN. now right.
      * intros [EQ | IN].
        -- injection EQ as EQK EQV. exfalso. apply E. symmetry. exact EQK.
        -- exact IN.
Qed.

Section TABULATE.

Context {K : Type} {K_isPoset : isPoset K}
  {HsOrd_K : HsOrd K (POSET := K_isPoset)}.
Context {V : Type}.

Lemma map_fst_pairs (f : K -> V) (l : list K)
  : L.map fst (L.map (fun k : K => (k, f k)) l) = l.
Proof.
  induction l as [ | k l IH]; [reflexivity | ].
  cbn [L.map fst]. f_equal. exact IH.
Qed.

Lemma isSorted_pairs (f : K -> V) (l : list K)
  (H : isSorted compare l = true)
  : isSorted compare
      (L.map fst (L.map (fun k : K => (k, f k)) l)) = true.
Proof.
  rewrite (map_fst_pairs f l). exact H.
Qed.

Definition tabulate (ks : fset K) (f : K -> V) : fpmap K V :=
  FiniteMap.mk (L.map (fun k : K => (k, f k)) ks.(FSet.data))
    (isSorted_pairs f ks.(FSet.data) ks.(FSet.data_isSorted)).

Lemma lookup_tabulate_in (ks : fset K) (f : K -> V) (k : K)
  (IN : L.In k ks.(FSet.data))
  : lookup k (tabulate ks f) = Some (f k).
Proof.
  eapply lookup_spec. cbn [tabulate FiniteMap.data].
  rewrite L.in_map_iff. exists k. split; [reflexivity | exact IN].
Qed.

Lemma lookup_tabulate_inv (ks : fset K) (f : K -> V) (k : K) (v : V)
  (LOOK : lookup k (tabulate ks f) = Some v)
  : L.In k ks.(FSet.data) /\ v = f k.
Proof.
  rewrite lookup_spec in LOOK. cbn [tabulate FiniteMap.data] in LOOK.
  rewrite L.in_map_iff in LOOK. destruct LOOK as (k' & EQ & k'_in).
  inversion EQ; subst k'. split; [exact k'_in | reflexivity].
Qed.

Fixpoint pairsOpt (f : K -> option V) (l : list K) {struct l}
  : list (K * V) :=
  match l with
  | [] => []
  | k :: l' =>
    match f k with
    | Some v => (k, v) :: pairsOpt f l'
    | None => pairsOpt f l'
    end
  end.

Lemma in_pairsOpt_incl (f : K -> option V) (l : list K) (k : K)
  (IN : L.In k (L.map fst (pairsOpt f l)))
  : L.In k l.
Proof.
  revert IN. induction l as [ | k0 l IH]; intros IN;
    [contradiction IN | ].
  cbn [pairsOpt] in IN. destruct (f k0) as [v | ].
  - cbn [L.map fst] in IN. destruct IN as [EQ | IN];
      [now left | right; exact (IH IN)].
  - right. exact (IH IN).
Qed.

Lemma isSorted_pairsOpt (f : K -> option V) (l : list K)
  (H : isSorted compare l = true)
  : isSorted compare (L.map fst (pairsOpt f l)) = true.
Proof.
  revert H. induction l as [ | k l IH]; intros H;
    [reflexivity | ].
  pose proof (proj1 (isSorted_cons_iff k l) H) as
    [k_lt_l l_sorted].
  cbn [pairsOpt]. destruct (f k) as [v | ];
    [ | exact (IH l_sorted)].
  cbn [L.map fst].
  eapply (proj2
    (isSorted_cons_iff k (L.map fst (pairsOpt f l)))). split.
  - intros z z_in. exact (k_lt_l z (in_pairsOpt_incl f l z z_in)).
  - exact (IH l_sorted).
Qed.

Definition tabulateOpt (ks : fset K) (f : K -> option V)
  : fpmap K V :=
  FiniteMap.mk (pairsOpt f ks.(FSet.data))
    (isSorted_pairsOpt f ks.(FSet.data) ks.(FSet.data_isSorted)).

Lemma in_pairsOpt_iff (f : K -> option V) (l : list K) (k : K) (v : V)
  : L.In (k, v) (pairsOpt f l) <->
    (L.In k l /\ f k = Some v).
Proof.
  induction l as [ | k0 l IH]; cbn [pairsOpt].
  - split; [intros [] | intros [[] _]].
  - destruct (f k0) as [v0 | ] eqn: FK0.
    + cbn [L.In]. rewrite IH. split.
      * intros [EQ | [IN FK]].
        { inversion EQ; subst k0 v0. split; [now left | exact FK0]. }
        { split; [now right | exact FK]. }
      * intros [[EQ | IN] FK].
        { subst k0. left. rewrite FK0 in FK. inversion FK. reflexivity. }
        { right. split; assumption. }
    + rewrite IH. split.
      * intros [IN FK]. split; [now right | exact FK].
      * intros [[EQ | IN] FK];
          [subst k0; congruence | split; assumption].
Qed.

Lemma lookup_tabulateOpt (ks : fset K) (f : K -> option V)
  (k : K) (v : V)
  : lookup k (tabulateOpt ks f) = Some v <->
    (L.In k ks.(FSet.data) /\ f k = Some v).
Proof.
  rewrite lookup_spec. cbn [tabulateOpt FiniteMap.data].
  exact (in_pairsOpt_iff f ks.(FSet.data) k v).
Qed.

Lemma map_fst_filter_incl (p : K * V -> bool) (l : list (K * V)) (k : K)
  (IN : L.In k (L.map fst (L.filter p l)))
  : L.In k (L.map fst l).
Proof.
  revert IN. induction l as [ | q l IH]; intros IN;
    [contradiction IN | ].
  cbn [L.filter] in IN. cbn [L.map].
  destruct (p q) as [ | ].
  - cbn [L.map] in IN. destruct IN as [EQ | IN];
      [now left | right; exact (IH IN)].
  - right. exact (IH IN).
Qed.

Lemma isSorted_filterPairs (p : K * V -> bool) (l : list (K * V))
  (H : isSorted compare (L.map fst l) = true)
  : isSorted compare (L.map fst (L.filter p l)) = true.
Proof.
  revert H. induction l as [ | q l IH]; intros H;
    [reflexivity | ].
  cbn [L.map] in H.
  pose proof (proj1 (isSorted_cons_iff (fst q) (L.map fst l)) H) as
    [q_lt_l l_sorted].
  cbn [L.filter]. destruct (p q) as [ | ];
    [ | exact (IH l_sorted)].
  cbn [L.map].
  eapply (proj2
    (isSorted_cons_iff (fst q) (L.map fst (L.filter p l)))). split.
  - intros z z_in.
    exact (q_lt_l z (map_fst_filter_incl p l z z_in)).
  - exact (IH l_sorted).
Qed.

Definition filterMap (p : K * V -> bool) (m : fpmap K V)
  : fpmap K V :=
  FiniteMap.mk (L.filter p m.(FiniteMap.data))
    (isSorted_filterPairs p m.(FiniteMap.data)
      m.(FiniteMap.data_isSorted)).

Lemma lookup_filterMap (p : K * V -> bool) (m : fpmap K V)
  (k : K) (v : V)
  : lookup k (filterMap p m) = Some v <->
    (lookup k m = Some v /\ p (k, v) = true).
Proof.
  rewrite !lookup_spec. cbn [filterMap FiniteMap.data].
  exact (L.filter_In p (k, v) m.(FiniteMap.data)).
Qed.

Lemma map_fst_mapVal {W : Type} (f : V -> W) (l : list (K * V))
  : L.map fst
      (L.map (fun p : K * V => (fst p, f (snd p))) l) =
    L.map fst l.
Proof.
  induction l as [ | p l IH]; [reflexivity | ].
  cbn [L.map fst]. f_equal. exact IH.
Qed.

Lemma isSorted_mapVal {W : Type} (f : V -> W) (l : list (K * V))
  (H : isSorted compare (L.map fst l) = true)
  : isSorted compare
      (L.map fst (L.map (fun p : K * V => (fst p, f (snd p))) l)) = true.
Proof.
  rewrite (map_fst_mapVal f l). exact H.
Qed.

Definition mapVal {W : Type} (f : V -> W) (m : fpmap K V)
  : fpmap K W :=
  FiniteMap.mk
    (L.map (fun p : K * V => (fst p, f (snd p))) m.(FiniteMap.data))
    (isSorted_mapVal f m.(FiniteMap.data) m.(FiniteMap.data_isSorted)).

End TABULATE.

Section ROWS.

Context {A : Type} {A_isPoset : isPoset A}
  {HsOrd_A : HsOrd A (POSET := A_isPoset)}.
Context {B : Type} {B_isPoset : isPoset B}
  {HsOrd_B : HsOrd B (POSET := B_isPoset)}.
Context {V : Type}.

Fixpoint rowList (q : A) (l : list ((A * B) * V)) {struct l}
  : list (B * V) :=
  match l with
  | [] => []
  | kv :: l' =>
    if eqb (fst (fst kv)) q then
      (snd (fst kv), snd kv) :: rowList q l'
    else
      rowList q l'
  end.

Lemma in_rowList (q : A) (l : list ((A * B) * V)) (z : B)
  (IN : L.In z (L.map fst (rowList q l)))
  : exists kv : (A * B) * V,
    L.In kv l /\ fst (fst kv) = q /\ snd (fst kv) = z.
Proof.
  revert IN. induction l as [ | kv l IH]; intros IN;
    [contradiction IN | ].
  cbn [rowList] in IN.
  destruct (eqb (fst (fst kv)) q) as [ | ] eqn: EQB.
  - cbn [L.map fst] in IN. destruct IN as [EQ | IN].
    + exists kv. rewrite eqb_eq in EQB.
      split; [now left | split; [exact EQB | exact EQ]].
    + pose proof (IH IN) as (kv' & IN' & FST' & SND').
      exists kv'. split; [now right | split; assumption].
  - pose proof (IH IN) as (kv' & IN' & FST' & SND').
    exists kv'. split; [now right | split; assumption].
Qed.

Lemma isSorted_rowList (q : A) (l : list ((A * B) * V))
  (H : isSorted compare (L.map fst l) = true)
  : isSorted compare (L.map fst (rowList q l)) = true.
Proof.
  revert H. induction l as [ | kv l IH]; intros H;
    [reflexivity | ].
  cbn [L.map] in H.
  pose proof (proj1 (isSorted_cons_iff (fst kv) (L.map fst l)) H) as
    [hd_lt tl_sorted].
  cbn [rowList].
  destruct (eqb (fst (fst kv)) q) as [ | ] eqn: EQB;
    [ | exact (IH tl_sorted)].
  cbn [L.map fst].
  eapply (proj2
    (isSorted_cons_iff (snd (fst kv)) (L.map fst (rowList q l)))).
  split.
  - intros z z_in.
    pose proof (in_rowList q l z z_in) as (kv' & IN' & FST' & SND').
    pose proof (hd_lt (fst kv') (L.in_map fst l kv' IN')) as LT.
    rewrite eqb_eq in EQB.
    change (compare (fst kv) (fst kv')) with
      (pair_compare (fst kv) (fst kv')) in LT.
    unfold pair_compare in LT. rewrite EQB, FST', compare_refl in LT.
    rewrite <- SND'. exact LT.
  - exact (IH tl_sorted).
Qed.

Fixpoint colList (b : B) (l : list ((A * B) * V)) {struct l}
  : list A :=
  match l with
  | [] => []
  | kv :: l' =>
    if eqb (snd (fst kv)) b then
      fst (fst kv) :: colList b l'
    else
      colList b l'
  end.

Lemma in_colList (b : B) (l : list ((A * B) * V)) (z : A)
  (IN : L.In z (colList b l))
  : exists kv : (A * B) * V,
    L.In kv l /\ snd (fst kv) = b /\ fst (fst kv) = z.
Proof.
  revert IN. induction l as [ | kv l IH]; intros IN;
    [contradiction IN | ].
  cbn [colList] in IN.
  destruct (eqb (snd (fst kv)) b) as [ | ] eqn: EQB.
  - cbn [L.In] in IN. destruct IN as [EQ | IN].
    + exists kv. rewrite eqb_eq in EQB.
      split; [now left | split; [exact EQB | exact EQ]].
    + pose proof (IH IN) as (kv' & IN' & SND' & FST').
      exists kv'. split; [now right | split; assumption].
  - pose proof (IH IN) as (kv' & IN' & SND' & FST').
    exists kv'. split; [now right | split; assumption].
Qed.

Lemma isSorted_colList (b : B) (l : list ((A * B) * V))
  (H : isSorted compare (L.map fst l) = true)
  : isSorted compare (colList b l) = true.
Proof.
  revert H. induction l as [ | kv l IH]; intros H;
    [reflexivity | ].
  cbn [L.map] in H.
  pose proof (proj1 (isSorted_cons_iff (fst kv) (L.map fst l)) H) as
    [hd_lt tl_sorted].
  cbn [colList].
  destruct (eqb (snd (fst kv)) b) as [ | ] eqn: EQB;
    [ | exact (IH tl_sorted)].
  eapply (proj2
    (isSorted_cons_iff (fst (fst kv)) (colList b l))). split.
  - intros z z_in.
    pose proof (in_colList b l z z_in) as (kv' & IN' & SND' & FST').
    pose proof (hd_lt (fst kv') (L.in_map fst l kv' IN')) as LT.
    rewrite eqb_eq in EQB.
    change (compare (fst kv) (fst kv')) with
      (pair_compare (fst kv) (fst kv')) in LT.
    unfold pair_compare in LT. rewrite <- FST'.
    destruct (compare (fst (fst kv)) (fst (fst kv'))) as [ | | ] eqn: OBS;
      trivial.
    exfalso. rewrite EQB, SND', compare_refl in LT. discriminate LT.
  - exact (IH tl_sorted).
Qed.

Definition col (b : B) (m : fpmap (A * B) V) : fset A :=
  FSet.mk (colList b m.(FiniteMap.data))
    (isSorted_colList b m.(FiniteMap.data) m.(FiniteMap.data_isSorted)).

Lemma in_col_iff (b : B) (m : fpmap (A * B) V) (z : A)
  : L.In z (col b m).(FSet.data) <->
    exists v : V, lookup (z, b) m = Some v.
Proof.
  split.
  - intros IN. cbn [col FSet.data] in IN.
    pose proof (in_colList b m.(FiniteMap.data) z IN) as
      (kv & KV_IN & SND & FST).
    destruct kv as [[x y] v]. cbn [fst snd] in *. subst x y.
    exists v. exact (proj2 (lookup_spec m (z, b) v) KV_IN).
  - intros (v & LOOK). rewrite lookup_spec in LOOK.
    cbn [col FSet.data].
    assert (BACK : forall l : list ((A * B) * V),
      L.In ((z, b), v) l -> L.In z (colList b l)).
    { intros l IN. induction l as [ | kv l IH]; cbn [colList];
        [contradiction IN | ].
      destruct IN as [EQ | IN].
      - subst kv. cbn [fst snd].
        destruct (eqb b b) eqn: E.
        + exact (or_introl eq_refl).
        + rewrite eqb_neq in E. contradiction E. reflexivity.
      - destruct (eqb (snd (fst kv)) b); [right | ]; exact (IH IN).
    }
    exact (BACK m.(FiniteMap.data) LOOK).
Qed.

Definition row (q : A) (m : fpmap (A * B) V) : fpmap B V :=
  FiniteMap.mk (rowList q m.(FiniteMap.data))
    (isSorted_rowList q m.(FiniteMap.data) m.(FiniteMap.data_isSorted)).

Lemma lookup_row (q : A) (m : fpmap (A * B) V) (b : B) (v : V)
  : lookup b (row q m) = Some v <-> lookup (q, b) m = Some v.
Proof.
  rewrite !lookup_spec. cbn [row FiniteMap.data].
  generalize m.(FiniteMap.data) as l. clear m. intros l.
  induction l as [ | kv l IH]; cbn [rowList].
  - split; [intros [] | intros []].
  - destruct (eqb (fst (fst kv)) q) as [ | ] eqn: EQB.
    + rewrite eqb_eq in EQB. cbn [L.In]. rewrite IH. split.
      * intros [EQ | IN]; [ | now right]. left.
        destruct kv as [[q0 b0] v0]. cbn [fst snd] in *. subst q0.
        inversion EQ; subst b0 v0. reflexivity.
      * intros [EQ | IN]; [ | now right]. left.
        destruct kv as [[q0 b0] v0]. cbn [fst snd] in *. subst q0.
        inversion EQ; subst b0 v0. reflexivity.
    + rewrite IH. cbn [L.In]. split; [now right | ].
      intros [EQ | IN]; [ | exact IN]. exfalso.
      destruct kv as [[q0 b0] v0]. cbn [fst snd] in *.
      inversion EQ; subst q0 b0 v0. rewrite eqb_neq in EQB.
      contradiction EQB. reflexivity.
Qed.

End ROWS.
