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

Abbreviation finite_map K := (FiniteMap.t K (isSorted compare)).

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

Definition lookup (k : K) (m : finite_map K V) : option V :=
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

Theorem finite_map_eq_spec (m : finite_map K V) (m' : finite_map K V)
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

Theorem lookup_spec (m : finite_map K V) (k : K) (v : V)
  : lookup k m = Some v <-> (k, v) ∈ m.(FiniteMap.data).
Proof.
  exact (lookup'_spec m.(FiniteMap.data) m.(FiniteMap.data_isSorted) k v).
Qed.

Definition empty : finite_map K V :=
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

Definition insert (k : K) (v : V) (m : finite_map K V) : finite_map K V :=
  FiniteMap.mk (insert' k v m.(FiniteMap.data)) (isSorted_insert' k v m.(FiniteMap.data) m.(FiniteMap.data_isSorted)).

Theorem lookup_insert_eq (k : K) (v : V) (m : finite_map K V)
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

Theorem lookup_insert_ne (k : K) (v : V) (m : finite_map K V) (k0 : K)
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

Definition remove (k : K) (m : finite_map K V) : finite_map K V :=
  FiniteMap.mk (remove' k m.(FiniteMap.data)) (isSorted_remove' k m.(FiniteMap.data) m.(FiniteMap.data_isSorted)).

Theorem lookup_remove_eq (k : K) (m : finite_map K V)
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

Theorem lookup_remove_ne (k : K) (m : finite_map K V) (k0 : K)
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

Definition keys (m : finite_map K V) : fset K :=
  FSet.mk (map fst m.(FiniteMap.data)) m.(FiniteMap.data_isSorted).

Theorem in_keys_iff (m : finite_map K V) (k : K)
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

Definition Similarity_finite_map_partial_map {K : Type} {V : Type} {POSET_K : isPoset K} {HsOrd_K : HsOrd K (POSET := POSET_K)} {K' : Type} {V' : Type} (Similarity_K_K' : Similarity K K') (Similarity_V_V' : Similarity V V') : Similarity (finite_map K V) (K' -> option V') :=
  fun m : finite_map K V => fun m' : K' -> option V' => forall k : K, forall k' : K', k =~= k' -> lookup k m =~= m' k'.

Context {K : Type} {V : Type} {POSET_K : isPoset K} {HsOrd_K : HsOrd K (POSET := POSET_K)}.

#[global]
Instance finite_map_corresponds_to_partial_map : Similarity (finite_map K V) (K -> option V) :=
  Similarity_finite_map_partial_map eq eq.

Theorem finite_map_corresponds_to_partial_map_iff (m : finite_map K V) (m' : K -> option V)
  : m =~= m' <-> (forall x : K, lookup x m = m' x).
Proof.
  split.
  - intros H_sim. do 4 red in H_sim. intros x. pose proof (H_sim x x eq_refl) as H. destruct H; f_equal; auto.
  - intros H_eq. do 4 red. intros x x' x_eq_x'. change (x = x') in x_eq_x'. subst x'.
    pose proof (H_eq x) as H. revert H. generalize (lookup x m) as o. generalize (m' x) as o'. clear.
    intros [x' | ] [x | ] H; try congruence; econs; red; congruence.
Qed.

End SIMILARITY.

Section HsOrd_finite_map.

#[local] Obligation Tactic := idtac.

Context {K : Type} {V : Type} {POSET_K : isPoset K} {HsOrd_K : HsOrd K (POSET := POSET_K)} {POSET_V : isPoset V} {HsOrd_V : HsOrd V (POSET := POSET_V)}.

#[local, program]
Instance finite_map_isProset : isProset (finite_map K V) :=
  { leProp (m : finite_map K V) (m' : finite_map K V) := m.(FiniteMap.data) =< m'.(FiniteMap.data)
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
Instance finite_map_isPoset : isPoset (finite_map K V) :=
  { Poset_isProset := finite_map_isProset
  ; Poset_eqProp_spec (m : finite_map K V) (m' : finite_map K V) := conj (fun H : m = m' => H) (fun H : m = m' => H)
  }.

#[local, program]
Instance finite_map_hsOrd : hsOrd (finite_map K V) (PROSET := Poset_isProset) :=
  { compare (m : finite_map K V) (m' : finite_map K V) := compare m.(FiniteMap.data) m'.(FiniteMap.data) }.
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
Instance HsOrd_finite_map : HsOrd (finite_map K V) (POSET := finite_map_isPoset) :=
  { HsOrd_hsOrd := finite_map_hsOrd }.

End HsOrd_finite_map.

#[global, refine]
Instance finite_map_isFunctor {K : Type} {POSET_K : isPoset K} (HsOrd_K : HsOrd K (POSET := POSET_K)) : isFunctor (finite_map K) :=
  fun V : Type => fun V' : Type => fun v_to_v' : V -> V' => fun m : finite_map K V => {| FiniteMap.data := map (fun '(k, v) => (k, v_to_v' v)) m.(FiniteMap.data); FiniteMap.data_isSorted := _ |}.
Proof.
  replace (map fst (map (fun '(k, v) => (k, v_to_v' v)) m.(FiniteMap.data))) with (map fst m.(FiniteMap.data)).
  - exact m.(FiniteMap.data_isSorted).
  - generalize (FiniteMap.data m) as xs; clear. induction xs as [ | [k v] xs IH]; simpl; f_equal; auto.
Defined.
