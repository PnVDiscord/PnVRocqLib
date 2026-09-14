Require Import PnV.Prelude.X.
Require Import PnV.Data.HsOrd.
Require Import Stdlib.ZArith.BinInt.
Require Import Stdlib.ZArith.ZArith_dec.
Require Import Stdlib.ZArith.Znat.
Require Import Stdlib.NArith.BinNat.
Require Import Stdlib.NArith.Nnat.
Require Import Stdlib.PArith.Pnat.

Module BalancedTree.

#[universes(template)]
Inductive tree (A : Type) : Type :=
  | Leaf
  | Node (l : tree A) (x : A) (r : tree A) (h : Z).

#[global] Arguments Leaf {A}.
#[global] Arguments Node {A} l x r h.

Section METHODS.

Context {A : Type}.

Definition height (tr : tree A) : Z :=
  match tr with
  | Leaf => 0%Z
  | Node _ _ _ h => h
  end.

Fixpoint depth (tr : tree A) : nat :=
  match tr with
  | Leaf => O
  | Node l _ r _ => S (Nat.max (depth l) (depth r))
  end.

Fixpoint min_depth (tr : tree A) : nat :=
  match tr with
  | Leaf => O
  | Node l _ r _ => S (Nat.min (min_depth l) (min_depth r))
  end.

Fixpoint size (tr : tree A) : nat :=
  match tr with
  | Leaf => O
  | Node l _ r _ => S (size l + size r)
  end.

Fixpoint elements (tr : tree A) : list A :=
  match tr with
  | Leaf => []
  | Node l x r _ => elements l ++ x :: elements r
  end.

Fixpoint elements_acc (tr : tree A) (suffix : list A) : list A :=
  match tr with
  | Leaf => suffix
  | Node l x r _ => elements_acc l (x :: elements_acc r suffix)
  end.

Inductive balanced : tree A -> Prop :=
  | balanced_Leaf
    : balanced Leaf
  | balanced_Node (l : tree A) (x : A) (r : tree A) (h : Z)
    (LEFT : balanced l)
    (RIGHT : balanced r)
    (RANGE : (- 2 <= height l - height r <= 2)%Z)
    (CACHE : h = (Z.max (height l) (height r) + 1)%Z)
    : balanced (Node l x r h).

Definition create (l : tree A) (x : A) (r : tree A) : tree A :=
  Node l x r (Z.max (height l) (height r) + 1)%Z.

Definition bal (l : tree A) (x : A) (r : tree A) : tree A :=
  if (height r + 2 <? height l)%Z then
    match l with
    | Leaf => create l x r
    | Node ll lx lr _ =>
      if (height lr <=? height ll)%Z then
        create ll lx (create lr x r)
      else
        match lr with
        | Leaf => create l x r
        | Node lrl lrx lrr _ => create (create ll lx lrl) lrx (create lrr x r)
        end
    end
  else if (height l + 2 <? height r)%Z then
    match r with
    | Leaf => create l x r
    | Node rl rx rr _ =>
      if (height rl <=? height rr)%Z then
        create (create l x rl) rx rr
      else
        match rl with
        | Leaf => create l x r
        | Node rll rlx rlr _ => create (create l x rll) rlx (create rlr rx rr)
        end
    end
  else
    create l x r.

Fixpoint remove_min (l : tree A) (x : A) (r : tree A) {struct l} : tree A * A :=
  match l with
  | Leaf => (r, x)
  | Node ll lx lr _ =>
    let '(l', m) := remove_min ll lx lr in
    (bal l' x r, m)
  end.

Definition merge (l : tree A) (r : tree A) : tree A :=
  match l, r with
  | Leaf, _ => r
  | _, Leaf => l
  | _, Node rl rx rr _ =>
    let '(r', m) := remove_min rl rx rr in
    bal l m r'
  end.

Definition lookup_raw (cmp : A -> comparison) : tree A -> option A :=
  fix go (tr : tree A) {struct tr} : option A :=
  match tr with
  | Leaf => None
  | Node l x r _ =>
    match cmp x with
    | Eq => Some x
    | Lt => go l
    | Gt => go r
    end
  end.

Definition add_raw (cmp : A -> A -> comparison) (x : A) : tree A -> tree A :=
  fix go (tr : tree A) : tree A :=
  match tr with
  | Leaf => create Leaf x Leaf
  | Node l y r h =>
    match cmp x y with
    | Eq => Node l x r h
    | Lt => bal (go l) y r
    | Gt => bal l y (go r)
    end
  end.

Definition remove_raw (cmp : A -> comparison) : tree A -> tree A :=
  fix go (tr : tree A) : tree A :=
  match tr with
  | Leaf => Leaf
  | Node l x r _ =>
    match cmp x with
    | Eq => merge l r
    | Lt => bal (go l) x r
    | Gt => bal l x (go r)
    end
  end.

Lemma elements_leaf
  : elements Leaf = [].
Proof.
  reflexivity.
Defined.

Lemma elements_node (l : tree A) (x : A) (r : tree A) (h : Z)
  : elements (Node l x r h) = elements l ++ x :: elements r.
Proof.
  reflexivity.
Defined.

Lemma elements_acc_spec (tr : tree A) (suffix : list A)
  : elements_acc tr suffix = elements tr ++ suffix.
Proof.
  revert suffix. induction tr; simpl; i; auto.
  rewrite IHtr1, IHtr2, <- app_assoc. reflexivity.
Qed.

Lemma length_elements (tr : tree A)
  : length (elements tr) = size tr.
Proof.
  induction tr; simpl; auto. rewrite length_app. simpl. lia.
Qed.

Ltac split_balance :=
  repeat first
  [ progress cbn [height]
  | match goal with
    | |- context [(?x <? ?y)%Z] => let OBS := fresh "OBS" in destruct (Z.ltb x y) eqn: OBS
    | |- context [(?x <=? ?y)%Z] => let OBS := fresh "OBS" in destruct (Z.leb x y) eqn: OBS
    | |- context [match ?tr with Leaf => _ | Node _ _ _ _ => _ end] => destruct tr
    end
  ].

Lemma elements_create (l : tree A) (x : A) (r : tree A)
  : elements (create l x r) = elements l ++ x :: elements r.
Proof.
  reflexivity.
Qed.

Lemma elements_bal (l : tree A) (x : A) (r : tree A)
  : elements (bal l x r) = elements l ++ x :: elements r.
Proof.
  now unfold bal; des_ifs; simpl; repeat progress (rewrite <- ?app_assoc; simpl app).
Qed.

Lemma elements_remove_min (l : tree A) (x : A) (r : tree A) (tr : tree A) (m : A)
  (H_OBS : remove_min l x r = (tr, m))
  : elements l ++ x :: elements r = m :: elements tr.
Proof.
  revert_until l; induction l; simpl; i; des_ifs.
  obtain HH with Heq by IHl1.
  rewrite elements_bal, HH. reflexivity.
Qed.

Lemma elements_merge (l : tree A) (r : tree A)
  : elements (merge l r) = elements l ++ elements r.
Proof.
  destruct l as [ | ll lx lr lh], r as [ | rl rx rr rh]; simpl; rewrite ?app_nil_r; auto.
  des_ifs. find* HH by elements_remove_min. rewrite -> elements_bal, <- HH. reflexivity.
Qed.

Lemma balanced_leaf
  : balanced Leaf.
Proof.
  econs.
Qed.

Lemma balanced_node_iff (l : tree A) (x : A) (r : tree A) (h : Z)
  : balanced (Node l x r h) <-> (balanced l /\ balanced r /\ (- 2 <= height l - height r <= 2)%Z /\ h = (Z.max (height l) (height r) + 1)%Z).
Proof.
  split.
  - intros H. inv H. auto.
  - intros (LEFT & RIGHT & RANGE & CACHE). econs; eauto.
Qed.

Lemma balanced_height_nonnegative (tr : tree A)
  (BALANCED : balanced tr)
  : (0 <= height tr)%Z.
Proof.
  induction BALANCED; simpl height; des_ifs; lia.
Qed.

Lemma create_balanced (l : tree A) (x : A) (r : tree A)
  (LEFT : balanced l)
  (RIGHT : balanced r)
  (RANGE : (- 2 <= height l - height r <= 2)%Z)
  : balanced (create l x r).
Proof.
  econs; eauto.
Qed.

Ltac unpack_balanced :=
  repeat (
    match goal with
    | [ H : balanced (Node _ _ _ _) |- _ ] => rewrite balanced_node_iff in H; destruct H as (? & ? & ? & ?)
    | [ H : balanced Leaf |- _ ] => clear H
    end
  );
  repeat (
    match goal with
    | [ H : balanced ?tr |- _ ] =>
      let NONNEG := fresh "NONNEG" in
      pose proof (balanced_height_nonnegative tr H) as NONNEG;
      lazymatch goal with
      | [ |- _ ] => revert H
      end
    end
  ); i.

Ltac create_balances :=
  first
  [ assumption
  | eapply create_balanced;
    [ create_balances
    | create_balances
    | cbn [create height]; des_ifs; lia
    ]
  ].

Lemma bal_balanced_height (l : tree A) (x : A) (r : tree A)
  (LEFT : balanced l)
  (RIGHT : balanced r)
  (RANGE : (- 3 <= height l - height r <= 3)%Z)
  : balanced (bal l x r) /\ (0 <= height (bal l x r) - Z.max (height l) (height r) <= 1)%Z /\ ((- 2 <= height l - height r <= 2)%Z -> height (bal l x r) = (Z.max (height l) (height r) + 1)%Z).
Proof.
  unfold bal; split_balance; s!; unpack_balanced; cbn [height] in *; try lia.
  all: split; [create_balances | ].
  all: split; [cbn [create height]; des_ifs; lia | intros RANGE2; cbn [create height]; des_ifs; lia].
Qed.

Lemma bal_balanced (l : tree A) (x : A) (r : tree A)
  (LEFT : balanced l)
  (RIGHT : balanced r)
  (RANGE : (- 3 <= height l - height r <= 3)%Z)
  : balanced (bal l x r).
Proof.
  now obtain [? _] with LEFT RIGHT RANGE by bal_balanced_height.
Qed.

Lemma bal_height_bounds (l : tree A) (x : A) (r : tree A)
  (LEFT : balanced l)
  (RIGHT : balanced r)
  (RANGE : (- 3 <= height l - height r <= 3)%Z)
  : (0 <= height (bal l x r) - Z.max (height l) (height r) <= 1)%Z /\ ((- 2 <= height l - height r <= 2)%Z -> height (bal l x r) = (Z.max (height l) (height r) + 1)%Z).
Proof.
  now obtain [_ ?] with LEFT RIGHT RANGE by bal_balanced_height.
Qed.

Lemma grow_height (l : Z) (r : Z) (l' : Z) (r' : Z) (b : Z)
  (OLD : (-2 <= l - r <= 2)%Z)
  (LEFT : (0 <= l' - l <= 1)%Z)
  (RIGHT : (0 <= r' - r <= 1)%Z)
  (BOUND : (0 <= b - Z.max l' r' <= 1)%Z)
  (EXACT : (-2 <= l' - r' <= 2)%Z -> b = (Z.max l' r' + 1)%Z)
  : (0 <= b - (Z.max l r + 1) <= 1)%Z.
Proof.
  find* [HH1 | HH1] by (Z_le_dec (-2)%Z (l' - r')%Z); find* [HH2 | HH2] by (Z_le_dec (l' - r')%Z 2%Z); lia.
Qed.

Lemma shrink_height (l : Z) (r : Z) (l' : Z) (r' : Z) (b : Z)
  (OLD : (-2 <= l - r <= 2)%Z)
  (LEFT : (0 <= l - l' <= 1)%Z)
  (RIGHT : (0 <= r - r' <= 1)%Z)
  (BOUND : (0 <= b - Z.max l' r' <= 1)%Z)
  (EXACT : (-2 <= l' - r' <= 2)%Z -> b = (Z.max l' r' + 1)%Z)
  : (0 <= (Z.max l r + 1) - b <= 1)%Z.
Proof.
  find* [HH1 | HH1] by (Z_le_dec (-2)%Z (l' - r')%Z); find* [HH2 | HH2] by (Z_le_dec (l' - r')%Z 2%Z); lia.
Qed.

Lemma remove_min_balanced_height (l : tree A) (x : A) (r : tree A) (h : Z) (tr : tree A) (m : A)
  (BALANCED : balanced (Node l x r h))
  (H_OBS : remove_min l x r = (tr, m))
  : balanced tr /\ (0 <= h - height tr <= 1)%Z.
Proof.
  revert_until l; induction l as [ | ll IH_ll lx lr IH_lr lh]; simpl; i.
  - rewrite balanced_node_iff in BALANCED. des; simpl in *; clarify. split; auto.
    find* NONNEG by balanced_height_nonnegative. lia.
  - rewrite balanced_node_iff in BALANCED. find* (LEFT & RIGHT & RANGE & CACHE) by BALANCED.
    des_ifs. obtain [LEFT' DELTA] with LEFT by IH_ll. simpl height in *.
    find* (AVL & BOUND & EXACT) by (bal_balanced_height t x r); [lia | split; auto].
    eapply shrink_height with (l := lh) (r := height r); eauto; lia.
Qed.

Lemma merge_balanced_height (l : tree A) (r : tree A)
  (LEFT : balanced l)
  (RIGHT : balanced r)
  (RANGE : (- 2 <= height l - height r <= 2)%Z)
  : balanced (merge l r) /\ (0 <= height (merge l r) - Z.max (height l) (height r) <= 1)%Z.
Proof.
  destruct l as [ | ll lx lr lh].
  - simpl. obtain NONNEG with RIGHT by balanced_height_nonnegative.
    rewrite Z.max_r by exact NONNEG. split; auto; lia.
  - destruct r as [ | rl rx rr rh].
    + simpl. obtain NONNEG with LEFT by balanced_height_nonnegative. simpl height in NONNEG.
      rewrite Z.max_l by exact NONNEG. split; auto; lia.
    + simpl. destruct (remove_min rl rx rr) as [r' m] eqn: H_OBS.
      obtain [RIGHT' DELTA] with RIGHT by remove_min_balanced_height.
      simpl height in *.
      assert (RANGE' : (- 3 <= height (Node ll lx lr lh) - height r' <= 3)%Z) by ss!.
      obtain (AVL & BOUND & EXACT) with LEFT RIGHT' RANGE' by (bal_balanced_height (Node ll lx lr lh) m r').
      split; auto.
      assert (SHRINK : (0 <= Z.max lh rh + 1 - height (bal (Node ll lx lr lh) m r') <= 1)%Z).
      { eapply shrink_height with (l := lh) (r := rh); eauto; simpl height in *; lia. }
      simpl height in *; lia.
Qed.

Lemma add_raw_balanced_height (cmp : A -> A -> comparison) (x : A) (tr : tree A)
  (BALANCED : balanced tr)
  : balanced (add_raw cmp x tr) /\ (0 <= height (add_raw cmp x tr) - height tr <= 1)%Z.
Proof.
  revert BALANCED; induction tr as [ | l IH_l y r IH_r h]; simpl; i.
  - split; [eapply create_balanced; eauto using balanced_leaf | ]; simpl; lia.
  - rewrite balanced_node_iff in BALANCED. find* (LEFT & RIGHT & RANGE & CACHE) by BALANCED.
    destruct (cmp x y).
    + split; [rewrite balanced_node_iff; auto | simpl; lia].
    + obtain [LEFT' DELTA] with LEFT by IH_l.
      obtain (AVL & BOUND & EXACT) with LEFT' RIGHT by (bal_balanced_height (add_raw cmp x l) y r).
      split; auto. rewrite CACHE.
      eapply grow_height with (l := height l) (r := height r); eauto; lia.
    + obtain [RIGHT' DELTA] with RIGHT by IH_r.
      obtain (AVL & BOUND & EXACT) with LEFT RIGHT' by (bal_balanced_height l y (add_raw cmp x r)).
      split; auto. rewrite CACHE.
      eapply grow_height with (l := height l) (r := height r); eauto; lia.
Qed.

Lemma remove_raw_balanced_height (cmp : A -> comparison) (tr : tree A)
  (BALANCED : balanced tr)
  : balanced (remove_raw cmp tr) /\ (0 <= height tr - height (remove_raw cmp tr) <= 1)%Z.
Proof.
  revert BALANCED; induction tr as [ | l IH_l x r IH_r h]; simpl; i.
  - split; auto; lia.
  - rewrite balanced_node_iff in BALANCED. find* (LEFT & RIGHT & RANGE & CACHE) by BALANCED.
    destruct (cmp x).
    + obtain [AVL BOUND] with LEFT RIGHT RANGE by merge_balanced_height. split; auto; lia.
    + obtain [LEFT' DELTA] with LEFT by IH_l.
      obtain (AVL & BOUND & EXACT) with LEFT' RIGHT by (bal_balanced_height (remove_raw cmp l) x r).
      split; auto. rewrite CACHE.
      eapply shrink_height with (l := height l) (r := height r); eauto; lia.
    + obtain [RIGHT' DELTA] with RIGHT by IH_r.
      obtain (AVL & BOUND & EXACT) with LEFT RIGHT' by (bal_balanced_height l x (remove_raw cmp r)).
      split; auto. rewrite CACHE.
      eapply shrink_height with (l := height l) (r := height r); eauto; lia.
Qed.

End METHODS.

#[universes(template), projections(primitive)]
Record t (A : Type) : Type :=
  mk
  { root : tree A
  ; root_balanced : balanced root
  } as X.

#[global] Arguments mk {A} root root_balanced.
#[global] Arguments root {A} X.
#[global] Arguments root_balanced {A} X.

Section METHODS.

Context {A : Type}.

Definition data (X : BalancedTree.t A) : list A :=
  elements_acc X.(root) [].

Lemma data_elements (X : BalancedTree.t A)
  : data X = elements X.(root).
Proof.
  unfold data. rewrite elements_acc_spec, app_nil_r. reflexivity.
Qed.

Definition empty : BalancedTree.t A :=
  mk Leaf balanced_leaf.

Definition lookup (cmp : A -> comparison) (X : BalancedTree.t A) : option A :=
  lookup_raw cmp X.(root).

Definition add (cmp : A -> A -> comparison) (x : A) (X : BalancedTree.t A) : BalancedTree.t A :=
  mk (add_raw cmp x X.(root)) (proj1 (add_raw_balanced_height cmp x X.(root) X.(root_balanced))).

Definition remove (cmp : A -> comparison) (X : BalancedTree.t A) : BalancedTree.t A :=
  mk (remove_raw cmp X.(root)) (proj1 (remove_raw_balanced_height cmp X.(root) X.(root_balanced))).

Lemma balanced_height_depth (tr : tree A)
  (BALANCED : balanced tr)
  : height tr = Z.of_nat (depth tr).
Proof.
  induction BALANCED as [ | l x r h LEFT IH_l RIGHT IH_r RANGE CACHE]; cbn [height depth]; [reflexivity | ].
  rewrite Nat2Z.inj_succ, Nat2Z.inj_max, <- IH_l, <- IH_r. lia.
Qed.

Fixpoint size_balanced (tr : tree A) : Prop :=
  match tr with
  | Leaf => True
  | Node l _ r _ => size_balanced l /\ size_balanced r /\ (size l = size r \/ size l = S (size r))
  end.

Lemma size_below_depth_power (tr : tree A)
  : size tr < 2 ^ depth tr.
Proof.
  induction tr as [ | l IH_l x r IH_r h]; cbn [size depth]; [simpl; lia | ].
  rewrite Nat.pow_succ_r'.
  assert (LE_l : 2 ^ depth l <= 2 ^ Nat.max (depth l) (depth r)).
  { eapply Nat.pow_le_mono_r; lia. }
  assert (LE_r : 2 ^ depth r <= 2 ^ Nat.max (depth l) (depth r)).
  { eapply Nat.pow_le_mono_r; lia. }
  lia.
Qed.

Lemma size_balanced_depth_lower (tr : tree A)
  (BALANCE : size_balanced tr)
  : forall h, depth tr = S h -> 2 ^ h <= size tr.
Proof.
  induction tr as [ | l IH_l x r IH_r cache]; simpl; i; try congruence.
  find* (LEFT & RIGHT & SIZES) by BALANCE. inv H.
  find* [LE | GE] by (Nat.le_ge_cases (depth l) (depth r)).
  - rewrite Nat.max_r by exact LE.
    destruct (depth r) as [ | h] eqn: HEIGHT.
    + simpl; lia.
    + obtain LOWER with RIGHT by IH_r.
      rewrite Nat.pow_succ_r'. des; lia.
  - rewrite Nat.max_l by exact GE.
    destruct (depth l) as [ | h] eqn: HEIGHT.
    + simpl; lia.
    + obtain LOWER with LEFT by IH_l.
      rewrite Nat.pow_succ_r'. des; lia.
Qed.

Lemma size_balanced_depth_log (tr : tree A)
  (BALANCE : size_balanced tr)
  (POS : 0 < size tr)
  : depth tr = S (Nat.log2 (size tr)).
Proof.
  find* UPPER by (size_below_depth_power tr).
  destruct (depth tr) as [ | h] eqn: HEIGHT.
  - simpl in *; lia.
  - obtain LOWER with BALANCE HEIGHT by size_balanced_depth_lower.
    rewrite Nat.log2_le_pow2 in LOWER by exact POS.
    rewrite Nat.log2_lt_pow2 in UPPER by exact POS.
    lia.
Qed.

Lemma size_balanced_depth_step (tr1 : tree A) (tr2 : tree A)
  (BALANCE1 : size_balanced tr1)
  (BALANCE2 : size_balanced tr2)
  (SIZES : size tr1 <= size tr2 <= S (size tr1))
  : depth tr1 <= depth tr2 <= S (depth tr1).
Proof.
  find* [ZERO | NONZERO] by (Nat.eq_dec (size tr1) O).
  - destruct tr1; [ | simpl in ZERO; lia].
    destruct tr2 as [ | l x r h]; [simpl; lia | simpl size in SIZES].
    assert (EMPTY_l : l = Leaf).
    { destruct l; ss!. }
    assert (EMPTY_r : r = Leaf).
    { destruct r; ss!. }
    subst l r. simpl. lia.
  - assert (POS1 : 0 < size tr1) by lia.
    assert (POS2 : 0 < size tr2) by lia.
    rewrite size_balanced_depth_log with (tr := tr1) by eauto.
    rewrite size_balanced_depth_log with (tr := tr2) by eauto.
    obtain LOWER with (proj1 SIZES) by Nat.log2_le_mono.
    obtain UPPER with (proj2 SIZES) by Nat.log2_le_mono.
    obtain STEP with (size tr1) by Nat.log2_succ_le. lia.
Qed.

Lemma div2_split (n : nat)
  : Nat.div2 (S n) + Nat.div2 n = n /\ (Nat.div2 (S n) = Nat.div2 n \/ Nat.div2 (S n) = S (Nat.div2 n)).
Proof.
  induction n as [ | n IH]; simpl; auto.
  change (S (Nat.div2 n) + Nat.div2 (S n) = S n /\ (S (Nat.div2 n) = Nat.div2 (S n) \/ S (Nat.div2 n) = S (Nat.div2 (S n)))).
  des; splits; lia.
Qed.

Lemma binary_split (n : N)
  (POS : 0 < N.to_nat n)
  : N.to_nat (N.div2 n) + N.to_nat (N.div2 (N.pred n)) + 1 = N.to_nat n /\ (N.to_nat (N.div2 n) = N.to_nat (N.div2 (N.pred n)) \/ N.to_nat (N.div2 n) = S (N.to_nat (N.div2 (N.pred n)))).
Proof.
  rewrite !N2Nat.inj_div2, N2Nat.inj_pred.
  destruct (N.to_nat n) as [ | k]; [lia | simpl Nat.pred].
  obtain [SUM BALANCE] with k by div2_split. split; [lia | exact BALANCE].
Qed.

Fixpoint build (fuel : nat) (n : N) (xs : list A) {struct fuel} : tree A * list A :=
  match fuel, n with
  | O, _ => (Leaf, xs)
  | _, N0 => (Leaf, xs)
  | S fuel', Npos p =>
    let '(l, middle) := build fuel' (N.div2 (Npos p)) xs in
    match middle with
    | [] => (l, [])
    | x :: rest =>
      let '(r, suffix) := build fuel' (N.div2 (N.pred (Npos p))) rest in
      (create l x r, suffix)
    end
  end.

Lemma build_spec (fuel : nat) (n : N) (xs : list A)
  (BOUND : N.to_nat n <= fuel)
  (ENOUGH : N.to_nat n <= length xs)
  : let '(tr, suffix) := build fuel n xs in
    balanced tr /\ size_balanced tr /\ size tr = N.to_nat n /\ elements tr ++ suffix = xs.
Proof.
  revert_until fuel. induction fuel as [ | fuel IH]; i.
  - assert (EQ : N.to_nat n = O) by lia.
    simpl. splits; auto. eapply balanced_leaf.
  - destruct n as [ | p].
    + simpl. splits; auto. eapply balanced_leaf.
    + cbn [build].
      assert (POS : 0 < N.to_nat (Npos p)) by apply Pos2Nat.is_pos.
      obtain [SUM BALANCE] with POS by binary_split.
      obtain SPEC_l with (N.div2 (Npos p)) xs by IH.
      destruct (build fuel (N.div2 (Npos p)) xs) as [l middle].
      find* (AVL_l & BALANCE_l & SIZE_l & EQ_l) by SPEC_l.
      destruct middle as [ | x rest].
      { rewrite app_nil_r in EQ_l.
        obtain LENGTH with EQ_l by (f_equal (@length A)).
        rewrite length_elements in LENGTH. lia.
      }
      { assert (ENOUGH_r : N.to_nat (N.div2 (N.pred (Npos p))) <= length rest).
        { obtain LENGTH with EQ_l by (f_equal (@length A)).
          rewrite length_app, length_elements in LENGTH. simpl in LENGTH. lia.
        }
        obtain SPEC_r with (N.div2 (N.pred (Npos p))) rest by IH.
        destruct (build fuel (N.div2 (N.pred (Npos p))) rest) as [r suffix].
        find* (AVL_r & BALANCE_r & SIZE_r & EQ_r) by SPEC_r. splits.
        - eapply create_balanced; auto.
          rewrite balanced_height_depth by exact AVL_l. rewrite balanced_height_depth by exact AVL_r.
          assert (SIZES : size r <= size l <= S (size r)) by now rewrite SIZE_l, SIZE_r; des; lia.
          obtain HEIGHTS with BALANCE_r BALANCE_l SIZES by size_balanced_depth_step. lia.
        - simpl. rewrite SIZE_l, SIZE_r. auto.
        - simpl. lia.
        - rewrite elements_create, <- app_assoc. simpl. congruence.
      }
Qed.

Lemma binary_length_spec (xs : list A) (acc : N)
  : N.to_nat (L.fold_left (fun n => fun _ => N.succ n) xs acc) = length xs + N.to_nat acc.
Proof.
  revert acc. induction xs as [ | x xs IH]; i; simpl; auto.
  rewrite IH, N2Nat.inj_succ. lia.
Qed.

#[refine]
Definition of_list (xs : list A) : BalancedTree.t A :=
  let fuel := L.fold_left (fun n : nat => fun _ => S n) xs 0 in
  let n := L.fold_left (fun n : N => fun _ => N.succ n) xs 0%N in
  BalancedTree.mk (fst (build fuel n xs)) _.
Proof.
  assert (FUEL : fuel = length xs) by apply L.fold_left_S_0.
  assert (SIZE : N.to_nat n = length xs).
  { unfold n. rewrite binary_length_spec. cbn. lia. }
  obtain SPEC with fuel n xs by build_spec.
  destruct (build fuel n xs) as [tr suffix]. exact (proj1 SPEC).
Defined.

Theorem data_of_list (xs : list A)
  : data (of_list xs) = xs.
Proof.
  rewrite data_elements. unfold of_list. simpl.
  rewrite L.fold_left_S_0.
  set (n := L.fold_left (fun n : N => fun _ => N.succ n) xs 0%N).
  assert (SIZE : N.to_nat n = length xs).
  { unfold n. rewrite binary_length_spec. cbn. lia. }
  obtain SPEC with (length xs) n xs by build_spec.
  destruct (build (length xs) n xs) as [tr suffix]. simpl in *.
  find* (AVL & BALANCE & SIZE' & EQ) by SPEC.
  assert (NIL : suffix = []).
  { obtain LENGTH with EQ by (f_equal (@length A)).
    rewrite length_app, length_elements in LENGTH.
    destruct suffix; simpl in *; [reflexivity | lia].
  }
  subst suffix. now rewrite app_nil_r in EQ.
Qed.

Lemma balanced_height_min_depth (tr : tree A)
  (BALANCED : balanced tr)
  : (height tr <= 3 * Z.of_nat (min_depth tr))%Z.
Proof.
  induction BALANCED; cbn [height min_depth]; [lia | ].
  find* [LE | GE] by (Nat.le_ge_cases (min_depth l) (min_depth r)).
  - rewrite Nat.min_l by exact LE. rewrite Nat2Z.inj_succ. des_ifs; lia.
  - rewrite Nat.min_r by exact GE. rewrite Nat2Z.inj_succ. des_ifs; lia.
Qed.

Lemma min_depth_size (tr : tree A)
  : 2 ^ min_depth tr <= S (size tr).
Proof.
  induction tr as [ | l IH_l x r IH_r h]; cbn [min_depth size]; [simpl; lia | ].
  rewrite Nat.pow_succ_r'.
  assert (LE_l : 2 ^ Nat.min (min_depth l) (min_depth r) <= 2 ^ min_depth l) by (eapply Nat.pow_le_mono_r; lia).
  assert (LE_r : 2 ^ Nat.min (min_depth l) (min_depth r) <= 2 ^ min_depth r) by (eapply Nat.pow_le_mono_r; lia).
  lia.
Qed.

Theorem balanced_depth_bound (tr : tree A)
  (BALANCED : balanced tr)
  : depth tr <= 3 * Nat.log2 (S (size tr)).
Proof.
  obtain HEIGHT with BALANCED by balanced_height_min_depth.
  obtain DEPTH with BALANCED by balanced_height_depth. rewrite DEPTH in HEIGHT.
  obtain SIZE with tr by min_depth_size.
  rewrite Nat.log2_le_pow2 in SIZE by lia. lia.
Qed.

Section steps.

Variable cmp : A -> comparison.

Fixpoint lookup_steps (tr : tree A) : nat :=
  match tr with
  | Leaf => O
  | Node l x r _ =>
    match cmp x with
    | Eq => 1
    | Lt => S (lookup_steps l)
    | Gt => S (lookup_steps r)
    end
  end.

Lemma lookup_steps_depth (tr : tree A)
  : lookup_steps tr <= depth tr.
Proof.
  induction tr; simpl; des_ifs; lia.
Qed.

Theorem lookup_steps_logarithmic (X : t A)
  : lookup_steps X.(root) <= 3 * Nat.log2 (S (length (data X))).
Proof.
  rewrite data_elements, length_elements.
  obtain STEPS with X.(root) by lookup_steps_depth.
  obtain DEPTH with X.(root_balanced) by balanced_depth_bound.
  lia.
Qed.

End steps.

End METHODS.

Section fold.

Context {A : Type} {B : Type} (f : B -> A -> B).

Fixpoint fold_raw (tr : tree A) (acc : B) : B :=
  match tr with
  | Leaf => acc
  | Node l x r _ => fold_raw r (f (fold_raw l acc) x)
  end.

Lemma fold_raw_spec (tr : tree A) (acc : B)
  : fold_raw tr acc = L.fold_left f (elements tr) acc.
Proof.
  revert acc. induction tr; i; cbn [fold_raw elements]; auto.
  rewrite L.fold_left_app. cbn [L.fold_left]. now rewrite IHtr1, IHtr2.
Qed.

Definition fold (X : t A) : B -> B :=
  fold_raw X.(root).

Lemma fold_spec (X : t A) (acc : B)
  : fold X acc = L.fold_left f (data X) acc.
Proof.
  unfold fold. rewrite fold_raw_spec, data_elements. reflexivity.
Qed.

End fold.

Section map.

Context {A : Type} {B : Type} (f : A -> B).

Fixpoint map_raw (tr : tree A) : tree B :=
  match tr with
  | Leaf => Leaf
  | Node l x r h => Node (map_raw l) (f x) (map_raw r) h
  end.

Lemma height_map (tr : tree A)
  : height (map_raw tr) = height tr.
Proof.
  destruct tr; reflexivity.
Qed.

Lemma map_balanced (tr : tree A)
  (BALANCED : balanced tr)
  : balanced (map_raw tr).
Proof.
  induction BALANCED; cbn [map_raw]; econs; auto; now rewrite !height_map.
Qed.

Definition map (X : BalancedTree.t A) : BalancedTree.t B :=
  mk (map_raw X.(root)) (map_balanced X.(root) X.(root_balanced)).

Lemma elements_map (tr : tree A)
  : elements (map_raw tr) = L.map f (elements tr).
Proof.
  induction tr; cbn [map_raw elements]; auto. rewrite L.map_app. cbn [L.map]. now rewrite IHtr1, IHtr2.
Qed.

Lemma data_map (X : BalancedTree.t A)
  : data (map X) = L.map f (data X).
Proof.
  rewrite !data_elements. unfold map. cbn [root]. apply elements_map.
Qed.

End map.

Section ORDERED_TREE.

Context {A : Type} {K : Type} {PROSET : isProset K} {ORD : hsOrd K}.

Variable key : A -> K.

Lemma sorted_app_inv (xs : list A) (ys : list A)
  (SORTED : isSorted compare (L.map key (xs ++ ys)) = true)
  : isSorted compare (L.map key xs) = true /\ isSorted compare (L.map key ys) = true /\ (forall x, forall y, L.In x xs -> L.In y ys -> compare (key x) (key y) = Lt).
Proof.
  revert SORTED. induction xs as [ | x xs IH]; i.
  - cbn in *. split; [reflexivity | split; [exact SORTED | ]]. ii. inv H.
  - cbn [app] in SORTED. rewrite OrderedList.sorted_cons_iff in SORTED. des.
    obtain (SORTED_xs & SORTED_ys & CROSS) with SORTED0 by IH.
    splits; eauto.
    + rewrite OrderedList.sorted_cons_iff. split; eauto.
      ii. eapply SORTED. rewrite L.in_app_iff. eauto.
    + ii; simpl in *; des; clarify; eauto.
      eapply SORTED. rewrite L.in_app_iff. eauto.
Qed.

Lemma compare_ge_gt_left (k : K) (x : A) (y : A)
  (GE : compare k (key y) ≠ Lt)
  (LT : compare (key x) (key y) = Lt)
  : compare k (key x) = Gt.
Proof.
  destruct (compare k (key y)) eqn: OBS; [ | congruence | ].
  - rewrite compare_compatWith_eqProp with (x' := key y) (y' := key x) by now try reflexivity; now rewrite <- compare_Eq_iff.
    now apply compare_Lt_flip.
  - apply compare_Lt_flip. eapply compare_Lt_trans; [exact LT | now apply compare_Gt_flip].
Qed.

Lemma lookup_app_gt (k : K) (xs : list A) (ys : list A)
  (GT : forall x, L.In x xs -> compare k (key x) = Gt)
  : OrderedList.lookup key k (xs ++ ys) = OrderedList.lookup key k ys.
Proof.
  revert GT. induction xs as [ | x xs IH]; i; [reflexivity | ].
  cbn [app OrderedList.lookup]. rewrite GT by now left. eapply IH. ii. apply GT. now right.
Qed.

Lemma lookup_app_lt (k : K) (xs : list A) (y : A) (ys : list A)
  (LT : compare k (key y) = Lt)
  : OrderedList.lookup key k (xs ++ y :: ys) = OrderedList.lookup key k xs.
Proof.
  induction xs as [ | x xs IH]; cbn [app OrderedList.lookup].
  - now rewrite LT.
  - destruct (compare k (key x)); auto.
Qed.

Lemma insert_app_gt (x : A) (xs : list A) (ys : list A)
  (GT : forall y, L.In y xs -> compare (key x) (key y) = Gt)
  : OrderedList.insert key x (xs ++ ys) = xs ++ OrderedList.insert key x ys.
Proof.
  revert GT. induction xs as [ | y xs IH]; i; [reflexivity | ].
  cbn [app OrderedList.insert]. rewrite GT by now left. f_equal. eapply IH. ii. apply GT. now right.
Qed.

Lemma insert_app_lt (x : A) (xs : list A) (y : A) (ys : list A)
  (LT : compare (key x) (key y) = Lt)
  : OrderedList.insert key x (xs ++ y :: ys) = OrderedList.insert key x xs ++ y :: ys.
Proof.
  induction xs as [ | z xs IH]; cbn [app OrderedList.insert].
  - now rewrite LT.
  - destruct (compare (key x) (key z)); cbn [app]; congruence.
Qed.

Lemma remove_app_gt (k : K) (xs : list A) (ys : list A)
  (GT : forall x, L.In x xs -> compare k (key x) = Gt)
  : OrderedList.remove key k (xs ++ ys) = xs ++ OrderedList.remove key k ys.
Proof.
  revert GT. induction xs as [ | x xs IH]; i; [reflexivity | ].
  cbn [app OrderedList.remove]. rewrite GT by now left. f_equal. eapply IH. ii. apply GT. now right.
Qed.

Lemma remove_app_lt (k : K) (xs : list A) (y : A) (ys : list A)
  (LT : compare k (key y) = Lt)
  : OrderedList.remove key k (xs ++ y :: ys) = OrderedList.remove key k xs ++ y :: ys.
Proof.
  induction xs as [ | x xs IH]; cbn [app OrderedList.remove].
  - now rewrite LT.
  - destruct (compare k (key x)); cbn [app]; congruence.
Qed.

Theorem lookup_raw_elements (k : K) (tr : tree A)
  (SORTED : isSorted compare (L.map key (elements tr)) = true)
  : lookup_raw (fun x => compare k (key x)) tr = OrderedList.lookup key k (elements tr).
Proof.
  revert SORTED. induction tr as [ | l IH_l y r IH_r h]; i; [reflexivity | ].
  cbn [elements] in SORTED.
  obtain (SORTED_l & SORTED_yr & CROSS) with SORTED by sorted_app_inv.
  rewrite OrderedList.sorted_cons_iff in SORTED_yr. find* (SORTED_y & SORTED_r) by SORTED_yr.
  assert (LEFT : forall x, L.In x (elements l) -> compare (key x) (key y) = Lt).
  { ii. eapply CROSS; eauto. now left. }
  cbn [lookup_raw elements]. destruct (compare k (key y)) eqn: OBS.
  - rewrite lookup_app_gt.
    + cbn [OrderedList.lookup]. now rewrite OBS.
    + ii. eapply compare_ge_gt_left; eauto; congruence.
  - rewrite lookup_app_lt by exact OBS. eapply IH_l; eauto.
  - rewrite lookup_app_gt.
    + cbn [OrderedList.lookup]. rewrite OBS. eapply IH_r; eauto.
    + ii. eapply compare_ge_gt_left; eauto; congruence.
Qed.

Theorem add_raw_elements (x : A) (tr : tree A)
  (SORTED : isSorted compare (L.map key (elements tr)) = true)
  : elements (add_raw (fun a => fun b => compare (key a) (key b)) x tr) = OrderedList.insert key x (elements tr).
Proof.
  revert SORTED. induction tr as [ | l IH_l y r IH_r h]; i; [reflexivity | ].
  cbn [elements] in SORTED.
  obtain (SORTED_l & SORTED_yr & CROSS) with SORTED by sorted_app_inv.
  rewrite OrderedList.sorted_cons_iff in SORTED_yr. find* (SORTED_y & SORTED_r) by SORTED_yr.
  assert (LEFT : forall z, L.In z (elements l) -> compare (key z) (key y) = Lt).
  { ii. eapply CROSS; eauto. now left. }
  cbn [add_raw]. destruct (compare (key x) (key y)) eqn: OBS.
  - cbn [elements]. rewrite insert_app_gt.
    + cbn [OrderedList.insert]. now rewrite OBS.
    + ii. eapply compare_ge_gt_left; eauto; congruence.
  - rewrite elements_bal, IH_l by exact SORTED_l.
    cbn [elements]. rewrite insert_app_lt by exact OBS. reflexivity.
  - rewrite elements_bal, IH_r by exact SORTED_r.
    cbn [elements]. rewrite insert_app_gt.
    + cbn [OrderedList.insert]. now rewrite OBS.
    + ii. eapply compare_ge_gt_left; eauto; congruence.
Qed.

Theorem remove_raw_elements (k : K) (tr : tree A)
  (SORTED : isSorted compare (L.map key (elements tr)) = true)
  : elements (remove_raw (fun x => compare k (key x)) tr) = OrderedList.remove key k (elements tr).
Proof.
  revert SORTED. induction tr as [ | l IH_l y r IH_r h]; i; [reflexivity | ].
  cbn [elements] in SORTED.
  obtain (SORTED_l & SORTED_yr & CROSS) with SORTED by sorted_app_inv.
  rewrite OrderedList.sorted_cons_iff in SORTED_yr. find* (SORTED_y & SORTED_r) by SORTED_yr.
  assert (LEFT : forall x, L.In x (elements l) -> compare (key x) (key y) = Lt).
  { ii. eapply CROSS; eauto. now left. }
  cbn [remove_raw]. destruct (compare k (key y)) eqn: OBS.
  - rewrite elements_merge. cbn [elements]. rewrite remove_app_gt.
    + cbn [OrderedList.remove]. now rewrite OBS.
    + ii. eapply compare_ge_gt_left; eauto; congruence.
  - rewrite elements_bal, IH_l by exact SORTED_l.
    cbn [elements]. rewrite remove_app_lt by exact OBS. reflexivity.
  - rewrite elements_bal, IH_r by exact SORTED_r.
    cbn [elements]. rewrite remove_app_gt.
    + cbn [OrderedList.remove]. now rewrite OBS.
    + ii. eapply compare_ge_gt_left; eauto; congruence.
Qed.

Theorem lookup_data (k : K) (X : t A)
  (SORTED : isSorted compare (L.map key (data X)) = true)
  : lookup (fun x => compare k (key x)) X = OrderedList.lookup key k (data X).
Proof.
  rewrite data_elements in SORTED |- *. unfold lookup.
  eapply lookup_raw_elements; eauto.
Qed.

Theorem data_add (x : A) (X : t A)
  (SORTED : isSorted compare (L.map key (data X)) = true)
  : data (add (fun a => fun b => compare (key a) (key b)) x X) = OrderedList.insert key x (data X).
Proof.
  rewrite data_elements with (X := X) in SORTED |- *.
  rewrite data_elements. cbn [add root].
  eapply add_raw_elements; eauto.
Qed.

Theorem data_remove (k : K) (X : t A)
  (SORTED : isSorted compare (L.map key (data X)) = true)
  : data (remove (fun x => compare k (key x)) X) = OrderedList.remove key k (data X).
Proof.
  rewrite data_elements with (X := X) in SORTED |- *.
  rewrite data_elements. cbn [remove root].
  eapply remove_raw_elements; eauto.
Qed.

End ORDERED_TREE.

End BalancedTree.
