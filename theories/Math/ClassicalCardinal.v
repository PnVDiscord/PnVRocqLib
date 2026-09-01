Require Import PnV.Prelude.Prelude.
Require Import PnV.Math.OrderTheory.
Require Import PnV.Data.Aczel.
Require Import PnV.Prelude.ClassicalFacts.
Require Import PnV.Math.SetTheory.
Require Import PnV.Data.Vector.
Require Import PnV.Math.ThN.
Require Import PnV.Prelude.PnVTacs.
Require Export PnV.Math.ClassicalSetTheory.

Import TypeTheoreticImplementation.

Module Cardinal3.

Section CARDINALITY.

Context `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}.

#[local] Existing Instance Aczel.children_isSetoid.

Lemma Cardinality_ofType_bool_le_of_nat_le (A : Type@{Set_u})
  (NAT_LE : Cardinality.ofType nat =< Cardinality.ofType A)
  : Cardinality.ofType bool =< Cardinality.ofType A.
Proof.
  destruct NAT_LE as [f f_cong f_inj].
  eapply Cardinal2.Cardinality_ofType_le_ofType with (f := fun b : bool => if b then f O else f (S O)).
  intros [ | ] [ | ] EQ; try reflexivity.
  - pose proof (f_inj O (S O) EQ) as H. discriminate H.
  - pose proof (f_inj (S O) O EQ) as H. discriminate H.
Qed.

Definition option_pair_code {A : Type@{Set_u}} (tag : nat -> A) (pair : A * A -> A) (xy : option A * option A) : A :=
  match xy with
  | (None, None) => pair (tag O, tag O)
  | (None, Some y) => pair (tag (S O), y)
  | (Some x, None) => pair (tag (S (S O)), x)
  | (Some x, Some y) => pair (tag (S (S (S O))), pair (x, y))
  end.

Lemma option_pair_code_inj {A : Type@{Set_u}} (tag : nat -> A) (pair : A * A -> A)
  (TAG_INJ : forall n : nat, forall m : nat, tag n = tag m -> n = m)
  (PAIR_INJ : forall p : A * A, forall q : A * A, pair p = pair q -> p = q)
  : forall p : option A * option A, forall q : option A * option A, option_pair_code tag pair p = option_pair_code tag pair q -> p = q.
Proof.
  intros [[x | ] [y | ]] [[x' | ] [y' | ]] EQ; unfold option_pair_code in EQ.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (PAIR_INJ _ _ H0) as EQ_xy. inv EQ_xy. reflexivity.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S (S (S O))) (S (S O)) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S (S (S O))) (S O) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S (S (S O))) O H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S (S O)) (S (S (S O))) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair. reflexivity.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S (S O)) (S O) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S (S O)) O H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S O) (S (S (S O))) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S O) (S (S O)) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair. reflexivity.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ (S O) O H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ O (S (S (S O))) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ O (S (S O)) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair.
    pose proof (TAG_INJ O (S O) H0) as Htag. discriminate Htag.
  - pose proof (PAIR_INJ _ _ EQ) as EQ_pair. inv EQ_pair. reflexivity.
Qed.

Lemma Cardinality_ofType_option_prod_le_self_of_nat_le_square_le (A : Type@{Set_u})
  (NAT_LE : Cardinality.ofType nat =< Cardinality.ofType A)
  (SQUARE_LE : Cardinality.ofType (A * A) =< Cardinality.ofType A)
  : Cardinality.ofType (option A * option A) =< Cardinality.ofType A.
Proof.
  destruct NAT_LE as [tag tag_cong tag_inj]. destruct SQUARE_LE as [pair pair_cong pair_inj].
  eapply Cardinal2.Cardinality_ofType_le_ofType with (f := option_pair_code tag pair).
  eapply option_pair_code_inj.
  - intros n m EQ. change (n = m). eapply tag_inj. change (tag n = tag m). exact EQ.
  - intros [x y] [x' y'] EQ. change ((x, y) = (x', y')). eapply pair_inj. change (pair (x, y) = pair (x', y')). exact EQ.
Qed.

Fixpoint encode_list_by_pair {A : Type@{Set_u}} (pair : A * A -> A) (pack : option A -> A) (xs : list A) : option A :=
  match xs with
  | [] => None
  | x :: xs => Some (pair (x, pack (encode_list_by_pair pair pack xs)))
  end.

Lemma encode_list_by_pair_inj {A : Type@{Set_u}} (pair : A * A -> A) (pack : option A -> A)
  (PAIR_INJ : forall p : A * A, forall q : A * A, pair p = pair q -> p = q)
  (PACK_INJ : forall x : option A, forall y : option A, pack x = pack y -> x = y)
  : forall xs : list A, forall ys : list A, encode_list_by_pair pair pack xs = encode_list_by_pair pair pack ys -> xs = ys.
Proof.
  induction xs as [ | x xs IH]; intros [ | y ys] EQ; simpl in EQ.
  - reflexivity.
  - discriminate EQ.
  - discriminate EQ.
  - injection EQ as EQ_code. pose proof (PAIR_INJ _ _ EQ_code) as EQ_pair.
    injection EQ_pair as EQ_x EQ_pack. subst y. f_equal. eapply IH. eapply PACK_INJ. exact EQ_pack.
Qed.

Lemma Cardinality_ofType_list_le_self_of_nat_le_square_le (A : Type@{Set_u})
  (NAT_LE : Cardinality.ofType nat =< Cardinality.ofType A)
  (SQUARE_LE : Cardinality.ofType (A * A) =< Cardinality.ofType A)
  : Cardinality.ofType (list A) =< Cardinality.ofType A.
Proof.
  destruct SQUARE_LE as [pair pair_cong pair_inj].
  pose proof (Cardinal2.Cardinality_ofType_option_le_self_of_nat_le A NAT_LE) as OPTION_LE.
  pose proof OPTION_LE as OPTION_LE'.
  destruct OPTION_LE as [pack pack_cong pack_inj].
  transitivity (Cardinality.ofType (option A)).
  - eapply Cardinal2.Cardinality_ofType_le_ofType with (f := encode_list_by_pair pair pack).
    eapply encode_list_by_pair_inj.
    + intros [x y] [x' y'] EQ. change ((x, y) = (x', y')). eapply pair_inj. change (pair (x, y) = pair (x', y')). exact EQ.
    + intros x y EQ. change (x = y). eapply pack_inj. change (pack x = pack y). exact EQ.
  - exact OPTION_LE'.
Qed.

Lemma Cardinality_ofType_sum_nat_le_self_of_nat_le_square_le (A : Type@{Set_u})
  (NAT_LE : Cardinality.ofType nat =< Cardinality.ofType A)
  (SQUARE_LE : Cardinality.ofType (A * A) =< Cardinality.ofType A)
  : Cardinality.ofType (A + nat) =< Cardinality.ofType A.
Proof.
  transitivity (Cardinality.ofType (bool * A)).
  - destruct NAT_LE as [tag tag_cong tag_inj].
    eapply Cardinal2.Cardinality_ofType_le_ofType with (f := fun x : A + nat => match x with inl a => (true, a) | inr n => (false, tag n) end).
    intros [a | n] [a' | n'] EQ; simpl in EQ.
    + inv EQ. reflexivity.
    + inv EQ.
    + inv EQ.
    + injection EQ as EQ_tag. f_equal. eapply tag_inj. exact EQ_tag.
  - transitivity (Cardinality.ofType (A * A)).
    + eapply Cardinal2.Cardinality_ofType_prod_le.
      * eapply Cardinality_ofType_bool_le_of_nat_le. exact NAT_LE.
      * reflexivity.
    + exact SQUARE_LE.
Qed.

Lemma Cardinality_ofType_list_sum_nat_le_self_of_nat_le_square_le (A : Type@{Set_u})
  (NAT_LE : Cardinality.ofType nat =< Cardinality.ofType A)
  (SQUARE_LE : Cardinality.ofType (A * A) =< Cardinality.ofType A)
  : Cardinality.ofType (list (A + nat)) =< Cardinality.ofType A.
Proof.
  transitivity (Cardinality.ofType (list A)).
  - eapply Cardinal2.Cardinality_ofType_list_le.
    eapply Cardinality_ofType_sum_nat_le_self_of_nat_le_square_le; eauto.
  - eapply Cardinality_ofType_list_le_self_of_nat_le_square_le; eauto.
Qed.

Lemma Cardinality_ofType_rose_le_self_of_nat_le_square_le (A : Type@{Set_u})
  (NAT_LE : Cardinality.ofType nat =< Cardinality.ofType A)
  (SQUARE_LE : Cardinality.ofType (A * A) =< Cardinality.ofType A)
  : Cardinality.ofType (B.rose A) =< Cardinality.ofType A.
Proof.
  transitivity (Cardinality.ofType (list (A + nat))).
  - eapply Cardinal2.Cardinality_ofType_rose_le_list_sum_nat.
  - eapply Cardinality_ofType_list_sum_nat_le_self_of_nat_le_square_le; eauto.
Qed.

Lemma Cardinality_ofType_rose_lt_of_lt_uncountable_square_le (A : Type@{Set_u}) (kappa : Cardinality.t)
  (LT : Cardinality.ofType A ≨ kappa)
  (UNCOUNTABLE : ~ kappa =< Cardinality.ofType nat)
  (SQUARE : forall B : Type@{Set_u}, Cardinality.ofType nat =< Cardinality.ofType B -> Cardinality.ofType (B * B) =< Cardinality.ofType B)
  : Cardinality.ofType (B.rose A) ≨ kappa.
Proof.
  pose proof (Cardinal1.Cardinality_le_total (Cardinality.ofType A) (Cardinality.ofType nat)) as [A_LE_NAT | NAT_LE_A].
  - eapply Cardinal1.Cardinality_le_lt_lt.
    + transitivity (Cardinality.ofType (list (nat + nat))).
      * destruct A_LE_NAT as [f f_cong f_inj].
        eapply Cardinal2.Cardinality_ofType_le_ofType with (f := fun t : B.rose A => map (fun x : A + nat => match x with inl a => inl (f a) | inr n => inr n end) (Cardinal2.encode_rose t)).
        intros t1 t2 EQ. eapply Cardinal2.encode_rose_inj. apply L.list_map_inj in EQ.
        { exact EQ. }
        intros [a | n] [a' | n'] EQ'; inv EQ'.
        { f_equal. eapply f_inj. exact H0. }
        { reflexivity. }
      * eapply Cardinal2.Cardinality_ofType_list_countable_le_nat.
    + eapply Cardinal2.nat_lt_of_uncountable. exact UNCOUNTABLE.
  - eapply Cardinal1.Cardinality_le_lt_lt.
    + eapply Cardinality_ofType_rose_le_self_of_nat_le_square_le.
      * exact NAT_LE_A.
      * eapply SQUARE. exact NAT_LE_A.
    + exact LT.
Qed.

Theorem Cardinality_ofType_rank_strict_initial_segment_lt (A : Type@{Set_u}) (kappa : Ord.t)
  (K_CARD : Cardinal1.hasCardinality (Cardinality.ofType A) kappa)
  (enum : Aczel.children kappa -> A)
  (enum_inj : forall c1 : Aczel.children kappa, forall c2 : Aczel.children kappa, c1 == c2 <-> enum c1 = enum c2)
  (rank : A -> Aczel.children kappa)
  (RANK : forall x : A, enum (rank x) = x)
  : forall a : A, Cardinality.ofType { x : A | Aczel.isElemOf kappa (rank x) (rank a) } ≨ Cardinality.ofType A.
Proof.
  i.
  pose proof (Cardinal1.hasCardinality_isOrdinal _ _ K_CARD) as K_ORD.
  set (alpha := Aczel.childnodes kappa (rank a)).
  assert (ALPHA_ORD : Aczel.isOrdinal alpha).
  { eapply Aczel.isOrdinal_member_isOrdinal.
    - exact K_ORD.
    - unfold alpha. eapply Aczel.member_intro.
  }
  assert (ALPHA_LT : alpha <ᵣ kappa).
  { unfold alpha. eapply Aczel.member_implies_rLt. eapply Aczel.member_intro. }
  assert (STRICT_LE : Cardinality.ofType { x : A | Aczel.isElemOf kappa (rank x) (rank a) } =< card alpha).
  { assert (Hchoice : forall i : { x : A | Aczel.isElemOf kappa (rank x) (rank a) }, exists c : Aczel.children alpha, Aczel.childnodes alpha c == Aczel.childnodes kappa (rank (proj1_sig i))).
    { intros [x Hx]. unfold alpha. unfold Aczel.isElemOf in Hx. destruct Hx as [c EQ]. exists c. symmetry. exact EQ. }
    pose proof (Axiom_of_Choice { x : A | Aczel.isElemOf kappa (rank x) (rank a) } (fun _ : { x : A | Aczel.isElemOf kappa (rank x) (rank a) } => Aczel.children alpha) (fun i : { x : A | Aczel.isElemOf kappa (rank x) (rank a) } => fun c : Aczel.children alpha => Aczel.childnodes alpha c == Aczel.childnodes kappa (rank (proj1_sig i))) Hchoice) as [pick PICK].
    exists pick.
    - intros i j EQ. change (i = j) in EQ. subst j. reflexivity.
    - intros [x Hx] [y Hy] EQ. eapply Cardinal2.sig_eq_from_proj1. simpl.
      assert (RANK_EQ : rank x == rank y).
      { change (Aczel.childnodes kappa (rank x) == Aczel.childnodes kappa (rank y)).
        transitivity (Aczel.childnodes alpha (pick (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a)) x Hx))).
        - symmetry. exact (PICK (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a)) x Hx)).
        - transitivity (Aczel.childnodes alpha (pick (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a)) y Hy))).
          + exact EQ.
          + exact (PICK (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a)) y Hy)).
      }
      pose proof (proj1 (enum_inj (rank x) (rank y)) RANK_EQ) as ENUM_EQ. now rewrite 2 RANK in ENUM_EQ.
  }
  assert (K_CARDINAL : Cardinal1.isCardinal kappa).
  { exists (Cardinality.ofType A). exact K_CARD. }
  pose proof (Cardinal1.card_children_lt_card_of_rLt alpha kappa ALPHA_ORD K_CARDINAL ALPHA_LT) as CARD_ALPHA_LT_KAPPA.
  assert (CARD_KAPPA_LE : card kappa =< Cardinality.ofType A).
  { pose proof (Cardinal1.isCardinal_elim kappa K_CARDINAL) as CARD_KAPPA.
    rewrite Cardinal1.Cardinality_le_iff. rewrite (Cardinal1.Cardinality_toTree_eq_intro (card kappa) kappa CARD_KAPPA).
    rewrite (Cardinal1.Cardinality_toTree_eq_intro (Cardinality.ofType A) kappa K_CARD). reflexivity.
  }
  eapply Cardinal1.Cardinality_le_lt_lt.
  - exact STRICT_LE.
  - eapply Cardinal1.Cardinality_lt_le_lt.
    + exact CARD_ALPHA_LT_KAPPA.
    + exact CARD_KAPPA_LE.
Qed.

Theorem Cardinality_ofType_rank_initial_segment_lt (A : Type@{Set_u}) (kappa : Ord.t)
  (K_CARD : Cardinal1.hasCardinality (Cardinality.ofType A) kappa)
  (UNCOUNTABLE : ~ Cardinality.ofType A =< Cardinality.ofType nat)
  (enum : Aczel.children kappa -> A)
  (enum_inj : forall c1 : Aczel.children kappa, forall c2 : Aczel.children kappa, c1 == c2 <-> enum c1 = enum c2)
  (rank : A -> Aczel.children kappa)
  (RANK : forall x : A, enum (rank x) = x)
  : forall a : A, Cardinality.ofType { x : A | Aczel.isElemOf kappa (rank x) (rank a) \/ Aczel.eqTree (Aczel.childnodes kappa (rank x)) (Aczel.childnodes kappa (rank a)) } ≨ Cardinality.ofType A.
Proof.
  i.
  set (StrictIdx := { x : A | Aczel.isElemOf kappa (rank x) (rank a) }).
  set (Idx := { x : A | Aczel.isElemOf kappa (rank x) (rank a) \/ Aczel.eqTree (Aczel.childnodes kappa (rank x)) (Aczel.childnodes kappa (rank a)) }).
  assert (IDX_LE : Cardinality.ofType Idx =< Cardinality.ofType (option StrictIdx)).
  { assert (Hchoice : forall i : Idx, exists oi : option StrictIdx, match oi with | Some j => proj1_sig j = proj1_sig i | None => rank (proj1_sig i) == rank a end).
    { intros [x [LT | EQ]].
      - exists (Some (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a)) x LT)). reflexivity.
      - exists None. exact EQ.
    }
    pose proof (Axiom_of_Choice Idx (fun _ : Idx => option StrictIdx) (fun i : Idx => fun oi : option StrictIdx => match oi with | Some j => proj1_sig j = proj1_sig i | None => rank (proj1_sig i) == rank a end) Hchoice) as [pick PICK].
    exists pick.
    - intros i j EQ. change (i = j) in EQ. subst j. reflexivity.
    - intros [x Hx] [y Hy] EQ. unfold Idx in *. simpl in *.
      pose proof (PICK (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a) \/ Aczel.eqTree (Aczel.childnodes kappa (rank z)) (Aczel.childnodes kappa (rank a))) x Hx)) as PICKx.
      pose proof (PICK (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a) \/ Aczel.eqTree (Aczel.childnodes kappa (rank z)) (Aczel.childnodes kappa (rank a))) y Hy)) as PICKy.
      destruct (pick (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a) \/ Aczel.eqTree (Aczel.childnodes kappa (rank z)) (Aczel.childnodes kappa (rank a))) x Hx)) as [[x' Hx'] | ] eqn:PICK_X; destruct (pick (@exist A (fun z : A => Aczel.isElemOf kappa (rank z) (rank a) \/ Aczel.eqTree (Aczel.childnodes kappa (rank z)) (Aczel.childnodes kappa (rank a))) y Hy)) as [[y' Hy'] | ] eqn:PICK_Y; simpl in *.
      + injection EQ as STRICT_EQ. eapply Cardinal2.sig_eq_from_proj1. simpl.
        rewrite <- PICKx. rewrite <- PICKy. exact STRICT_EQ.
      + discriminate EQ.
      + discriminate EQ.
      + eapply Cardinal2.sig_eq_from_proj1. simpl.
        assert (RANK_EQ : rank x == rank y).
        { transitivity (rank a); [exact PICKx | symmetry; exact PICKy]. }
        pose proof (proj1 (enum_inj (rank x) (rank y)) RANK_EQ) as ENUM_EQ. now rewrite 2 RANK in ENUM_EQ.
  }
  eapply Cardinal1.Cardinality_le_lt_lt.
  - unfold Idx in IDX_LE. exact IDX_LE.
  - eapply Cardinal2.Cardinality_ofType_option_lt_of_lt_uncountable.
    + unfold StrictIdx. eapply Cardinality_ofType_rank_strict_initial_segment_lt; eauto.
    + exact UNCOUNTABLE.
Qed.

Section SQUARE_ABSORPTION.

Variable A : Type@{Set_u}.

Variable nat_embed : nat -> A.

Hypothesis nat_embed_inj : forall n : nat, forall m : nat, nat_embed n = nat_embed m -> n = m.

Record square_state : Type :=
  mk_square_state
  { st_carrier : Type@{Set_u}
  ; st_isSetoid : isSetoid st_carrier
  ; st_emb : st_carrier -> A
  ; st_emb_cong : forall x : st_carrier, forall y : st_carrier, @eqProp st_carrier st_isSetoid x y -> st_emb x = st_emb y
  ; st_emb_inj : forall x : st_carrier, forall y : st_carrier, st_emb x = st_emb y -> @eqProp st_carrier st_isSetoid x y
  ; st_nat : nat -> st_carrier
  ; st_nat_emb : forall n : nat, st_emb (st_nat n) = nat_embed n
  ; st_code : st_carrier * st_carrier -> st_carrier
  ; st_code_cong : forall x1 : st_carrier, forall x2 : st_carrier, forall y1 : st_carrier, forall y2 : st_carrier, @eqProp st_carrier st_isSetoid x1 x2 -> @eqProp st_carrier st_isSetoid y1 y2 -> @eqProp st_carrier st_isSetoid (st_code (x1, y1)) (st_code (x2, y2))
  ; st_code_inj : forall x1 : st_carrier, forall x2 : st_carrier, forall y1 : st_carrier, forall y2 : st_carrier, @eqProp st_carrier st_isSetoid (st_code (x1, y1)) (st_code (x2, y2)) -> @eqProp st_carrier st_isSetoid x1 x2 /\ @eqProp st_carrier st_isSetoid y1 y2
  }.

Definition state_card (s : square_state) : Cardinality.t :=
  Cardinality.mk (st_carrier s) (st_isSetoid s).

Lemma st_nat_inj (s : square_state) (n : nat) (m : nat)
  (EQ : @eqProp (st_carrier s) (st_isSetoid s) (st_nat s n) (st_nat s m))
  : n = m.
Proof.
  eapply nat_embed_inj. rewrite <- (st_nat_emb s n). rewrite <- (st_nat_emb s m). now eapply st_emb_cong.
Qed.

Definition square_state_initial
  : square_state.
Proof.
  refine (
    {|
      st_carrier := nat;
      st_isSetoid := mkSetoid_from_eq;
      st_emb := nat_embed;
      st_emb_cong := _;
      st_emb_inj := _;
      st_nat := fun n : nat => n;
      st_nat_emb := fun _ : nat => eq_refl;
      st_code := fun xy : nat * nat => cpInv (Datatypes.fst xy) (Datatypes.snd xy);
      st_code_cong := _;
      st_code_inj := _;
    |}
  ).
  - intros x y EQ. change (x = y) in EQ. subst y. reflexivity.
  - intros x y EQ. eapply nat_embed_inj. exact EQ.
  - intros x1 x2 y1 y2 EQ_x EQ_y. change (x1 = x2) in EQ_x. change (y1 = y2) in EQ_y. now subst x2 y2.
  - intros x1 x2 y1 y2 EQ. eapply cpInv_inj. exact EQ.
Defined.

Record state_embedding (s : square_state) (t : square_state) : Type :=
  mk_state_embedding
  { st_lift : st_carrier s -> st_carrier t
  ; st_lift_cong : forall x : st_carrier s, forall y : st_carrier s, @eqProp (st_carrier s) (st_isSetoid s) x y -> @eqProp (st_carrier t) (st_isSetoid t) (st_lift x) (st_lift y)
  ; st_lift_emb : forall x : st_carrier s, st_emb t (st_lift x) = st_emb s x
  ; st_lift_code : forall x : st_carrier s, forall y : st_carrier s, @eqProp (st_carrier t) (st_isSetoid t) (st_lift (st_code s (x, y))) (st_code t (st_lift x, st_lift y))
  }.

Definition state_le (s : square_state) (t : square_state) : Prop :=
  exists emb : state_embedding s t, True.

#[local]
Instance state_le_PreOrder
  : PreOrder state_le.
Proof.
  split.
  - intros s.
    exists (
      {|
        st_lift := fun x : st_carrier s => x;
        st_lift_cong := fun _ => fun _ => fun H => H;
        st_lift_emb := fun _ => eq_refl;
        st_lift_code := fun _ => fun _ => eqProp_refl _;
      |}
    ).
    exact I.
  - intros s t u [emb_st _] [emb_tu _].
    unshelve eexists (
      {|
        st_lift := fun x : st_carrier s => st_lift t u emb_tu (st_lift s t emb_st x);
        st_lift_cong := fun x => fun y => fun H => st_lift_cong t u emb_tu _ _ (st_lift_cong s t emb_st _ _ H);
        st_lift_emb := _;
        st_lift_code := _;
      |}
    ); [simpl | simpl | exact I].
    + intros x. rewrite st_lift_emb. eapply st_lift_emb.
    + intros x y. transitivity (st_lift t u emb_tu (st_code t (st_lift s t emb_st x, st_lift s t emb_st y))).
      * eapply st_lift_cong. eapply st_lift_code.
      * eapply st_lift_code.
Qed.

#[local]
Instance square_state_isProset : isProset square_state :=
  { leProp := state_le
  ; Proset_isSetoid := mkSetoidFromPreOrder state_le_PreOrder
  ; leProp_PreOrder := state_le_PreOrder
  ; leProp_PartialOrder := mkSetoidFromPreOrder_good state_le_PreOrder
  }.

Definition state_encode_sum (s : square_state) (x : st_carrier s + st_carrier s) : st_carrier s :=
  match x with
  | inl a => st_code s (st_nat s O, a)
  | inr a => st_code s (st_nat s (S O), a)
  end.

Definition state_sum_isSetoid (s : square_state) : isSetoid (st_carrier s + st_carrier s) :=
  @sum_isSetoid (st_carrier s) (st_carrier s) (st_isSetoid s) (st_isSetoid s).

Definition state_sum_prod_isSetoid (s : square_state) : isSetoid ((st_carrier s + st_carrier s) * (st_carrier s + st_carrier s)) :=
  @prod_isSetoid _ _ (state_sum_isSetoid s) (state_sum_isSetoid s).

Lemma state_encode_sum_cong (s : square_state)
  : forall x : st_carrier s + st_carrier s, forall y : st_carrier s + st_carrier s, @eqProp (st_carrier s + st_carrier s) (state_sum_isSetoid s) x y -> @eqProp (st_carrier s) (st_isSetoid s) (state_encode_sum s x) (state_encode_sum s y).
Proof.
  intros [x | x] [y | y] EQ; inv EQ; simpl.
  - eapply st_code_cong; [reflexivity | exact x_corres].
  - eapply st_code_cong; [reflexivity | exact y_corres].
Qed.

Lemma state_encode_sum_inj (s : square_state)
  : forall x : st_carrier s + st_carrier s, forall y : st_carrier s + st_carrier s, @eqProp (st_carrier s) (st_isSetoid s) (state_encode_sum s x) (state_encode_sum s y) -> @eqProp (st_carrier s + st_carrier s) (state_sum_isSetoid s) x y.
Proof.
  intros [x | x] [y | y] EQ; simpl in EQ.
  - pose proof (st_code_inj s (st_nat s O) (st_nat s O) x y EQ) as [_ EQ_xy]. econs. exact EQ_xy.
  - pose proof (st_code_inj s (st_nat s O) (st_nat s (S O)) x y EQ) as [EQ_tag _].
    pose proof (st_nat_inj s O (S O) EQ_tag) as BAD. discriminate BAD.
  - pose proof (st_code_inj s (st_nat s (S O)) (st_nat s O) x y EQ) as [EQ_tag _].
    pose proof (st_nat_inj s (S O) O EQ_tag) as BAD. discriminate BAD.
  - pose proof (st_code_inj s (st_nat s (S O)) (st_nat s (S O)) x y EQ) as [_ EQ_xy]. econs. exact EQ_xy.
Qed.

Definition state_encode_pair (s : square_state) (xy : (st_carrier s + st_carrier s) * (st_carrier s + st_carrier s)) : st_carrier s :=
  st_code s (state_encode_sum s (Datatypes.fst xy), state_encode_sum s (Datatypes.snd xy)).

Lemma state_encode_pair_cong (s : square_state)
  : forall p : (st_carrier s + st_carrier s) * (st_carrier s + st_carrier s), forall q : (st_carrier s + st_carrier s) * (st_carrier s + st_carrier s), @eqProp ((st_carrier s + st_carrier s) * (st_carrier s + st_carrier s)) (state_sum_prod_isSetoid s) p q -> @eqProp (st_carrier s) (st_isSetoid s) (state_encode_pair s p) (state_encode_pair s q).
Proof.
  intros [x1 y1] [x2 y2] [EQ_x EQ_y]. simpl.
  eapply st_code_cong; eapply state_encode_sum_cong; assumption.
Qed.

Lemma state_encode_pair_inj (s : square_state)
  : forall p : (st_carrier s + st_carrier s) * (st_carrier s + st_carrier s), forall q : (st_carrier s + st_carrier s) * (st_carrier s + st_carrier s), @eqProp (st_carrier s) (st_isSetoid s) (state_encode_pair s p) (state_encode_pair s q) -> @eqProp ((st_carrier s + st_carrier s) * (st_carrier s + st_carrier s)) (state_sum_prod_isSetoid s) p q.
Proof.
  intros [x1 y1] [x2 y2] EQ. simpl in EQ.
  pose proof (st_code_inj s (state_encode_sum s x1) (state_encode_sum s x2) (state_encode_sum s y1) (state_encode_sum s y2) EQ) as [EQ_x EQ_y].
  split; eapply state_encode_sum_inj; assumption.
Qed.

Definition square_state_extend (s : square_state) (fresh : st_carrier s -> A)
  (fresh_cong : forall x : st_carrier s, forall y : st_carrier s, @eqProp (st_carrier s) (st_isSetoid s) x y -> fresh x = fresh y)
  (fresh_inj : forall x : st_carrier s, forall y : st_carrier s, fresh x = fresh y -> @eqProp (st_carrier s) (st_isSetoid s) x y)
  (fresh_out : forall x : st_carrier s, forall y : st_carrier s, ~ fresh x = st_emb s y)
  : square_state.
Proof.
  pose (B := st_carrier s).
  pose (B_isSetoid := st_isSetoid s).
  refine (
    {|
      st_carrier := B + B;
      st_isSetoid := @sum_isSetoid B B B_isSetoid B_isSetoid;
      st_emb := fun x : B + B => match x with inl b => st_emb s b | inr b => fresh b end;
      st_emb_cong := _;
      st_emb_inj := _;
      st_nat := fun n : nat => inl (st_nat s n);
      st_nat_emb := _;
      st_code := fun xy : (B + B) * (B + B) => match Datatypes.fst xy, Datatypes.snd xy with inl x, inl y => inl (st_code s (x, y)) | _, _ => inr (state_encode_pair s xy) end;
      st_code_cong := _;
      st_code_inj := _;
    |}
  ).
  - intros [x | x] [y | y] EQ; inv EQ; simpl.
    + eapply st_emb_cong. exact x_corres.
    + eapply fresh_cong. exact y_corres.
  - intros [x | x] [y | y] EQ; simpl in EQ.
    + econs. eapply st_emb_inj. exact EQ.
    + exfalso. exact (fresh_out y x (eq_sym EQ)).
    + exfalso. exact (fresh_out x y EQ).
    + econs. eapply fresh_inj. exact EQ.
  - intros n. eapply st_nat_emb.
  - intros [x1 | x1] [x2 | x2] [y1 | y1] [y2 | y2] EQ_x EQ_y; inv EQ_x; inv EQ_y; simpl.
    + econs. eapply st_code_cong; eauto.
    + econs. eapply state_encode_pair_cong. split; econs; eauto.
    + econs. eapply state_encode_pair_cong. split; econs; eauto.
    + econs. eapply state_encode_pair_cong. split; econs; eauto.
  - intros [x1 | x1] [x2 | x2] [y1 | y1] [y2 | y2] EQ; simpl in EQ; inv EQ.
    + pose proof (st_code_inj s x1 x2 y1 y2 x_corres) as [EQ_x EQ_y]. split; econs; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
    + pose proof (state_encode_pair_inj s _ _ y_corres) as [EQ_x EQ_y]. split; assumption.
Defined.

Lemma square_state_extend_exists (s : square_state) (fresh : st_carrier s -> A)
  (fresh_cong : forall x : st_carrier s, forall y : st_carrier s, @eqProp (st_carrier s) (st_isSetoid s) x y -> fresh x = fresh y)
  (fresh_inj : forall x : st_carrier s, forall y : st_carrier s, fresh x = fresh y -> @eqProp (st_carrier s) (st_isSetoid s) x y)
  (fresh_out : forall x : st_carrier s, forall y : st_carrier s, ~ fresh x = st_emb s y)
  : exists t : square_state, state_le s t.
Proof.
  exists (square_state_extend s fresh fresh_cong fresh_inj fresh_out).
  unfold state_le. cbn. eexists; [change (state_embedding s (square_state_extend s fresh fresh_cong fresh_inj fresh_out)) | exact I].
  unshelve refine (
    {|
      st_lift := fun x : st_carrier s => (inl x : st_carrier (square_state_extend s fresh fresh_cong fresh_inj fresh_out));
      st_lift_cong := _;
      st_lift_emb := _;
      st_lift_code := _;
    |}
  ).
  - intros x y H. econs. exact H.
  - intros x. reflexivity.
  - intros x y. reflexivity.
Qed.

End SQUARE_ABSORPTION.

Section GRAPH_SQUARE_ABSORPTION.

#[local] Infix "\in" := E.In : type_scope.

Variable A : Type@{Set_u}.

Variable nat_embed : nat -> A.

Hypothesis nat_embed_inj : forall n : nat, forall m : nat, nat_embed n = nat_embed m -> n = m.

Record graph_state : Type@{Set_u} :=
  mk_graph_state
  { gs_carrier : A -> Prop
  ; gs_nat : forall n : nat, gs_carrier (nat_embed n)
  ; gs_code : A -> A -> A -> Prop
  ; gs_code_dom : forall x : A, forall y : A, forall z : A, gs_code x y z -> gs_carrier x /\ gs_carrier y /\ gs_carrier z
  ; gs_code_total : forall x : A, forall y : A, gs_carrier x -> gs_carrier y -> exists z : A, gs_code x y z
  ; gs_code_functional : forall x : A, forall y : A, forall z1 : A, forall z2 : A, gs_code x y z1 -> gs_code x y z2 -> z1 = z2
  ; gs_code_inj : forall x1 : A, forall y1 : A, forall z1 : A, forall x2 : A, forall y2 : A, forall z2 : A, gs_code x1 y1 z1 -> gs_code x2 y2 z2 -> z1 = z2 -> x1 = x2 /\ y1 = y2
  }.

Definition graph_state_le (s : graph_state) (t : graph_state) : Prop :=
  (forall a : A, gs_carrier s a -> gs_carrier t a) /\ (forall x : A, forall y : A, forall z : A, gs_code s x y z -> gs_code t x y z).

#[local]
Instance graph_state_le_PreOrder
  : PreOrder graph_state_le.
Proof.
  split.
  - intros s. split; eauto.
  - intros s t u LE_st LE_tu. split.
    + intros a Ha. exact (proj1 LE_tu a (proj1 LE_st a Ha)).
    + intros x y z Hcode. exact (proj2 LE_tu x y z (proj2 LE_st x y z Hcode)).
Qed.

#[local]
Instance graph_state_isProset : isProset graph_state :=
  { leProp := graph_state_le
  ; Proset_isSetoid := mkSetoidFromPreOrder graph_state_le_PreOrder
  ; leProp_PreOrder := graph_state_le_PreOrder
  ; leProp_PartialOrder := mkSetoidFromPreOrder_good graph_state_le_PreOrder
  }.

Definition graph_state_initial_code (x : A) (y : A) (z : A) : Prop :=
  exists n : nat, exists m : nat, x = nat_embed n /\ y = nat_embed m /\ z = nat_embed (cpInv n m).

Definition graph_state_initial
  : graph_state.
Proof.
  refine (
    {|
      gs_carrier := fun a : A => exists n : nat, a = nat_embed n;
      gs_nat := _;
      gs_code := graph_state_initial_code;
      gs_code_dom := _;
      gs_code_total := _;
      gs_code_functional := _;
      gs_code_inj := _;
    |}
  ).
  - intros n. exists n. reflexivity.
  - intros x y z (n & m & Hx & Hy & Hz). subst. splits; eauto.
  - intros x y (n & Hx) (m & Hy). subst. exists (nat_embed (cpInv n m)). exists n, m. splits; reflexivity.
  - intros x y z1 z2 (n1 & m1 & Hx1 & Hy1 & Hz1) (n2 & m2 & Hx2 & Hy2 & Hz2). subst.
    assert (n1 = n2) by now eapply nat_embed_inj.
    assert (m1 = m2) by now eapply nat_embed_inj.
    now subst n2 m2.
  - intros x1 y1 z1 x2 y2 z2 (n1 & m1 & Hx1 & Hy1 & Hz1) (n2 & m2 & Hx2 & Hy2 & Hz2) Hz. subst.
    pose proof (nat_embed_inj _ _ Hz) as Hpair. pose proof (cpInv_inj _ _ _ _ Hpair) as [Hn Hm]. subst n2 m2. split; reflexivity.
Defined.

Definition graph_state_chain_upperbound (C : ensemble graph_state)
  (NONEMPTY : exists s : graph_state, s \in C)
  (CHAIN : forall s1 : graph_state, forall s2 : graph_state, s1 \in C -> s2 \in C -> graph_state_le s1 s2 \/ graph_state_le s2 s1)
  : exists u : graph_state, forall s : graph_state, s \in C -> graph_state_le s u.
Proof.
  destruct NONEMPTY as [s0 IN0]. unshelve eexists.
  { refine (
      {|
        gs_carrier := fun a : A => exists s : graph_state, s \in C /\ gs_carrier s a;
        gs_nat := _;
        gs_code := fun x : A => fun y : A => fun z : A => exists s : graph_state, s \in C /\ gs_code s x y z;
        gs_code_dom := _;
        gs_code_total := _;
        gs_code_functional := _;
        gs_code_inj := _;
      |}
    ).
    - intros n. exists s0. split; [exact IN0 | exact (gs_nat s0 n)].
    - intros x y z (s & INs & Hcode). pose proof (gs_code_dom s x y z Hcode) as (Hx & Hy & Hz). splits; exists s; split; assumption.
    - intros x y (sx & INx & Hx) (sy & INy & Hy). pose proof (CHAIN sx sy INx INy) as [LE | LE].
      + pose proof (gs_code_total sy x y (proj1 LE x Hx) Hy) as [z Hcode]. exists z. exists sy. split; assumption.
      + pose proof (gs_code_total sx x y Hx (proj1 LE y Hy)) as [z Hcode]. exists z. exists sx. split; assumption.
    - intros x y z1 z2 (s1 & IN1 & Hcode1) (s2 & IN2 & Hcode2). pose proof (CHAIN s1 s2 IN1 IN2) as [LE | LE].
      + eapply gs_code_functional; [exact (proj2 LE x y z1 Hcode1) | exact Hcode2].
      + eapply gs_code_functional; [exact Hcode1 | exact (proj2 LE x y z2 Hcode2)].
    - intros x1 y1 z1 x2 y2 z2 (s1 & IN1 & Hcode1) (s2 & IN2 & Hcode2) Hz. pose proof (CHAIN s1 s2 IN1 IN2) as [LE | LE].
      + eapply gs_code_inj; [exact (proj2 LE x1 y1 z1 Hcode1) | exact Hcode2 | exact Hz].
      + eapply gs_code_inj; [exact Hcode1 | exact (proj2 LE x2 y2 z2 Hcode2) | exact Hz].
  }
  intros s INs. split.
  - intros a Ha. exists s. split; assumption.
  - intros x y z Hcode. exists s. split; assumption.
Defined.

Lemma graph_state_maximal_exists
  : exists m : graph_state, forall t : graph_state, graph_state_le m t -> graph_state_le t m.
Proof.
  eapply Zorn's_lemma with (D := graph_state) (PROSET := graph_state_isProset).
  - econs. exact graph_state_initial.
  - intros C NONEMPTY CHAIN. eapply graph_state_chain_upperbound; eauto.
Qed.

Definition graph_state_type (s : graph_state) : Type@{Set_u} :=
  { a : A | gs_carrier s a }.

Definition graph_state_nat (s : graph_state) (n : nat) : graph_state_type s :=
  @exist A (gs_carrier s) (nat_embed n) (gs_nat s n).

Lemma graph_state_nat_inj (s : graph_state) (n : nat) (m : nat)
  (EQ : graph_state_nat s n = graph_state_nat s m)
  : n = m.
Proof.
  eapply nat_embed_inj. injection EQ as EQ_proj. exact EQ_proj.
Qed.

Definition graph_sum_type (s : graph_state) : Type@{Set_u} :=
  (graph_state_type s + graph_state_type s)%type.

Definition graph_pair_type (s : graph_state) : Type@{Set_u} :=
  (graph_sum_type s * graph_sum_type s)%type.

Inductive graph_sum_code (s : graph_state) : graph_sum_type s -> graph_state_type s -> Prop :=
  | graph_sum_code_l (x : graph_state_type s) (b : graph_state_type s)
    (CODE : gs_code s (nat_embed O) (proj1_sig x) (proj1_sig b))
    : graph_sum_code s (inl x) b
  | graph_sum_code_r (x : graph_state_type s) (b : graph_state_type s)
    (CODE : gs_code s (nat_embed (S O)) (proj1_sig x) (proj1_sig b))
    : graph_sum_code s (inr x) b.

Lemma graph_sum_code_total (s : graph_state) (x : graph_sum_type s)
  : exists b : graph_state_type s, graph_sum_code s x b.
Proof.
  destruct x as [x | x].
  - pose proof (gs_code_total s (nat_embed O) (proj1_sig x) (gs_nat s O) (proj2_sig x)) as [b Hcode].
    pose proof (gs_code_dom s _ _ _ Hcode) as (_ & _ & Hb). exists (@exist A (gs_carrier s) b Hb). econs. exact Hcode.
  - pose proof (gs_code_total s (nat_embed (S O)) (proj1_sig x) (gs_nat s (S O)) (proj2_sig x)) as [b Hcode].
    pose proof (gs_code_dom s _ _ _ Hcode) as (_ & _ & Hb). exists (@exist A (gs_carrier s) b Hb). econs. exact Hcode.
Qed.

Lemma graph_sum_code_functional (s : graph_state) (x : graph_sum_type s) (b1 : graph_state_type s) (b2 : graph_state_type s)
  (CODE1 : graph_sum_code s x b1)
  (CODE2 : graph_sum_code s x b2)
  : b1 = b2.
Proof.
  destruct x as [x | x]; inv CODE1; inv CODE2; eapply Cardinal2.sig_eq_from_proj1; eapply gs_code_functional; eauto.
Qed.

Lemma graph_sum_code_inj (s : graph_state) (x1 : graph_sum_type s) (x2 : graph_sum_type s) (b1 : graph_state_type s) (b2 : graph_state_type s)
  (CODE1 : graph_sum_code s x1 b1)
  (CODE2 : graph_sum_code s x2 b2)
  (EQ : b1 = b2)
  : x1 = x2.
Proof.
  subst b2.
  destruct x1 as [x1 | x1], x2 as [x2 | x2]; inv CODE1; inv CODE2.
  - pose proof (gs_code_inj s _ _ _ _ _ _ CODE CODE0 eq_refl) as [_ EQ_x]. f_equal. eapply Cardinal2.sig_eq_from_proj1. exact EQ_x.
  - pose proof (gs_code_inj s _ _ _ _ _ _ CODE CODE0 eq_refl) as [EQ_tag _].
    pose proof (nat_embed_inj O (S O) EQ_tag) as BAD. discriminate BAD.
  - pose proof (gs_code_inj s _ _ _ _ _ _ CODE CODE0 eq_refl) as [EQ_tag _].
    pose proof (nat_embed_inj (S O) O EQ_tag) as BAD. discriminate BAD.
  - pose proof (gs_code_inj s _ _ _ _ _ _ CODE CODE0 eq_refl) as [_ EQ_x]. f_equal. eapply Cardinal2.sig_eq_from_proj1. exact EQ_x.
Qed.

Inductive graph_pair_code (s : graph_state) : graph_pair_type s -> graph_state_type s -> Prop :=
  | graph_pair_code_intro (x : graph_sum_type s) (y : graph_sum_type s) (bx : graph_state_type s) (by0 : graph_state_type s) (b : graph_state_type s)
    (CODE_x : graph_sum_code s x bx)
    (CODE_y : graph_sum_code s y by0)
    (CODE : gs_code s (proj1_sig bx) (proj1_sig by0) (proj1_sig b))
    : graph_pair_code s (x, y) b.

Lemma graph_pair_code_total (s : graph_state) (p : graph_pair_type s)
  : exists b : graph_state_type s, graph_pair_code s p b.
Proof.
  destruct p as [x y]. pose proof (graph_sum_code_total s x) as [bx CODE_x]. pose proof (graph_sum_code_total s y) as [by0 CODE_y].
  pose proof (gs_code_total s (proj1_sig bx) (proj1_sig by0) (proj2_sig bx) (proj2_sig by0)) as [b CODE].
  pose proof (gs_code_dom s _ _ _ CODE) as (_ & _ & Hb). exists (@exist A (gs_carrier s) b Hb). econs; eauto.
Qed.

Lemma graph_pair_code_functional (s : graph_state) (p : graph_pair_type s) (b1 : graph_state_type s) (b2 : graph_state_type s)
  (CODE1 : graph_pair_code s p b1)
  (CODE2 : graph_pair_code s p b2)
  : b1 = b2.
Proof.
  inv CODE1. inv CODE2. pose proof (graph_sum_code_functional s _ _ _ CODE_x CODE_x0). subst bx0.
  pose proof (graph_sum_code_functional s _ _ _ CODE_y CODE_y0). subst by0.
  eapply Cardinal2.sig_eq_from_proj1. eapply gs_code_functional; eauto.
Qed.

Lemma graph_pair_code_inj (s : graph_state) (p1 : graph_pair_type s) (p2 : graph_pair_type s) (b1 : graph_state_type s) (b2 : graph_state_type s)
  (CODE1 : graph_pair_code s p1 b1)
  (CODE2 : graph_pair_code s p2 b2)
  (EQ : b1 = b2)
  : p1 = p2.
Proof.
  subst b2. inv CODE1. inv CODE2.
  pose proof (gs_code_inj s _ _ _ _ _ _ CODE CODE0 eq_refl) as [EQ_bx EQ_by].
  pose proof (graph_sum_code_inj s _ _ _ _ CODE_x CODE_x0 (Cardinal2.sig_eq_from_proj1 _ _ EQ_bx)) as EQ_x.
  pose proof (graph_sum_code_inj s _ _ _ _ CODE_y CODE_y0 (Cardinal2.sig_eq_from_proj1 _ _ EQ_by)) as EQ_y.
  subst. reflexivity.
Qed.

Definition graph_state_complement_type (s : graph_state) : Type@{Set_u} :=
  { a : A | ~ gs_carrier s a }.

Inductive graph_extend_repr (s : graph_state) (fresh : graph_state_type s -> graph_state_complement_type s) : A -> graph_sum_type s -> Prop :=
  | graph_extend_repr_old (b : graph_state_type s)
    : graph_extend_repr s fresh (proj1_sig b) (inl b)
  | graph_extend_repr_new (b : graph_state_type s)
    : graph_extend_repr s fresh (proj1_sig (fresh b)) (inr b).

Definition graph_extend_nonold (s : graph_state) (p : graph_pair_type s) : Prop :=
  match p with
  | (inl _, inl _) => False
  | _ => True
  end.

Lemma graph_extend_repr_unique (s : graph_state) (fresh : graph_state_type s -> graph_state_complement_type s) (a : A) (x : graph_sum_type s) (y : graph_sum_type s)
  (fresh_inj : forall b1 : graph_state_type s, forall b2 : graph_state_type s, proj1_sig (fresh b1) = proj1_sig (fresh b2) -> b1 = b2)
  (REPR_x : graph_extend_repr s fresh a x)
  (REPR_y : graph_extend_repr s fresh a y)
  : x = y.
Proof.
  inv REPR_x; inv REPR_y.
  - f_equal. eapply Cardinal2.sig_eq_from_proj1. symmetry. exact H0.
  - destruct b as [a Ha]. simpl in H0. subst a. contradiction (proj2_sig (fresh b0)).
  - destruct b0 as [a Ha]. simpl in H0. subst a. contradiction (proj2_sig (fresh b)).
  - f_equal. eapply fresh_inj. symmetry. exact H0.
Qed.

Lemma graph_extend_repr_same (s : graph_state) (fresh : graph_state_type s -> graph_state_complement_type s)
  (a : A) (b : A) (x : graph_sum_type s)
  (REPR_a : graph_extend_repr s fresh a x)
  (REPR_b : graph_extend_repr s fresh b x)
  : a = b.
Proof.
  inv REPR_a; inv REPR_b; reflexivity.
Qed.

Inductive graph_extend_code (s : graph_state) (fresh : graph_state_type s -> graph_state_complement_type s) : A -> A -> A -> Prop :=
  | graph_extend_code_old (x : A) (y : A) (z : A)
    (CODE : gs_code s x y z)
    : graph_extend_code s fresh x y z
  | graph_extend_code_new (x : A) (y : A) (z : A) (sx : graph_sum_type s) (sy : graph_sum_type s) (b : graph_state_type s)
    (REPR_x : graph_extend_repr s fresh x sx)
    (REPR_y : graph_extend_repr s fresh y sy)
    (NONOLD : graph_extend_nonold s (sx, sy))
    (CODE : graph_pair_code s (sx, sy) b)
    (EQ_z : z = proj1_sig (fresh b))
    : graph_extend_code s fresh x y z.

Lemma graph_extend_repr_of_carrier (s : graph_state) (fresh : graph_state_type s -> graph_state_complement_type s) (a : A)
  (Ha : exists x : graph_sum_type s, graph_extend_repr s fresh a x)
  : gs_carrier s a \/ exists b : graph_state_type s, a = proj1_sig (fresh b).
Proof.
  destruct Ha as [x Hx]. inv Hx.
  - left. exact (proj2_sig b).
  - right. exists b. reflexivity.
Qed.

Definition graph_state_extend (s : graph_state) (fresh : graph_state_type s -> graph_state_complement_type s)
  (fresh_inj : forall b1 : graph_state_type s, forall b2 : graph_state_type s, proj1_sig (fresh b1) = proj1_sig (fresh b2) -> b1 = b2)
  : graph_state.
Proof.
  refine (
    {|
      gs_carrier := fun a : A => exists x : graph_sum_type s, graph_extend_repr s fresh a x;
      gs_nat := _;
      gs_code := graph_extend_code s fresh;
      gs_code_dom := _;
      gs_code_total := _;
      gs_code_functional := _;
      gs_code_inj := _;
    |}
  ).
  - intros n. exists (inl (graph_state_nat s n)).
    change (graph_extend_repr s fresh (proj1_sig (graph_state_nat s n)) (inl (graph_state_nat s n))). eapply graph_extend_repr_old.
  - intros x y z Hcode. inv Hcode.
    + pose proof (gs_code_dom s x y z CODE) as (Hx & Hy & Hz). splits.
      * exists (inl (@exist A (gs_carrier s) x Hx)). change (graph_extend_repr s fresh (proj1_sig (@exist A (gs_carrier s) x Hx)) (inl (@exist A (gs_carrier s) x Hx))). eapply graph_extend_repr_old.
      * exists (inl (@exist A (gs_carrier s) y Hy)). change (graph_extend_repr s fresh (proj1_sig (@exist A (gs_carrier s) y Hy)) (inl (@exist A (gs_carrier s) y Hy))). eapply graph_extend_repr_old.
      * exists (inl (@exist A (gs_carrier s) z Hz)). change (graph_extend_repr s fresh (proj1_sig (@exist A (gs_carrier s) z Hz)) (inl (@exist A (gs_carrier s) z Hz))). eapply graph_extend_repr_old.
    + splits; [exists sx | exists sy | exists (inr b)]; eauto using graph_extend_repr_new.
  - intros x y [sx REPR_x] [sy REPR_y]. destruct sx as [bx | bx], sy as [by0 | by0].
    + pose proof (gs_code_total s x y) as [z CODE].
      { inv REPR_x. exact (proj2_sig bx). }
      { inv REPR_y. exact (proj2_sig by0). }
      exists z. econs. exact CODE.
    + pose proof (graph_pair_code_total s (inl bx, inr by0)) as [b CODE]. exists (proj1_sig (fresh b)).
      eapply graph_extend_code_new with (sx := inl bx) (sy := inr by0) (b := b); eauto.
      simpl. exact I.
    + pose proof (graph_pair_code_total s (inr bx, inl by0)) as [b CODE]. exists (proj1_sig (fresh b)).
      eapply graph_extend_code_new with (sx := inr bx) (sy := inl by0) (b := b); eauto.
      simpl. exact I.
    + pose proof (graph_pair_code_total s (inr bx, inr by0)) as [b CODE]. exists (proj1_sig (fresh b)).
      eapply graph_extend_code_new with (sx := inr bx) (sy := inr by0) (b := b); eauto.
      simpl. exact I.
  - intros x y z1 z2 CODE1 CODE2. inv CODE1; inv CODE2.
    + eapply gs_code_functional; eauto.
    + pose proof (gs_code_dom s x y z1 CODE) as (Hx & Hy & _).
      pose proof (graph_extend_repr_unique s fresh x sx (inl (@exist A (gs_carrier s) x Hx)) fresh_inj REPR_x (graph_extend_repr_old s fresh (@exist A (gs_carrier s) x Hx))) as EQ_x.
      pose proof (graph_extend_repr_unique s fresh y sy (inl (@exist A (gs_carrier s) y Hy)) fresh_inj REPR_y (graph_extend_repr_old s fresh (@exist A (gs_carrier s) y Hy))) as EQ_y.
      subst sx sy. contradiction.
    + pose proof (gs_code_dom s x y z2 CODE0) as (Hx & Hy & _).
      pose proof (graph_extend_repr_unique s fresh x sx (inl (@exist A (gs_carrier s) x Hx)) fresh_inj REPR_x (graph_extend_repr_old s fresh (@exist A (gs_carrier s) x Hx))) as EQ_x.
      pose proof (graph_extend_repr_unique s fresh y sy (inl (@exist A (gs_carrier s) y Hy)) fresh_inj REPR_y (graph_extend_repr_old s fresh (@exist A (gs_carrier s) y Hy))) as EQ_y.
      subst sx sy. contradiction.
    + pose proof (graph_extend_repr_unique s fresh x sx sx0 fresh_inj REPR_x REPR_x0) as EQ_x.
      pose proof (graph_extend_repr_unique s fresh y sy sy0 fresh_inj REPR_y REPR_y0) as EQ_y.
      subst sx0 sy0. pose proof (graph_pair_code_functional s _ _ _ CODE CODE0) as EQ_b. subst b0. reflexivity.
  - intros x1 y1 z1 x2 y2 z2 CODE1 CODE2 EQ_z. inv CODE1; inv CODE2.
    + eapply gs_code_inj; eauto.
    + pose proof (gs_code_dom s _ _ _ CODE) as (_ & _ & Hz_old).
      destruct (fresh b) as [fb Hfb]. simpl in *. subst. contradiction.
    + pose proof (gs_code_dom s _ _ _ CODE0) as (_ & _ & Hz_old).
      destruct (fresh b) as [fb Hfb]. simpl in *. subst. contradiction.
    + pose proof (fresh_inj b b0 EQ_z) as EQ_b. subst b0.
      pose proof (graph_pair_code_inj s _ _ _ _ CODE CODE0 eq_refl) as EQ_pair. inv EQ_pair.
      split; eapply graph_extend_repr_same; eauto.
Defined.

Lemma graph_state_extend_le (s : graph_state) (fresh : graph_state_type s -> graph_state_complement_type s)
  (fresh_inj : forall b1 : graph_state_type s, forall b2 : graph_state_type s, proj1_sig (fresh b1) = proj1_sig (fresh b2) -> b1 = b2)
  : graph_state_le s (graph_state_extend s fresh fresh_inj).
Proof.
  split.
  - intros a Ha. exists (inl (@exist A (gs_carrier s) a Ha)).
    change (graph_extend_repr s fresh (proj1_sig (@exist A (gs_carrier s) a Ha)) (inl (@exist A (gs_carrier s) a Ha))). eapply graph_extend_repr_old.
  - intros x y z Hcode. econs. exact Hcode.
Qed.

Lemma graph_state_type_nat_le (s : graph_state)
  : Cardinality.ofType nat =< Cardinality.ofType (graph_state_type s).
Proof.
  eapply Cardinal2.Cardinality_ofType_le_ofType with (f := graph_state_nat s).
  intros n m EQ. eapply graph_state_nat_inj. exact EQ.
Qed.

Lemma graph_state_type_prod_le (s : graph_state)
  : Cardinality.ofType (graph_state_type s * graph_state_type s) =< Cardinality.ofType (graph_state_type s).
Proof.
  assert (Hchoice : forall p : graph_state_type s * graph_state_type s, exists b : graph_state_type s, gs_code s (proj1_sig (Datatypes.fst p)) (proj1_sig (Datatypes.snd p)) (proj1_sig b)).
  { intros [x y]. pose proof (gs_code_total s (proj1_sig x) (proj1_sig y) (proj2_sig x) (proj2_sig y)) as [z CODE].
    pose proof (gs_code_dom s _ _ _ CODE) as (_ & _ & Hz). exists (@exist A (gs_carrier s) z Hz). exact CODE.
  }
  pose proof (Axiom_of_Choice (graph_state_type s * graph_state_type s) (fun _ : graph_state_type s * graph_state_type s => graph_state_type s) (fun p : graph_state_type s * graph_state_type s => fun b : graph_state_type s => gs_code s (proj1_sig (Datatypes.fst p)) (proj1_sig (Datatypes.snd p)) (proj1_sig b)) Hchoice) as [code CODE].
  eapply Cardinal2.Cardinality_ofType_le_ofType with (f := code).
  intros [x1 y1] [x2 y2] EQ. change (code (x1, y1) = code (x2, y2)) in EQ.
  assert (EQ_proj : proj1_sig (code (x1, y1)) = proj1_sig (code (x2, y2))) by now rewrite EQ.
  pose proof (gs_code_inj s _ _ _ _ _ _ (CODE (x1, y1)) (CODE (x2, y2)) EQ_proj) as [EQ_x EQ_y].
  f_equal; eapply Cardinal2.sig_eq_from_proj1; assumption.
Qed.

Definition graph_cover_sum_type (s : graph_state) : Type@{Set_u} :=
  (graph_state_type s + graph_state_complement_type s)%type.

Definition graph_sum_proj (s : graph_state) (x : graph_cover_sum_type s) : A :=
  match x with
  | inl b => proj1_sig b
  | inr c => proj1_sig c
  end.

Lemma graph_state_cover_le_sum (s : graph_state)
  : Cardinality.ofType A =< Cardinality.ofType (graph_cover_sum_type s).
Proof.
  assert (Hchoice : forall a : A, exists x : graph_cover_sum_type s, graph_sum_proj s x = a).
  { intros a. pose proof (classic (gs_carrier s a)) as [Ha | Ha].
    - exists (inl (@exist A (gs_carrier s) a Ha)). reflexivity.
    - exists (inr (@exist A (fun x : A => ~ gs_carrier s x) a Ha)). reflexivity.
  }
  pose proof (Axiom_of_Choice A (fun _ : A => graph_cover_sum_type s) (fun a : A => fun x : graph_cover_sum_type s => graph_sum_proj s x = a) Hchoice) as [pick PICK].
  eapply Cardinal2.Cardinality_ofType_le_ofType with (f := pick).
  intros a1 a2 EQ. change (pick a1 = pick a2) in EQ. rewrite <- (PICK a1). rewrite <- (PICK a2). now rewrite EQ.
Qed.

Lemma graph_state_complement_le_carrier (m : graph_state)
  (MAX : forall t : graph_state, graph_state_le m t -> graph_state_le t m)
  : Cardinality.ofType (graph_state_complement_type m) =< Cardinality.ofType (graph_state_type m).
Proof.
  pose proof (Cardinal1.Cardinality_le_total (Cardinality.ofType (graph_state_type m)) (Cardinality.ofType (graph_state_complement_type m))) as [LE | LE].
  - destruct LE as [fresh fresh_cong fresh_inj].
    assert (fresh_inj_proj : forall b1 : graph_state_type m, forall b2 : graph_state_type m, proj1_sig (fresh b1) = proj1_sig (fresh b2) -> b1 = b2).
    { intros b1 b2 EQ. eapply fresh_inj. change (fresh b1 = fresh b2). eapply Cardinal2.sig_eq_from_proj1. exact EQ. }
    pose proof (MAX (graph_state_extend m fresh fresh_inj_proj) (graph_state_extend_le m fresh fresh_inj_proj)) as BACK.
    pose (b0 := graph_state_nat m O).
    pose proof (proj1 BACK (proj1_sig (fresh b0))) as IN_BACK.
    assert (IN_EXT : gs_carrier (graph_state_extend m fresh fresh_inj_proj) (proj1_sig (fresh b0))).
    { exists (inr b0). econs. }
    specialize (IN_BACK IN_EXT). exact (False_rect _ (proj2_sig (fresh b0) IN_BACK)).
  - exact LE.
Qed.

End GRAPH_SQUARE_ABSORPTION.

Theorem Cardinality_ofType_prod_self_le_of_nat_le (A : Type@{Set_u})
  (NAT_LE : Cardinality.ofType nat =< Cardinality.ofType A)
  : Cardinality.ofType (A * A) =< Cardinality.ofType A.
Proof.
  destruct NAT_LE as [nat_emb nat_emb_cong nat_emb_inj].
  assert (nat_emb_inj_raw : forall n : nat, forall m : nat, nat_emb n = nat_emb m -> n = m).
  { intros n m EQ. eapply nat_emb_inj. change (nat_emb n = nat_emb m). exact EQ. }
  pose proof (@graph_state_maximal_exists A nat_emb nat_emb_inj_raw) as [m MAX].
  pose proof (@graph_state_type_nat_le A nat_emb nat_emb_inj_raw m) as NAT_LE_B.
  pose proof (@graph_state_type_prod_le A nat_emb m) as PROD_B_LE_B.
  pose proof (@graph_state_complement_le_carrier A nat_emb nat_emb_inj_raw m MAX) as COMP_LE_B.
  assert (B_LE_A : Cardinality.ofType (graph_state_type A nat_emb m) =< Cardinality.ofType A).
  { eapply Cardinal2.Cardinality_ofType_sig_le. }
  assert (A_LE_B : Cardinality.ofType A =< Cardinality.ofType (graph_state_type A nat_emb m)).
  { transitivity (Cardinality.ofType (graph_cover_sum_type A nat_emb m)).
    - eapply graph_state_cover_le_sum.
    - transitivity (Cardinality.mul (Cardinality.ofType bool) (Cardinality.ofType (graph_state_type A nat_emb m))).
      + eapply Cardinal2.Cardinality_ofType_sum_le.
        * reflexivity.
        * exact COMP_LE_B.
      + transitivity (Cardinality.ofType (graph_state_type A nat_emb m * graph_state_type A nat_emb m)).
        * pose proof (Cardinal2.Cardinality_ofType_prod_eq bool (graph_state_type A nat_emb m)) as PROD_EQ. rewrite <- PROD_EQ.
          eapply Cardinal2.Cardinality_ofType_prod_le.
          { eapply Cardinality_ofType_bool_le_of_nat_le. exact NAT_LE_B. }
          { reflexivity. }
        * exact PROD_B_LE_B.
  }
  transitivity (Cardinality.ofType (graph_state_type A nat_emb m * graph_state_type A nat_emb m)).
  - eapply Cardinal2.Cardinality_ofType_prod_le; exact A_LE_B.
  - transitivity (Cardinality.ofType (graph_state_type A nat_emb m)); [exact PROD_B_LE_B | exact B_LE_A].
Qed.

Theorem Cardinality_ofType_rose_lt_of_lt_uncountable (A : Type@{Set_u}) (kappa : Cardinality.t)
  (LT : Cardinality.ofType A ≨ kappa)
  (UNCOUNTABLE : ~ kappa =< Cardinality.ofType nat)
  : Cardinality.ofType (B.rose A) ≨ kappa.
Proof.
  eapply Cardinality_ofType_rose_lt_of_lt_uncountable_square_le; eauto.
  intros B NAT_LE. eapply Cardinality_ofType_prod_self_le_of_nat_le. exact NAT_LE.
Qed.

End CARDINALITY.

End Cardinal3.

Module Inaccessible.

Section CLASSICAL.

#[local] Existing Instance Ord_isProset.

Record inaccessible (X : Type@{Set_u}) (base : Ord.t) (next : Ord.t -> Ord.t) (k : Ord.t) : Prop :=
  mk_inaccessible
  { inaccessible_base : base <ᵣ k
  ; inaccessible_next : forall alpha : Ord.t, alpha <ᵣ k -> next alpha <ᵣ k
  ; inaccessible_join : forall os : X -> Ord.t, (forall x : X, os x <ᵣ k) -> Ord.sup X os <ᵣ k
  ; inaccessible_union : forall alpha : Ord.t, forall beta : Ord.t, alpha <ᵣ k -> beta <ᵣ k -> Ord_join alpha beta <ᵣ k
  }.

Record ginaccessible (X : Type@{Set_u}) (base : Ord.t) (next : Ord.t -> Ord.t) (k : Ord.t) : Prop :=
  mk_ginaccessible
  { ginaccessible_base : base <ᵣ k
  ; ginaccessible_next : forall alpha : Ord.t, alpha <ᵣ k -> next alpha <ᵣ k
  ; ginaccessible_join : forall P : X -> Prop, forall os : @sig X P -> Ord.t, (forall x : @sig X P, os x <ᵣ k) -> Ord.sup (@sig X P) os <ᵣ k
  ; ginaccessible_union : forall alpha : Ord.t, forall beta : Ord.t, alpha <ᵣ k -> beta <ᵣ k -> Ord_join alpha beta <ᵣ k
  }.

Context `{Axms : ClassicalAxioms (b_AC := true) (b_fun_ext := true) (b_prop_ext := true)}.

Lemma inaccessible_mon (X0 : Type@{Set_u}) (X1 : Type@{Set_u}) (base0 : Ord.t) (base1 : Ord.t) (next0 : Ord.t -> Ord.t) (next1 : Ord.t -> Ord.t) (k : Ord.t)
  (H_surj : exists f : X1 -> X0, forall x0 : X0, exists x1 : X1, f x1 = x0)
  (H_base : base0 <ᵣ k)
  (H_next : forall alpha : Ord.t, alpha <ᵣ k -> next0 alpha ≦ᵣ next1 alpha)
  (H_inaccessible : inaccessible X1 base1 next1 k)
  : inaccessible X0 base0 next0 k.
Proof.
  destruct H_surj as [f H_surj]. econs.
  - exact H_base.
  - intros alpha H_rLt. eapply rLe_rLt_rLt.
    + eapply H_next. exact H_rLt.
    + eapply H_inaccessible. exact H_rLt.
  - intros os H_rLt. eapply rLe_rLt_rLt with (y := Ord.sup X1 (fun x1 : X1 => os (f x1))).
    + eapply Ord_sup_rLe_intro. intros x0. pose proof (H_surj x0) as [x1 H_eq]. subst x0.
      change ((fun x1 : X1 => os (f x1)) x1 ≦ᵣ Ord.sup X1 (fun x2 : X1 => os (f x2))). eapply Ord_rLe_sup_intro.
    + eapply H_inaccessible. intros x1. eapply H_rLt.
  - intros alpha beta H_rLt0 H_rLt1. eapply H_inaccessible; assumption.
Qed.

Lemma ginaccessible_inaccessible (X : Type@{Set_u}) (base : Ord.t) (next : Ord.t -> Ord.t) (k : Ord.t)
  (H_inaccessible : ginaccessible X base next k)
  : inaccessible X base next k.
Proof.
  econs.
  - eapply H_inaccessible.
  - eapply H_inaccessible.
  - intros os H_rLt. eapply rLe_rLt_rLt with (y := Ord.sup (@sig X (fun _ : X => True)) (fun x : @sig X (fun _ : X => True) => os (proj1_sig x))).
    + eapply Ord_sup_rLe_intro. intros x.
      change ((fun x : @sig X (fun _ : X => True) => os (proj1_sig x)) (@exist X (fun _ : X => True) x I) ≦ᵣ Ord.sup (@sig X (fun _ : X => True)) (fun x0 : @sig X (fun _ : X => True) => os (proj1_sig x0))).
      eapply Ord_rLe_sup_intro.
    + eapply H_inaccessible. intros x. eapply H_rLt.
  - eapply H_inaccessible.
Qed.

Inductive tree {X : Type@{Set_u}} : Type@{Set_u} :=
  | tree_O : @tree X
  | tree_S : @tree X -> @tree X
  | tree_join : (X -> @tree X) -> @tree X
  | tree_union : @tree X -> @tree X -> @tree X.

#[global] Arguments tree : clear implicits.

Definition tree_lt {X : Type@{Set_u}} (tr0 : tree X) (tr1 : tree X) : Prop :=
  match tr1 with
  | tree_O => False
  | tree_S tr => tr0 = tr
  | tree_join trs => exists x : X, tr0 = trs x
  | tree_union trl trr => tr0 = trl \/ tr0 = trr
  end.

Lemma tree_lt_well_founded (X : Type@{Set_u})
  : well_founded (@tree_lt X).
Proof.
  ii. induction a as [ | tr IH | trs IH | tr0 IH0 tr1 IH1].
  - econs. intros y H_rLt. contradiction.
  - econs. intros y H_rLt. simpl in H_rLt. subst y. exact IH.
  - econs. intros y H_rLt. simpl in H_rLt. destruct H_rLt as [x ->]. exact (IH x).
  - econs. intros y H_rLt. simpl in H_rLt. destruct H_rLt as [-> | ->]; assumption.
Qed.

Definition tree_top (X : Type@{Set_u}) : Ord.t :=
  @fromWfSet (tree X) (@tree_lt X) (tree_lt_well_founded X).

Lemma tree_O_rEq (X : Type@{Set_u})
  : @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tree_O =ᵣ Ord.zer.
Proof.
  rewrite rEq_iff. split.
  - eapply fromWf_isSupremum. intros y H_rLt. contradiction H_rLt.
  - eapply Ord_zer_rLe.
Qed.

Lemma tree_S_rEq (X : Type@{Set_u}) (tr : tree X)
  : @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_S tr) =ᵣ Ord.suc (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr).
Proof.
  rewrite rEq_iff. split.
  - eapply fromWf_isSupremum. intros y H_rLt. simpl in H_rLt. subst y. unfold Ord.suc. eapply rLt_succ_intro.
  - unfold Ord.suc. rewrite succ_rLe_iff. eapply member_implies_rLt. rewrite fromWf_unfold.
    exists tr. split; [reflexivity | reflexivity].
Qed.

Lemma tree_join_rEq (X : Type@{Set_u}) (trs : X -> tree X)
  : @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_join trs) =ᵣ mkNode X (fun x : X => @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (trs x)).
Proof.
  rewrite rEq_iff. split.
  - eapply fromWf_isSupremum. intros y H_rLt. simpl in H_rLt. destruct H_rLt as [x ->].
    eapply member_implies_rLt. exists x. reflexivity.
  - econs. intros x. eapply member_implies_rLt. rewrite fromWf_unfold.
    exists (trs x). split; [now exists x | reflexivity].
Qed.

Lemma tree_union_le (X : Type@{Set_u}) (tr0 : tree X) (tr1 : tree X)
  : @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_union tr0 tr1) ≦ᵣ Ord.suc (Ord_join (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0) (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1)).
Proof.
  eapply fromWf_isSupremum. intros y H_rLt. simpl in H_rLt. unfold Ord.suc. rewrite rLt_succ_iff. destruct H_rLt as [-> | ->].
  - eapply Ord_join_l.
  - eapply Ord_join_r.
Qed.

Lemma tree_union_le_rev (X : Type@{Set_u}) (tr0 : tree X) (tr1 : tree X)
  : Ord_join (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0) (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1) ≦ᵣ @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_union tr0 tr1).
Proof.
  eapply Ord_join_spec; eapply rLt_implies_rLe; eapply member_implies_rLt; rewrite fromWf_unfold.
  - exists tr0. now split; [left | reflexivity].
  - exists tr1. now split; [right | reflexivity].
Qed.

Lemma tree_top_O (X : Type@{Set_u})
  : Ord.zer <ᵣ tree_top X.
Proof.
  eapply rLe_rLt_rLt with (y := @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tree_O).
  - exact (proj2 (tree_O_rEq X)).
  - eapply member_implies_rLt. exists tree_O. reflexivity.
Qed.

Lemma tree_top_S (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ tree_top X)
  : Ord.suc alpha <ᵣ tree_top X.
Proof.
  destruct H_rLt as [[tr H_rLe]]. eapply rLe_rLt_rLt with (y := @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_S tr)).
  - transitivity (Ord.suc (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr)).
    + eapply Ord_suc_rLe. exact H_rLe.
    + exact (proj2 (tree_S_rEq X tr)).
  - eapply member_implies_rLt. exists (tree_S tr). reflexivity.
Qed.

Lemma tree_top_union (X : Type@{Set_u}) (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ tree_top X)
  (H_rLt1 : beta <ᵣ tree_top X)
  : Ord_join alpha beta <ᵣ tree_top X.
Proof.
  destruct H_rLt0 as [[tr0 H_rLe0]], H_rLt1 as [[tr1 H_rLe1]].
  eapply rLe_rLt_rLt with (y := @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_union tr0 tr1)).
  - transitivity (Ord_join (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0) (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1)).
    + eapply Ord_join_spec.
      * transitivity (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0); [exact H_rLe0 | eapply Ord_join_l].
      * transitivity (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1); [exact H_rLe1 | eapply Ord_join_r].
    + eapply tree_union_le_rev.
  - eapply member_implies_rLt. exists (tree_union tr0 tr1). reflexivity.
Qed.

Lemma tree_top_join (X : Type@{Set_u}) (os : X -> Ord.t)
  (H_rLt : forall x : X, os x <ᵣ tree_top X)
  : Ord.sup X os <ᵣ tree_top X.
Proof.
  exploit (Axiom_of_Choice X (fun _ : X => tree X) (fun x : X => fun tr : tree X => os x ≦ᵣ @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr)).
  { intros x. pose proof (H_rLt x) as [[tr H_rLe]]. exists tr. exact H_rLe. }
  intros [f H_f]. eapply rLe_rLt_rLt with (y := @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_join f)).
  - eapply Ord_sup_rLe_intro. intros x. transitivity (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (f x)).
    + eapply H_f.
    + eapply rLt_implies_rLe. eapply member_implies_rLt. rewrite fromWf_unfold.
      exists (f x). split; [now exists x | reflexivity].
  - eapply member_implies_rLt. exists (tree_join f). reflexivity.
Qed.

Lemma tree_top_S_inaccessible (X : Type@{Set_u})
  : inaccessible X Ord.zer Ord.suc (tree_top X).
Proof.
  econs.
  - eapply tree_top_O.
  - eapply tree_top_S.
  - eapply tree_top_join.
  - eapply tree_top_union.
Qed.

Lemma tree_top_orec (X : Type@{Set_u}) (base0 : Ord.t) (next : Ord.t -> Ord.t) (base1 : Ord.t)
  (H_next_le : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (H_next_mon : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  (H_inaccessible : inaccessible X base0 next (tree_top X))
  (H_base1 : base1 <ᵣ tree_top X)
  : forall alpha : Ord.t, alpha <ᵣ tree_top X -> Ord.orec base1 next alpha <ᵣ tree_top X.
Proof.
  intros alpha H_rLt.
  enough (H_recs : forall tr : tree X, Ord.orec base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr) <ᵣ tree_top X).
  { destruct H_rLt as [[tr H_rLe]]. eapply rLe_rLt_rLt; [eapply Ord_orec_rLe; eauto; exact H_rLe | eapply H_recs]. }
  intros tr. induction tr as [ | tr IH | trs IH | tr0 IH0 tr1 IH1].
  - eapply rLe_rLt_rLt with (y := base1).
    + pose proof (Ord_orec_rEq_r base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tree_O) Ord.zer H_next_le H_next_mon (tree_O_rEq X)) as H_eq.
      pose proof (Ord_orec_zer base1 next) as H_eq0. transitivity (Ord.orec base1 next Ord.zer).
      * eapply H_eq.
      * exact (proj1 H_eq0).
    + exact H_base1.
  - eapply rLe_rLt_rLt with (y := next (Ord.orec base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr))).
    + pose proof (Ord_orec_rEq_r base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_S tr)) (Ord.suc (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr)) H_next_le H_next_mon (tree_S_rEq X tr)) as H_eq.
      transitivity (Ord.orec base1 next (Ord.suc (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr))).
      * eapply H_eq.
      * exact (proj1 (Ord_orec_suc base1 next H_next_le H_next_mon (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr))).
    + eapply H_inaccessible. exact IH.
  - eapply rLe_rLt_rLt with (y := Ord_join base1 (Ord.sup X (fun x : X => next (Ord.orec base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (trs x)))))).
    + transitivity (Ord.orec base1 next (mkNode X (fun x : X => @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (trs x)))).
      * eapply Ord_orec_rEq_r with (base := base1) (next := next) (alpha := @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (tree_join trs)) (beta := mkNode X (fun x : X => @fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) (trs x))); [exact H_next_le | exact H_next_mon | exact (tree_join_rEq X trs)].
      * rewrite Ord_orec_unfold. reflexivity.
    + eapply H_inaccessible.
      * exact H_base1.
      * eapply H_inaccessible. intros x. eapply H_inaccessible. exact (IH x).
  - eapply rLe_rLt_rLt with (y := Ord.orec base1 next (Ord.suc (Ord_join (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0) (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1)))).
    + eapply Ord_orec_rLe; eauto. eapply tree_union_le.
    + eapply rLe_rLt_rLt with (y := next (Ord.orec base1 next (Ord_join (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0) (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1)))).
      * exact (proj1 (Ord_orec_suc base1 next H_next_le H_next_mon (Ord_join (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0) (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1)))).
      * eapply H_inaccessible. eapply rLe_rLt_rLt with (y := Ord_join (Ord.orec base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0)) (Ord.orec base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1))).
        { exact (proj1 (Ord_orec_join base1 next (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr0) (@fromWf (tree X) (@tree_lt X) (tree_lt_well_founded X) tr1) H_next_le H_next_mon)). }
        { eapply H_inaccessible; assumption. }
Qed.

Lemma tree_top_rec_inaccessible (X : Type@{Set_u}) (base0 : Ord.t) (next : Ord.t -> Ord.t) (base1 : Ord.t)
  (H_next_le : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (H_next_mon : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  (H_inaccessible : inaccessible X base0 next (tree_top X))
  (H_base1 : base1 <ᵣ tree_top X)
  : inaccessible X base0 (Ord.orec base1 next) (tree_top X).
Proof.
  econs.
  - eapply H_inaccessible.
  - eapply tree_top_orec; eauto.
  - eapply H_inaccessible.
  - eapply H_inaccessible.
Qed.

Lemma tree_top_add_inaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ tree_top X)
  : inaccessible X Ord.zer (Ord.add alpha) (tree_top X).
Proof.
  unfold Ord.add. eapply tree_top_rec_inaccessible; eauto.
  - intros x. eapply Ord_rLe_suc.
  - intros x y H_rLe. eapply Ord_suc_rLe. exact H_rLe.
  - eapply tree_top_S_inaccessible.
Qed.

Lemma tree_top_add (X : Type@{Set_u}) (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ tree_top X)
  (H_rLt1 : beta <ᵣ tree_top X)
  : Ord.add alpha beta <ᵣ tree_top X.
Proof.
  eapply tree_top_add_inaccessible; eauto.
Qed.

Lemma tree_top_flip_add_inaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ tree_top X)
  : inaccessible X Ord.zer (fun x : Ord.t => Ord.add x alpha) (tree_top X).
Proof.
  econs.
  - eapply tree_top_O.
  - intros x LT_x. eapply tree_top_add; eauto.
  - eapply tree_top_join.
  - eapply tree_top_union.
Qed.

Lemma tree_top_mul_inaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ tree_top X)
  : inaccessible X Ord.zer (Ord.mul alpha) (tree_top X).
Proof.
  unfold Ord.mul. eapply tree_top_rec_inaccessible; eauto.
  - intros x. eapply Ord_add_base_l.
  - intros x y H_rLe. eapply Ord_add_rLe_l. exact H_rLe.
  - eapply tree_top_flip_add_inaccessible. exact H_rLt.
  - eapply tree_top_O.
Qed.

Lemma tree_top_mul (X : Type@{Set_u}) (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ tree_top X)
  (H_rLt1 : beta <ᵣ tree_top X)
  : Ord.mul alpha beta <ᵣ tree_top X.
Proof.
  eapply tree_top_mul_inaccessible; eauto.
Qed.

Lemma tree_top_flip_mul_inaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ tree_top X)
  : inaccessible X Ord.zer (fun x : Ord.t => Ord.mul x alpha) (tree_top X).
Proof.
  econs.
  - eapply tree_top_O.
  - intros x LT_x. eapply tree_top_mul; eauto.
  - eapply tree_top_join.
  - eapply tree_top_union.
Qed.

Lemma tree_top_exp_inaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_pos : Ord.zer <ᵣ alpha)
  (H_rLt : alpha <ᵣ tree_top X)
  : inaccessible X Ord.zer (Ord.exp alpha) (tree_top X).
Proof.
  unfold Ord.exp. eapply tree_top_rec_inaccessible; eauto.
  - intros x. eapply Ord_mul_base_l. exact H_pos.
  - intros x y H_rLe. eapply Ord_mul_rLe_l. exact H_rLe.
  - eapply tree_top_flip_mul_inaccessible. exact H_rLt.
  - unfold Ord.one. eapply tree_top_S. eapply tree_top_O.
Qed.

Lemma tree_top_exp (X : Type@{Set_u}) (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ tree_top X)
  (H_rLt1 : beta <ᵣ tree_top X)
  : Ord.exp alpha beta <ᵣ tree_top X.
Proof.
  eapply rLe_rLt_rLt with (y := Ord.exp (Ord.suc alpha) beta).
  - eapply Ord_exp_rLe_l. eapply Ord_rLe_suc.
  - eapply tree_top_exp_inaccessible.
    + eapply rLe_rLt_rLt with (y := alpha); [eapply Ord_zer_rLe | unfold Ord.suc; eapply rLt_succ_intro].
    + eapply tree_top_S. exact H_rLt0.
    + exact H_rLt1.
Qed.

Lemma tree_top_flip_exp_inaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ tree_top X)
  : inaccessible X Ord.zer (fun x : Ord.t => Ord.exp x alpha) (tree_top X).
Proof.
  econs.
  - eapply tree_top_O.
  - intros x LT_x. eapply tree_top_exp; eauto.
  - eapply tree_top_join.
  - eapply tree_top_union.
Qed.

Inductive gtree {X : Type@{Set_u}} : Type@{Set_u} :=
  | gtree_O : @gtree X
  | gtree_S : @gtree X -> @gtree X
  | gtree_join : forall P : X -> Prop, (@sig X P -> @gtree X) -> @gtree X
  | gtree_union : @gtree X -> @gtree X -> @gtree X.

#[global] Arguments gtree : clear implicits.

Definition gtree_lt {X : Type@{Set_u}} (tr0 : gtree X) (tr1 : gtree X) : Prop :=
  match tr1 with
  | gtree_O => False
  | gtree_S tr => tr0 = tr
  | gtree_join P trs => exists x : @sig X P, tr0 = trs x
  | gtree_union trl trr => tr0 = trl \/ tr0 = trr
  end.

Lemma gtree_lt_well_founded (X : Type@{Set_u})
  : well_founded (@gtree_lt X).
Proof.
  ii. induction a as [ | tr IH | P trs IH | tr0 IH0 tr1 IH1].
  - econs. intros y H_rLt. contradiction.
  - econs. intros y H_rLt. simpl in H_rLt. subst y. exact IH.
  - econs. intros y H_rLt. simpl in H_rLt. destruct H_rLt as [x ->]. exact (IH x).
  - econs. intros y H_rLt. simpl in H_rLt. destruct H_rLt as [-> | ->]; assumption.
Qed.

Definition gtree_top (X : Type@{Set_u}) : Ord.t :=
  @fromWfSet (gtree X) (@gtree_lt X) (gtree_lt_well_founded X).

Lemma gtree_O_rEq (X : Type@{Set_u})
  : @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) gtree_O =ᵣ Ord.zer.
Proof.
  rewrite rEq_iff. split.
  - eapply fromWf_isSupremum. intros y H_rLt. contradiction H_rLt.
  - eapply Ord_zer_rLe.
Qed.

Lemma gtree_S_rEq (X : Type@{Set_u}) (tr : gtree X)
  : @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_S tr) =ᵣ Ord.suc (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr).
Proof.
  rewrite rEq_iff. split.
  - eapply fromWf_isSupremum. intros y H_rLt. simpl in H_rLt. subst y. unfold Ord.suc. eapply rLt_succ_intro.
  - unfold Ord.suc. rewrite succ_rLe_iff. eapply member_implies_rLt. rewrite fromWf_unfold.
    exists tr. split; [reflexivity | reflexivity].
Qed.

Lemma gtree_join_rEq (X : Type@{Set_u}) (P : X -> Prop) (trs : @sig X P -> gtree X)
  : @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_join P trs) =ᵣ mkNode (@sig X P) (fun x : @sig X P => @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (trs x)).
Proof.
  rewrite rEq_iff. split.
  - eapply fromWf_isSupremum. intros y H_rLt. simpl in H_rLt. destruct H_rLt as [x ->].
    eapply member_implies_rLt. exists x. reflexivity.
  - econs. intros x. eapply member_implies_rLt. rewrite fromWf_unfold.
    exists (trs x). split; [now exists x | reflexivity].
Qed.

Lemma gtree_union_le (X : Type@{Set_u}) (tr0 : gtree X) (tr1 : gtree X)
  : @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_union tr0 tr1) ≦ᵣ Ord.suc (Ord_join (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0) (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1)).
Proof.
  eapply fromWf_isSupremum. intros y H_rLt. simpl in H_rLt. unfold Ord.suc. rewrite rLt_succ_iff. destruct H_rLt as [-> | ->].
  - eapply Ord_join_l.
  - eapply Ord_join_r.
Qed.

Lemma gtree_union_le_rev (X : Type@{Set_u}) (tr0 : gtree X) (tr1 : gtree X)
  : Ord_join (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0) (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1) ≦ᵣ @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_union tr0 tr1).
Proof.
  eapply Ord_join_spec; eapply rLt_implies_rLe; eapply member_implies_rLt; rewrite fromWf_unfold.
  - exists tr0. split; [now left | reflexivity].
  - exists tr1. split; [now right | reflexivity].
Qed.

Lemma gtree_top_O (X : Type@{Set_u})
  : Ord.zer <ᵣ gtree_top X.
Proof.
  eapply rLe_rLt_rLt with (y := @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) gtree_O).
  - exact (proj2 (gtree_O_rEq X)).
  - eapply member_implies_rLt. exists gtree_O. reflexivity.
Qed.

Lemma gtree_top_S (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ gtree_top X)
  : Ord.suc alpha <ᵣ gtree_top X.
Proof.
  destruct H_rLt as [[tr H_rLe]]. eapply rLe_rLt_rLt with (y := @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_S tr)).
  - transitivity (Ord.suc (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr)).
    + eapply Ord_suc_rLe. exact H_rLe.
    + exact (proj2 (gtree_S_rEq X tr)).
  - eapply member_implies_rLt. exists (gtree_S tr). reflexivity.
Qed.

Lemma gtree_top_union (X : Type@{Set_u}) (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ gtree_top X)
  (H_rLt1 : beta <ᵣ gtree_top X)
  : Ord_join alpha beta <ᵣ gtree_top X.
Proof.
  destruct H_rLt0 as [[tr0 H_rLe0]], H_rLt1 as [[tr1 H_rLe1]].
  eapply rLe_rLt_rLt with (y := @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_union tr0 tr1)).
  - transitivity (Ord_join (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0) (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1)).
    + eapply Ord_join_spec.
      * transitivity (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0); [exact H_rLe0 | eapply Ord_join_l].
      * transitivity (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1); [exact H_rLe1 | eapply Ord_join_r].
    + eapply gtree_union_le_rev.
  - eapply member_implies_rLt. exists (gtree_union tr0 tr1). reflexivity.
Qed.

Lemma gtree_top_join (X : Type@{Set_u}) (P : X -> Prop) (os : @sig X P -> Ord.t)
  (H_rLt : forall x : @sig X P, os x <ᵣ gtree_top X)
  : Ord.sup (@sig X P) os <ᵣ gtree_top X.
Proof.
  pose proof (Axiom_of_Choice (@sig X P) (fun _ : @sig X P => gtree X) (fun x : @sig X P => fun tr : gtree X => os x ≦ᵣ @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr)) as [f H_f].
  { intros x. pose proof (H_rLt x) as [[tr H_rLe]]. exists tr. exact H_rLe. }
  eapply rLe_rLt_rLt with (y := @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_join P f)).
  - eapply Ord_sup_rLe_intro. intros x. transitivity (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (f x)).
    + eapply H_f.
    + eapply rLt_implies_rLe. eapply member_implies_rLt. rewrite fromWf_unfold. exists (f x). split; [now exists x | reflexivity].
  - eapply member_implies_rLt. exists (gtree_join P f). reflexivity.
Qed.

Lemma gtree_top_S_ginaccessible (X : Type@{Set_u})
  : ginaccessible X Ord.zer Ord.suc (gtree_top X).
Proof.
  econs.
  - eapply gtree_top_O.
  - eapply gtree_top_S.
  - eapply gtree_top_join.
  - eapply gtree_top_union.
Qed.

Lemma gtree_top_orec (X : Type@{Set_u}) (base0 : Ord.t) (next : Ord.t -> Ord.t) (base1 : Ord.t)
  (H_next_le : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (H_next_mon : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  (H_inaccessible : ginaccessible X base0 next (gtree_top X))
  (H_base1 : base1 <ᵣ gtree_top X)
  : forall alpha : Ord.t, alpha <ᵣ gtree_top X -> Ord.orec base1 next alpha <ᵣ gtree_top X.
Proof.
  intros alpha H_rLt.
  enough (H_recs : forall tr : gtree X, Ord.orec base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr) <ᵣ gtree_top X).
  { destruct H_rLt as [[tr H_rLe]]. eapply rLe_rLt_rLt; [eapply Ord_orec_rLe; eauto; exact H_rLe | eapply H_recs]. }
  intros tr. induction tr as [ | tr IH | P trs IH | tr0 IH0 tr1 IH1].
  - eapply rLe_rLt_rLt with (y := base1).
    + pose proof (Ord_orec_rEq_r base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) gtree_O) Ord.zer H_next_le H_next_mon (gtree_O_rEq X)) as H_eq.
      pose proof (Ord_orec_zer base1 next) as H_eq0. transitivity (Ord.orec base1 next Ord.zer).
      * eapply H_eq.
      * exact (proj1 H_eq0).
    + exact H_base1.
  - eapply rLe_rLt_rLt with (y := next (Ord.orec base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr))).
    + pose proof (Ord_orec_rEq_r base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_S tr)) (Ord.suc (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr)) H_next_le H_next_mon (gtree_S_rEq X tr)) as H_eq.
      transitivity (Ord.orec base1 next (Ord.suc (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr))).
      * eapply H_eq.
      * exact (proj1 (Ord_orec_suc base1 next H_next_le H_next_mon (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr))).
    + eapply H_inaccessible. exact IH.
  - eapply rLe_rLt_rLt with (y := Ord_join base1 (Ord.sup (@sig X P) (fun x : @sig X P => next (Ord.orec base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (trs x)))))).
    + pose proof (Ord_orec_rEq_r base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (gtree_join P trs)) (mkNode (@sig X P) (fun x : @sig X P => @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (trs x))) H_next_le H_next_mon (gtree_join_rEq X P trs)) as H_eq.
      transitivity (Ord.orec base1 next (mkNode (@sig X P) (fun x : @sig X P => @fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) (trs x)))).
      * eapply H_eq.
      * rewrite Ord_orec_unfold. reflexivity.
    + eapply H_inaccessible.
      * exact H_base1.
      * eapply H_inaccessible. intros x. eapply H_inaccessible. exact (IH x).
  - eapply rLe_rLt_rLt with (y := Ord.orec base1 next (Ord.suc (Ord_join (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0) (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1)))).
    + eapply Ord_orec_rLe; eauto. eapply gtree_union_le.
    + eapply rLe_rLt_rLt with (y := next (Ord.orec base1 next (Ord_join (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0) (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1)))).
      * exact (proj1 (Ord_orec_suc base1 next H_next_le H_next_mon (Ord_join (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0) (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1)))).
      * eapply H_inaccessible. eapply rLe_rLt_rLt with (y := Ord_join (Ord.orec base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0)) (Ord.orec base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1))).
        { exact (proj1 (Ord_orec_join base1 next (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr0) (@fromWf (gtree X) (@gtree_lt X) (gtree_lt_well_founded X) tr1) H_next_le H_next_mon)). }
        { eapply H_inaccessible; assumption. }
Qed.

Lemma gtree_top_rec_ginaccessible (X : Type@{Set_u}) (base0 : Ord.t) (next : Ord.t -> Ord.t) (base1 : Ord.t)
  (H_next_le : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (H_next_mon : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  (H_inaccessible : ginaccessible X base0 next (gtree_top X))
  (H_base1 : base1 <ᵣ gtree_top X)
  : ginaccessible X base0 (Ord.orec base1 next) (gtree_top X).
Proof.
  econs.
  - eapply H_inaccessible.
  - eapply gtree_top_orec; eauto.
  - eapply H_inaccessible.
  - eapply H_inaccessible.
Qed.

Lemma gtree_top_add_ginaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ gtree_top X)
  : ginaccessible X Ord.zer (Ord.add alpha) (gtree_top X).
Proof.
  unfold Ord.add. eapply gtree_top_rec_ginaccessible; eauto.
  - intros x. eapply Ord_rLe_suc.
  - intros x y H_rLe. eapply Ord_suc_rLe. exact H_rLe.
  - eapply gtree_top_S_ginaccessible.
Qed.

Lemma gtree_top_add (X : Type@{Set_u}) (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ gtree_top X)
  (H_rLt1 : beta <ᵣ gtree_top X)
  : Ord.add alpha beta <ᵣ gtree_top X.
Proof.
  eapply gtree_top_add_ginaccessible; eauto.
Qed.

Lemma gtree_top_flip_add_ginaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ gtree_top X)
  : ginaccessible X Ord.zer (fun x : Ord.t => Ord.add x alpha) (gtree_top X).
Proof.
  econs.
  - eapply gtree_top_O.
  - intros x LT_x. eapply gtree_top_add; eauto.
  - eapply gtree_top_join.
  - eapply gtree_top_union.
Qed.

Lemma gtree_top_mul_ginaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ gtree_top X)
  : ginaccessible X Ord.zer (Ord.mul alpha) (gtree_top X).
Proof.
  unfold Ord.mul. eapply gtree_top_rec_ginaccessible; eauto.
  - intros x. eapply Ord_add_base_l.
  - intros x y H_rLe. eapply Ord_add_rLe_l. exact H_rLe.
  - eapply gtree_top_flip_add_ginaccessible. exact H_rLt.
  - eapply gtree_top_O.
Qed.

Lemma gtree_top_mul (X : Type@{Set_u}) (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ gtree_top X)
  (H_rLt1 : beta <ᵣ gtree_top X)
  : Ord.mul alpha beta <ᵣ gtree_top X.
Proof.
  eapply gtree_top_mul_ginaccessible; eauto.
Qed.

Lemma gtree_top_flip_mul_ginaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ gtree_top X)
  : ginaccessible X Ord.zer (fun x : Ord.t => Ord.mul x alpha) (gtree_top X).
Proof.
  econs.
  - eapply gtree_top_O.
  - intros x LT_x. eapply gtree_top_mul; eauto.
  - eapply gtree_top_join.
  - eapply gtree_top_union.
Qed.

Lemma gtree_top_exp_ginaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_pos : Ord.zer <ᵣ alpha)
  (H_rLt : alpha <ᵣ gtree_top X)
  : ginaccessible X Ord.zer (Ord.exp alpha) (gtree_top X).
Proof.
  unfold Ord.exp. eapply gtree_top_rec_ginaccessible; eauto.
  - intros x. eapply Ord_mul_base_l. exact H_pos.
  - intros x y H_rLe. eapply Ord_mul_rLe_l. exact H_rLe.
  - eapply gtree_top_flip_mul_ginaccessible. exact H_rLt.
  - unfold Ord.one. eapply gtree_top_S. eapply gtree_top_O.
Qed.

Lemma gtree_top_exp (X : Type@{Set_u}) (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ gtree_top X)
  (H_rLt1 : beta <ᵣ gtree_top X)
  : Ord.exp alpha beta <ᵣ gtree_top X.
Proof.
  eapply rLe_rLt_rLt with (y := Ord.exp (Ord.suc alpha) beta).
  - eapply Ord_exp_rLe_l. eapply Ord_rLe_suc.
  - eapply gtree_top_exp_ginaccessible.
    + eapply rLe_rLt_rLt with (y := alpha); [eapply Ord_zer_rLe | unfold Ord.suc; eapply rLt_succ_intro].
    + eapply gtree_top_S. exact H_rLt0.
    + exact H_rLt1.
Qed.

Lemma gtree_top_flip_exp_ginaccessible (X : Type@{Set_u}) (alpha : Ord.t)
  (H_rLt : alpha <ᵣ gtree_top X)
  : ginaccessible X Ord.zer (fun x : Ord.t => Ord.exp x alpha) (gtree_top X).
Proof.
  econs.
  - eapply gtree_top_O.
  - intros x LT_x. eapply gtree_top_exp; eauto.
  - eapply gtree_top_join.
  - eapply gtree_top_union.
Qed.

Definition kappa : Ord.t :=
  @mkNode { A : Type & { R : A -> A -> Prop | well_founded R } } (fun RWF => @fromWfSet (projT1 RWF) (proj1_sig (projT2 RWF)) (proj2_sig (projT2 RWF))).

Lemma kappa_complete (alpha : Ord.t)
  (H_rLt : alpha <ᵣ kappa)
  : exists A : Type, exists R : A -> A -> Prop, exists R_wf : well_founded R, alpha ≦ᵣ @fromWfSet A R R_wf.
Proof.
  destruct H_rLt as [[[A [R R_wf]] H_rLe]]. exists A, R, R_wf. exact H_rLe.
Qed.

Lemma kappa_inaccessible_from_wf_set (A : Type) (R : A -> A -> Prop) (R_wf : well_founded R)
  : @fromWfSet A R R_wf <ᵣ kappa.
Proof.
  econs. exists (@existT Type (fun A : Type => { R : A -> A -> Prop | well_founded R }) A (@exist (A -> A -> Prop) (@well_founded A) R R_wf)). reflexivity.
Qed.

Lemma kappa_inaccessible_from_wf (A : Type) (R : A -> A -> Prop) (R_wf : well_founded R) (a : A)
  : @fromWf A R R_wf a <ᵣ kappa.
Proof.
  eapply rLt_rLe_rLt with (y := @fromWfSet A R R_wf).
  - eapply member_implies_rLt. exists a. reflexivity.
  - eapply rLt_implies_rLe. eapply kappa_inaccessible_from_wf_set.
Qed.

Lemma kappa_inaccessible_cardinality (A : Type)
  : Cardinality.toTree (Cardinality.ofType A) <ᵣ kappa.
Proof.
  pose proof (well_ordering_thm A (@mkSetoid_from_eq A)) as (R & R_wf & R_total & R_trans & R_compat).
  eapply rLe_rLt_rLt with (y := @fromWfSet A R R_wf).
  - eapply Cardinal1.Cardinality_lowerbound; eauto.
  - eapply kappa_inaccessible_from_wf_set.
Qed.

Lemma kappa_inaccessible_O
  : Ord.zer <ᵣ kappa.
Proof.
  eapply rLe_rLt_rLt with (y := @fromWfSet Empty_set (fun x : Empty_set => fun _ : Empty_set => False) (Empty_set_ind _)).
  - eapply Ord_zer_rLe.
  - eapply kappa_inaccessible_from_wf_set.
Qed.

Lemma kappa_inaccessible_is_S (alpha : Ord.t) (beta : Ord.t)
  (H_succ : beta =ᵣ Ord.suc alpha)
  (H_rLt : alpha <ᵣ kappa)
  : beta <ᵣ kappa.
Proof.
  rewrite H_succ. pose proof (kappa_complete alpha H_rLt) as (A & R & R_wf & H_rLe).
  set (Ropt := fun x : option A => fun y : option A =>
    match x, y with
    | Some x', Some y' => R x' y'
    | Some x', None => True
    | None, _ => False
    end
  ).
  assert (H_some_acc : forall a : A, Acc Ropt (Some a)).
  { intros a. induction (R_wf a) as [a H_Acc_inv IH]. econs. intros [b | ] H_rel.
    - eapply IH. exact H_rel.
    - contradiction.
  }
  assert (Ropt_wf : well_founded Ropt).
  { intros [a | ]. eapply H_some_acc. econs. intros [a | ] H_rel.
    - eapply H_some_acc.
    - contradiction.
  }
  assert (H_top : @fromWfSet A R R_wf ≦ᵣ @fromWf (option A) Ropt Ropt_wf None).
  { econs. intros a.
    assert (H_rLe_a : @fromWf A R R_wf a ≦ᵣ @fromWf (option A) Ropt Ropt_wf (Some a)).
    { eapply fromWf_cong with (RA := R) (RB := Ropt) (f := @Some A) (RA_wf := R_wf) (RB_wf := Ropt_wf). intros x y H_xy. exact H_xy. }
    assert (H_rLt_a : @fromWf (option A) Ropt Ropt_wf (Some a) <ᵣ @fromWf (option A) Ropt Ropt_wf None).
    { eapply member_implies_rLt. rewrite fromWf_unfold. exists (Some a). split; [reflexivity | reflexivity]. }
    eapply rLe_rLt_rLt; eauto.
  }
  eapply rLe_rLt_rLt with (y := Ord.suc (@fromWfSet A R R_wf)).
  - eapply Ord_suc_rLe. exact H_rLe.
  - eapply rLe_rLt_rLt with (y := @fromWfSet (option A) Ropt Ropt_wf).
    + unfold Ord.suc. rewrite succ_rLe_iff. eapply rLe_rLt_rLt with (y := @fromWf (option A) Ropt Ropt_wf None).
      * exact H_top.
      * eapply member_implies_rLt. exists None. reflexivity.
    + eapply kappa_inaccessible_from_wf_set.
Qed.

Lemma kappa_inaccessible_S (alpha : Ord.t)
  (H_rLt : alpha <ᵣ kappa)
  : Ord.suc alpha <ᵣ kappa.
Proof.
  eapply kappa_inaccessible_is_S; eauto. reflexivity.
Qed.

Lemma kappa_inaccessible_Ord_of_nat (n : nat)
  : Ord_of_nat n <ᵣ kappa.
Proof.
  induction n as [ | n IH].
  - eapply kappa_inaccessible_O.
  - simpl. eapply kappa_inaccessible_S. exact IH.
Qed.

Lemma kappa_inaccessible_join (A : Type) (os : A -> Ord.t)
  (H_rLt : forall a : A, os a <ᵣ kappa)
  : Ord.sup A os <ᵣ kappa.
Proof.
  pose proof (Axiom_of_Choice A (fun _ : A => { B : Type & { R : B -> B -> Prop | well_founded R } }) (fun a : A => fun RWF : { B : Type & { R : B -> B -> Prop | well_founded R } } => os a ≦ᵣ @fromWfSet (projT1 RWF) (proj1_sig (projT2 RWF)) (proj2_sig (projT2 RWF)))) as [f H_f].
  { intros a. pose proof (kappa_complete (os a) (H_rLt a)) as (B & R & R_wf & H_rLe). exists (@existT Type (fun B : Type => { R : B -> B -> Prop | well_founded R }) B (@exist (B -> B -> Prop) (@well_founded B) R R_wf)). exact H_rLe. }
  set (B := fun a : A => projT1 (f a)).
  set (R := fun a : A => proj1_sig (projT2 (f a))).
  set (R_wf := fun a : A => proj2_sig (projT2 (f a))).
  pose (A_join := { a : A & option (B a) }).
  pose (fun x : A_join => fun y : A_join =>
    match y with
    | @existT _ _ a None =>
      match x with
      | @existT _ _ a' (Some _) => a = a'
      | _ => False
      end
    | @existT _ _ a (Some y') =>
      match x with
      | @existT _ _ a' (Some x') => exists H_eq : a' = a, R a (eq_rect a' B x' a H_eq) y'
      | _ => False
      end
    end
  ) as R_join.
  assert (R_join_wf : well_founded R_join).
  { intros [a [x | ]].
    + induction (R_wf a x) as [x H_Acc_inv IH]. econs. intros [a' [y | ]] H_rel.
      * unfold R_join in H_rel. destruct H_rel as [H_eq H_rel]. subst a'. simpl in H_rel. eapply IH. exact H_rel.
      * contradiction.
    + econs. intros [a' [y | ]] H_rel.
      * unfold R_join in H_rel. subst a'. induction (R_wf a y) as [y H_Acc_inv IH]. econs. intros [a' [z | ]] H_rel.
        { unfold R_join in H_rel. destruct H_rel as [H_eq H_rel]. subst a'. simpl in H_rel. eapply IH. exact H_rel. }
        { contradiction. }
      * contradiction.
  }
  eapply rLe_rLt_rLt with (y := @fromWfSet A_join R_join R_join_wf).
  - eapply Ord_sup_rLe_intro. intros a. transitivity (@fromWfSet (B a) (R a) (R_wf a)).
    + eapply H_f.
    + eapply rLt_implies_rLe. eapply rLe_rLt_rLt with (y := @fromWf A_join R_join R_join_wf (@existT A (fun a : A => option (B a)) a None)).
      * econs. intros x. eapply rLe_rLt_rLt with (y := @fromWf A_join R_join R_join_wf (@existT A (fun a : A => option (B a)) a (Some x))).
        { eapply fromWf_cong with (RA := R a) (RB := R_join) (f := fun x : B a => @existT A (fun a : A => option (B a)) a (Some x)) (RA_wf := R_wf a) (RB_wf := R_join_wf). intros x0 y0 H_xy. exists eq_refl. exact H_xy. }
        { eapply member_implies_rLt. rewrite fromWf_unfold. exists (@existT A (fun a : A => option (B a)) a (Some x)). split; [reflexivity | reflexivity]. }
      * eapply member_implies_rLt. exists (@existT A (fun a : A => option (B a)) a None). reflexivity.
  - eapply kappa_inaccessible_from_wf_set.
Qed.

Lemma kappa_inaccessible_union (alpha : Ord.t) (beta : Ord.t)
  (H_rLt : alpha <ᵣ kappa)
  (H_rLt' : beta <ᵣ kappa)
  : Ord_join alpha beta <ᵣ kappa.
Proof.
  unfold Ord_join. eapply kappa_inaccessible_join. intros [ | ]; assumption.
Qed.

Lemma kappa_inaccessible_omega
  : omega <ᵣ kappa.
Proof.
  unfold omega. eapply kappa_inaccessible_join. intros n. eapply kappa_inaccessible_Ord_of_nat.
Qed.

Lemma kappa_inaccessible_orec (base : Ord.t) (next : Ord.t -> Ord.t)
  (H_next_le : forall alpha : Ord.t, alpha ≦ᵣ next alpha)
  (H_next_mon : forall alpha : Ord.t, forall beta : Ord.t, alpha ≦ᵣ beta -> next alpha ≦ᵣ next beta)
  (H_base : base <ᵣ kappa)
  (H_next : forall alpha : Ord.t, alpha <ᵣ kappa -> next alpha <ᵣ kappa)
  : forall alpha : Ord.t, alpha <ᵣ kappa -> Ord.orec base next alpha <ᵣ kappa.
Proof.
  intros alpha H_rLt.
  pose proof (kappa_complete alpha H_rLt) as (A & R & R_wf & H_rLe).
  assert (H_rec : forall a : A, Ord.orec base next (@fromWf A R R_wf a) <ᵣ kappa).
  { intros a. induction (R_wf a) as [a H_Acc_inv IH].
    eapply rLe_rLt_rLt with (y := Ord.orec base next (Ord.suc (Ord.sup (@sig A (fun b : A => R b a)) (fun b : @sig A (fun b : A => R b a) => @fromWf A R R_wf (proj1_sig b))))).
    - eapply Ord_orec_rLe; eauto. eapply fromWf_isSupremum. intros b R_b_a.
      eapply rLe_rLt_rLt with (y := Ord.sup (@sig A (fun b : A => R b a)) (fun b : @sig A (fun b : A => R b a) => @fromWf A R R_wf (proj1_sig b))).
      + change ((fun b0 : @sig A (fun b : A => R b a) => @fromWf A R R_wf (proj1_sig b0)) (@exist A (fun b : A => R b a) b R_b_a) ≦ᵣ Ord.sup (@sig A (fun b : A => R b a)) (fun b0 : @sig A (fun b : A => R b a) => @fromWf A R R_wf (proj1_sig b0))). eapply Ord_rLe_sup_intro.
      + unfold Ord.suc. eapply rLt_succ_intro.
    - eapply rLe_rLt_rLt with (y := next (Ord.orec base next (Ord.sup (@sig A (fun b : A => R b a)) (fun b : @sig A (fun b : A => R b a) => @fromWf A R R_wf (proj1_sig b))))).
      + exact (proj1 (Ord_orec_suc base next H_next_le H_next_mon (Ord.sup (@sig A (fun b : A => R b a)) (fun b : @sig A (fun b : A => R b a) => @fromWf A R R_wf (proj1_sig b))))).
      + eapply H_next. eapply rLe_rLt_rLt with (y := Ord_join base (Ord.sup (@sig A (fun b : A => R b a)) (fun b : @sig A (fun b : A => R b a) => Ord.orec base next (@fromWf A R R_wf (proj1_sig b))))).
        * exact (proj1 (Ord_orec_sup base next (@sig A (fun b : A => R b a)) (fun b : @sig A (fun b : A => R b a) => @fromWf A R R_wf (proj1_sig b)) H_next_le H_next_mon)).
        * eapply kappa_inaccessible_union.
          { exact H_base. }
          { eapply kappa_inaccessible_join. intros [b R_b_a]. eapply IH. exact R_b_a. }
  }
  eapply rLe_rLt_rLt with (y := Ord.orec base next (@fromWfSet A R R_wf)).
  - eapply Ord_orec_rLe; [exact H_next_le | exact H_next_mon | exact H_rLe].
  - eapply rLe_rLt_rLt with (y := Ord_join base (Ord.sup A (fun a : A => next (Ord.orec base next (@fromWf A R R_wf a))))).
    + unfold fromWfSet. rewrite Ord_orec_unfold. reflexivity.
    + eapply kappa_inaccessible_union.
      * exact H_base.
      * eapply kappa_inaccessible_join. intros a. eapply H_next. eapply H_rec.
Qed.

Lemma kappa_inaccessible_add (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ kappa)
  (H_rLt1 : beta <ᵣ kappa)
  : Ord.add alpha beta <ᵣ kappa.
Proof.
  unfold Ord.add. eapply kappa_inaccessible_orec; eauto.
  - intros x. eapply Ord_rLe_suc.
  - intros x y H_rLe. eapply Ord_suc_rLe. exact H_rLe.
  - intros x H_rLt. eapply kappa_inaccessible_S. exact H_rLt.
Qed.

Lemma kappa_inaccessible_mul (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ kappa)
  (H_rLt1 : beta <ᵣ kappa)
  : Ord.mul alpha beta <ᵣ kappa.
Proof.
  unfold Ord.mul. eapply kappa_inaccessible_orec; eauto.
  - intros x. eapply Ord_add_base_l.
  - intros x y H_rLe. eapply Ord_add_rLe_l. exact H_rLe.
  - eapply kappa_inaccessible_O.
  - intros x H_rLt. eapply kappa_inaccessible_add; eauto.
Qed.

Lemma kappa_inaccessible_exp (alpha : Ord.t) (beta : Ord.t)
  (H_rLt0 : alpha <ᵣ kappa)
  (H_rLt1 : beta <ᵣ kappa)
  : Ord.exp alpha beta <ᵣ kappa.
Proof.
  eapply rLe_rLt_rLt with (y := Ord.exp (Ord.suc alpha) beta).
  - eapply Ord_exp_rLe_l. eapply Ord_rLe_suc.
  - unfold Ord.exp. eapply kappa_inaccessible_orec; eauto.
    + intros x. eapply Ord_mul_base_l. eapply rLe_rLt_rLt with (y := alpha).
      * eapply Ord_zer_rLe.
      * unfold Ord.suc. eapply rLt_succ_intro.
    + intros x y H_rLe. eapply Ord_mul_rLe_l. exact H_rLe.
    + unfold Ord.one. eapply kappa_inaccessible_S. eapply kappa_inaccessible_O.
    + intros x H_rLt. eapply kappa_inaccessible_mul.
      * exact H_rLt.
      * eapply kappa_inaccessible_S. exact H_rLt0.
Qed.

End CLASSICAL.

End Inaccessible.
