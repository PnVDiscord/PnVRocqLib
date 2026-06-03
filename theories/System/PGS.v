Require Import PnV.Prelude.Prelude.
Require Import PnV.Data.FiniteSet.
Require Import PnV.Data.FiniteMap.
Require Import PnV.Data.Graph.
Require Import PnV.Data.Vector.

#[local] Infix "\in" := E.In : type_scope.
#[local] Infix "=~=" := is_similar_to : type_scope.
#[local] Infix "∈" := L.In.

Inductive symbol (terminal : Type) (nonterminal : Type) : Type :=
  | symbol_terminal (tok : terminal)
    : symbol terminal nonterminal
  | symbol_nonterminal (nt : nonterminal)
    : symbol terminal nonterminal.

#[global] Arguments symbol_terminal {terminal} {nonterminal} tok.
#[global] Arguments symbol_nonterminal {terminal} {nonterminal} nt.

#[global]
Instance symbol_hasEqDec {terminal : Type} {nonterminal : Type}
  (terminal_hasEqDec : hasEqDec terminal)
  (nonterminal_hasEqDec : hasEqDec nonterminal)
  : hasEqDec (symbol terminal nonterminal).
Proof.
  red in terminal_hasEqDec, nonterminal_hasEqDec |- *. decide equality.
Defined.

Definition all_symbols {terminal : Type} {nonterminal : Type} (all_terminals : list terminal) (all_nonterminals : list nonterminal) : list (symbol terminal nonterminal) :=
  map symbol_terminal all_terminals ++ map symbol_nonterminal all_nonterminals.

Lemma all_symbols_terminal_complete {terminal : Type} {nonterminal : Type} (all_terminals : list terminal) (all_nonterminals : list nonterminal) (tok : terminal)
  (IN : tok ∈ all_terminals)
  : symbol_terminal tok ∈ all_symbols all_terminals all_nonterminals.
Proof.
  unfold all_symbols. rewrite in_app_iff. left. rewrite in_map_iff. exists tok. split; [reflexivity | exact IN].
Qed.

Lemma all_symbols_nonterminal_complete {terminal : Type} {nonterminal : Type} (all_terminals : list terminal) (all_nonterminals : list nonterminal) (nt : nonterminal)
  (IN : nt ∈ all_nonterminals)
  : symbol_nonterminal nt ∈ all_symbols all_terminals all_nonterminals.
Proof.
  unfold all_symbols. rewrite in_app_iff. right. rewrite in_map_iff. exists nt. split; [reflexivity | exact IN].
Qed.

Module Type GRAMMAR_SPEC.

Declare Module Token : FINITE_ENUM.

Declare Module Nonterminal : FINITE_ENUM.

Declare Module Production : FINITE_ENUM.

Parameter start : Nonterminal.t.

Parameter lhs : Production.t -> Nonterminal.t.

Parameter rhs : Production.t -> list (symbol Token.t Nonterminal.t).

End GRAMMAR_SPEC.

Module PGS (Grammar : GRAMMAR_SPEC).

#[local] Existing Instance Grammar.Token.t_hasEqDec.
#[local] Existing Instance Grammar.Nonterminal.t_hasEqDec.
#[local] Existing Instance Grammar.Production.t_hasEqDec.

Module Error.

Inductive t : Set :=
  | ShiftReduceConflict
    (state_index : nat)
    (tok : option Grammar.Token.t)
  | ReduceReduceConflict
    (state_index : nat)
    (tok : option Grammar.Token.t)
  | NoAction
    (state_index : nat)
    (tok : option Grammar.Token.t)
  | InternalInvariantBroken.

End Error.

#[universes(polymorphic=yes)]
Definition ErrM@{u} (A : Type@{u}) : Type@{u} :=
  Error.t + A.

Notation token := Grammar.Token.t.
Notation nonterminal := Grammar.Nonterminal.t.
Notation production := Grammar.Production.t.
Notation raw_symbol := (symbol token nonterminal).

#[local]
Instance token_hasEqDec : hasEqDec@{Set} token :=
  Grammar.Token.t_hasEqDec.

#[local]
Instance nonterminal_hasEqDec : hasEqDec@{Set} nonterminal :=
  Grammar.Nonterminal.t_hasEqDec.

#[local]
Instance production_hasEqDec : hasEqDec@{Set} production :=
  Grammar.Production.t_hasEqDec.

Definition raw_symbols : list raw_symbol :=
  all_symbols Grammar.Token.all Grammar.Nonterminal.all.

Lemma raw_symbols_terminal_complete (tok : token)
  : symbol_terminal tok ∈ raw_symbols.
Proof.
  unfold raw_symbols. eapply all_symbols_terminal_complete. eapply Grammar.Token.all_complete.
Qed.

Lemma raw_symbols_nonterminal_complete (nt : nonterminal)
  : symbol_nonterminal nt ∈ raw_symbols.
Proof.
  unfold raw_symbols. eapply all_symbols_nonterminal_complete. eapply Grammar.Nonterminal.all_complete.
Qed.

Definition raw_symbol_wf (sym : raw_symbol) : Prop :=
  sym ∈ raw_symbols.

Definition production_wf (prod : production) : Prop :=
  forall sym, sym ∈ Grammar.rhs prod -> raw_symbol_wf sym.

Lemma production_wf_all (prod : production)
  : production_wf prod.
Proof.
  intros [tok | nt] _; [eapply raw_symbols_terminal_complete | eapply raw_symbols_nonterminal_complete].
Qed.

Lemma start_symbol_wf
  : Grammar.start ∈ Grammar.Nonterminal.all.
Proof.
  eapply Grammar.Nonterminal.all_complete.
Qed.

Definition sentence (tokens : list token) : list raw_symbol :=
  map symbol_terminal tokens.

Inductive derives1 : list raw_symbol -> list raw_symbol -> Prop :=
  | derives1_intro (prod : production) (prefix : list raw_symbol) (suffix : list raw_symbol)
    : derives1 (prefix ++ symbol_nonterminal (Grammar.lhs prod) :: suffix) (prefix ++ Grammar.rhs prod ++ suffix).

Inductive derives : list raw_symbol -> list raw_symbol -> Prop :=
  | derives_refl (xs : list raw_symbol)
    : derives xs xs
  | derives_step (xs : list raw_symbol) (ys : list raw_symbol) (zs : list raw_symbol)
    (STEP : derives1 xs ys)
    (REST : derives ys zs)
    : derives xs zs.

#[local] Hint Constructors derives1 derives : core.

Lemma derives_trans (xs : list raw_symbol) (ys : list raw_symbol) (zs : list raw_symbol)
  (DERIVES1 : derives xs ys)
  (DERIVES2 : derives ys zs)
  : derives xs zs.
Proof.
  induction DERIVES1 as [xs | xs ys mid STEP REST IH]; [exact DERIVES2 | ]. eapply derives_step; [exact STEP | eapply IH; exact DERIVES2].
Qed.

Definition in_language (tokens : list token) : Prop :=
  derives [symbol_nonterminal Grammar.start] (sentence tokens).

Definition nullable_nt (nt : nonterminal) : Prop :=
  derives [symbol_nonterminal nt] [].

Definition first_token_of_symbols (xs : list raw_symbol) (tok : token) : Prop :=
  exists suffix, derives xs (symbol_terminal tok :: suffix).

Notation aug_token := (option token).
Notation aug_nonterminal := (option nonterminal).
Notation aug_symbol := (symbol aug_token aug_nonterminal).

Definition end_marker : aug_token :=
  None.

Definition fresh_start : aug_nonterminal :=
  None.

#[local]
Instance aug_token_hasEqDec : hasEqDec@{Set} aug_token :=
  option_hasEqDec token_hasEqDec.

#[local]
Instance aug_nonterminal_hasEqDec : hasEqDec@{Set} aug_nonterminal :=
  option_hasEqDec nonterminal_hasEqDec.

#[local]
Instance aug_symbol_hasEqDec : hasEqDec@{Set} aug_symbol :=
  symbol_hasEqDec aug_token_hasEqDec aug_nonterminal_hasEqDec.

Definition lift_token (tok : token) : aug_token :=
  Some tok.

Definition lift_nonterminal (nt : nonterminal) : aug_nonterminal :=
  Some nt.

Lemma end_marker_fresh_token (tok : token)
  : ~ end_marker = lift_token tok.
Proof.
  discriminate.
Qed.

Lemma fresh_start_fresh_nonterminal (nt : nonterminal)
  : ~ fresh_start = lift_nonterminal nt.
Proof.
  discriminate.
Qed.

Definition lift_symbol (sym : raw_symbol) : aug_symbol :=
  match sym with
  | symbol_terminal tok => symbol_terminal (lift_token tok)
  | symbol_nonterminal nt => symbol_nonterminal (lift_nonterminal nt)
  end.

Inductive aug_production : Set :=
  | aug_start
    : aug_production
  | aug_old (prod : production)
    : aug_production.

#[global]
Instance aug_production_hasEqDec
  : hasEqDec@{Set} aug_production.
Proof.
  red. decide equality; eapply eq_dec.
Defined.

Definition aug_lhs (prod : aug_production) : aug_nonterminal :=
  match prod with
  | aug_start => fresh_start
  | aug_old prod => lift_nonterminal (Grammar.lhs prod)
  end.

Definition aug_rhs (prod : aug_production) : list aug_symbol :=
  match prod with
  | aug_start => [symbol_nonterminal (lift_nonterminal Grammar.start); symbol_terminal end_marker]
  | aug_old prod => map lift_symbol (Grammar.rhs prod)
  end.

Definition all_aug_productions : list aug_production :=
  aug_start :: map aug_old Grammar.Production.all.

Lemma all_aug_productions_complete (prod : aug_production)
  : prod ∈ all_aug_productions.
Proof.
  destruct prod as [ | prod].
  - left. reflexivity.
  - right. rewrite in_map_iff. exists prod. split; [reflexivity | eapply Grammar.Production.all_complete].
Qed.

Lemma aug_start_not_in_old_productions
  : ~ aug_start ∈ map aug_old Grammar.Production.all.
Proof.
  intros IN. rewrite in_map_iff in IN. destruct IN as (prod & EQ & _). discriminate.
Qed.

Lemma aug_old_injective_on_all (prod1 : production) (prod2 : production)
  (IN1 : prod1 ∈ Grammar.Production.all)
  (IN2 : prod2 ∈ Grammar.Production.all)
  (EQ : aug_old prod1 = aug_old prod2)
  : prod1 = prod2.
Proof.
  inv EQ. reflexivity.
Qed.

Lemma all_aug_productions_no_dup
  : NoDup all_aug_productions.
Proof.
  unfold all_aug_productions. econs.
  - eapply aug_start_not_in_old_productions.
  - eapply NoDup_map_injective_on; [eapply aug_old_injective_on_all | eapply Grammar.Production.all_no_dup].
Qed.

Definition all_aug_tokens : list aug_token :=
  None :: map Some Grammar.Token.all.

Definition all_aug_nonterminals : list aug_nonterminal :=
  None :: map Some Grammar.Nonterminal.all.

Definition all_aug_symbols : list aug_symbol :=
  all_symbols all_aug_tokens all_aug_nonterminals.

Lemma all_aug_tokens_complete (tok : aug_token)
  : tok ∈ all_aug_tokens.
Proof.
  destruct tok as [tok | ].
  - right. rewrite in_map_iff. exists tok. split; [reflexivity | eapply Grammar.Token.all_complete].
  - left. reflexivity.
Qed.

Lemma all_aug_nonterminals_complete (nt : aug_nonterminal)
  : nt ∈ all_aug_nonterminals.
Proof.
  destruct nt as [nt | ].
  - right. rewrite in_map_iff. exists nt. split; [reflexivity | eapply Grammar.Nonterminal.all_complete].
  - left. reflexivity.
Qed.

Lemma all_aug_tokens_no_dup
  : NoDup all_aug_tokens.
Proof.
  unfold all_aug_tokens. econs.
  - intros IN. rewrite in_map_iff in IN. destruct IN as (tok & EQ & _). discriminate.
  - eapply NoDup_map_injective_on.
    + intros tok1 tok2 _ _ EQ. inv EQ. reflexivity.
    + eapply Grammar.Token.all_no_dup.
Qed.

Lemma all_aug_nonterminals_no_dup
  : NoDup all_aug_nonterminals.
Proof.
  unfold all_aug_nonterminals. econs.
  - intros IN. rewrite in_map_iff in IN. destruct IN as (nt & EQ & _). discriminate.
  - eapply NoDup_map_injective_on.
    + intros nt1 nt2 _ _ EQ. inv EQ. reflexivity.
    + eapply Grammar.Nonterminal.all_no_dup.
Qed.

Lemma all_aug_symbols_terminal_complete (tok : aug_token)
  : symbol_terminal tok ∈ all_aug_symbols.
Proof.
  unfold all_aug_symbols. eapply all_symbols_terminal_complete. eapply all_aug_tokens_complete.
Qed.

Lemma all_aug_symbols_nonterminal_complete (nt : aug_nonterminal)
  : symbol_nonterminal nt ∈ all_aug_symbols.
Proof.
  unfold all_aug_symbols. eapply all_symbols_nonterminal_complete. eapply all_aug_nonterminals_complete.
Qed.

Definition aug_symbol_wf (sym : aug_symbol) : Prop :=
  sym ∈ all_aug_symbols.

Lemma lift_symbol_wf (sym : raw_symbol)
  : aug_symbol_wf (lift_symbol sym).
Proof.
  destruct sym as [tok | nt]; [eapply all_aug_symbols_terminal_complete | eapply all_aug_symbols_nonterminal_complete].
Qed.

Definition aug_production_wf (prod : aug_production) : Prop :=
  forall sym, sym ∈ aug_rhs prod -> aug_symbol_wf sym.

Lemma aug_production_wf_all (prod : aug_production)
  : aug_production_wf prod.
Proof.
  destruct prod as [ | prod]; unfold aug_production_wf; simpl; intros sym IN.
  - destruct IN as [EQ | [EQ | []]]; subst sym; [eapply all_aug_symbols_nonterminal_complete | eapply all_aug_symbols_terminal_complete].
  - rewrite in_map_iff in IN. destruct IN as (raw & EQ & _). subst sym. eapply lift_symbol_wf.
Qed.

Definition aug_sentence (tokens : list token) : list aug_symbol :=
  map (fun tok : token => symbol_terminal (lift_token tok)) tokens ++ [symbol_terminal end_marker].

Definition lift_sentential (xs : list raw_symbol) : list aug_symbol :=
  map lift_symbol xs.

Lemma lift_sentence (tokens : list token)
  : lift_sentential (sentence tokens) = map (fun tok : token => symbol_terminal (lift_token tok)) tokens.
Proof.
  unfold lift_sentential, sentence. induction tokens as [ | tok tokens IH]; simpl; congruence.
Qed.

Definition aug_start_sentence : list aug_symbol :=
  [symbol_nonterminal fresh_start].

Inductive aug_derives1 : list aug_symbol -> list aug_symbol -> Prop :=
  | aug_derives1_intro (prod : aug_production) (prefix : list aug_symbol) (suffix : list aug_symbol)
    : aug_derives1 (prefix ++ symbol_nonterminal (aug_lhs prod) :: suffix) (prefix ++ aug_rhs prod ++ suffix).

Inductive aug_derives : list aug_symbol -> list aug_symbol -> Prop :=
  | aug_derives_refl (xs : list aug_symbol)
    : aug_derives xs xs
  | aug_derives_step (xs : list aug_symbol) (ys : list aug_symbol) (zs : list aug_symbol)
    (STEP : aug_derives1 xs ys)
    (REST : aug_derives ys zs)
    : aug_derives xs zs.

#[local] Hint Constructors aug_derives1 aug_derives : core.

Definition aug_in_language (tokens : list token) : Prop :=
  aug_derives aug_start_sentence (aug_sentence tokens).

Lemma lift_sentential_app (xs : list raw_symbol) (ys : list raw_symbol)
  : lift_sentential (xs ++ ys) = lift_sentential xs ++ lift_sentential ys.
Proof.
  unfold lift_sentential. rewrite map_app. reflexivity.
Qed.

Lemma lift_derives1 (xs : list raw_symbol) (ys : list raw_symbol)
  (STEP : derives1 xs ys)
  : aug_derives1 (lift_sentential xs) (lift_sentential ys).
Proof.
  inv STEP. unfold lift_sentential. rewrite !map_app. simpl. exact (aug_derives1_intro (aug_old prod) (map lift_symbol prefix) (map lift_symbol suffix)).
Qed.

Lemma lift_derives (xs : list raw_symbol) (ys : list raw_symbol)
  (DERIVES : derives xs ys)
  : aug_derives (lift_sentential xs) (lift_sentential ys).
Proof.
  induction DERIVES as [xs | xs ys zs STEP REST IH].
  - econs.
  - eapply aug_derives_step; [eapply lift_derives1; exact STEP | exact IH].
Qed.

Lemma aug_derives1_app_suffix (xs : list aug_symbol) (ys : list aug_symbol) (suffix : list aug_symbol)
  (STEP : aug_derives1 xs ys)
  : aug_derives1 (xs ++ suffix) (ys ++ suffix).
Proof.
  inv STEP.
  replace ((prefix ++ symbol_nonterminal (aug_lhs prod) :: suffix0) ++ suffix) with (prefix ++ symbol_nonterminal (aug_lhs prod) :: (suffix0 ++ suffix)) by (rewrite <- app_assoc; reflexivity).
  replace ((prefix ++ aug_rhs prod ++ suffix0) ++ suffix) with (prefix ++ aug_rhs prod ++ (suffix0 ++ suffix)) by (repeat rewrite <- app_assoc; reflexivity).
  exact (aug_derives1_intro prod prefix (suffix0 ++ suffix)).
Qed.

Lemma aug_derives_app_suffix (xs : list aug_symbol) (ys : list aug_symbol) (suffix : list aug_symbol)
  (DERIVES : aug_derives xs ys)
  : aug_derives (xs ++ suffix) (ys ++ suffix).
Proof.
  induction DERIVES as [xs | xs ys zs STEP REST IH].
  - econs.
  - eapply aug_derives_step; [eapply aug_derives1_app_suffix; exact STEP | exact IH].
Qed.

Lemma aug_derives1_app_prefix (xs : list aug_symbol) (ys : list aug_symbol) (prefix : list aug_symbol)
  (STEP : aug_derives1 xs ys)
  : aug_derives1 (prefix ++ xs) (prefix ++ ys).
Proof.
  inv STEP.
  replace (prefix ++ (prefix0 ++ symbol_nonterminal (aug_lhs prod) :: suffix)) with ((prefix ++ prefix0) ++ symbol_nonterminal (aug_lhs prod) :: suffix) by (rewrite app_assoc; reflexivity).
  replace (prefix ++ prefix0 ++ aug_rhs prod ++ suffix) with ((prefix ++ prefix0) ++ (aug_rhs prod ++ suffix)) by (symmetry; exact (app_assoc prefix prefix0 (aug_rhs prod ++ suffix))).
  exact (aug_derives1_intro prod (prefix ++ prefix0) suffix).
Qed.

Lemma aug_derives_app_prefix (xs : list aug_symbol) (ys : list aug_symbol) (prefix : list aug_symbol)
  (DERIVES : aug_derives xs ys)
  : aug_derives (prefix ++ xs) (prefix ++ ys).
Proof.
  induction DERIVES as [xs | xs ys zs STEP REST IH].
  - econs.
  - eapply aug_derives_step; [eapply aug_derives1_app_prefix; exact STEP | exact IH].
Qed.

Lemma aug_derives_app (xs1 : list aug_symbol) (ys1 : list aug_symbol) (xs2 : list aug_symbol) (ys2 : list aug_symbol)
  (DERIVES1 : aug_derives xs1 ys1)
  (DERIVES2 : aug_derives xs2 ys2)
  : aug_derives (xs1 ++ xs2) (ys1 ++ ys2).
Proof.
  induction DERIVES1 as [xs1 | xs1 mid ys1 STEP REST IH].
  - eapply aug_derives_app_prefix. exact DERIVES2.
  - eapply aug_derives_step; [eapply aug_derives1_app_suffix; exact STEP | exact IH].
Qed.

Theorem in_language_aug_in_language (tokens : list token)
  (LANG : in_language tokens)
  : aug_in_language tokens.
Proof.
  unfold aug_in_language, aug_sentence, aug_start_sentence.
  eapply aug_derives_step with (ys := [symbol_nonterminal (lift_nonterminal Grammar.start); symbol_terminal end_marker]).
  - exact (aug_derives1_intro aug_start [] []).
  - change ([symbol_nonterminal (lift_nonterminal Grammar.start); symbol_terminal end_marker]) with (lift_sentential [symbol_nonterminal Grammar.start] ++ [symbol_terminal end_marker]).
    rewrite <- lift_sentence. eapply aug_derives_app_suffix. unfold in_language in LANG. eapply lift_derives. exact LANG.
Qed.

Definition erase_aug_symbol (sym : aug_symbol) : list raw_symbol :=
  match sym with
  | symbol_terminal (Some tok) => [symbol_terminal tok]
  | symbol_terminal None => []
  | symbol_nonterminal (Some nt) => [symbol_nonterminal nt]
  | symbol_nonterminal None => [symbol_nonterminal Grammar.start]
  end.

Definition erase_aug_sentential (xs : list aug_symbol) : list raw_symbol :=
  flat_map erase_aug_symbol xs.

Lemma erase_aug_sentential_app (xs : list aug_symbol) (ys : list aug_symbol)
  : erase_aug_sentential (xs ++ ys) = erase_aug_sentential xs ++ erase_aug_sentential ys.
Proof.
  unfold erase_aug_sentential. rewrite flat_map_app. reflexivity.
Qed.

Lemma erase_lift_symbol (sym : raw_symbol)
  : erase_aug_symbol (lift_symbol sym) = [sym].
Proof.
  destruct sym; reflexivity.
Qed.

Lemma erase_lift_sentential (xs : list raw_symbol)
  : erase_aug_sentential (lift_sentential xs) = xs.
Proof.
  unfold erase_aug_sentential, lift_sentential. induction xs as [ | sym xs IH]; simpl; [reflexivity | ]. rewrite erase_lift_symbol. rewrite IH. reflexivity.
Qed.

Lemma erase_aug_rhs (prod : aug_production)
  : erase_aug_sentential (aug_rhs prod) = match prod with aug_start => [symbol_nonterminal Grammar.start] | aug_old prod => Grammar.rhs prod end.
Proof.
  destruct prod as [ | prod]; simpl.
  - reflexivity.
  - eapply erase_lift_sentential.
Qed.

Lemma erase_aug_derives1 (xs : list aug_symbol) (ys : list aug_symbol)
  (STEP : aug_derives1 xs ys)
  : derives (erase_aug_sentential xs) (erase_aug_sentential ys).
Proof.
  inv STEP. rewrite !erase_aug_sentential_app. simpl. rewrite erase_aug_rhs. destruct prod as [ | prod].
  - econs.
  - eapply derives_step; [exact (derives1_intro prod (erase_aug_sentential prefix) (erase_aug_sentential suffix)) | econs].
Qed.

Lemma erase_aug_derives (xs : list aug_symbol) (ys : list aug_symbol)
  (DERIVES : aug_derives xs ys)
  : derives (erase_aug_sentential xs) (erase_aug_sentential ys).
Proof.
  induction DERIVES as [xs | xs ys zs STEP REST IH].
  - econs.
  - eapply derives_trans; [eapply erase_aug_derives1; exact STEP | exact IH].
Qed.

Lemma erase_aug_start_sentence
  : erase_aug_sentential aug_start_sentence = [symbol_nonterminal Grammar.start].
Proof.
  reflexivity.
Qed.

Lemma erase_aug_sentence (tokens : list token)
  : erase_aug_sentential (aug_sentence tokens) = sentence tokens.
Proof.
  unfold erase_aug_sentential, aug_sentence, sentence. induction tokens as [ | tok tokens IH]; simpl; [reflexivity | ]. rewrite IH. reflexivity.
Qed.

Theorem aug_in_language_in_language (tokens : list token)
  (LANG : aug_in_language tokens)
  : in_language tokens.
Proof.
  unfold aug_in_language in LANG. unfold in_language. pose proof (erase_aug_derives aug_start_sentence (aug_sentence tokens) LANG) as DERIVES. rewrite erase_aug_start_sentence in DERIVES. rewrite erase_aug_sentence in DERIVES. exact DERIVES.
Qed.

Record item : Set :=
  mkItem
  { item_prod : aug_production
  ; item_dot : nat
  }.

#[global]
Instance item_hasEqDec
  : hasEqDec@{Set} item.
Proof.
  intros [prod1 dot1] [prod2 dot2].
  destruct (eq_dec prod1 prod2) as [EQ_prod | NE_prod].
  - subst prod2. destruct (Nat.eq_dec dot1 dot2) as [EQ_dot | NE_dot].
    + subst dot2. left. reflexivity.
    + right. intros EQ. inv EQ. contradiction.
  - right. intros EQ. inv EQ. contradiction.
Defined.

Definition item_rhs (it : item) : list aug_symbol :=
  aug_rhs it.(item_prod).

Definition item_wf (it : item) : Prop :=
  it.(item_dot) <= length (item_rhs it).

Definition before_dot (it : item) : list aug_symbol :=
  firstn it.(item_dot) (item_rhs it).

Definition after_dot (it : item) : list aug_symbol :=
  skipn it.(item_dot) (item_rhs it).

Definition next_symbol (it : item) : option aug_symbol :=
  nth_error (item_rhs it) it.(item_dot).

Definition advance (it : item) : item :=
  mkItem it.(item_prod) (S it.(item_dot)).

Definition is_final (it : item) : bool :=
  Nat.eqb it.(item_dot) (length (item_rhs it)).

Definition is_initial_item (it : item) : bool :=
  match it.(item_prod), it.(item_dot) with
  | aug_start, O => true
  | _, _ => false
  end.

Definition is_kernel_item (it : item) : bool :=
  match it.(item_prod), it.(item_dot) with
  | aug_start, O => true
  | _, O => false
  | _, S _ => true
  end.

Definition is_nonkernel_item (it : item) : bool :=
  negb (is_kernel_item it).

Lemma is_kernel_or_nonkernel (it : item)
  : is_kernel_item it = true \/ is_nonkernel_item it = true.
Proof.
  unfold is_nonkernel_item. destruct (is_kernel_item it); [left; reflexivity | right; reflexivity].
Qed.

Definition items_of_production (prod : aug_production) : list item :=
  map (mkItem prod) (seq 0 (S (length (aug_rhs prod)))).

Definition all_items : list item :=
  flat_map items_of_production all_aug_productions.

Lemma in_seq_0_succ_length (dot : nat) (len : nat)
  (LE : dot <= len)
  : dot ∈ seq 0 (S len).
Proof.
  rewrite in_seq. lia.
Qed.

Lemma items_of_production_complete (prod : aug_production) (dot : nat)
  (LE : dot <= length (aug_rhs prod))
  : mkItem prod dot ∈ items_of_production prod.
Proof.
  unfold items_of_production. rewrite in_map_iff. exists dot. split; [reflexivity | eapply in_seq_0_succ_length; exact LE].
Qed.

Lemma all_items_complete (it : item)
  (WF : item_wf it)
  : it ∈ all_items.
Proof.
  destruct it as [prod dot]. unfold all_items. rewrite in_flat_map.
  exists prod. split.
  - eapply all_aug_productions_complete.
  - unfold item_wf, item_rhs in WF. simpl in WF. eapply items_of_production_complete. exact WF.
Qed.

Lemma next_symbol_some_advance_wf (it : item) (sym : aug_symbol)
  (NEXT : next_symbol it = Some sym)
  : item_wf (advance it).
Proof.
  destruct it as [prod dot]. unfold next_symbol, item_wf, advance, item_rhs in *. simpl in *.
  assert (LT : dot < length (aug_rhs prod)).
  { rewrite <- nth_error_Some. rewrite NEXT. discriminate. }
  lia.
Qed.

Lemma is_final_true_iff (it : item)
  : is_final it = true <-> it.(item_dot) = length (item_rhs it).
Proof.
  unfold is_final. eapply Nat.eqb_eq.
Qed.

Lemma is_final_false_next_symbol (it : item)
  (WF : item_wf it)
  (NOT_FINAL : is_final it = false)
  : exists sym, next_symbol it = Some sym.
Proof.
  unfold is_final in NOT_FINAL. rewrite Nat.eqb_neq in NOT_FINAL.
  unfold item_wf in WF. unfold next_symbol.
  destruct (nth_error (item_rhs it) (item_dot it)) as [sym | ] eqn: OBS.
  - exists sym. reflexivity.
  - rewrite nth_error_None in OBS. lia.
Qed.

Definition subsetb {A : Type} `{A_hasEqDec : hasEqDec A} (xs : list A) (ys : list A) : bool :=
  forallb (fun x : A => mem x ys) xs.

Definition same_setb {A : Type} `{A_hasEqDec : hasEqDec A} (xs : list A) (ys : list A) : bool :=
  subsetb xs ys && subsetb ys xs.

Lemma subsetb_sound {A : Type} `{A_hasEqDec : hasEqDec A} (xs : list A) (ys : list A)
  (SUBSET : subsetb xs ys = true)
  : forall x : A, x ∈ xs -> x ∈ ys.
Proof.
  unfold subsetb in SUBSET. rewrite forallb_forall in SUBSET.
  intros x IN. pose proof (SUBSET x IN) as MEM. rewrite mem_true_iff in MEM. exact MEM.
Qed.

Lemma subsetb_complete {A : Type} `{A_hasEqDec : hasEqDec A} (xs : list A) (ys : list A)
  (SUBSET : forall x : A, x ∈ xs -> x ∈ ys)
  : subsetb xs ys = true.
Proof.
  unfold subsetb. rewrite forallb_forall. intros x IN. rewrite mem_true_iff. eapply SUBSET. exact IN.
Qed.

Definition fin_list (n : nat) : list (Fin.t n) :=
  V.to_list (V.fromMap (fun i : Fin.t n => i)).

Lemma fin_list_complete (n : nat) (i : Fin.t n)
  : i ∈ fin_list n.
Proof.
  unfold fin_list. rewrite V.in_to_list_iff. exists i. rewrite V.fromMap_spec. reflexivity.
Qed.

Definition nullable_symbol_under (nts : list nonterminal) (sym : raw_symbol) : bool :=
  match sym with
  | symbol_terminal _ => false
  | symbol_nonterminal nt => @mem nonterminal nonterminal_hasEqDec nt nts
  end.

Definition nullable_rhs_under (nts : list nonterminal) (rhs : list raw_symbol) : bool :=
  forallb (nullable_symbol_under nts) rhs.

Definition nullable_closedb (nts : list nonterminal) : bool :=
  forallb (fun prod : production => if nullable_rhs_under nts (Grammar.rhs prod) then @mem nonterminal nonterminal_hasEqDec (Grammar.lhs prod) nts else true) Grammar.Production.all.

Definition nullable_nts : list nonterminal :=
  filter (fun nt : nonterminal => forallb (fun nts : list nonterminal => if nullable_closedb nts then @mem nonterminal nonterminal_hasEqDec nt nts else true) (powerset Grammar.Nonterminal.all)) Grammar.Nonterminal.all.

Definition nullable_ntb (nt : nonterminal) : bool :=
  @mem nonterminal nonterminal_hasEqDec nt nullable_nts.

Definition nullable_lfp : ensemble nonterminal :=
  fun nt => nt ∈ Grammar.Nonterminal.all /\ forall candidate, candidate ∈ powerset Grammar.Nonterminal.all -> nullable_closedb candidate = true -> nt ∈ candidate.

Lemma nullable_nts_sim
  : nullable_nts =~= nullable_lfp.
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros nt. unfold nullable_nts, nullable_lfp. rewrite filter_In. split.
  - intros [IN_all CLOSED]. split; [exact IN_all | ].
    intros candidate IN_candidate CLOSED_candidate. rewrite forallb_forall in CLOSED. pose proof (CLOSED candidate IN_candidate) as MEM. rewrite CLOSED_candidate in MEM. rewrite mem_true_iff in MEM. exact MEM.
  - intros [IN_all CLOSED]. split; [exact IN_all | ].
    rewrite forallb_forall. intros candidate IN_candidate. destruct (nullable_closedb candidate) eqn: CLOSED_candidate.
    + rewrite mem_true_iff. eapply CLOSED; [exact IN_candidate | exact CLOSED_candidate].
    + reflexivity.
Qed.

Definition nullable_symbol_lfp (sym : raw_symbol) : Prop :=
  match sym with
  | symbol_terminal _ => False
  | symbol_nonterminal nt => nt \in nullable_lfp
  end.

Definition nullable_rhs_lfp (rhs : list raw_symbol) : Prop :=
  forall sym, sym ∈ rhs -> nullable_symbol_lfp sym.

Lemma nullable_rhs_under_complete (candidate : list nonterminal) (rhs : list raw_symbol)
  (COMPLETE : forall nt, nt \in nullable_lfp -> nt ∈ candidate)
  (NULLABLE : nullable_rhs_lfp rhs)
  : nullable_rhs_under candidate rhs = true.
Proof.
  unfold nullable_rhs_under. rewrite forallb_forall. intros sym IN. pose proof (NULLABLE sym IN) as NULLABLE_sym.
  destruct sym as [tok | nt]; simpl in *; [contradiction | ].
  rewrite mem_true_iff. eapply COMPLETE. exact NULLABLE_sym.
Qed.

Lemma nullable_lfp_step (prod : production)
  (NULLABLE_RHS : nullable_rhs_lfp (Grammar.rhs prod))
  : Grammar.lhs prod \in nullable_lfp.
Proof.
  split.
  - eapply Grammar.Nonterminal.all_complete.
  - intros candidate IN_candidate CLOSED_candidate.
    pose proof (CLOSED_candidate) as CLOSED_candidate_eq.
    unfold nullable_closedb in CLOSED_candidate. rewrite forallb_forall in CLOSED_candidate.
    pose proof (CLOSED_candidate prod (Grammar.Production.all_complete prod)) as CLOSED_prod.
    replace (nullable_rhs_under candidate (Grammar.rhs prod)) with true in CLOSED_prod.
    + rewrite mem_true_iff in CLOSED_prod. exact CLOSED_prod.
    + symmetry. eapply nullable_rhs_under_complete.
      * intros nt IN_lfp. destruct IN_lfp as [_ CLOSED]. eapply CLOSED; [exact IN_candidate | exact CLOSED_candidate_eq].
      * exact NULLABLE_RHS.
Qed.

Lemma nullable_ntb_iff_lfp (nt : nonterminal)
  : nullable_ntb nt = true <-> nt \in nullable_lfp.
Proof.
  unfold nullable_ntb. rewrite mem_true_iff. pose proof (nullable_nts_sim) as SIM. rewrite list_corresponds_to_finite_ensemble_iff in SIM. exact (SIM nt).
Qed.

Notation first_pair := (nonterminal * token)%type.

Definition all_first_pairs : list first_pair :=
  product Grammar.Nonterminal.all Grammar.Token.all.

Definition first_symbol_under (candidate : list first_pair) (sym : raw_symbol) (tok : token) : bool :=
  match sym with
  | symbol_terminal tok0 => eqb tok0 tok
  | symbol_nonterminal nt => @mem first_pair _ (nt, tok) candidate
  end.

Fixpoint first_rhs_under (candidate : list first_pair) (rhs : list raw_symbol) (tok : token) {struct rhs} : bool :=
  match rhs with
  | [] => false
  | sym :: rhs' => first_symbol_under candidate sym tok || match sym with symbol_terminal _ => false | symbol_nonterminal nt => nullable_ntb nt && first_rhs_under candidate rhs' tok end
  end.

Definition first_pairs_closedb (candidate : list first_pair) : bool :=
  forallb (fun prod : production => forallb (fun tok : token => if first_rhs_under candidate (Grammar.rhs prod) tok then @mem first_pair _ (Grammar.lhs prod, tok) candidate else true) Grammar.Token.all) Grammar.Production.all.

Definition first_pairs : list first_pair :=
  filter (fun pair : first_pair => forallb (fun candidate : list first_pair => if first_pairs_closedb candidate then @mem first_pair _ pair candidate else true) (powerset all_first_pairs)) all_first_pairs.

Definition first_pair_lfp : ensemble first_pair :=
  fun pair => pair ∈ all_first_pairs /\ forall candidate, candidate ∈ powerset all_first_pairs -> first_pairs_closedb candidate = true -> pair ∈ candidate.

Lemma first_pairs_sim
  : first_pairs =~= first_pair_lfp.
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros pair. unfold first_pairs, first_pair_lfp. rewrite filter_In. split.
  - intros [IN_all CLOSED]. split; [exact IN_all | ].
    intros candidate IN_candidate CLOSED_candidate. rewrite forallb_forall in CLOSED. pose proof (CLOSED candidate IN_candidate) as MEM. rewrite CLOSED_candidate in MEM. rewrite mem_true_iff in MEM. exact MEM.
  - intros [IN_all CLOSED]. split; [exact IN_all | ].
    rewrite forallb_forall. intros candidate IN_candidate. destruct (first_pairs_closedb candidate) eqn: CLOSED_candidate.
    + rewrite mem_true_iff. eapply CLOSED; [exact IN_candidate | exact CLOSED_candidate].
    + reflexivity.
Qed.

Fixpoint first_rhs_lfp (rhs : list raw_symbol) (tok : token) {struct rhs} : Prop :=
  match rhs with
  | [] => False
  | symbol_terminal tok0 :: _ => tok0 = tok
  | symbol_nonterminal nt :: rhs' => (nt, tok) \in first_pair_lfp \/ (nt \in nullable_lfp /\ first_rhs_lfp rhs' tok)
  end.

Lemma first_rhs_under_complete (candidate : list first_pair) (rhs : list raw_symbol) (tok : token)
  (COMPLETE : forall nt, forall tok, (nt, tok) \in first_pair_lfp -> (nt, tok) ∈ candidate)
  (FIRST : first_rhs_lfp rhs tok)
  : first_rhs_under candidate rhs tok = true.
Proof.
  revert tok FIRST. induction rhs as [ | [tok0 | nt] rhs IH]; simpl; intros tok FIRST; try contradiction.
  - rewrite orb_false_r. rewrite eqb_eq. exact FIRST.
  - destruct FIRST as [FIRST | [NULLABLE FIRST]].
    + rewrite orb_true_iff. left. unfold first_symbol_under. rewrite mem_true_iff. eapply COMPLETE. exact FIRST.
    + rewrite orb_true_iff. right. rewrite andb_true_iff. split.
      * rewrite nullable_ntb_iff_lfp. exact NULLABLE.
      * eapply IH. exact FIRST.
Qed.

Lemma first_pair_lfp_step (prod : production) (tok : token)
  (FIRST_RHS : first_rhs_lfp (Grammar.rhs prod) tok)
  : (Grammar.lhs prod, tok) \in first_pair_lfp.
Proof.
  split.
  - eapply product_complete; [eapply Grammar.Nonterminal.all_complete | eapply Grammar.Token.all_complete].
  - intros candidate IN_candidate CLOSED_candidate.
    pose proof (CLOSED_candidate) as CLOSED_candidate_eq.
    unfold first_pairs_closedb in CLOSED_candidate. rewrite forallb_forall in CLOSED_candidate.
    pose proof (CLOSED_candidate prod (Grammar.Production.all_complete prod)) as CLOSED_prod.
    rewrite forallb_forall in CLOSED_prod. pose proof (CLOSED_prod tok (Grammar.Token.all_complete tok)) as CLOSED_tok.
    replace (first_rhs_under candidate (Grammar.rhs prod) tok) with true in CLOSED_tok.
    + rewrite mem_true_iff in CLOSED_tok. exact CLOSED_tok.
    + symmetry. eapply first_rhs_under_complete.
      * intros nt tok0 IN_lfp. destruct IN_lfp as [_ CLOSED]. eapply CLOSED; [exact IN_candidate | exact CLOSED_candidate_eq].
      * exact FIRST_RHS.
Qed.

Definition first_tokens_of_nonterminal' (nt : nonterminal) : list token :=
  filter (fun tok : token => @mem first_pair _ (nt, tok) first_pairs) Grammar.Token.all.

Definition first_tokens_of_nonterminal (nt : nonterminal) : ensemble token :=
  fun tok => (nt, tok) \in first_pair_lfp.

Lemma first_tokens_of_nonterminal_sim (nt : nonterminal)
  : first_tokens_of_nonterminal' nt =~= first_tokens_of_nonterminal nt.
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros tok. unfold first_tokens_of_nonterminal', first_tokens_of_nonterminal. rewrite filter_In. split.
  - intros [_ IN]. rewrite mem_true_iff in IN. pose proof (first_pairs_sim) as SIM. rewrite list_corresponds_to_finite_ensemble_iff in SIM. eapply SIM. exact IN.
  - intros IN. split; [eapply Grammar.Token.all_complete | ]. rewrite mem_true_iff. pose proof (first_pairs_sim) as SIM. rewrite list_corresponds_to_finite_ensemble_iff in SIM. eapply SIM. exact IN.
Qed.

Lemma first_rhs_under_first_pairs_iff (rhs : list raw_symbol) (tok : token)
  : first_rhs_under first_pairs rhs tok = true <-> first_rhs_lfp rhs tok.
Proof.
  split.
  - revert tok. induction rhs as [ | [tok0 | nt] rhs IH]; simpl; intros tok FIRST; try discriminate.
    + rewrite orb_true_iff in FIRST. destruct FIRST as [FIRST | FIRST]; [unfold first_symbol_under in FIRST; rewrite eqb_eq in FIRST; exact FIRST | discriminate].
    + rewrite orb_true_iff in FIRST. destruct FIRST as [FIRST | REST].
      * left. unfold first_symbol_under in FIRST. rewrite mem_true_iff in FIRST. pose proof (first_pairs_sim) as SIM. rewrite list_corresponds_to_finite_ensemble_iff in SIM. eapply SIM. exact FIRST.
      * rewrite andb_true_iff in REST. destruct REST as [NULLABLE FIRST]. right. split; [rewrite <- nullable_ntb_iff_lfp; exact NULLABLE | eapply IH; exact FIRST].
  - intros FIRST. eapply first_rhs_under_complete.
    + intros nt tok0 IN_lfp. pose proof (first_pairs_sim) as SIM. rewrite list_corresponds_to_finite_ensemble_iff in SIM. eapply (proj2 (SIM (nt, tok0))). exact IN_lfp.
    + exact FIRST.
Qed.

Definition nullable_aug_nonterminalb (nt : aug_nonterminal) : bool :=
  match nt with
  | None => false
  | Some nt => nullable_ntb nt
  end.

Definition production_starts_with (nt : aug_nonterminal) (prod : aug_production) : bool :=
  eqb (aug_lhs prod) nt.

Definition productions_for (nt : aug_nonterminal) : list aug_production :=
  filter (production_starts_with nt) all_aug_productions.

Definition initial_item_of_production (prod : aug_production) : item :=
  mkItem prod 0.

Definition item_closure_successors (it : item) : list item :=
  match next_symbol it with
  | Some (symbol_nonterminal nt) => map initial_item_of_production (productions_for nt)
  | _ => []
  end.

Definition item_closure_expand (items : list item) : list item :=
  nodup eq_dec (items ++ flat_map item_closure_successors items).

Lemma item_closure_expand_monotone (items1 : list item) (items2 : list item) (it : item)
  (SUBSET : forall item, item ∈ items1 -> item ∈ items2)
  (IN : it ∈ item_closure_expand items1)
  : it ∈ item_closure_expand items2.
Proof.
  unfold item_closure_expand in *. rewrite nodup_In in *. rewrite in_app_iff in *. destruct IN as [IN | IN].
  - left. eapply SUBSET. exact IN.
  - right. rewrite in_flat_map in IN. destruct IN as (src & IN_src & IN_succ). rewrite in_flat_map. exists src. split; [eapply SUBSET; exact IN_src | exact IN_succ].
Qed.

Definition itemset_closedb (seed : list item) (candidate : list item) : bool :=
  @subsetb item item_hasEqDec seed candidate && forallb (fun it : item => @subsetb item item_hasEqDec (item_closure_successors it) candidate) candidate.

Definition lr0_closure (seed : list item) : list item :=
  filter (fun it : item => forallb (fun candidate : list item => if itemset_closedb seed candidate then @mem item item_hasEqDec it candidate else true) (powerset all_items)) all_items.

Definition item_closure (seed : list item) : ensemble item :=
  fun it => it ∈ all_items /\ forall candidate, candidate ∈ powerset all_items -> itemset_closedb seed candidate = true -> it ∈ candidate.

Lemma lr0_closure_sim (seed : list item)
  : lr0_closure seed =~= item_closure seed.
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros it. unfold lr0_closure, item_closure. rewrite filter_In. split.
  - intros [IN_all CLOSED]. split; [exact IN_all | ].
    intros candidate IN_candidate CLOSED_candidate. rewrite forallb_forall in CLOSED. pose proof (CLOSED candidate IN_candidate) as MEM. rewrite CLOSED_candidate in MEM. rewrite mem_true_iff in MEM. exact MEM.
  - intros [IN_all CLOSED]. split; [exact IN_all | ].
    rewrite forallb_forall. intros candidate IN_candidate. destruct (itemset_closedb seed candidate) eqn: CLOSED_candidate.
    + rewrite mem_true_iff. eapply CLOSED; [exact IN_candidate | exact CLOSED_candidate].
    + reflexivity.
Qed.

Theorem lr0_closure_sound (seed : list item) (it : item)
  (IN : it ∈ lr0_closure seed)
  : it \in item_closure seed.
Proof.
  pose proof (lr0_closure_sim seed) as SIM. rewrite list_corresponds_to_finite_ensemble_iff in SIM. eapply SIM. exact IN.
Qed.

Theorem lr0_closure_complete (seed : list item) (it : item)
  (IN : it \in item_closure seed)
  : it ∈ lr0_closure seed.
Proof.
  pose proof (lr0_closure_sim seed) as SIM. rewrite list_corresponds_to_finite_ensemble_iff in SIM. eapply SIM. exact IN.
Qed.

Lemma item_closure_seed (seed : list item) (it : item)
  (IN_all : it ∈ all_items)
  (IN_seed : it ∈ seed)
  : it \in item_closure seed.
Proof.
  split; [exact IN_all | ].
  intros candidate _ CLOSED. unfold itemset_closedb in CLOSED. rewrite andb_true_iff in CLOSED. destruct CLOSED as [SUBSET _].
  eapply subsetb_sound; [exact SUBSET | exact IN_seed].
Qed.

Lemma item_closure_successors_in_all_items (it : item) (succ : item)
  (IN : succ ∈ item_closure_successors it)
  : succ ∈ all_items.
Proof.
  unfold item_closure_successors in IN. destruct (next_symbol it) as [[tok | nt] | ] eqn: NEXT; try contradiction.
  rewrite in_map_iff in IN. destruct IN as (prod & EQ & IN_prod). subst succ.
  eapply all_items_complete. unfold item_wf, initial_item_of_production, item_rhs. simpl. lia.
Qed.

Lemma item_closure_step (seed : list item) (it : item) (succ : item)
  (IN : it \in item_closure seed)
  (SUCC : succ ∈ item_closure_successors it)
  : succ \in item_closure seed.
Proof.
  destruct IN as [IN_all CLOSED]. split.
  - eapply item_closure_successors_in_all_items. exact SUCC.
  - intros candidate IN_candidate CLOSED_candidate.
    pose proof (CLOSED candidate IN_candidate CLOSED_candidate) as IN_candidate_it.
    unfold itemset_closedb in CLOSED_candidate. rewrite andb_true_iff in CLOSED_candidate. destruct CLOSED_candidate as [_ CLOSED_steps].
    rewrite forallb_forall in CLOSED_steps. pose proof (CLOSED_steps it IN_candidate_it) as SUBSET.
    eapply subsetb_sound; [exact SUBSET | exact SUCC].
Qed.

Theorem lr0_closure_seed_member (seed : list item) (it : item)
  (SEED_ALL : forall item, item ∈ seed -> item ∈ all_items)
  (IN : it ∈ seed)
  : it ∈ lr0_closure seed.
Proof.
  eapply lr0_closure_complete. eapply item_closure_seed; [eapply SEED_ALL; exact IN | exact IN].
Qed.

Theorem lr0_closure_step_member (seed : list item) (it : item) (succ : item)
  (IN : it ∈ lr0_closure seed)
  (SUCC : succ ∈ item_closure_successors it)
  : succ ∈ lr0_closure seed.
Proof.
  eapply lr0_closure_complete. eapply item_closure_step; [eapply lr0_closure_sound; exact IN | exact SUCC].
Qed.

Theorem item_closure_idempotent_iff (seed : list item) (it : item)
  (SEED_ALL : forall item, item ∈ seed -> item ∈ all_items)
  : it \in item_closure (lr0_closure seed) <-> it \in item_closure seed.
Proof.
  split.
  - intros IN. destruct IN as [IN_all CLOSED]. split; [exact IN_all | ].
    intros candidate IN_candidate CLOSED_candidate. eapply CLOSED.
    + exact IN_candidate.
    + unfold itemset_closedb. rewrite andb_true_iff. split.
      * eapply subsetb_complete. intros mid IN_mid. eapply lr0_closure_sound in IN_mid. destruct IN_mid as [_ CLOSED_mid]. eapply CLOSED_mid; [exact IN_candidate | exact CLOSED_candidate].
      * unfold itemset_closedb in CLOSED_candidate. rewrite andb_true_iff in CLOSED_candidate. exact (proj2 CLOSED_candidate).
  - intros IN. destruct IN as [IN_all CLOSED]. split; [exact IN_all | ].
    intros candidate IN_candidate CLOSED_candidate. eapply CLOSED.
    + exact IN_candidate.
    + unfold itemset_closedb. rewrite andb_true_iff. split.
      * eapply subsetb_complete. intros seed_item IN_seed_item. unfold itemset_closedb in CLOSED_candidate. rewrite andb_true_iff in CLOSED_candidate. destruct CLOSED_candidate as [SUBSET _]. eapply subsetb_sound; [exact SUBSET | ]. eapply lr0_closure_seed_member; [exact SEED_ALL | exact IN_seed_item].
      * unfold itemset_closedb in CLOSED_candidate. rewrite andb_true_iff in CLOSED_candidate. exact (proj2 CLOSED_candidate).
Qed.

Definition advances_on_symbol (sym : aug_symbol) (it : item) : list item :=
  match next_symbol it with
  | Some sym' => if eqb sym sym' then [advance it] else []
  | None => []
  end.

Definition item_advance_on_symbol (items : list item) (sym : aug_symbol) (it : item) : Prop :=
  exists src, src ∈ items /\ next_symbol src = Some sym /\ it = advance src.

Lemma advances_on_symbol_sound (sym : aug_symbol) (src : item) (it : item)
  (IN : it ∈ advances_on_symbol sym src)
  : next_symbol src = Some sym /\ it = advance src.
Proof.
  unfold advances_on_symbol in IN. destruct (next_symbol src) as [sym' | ] eqn: NEXT; try contradiction. destruct (eqb sym sym') eqn: EQ; simpl in IN; try contradiction.
  destruct IN as [EQ_it | []]. subst it. rewrite eqb_eq in EQ. subst sym'. split; reflexivity.
Qed.

Lemma advances_on_symbol_complete (sym : aug_symbol) (src : item)
  (NEXT : next_symbol src = Some sym)
  : advance src ∈ advances_on_symbol sym src.
Proof.
  unfold advances_on_symbol. rewrite NEXT. replace (eqb sym sym) with true by (symmetry; rewrite eqb_eq; reflexivity). left. reflexivity.
Qed.

Lemma flat_map_advances_on_symbol_sound (items : list item) (sym : aug_symbol) (it : item)
  (IN : it ∈ flat_map (advances_on_symbol sym) items)
  : item_advance_on_symbol items sym it.
Proof.
  rewrite in_flat_map in IN. destruct IN as (src & IN_src & IN_adv). pose proof (advances_on_symbol_sound sym src it IN_adv) as [NEXT EQ]. exists src. splits; [exact IN_src | exact NEXT | exact EQ].
Qed.

Lemma flat_map_advances_on_symbol_complete (items : list item) (sym : aug_symbol) (src : item)
  (IN : src ∈ items)
  (NEXT : next_symbol src = Some sym)
  : advance src ∈ flat_map (advances_on_symbol sym) items.
Proof.
  rewrite in_flat_map. exists src. split; [exact IN | eapply advances_on_symbol_complete; exact NEXT].
Qed.

Definition lr0_goto (items : list item) (sym : aug_symbol) : list item :=
  lr0_closure (flat_map (advances_on_symbol sym) items).

Definition item_goto (items : list item) (sym : aug_symbol) : ensemble item :=
  item_closure (flat_map (advances_on_symbol sym) items).

Theorem lr0_goto_sim (items : list item) (sym : aug_symbol)
  : lr0_goto items sym =~= item_goto items sym.
Proof.
  eapply lr0_closure_sim.
Qed.

Theorem lr0_goto_sound (items : list item) (sym : aug_symbol) (it : item)
  (IN : it ∈ lr0_goto items sym)
  : it \in item_goto items sym.
Proof.
  pose proof (lr0_goto_sim items sym) as SIM. rewrite list_corresponds_to_finite_ensemble_iff in SIM. eapply SIM. exact IN.
Qed.

Theorem lr0_goto_complete (items : list item) (sym : aug_symbol) (it : item)
  (IN : it \in item_goto items sym)
  : it ∈ lr0_goto items sym.
Proof.
  pose proof (lr0_goto_sim items sym) as SIM. rewrite list_corresponds_to_finite_ensemble_iff in SIM. eapply SIM. exact IN.
Qed.

Definition itemset_emptyb (items : list item) : bool :=
  match items with
  | [] => true
  | _ :: _ => false
  end.

Definition state : Set :=
  list item.

#[global]
Instance state_hasEqDec
  : hasEqDec@{Set} state.
Proof.
  eapply list_hasEqDec. exact item_hasEqDec.
Defined.

Definition start_item : item :=
  mkItem aug_start 0.

Definition start_state : state :=
  lr0_closure [start_item].

Definition all_lr0_states : list state :=
  filter (fun st : state => @same_setb item item_hasEqDec (lr0_closure st) st) (powerset all_items).

Definition lr0_next (st : state) (sym : aug_symbol) : option state :=
  let target := lr0_goto st sym in
  if itemset_emptyb target then None else Some target.

Definition lr0_transition : Set :=
  (state * aug_symbol * state)%type.

Definition lr0_transitions : list lr0_transition :=
  flat_map (fun st : state => flat_map (fun sym : aug_symbol => match lr0_next st sym with Some st' => [(st, sym, st')] | None => [] end) all_aug_symbols) all_lr0_states.

Definition lr0_state_successors (st : state) : list state :=
  flat_map (fun sym : aug_symbol => match lr0_next st sym with Some st' => [st'] | None => [] end) all_aug_symbols.

Definition lr0_state_saturation_closedb (candidate : list state) : bool :=
  @mem state state_hasEqDec start_state candidate && forallb (fun st : state => if @mem state state_hasEqDec st candidate then @subsetb state state_hasEqDec (lr0_state_successors st) candidate else true) all_lr0_states.

Definition lr0_reachable_states : list state :=
  filter (fun st : state => forallb (fun candidate : list state => if lr0_state_saturation_closedb candidate then @mem state state_hasEqDec st candidate else true) (powerset all_lr0_states)) all_lr0_states.

Definition lr0_reachable_state : ensemble state :=
  fun st => st ∈ all_lr0_states /\ forall candidate, candidate ∈ powerset all_lr0_states -> lr0_state_saturation_closedb candidate = true -> st ∈ candidate.

Lemma lr0_reachable_states_sim
  : lr0_reachable_states =~= lr0_reachable_state.
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros st. unfold lr0_reachable_states, lr0_reachable_state. rewrite filter_In. split.
  - intros [IN_all CLOSED]. split; [exact IN_all | ].
    intros candidate IN_candidate CLOSED_candidate. rewrite forallb_forall in CLOSED. pose proof (CLOSED candidate IN_candidate) as MEM. rewrite CLOSED_candidate in MEM. rewrite mem_true_iff in MEM. exact MEM.
  - intros [IN_all CLOSED]. split; [exact IN_all | ].
    rewrite forallb_forall. intros candidate IN_candidate. destruct (lr0_state_saturation_closedb candidate) eqn: CLOSED_candidate.
    + rewrite mem_true_iff. eapply CLOSED; [exact IN_candidate | exact CLOSED_candidate].
    + reflexivity.
Qed.

Lemma lr0_state_successors_sound (st : state) (st' : state)
  (IN : st' ∈ lr0_state_successors st)
  : exists sym, sym ∈ all_aug_symbols /\ lr0_next st sym = Some st'.
Proof.
  unfold lr0_state_successors in IN. rewrite in_flat_map in IN. destruct IN as (sym & IN_sym & IN_target). destruct (lr0_next st sym) as [target | ] eqn: NEXT; simpl in IN_target; try contradiction.
  destruct IN_target as [EQ | []]. subst st'. exists sym. split; [exact IN_sym | exact NEXT].
Qed.

Lemma lr0_state_successors_complete (st : state) (sym : aug_symbol) (st' : state)
  (IN_sym : sym ∈ all_aug_symbols)
  (NEXT : lr0_next st sym = Some st')
  : st' ∈ lr0_state_successors st.
Proof.
  unfold lr0_state_successors. rewrite in_flat_map. exists sym. split; [exact IN_sym | ]. rewrite NEXT. left. reflexivity.
Qed.

Lemma lr0_transitions_sound (src : state) (sym : aug_symbol) (tgt : state)
  (IN : (src, sym, tgt) ∈ lr0_transitions)
  : src ∈ all_lr0_states /\ sym ∈ all_aug_symbols /\ lr0_next src sym = Some tgt.
Proof.
  unfold lr0_transitions in IN. rewrite in_flat_map in IN. destruct IN as (src0 & IN_src & IN_sym_flat). rewrite in_flat_map in IN_sym_flat.
  destruct IN_sym_flat as (sym0 & IN_sym & IN_tr). destruct (lr0_next src0 sym0) as [tgt0 | ] eqn: NEXT; simpl in IN_tr; try contradiction.
  destruct IN_tr as [EQ | []]. inv EQ. splits; [exact IN_src | exact IN_sym | exact NEXT].
Qed.

Lemma lr0_transitions_complete (src : state) (sym : aug_symbol) (tgt : state)
  (IN_src : src ∈ all_lr0_states)
  (IN_sym : sym ∈ all_aug_symbols)
  (NEXT : lr0_next src sym = Some tgt)
  : (src, sym, tgt) ∈ lr0_transitions.
Proof.
  unfold lr0_transitions. rewrite in_flat_map. exists src. split; [exact IN_src | ]. rewrite in_flat_map. exists sym. split; [exact IN_sym | ]. rewrite NEXT. left. reflexivity.
Qed.

#[projections(primitive)]
Record raw_nt_transition : Set :=
  mkRawNTTransition
  { raw_ntx_source : state
  ; raw_ntx_nonterminal : aug_nonterminal
  ; raw_ntx_target : state
  }.

#[global]
Instance raw_nt_transition_hasEqDec
  : hasEqDec@{Set} raw_nt_transition.
Proof.
  intros [src1 nt1 tgt1] [src2 nt2 tgt2].
  destruct (eq_dec src1 src2) as [EQ_src | NE_src].
  - subst src2. destruct (eq_dec nt1 nt2) as [EQ_nt | NE_nt].
    + subst nt2. destruct (eq_dec tgt1 tgt2) as [EQ_tgt | NE_tgt].
      * subst tgt2. left. reflexivity.
      * right. intros EQ. inv EQ. contradiction.
    + right. intros EQ. inv EQ. contradiction.
  - right. intros EQ. inv EQ. contradiction.
Defined.

Definition nt_transition_of_lr0_transition (tr : lr0_transition) : list raw_nt_transition :=
  match tr with
  | (src, symbol_nonterminal nt, tgt) => [mkRawNTTransition src nt tgt]
  | _ => []
  end.

Definition raw_nt_transitions : list raw_nt_transition :=
  flat_map nt_transition_of_lr0_transition lr0_transitions.

Definition nt_transition_count : nat :=
  length raw_nt_transitions.

Definition nt_transition : Set :=
  Fin.t nt_transition_count.

#[local]
Instance nt_transition_hasEqDec
  : hasEqDec@{Set} nt_transition :=
  Fin.Fin_hasEqDec.

Definition raw_nt_transition_table : Vector.t raw_nt_transition nt_transition_count :=
  V.from_list raw_nt_transitions.

Definition decode_nt_transition (v : nt_transition) : raw_nt_transition :=
  V.nth raw_nt_transition_table v.

Definition all_nt_transition_vertices : list nt_transition :=
  nodup eq_dec (fin_list nt_transition_count).

Lemma all_nt_transition_vertices_sim
  : all_nt_transition_vertices =~= E.full.
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. intros v. split.
  - intros _. econs.
  - intros _. unfold all_nt_transition_vertices. rewrite nodup_In. eapply fin_list_complete.
Qed.

Lemma all_nt_transition_vertices_no_dup
  : NoDup all_nt_transition_vertices.
Proof.
  unfold all_nt_transition_vertices. eapply NoDup_nodup.
Qed.

Definition direct_read_tokens (raw : raw_nt_transition) : list aug_token :=
  filter (fun tok : aug_token => match lr0_next raw.(raw_ntx_target) (symbol_terminal tok) with Some _ => true | None => false end) all_aug_tokens.

Definition DR' (v : nt_transition) : list aug_token :=
  direct_read_tokens (decode_nt_transition v).

Definition DR (v : nt_transition) : ensemble aug_token :=
  E.fromList (DR' v).

Definition directly_reads (v : nt_transition) (tok : aug_token) : Prop :=
  tok \in DR v.

Lemma DR_sim (v : nt_transition)
  : DR' v =~= DR v.
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. reflexivity.
Qed.

Lemma direct_read_tokens_sound (raw : raw_nt_transition) (tok : aug_token)
  (IN : tok ∈ direct_read_tokens raw)
  : exists st, lr0_next raw.(raw_ntx_target) (symbol_terminal tok) = Some st.
Proof.
  unfold direct_read_tokens in IN. rewrite filter_In in IN. destruct IN as [_ NEXT]. destruct (lr0_next raw.(raw_ntx_target) (symbol_terminal tok)) as [st | ] eqn: EQ; try discriminate. exists st. reflexivity.
Qed.

Lemma direct_read_tokens_complete (raw : raw_nt_transition) (tok : aug_token) (st : state)
  (NEXT : lr0_next raw.(raw_ntx_target) (symbol_terminal tok) = Some st)
  : tok ∈ direct_read_tokens raw.
Proof.
  unfold direct_read_tokens. rewrite filter_In. split; [eapply all_aug_tokens_complete | ]. rewrite NEXT. reflexivity.
Qed.

Theorem DR_end_marker_iff (v : nt_transition)
  : end_marker ∈ DR' v <-> (exists st, lr0_next (decode_nt_transition v).(raw_ntx_target) (symbol_terminal end_marker) = Some st).
Proof.
  split.
  - intros IN. eapply direct_read_tokens_sound. exact IN.
  - intros (st & NEXT). eapply direct_read_tokens_complete. exact NEXT.
Qed.

Definition raw_readsb (src : raw_nt_transition) (tgt : raw_nt_transition) : bool :=
  match lr0_next src.(raw_ntx_target) (symbol_nonterminal tgt.(raw_ntx_nonterminal)) with
  | Some st => @same_setb item item_hasEqDec st tgt.(raw_ntx_target) && nullable_aug_nonterminalb tgt.(raw_ntx_nonterminal)
  | None => false
  end.

Definition reads_edgeb (src : nt_transition) (tgt : nt_transition) : bool :=
  raw_readsb (decode_nt_transition src) (decode_nt_transition tgt).

Definition reads_edges : list (nt_transition * nt_transition) :=
  filter (fun edge : nt_transition * nt_transition => reads_edgeb (fst edge) (snd edge)) (product all_nt_transition_vertices all_nt_transition_vertices).

Definition reads_graph : GRAPH.t :=
  {|
    GRAPH.vertices := nt_transition;
    GRAPH.edges := E.fromList reads_edges;
  |}.

Definition reads (src : nt_transition) (tgt : nt_transition) : Prop :=
  (src, tgt) \in reads_graph.(GRAPH.edges).

Lemma reads_edge_iff (src : nt_transition) (tgt : nt_transition)
  : reads src tgt <-> (src, tgt) ∈ reads_edges.
Proof.
  reflexivity.
Qed.

Definition reads_edge_dec (src : nt_transition) (tgt : nt_transition)
  : B.Decision ((src, tgt) \in reads_graph.(GRAPH.edges)).
Proof.
  unfold reads_graph. simpl. unfold E.fromList.
  destruct (in_dec eq_dec (src, tgt) reads_edges) as [IN | NOT_IN].
  - left. exact IN.
  - right. exact NOT_IN.
Defined.

Definition Read' : nt_transition -> list aug_token :=
  @DigraphFixedpoint.gmu' reads_graph aug_token DR' all_nt_transition_vertices nt_transition_hasEqDec reads_edge_dec.

Definition Read : nt_transition -> ensemble aug_token :=
  @DigraphFixedpoint.gmu reads_graph aug_token DR.

Theorem Read_sim (v : nt_transition)
  : Read' v =~= Read v.
Proof.
  eapply DigraphFixedpoint.gmu_sim.
  - eapply DR_sim.
  - eapply all_nt_transition_vertices_sim.
Qed.

Theorem Read_iff_reads_reachable_DR (v : nt_transition) (tok : aug_token)
  : tok \in Read v <-> tok \in (@DigraphFixedpoint.reachable reads_graph v >>= DR).
Proof.
  eapply (@DigraphFixedpoint.gmu_iff_reachable_seed reads_graph aug_token DR v tok).
Qed.

Fixpoint lr0_path (st : state) (syms : list aug_symbol) {struct syms} : option state :=
  match syms with
  | [] => Some st
  | sym :: syms' =>
    match lr0_next st sym with
    | Some st' => lr0_path st' syms'
    | None => None
    end
  end.

Inductive lr0_path_rel : state -> list aug_symbol -> state -> Prop :=
  | lr0_path_rel_nil st
    : lr0_path_rel st [] st
  | lr0_path_rel_cons st1 st2 st3 sym syms
    (NEXT : lr0_next st1 sym = Some st2)
    (REST : lr0_path_rel st2 syms st3)
    : lr0_path_rel st1 (sym :: syms) st3.

#[local] Hint Constructors lr0_path_rel : core.

Lemma lr0_path_sound (st : state) (syms : list aug_symbol) (st' : state)
  (PATH : lr0_path st syms = Some st')
  : lr0_path_rel st syms st'.
Proof.
  revert st st' PATH. induction syms as [ | sym syms IH]; simpl; intros st st' PATH.
  - inv PATH. econs.
  - destruct (lr0_next st sym) as [st1 | ] eqn: NEXT; try discriminate.
    econs; [exact NEXT | ]. eapply IH. exact PATH.
Qed.

Lemma lr0_path_complete (st : state) (syms : list aug_symbol) (st' : state)
  (PATH : lr0_path_rel st syms st')
  : lr0_path st syms = Some st'.
Proof.
  induction PATH as [st | st1 st2 st3 sym syms NEXT REST IH]; simpl.
  - reflexivity.
  - rewrite NEXT. exact IH.
Qed.

Definition path_reachesb (src : state) (syms : list aug_symbol) (tgt : state) : bool :=
  match lr0_path src syms with
  | Some st => @same_setb item item_hasEqDec st tgt
  | None => false
  end.

Definition path_reaches (src : state) (syms : list aug_symbol) (tgt : state) : Prop :=
  exists st, lr0_path_rel src syms st /\ @same_setb item item_hasEqDec st tgt = true.

Lemma path_reachesb_iff (src : state) (syms : list aug_symbol) (tgt : state)
  : path_reachesb src syms tgt = true <-> path_reaches src syms tgt.
Proof.
  unfold path_reachesb, path_reaches. destruct (lr0_path src syms) as [st | ] eqn: PATH.
  - split.
    + intros SAME. exists st. split; [eapply lr0_path_sound; exact PATH | exact SAME].
    + intros (st0 & REL & SAME). pose proof (lr0_path_complete src syms st0 REL) as PATH0. rewrite PATH in PATH0. inv PATH0. exact SAME.
  - split.
    + discriminate.
    + intros (st0 & REL & _). pose proof (lr0_path_complete src syms st0 REL) as PATH0. congruence.
Qed.

Definition nullable_aug_symbolb (sym : aug_symbol) : bool :=
  match sym with
  | symbol_terminal _ => false
  | symbol_nonterminal nt => nullable_aug_nonterminalb nt
  end.

Definition nullable_aug_rhsb (rhs : list aug_symbol) : bool :=
  forallb nullable_aug_symbolb rhs.

Definition nullable_aug_nonterminal (nt : aug_nonterminal) : Prop :=
  match nt with
  | None => False
  | Some nt => nt \in nullable_lfp
  end.

Definition nullable_aug_symbol (sym : aug_symbol) : Prop :=
  match sym with
  | symbol_terminal _ => False
  | symbol_nonterminal nt => nullable_aug_nonterminal nt
  end.

Definition nullable_aug_rhs (rhs : list aug_symbol) : Prop :=
  forall sym, sym ∈ rhs -> nullable_aug_symbol sym.

Lemma nullable_aug_nonterminalb_iff (nt : aug_nonterminal)
  : nullable_aug_nonterminalb nt = true <-> nullable_aug_nonterminal nt.
Proof.
  destruct nt as [nt | ]; simpl.
  - eapply nullable_ntb_iff_lfp.
  - split; [discriminate | contradiction].
Qed.

Lemma nullable_aug_symbolb_iff (sym : aug_symbol)
  : nullable_aug_symbolb sym = true <-> nullable_aug_symbol sym.
Proof.
  destruct sym as [tok | nt]; simpl.
  - split; [discriminate | contradiction].
  - eapply nullable_aug_nonterminalb_iff.
Qed.

Lemma nullable_aug_rhsb_iff (rhs : list aug_symbol)
  : nullable_aug_rhsb rhs = true <-> nullable_aug_rhs rhs.
Proof.
  unfold nullable_aug_rhsb, nullable_aug_rhs. rewrite forallb_forall. split.
  - intros ALL sym IN. rewrite <- nullable_aug_symbolb_iff. eapply ALL. exact IN.
  - intros ALL sym IN. rewrite nullable_aug_symbolb_iff. eapply ALL. exact IN.
Qed.

Fixpoint rhs_splits_at_nonterminal (nt : aug_nonterminal) (rhs : list aug_symbol) {struct rhs} : list (list aug_symbol * list aug_symbol) :=
  match rhs with
  | [] => []
  | sym :: rhs' =>
    let rest := map (fun split : list aug_symbol * list aug_symbol => (sym :: fst split, snd split)) (rhs_splits_at_nonterminal nt rhs') in
    match sym with
    | symbol_nonterminal nt' => if eqb nt nt' then ([], rhs') :: rest else rest
    | symbol_terminal _ => rest
    end
  end.

Definition raw_includesb (src : raw_nt_transition) (tgt : raw_nt_transition) : bool :=
  existsb (fun prod : aug_production => if eqb (aug_lhs prod) tgt.(raw_ntx_nonterminal) then existsb (fun split : list aug_symbol * list aug_symbol => nullable_aug_rhsb (snd split) && path_reachesb tgt.(raw_ntx_source) (fst split) src.(raw_ntx_source)) (rhs_splits_at_nonterminal src.(raw_ntx_nonterminal) (aug_rhs prod)) else false) all_aug_productions.

Definition includes_edgeb (src : nt_transition) (tgt : nt_transition) : bool :=
  raw_includesb (decode_nt_transition src) (decode_nt_transition tgt).

Definition includes_edges : list (nt_transition * nt_transition) :=
  filter (fun edge : nt_transition * nt_transition => includes_edgeb (fst edge) (snd edge)) (product all_nt_transition_vertices all_nt_transition_vertices).

Definition includes_graph : GRAPH.t :=
  {|
    GRAPH.vertices := nt_transition;
    GRAPH.edges := E.fromList includes_edges;
  |}.

Definition includes (src : nt_transition) (tgt : nt_transition) : Prop :=
  (src, tgt) \in includes_graph.(GRAPH.edges).

Lemma includes_edge_iff (src : nt_transition) (tgt : nt_transition)
  : includes src tgt <-> (src, tgt) ∈ includes_edges.
Proof.
  reflexivity.
Qed.

Definition includes_edge_dec (src : nt_transition) (tgt : nt_transition)
  : B.Decision ((src, tgt) \in includes_graph.(GRAPH.edges)).
Proof.
  unfold includes_graph. simpl. unfold E.fromList.
  destruct (in_dec eq_dec (src, tgt) includes_edges) as [IN | NOT_IN].
  - left. exact IN.
  - right. exact NOT_IN.
Defined.

Definition Follow' : nt_transition -> list aug_token :=
  @DigraphFixedpoint.gmu' includes_graph aug_token Read' all_nt_transition_vertices nt_transition_hasEqDec includes_edge_dec.

Definition Follow : nt_transition -> ensemble aug_token :=
  @DigraphFixedpoint.gmu includes_graph aug_token Read.

Theorem Follow_sim (v : nt_transition)
  : Follow' v =~= Follow v.
Proof.
  eapply DigraphFixedpoint.gmu_sim.
  - eapply Read_sim.
  - eapply all_nt_transition_vertices_sim.
Qed.

Theorem Follow_iff_includes_reachable_Read (v : nt_transition) (tok : aug_token)
  : tok \in Follow v <-> tok \in (@DigraphFixedpoint.reachable includes_graph v >>= Read).
Proof.
  eapply (@DigraphFixedpoint.gmu_iff_reachable_seed includes_graph aug_token Read v tok).
Qed.

#[projections(primitive)]
Record reduction_candidate : Set :=
  mkReductionCandidate
  { reduction_state : state
  ; reduction_prod : aug_production
  }.

#[global]
Instance reduction_candidate_hasEqDec
  : hasEqDec@{Set} reduction_candidate.
Proof.
  intros [st1 prod1] [st2 prod2].
  destruct (eq_dec st1 st2) as [EQ_st | NE_st].
  - subst st2. destruct (eq_dec prod1 prod2) as [EQ_prod | NE_prod].
    + subst prod2. left. reflexivity.
    + right. intros EQ. inv EQ. contradiction.
  - right. intros EQ. inv EQ. contradiction.
Defined.

Definition final_item_of_production (prod : aug_production) : item :=
  mkItem prod (length (aug_rhs prod)).

Definition reductions_of_state (st : state) : list reduction_candidate :=
  flat_map (fun prod : aug_production => if @mem item item_hasEqDec (final_item_of_production prod) st then [mkReductionCandidate st prod] else []) all_aug_productions.

Definition all_reduction_candidates : list reduction_candidate :=
  flat_map reductions_of_state all_lr0_states.

Definition lookbackb (red : reduction_candidate) (v : nt_transition) : bool :=
  let raw := decode_nt_transition v in
  if eqb raw.(raw_ntx_nonterminal) (aug_lhs red.(reduction_prod)) then
    path_reachesb raw.(raw_ntx_source) (aug_rhs red.(reduction_prod)) red.(reduction_state)
  else
    false.

Definition lookback_spec (red : reduction_candidate) (v : nt_transition) : Prop :=
  let raw := decode_nt_transition v in
  raw.(raw_ntx_nonterminal) = aug_lhs red.(reduction_prod) /\ path_reaches raw.(raw_ntx_source) (aug_rhs red.(reduction_prod)) red.(reduction_state).

Lemma lookbackb_iff (red : reduction_candidate) (v : nt_transition)
  : lookbackb red v = true <-> lookback_spec red v.
Proof.
  unfold lookbackb, lookback_spec. destruct (eqb (raw_ntx_nonterminal (decode_nt_transition v)) (aug_lhs (reduction_prod red))) eqn: EQ.
  - rewrite eqb_eq in EQ. rewrite path_reachesb_iff. split.
    + intros PATH. split; [exact EQ | exact PATH].
    + intros [_ PATH]. exact PATH.
  - split.
    + discriminate.
    + intros [EQ_nt _]. rewrite eqb_neq in EQ. contradiction.
Qed.

Definition lookback_vertices (red : reduction_candidate) : list nt_transition :=
  filter (lookbackb red) all_nt_transition_vertices.

Definition lookback (red : reduction_candidate) (v : nt_transition) : Prop :=
  v ∈ lookback_vertices red.

Lemma lookback_iff (red : reduction_candidate) (v : nt_transition)
  : lookback red v <-> v ∈ lookback_vertices red.
Proof.
  reflexivity.
Qed.

Lemma lookback_vertices_sound (red : reduction_candidate) (v : nt_transition)
  (IN : v ∈ lookback_vertices red)
  : lookback_spec red v.
Proof.
  unfold lookback_vertices in IN. rewrite filter_In in IN. destruct IN as [_ LOOKBACK]. rewrite <- lookbackb_iff. exact LOOKBACK.
Qed.

Lemma lookback_vertices_complete (red : reduction_candidate) (v : nt_transition)
  (IN_vertex : v ∈ all_nt_transition_vertices)
  (LOOKBACK : lookback_spec red v)
  : v ∈ lookback_vertices red.
Proof.
  unfold lookback_vertices. rewrite filter_In. split; [exact IN_vertex | ]. rewrite lookbackb_iff. exact LOOKBACK.
Qed.

Definition LA' (red : reduction_candidate) : list aug_token :=
  flat_map Follow' (lookback_vertices red).

Definition LA (red : reduction_candidate) : ensemble aug_token :=
  E.fromList (LA' red).

Theorem LA_sim (red : reduction_candidate)
  : LA' red =~= LA red.
Proof.
  rewrite list_corresponds_to_finite_ensemble_iff. reflexivity.
Qed.

Theorem LA_iff_lookback_Follow' (red : reduction_candidate) (tok : aug_token)
  : tok \in LA red <-> (exists v, lookback red v /\ tok ∈ Follow' v).
Proof.
  unfold LA, LA', lookback. cbv [E.In E.fromList]. rewrite in_flat_map. split.
  - intros (v & IN_v & IN_tok). exists v. split; [exact IN_v | exact IN_tok].
  - intros (v & IN_v & IN_tok). exists v. split; [exact IN_v | exact IN_tok].
Qed.

Theorem LA_sound_lookback_Follow (red : reduction_candidate) (tok : aug_token)
  (IN : tok \in LA red)
  : exists v, lookback red v /\ tok \in Follow v.
Proof.
  rewrite LA_iff_lookback_Follow' in IN. destruct IN as (v & LOOKBACK & IN_FOLLOW).
  exists v. split; [exact LOOKBACK | ].
  pose proof (Follow_sim v) as SIM. rewrite list_corresponds_to_finite_ensemble_iff in SIM. eapply SIM. exact IN_FOLLOW.
Qed.

Theorem LA_iff_lookback_Follow (red : reduction_candidate) (tok : aug_token)
  : tok \in LA red <-> (exists v, lookback red v /\ tok \in Follow v).
Proof.
  split.
  - intros IN. eapply LA_sound_lookback_Follow. exact IN.
  - intros (v & LOOKBACK & IN_FOLLOW). rewrite LA_iff_lookback_Follow'. exists v. split; [exact LOOKBACK | ]. pose proof (Follow_sim v) as SIM. rewrite list_corresponds_to_finite_ensemble_iff in SIM. eapply SIM. exact IN_FOLLOW.
Qed.

Theorem LA_token_cases (red : reduction_candidate) (tok : aug_token)
  (IN : tok \in LA red)
  : tok = end_marker \/ exists raw_tok, tok = lift_token raw_tok.
Proof.
  destruct tok as [tok | ]; [right; exists tok; reflexivity | left; reflexivity].
Qed.

Inductive action : Set :=
  | Shift (st : state)
    : action
  | Reduce (prod : aug_production)
    : action
  | Accept
    : action.

#[global]
Instance action_hasEqDec
  : hasEqDec@{Set} action.
Proof.
  intros act1 act2. destruct act1 as [st1 | prod1 | ], act2 as [st2 | prod2 | ].
  - destruct (eq_dec st1 st2) as [EQ | NE].
    + subst st2. left. reflexivity.
    + right. intros EQ. inv EQ. contradiction.
  - right. discriminate.
  - right. discriminate.
  - right. discriminate.
  - destruct (eq_dec prod1 prod2) as [EQ | NE].
    + subst prod2. left. reflexivity.
    + right. intros EQ. inv EQ. contradiction.
  - right. discriminate.
  - right. discriminate.
  - right. discriminate.
  - left. reflexivity.
Defined.

#[projections(primitive)]
Record action_entry : Set :=
  mkActionEntry
  { action_entry_state : state
  ; action_entry_token : aug_token
  ; action_entry_action : action
  }.

#[projections(primitive)]
Record conflict_report : Set :=
  mkConflictReport
  { conflict_state : state
  ; conflict_token : aug_token
  ; conflict_old_action : action
  ; conflict_new_action : action
  }.

Inductive diagnostic_note : Set :=
  | ReadsPropagationNote (from : nt_transition) (to : nt_transition)
    : diagnostic_note
  | IncludesPropagationNote (from : nt_transition) (to : nt_transition)
    : diagnostic_note
  | LookbackPropagationNote (red : reduction_candidate) (via : nt_transition)
    : diagnostic_note.

#[global]
Instance action_entry_hasEqDec
  : hasEqDec@{Set} action_entry.
Proof.
  intros [st1 tok1 act1] [st2 tok2 act2].
  destruct (eq_dec st1 st2) as [EQ_st | NE_st].
  - subst st2. destruct (eq_dec tok1 tok2) as [EQ_tok | NE_tok].
    + subst tok2. destruct (eq_dec act1 act2) as [EQ_act | NE_act].
      * subst act2. left. reflexivity.
      * right. intros EQ. inv EQ. contradiction.
    + right. intros EQ. inv EQ. contradiction.
  - right. intros EQ. inv EQ. contradiction.
Defined.

Definition action_entry_same_key (lhs : action_entry) (rhs : action_entry) : bool :=
  eqb lhs.(action_entry_state) rhs.(action_entry_state) && eqb lhs.(action_entry_token) rhs.(action_entry_token).

Definition action_conflict_report (old : action_entry) (new : action_entry) : conflict_report :=
  mkConflictReport old.(action_entry_state) new.(action_entry_token) old.(action_entry_action) new.(action_entry_action).

Definition propagation_witnesses (red : reduction_candidate) : list diagnostic_note :=
  map (LookbackPropagationNote red) (lookback_vertices red).

Definition action_conflict_error (old : action_entry) (new : action_entry) : Error.t :=
  let report := action_conflict_report old new in
  match report.(conflict_old_action), report.(conflict_new_action) with
  | Shift _, Reduce _ => Error.ShiftReduceConflict 0 new.(action_entry_token)
  | Reduce _, Shift _ => Error.ShiftReduceConflict 0 new.(action_entry_token)
  | _, _ => Error.ReduceReduceConflict 0 new.(action_entry_token)
  end.

Fixpoint insert_action_entry (entry : action_entry) (table : list action_entry) {struct table} : ErrM (list action_entry) :=
  match table with
  | [] => inr [entry]
  | old :: rest =>
    if action_entry_same_key old entry then
      if eqb old.(action_entry_action) entry.(action_entry_action) then inr table else inl (action_conflict_error old entry)
    else
      match insert_action_entry entry rest with
      | inl err => inl err
      | inr rest' => inr (old :: rest')
      end
  end.

Fixpoint build_action_table_loop (entries : list action_entry) (acc : list action_entry) {struct entries} : ErrM (list action_entry) :=
  match entries with
  | [] => inr acc
  | entry :: entries' =>
    match insert_action_entry entry acc with
    | inl err => inl err
    | inr acc' => build_action_table_loop entries' acc'
    end
  end.

Lemma insert_action_entry_in_inv (entry : action_entry) (table : list action_entry) (table' : list action_entry) (other : action_entry)
  (INSERT : insert_action_entry entry table = inr table')
  (IN : other ∈ table')
  : other = entry \/ other ∈ table.
Proof.
  revert table' other INSERT IN. induction table as [ | head table IH]; simpl; intros table' other INSERT IN.
  - inv INSERT. simpl in IN. destruct IN as [EQ | []]. left. symmetry. exact EQ.
  - destruct (action_entry_same_key head entry) eqn: SAME.
    + destruct (eqb (action_entry_action head) (action_entry_action entry)) eqn: SAME_ACTION; inv INSERT. right. exact IN.
    + destruct (insert_action_entry entry table) as [err | rest'] eqn: INSERT_rest; try discriminate. inv INSERT.
      simpl in IN. destruct IN as [EQ | IN].
      * right. left. exact EQ.
      * pose proof (IH rest' other eq_refl IN) as [EQ | IN_table].
        { left. exact EQ. }
        { right. right. exact IN_table. }
Qed.

Lemma build_action_table_loop_in_inv (entries : list action_entry) (acc : list action_entry) (table : list action_entry) (entry : action_entry)
  (BUILD : build_action_table_loop entries acc = inr table)
  (IN : entry ∈ table)
  : entry ∈ acc \/ entry ∈ entries.
Proof.
  revert acc table entry BUILD IN. induction entries as [ | head entries IH]; simpl; intros acc table entry BUILD IN.
  - inv BUILD. left. exact IN.
  - destruct (insert_action_entry head acc) as [err | acc'] eqn: INSERT; try discriminate.
    pose proof (IH acc' table entry BUILD IN) as [IN_acc' | IN_entries].
    + pose proof (insert_action_entry_in_inv head acc acc' entry INSERT IN_acc') as [EQ | IN_acc].
      * right. left. symmetry. exact EQ.
      * left. exact IN_acc.
    + right. right. exact IN_entries.
Qed.

Definition shift_action_entries : list action_entry :=
  flat_map (fun tr : lr0_transition => match tr with (src, symbol_terminal tok, tgt) => [mkActionEntry src tok (Shift tgt)] | _ => [] end) lr0_transitions.

Definition reduce_action_entries : list action_entry :=
  flat_map (fun red : reduction_candidate => map (fun tok : aug_token => mkActionEntry red.(reduction_state) tok (Reduce red.(reduction_prod))) (LA' red)) all_reduction_candidates.

Definition accept_action_entries : list action_entry :=
  flat_map (fun red : reduction_candidate => match red.(reduction_prod) with aug_start => [mkActionEntry red.(reduction_state) end_marker Accept] | aug_old _ => [] end) all_reduction_candidates.

Definition action_candidates : list action_entry :=
  shift_action_entries ++ reduce_action_entries ++ accept_action_entries.

Lemma shift_action_entries_sound (entry : action_entry)
  (IN : entry ∈ shift_action_entries)
  : exists src, exists tok, exists tgt, (src, symbol_terminal tok, tgt) ∈ lr0_transitions /\ entry = mkActionEntry src tok (Shift tgt).
Proof.
  unfold shift_action_entries in IN. rewrite in_flat_map in IN.
  destruct IN as (tr & IN_tr & IN_entry). destruct tr as [[src [tok | nt]] tgt]; simpl in IN_entry; try contradiction.
  destruct IN_entry as [EQ | []]. subst entry. exists src. exists tok. exists tgt. split; [exact IN_tr | reflexivity].
Qed.

Lemma reduce_action_entries_sound (entry : action_entry)
  (IN : entry ∈ reduce_action_entries)
  : exists red, exists tok, red ∈ all_reduction_candidates /\ tok ∈ LA' red /\ entry = mkActionEntry red.(reduction_state) tok (Reduce red.(reduction_prod)).
Proof.
  unfold reduce_action_entries in IN. rewrite in_flat_map in IN.
  destruct IN as (red & IN_red & IN_entry). rewrite in_map_iff in IN_entry.
  destruct IN_entry as (tok & EQ & IN_tok). subst entry. exists red. exists tok. splits; [exact IN_red | exact IN_tok | reflexivity].
Qed.

Lemma accept_action_entries_sound (entry : action_entry)
  (IN : entry ∈ accept_action_entries)
  : exists red, red ∈ all_reduction_candidates /\ red.(reduction_prod) = aug_start /\ entry = mkActionEntry red.(reduction_state) end_marker Accept.
Proof.
  unfold accept_action_entries in IN. rewrite in_flat_map in IN.
  destruct IN as (red & IN_red & IN_entry). destruct (reduction_prod red) as [ | prod] eqn: EQ_prod; simpl in IN_entry; try contradiction.
  destruct IN_entry as [EQ | []]. subst entry. exists red. splits; [exact IN_red | exact EQ_prod | reflexivity].
Qed.

Lemma action_candidates_sound (entry : action_entry)
  (IN : entry ∈ action_candidates)
  : entry ∈ shift_action_entries \/ entry ∈ reduce_action_entries \/ entry ∈ accept_action_entries.
Proof.
  unfold action_candidates in IN. rewrite in_app_iff in IN. destruct IN as [IN | IN].
  - left. exact IN.
  - rewrite in_app_iff in IN. destruct IN as [IN | IN]; [right; left; exact IN | right; right; exact IN].
Qed.

Definition action_table_result : ErrM (list action_entry) :=
  build_action_table_loop action_candidates [].

#[projections(primitive)]
Record goto_entry : Set :=
  mkGotoEntry
  { goto_entry_state : state
  ; goto_entry_nonterminal : aug_nonterminal
  ; goto_entry_target : state
  }.

Definition goto_entries : list goto_entry :=
  map (fun raw : raw_nt_transition => mkGotoEntry raw.(raw_ntx_source) raw.(raw_ntx_nonterminal) raw.(raw_ntx_target)) raw_nt_transitions.

#[projections(primitive)]
Record certified_table : Type :=
  mkCertifiedTable
  { certified_action_table : list action_entry
  ; certified_goto_table : list goto_entry
  ; certified_action_table_eq : action_table_result = inr certified_action_table
  ; certified_goto_table_eq : certified_goto_table = goto_entries
  }.

Definition build_table : ErrM certified_table :=
  match action_table_result as result return action_table_result = result -> ErrM certified_table with
  | inl err => fun _ => inl err
  | inr table => fun EQ => inr (mkCertifiedTable table goto_entries EQ eq_refl)
  end eq_refl.

Fixpoint lookup_action (table : list action_entry) (st : state) (tok : aug_token) {struct table} : option action :=
  match table with
  | [] => None
  | entry :: table' => if eqb entry.(action_entry_state) st && eqb entry.(action_entry_token) tok then Some entry.(action_entry_action) else lookup_action table' st tok
  end.

Fixpoint lookup_goto (table : list goto_entry) (st : state) (nt : aug_nonterminal) {struct table} : option state :=
  match table with
  | [] => None
  | entry :: table' => if eqb entry.(goto_entry_state) st && eqb entry.(goto_entry_nonterminal) nt then Some entry.(goto_entry_target) else lookup_goto table' st nt
  end.

Inductive parse_tree : Set :=
  | parse_leaf (tok : token)
    : parse_tree
  | parse_node (prod : aug_production) (children : list parse_tree)
    : parse_tree.

Definition parse_tree_root (tree : parse_tree) : aug_symbol :=
  match tree with
  | parse_leaf tok => symbol_terminal (lift_token tok)
  | parse_node prod _ => symbol_nonterminal (aug_lhs prod)
  end.

Fixpoint parse_tree_yield (tree : parse_tree) : list aug_symbol :=
  match tree with
  | parse_leaf tok => [symbol_terminal (lift_token tok)]
  | parse_node _ children => flat_map parse_tree_yield children
  end.

Inductive parse_tree_wf : parse_tree -> Prop :=
  | parse_leaf_wf tok
    : parse_tree_wf (parse_leaf tok)
  | parse_node_wf prod children
    (ROOTS : map parse_tree_root children = aug_rhs prod)
    (CHILDREN : Forall parse_tree_wf children)
    : parse_tree_wf (parse_node prod children).

#[local] Hint Constructors parse_tree_wf : core.

Definition parse_tree_roots (trees : list parse_tree) : list aug_symbol :=
  map parse_tree_root trees.

Fixpoint parse_tree_size (tree : parse_tree) : nat :=
  match tree with
  | parse_leaf _ => 1
  | parse_node _ children => S (fold_right (fun child acc => parse_tree_size child + acc) 0 children)
  end.

Lemma parse_tree_size_in_children (prod : aug_production) (children : list parse_tree) (child : parse_tree)
  (IN : child ∈ children)
  : parse_tree_size child < parse_tree_size (parse_node prod children).
Proof.
  simpl. induction children as [ | head children IH]; simpl in IN |- *; [contradiction | ]. destruct IN as [EQ | IN].
  - subst child. lia.
  - pose proof (IH IN). lia.
Qed.

Lemma parse_tree_wf_derives_fuel (n : nat) (tree : parse_tree)
  (SIZE : parse_tree_size tree <= n)
  (WF : parse_tree_wf tree)
  : aug_derives [parse_tree_root tree] (parse_tree_yield tree).
Proof.
  revert tree SIZE WF. induction n as [ | n IH]; intros tree SIZE WF.
  - destruct tree as [tok | prod children]; simpl in SIZE; lia.
  - destruct tree as [tok | prod children].
    + simpl. econs.
    + inv WF. simpl. eapply aug_derives_step with (ys := aug_rhs prod).
      * change [@symbol_nonterminal aug_token aug_nonterminal (aug_lhs prod)] with ([] ++ @symbol_nonterminal aug_token aug_nonterminal (aug_lhs prod) :: []). replace (aug_rhs prod) with ([] ++ aug_rhs prod ++ []) by (simpl; rewrite app_nil_r; reflexivity). exact (aug_derives1_intro prod [] []).
      * rewrite <- ROOTS. assert (BOUND : forall child, child ∈ children -> parse_tree_size child <= n).
        { intros child IN. pose proof (parse_tree_size_in_children prod children child IN) as LT. simpl in SIZE, LT. lia. }
        clear ROOTS SIZE. induction CHILDREN as [ | child children WF_child WF_children IH_children]; simpl.
        { econs. }
        { change (parse_tree_root child :: map parse_tree_root children) with ([parse_tree_root child] ++ map parse_tree_root children). eapply aug_derives_app.
          - eapply IH; [eapply BOUND; left; reflexivity | exact WF_child].
          - eapply IH_children. intros child0 IN. eapply BOUND. right. exact IN.
        }
Qed.

Lemma parse_tree_wf_derives (tree : parse_tree)
  (WF : parse_tree_wf tree)
  : aug_derives [parse_tree_root tree] (parse_tree_yield tree).
Proof.
  eapply parse_tree_wf_derives_fuel; [reflexivity | exact WF].
Qed.

#[projections(primitive)]
Record stack_frame : Set :=
  mkStackFrame
  { frame_state : state
  ; frame_tree : option parse_tree
  }.

Definition parser_stack : Set :=
  list stack_frame.

#[projections(primitive)]
Record parser_config : Set :=
  mkParserConfig
  { config_stack : parser_stack
  ; config_input : list token
  }.

Definition initial_config (tokens : list token) : parser_config :=
  mkParserConfig [mkStackFrame start_state None] tokens.

Definition lookahead_of_input (input : list token) : aug_token :=
  match input with
  | [] => end_marker
  | tok :: _ => lift_token tok
  end.

Definition consume_input (input : list token) : list token :=
  match input with
  | [] => []
  | _ :: input' => input'
  end.

Definition top_state (stack : parser_stack) : option state :=
  match stack with
  | [] => None
  | frame :: _ => Some frame.(frame_state)
  end.

Definition frame_trees (frames : list stack_frame) : list parse_tree :=
  flat_map (fun frame : stack_frame => match frame.(frame_tree) with Some tree => [tree] | None => [] end) frames.

Definition token_sentence (tokens : list token) : list aug_symbol :=
  map (fun tok : token => symbol_terminal (lift_token tok)) tokens.

Definition stack_yield (stack : parser_stack) : list aug_symbol :=
  flat_map parse_tree_yield (rev (frame_trees stack)).

Definition accepting_stack_tree (stack : parser_stack) : option parse_tree :=
  match stack with
  | top :: bottom :: [] =>
    match top.(frame_tree), bottom.(frame_tree) with
    | Some tree, None => if eqb (parse_tree_root tree) (symbol_nonterminal (lift_nonterminal Grammar.start)) then Some tree else None
    | _, _ => None
    end
  | _ => None
  end.

Definition frame_wf (frame : stack_frame) : Prop :=
  match frame.(frame_tree) with
  | Some tree => parse_tree_wf tree
  | None => True
  end.

Definition stack_wf (stack : parser_stack) : Prop :=
  Forall frame_wf stack.

Definition parser_config_sound (tokens : list token) (cfg : parser_config) : Prop :=
  stack_wf cfg.(config_stack) /\ stack_yield cfg.(config_stack) ++ token_sentence cfg.(config_input) = token_sentence tokens.

Lemma frame_trees_app (frames1 : list stack_frame) (frames2 : list stack_frame)
  : frame_trees (frames1 ++ frames2) = frame_trees frames1 ++ frame_trees frames2.
Proof.
  unfold frame_trees. rewrite flat_map_app. reflexivity.
Qed.

Lemma stack_yield_cons_some (st : state) (tree : parse_tree) (stack : parser_stack)
  : stack_yield (mkStackFrame st (Some tree) :: stack) = stack_yield stack ++ parse_tree_yield tree.
Proof.
  unfold stack_yield, frame_trees. simpl. rewrite flat_map_app. simpl. rewrite app_nil_r. reflexivity.
Qed.

Lemma stack_yield_app (stack1 : parser_stack) (stack2 : parser_stack)
  : stack_yield (stack1 ++ stack2) = stack_yield stack2 ++ flat_map parse_tree_yield (rev (frame_trees stack1)).
Proof.
  unfold stack_yield. rewrite frame_trees_app. rewrite L.list_rev_app. rewrite flat_map_app. reflexivity.
Qed.

Lemma frame_trees_wf (frames : list stack_frame)
  (WF : stack_wf frames)
  : Forall parse_tree_wf (frame_trees frames).
Proof.
  induction WF as [ | frame frames WF_frame WF_frames IH]; simpl.
  - econs.
  - destruct frame as [st [tree | ]]; simpl in *; [econs; [exact WF_frame | exact IH] | exact IH].
Qed.

Lemma stack_wf_firstn (n : nat) (stack : parser_stack)
  (WF : stack_wf stack)
  : stack_wf (firstn n stack).
Proof.
  revert n. induction WF as [ | frame frames WF_frame WF_frames IH]; intros [ | n]; simpl.
  - econs.
  - econs.
  - econs.
  - econs; [exact WF_frame | eapply IH].
Qed.

Lemma stack_wf_skipn (n : nat) (stack : parser_stack)
  (WF : stack_wf stack)
  : stack_wf (skipn n stack).
Proof.
  revert n. induction WF as [ | frame frames WF_frame WF_frames IH]; intros [ | n]; simpl.
  - econs.
  - econs.
  - econs; [exact WF_frame | exact WF_frames].
  - eapply IH.
Qed.

Lemma initial_config_sound (tokens : list token)
  : parser_config_sound tokens (initial_config tokens).
Proof.
  unfold parser_config_sound, initial_config, stack_wf, stack_yield, frame_trees. simpl. split; [econs; simpl; eauto | reflexivity].
Qed.

Definition shift_step (st' : state) (cfg : parser_config) : ErrM parser_config :=
  match cfg.(config_input) with
  | [] => inl Error.InternalInvariantBroken
  | tok :: input' => inr (mkParserConfig (mkStackFrame st' (Some (parse_leaf tok)) :: cfg.(config_stack)) input')
  end.

Definition reduce_step (table : certified_table) (prod : aug_production) (cfg : parser_config) : ErrM parser_config :=
  let pop_count := length (aug_rhs prod) in
  let popped := firstn pop_count cfg.(config_stack) in
  let rest := skipn pop_count cfg.(config_stack) in
  let children := rev (frame_trees popped) in
  match top_state rest with
  | None => inl Error.InternalInvariantBroken
  | Some st =>
    if @eqb (list aug_symbol) (list_hasEqDec aug_symbol_hasEqDec) (parse_tree_roots children) (aug_rhs prod) then
      match lookup_goto table.(certified_goto_table) st (aug_lhs prod) with
      | None => inl Error.InternalInvariantBroken
      | Some st' => inr (mkParserConfig (mkStackFrame st' (Some (parse_node prod children)) :: rest) cfg.(config_input))
      end
    else
      inl Error.InternalInvariantBroken
  end.

Definition accept_step (cfg : parser_config) : ErrM parse_tree :=
  match cfg.(config_input), accepting_stack_tree cfg.(config_stack) with
  | [], Some tree => inr tree
  | _, _ => inl Error.InternalInvariantBroken
  end.

Inductive parser_step_result : Set :=
  | ParserContinue (cfg' : parser_config)
    : parser_step_result
  | ParserAccept (tree : parse_tree)
    : parser_step_result.

Definition parser_step (table : certified_table) (cfg : parser_config) : ErrM parser_step_result :=
  match top_state cfg.(config_stack) with
  | None => inl Error.InternalInvariantBroken
  | Some st =>
    let lookahead := lookahead_of_input cfg.(config_input) in
    match lookup_action table.(certified_action_table) st lookahead with
    | None => inl (Error.NoAction 0 lookahead)
    | Some (Shift st') =>
      match lookahead with
      | None => inl Error.InternalInvariantBroken
      | _ =>
        match shift_step st' cfg with
        | inl err => inl err
        | inr cfg' => inr (ParserContinue cfg')
        end
      end
    | Some (Reduce prod) =>
      match reduce_step table prod cfg with
      | inl err => inl err
      | inr cfg' => inr (ParserContinue cfg')
      end
    | Some Accept =>
      match accept_step cfg with
      | inl err => inl err
      | inr tree => inr (ParserAccept tree)
      end
    end
  end.

Inductive parser_step_rel (table : certified_table) : parser_config -> parser_step_result -> Prop :=
  | parser_step_rel_intro cfg result
    (STEP : parser_step table cfg = inr result)
    : parser_step_rel table cfg result.

Lemma parser_step_rel_iff (table : certified_table) (cfg : parser_config) (result : parser_step_result)
  : parser_step_rel table cfg result <-> parser_step table cfg = inr result.
Proof.
  split.
  - intros STEP. inv STEP. exact STEP0.
  - intros STEP. econs. exact STEP.
Qed.

Theorem parser_step_rel_deterministic (table : certified_table) (cfg : parser_config) (result1 : parser_step_result) (result2 : parser_step_result)
  (STEP1 : parser_step_rel table cfg result1)
  (STEP2 : parser_step_rel table cfg result2)
  : result1 = result2.
Proof.
  rewrite parser_step_rel_iff in STEP1. rewrite parser_step_rel_iff in STEP2. congruence.
Qed.

Inductive parser_config_ok (table : certified_table) : parser_config -> Prop :=
  | parser_config_ok_intro cfg
    (STACK_NONEMPTY : cfg.(config_stack) <> [])
    : parser_config_ok table cfg.

Definition parser_order (table : certified_table) (cfg' : parser_config) (cfg : parser_config) : Prop :=
  parser_step table cfg = inr (ParserContinue cfg').

Definition parser_step_outcome (table : certified_table) (cfg : parser_config) : ErrM ({ tree : parse_tree | parser_step table cfg = inr (ParserAccept tree) } + { cfg' : parser_config | parser_order table cfg' cfg }) :=
  match parser_step table cfg as result return parser_step table cfg = result -> ErrM ({ tree : parse_tree | parser_step table cfg = inr (ParserAccept tree) } + { cfg' : parser_config | parser_order table cfg' cfg }) with
  | inl err => fun _ => inl err
  | inr (ParserAccept tree) => fun STEP => inr (inl (exist _ tree STEP))
  | inr (ParserContinue cfg') => fun STEP => inr (inr (exist _ cfg' STEP))
  end eq_refl.

Fixpoint parse_loop_acc (table : certified_table) (cfg : parser_config) (ACC : Acc (parser_order table) cfg) {struct ACC} : ErrM parse_tree :=
  match parser_step_outcome table cfg with
  | inl err => inl err
  | inr (inl accepted) => inr (proj1_sig accepted)
  | inr (inr next) => parse_loop_acc table (proj1_sig next) (Acc_inv ACC (proj2_sig next))
  end.

Definition parse_with_acc (table : certified_table) (tokens : list token) (ACC : Acc (parser_order table) (initial_config tokens)) : ErrM parse_tree :=
  parse_loop_acc table (initial_config tokens) ACC.

Definition parse (table : certified_table) (tokens : list token) (ACC : Acc (parser_order table) (initial_config tokens)) : ErrM parse_tree :=
  parse_with_acc table tokens ACC.

Definition generated_table : ErrM certified_table :=
  build_table.

Definition parse_aug_sound_statement (table : certified_table) : Prop :=
  forall tokens, forall ACC, forall tree, parse table tokens ACC = inr tree -> aug_in_language tokens.

Definition parse_sound_statement (table : certified_table) : Prop :=
  forall tokens, forall ACC, forall tree, parse table tokens ACC = inr tree -> in_language tokens.

Definition parse_complete_statement (table : certified_table) : Prop :=
  forall tokens, in_language tokens -> exists ACC, exists tree, parse table tokens ACC = inr tree.

Lemma shift_step_preserves_parser_config_sound (tokens : list token) (st' : state) (cfg : parser_config) (cfg' : parser_config)
  (SOUND : parser_config_sound tokens cfg)
  (STEP : shift_step st' cfg = inr cfg')
  : parser_config_sound tokens cfg'.
Proof.
  unfold shift_step in STEP. destruct cfg.(config_input) as [ | tok input'] eqn:INPUT; try discriminate. inv STEP. destruct SOUND as [WF EQ]. rewrite INPUT in EQ. split.
  - econs; [simpl; econs | exact WF].
  - change (stack_yield (mkStackFrame st' (Some (parse_leaf tok)) :: cfg.(config_stack)) ++ token_sentence input' = token_sentence tokens). rewrite stack_yield_cons_some. simpl. rewrite <- app_assoc. simpl. exact EQ.
Qed.

Lemma reduce_step_preserves_parser_config_sound (tokens : list token) (table : certified_table) (prod : aug_production) (cfg : parser_config) (cfg' : parser_config)
  (SOUND : parser_config_sound tokens cfg)
  (STEP : reduce_step table prod cfg = inr cfg')
  : parser_config_sound tokens cfg'.
Proof.
  destruct cfg as [stack input]. unfold reduce_step in STEP. simpl in *. destruct SOUND as [WF EQ]. change (stack_wf stack) in WF. change (stack_yield stack ++ token_sentence input = token_sentence tokens) in EQ.
  set (pop_count := length (aug_rhs prod)) in *.
  set (popped := firstn pop_count stack) in *.
  set (rest := skipn pop_count stack) in *.
  set (children := rev (frame_trees popped)) in *.
  destruct (top_state rest) as [st | ] eqn:TOP; try discriminate.
  destruct (@eqb (list aug_symbol) (list_hasEqDec aug_symbol_hasEqDec) (parse_tree_roots children) (aug_rhs prod)) eqn:ROOTS; try discriminate.
  destruct (lookup_goto (certified_goto_table table) st (aug_lhs prod)) as [st' | ] eqn:GOTO; try discriminate.
  inv STEP. rewrite eqb_eq in ROOTS. unfold parse_tree_roots in ROOTS. split.
  - econs.
    + simpl. econs.
      * exact ROOTS.
      * subst children. eapply Forall_rev. eapply frame_trees_wf. subst popped. eapply stack_wf_firstn. exact WF.
    + subst rest. eapply stack_wf_skipn. exact WF.
  - change (stack_yield (mkStackFrame st' (Some (parse_node prod children)) :: rest) ++ token_sentence input = token_sentence tokens). rewrite stack_yield_cons_some. simpl. subst children. replace ((stack_yield rest ++ flat_map parse_tree_yield (rev (frame_trees popped))) ++ token_sentence input) with (stack_yield (popped ++ rest) ++ token_sentence input) by (rewrite stack_yield_app; reflexivity). subst popped rest pop_count. rewrite firstn_skipn. exact EQ.
Qed.

Lemma parser_step_preserves_parser_config_sound (tokens : list token) (table : certified_table) (cfg : parser_config) (cfg' : parser_config)
  (SOUND : parser_config_sound tokens cfg)
  (STEP : parser_step table cfg = inr (ParserContinue cfg'))
  : parser_config_sound tokens cfg'.
Proof.
  unfold parser_step in STEP.
  destruct (top_state (config_stack cfg)) as [st | ] eqn:TOP; try discriminate.
  destruct (lookup_action (certified_action_table table) st (lookahead_of_input (config_input cfg))) as [[st' | prod | ] | ] eqn:LOOKUP; try discriminate.
  - destruct (lookahead_of_input (config_input cfg)) as [tok | ] eqn:LOOKAHEAD; try discriminate. destruct (shift_step st' cfg) as [err | cfg0] eqn:SHIFT; try discriminate. inv STEP. eapply shift_step_preserves_parser_config_sound; [exact SOUND | exact SHIFT].
  - destruct (reduce_step table prod cfg) as [err | cfg0] eqn:REDUCE; try discriminate. inv STEP. eapply reduce_step_preserves_parser_config_sound; [exact SOUND | exact REDUCE].
  - destruct (accept_step cfg) as [err | tree] eqn:ACCEPT; discriminate.
Qed.

Lemma accepting_config_sound (tokens : list token) (cfg : parser_config) (tree : parse_tree)
  (SOUND : parser_config_sound tokens cfg)
  (INPUT : cfg.(config_input) = [])
  (ACCEPT : accepting_stack_tree cfg.(config_stack) = Some tree)
  : aug_in_language tokens.
Proof.
  destruct cfg as [stack input]. simpl in *. subst input. destruct SOUND as [WF EQ]. unfold accepting_stack_tree in ACCEPT. destruct stack as [ | top [ | bottom [ | extra rest]]]; try discriminate.
  destruct top as [top_st [top_tree | ]]; destruct bottom as [bottom_st [bottom_tree | ]]; simpl in *; try discriminate.
  destruct (eqb (parse_tree_root top_tree) (symbol_nonterminal (lift_nonterminal Grammar.start))) eqn:ROOT; try discriminate.
  injection ACCEPT as TREE_EQ. subst tree. rewrite eqb_eq in ROOT. inv WF. simpl in H1. unfold stack_yield, frame_trees in EQ. simpl in EQ. rewrite app_nil_r in EQ.
  unfold aug_in_language, aug_start_sentence, aug_sentence. change (map (fun tok : token => symbol_terminal (lift_token tok)) tokens) with (token_sentence tokens). eapply aug_derives_step with (ys := [symbol_nonterminal (lift_nonterminal Grammar.start); symbol_terminal end_marker]).
  - exact (aug_derives1_intro aug_start [] []).
  - rewrite <- ROOT. change [parse_tree_root top_tree; symbol_terminal end_marker] with ([parse_tree_root top_tree] ++ [symbol_terminal end_marker]). replace (token_sentence tokens ++ [symbol_terminal end_marker]) with (parse_tree_yield top_tree ++ [symbol_terminal end_marker]) by (rewrite <- EQ; rewrite app_nil_r; reflexivity). eapply aug_derives_app_suffix. eapply parse_tree_wf_derives. exact H1.
Qed.

Lemma parser_step_accept_sound (tokens : list token) (table : certified_table) (cfg : parser_config) (tree : parse_tree)
  (SOUND : parser_config_sound tokens cfg)
  (STEP : parser_step table cfg = inr (ParserAccept tree))
  : aug_in_language tokens.
Proof.
  unfold parser_step in STEP.
  destruct (top_state (config_stack cfg)) as [st | ] eqn:TOP; try discriminate.
  destruct (lookup_action (certified_action_table table) st (lookahead_of_input (config_input cfg))) as [[st' | prod | ] | ] eqn:LOOKUP; try discriminate.
  - destruct (lookahead_of_input (config_input cfg)) as [tok | ] eqn:LOOKAHEAD; try discriminate. destruct (shift_step st' cfg) as [err | cfg'] eqn:SHIFT; discriminate.
  - destruct (reduce_step table prod cfg) as [err | cfg'] eqn:REDUCE; discriminate.
  - destruct (accept_step cfg) as [err | accepted] eqn:ACCEPT; try discriminate. inv STEP. unfold accept_step in ACCEPT. destruct cfg.(config_input) as [ | tok input] eqn:INPUT; simpl in ACCEPT; try (destruct (accepting_stack_tree cfg.(config_stack)); discriminate). destruct (accepting_stack_tree cfg.(config_stack)) as [tree0 | ] eqn:STACK; try discriminate. inv ACCEPT. eapply accepting_config_sound; [exact SOUND | exact INPUT | exact STACK].
Qed.

Lemma parse_loop_acc_sound (table : certified_table) (cfg : parser_config) (ACC : Acc (parser_order table) cfg) (tokens : list token) (tree : parse_tree)
  (SOUND : parser_config_sound tokens cfg)
  (PARSE : parse_loop_acc table cfg ACC = inr tree)
  : aug_in_language tokens.
Proof.
  revert cfg ACC tokens tree SOUND PARSE. fix IH 2. intros cfg ACC tokens tree SOUND PARSE. destruct ACC as [ACC_NEXT]. destruct (parser_step_outcome table cfg) as [err | [accepted | next]] eqn:STEP_OUT.
  - cbn [parse_loop_acc] in PARSE. rewrite STEP_OUT in PARSE. simpl in PARSE. discriminate.
  - cbn [parse_loop_acc] in PARSE. rewrite STEP_OUT in PARSE. destruct accepted as [accepted STEP_ACCEPT]. simpl in PARSE. inv PARSE. eapply parser_step_accept_sound; [exact SOUND | exact STEP_ACCEPT].
  - cbn [parse_loop_acc] in PARSE. rewrite STEP_OUT in PARSE. destruct next as [cfg' STEP_CONT]. simpl in PARSE. eapply (IH cfg' (ACC_NEXT cfg' STEP_CONT) tokens tree).
    + eapply parser_step_preserves_parser_config_sound; [exact SOUND | exact STEP_CONT].
    + exact PARSE.
Qed.

Theorem parse_aug_sound (table : certified_table)
  : parse_aug_sound_statement table.
Proof.
  unfold parse_aug_sound_statement, parse, parse_with_acc. intros tokens ACC tree PARSE. eapply parse_loop_acc_sound; [eapply initial_config_sound | exact PARSE].
Qed.

Theorem parse_sound (table : certified_table)
  : parse_sound_statement table.
Proof.
  unfold parse_sound_statement. intros tokens ACC tree PARSE. eapply aug_in_language_in_language. eapply parse_aug_sound. exact PARSE.
Qed.

Record generated_parser : Type :=
  mkGeneratedParser
  { generated_parser_table : certified_table
  ; generated_parser_parse : forall tokens, Acc (parser_order generated_parser_table) (initial_config tokens) -> ErrM parse_tree
  ; generated_parser_sound_goal : Prop
  ; generated_parser_complete_goal : Prop
  }.

Definition generated_parser_of_table (table : certified_table) : generated_parser :=
  mkGeneratedParser table (parse table) (parse_sound_statement table) (parse_complete_statement table).

Definition generate_parser : ErrM generated_parser :=
  match generated_table with
  | inl err => inl err
  | inr table => inr (generated_parser_of_table table)
  end.

Theorem certified_action_table_in_candidates (table : certified_table) (entry : action_entry)
  (IN : entry ∈ table.(certified_action_table))
  : entry ∈ action_candidates.
Proof.
  pose proof (build_action_table_loop_in_inv action_candidates [] table.(certified_action_table) entry table.(certified_action_table_eq) IN) as [IN_nil | IN_candidates].
  - contradiction.
  - exact IN_candidates.
Qed.

Lemma lookup_action_sound (table : list action_entry) (st : state) (tok : aug_token) (act : action)
  (LOOKUP : lookup_action table st tok = Some act)
  : exists entry, entry ∈ table /\ entry.(action_entry_state) = st /\ entry.(action_entry_token) = tok /\ entry.(action_entry_action) = act.
Proof.
  revert st tok act LOOKUP. induction table as [ | entry table IH]; simpl; intros st tok act LOOKUP.
  - discriminate.
  - destruct (eqb (action_entry_state entry) st && eqb (action_entry_token entry) tok) eqn: EQ.
    + inv LOOKUP. exists entry. rewrite andb_true_iff in EQ. destruct EQ as [EQ_st EQ_tok]. rewrite eqb_eq in EQ_st. rewrite eqb_eq in EQ_tok. splits; [left; reflexivity | exact EQ_st | exact EQ_tok | reflexivity].
    + pose proof (IH st tok act LOOKUP) as (entry' & IN & EQ_st & EQ_tok & EQ_act). exists entry'. splits; [right; exact IN | exact EQ_st | exact EQ_tok | exact EQ_act].
Qed.

Lemma lookup_action_complete (table : list action_entry) (entry : action_entry)
  (IN : entry ∈ table)
  (UNIQUE : forall other, other ∈ table -> other.(action_entry_state) = entry.(action_entry_state) -> other.(action_entry_token) = entry.(action_entry_token) -> other.(action_entry_action) = entry.(action_entry_action))
  : lookup_action table entry.(action_entry_state) entry.(action_entry_token) = Some entry.(action_entry_action).
Proof.
  induction table as [ | other table IH]; simpl in IN |- *.
  - contradiction.
  - destruct IN as [EQ | IN].
    + subst other. replace (eqb (action_entry_state entry) (action_entry_state entry)) with true by (symmetry; rewrite eqb_eq; reflexivity). replace (eqb (action_entry_token entry) (action_entry_token entry)) with true by (symmetry; rewrite eqb_eq; reflexivity). reflexivity.
    + destruct (eqb (action_entry_state other) (action_entry_state entry) && eqb (action_entry_token other) (action_entry_token entry)) eqn: EQ.
      * rewrite andb_true_iff in EQ. destruct EQ as [EQ_st EQ_tok]. rewrite eqb_eq in EQ_st. rewrite eqb_eq in EQ_tok. f_equal. eapply UNIQUE; [left; reflexivity | exact EQ_st | exact EQ_tok].
      * eapply IH.
        { exact IN. }
          { intros other' IN' EQ_st EQ_tok. eapply UNIQUE; [right; exact IN' | exact EQ_st | exact EQ_tok]. }
Qed.

Lemma insert_action_entry_lookup_inserted (entry : action_entry) (table : list action_entry) (table' : list action_entry)
  (INSERT : insert_action_entry entry table = inr table')
  : lookup_action table' entry.(action_entry_state) entry.(action_entry_token) = Some entry.(action_entry_action).
Proof.
  revert table' INSERT. induction table as [ | head table IH]; simpl; intros table' INSERT.
  - inv INSERT. simpl. replace (eqb (action_entry_state entry) (action_entry_state entry)) with true by (symmetry; rewrite eqb_eq; reflexivity). replace (eqb (action_entry_token entry) (action_entry_token entry)) with true by (symmetry; rewrite eqb_eq; reflexivity). reflexivity.
  - destruct (action_entry_same_key head entry) eqn: SAME.
    + destruct (eqb (action_entry_action head) (action_entry_action entry)) eqn: SAME_ACTION; try discriminate. inv INSERT. simpl. unfold action_entry_same_key in SAME. rewrite andb_true_iff in SAME. destruct SAME as [EQ_st EQ_tok]. replace (eqb (action_entry_state head) (action_entry_state entry)) with true by (symmetry; exact EQ_st). replace (eqb (action_entry_token head) (action_entry_token entry)) with true by (symmetry; exact EQ_tok). rewrite eqb_eq in SAME_ACTION. rewrite SAME_ACTION. reflexivity.
    + destruct (insert_action_entry entry table) as [err | rest'] eqn: INSERT_rest; try discriminate. inv INSERT. simpl. unfold action_entry_same_key in SAME. replace (eqb (action_entry_state head) (action_entry_state entry) && eqb (action_entry_token head) (action_entry_token entry)) with false by (symmetry; exact SAME). eapply IH. reflexivity.
Qed.

Lemma insert_action_entry_preserves_lookup (entry : action_entry) (table : list action_entry) (table' : list action_entry) (st : state) (tok : aug_token) (act : action)
  (INSERT : insert_action_entry entry table = inr table')
  (LOOKUP : lookup_action table st tok = Some act)
  : lookup_action table' st tok = Some act.
Proof.
  revert table' st tok act INSERT LOOKUP. induction table as [ | head table IH]; simpl; intros table' st tok act INSERT LOOKUP.
  - discriminate.
  - destruct (action_entry_same_key head entry) eqn: SAME.
    + destruct (eqb (action_entry_action head) (action_entry_action entry)) eqn: SAME_ACTION; inv INSERT. exact LOOKUP.
    + destruct (insert_action_entry entry table) as [err | rest'] eqn: INSERT_rest; try discriminate. inv INSERT. simpl. destruct (eqb (action_entry_state head) st && eqb (action_entry_token head) tok) eqn: KEY.
      * exact LOOKUP.
      * eapply IH; [reflexivity | exact LOOKUP].
Qed.

Lemma build_action_table_loop_preserves_lookup (entries : list action_entry) (acc : list action_entry) (table : list action_entry) (st : state) (tok : aug_token) (act : action)
  (BUILD : build_action_table_loop entries acc = inr table)
  (LOOKUP : lookup_action acc st tok = Some act)
  : lookup_action table st tok = Some act.
Proof.
  revert acc table st tok act BUILD LOOKUP. induction entries as [ | entry entries IH]; simpl; intros acc table st tok act BUILD LOOKUP.
  - inv BUILD. exact LOOKUP.
  - destruct (insert_action_entry entry acc) as [err | acc'] eqn: INSERT; try discriminate. eapply IH; [exact BUILD | ]. eapply insert_action_entry_preserves_lookup; [exact INSERT | exact LOOKUP].
Qed.

Lemma build_action_table_loop_lookup_from_entries (entries : list action_entry) (acc : list action_entry) (table : list action_entry) (entry : action_entry)
  (BUILD : build_action_table_loop entries acc = inr table)
  (IN : entry ∈ entries)
  : lookup_action table entry.(action_entry_state) entry.(action_entry_token) = Some entry.(action_entry_action).
Proof.
  revert acc table entry BUILD IN. induction entries as [ | head entries IH]; simpl; intros acc table entry BUILD IN.
  - contradiction.
  - destruct (insert_action_entry head acc) as [err | acc'] eqn: INSERT; try discriminate. destruct IN as [EQ | IN].
    + subst head. eapply build_action_table_loop_preserves_lookup; [exact BUILD | ]. eapply insert_action_entry_lookup_inserted. exact INSERT.
    + eapply IH; [exact BUILD | exact IN].
Qed.

Definition action_table_conflict_free (table : list action_entry) : Prop :=
  forall entry1, forall entry2, entry1 ∈ table -> entry2 ∈ table -> entry1.(action_entry_state) = entry2.(action_entry_state) -> entry1.(action_entry_token) = entry2.(action_entry_token) -> entry1.(action_entry_action) = entry2.(action_entry_action).

Lemma action_entry_same_key_true_iff (entry1 : action_entry) (entry2 : action_entry)
  : action_entry_same_key entry1 entry2 = true <-> entry1.(action_entry_state) = entry2.(action_entry_state) /\ entry1.(action_entry_token) = entry2.(action_entry_token).
Proof.
  unfold action_entry_same_key. rewrite andb_true_iff. split.
  - intros [EQ_st EQ_tok]. rewrite eqb_eq in EQ_st. rewrite eqb_eq in EQ_tok. split; [exact EQ_st | exact EQ_tok].
  - intros [EQ_st EQ_tok]. split; rewrite eqb_eq; assumption.
Qed.

Lemma action_table_conflict_free_tail (head : action_entry) (table : list action_entry)
  (CONFLICT_FREE : action_table_conflict_free (head :: table))
  : action_table_conflict_free table.
Proof.
  intros entry1 entry2 IN1 IN2 EQ_st EQ_tok. eapply CONFLICT_FREE; [right; exact IN1 | right; exact IN2 | exact EQ_st | exact EQ_tok].
Qed.

Lemma insert_action_entry_existing_same_key_action (entry : action_entry) (table : list action_entry) (table' : list action_entry) (old : action_entry)
  (CONFLICT_FREE : action_table_conflict_free table)
  (INSERT : insert_action_entry entry table = inr table')
  (IN_old : old ∈ table)
  (EQ_st : old.(action_entry_state) = entry.(action_entry_state))
  (EQ_tok : old.(action_entry_token) = entry.(action_entry_token))
  : old.(action_entry_action) = entry.(action_entry_action).
Proof.
  revert table' old INSERT IN_old EQ_st EQ_tok. induction table as [ | head table IH]; simpl; intros table' old INSERT IN_old EQ_st EQ_tok.
  - contradiction.
  - destruct (action_entry_same_key head entry) eqn: SAME.
    + destruct (eqb (action_entry_action head) (action_entry_action entry)) eqn: SAME_ACTION; inv INSERT.
      rewrite eqb_eq in SAME_ACTION. destruct IN_old as [EQ | IN_old].
      * subst head. exact SAME_ACTION.
      * pose proof (proj1 (action_entry_same_key_true_iff head entry) SAME) as [EQ_st_head EQ_tok_head].
        transitivity head.(action_entry_action).
        { eapply CONFLICT_FREE; [right; exact IN_old | left; reflexivity | congruence | congruence]. }
        { exact SAME_ACTION. }
    + destruct (insert_action_entry entry table) as [err | rest'] eqn: INSERT_rest; try discriminate.
      destruct IN_old as [EQ | IN_old].
      * subst head. exfalso. assert (KEY : action_entry_same_key old entry = true) by (rewrite action_entry_same_key_true_iff; split; [exact EQ_st | exact EQ_tok]). congruence.
      * eapply IH.
        { eapply action_table_conflict_free_tail. exact CONFLICT_FREE. }
        { exact eq_refl. }
        { exact IN_old. }
        { exact EQ_st. }
        { exact EQ_tok. }
Qed.

Lemma insert_action_entry_conflict_free (entry : action_entry) (table : list action_entry) (table' : list action_entry)
  (CONFLICT_FREE : action_table_conflict_free table)
  (INSERT : insert_action_entry entry table = inr table')
  : action_table_conflict_free table'.
Proof.
  intros entry1 entry2 IN1 IN2 EQ_st EQ_tok.
  pose proof (insert_action_entry_in_inv entry table table' entry1 INSERT IN1) as [EQ1 | IN1_old].
  - subst entry1.
    pose proof (insert_action_entry_in_inv entry table table' entry2 INSERT IN2) as [EQ2 | IN2_old].
    + subst entry2. reflexivity.
    + symmetry. eapply insert_action_entry_existing_same_key_action; [exact CONFLICT_FREE | exact INSERT | exact IN2_old | symmetry; exact EQ_st | symmetry; exact EQ_tok].
  - pose proof (insert_action_entry_in_inv entry table table' entry2 INSERT IN2) as [EQ2 | IN2_old].
    + subst entry2. eapply insert_action_entry_existing_same_key_action; [exact CONFLICT_FREE | exact INSERT | exact IN1_old | exact EQ_st | exact EQ_tok].
    + eapply CONFLICT_FREE; [exact IN1_old | exact IN2_old | exact EQ_st | exact EQ_tok].
Qed.

Lemma build_action_table_loop_conflict_free (entries : list action_entry) (acc : list action_entry) (table : list action_entry)
  (CONFLICT_FREE : action_table_conflict_free acc)
  (BUILD : build_action_table_loop entries acc = inr table)
  : action_table_conflict_free table.
Proof.
  revert acc table CONFLICT_FREE BUILD. induction entries as [ | entry entries IH]; simpl; intros acc table CONFLICT_FREE BUILD.
  - inv BUILD. exact CONFLICT_FREE.
  - destruct (insert_action_entry entry acc) as [err | acc'] eqn: INSERT; try discriminate.
    eapply IH; [ | exact BUILD]. eapply insert_action_entry_conflict_free; [exact CONFLICT_FREE | exact INSERT].
Qed.

Lemma action_table_conflict_free_nil
  : action_table_conflict_free [].
Proof.
  intros entry1 entry2 IN1 _ _ _. contradiction.
Qed.

Theorem certified_action_table_conflict_free (table : certified_table)
  : action_table_conflict_free table.(certified_action_table).
Proof.
  eapply build_action_table_loop_conflict_free.
  - eapply action_table_conflict_free_nil.
  - exact table.(certified_action_table_eq).
Qed.

Definition theorem_flow_statement (table : certified_table) : Prop :=
  (forall v, forall tok, tok \in Read v <-> tok \in (@DigraphFixedpoint.reachable reads_graph v >>= DR)) /\ (forall v, forall tok, tok \in Follow v <-> tok \in (@DigraphFixedpoint.reachable includes_graph v >>= Read)) /\ (forall red, forall tok, tok \in LA red <-> (exists v, lookback red v /\ tok \in Follow v)) /\ action_table_conflict_free table.(certified_action_table) /\ parse_sound_statement table.

Theorem theorem_flow_statement_intro (table : certified_table)
  (PARSER_SOUND : parse_sound_statement table)
  : theorem_flow_statement table.
Proof.
  unfold theorem_flow_statement. splits.
  - intros v tok. eapply Read_iff_reads_reachable_DR.
  - intros v tok. eapply Follow_iff_includes_reachable_Read.
  - intros red tok. eapply LA_iff_lookback_Follow.
  - eapply certified_action_table_conflict_free.
  - exact PARSER_SOUND.
Qed.

Theorem theorem_flow_statement_sound (table : certified_table)
  : theorem_flow_statement table.
Proof.
  eapply theorem_flow_statement_intro. eapply parse_sound.
Qed.

Theorem lookup_action_deterministic_from_conflict_free (table : list action_entry) (st : state) (tok : aug_token) (act1 : action) (act2 : action)
  (CONFLICT_FREE : action_table_conflict_free table)
  (LOOKUP1 : lookup_action table st tok = Some act1)
  (LOOKUP2 : lookup_action table st tok = Some act2)
  : act1 = act2.
Proof.
  pose proof (lookup_action_sound table st tok act1 LOOKUP1) as (entry1 & IN1 & EQ_st1 & EQ_tok1 & EQ_act1).
  pose proof (lookup_action_sound table st tok act2 LOOKUP2) as (entry2 & IN2 & EQ_st2 & EQ_tok2 & EQ_act2).
  rewrite <- EQ_act1. rewrite <- EQ_act2. eapply CONFLICT_FREE; [exact IN1 | exact IN2 | congruence | congruence].
Qed.

Lemma lookup_goto_sound (table : list goto_entry) (st : state) (nt : aug_nonterminal) (target : state)
  (LOOKUP : lookup_goto table st nt = Some target)
  : exists entry, entry ∈ table /\ entry.(goto_entry_state) = st /\ entry.(goto_entry_nonterminal) = nt /\ entry.(goto_entry_target) = target.
Proof.
  revert st nt target LOOKUP. induction table as [ | entry table IH]; simpl; intros st nt target LOOKUP.
  - discriminate.
  - destruct (eqb (goto_entry_state entry) st && eqb (goto_entry_nonterminal entry) nt) eqn: EQ.
    + inv LOOKUP. exists entry. rewrite andb_true_iff in EQ. destruct EQ as [EQ_st EQ_nt]. rewrite eqb_eq in EQ_st. rewrite eqb_eq in EQ_nt. splits; [left; reflexivity | exact EQ_st | exact EQ_nt | reflexivity].
    + pose proof (IH st nt target LOOKUP) as (entry' & IN & EQ_st & EQ_nt & EQ_target). exists entry'. splits; [right; exact IN | exact EQ_st | exact EQ_nt | exact EQ_target].
Qed.

Lemma nt_transition_of_lr0_transition_sound (tr : lr0_transition) (raw : raw_nt_transition)
  (IN_tr : tr ∈ lr0_transitions)
  (IN : raw ∈ nt_transition_of_lr0_transition tr)
  : (raw.(raw_ntx_source), symbol_nonterminal raw.(raw_ntx_nonterminal), raw.(raw_ntx_target)) ∈ lr0_transitions.
Proof.
  destruct tr as [[src [tok | nt]] tgt]; simpl in IN; try contradiction. destruct IN as [EQ | []]. subst raw. exact IN_tr.
Qed.

Lemma raw_nt_transitions_sound (raw : raw_nt_transition)
  (IN : raw ∈ raw_nt_transitions)
  : (raw.(raw_ntx_source), symbol_nonterminal raw.(raw_ntx_nonterminal), raw.(raw_ntx_target)) ∈ lr0_transitions.
Proof.
  unfold raw_nt_transitions in IN. rewrite in_flat_map in IN. destruct IN as (tr & IN_tr & IN_raw). pose proof (nt_transition_of_lr0_transition_sound tr raw IN_tr IN_raw) as IN_lr0. exact IN_lr0.
Qed.

Lemma goto_entries_sound (entry : goto_entry)
  (IN : entry ∈ goto_entries)
  : (entry.(goto_entry_state), symbol_nonterminal entry.(goto_entry_nonterminal), entry.(goto_entry_target)) ∈ lr0_transitions.
Proof.
  unfold goto_entries in IN. rewrite in_map_iff in IN. destruct IN as (raw & EQ & IN_raw). subst entry. simpl. eapply raw_nt_transitions_sound. exact IN_raw.
Qed.

Theorem certified_goto_lookup_sound (table : certified_table) (st : state) (nt : aug_nonterminal) (target : state)
  (LOOKUP : lookup_goto table.(certified_goto_table) st nt = Some target)
  : lr0_next st (symbol_nonterminal nt) = Some target.
Proof.
  pose proof (lookup_goto_sound table.(certified_goto_table) st nt target LOOKUP) as (entry & IN_table & EQ_st & EQ_nt & EQ_target).
  rewrite table.(certified_goto_table_eq) in IN_table. pose proof (goto_entries_sound entry IN_table) as IN_lr0. pose proof (lr0_transitions_sound entry.(goto_entry_state) (symbol_nonterminal entry.(goto_entry_nonterminal)) entry.(goto_entry_target) IN_lr0) as (_ & _ & NEXT). congruence.
Qed.

Lemma lookup_goto_complete (table : list goto_entry) (entry : goto_entry)
  (IN : entry ∈ table)
  (UNIQUE : forall other, other ∈ table -> other.(goto_entry_state) = entry.(goto_entry_state) -> other.(goto_entry_nonterminal) = entry.(goto_entry_nonterminal) -> other.(goto_entry_target) = entry.(goto_entry_target))
  : lookup_goto table entry.(goto_entry_state) entry.(goto_entry_nonterminal) = Some entry.(goto_entry_target).
Proof.
  induction table as [ | other table IH]; simpl in IN |- *.
  - contradiction.
  - destruct IN as [EQ | IN].
    + subst other. replace (eqb (goto_entry_state entry) (goto_entry_state entry)) with true by (symmetry; rewrite eqb_eq; reflexivity). replace (eqb (goto_entry_nonterminal entry) (goto_entry_nonterminal entry)) with true by (symmetry; rewrite eqb_eq; reflexivity). reflexivity.
    + destruct (eqb (goto_entry_state other) (goto_entry_state entry) && eqb (goto_entry_nonterminal other) (goto_entry_nonterminal entry)) eqn: EQ.
      * rewrite andb_true_iff in EQ. destruct EQ as [EQ_st EQ_nt]. rewrite eqb_eq in EQ_st. rewrite eqb_eq in EQ_nt. f_equal. eapply UNIQUE; [left; reflexivity | exact EQ_st | exact EQ_nt].
      * eapply IH.
        { exact IN. }
        { intros other' IN' EQ_st EQ_nt. eapply UNIQUE; [right; exact IN' | exact EQ_st | exact EQ_nt]. }
Qed.

Theorem certified_shift_action_sound (table : certified_table) (st : state) (tok : aug_token) (tgt : state)
  (LOOKUP : lookup_action table.(certified_action_table) st tok = Some (Shift tgt))
  : (st, symbol_terminal tok, tgt) ∈ lr0_transitions.
Proof.
  pose proof (lookup_action_sound table.(certified_action_table) st tok (Shift tgt) LOOKUP) as (entry & IN_table & EQ_st & EQ_tok & EQ_act).
  pose proof (certified_action_table_in_candidates table entry IN_table) as IN_candidates.
  pose proof (action_candidates_sound entry IN_candidates) as [IN_shift | [IN_reduce | IN_accept]].
  - pose proof (shift_action_entries_sound entry IN_shift) as (src & tok0 & tgt0 & IN_tr & EQ_entry). subst entry. simpl in *. subst src tok0. inv EQ_act. exact IN_tr.
  - pose proof (reduce_action_entries_sound entry IN_reduce) as (red & tok0 & IN_red & IN_tok & EQ_entry). subst entry. simpl in *. discriminate.
  - pose proof (accept_action_entries_sound entry IN_accept) as (red & IN_red & EQ_prod & EQ_entry). subst entry. simpl in *. discriminate.
Qed.

Theorem certified_shift_action_complete (table : certified_table) (st : state) (tok : aug_token) (tgt : state)
  (IN : (st, symbol_terminal tok, tgt) ∈ lr0_transitions)
  : lookup_action table.(certified_action_table) st tok = Some (Shift tgt).
Proof.
  eapply build_action_table_loop_lookup_from_entries with (entry := mkActionEntry st tok (Shift tgt)).
  - exact table.(certified_action_table_eq).
  - unfold action_candidates. rewrite in_app_iff. left. unfold shift_action_entries. rewrite in_flat_map. exists (st, symbol_terminal tok, tgt). split; [exact IN | simpl; left; reflexivity].
Qed.

Theorem certified_reduce_action_sound (table : certified_table) (st : state) (tok : aug_token) (prod : aug_production)
  (LOOKUP : lookup_action table.(certified_action_table) st tok = Some (Reduce prod))
  : exists red, red ∈ all_reduction_candidates /\ tok ∈ LA' red /\ red.(reduction_state) = st /\ red.(reduction_prod) = prod.
Proof.
  pose proof (lookup_action_sound table.(certified_action_table) st tok (Reduce prod) LOOKUP) as (entry & IN_table & EQ_st & EQ_tok & EQ_act).
  pose proof (certified_action_table_in_candidates table entry IN_table) as IN_candidates.
  pose proof (action_candidates_sound entry IN_candidates) as [IN_shift | [IN_reduce | IN_accept]].
  - pose proof (shift_action_entries_sound entry IN_shift) as (src & tok0 & tgt0 & IN_tr & EQ_entry). subst entry. simpl in *. discriminate.
  - pose proof (reduce_action_entries_sound entry IN_reduce) as (red & tok0 & IN_red & IN_tok & EQ_entry). subst entry. simpl in *. inv EQ_act. exists red. splits; [exact IN_red | exact IN_tok | reflexivity | reflexivity].
  - pose proof (accept_action_entries_sound entry IN_accept) as (red & IN_red & EQ_prod & EQ_entry). subst entry. simpl in *. discriminate.
Qed.

Theorem certified_reduce_action_complete (table : certified_table) (red : reduction_candidate) (tok : aug_token)
  (IN_red : red ∈ all_reduction_candidates)
  (IN_tok : tok ∈ LA' red)
  : lookup_action table.(certified_action_table) red.(reduction_state) tok = Some (Reduce red.(reduction_prod)).
Proof.
  eapply build_action_table_loop_lookup_from_entries with (entry := mkActionEntry red.(reduction_state) tok (Reduce red.(reduction_prod))).
  - exact table.(certified_action_table_eq).
  - unfold action_candidates. rewrite in_app_iff. right. rewrite in_app_iff. left. unfold reduce_action_entries. rewrite in_flat_map. exists red. split; [exact IN_red | ]. rewrite in_map_iff. exists tok. split; [reflexivity | exact IN_tok].
Qed.

Theorem certified_accept_action_sound (table : certified_table) (st : state) (tok : aug_token)
  (LOOKUP : lookup_action table.(certified_action_table) st tok = Some Accept)
  : exists red, red ∈ all_reduction_candidates /\ red.(reduction_state) = st /\ red.(reduction_prod) = aug_start /\ tok = end_marker.
Proof.
  pose proof (lookup_action_sound table.(certified_action_table) st tok Accept LOOKUP) as (entry & IN_table & EQ_st & EQ_tok & EQ_act).
  pose proof (certified_action_table_in_candidates table entry IN_table) as IN_candidates.
  pose proof (action_candidates_sound entry IN_candidates) as [IN_shift | [IN_reduce | IN_accept]].
  - pose proof (shift_action_entries_sound entry IN_shift) as (src & tok0 & tgt0 & IN_tr & EQ_entry). subst entry. simpl in *. discriminate.
  - pose proof (reduce_action_entries_sound entry IN_reduce) as (red & tok0 & IN_red & IN_tok & EQ_entry). subst entry. simpl in *. discriminate.
  - pose proof (accept_action_entries_sound entry IN_accept) as (red & IN_red & EQ_prod & EQ_entry). subst entry. simpl in *. exists red. splits; [exact IN_red | exact EQ_st | exact EQ_prod | symmetry; exact EQ_tok].
Qed.

Theorem certified_accept_action_complete (table : certified_table) (red : reduction_candidate)
  (IN_red : red ∈ all_reduction_candidates)
  (EQ_prod : red.(reduction_prod) = aug_start)
  : lookup_action table.(certified_action_table) red.(reduction_state) end_marker = Some Accept.
Proof.
  eapply build_action_table_loop_lookup_from_entries with (entry := mkActionEntry red.(reduction_state) end_marker Accept).
  - exact table.(certified_action_table_eq).
  - unfold action_candidates. rewrite in_app_iff. right. rewrite in_app_iff. right. unfold accept_action_entries. rewrite in_flat_map. exists red. split; [exact IN_red | ]. rewrite EQ_prod. simpl. left. reflexivity.
Qed.

Lemma item_closure_successors_sound (it : item) (prod : aug_production) (nt : aug_nonterminal)
  (NEXT : next_symbol it = Some (symbol_nonterminal nt))
  (PROD : prod ∈ productions_for nt)
  : initial_item_of_production prod ∈ item_closure_successors it.
Proof.
  unfold item_closure_successors. rewrite NEXT. rewrite in_map_iff. exists prod. split; [reflexivity | exact PROD].
Qed.

Lemma productions_for_sound (nt : aug_nonterminal) (prod : aug_production)
  (IN : prod ∈ productions_for nt)
  : aug_lhs prod = nt.
Proof.
  unfold productions_for, production_starts_with in IN. rewrite filter_In in IN.
  destruct IN as [_ EQ]. rewrite eqb_eq in EQ. exact EQ.
Qed.

Lemma productions_for_complete (nt : aug_nonterminal) (prod : aug_production)
  (LHS : aug_lhs prod = nt)
  : prod ∈ productions_for nt.
Proof.
  unfold productions_for, production_starts_with. rewrite filter_In. split.
  - eapply all_aug_productions_complete.
  - rewrite eqb_eq. exact LHS.
Qed.

End PGS.
