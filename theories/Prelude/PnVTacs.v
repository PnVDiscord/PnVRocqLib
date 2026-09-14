Require Export Stdlib.micromega.Lia.
Require Import PnV.Prelude.Notations.
Require Export PnV.Prelude.SfLib.

Tactic Notation "rewrite*" uconstr( t ) "by" ident ( H_EQ ) :=
  let lhs := fresh "lhs" in
  set (lhs := t) in |- *;
  match type of H_EQ with
  | ?X = ?Y => change (lhs = Y) in H_EQ; rewrite -> H_EQ; subst lhs
  end.

Tactic Notation "find" simple_intropattern( p ) "by" uconstr( H ) :=
  unshelve hexploit H; [eauto .. | intros p].

Tactic Notation "find*" simple_intropattern( p ) "by" uconstr( H ) :=
  hexploit H; [eauto .. | intros p].

Module Tac_obtain_private.

Definition _Tag (cnt : nat) : Set :=
  unit.

#[universes(template), projections(primitive)]
Record _TaggedLock (tag : nat) (A : Type) : Type :=
  _mkTaggedLock { _unTaggedLock : A } as lock.

#[global] Arguments _mkTaggedLock {tag} {A}.
#[global] Arguments _unTaggedLock {tag} {A} lock.

Ltac new_tag_cnt :=
  let TAG_cnt := fresh "TAG_cnt" in
  refine (let TAG_cnt : _Tag 0 := tt in _);
  clearbody TAG_cnt.

Ltac load arg :=
  let Shelf := fresh "Shelf" in
  match goal with
  | [ TAG_cnt : _Tag ?n |- _ ] =>
    refine (let Shelf : _TaggedLock n _ := _mkTaggedLock arg in _);
    change (_Tag (S n)) in TAG_cnt
  end.

Ltac free_all :=
  repeat (
    match goal with
    | [ Shelf : _TaggedLock _ _ |- _ ] => subst Shelf
    end
  );
  repeat (
    match goal with
    | [ TAG_cnt : _Tag _ |- _ ] => clear TAG_cnt
    end
  ).

Ltac isSort A :=
  lazymatch A with
  | Set => idtac
  | Type => idtac
  | Prop => idtac
  | SProp => idtac
  | _ => fail
  end.

Ltac unify_arg_type expected actual :=
  first
  [ unify expected actual
  | isSort expected;
    isSort actual
  ].

Ltac all_consumed idx :=
  match goal with
  | [ TAG_cnt : _Tag ?total |- _ ] => constr_eq idx total
  end.

Ltac xapply idx prf :=
  lazymatch type of prf with
  | forall x : ?A, _ =>
    first
    [ lazymatch goal with
      | [ Shelf := @_mkTaggedLock _ ?A' ?arg : _TaggedLock idx _ |- _ ] =>
        tryif is_evar A then fail else unify_arg_type A A';
        xapply constr:(S idx) (prf arg)
      end
    | isSort A;
      let _RET_ := fresh "_RET_" in
      epose proof (prf _) as _RET_;
      xapply idx _RET_;
      clear _RET_
    | let _RET_ := fresh "_RET_" in
      unshelve epose proof (prf _) as _RET_;
      [ idtac
      | xapply idx _RET_;
        clear _RET_
      ]
    | lazymatch goal with
      | [ Shelf := @_mkTaggedLock _ ?A' ?arg : _TaggedLock idx _ |- _ ] =>
        unify_arg_type A A';
        xapply constr:(S idx) (prf arg)
      end
    ]
  | let _ := _ in _ =>
    let _RET_ := fresh "_RET_" in
    epose proof prf as _RET_;
    cbv zeta in _RET_;
    xapply idx _RET_;
    clear _RET_
  | ?T =>
    tryif all_consumed idx then (
      let _RET_ := fresh "_RET_" in
      epose proof (_RET_ := prf);
      revert _RET_
    ) else (
      xapply_hidden idx prf T
    )
  end
with xapply_hidden idx prf T :=
  first
  [ lazymatch T with
    | ?P <-> ?Q =>
      lazymatch goal with
      | [ Shelf := @_mkTaggedLock _ ?A' _ : _TaggedLock idx _ |- _ ] =>
        first
        [ unify P A'; xapply idx constr:(@proj1 (P -> Q) (Q -> P) prf)
        | unify Q A'; xapply idx constr:(@proj2 (P -> Q) (Q -> P) prf)
        | xapply idx constr:(@proj1 (P -> Q) (Q -> P) prf)
        | xapply idx constr:(@proj2 (P -> Q) (Q -> P) prf)
        ]
      end
    | ?L /\ ?R =>
      first
      [ xapply idx constr:(@proj1 L R prf)
      | xapply idx constr:(@proj2 L R prf)
      ]
    end
  | let T' := eval red in T in
    tryif constr_eq T T' then fail else xapply idx constr:(prf : T')
  | let T' := eval hnf in T in
    tryif constr_eq T T' then fail else xapply idx constr:(prf : T')
  | fail 1 "obtain: not all supplied arguments were consumed"
  ].

Ltac prepare func :=
  unshelve (
    let _RET_ := fresh "_RET_" in
    let func := open_constr:(func) in
    epose proof func as _RET_;
    xapply constr:(0) _RET_;
    (try clear _RET_);
    shelve
  );
  free_all.

Ltac last :=
  first
  [ typeclasses eauto
  | congruence
  | tauto
  | lia
  | eauto
  ].

Ltac infer_premise :=
  lazymatch goal with
  | |- ?T =>
    let S := type of T in
    lazymatch S with
    | Prop => last
    | _ => shelve
    end
  end.

Ltac fire func :=
  unshelve (
    prepare func;
    [ infer_premise.. | shelve ]
  ).

End Tac_obtain_private.

Tactic Notation "obtain" simple_intropattern( ret ) "with" "*" "by" uconstr( func ) :=
  find* ret by func.

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.load arg4; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.load arg4; Tac_obtain_private.load arg5; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.load arg4; Tac_obtain_private.load arg5; Tac_obtain_private.load arg6; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.load arg4; Tac_obtain_private.load arg5; Tac_obtain_private.load arg6; Tac_obtain_private.load arg7; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.load arg4; Tac_obtain_private.load arg5; Tac_obtain_private.load arg6; Tac_obtain_private.load arg7; Tac_obtain_private.load arg8; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.load arg4; Tac_obtain_private.load arg5; Tac_obtain_private.load arg6; Tac_obtain_private.load arg7; Tac_obtain_private.load arg8; Tac_obtain_private.load arg9; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.load arg4; Tac_obtain_private.load arg5; Tac_obtain_private.load arg6; Tac_obtain_private.load arg7; Tac_obtain_private.load arg8; Tac_obtain_private.load arg9; Tac_obtain_private.load arg10; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.load arg4; Tac_obtain_private.load arg5; Tac_obtain_private.load arg6; Tac_obtain_private.load arg7; Tac_obtain_private.load arg8; Tac_obtain_private.load arg9; Tac_obtain_private.load arg10; Tac_obtain_private.load arg11; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) uconstr( arg12 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.load arg4; Tac_obtain_private.load arg5; Tac_obtain_private.load arg6; Tac_obtain_private.load arg7; Tac_obtain_private.load arg8; Tac_obtain_private.load arg9; Tac_obtain_private.load arg10; Tac_obtain_private.load arg11; Tac_obtain_private.load arg12; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) uconstr( arg12 ) uconstr( arg13 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.load arg4; Tac_obtain_private.load arg5; Tac_obtain_private.load arg6; Tac_obtain_private.load arg7; Tac_obtain_private.load arg8; Tac_obtain_private.load arg9; Tac_obtain_private.load arg10; Tac_obtain_private.load arg11; Tac_obtain_private.load arg12; Tac_obtain_private.load arg13; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) uconstr( arg12 ) uconstr( arg13 ) uconstr( arg14 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.load arg4; Tac_obtain_private.load arg5; Tac_obtain_private.load arg6; Tac_obtain_private.load arg7; Tac_obtain_private.load arg8; Tac_obtain_private.load arg9; Tac_obtain_private.load arg10; Tac_obtain_private.load arg11; Tac_obtain_private.load arg12; Tac_obtain_private.load arg13; Tac_obtain_private.load arg14; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) uconstr( arg12 ) uconstr( arg13 ) uconstr( arg14 ) uconstr( arg15 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.load arg4; Tac_obtain_private.load arg5; Tac_obtain_private.load arg6; Tac_obtain_private.load arg7; Tac_obtain_private.load arg8; Tac_obtain_private.load arg9; Tac_obtain_private.load arg10; Tac_obtain_private.load arg11; Tac_obtain_private.load arg12; Tac_obtain_private.load arg13; Tac_obtain_private.load arg14; Tac_obtain_private.load arg15; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) uconstr( arg12 ) uconstr( arg13 ) uconstr( arg14 ) uconstr( arg15 ) uconstr( arg16 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.load arg4; Tac_obtain_private.load arg5; Tac_obtain_private.load arg6; Tac_obtain_private.load arg7; Tac_obtain_private.load arg8; Tac_obtain_private.load arg9; Tac_obtain_private.load arg10; Tac_obtain_private.load arg11; Tac_obtain_private.load arg12; Tac_obtain_private.load arg13; Tac_obtain_private.load arg14; Tac_obtain_private.load arg15; Tac_obtain_private.load arg16; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) uconstr( arg12 ) uconstr( arg13 ) uconstr( arg14 ) uconstr( arg15 ) uconstr( arg16 ) uconstr( arg17 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.load arg4; Tac_obtain_private.load arg5; Tac_obtain_private.load arg6; Tac_obtain_private.load arg7; Tac_obtain_private.load arg8; Tac_obtain_private.load arg9; Tac_obtain_private.load arg10; Tac_obtain_private.load arg11; Tac_obtain_private.load arg12; Tac_obtain_private.load arg13; Tac_obtain_private.load arg14; Tac_obtain_private.load arg15; Tac_obtain_private.load arg16; Tac_obtain_private.load arg17; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) uconstr( arg12 ) uconstr( arg13 ) uconstr( arg14 ) uconstr( arg15 ) uconstr( arg16 ) uconstr( arg17 ) uconstr( arg18 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.load arg4; Tac_obtain_private.load arg5; Tac_obtain_private.load arg6; Tac_obtain_private.load arg7; Tac_obtain_private.load arg8; Tac_obtain_private.load arg9; Tac_obtain_private.load arg10; Tac_obtain_private.load arg11; Tac_obtain_private.load arg12; Tac_obtain_private.load arg13; Tac_obtain_private.load arg14; Tac_obtain_private.load arg15; Tac_obtain_private.load arg16; Tac_obtain_private.load arg17; Tac_obtain_private.load arg18; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) uconstr( arg12 ) uconstr( arg13 ) uconstr( arg14 ) uconstr( arg15 ) uconstr( arg16 ) uconstr( arg17 ) uconstr( arg18 ) uconstr( arg19 ) "by" uconstr( func ) :=
  Tac_obtain_private.new_tag_cnt; Tac_obtain_private.load arg1; Tac_obtain_private.load arg2; Tac_obtain_private.load arg3; Tac_obtain_private.load arg4; Tac_obtain_private.load arg5; Tac_obtain_private.load arg6; Tac_obtain_private.load arg7; Tac_obtain_private.load arg8; Tac_obtain_private.load arg9; Tac_obtain_private.load arg10; Tac_obtain_private.load arg11; Tac_obtain_private.load arg12; Tac_obtain_private.load arg13; Tac_obtain_private.load arg14; Tac_obtain_private.load arg15; Tac_obtain_private.load arg16; Tac_obtain_private.load arg17; Tac_obtain_private.load arg18; Tac_obtain_private.load arg19; Tac_obtain_private.fire func; [Tac_obtain_private.last.. | intros ret].
