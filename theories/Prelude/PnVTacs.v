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

Module Tac_obtaion_private.

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

Ltac xapply idx prf :=
  lazymatch type of prf with
  | forall x : ?A, _ =>
    first
    [ lazymatch goal with
      | [ Shelf := @_mkTaggedLock _ ?A' ?arg : _TaggedLock idx _ |- _ ] =>
        unify_arg_type A A';
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
    ]
  | let _ := _ in _ =>
    let _RET_ := fresh "_RET_" in
    epose proof prf as _RET_;
    cbv zeta in _RET_;
    xapply idx _RET_;
    clear _RET_
  | _ =>
    match goal with
    | [ TAG_cnt : _Tag ?total |- _ ] =>
      first
      [ constr_eq idx total
      | fail 1 "obtain: not all supplied arguments were consumed"
      ]
    end;
    let _RET_ := fresh "_RET_" in
    epose proof (_RET_ := prf);
    revert _RET_
  end.

Ltac fire func :=
  let _RET_ := fresh "_RET_" in
  epose proof func as _RET_;
  xapply constr:(0) _RET_;
  try clear _RET_;
  free_all.

Ltac last :=
  first
  [ typeclasses eauto
  | congruence
  | tauto
  | lia
  | eauto
  ].

End Tac_obtaion_private.

Tactic Notation "obtain" simple_intropattern( ret ) "with" "*" "by" uconstr( func ) :=
  find* ret by func.

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.load arg4;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.load arg4;
  Tac_obtaion_private.load arg5;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.load arg4;
  Tac_obtaion_private.load arg5;
  Tac_obtaion_private.load arg6;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.load arg4;
  Tac_obtaion_private.load arg5;
  Tac_obtaion_private.load arg6;
  Tac_obtaion_private.load arg7;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.load arg4;
  Tac_obtaion_private.load arg5;
  Tac_obtaion_private.load arg6;
  Tac_obtaion_private.load arg7;
  Tac_obtaion_private.load arg8;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.load arg4;
  Tac_obtaion_private.load arg5;
  Tac_obtaion_private.load arg6;
  Tac_obtaion_private.load arg7;
  Tac_obtaion_private.load arg8;
  Tac_obtaion_private.load arg9;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.load arg4;
  Tac_obtaion_private.load arg5;
  Tac_obtaion_private.load arg6;
  Tac_obtaion_private.load arg7;
  Tac_obtaion_private.load arg8;
  Tac_obtaion_private.load arg9;
  Tac_obtaion_private.load arg10;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.load arg4;
  Tac_obtaion_private.load arg5;
  Tac_obtaion_private.load arg6;
  Tac_obtaion_private.load arg7;
  Tac_obtaion_private.load arg8;
  Tac_obtaion_private.load arg9;
  Tac_obtaion_private.load arg10;
  Tac_obtaion_private.load arg11;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) uconstr( arg12 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.load arg4;
  Tac_obtaion_private.load arg5;
  Tac_obtaion_private.load arg6;
  Tac_obtaion_private.load arg7;
  Tac_obtaion_private.load arg8;
  Tac_obtaion_private.load arg9;
  Tac_obtaion_private.load arg10;
  Tac_obtaion_private.load arg11;
  Tac_obtaion_private.load arg12;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) uconstr( arg12 ) uconstr( arg13 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.load arg4;
  Tac_obtaion_private.load arg5;
  Tac_obtaion_private.load arg6;
  Tac_obtaion_private.load arg7;
  Tac_obtaion_private.load arg8;
  Tac_obtaion_private.load arg9;
  Tac_obtaion_private.load arg10;
  Tac_obtaion_private.load arg11;
  Tac_obtaion_private.load arg12;
  Tac_obtaion_private.load arg13;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) uconstr( arg12 ) uconstr( arg13 ) uconstr( arg14 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.load arg4;
  Tac_obtaion_private.load arg5;
  Tac_obtaion_private.load arg6;
  Tac_obtaion_private.load arg7;
  Tac_obtaion_private.load arg8;
  Tac_obtaion_private.load arg9;
  Tac_obtaion_private.load arg10;
  Tac_obtaion_private.load arg11;
  Tac_obtaion_private.load arg12;
  Tac_obtaion_private.load arg13;
  Tac_obtaion_private.load arg14;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) uconstr( arg12 ) uconstr( arg13 ) uconstr( arg14 ) uconstr( arg15 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.load arg4;
  Tac_obtaion_private.load arg5;
  Tac_obtaion_private.load arg6;
  Tac_obtaion_private.load arg7;
  Tac_obtaion_private.load arg8;
  Tac_obtaion_private.load arg9;
  Tac_obtaion_private.load arg10;
  Tac_obtaion_private.load arg11;
  Tac_obtaion_private.load arg12;
  Tac_obtaion_private.load arg13;
  Tac_obtaion_private.load arg14;
  Tac_obtaion_private.load arg15;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) uconstr( arg12 ) uconstr( arg13 ) uconstr( arg14 ) uconstr( arg15 ) uconstr( arg16 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.load arg4;
  Tac_obtaion_private.load arg5;
  Tac_obtaion_private.load arg6;
  Tac_obtaion_private.load arg7;
  Tac_obtaion_private.load arg8;
  Tac_obtaion_private.load arg9;
  Tac_obtaion_private.load arg10;
  Tac_obtaion_private.load arg11;
  Tac_obtaion_private.load arg12;
  Tac_obtaion_private.load arg13;
  Tac_obtaion_private.load arg14;
  Tac_obtaion_private.load arg15;
  Tac_obtaion_private.load arg16;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) uconstr( arg12 ) uconstr( arg13 ) uconstr( arg14 ) uconstr( arg15 ) uconstr( arg16 ) uconstr( arg17 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.load arg4;
  Tac_obtaion_private.load arg5;
  Tac_obtaion_private.load arg6;
  Tac_obtaion_private.load arg7;
  Tac_obtaion_private.load arg8;
  Tac_obtaion_private.load arg9;
  Tac_obtaion_private.load arg10;
  Tac_obtaion_private.load arg11;
  Tac_obtaion_private.load arg12;
  Tac_obtaion_private.load arg13;
  Tac_obtaion_private.load arg14;
  Tac_obtaion_private.load arg15;
  Tac_obtaion_private.load arg16;
  Tac_obtaion_private.load arg17;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) uconstr( arg12 ) uconstr( arg13 ) uconstr( arg14 ) uconstr( arg15 ) uconstr( arg16 ) uconstr( arg17 ) uconstr( arg18 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.load arg4;
  Tac_obtaion_private.load arg5;
  Tac_obtaion_private.load arg6;
  Tac_obtaion_private.load arg7;
  Tac_obtaion_private.load arg8;
  Tac_obtaion_private.load arg9;
  Tac_obtaion_private.load arg10;
  Tac_obtaion_private.load arg11;
  Tac_obtaion_private.load arg12;
  Tac_obtaion_private.load arg13;
  Tac_obtaion_private.load arg14;
  Tac_obtaion_private.load arg15;
  Tac_obtaion_private.load arg16;
  Tac_obtaion_private.load arg17;
  Tac_obtaion_private.load arg18;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].

Tactic Notation "obtain" simple_intropattern( ret ) "with" uconstr( arg1 ) uconstr( arg2 ) uconstr( arg3 ) uconstr( arg4 ) uconstr( arg5 ) uconstr( arg6 ) uconstr( arg7 ) uconstr( arg8 ) uconstr( arg9 ) uconstr( arg10 ) uconstr( arg11 ) uconstr( arg12 ) uconstr( arg13 ) uconstr( arg14 ) uconstr( arg15 ) uconstr( arg16 ) uconstr( arg17 ) uconstr( arg18 ) uconstr( arg19 ) "by" uconstr( func ) :=
  Tac_obtaion_private.new_tag_cnt;
  Tac_obtaion_private.load arg1;
  Tac_obtaion_private.load arg2;
  Tac_obtaion_private.load arg3;
  Tac_obtaion_private.load arg4;
  Tac_obtaion_private.load arg5;
  Tac_obtaion_private.load arg6;
  Tac_obtaion_private.load arg7;
  Tac_obtaion_private.load arg8;
  Tac_obtaion_private.load arg9;
  Tac_obtaion_private.load arg10;
  Tac_obtaion_private.load arg11;
  Tac_obtaion_private.load arg12;
  Tac_obtaion_private.load arg13;
  Tac_obtaion_private.load arg14;
  Tac_obtaion_private.load arg15;
  Tac_obtaion_private.load arg16;
  Tac_obtaion_private.load arg17;
  Tac_obtaion_private.load arg18;
  Tac_obtaion_private.load arg19;
  Tac_obtaion_private.fire func;
  [Tac_obtaion_private.last.. | intros ret].
