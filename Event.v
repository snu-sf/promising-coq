Require Import PeanoNat.

Require Import Basic.

Module Loc.
  Include Ident.
End Loc.

Module Const := Nat.

Module Ordering.
  Inductive t: Type :=
  | relaxed
  | acquire
  | release
  | relacq
  | seqcst
  .

  Inductive le: forall (lhs rhs:t), Prop :=
  | le_refl ord: le ord ord
  | relaxed_ rhs: le relaxed rhs
  | _seqcst lhs: le lhs seqcst
  | acquire_: le acquire relacq
  | release_: le release relacq
  .
End Ordering.

Module Event.
  Inductive t: Type :=
  | read (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | write (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | update (loc:Loc.t) (rval wval:Const.t) (ord:Ordering.t)
  .
End Event.
