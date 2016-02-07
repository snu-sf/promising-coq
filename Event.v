Require Import PeanoNat.

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

Module Const := Nat.
