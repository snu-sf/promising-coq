Require Import PeanoNat.
Require Import Equalities.

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

  Definition eq_dec (x y:t): {x = y} + {x <> y}.
  Proof. decide equality. Qed.
End Ordering.

Module Event <: DecidableType.
  Inductive t_: Type :=
  | read (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | write (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | update (loc:Loc.t) (rval wval:Const.t) (ord:Ordering.t)
  .
  Definition t := t_.

  Definition eq := @eq t.
  Program Instance eq_equiv: Equivalence eq.
  Definition eq_dec (x y:t): {eq x y} + {~ eq x y}.
  Proof.
    unfold eq.
    decide equality;
      (try apply Loc.eq_dec);
      (try apply Const.eq_dec);
      (try apply Ordering.eq_dec).
  Qed.
End Event.
