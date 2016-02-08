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
  .

  Inductive le: forall (lhs rhs:t), Prop :=
  | le_refl ord: le ord ord
  | relaxed_ rhs: le relaxed rhs
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

  Definition is_reading (e:Event.t): option (Loc.t * Const.t) :=
    match e with
    | read loc val _ => Some (loc, val)
    | write loc _ _ => None
    | update loc val _ _ => Some (loc, val)
    end.

  Definition is_writing (e:Event.t): option (Loc.t * Const.t) :=
    match e with
    | read _ _ _ => None
    | write loc val _ => Some (loc, val)
    | update loc _ val _ => Some (loc, val)
    end.
End Event.
