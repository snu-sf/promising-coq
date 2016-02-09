Require Import List.
Require Import PeanoNat.
Require Import Equalities.

Require Import Basic.

Module Loc.
  Include Ident.
End Loc.

Module Const := Nat.

Module Ordering.
  Inductive t :=
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

Module RWEvent <: DecidableType.
  Inductive t_ :=
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

  Definition is_writing (e:t): option (Loc.t * Const.t) :=
    match e with
    | read _ _ _ => None
    | write loc val _ => Some (loc, val)
    | update loc _ val _ => Some (loc, val)
    end.

  Definition get_ordering (e:t): Ordering.t :=
    match e with
    | read _ _ ord => ord
    | write _ _ ord => ord
    | update _ _ _ ord => ord
    end.
End RWEvent.

Module Event <: DecidableType.
  Structure t_ := mk {
    lhs: Const.t;
    rhses: list Const.t;
  }.
  Definition t := t_.

  Definition eq := @eq t.
  Program Instance eq_equiv: Equivalence eq.
  Definition eq_dec (x y:t): {eq x y} + {~ eq x y}.
  Proof.
    unfold eq.
    decide equality;
      (try apply list_eq_dec);
      (try apply Const.eq_dec).
  Qed.
End Event.

Module ThreadEvent <: DecidableType.
  Inductive t_ :=
  | rw (e:RWEvent.t)
  | fence (ord:Ordering.t)
  | syscall (e:Event.t)
  .
  Definition t := t_.

  Definition eq := @eq t.
  Program Instance eq_equiv: Equivalence eq.
  Definition eq_dec (x y:t): {eq x y} + {~ eq x y}.
  Proof.
    unfold eq.
    decide equality;
      (try apply RWEvent.eq_dec);
      (try apply Ordering.eq_dec);
      (try apply Event.eq_dec).
  Qed.
End ThreadEvent.
