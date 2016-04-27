Require Import List.
Require Import PeanoNat.
Require Import Orders.
Require Import MSetList.
Require Import Omega.

Require Import sflib.

Require Import Basic.

Set Implicit Arguments.
Import ListNotations.


Module Loc := Ident.
Module LocSet := IdentSet.
Module LocMap := IdentMap.
Module LocFun := IdentFun.


Module Const := Nat.


Module Ordering.
  (* TODO: support the unordered/monotonic atomics (#46) *)
  (* TODO: support the SC atomics (#40) *)
  Inductive t :=
  | relaxed
  | acquire
  | release
  | relacq
  | sc
  .

  Definition le (lhs rhs:t): bool :=
    match lhs, rhs with
    | relaxed, _ => true
    | _, relaxed => false

    | _, sc => true
    | sc, _ => false

    | _, relacq => true
    | relacq, _ => false

    | acquire, release => false
    | acquire, acquire => true

    | release, acquire => false
    | release, release => true
    end.
End Ordering.


Module MemEvent.
  Inductive t :=
  | read (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | write (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | update (loc:Loc.t) (valr valw:Const.t) (ord:Ordering.t)
  | fence (ord:Ordering.t)
  .

  Definition is_writing (e:t): option (Loc.t * Const.t * Ordering.t) :=
    match e with
    | read _ _ _ => None
    | write loc val ord => Some (loc, val, ord)
    | update loc _ val ord => Some (loc, val, ord)
    | fence _ => None
    end.

  Definition is_writing_to (loc:Loc.t) (e:t): option(Const.t * Ordering.t) :=
    match is_writing e with
    | None => None
    | Some (loc', val, ord) =>
      if Loc.eq_dec loc' loc
      then Some (val, ord)
      else None
    end.

  Definition is_reading (e:t): option (Loc.t * Const.t * Ordering.t) :=
    match e with
    | read loc val ord => Some (loc, val, ord)
    | write _ _ _ => None
    | update loc val _ ord => Some (loc, val, ord)
    | fence _ => None
    end.

  Definition get_ordering (e:t): Ordering.t :=
    match e with
    | read _ _ ord => ord
    | write _ _ ord => ord
    | update _ _ _ ord => ord
    | fence ord => ord
    end.
End MemEvent.


(* TODO: In reality, on the contrary to what is currently defined,
 * syscalls may change the memory.
 *)
(* NOTE: Syscall's results are not predictable.
 * Hence we disallow syscalls in the consistency check.
 *)
Module Event.
  Structure t := mk {
    output: Const.t;
    inputs: list Const.t;
  }.
End Event.


Module ThreadEvent.
  Inductive t :=
  | mem (e:MemEvent.t)
  | syscall (e:Event.t)
  .
End ThreadEvent.
