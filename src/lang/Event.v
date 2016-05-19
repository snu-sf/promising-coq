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
  (* TODO: support the SC atomics (#40) *)
  Inductive t :=
  | nonatomic
  | relaxed
  | acqrel
  | seqcst
  .

  Definition le (lhs rhs:t): bool :=
    match lhs, rhs with
    | nonatomic, _ => true
    | _, nonatomic => false

    | relaxed, _ => true
    | _, relaxed => false

    | acqrel, _ => true
    | _, acqrel => false

    | seqcst, seqcst => true
    end.
  Global Opaque le.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. destruct x; auto.
  Qed.
  Next Obligation.
    ii. destruct x, y, z; auto.
  Qed.
End Ordering.


Module MemEvent.
  Inductive t :=
  | read (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | write (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | update (loc:Loc.t) (valr valw:Const.t) (ordr ordw:Ordering.t)
  | fence (ordr ordw:Ordering.t)
  .
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
