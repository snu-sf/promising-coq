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
  | acqrel
  | sc
  .

  Inductive le: forall (lhs rhs:t), Prop :=
  | le_relaxed_o o:
      le relaxed o
  | le_o_sc o:
      le o sc
  | le_acqrel_acqrel:
      le acqrel acqrel
  .

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. destruct x; econs.
  Qed.
  Next Obligation.
    ii. inv H; inv H0; econs.
  Qed.

  Definition le_dec (lhs rhs:t): {le lhs rhs} + {~ le lhs rhs}.
  Proof.
    destruct lhs, rhs;
      (try by left; econs);
      (try by right; intro X; inv X).
  Defined.
  Global Opaque le_dec.
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
