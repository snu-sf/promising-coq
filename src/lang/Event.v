Require Import List.
Require Import PeanoNat.
Require Import Orders.
Require Import MSetList.
Require Import Omega.

Require Import sflib.

Require Import Basic.
Require Import Time.

Set Implicit Arguments.
Import ListNotations.


Module Loc := Ident.
Module LocSet := IdentSet.
Module LocMap := IdentMap.
Module LocFun := IdentFun.


Module Const := Nat.


Module Ordering.
  (* TODO: support the nonatomics (#61).  Nonatomic accesses differ
     from unordered accesses in that nonatomic accesses may corrupt
     data in the presence of a race.

     NOTE: Even in Java, a data race may result in out-of-thin-air
     integral values.  But even with data races, it is impossible to
     forge an out-of-thin-air reference values.  See the link for more
     details:
     https://docs.oracle.com/javase/specs/jls/se7/html/jls-17.html#jls-17.7

     Hence, our compilation scheme for Java plain accesses is as follows.
     - Plain accesses to pointers are compiled to unordered accesses.
     - Plain accesses to numbers are compiled to nonatomic accesses.
   *)
  (* TODO: support the SC atomics (#40). *)
  Inductive t :=
  | unordered
  | relaxed
  | acqrel
  | seqcst
  .

  Definition le (lhs rhs:t): bool :=
    match lhs, rhs with
    | unordered, _ => true
    | _, unordered => false

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


(* TODO (syscall): In fact, syscalls may change the memory, on the
 * contrary to what is currently defined.
 *)
(* NOTE (syscall): we disallow syscalls in the validation of the
 * consistency check, as syscall's results are not predictable.
 *)
Module Event.
  Structure t := mk {
    output: Const.t;
    inputs: list Const.t;
  }.
End Event.


Module ProgramEvent.
  Inductive t :=
  | read (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | write (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | update (loc:Loc.t) (valr valw:Const.t) (ordr ordw:Ordering.t)
  | fence (ordr ordw:Ordering.t)
  | syscall (e:Event.t)
  .
End ProgramEvent.
