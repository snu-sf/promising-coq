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
  (* NOTE: we curently do not support the nonatomics (#61).  Nonatomic
     accesses differ from plain accesses in that nonatomic accesses may
     corrupt data in the presence of a race.

     Even in Java, a data race may result in out-of-thin-air integral
     values.  But even with data races, it is impossible to forge an
     out-of-thin-air reference values.  See the link for more details:
     https://docs.oracle.com/javase/specs/jls/se7/html/jls-17.html#jls-17.7

     Hence, our compilation scheme for Java normal accesses is as
     follows.
     - Normal accesses to pointers are compiled to plain accesses.
     - Normal accesses to numbers are compiled to nonatomic accesses.
   *)
  Inductive t :=
  | plain
  | relaxed
  | acqrel
  | seqcst
  .

  Definition le (lhs rhs:t): bool :=
    match lhs, rhs with
    | plain, _ => true
    | _, plain => false

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


(* NOTE (syscall): In fact, syscalls may change the memory, on the
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

  Definition is_reading (e:t): option (Loc.t * Ordering.t) :=
    match e with
    | read loc _ ord => Some (loc, ord)
    | update loc _ _ ordr _ => Some (loc, ordr)
    | _ => None
    end.

  Definition is_writing (e:t): option (Loc.t * Ordering.t) :=
    match e with
    | write loc _ ord => Some (loc, ord)
    | update loc _ _ _ ordw => Some (loc, ordw)
    | _ => None
    end.

  Inductive ord: forall (e1 e2:t), Prop :=
  | ord_read
      l v o1 o2
      (O: Ordering.le o1 o2):
      ord (read l v o1) (read l v o2)
  | ord_write
      l v o1 o2
      (O: Ordering.le o1 o2):
      ord (write l v o1) (write l v o2)
  | ord_update
      l vr vw or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (update l vr vw or1 ow1) (update l vr vw or2 ow2)
  | ord_fence
      or1 or2 ow1 ow2
      (OR: Ordering.le or1 or2)
      (OW: Ordering.le ow1 ow2):
      ord (fence or1 ow1) (fence or2 ow2)
  | ord_syscall
      e:
      ord (syscall e) (syscall e)
  .

  Inductive ord_opt: forall (e1 e2:option t), Prop :=
  | ord_opt_none:
      ord_opt None None
  | ord_opt_some
      e1 e2
      (ORD: ord e1 e2):
      ord_opt (Some e1) (Some e2)
  .
End ProgramEvent.
