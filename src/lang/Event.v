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
  | strong_relaxed
  | acqrel
  | seqcst
  .

  Definition le (lhs rhs:t): bool :=
    match lhs, rhs with
    | plain, _ => true
    | _, plain => false

    | relaxed, _ => true
    | _, relaxed => false

    | strong_relaxed, _ => true
    | _, strong_relaxed => false

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

  Definition join (lhs rhs:t): t :=
    match lhs, rhs with
    | plain, _ => rhs
    | _, plain => lhs

    | relaxed, _ => rhs
    | _, relaxed => lhs

    | strong_relaxed, _ => rhs
    | _, strong_relaxed => lhs

    | acqrel, _ => rhs
    | _, acqrel => lhs

    | seqcst, _ => rhs
    end.

  Lemma join_comm lhs rhs: join lhs rhs = join rhs lhs.
  Proof. destruct lhs, rhs; ss. Qed.

  Lemma join_assoc a b c: join (join a b) c = join a (join b c).
  Proof. destruct a, b, c; ss. Qed.

  Lemma join_l lhs rhs:
    le lhs (join lhs rhs).
  Proof. destruct lhs, rhs; ss. Qed.

  Lemma join_r lhs rhs:
    le rhs (join lhs rhs).
  Proof. destruct lhs, rhs; ss. Qed.

  Lemma join_spec lhs rhs o
        (LHS: le lhs o)
        (RHS: le rhs o):
    le (join lhs rhs) o.
  Proof. destruct lhs, rhs; ss. Qed.

  Lemma join_cases lhs rhs:
    join lhs rhs = lhs \/ join lhs rhs = rhs.
  Proof. destruct lhs, rhs; auto. Qed.
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
  | silent
  | read (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | write (loc:Loc.t) (val:Const.t) (ord:Ordering.t)
  | update (loc:Loc.t) (valr valw:Const.t) (ordr ordw:Ordering.t)
  | fence (ordr ordw:Ordering.t)
  | syscall (e:Event.t)
  .

  Definition is_reading (e:t): option (Loc.t * Const.t * Ordering.t) :=
    match e with
    | read loc val ord => Some (loc, val, ord)
    | update loc valr _ ordr _ => Some (loc, valr, ordr)
    | _ => None
    end.

  Definition is_writing (e:t): option (Loc.t * Const.t * Ordering.t) :=
    match e with
    | write loc val ord => Some (loc, val, ord)
    | update loc _ valw _ ordw => Some (loc, valw, ordw)
    | _ => None
    end.

  Inductive ord: forall (e1 e2:t), Prop :=
  | ord_silent:
      ord silent silent
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
End ProgramEvent.
