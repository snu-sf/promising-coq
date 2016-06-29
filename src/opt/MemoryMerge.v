Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.

Set Implicit Arguments.


Module MemoryMerge.
  Lemma add_update_add
        mem0 loc from1 from2 to val released1 released2 mem1 mem2
        (ADD1: Memory.add mem0 loc from1 to val released1 mem1)
        (UPDATE2: Memory.update mem1 loc from1 from2 to val released1 released2 mem2):
    Memory.add mem0 loc from2 to val released2 mem2.
  Proof.
    inv ADD1. inv ADD. inv UPDATE2. inv UPDATE.
    rewrite LocFun.add_add_eq. econs; auto.
    unfold Cell.add, Cell.update in *.
    destruct r, r0. ss. subst.
    unfold LocFun.add. condtac; [|congr]. s.
    rewrite DOMap.add_add_eq. econs; auto. i.
    hexploit DISJOINT; eauto. ii. eapply H; eauto.
    eapply Interval.le_mem; try eexact LHS; eauto. econs; eauto. refl.
  Qed.

  Lemma update_update_update
        mem0 loc from0 from1 from2 to val released0 released1 released2 mem1 mem2
        (UPDATE1: Memory.update mem0 loc from0 from1 to val released0 released1 mem1)
        (UPDATE2: Memory.update mem1 loc from1 from2 to val released1 released2 mem2):
    Memory.update mem0 loc from0 from2 to val released0 released2 mem2.
  Proof.
    inv UPDATE1. inv UPDATE. inv UPDATE2. inv UPDATE.
    rewrite LocFun.add_add_eq. econs; auto.
    unfold Cell.update in *.
    destruct r, r0. ss. subst.
    unfold LocFun.add. condtac; [|congr]. s.
    rewrite DOMap.add_add_eq. econs; auto.
    - etrans; eauto.
    - etrans; eauto.
  Qed.

  Lemma promise_promise_promise
        loc from1 from2 to val released1 released2 promises0 promises1 promises2 mem0 mem1 mem2 kind
        (PROMISE1: Memory.promise promises0 mem0 loc from1 to val released1 promises1 mem1 kind)
        (PROMISE2: Memory.promise promises1 mem1 loc from2 to val released2 promises2 mem2 (Memory.promise_kind_update from1 released1)):
    Memory.promise promises0 mem0 loc from2 to val released2 promises2 mem2 kind.
  Proof.
    inv PROMISE2. inv PROMISE1.
    - econs; eauto.
      + eapply add_update_add; eauto.
      + eapply add_update_add; eauto.
    - econs; eauto.
      + eapply update_update_update; eauto.
      + eapply update_update_update; eauto.
  Qed.
End MemoryMerge.
