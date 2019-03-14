Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
From Paco Require Import paco.

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
  Lemma add_lower_add
        mem0 loc from to val released1 released2 mem1 mem2
        (ADD1: Memory.add mem0 loc from to val released1 mem1)
        (LOWER2: Memory.lower mem1 loc from to val released1 released2 mem2):
    Memory.add mem0 loc from to val released2 mem2.
  Proof.
    inv ADD1. inv ADD. inv LOWER2. inv LOWER.
    rewrite LocFun.add_add_eq. econs; auto.
    unfold Cell.add in *.
    destruct r, r0. ss. subst.
    unfold LocFun.add. condtac; [|congr]. s.
    rewrite DOMap.add_add_eq. econs; auto.
  Qed.

  Lemma split_lower_split
        mem0 loc ts1 ts2 ts3 val2 val3 released2 released2' released3 mem1 mem2
        (SPLIT1: Memory.split mem0 loc ts1 ts2 ts3 val2 val3 released2 released3 mem1)
        (LOWER2: Memory.lower mem1 loc ts1 ts2 val2 released2 released2' mem2):
    Memory.split mem0 loc ts1 ts2 ts3 val2 val3 released2' released3 mem2.
  Proof.
    inv SPLIT1. inv SPLIT. inv LOWER2. inv LOWER.
    rewrite LocFun.add_add_eq. econs; auto.
    unfold Cell.split in *.
    destruct r, r0. ss. subst.
    unfold LocFun.add. condtac; [|congr]. s.
    rewrite DOMap.add_add_eq. econs; auto.
  Qed.

  Lemma lower_lower_lower
        mem0 loc from to val released0 released1 released2 mem1 mem2
        (LOWER1: Memory.lower mem0 loc from to val released0 released1 mem1)
        (LOWER2: Memory.lower mem1 loc from to val released1 released2 mem2):
    Memory.lower mem0 loc from to val released0 released2 mem2.
  Proof.
    inv LOWER1. inv LOWER. inv LOWER2. inv LOWER.
    rewrite LocFun.add_add_eq. econs; auto.
    unfold Cell.lower in *.
    destruct r, r0. ss. subst.
    unfold LocFun.add. condtac; [|congr]. s.
    rewrite DOMap.add_add_eq. econs; auto.
    etrans; eauto.
  Qed.

  Lemma promise_promise_promise
        loc from to val released1 released2 promises0 promises1 promises2 mem0 mem1 mem2 kind
        (PROMISE1: Memory.promise promises0 mem0 loc from to val released1 promises1 mem1 kind)
        (PROMISE2: Memory.promise promises1 mem1 loc from to val released2 promises2 mem2 (Memory.op_kind_lower released1)):
    Memory.promise promises0 mem0 loc from to val released2 promises2 mem2 kind.
  Proof.
    inv PROMISE2. inv PROMISE1.
    - econs; eauto.
      + eapply add_lower_add; eauto.
      + eapply add_lower_add; eauto.
    - econs; eauto.
      + eapply split_lower_split; eauto.
      + eapply split_lower_split; eauto.
    - econs; eauto.
      + eapply lower_lower_lower; eauto.
      + eapply lower_lower_lower; eauto.
  Qed.
End MemoryMerge.
