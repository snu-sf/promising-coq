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


Lemma add_lower_add
      mem1 loc from to val released released' mem2
      (ADD: Memory.add mem1 loc from to val released mem2)
      (REL_LE: Capability.le released' released)
      (REL_WF: Capability.wf released'):
  exists mem2', Memory.add mem1 loc from to val released' mem2'.
Proof.
  apply Memory.add_exists; auto.
  - inv ADD. inv ADD0. eauto.
  - inv ADD. inv ADD0. auto.
Qed.

Lemma split_lower_split
      mem1 loc from to1 to2 val released released' mem2
      (SPLIT: Memory.split mem1 loc from to1 to2 val released mem2)
      (REL_LE: Capability.le released' released)
      (REL_WF: Capability.wf released'):
  exists mem2', Memory.split mem1 loc from to1 to2 val released' mem2'.
Proof.
  exploit Memory.split_get0; eauto. i. des.
  eapply Memory.split_exists; eauto.
  - inv SPLIT. inv SPLIT0. auto.
  - inv SPLIT. inv SPLIT0. auto.
Qed.

Lemma lower_lower_lower
      mem1 loc from to val released0 released released' mem2
      (LOWER: Memory.lower mem1 loc from to val released0 released mem2)
      (REL_LE: Capability.le released' released)
      (REL_WF: Capability.wf released'):
  exists mem2', Memory.lower mem1 loc from to val released0 released' mem2'.
Proof.
  inv LOWER.
  exploit add_lower_add; eauto. i. des.
  esplits. econs; eauto.
  etrans; eauto.
Qed.

Lemma promise_lower_promise
      promises1 mem1 loc from to val released released' promises2 mem2 kind
      (PROMISE: Memory.promise promises1 mem1 loc from to val released promises2 mem2 kind)
      (REL_LE: Capability.le released' released)
      (REL_WF: Capability.wf released'):
  exists promises2' mem2',
    Memory.promise promises1 mem1 loc from to val released' promises2' mem2' kind.
Proof.
  inv PROMISE.
  - exploit add_lower_add; try apply PROMISES; eauto. i. des.
    exploit add_lower_add; try apply MEM; eauto. i. des.
    esplits. econs; eauto.
    etrans; eauto. apply REL_LE.
  - exploit split_lower_split; try apply PROMISES; eauto. i. des.
    exploit split_lower_split; try apply MEM; eauto. i. des.
    esplits. econs; eauto.
    etrans; eauto. apply REL_LE.
  - exploit lower_lower_lower; try apply PROMISES; eauto. i. des.
    exploit lower_lower_lower; try apply MEM; eauto. i. des.
    esplits. econs; eauto.
Qed.

Lemma write_lower_write
      promises1 mem1 loc from to val released released' promises2 mem2 kind
      (WRITE: Memory.write promises1 mem1 loc from to val released promises2 mem2 kind)
      (REL_LE: Capability.le released' released)
      (REL_WF: Capability.wf released'):
  exists promises2' mem2',
    Memory.write promises1 mem1 loc from to val released' promises2' mem2' kind.
Proof.
  inv WRITE. exploit promise_lower_promise; eauto. i. des.
  exploit Memory.promise_get2; eauto. i.
  exploit Memory.remove_exists; eauto. i. des.
  esplits. econs; eauto.
Qed.

Lemma remove_promise_remove
      promises0 mem0 loc from to val released1 released2 promises2
      (PRMOISES: Memory.le promises0 mem0)
      (REL_LE: Capability.le released2 released1)
      (REL_WF1: Capability.wf released1)
      (REL_WF2: Capability.wf released2)
      (TIME: Time.lt from to)
      (REMOVE: Memory.remove promises0 loc from to val released1 promises2):
  exists promises1' mem1',
    <<PROMISE: Memory.promise promises0 mem0 loc from to val released2 promises1' mem1' Memory.promise_kind_lower>> /\
    <<REMOVE: Memory.remove promises1' loc from to val released2 promises2>> /\
    <<MEM: Memory.sim mem0 mem1'>>.
Proof.
  exploit Memory.remove_get0; eauto. i.
  exploit Memory.promise_exists_same; try apply x0; eauto. i. des.
  exploit promise_lower_promise; eauto. i. des.
  esplits; eauto.
  - admit. (* Memory.remove *)
  - inv x2. econs 2; eauto. econs 2. eauto.
Admitted.

Lemma promise_time_lt
      promises1 mem1 loc from to val released promises2 mem2 kind
      (PROMISE: Memory.promise promises1 mem1 loc from to val released promises2 mem2 kind):
  Time.lt from to.
Proof.
  inv PROMISE.
  - inv MEM. inv ADD. auto.
  - inv MEM. inv SPLIT. auto.
  - inv MEM. inv ADD. inv ADD0. auto.
Qed.

Lemma write_time_lt
      promises1 mem1 loc from to val released promises2 mem2 kind
      (WRITE: Memory.write promises1 mem1 loc from to val released promises2 mem2 kind):
  Time.lt from to.
Proof.
  inv WRITE. eapply promise_time_lt. eauto.
Qed.
