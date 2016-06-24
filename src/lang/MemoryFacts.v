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
  exploit Memory.promise_lower_promise; eauto. i. des.
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
