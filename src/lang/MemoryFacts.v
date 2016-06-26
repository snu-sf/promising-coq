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

(* TODO *)
Inductive sim_memory (mem_src mem_tgt:Memory.t): Prop :=
.

Lemma add_update_add
      mem0 loc from1 from2 to val released1 released2 mem1 mem2
      (ADD1: Memory.add mem0 loc from1 to val released1 mem1)
      (UPDATE2: Memory.update mem1 loc from1 from2 to val released1 released2 mem2):
  Memory.add mem0 loc from2 to val released2 mem2.
Proof.
Admitted.

Lemma update_update_update
      mem0 loc from0 from1 from2 to val released0 released1 released2 mem1 mem2
      (UPDATE1: Memory.update mem0 loc from0 from1 to val released0 released1 mem1)
      (UPDATE2: Memory.update mem1 loc from1 from2 to val released1 released2 mem2):
  Memory.update mem0 loc from0 from2 to val released0 released2 mem2.
Proof.
Admitted.

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

Lemma remove_promise_remove
      promises0 mem0 loc from to val released1 released2 promises2
      (PRMOISES: Memory.le promises0 mem0)
      (MEM: Memory.closed mem0)
      (REL_LE: Capability.le released2 released1)
      (REL_WF1: Capability.wf released1)
      (REL_WF2: Capability.wf released2)
      (TIME: Time.lt from to)
      (REMOVE: Memory.remove promises0 loc from to val released1 promises2):
  exists promises1' mem1',
    <<PROMISE: Memory.promise promises0 mem0 loc from to val released2 promises1' mem1' (Memory.promise_kind_update from released1)>> /\
    <<REMOVE: Memory.remove promises1' loc from to val released2 promises2>> /\
    <<MEM: sim_memory mem1' mem0>>.
Proof.
Admitted.

Lemma promise_time_lt
      promises1 mem1 loc from to val released promises2 mem2 kind
      (PROMISE: Memory.promise promises1 mem1 loc from to val released promises2 mem2 kind):
  Time.lt from to.
Proof.
  inv PROMISE.
  - inv MEM. inv ADD. auto.
  - inv MEM. inv UPDATE. auto.
Qed.

Lemma write_time_lt
      promises1 mem1 loc from to val released promises2 mem2 kind
      (WRITE: Memory.write promises1 mem1 loc from to val released promises2 mem2 kind):
  Time.lt from to.
Proof.
  inv WRITE. eapply promise_time_lt. eauto.
Qed.
