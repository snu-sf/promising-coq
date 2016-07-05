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
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Commit.
Require Import Thread.
Require Import Configuration.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import FulfillStep.
Require Import MemoryReorder.

Set Implicit Arguments.


Lemma reorder_promise_program_diff
      loc from to val released kind lc1 lc1'
      e2 lang2 st2 st2' lc2 lc2'
      sc0 mem0
      mem1
      sc2 mem2
      (STEP1: Local.promise_step lc1 mem0 loc from to val released lc1' mem1 kind)
      (STEP2: Thread.program_step e2 (Thread.mk lang2 st2 lc2 sc0 mem1) (Thread.mk lang2 st2' lc2' sc2 mem2))
      (E2: forall ord, ThreadEvent.is_reading e2 <> Some (loc, to, val, released, ord)):
  exists mem1',
    <<STEP1: Thread.program_step e2 (Thread.mk lang2 st2 lc2 sc0 mem0) (Thread.mk lang2 st2' lc2' sc2 mem1')>> /\
    <<STEP2: Local.promise_step lc1 mem1' loc from to val released lc1' mem2 kind>>.
Proof.
Admitted.
