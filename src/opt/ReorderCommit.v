Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful5.

Require Import Basic.
Require Import Event.
Require Import Language.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Commit.
Require Import Thread.

Require Import Configuration.
Require Import Simulation.
Require Import Compatibility.
Require Import MemInv.
Require Import Progress.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma read_read_commit
      loc1 ts1 released1 ord1
      loc2 ts2 released2 ord2
      commit0
      (LOC: loc1 = loc2 -> Ordering.le ord1 Ordering.unordered)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Commit.wf commit0)
      (WF1: Capability.wf released1)
      (WF2: Capability.wf released2):
  Commit.le
    (Commit.read_commit
       (Commit.read_commit commit0 loc2 ts2 released2 ord2)
       loc1 ts1 released1 ord1)
    (Commit.read_commit
       (Commit.read_commit commit0 loc1 ts1 released1 ord1)
       loc2 ts2 released2 ord2).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    (try by condtac; aggrtac).
Qed.

Lemma read_write_commit
      loc1 ts1 released1 ord1
      loc2 ts2 ord2
      commit0 sc0
      (LOC: loc1 <> loc2)
      (ORD: Ordering.le ord1 Ordering.acqrel \/ Ordering.le ord2 Ordering.acqrel)
      (WF0: Commit.wf commit0)
      (WF1: Capability.wf released1):
  Commit.le
    (Commit.read_commit
       (Commit.write_commit commit0 sc0 loc2 ts2 ord2)
       loc1 ts1 released1 ord1)
    (Commit.write_commit
       (Commit.read_commit commit0 loc1 ts1 released1 ord1)
       sc0 loc2 ts2 ord2).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    (try by condtac; aggrtac).
  repeat condtac; aggrtac; try apply WF0.
Qed.

Lemma read_read_fence_commit
      loc1 ts1 released1 ord1
      ord2
      commit0
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Commit.wf commit0)
      (WF1: Capability.wf released1):
  Commit.le
    (Commit.read_commit
       (Commit.read_fence_commit commit0 ord2)
       loc1 ts1 released1 ord1)
    (Commit.read_fence_commit
       (Commit.read_commit commit0 loc1 ts1 released1 ord1)
       ord2).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    (try by condtac; aggrtac).
  - repeat condtac; aggrtac; try apply WF0.
  - repeat condtac; aggrtac; try apply WF0.
Qed.

Lemma read_write_fence_commit
      loc1 ts1 released1 ord1
      ord2
      commit0 sc0
      (WF0: Commit.wf commit0)
      (WF1: Capability.wf released1):
  Commit.le
    (Commit.read_commit
       (Commit.write_fence_commit commit0 sc0 ord2)
       loc1 ts1 released1 ord1)
    (Commit.write_fence_commit
       (Commit.read_commit commit0 loc1 ts1 released1 ord1)
       sc0 ord2).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    (try by condtac; aggrtac).
  - unfold Commit.write_fence_sc;
    repeat (condtac; aggrtac).
  - unfold Commit.write_fence_sc.
    repeat (condtac; aggrtac).
  - unfold Commit.write_fence_sc.
    repeat (condtac; aggrtac).
Qed.

Lemma write_read_commit
      loc1 ts1 ord1
      loc2 ts2 released2 ord2
      commit0 sc0
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Commit.wf commit0)
      (WF2: Capability.wf released2):
  Commit.le
    (Commit.write_commit
       (Commit.read_commit commit0 loc2 ts2 released2 ord2)
       sc0 loc1 ts1 ord1)
    (Commit.read_commit
       (Commit.write_commit commit0 sc0 loc1 ts1 ord1)
       loc2 ts2 released2 ord2).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    (try by condtac; aggrtac).
  - condtac; aggrtac. condtac.
    + destruct ord1; inv ORD1; inv COND0.
    + aggrtac; try apply WF0.
Qed.

Lemma write_write_commit
      loc1 ts1 ord1
      loc2 ts2 ord2
      commit0 sc0
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: Commit.wf commit0):
  Commit.le
    (Commit.write_commit
       (Commit.write_commit commit0 sc0 loc2 ts2 ord2)
       (Commit.write_sc sc0 loc2 ts2 ord2)
       loc1 ts1 ord1)
    (Commit.write_commit
       (Commit.write_commit commit0 sc0 loc1 ts1 ord1)
       (Commit.write_sc sc0 loc1 ts1 ord1)
       loc2 ts2 ord2).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    (repeat (condtac; aggrtac; try apply WF0)).
  - rewrite <- ? Capability.join_r.
    econs; aggrtac. apply CommitFacts.write_sc_incr.
  - rewrite <- ? Capability.join_r.
    econs; aggrtac. apply CommitFacts.write_sc_incr.
  - rewrite <- ? Capability.join_r.
    econs; aggrtac. apply CommitFacts.write_sc_incr.
Qed.

Lemma write_write_sc
      loc1 ts1 ord1
      loc2 ts2 ord2
      sc0
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed):
  TimeMap.le
    (Commit.write_sc
       (Commit.write_sc sc0 loc2 ts2 ord2)
       loc1 ts1 ord1)
    (Commit.write_sc
       (Commit.write_sc sc0 loc1 ts1 ord1)
       loc2 ts2 ord2).
Proof.
  ii. unfold Commit.write_sc. aggrtac.
Qed.

Lemma read_fence_write_commit
      ord1
      loc2 ts2 ord2
      commit0 sc0
      (ORD1: Ordering.le ord1 Ordering.acqrel)
      (WF0: Commit.wf commit0):
  Commit.le
    (Commit.read_fence_commit
       (Commit.write_commit commit0 sc0 loc2 ts2 ord2)
       ord1)
    (Commit.write_commit
       (Commit.read_fence_commit commit0 ord1)
       sc0 loc2 ts2 ord2).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    (repeat (condtac; aggrtac; try apply WF0)).
  - rewrite <- Capability.join_r.
    rewrite <- ? Capability.join_l.
    apply WF0.
  - rewrite <- Capability.join_r.
    rewrite <- ? Capability.join_l.
    apply WF0.
Qed.

Lemma write_fence_write_commit
      ord1
      loc2 ts2 ord2
      commit0 sc0
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: Commit.wf commit0):
  Commit.le
    (Commit.write_fence_commit
       (Commit.write_commit commit0 sc0 loc2 ts2 ord2)
       (Commit.write_sc sc0 loc2 ts2 ord2)
       ord1)
    (Commit.write_commit
       (Commit.write_fence_commit commit0 sc0 ord1)
       sc0 loc2 ts2 ord2).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    (repeat (condtac; aggrtac; try apply WF0)).
Qed.

Lemma write_fence_write_sc
      ord1
      loc2 ts2 ord2
      commit0 sc0
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: Commit.wf commit0):
  TimeMap.le
    (Commit.write_fence_sc
       (Commit.write_commit commit0 sc0 loc2 ts2 ord2)
       (Commit.write_sc sc0 loc2 ts2 ord2)
       ord1)
    (Commit.write_sc
       (Commit.write_fence_sc commit0 sc0 ord1)
       loc2 ts2 ord2).
Proof.
  ii. unfold Commit.write_sc, Commit.write_fence_sc.
  repeat condtac; aggrtac.
Qed.

Lemma read_fence_write_fence_commit
      ord1
      ord2
      commit0 sc0
      (WF0: Commit.wf commit0):
  Commit.le
    (Commit.read_fence_commit
       (Commit.write_fence_commit commit0 sc0 ord2)
       ord1)
    (Commit.write_fence_commit
       (Commit.read_fence_commit commit0 ord1)
       sc0 ord2).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    (try by condtac; aggrtac).
  - condtac; aggrtac.
    + condtac; aggrtac.
      rewrite <- Capability.join_r.
      rewrite <- Capability.join_l.
      apply WF0.
    + condtac; aggrtac.
      rewrite <- ? Capability.join_r.
      unfold Commit.write_fence_sc. repeat (condtac; aggrtac).
      rewrite <- TimeMap.join_r. apply WF0.
  - condtac; aggrtac.
    + condtac; aggrtac.
      rewrite <- ? Capability.join_r.
      unfold Commit.write_fence_sc. repeat (condtac; aggrtac).
      rewrite <- TimeMap.join_r. apply WF0.
    + condtac; aggrtac.
      rewrite <- Capability.join_r.
      unfold Commit.write_fence_sc. repeat (condtac; aggrtac).
  - condtac; aggrtac.
    rewrite <- ? Capability.join_r.
    unfold Commit.write_fence_sc. repeat (condtac; aggrtac).
    rewrite <- TimeMap.join_r. apply WF0.
Qed.
