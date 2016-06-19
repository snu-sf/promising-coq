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
      loc ts released ord1 ord2 ord
      commit0
      (ORD1: Ordering.le ord1 ord)
      (ORD2: Ordering.le ord2 ord)
      (WF0: Commit.wf commit0)
      (WF_REL: Capability.wf released):
  Commit.le
    (Commit.read_commit (Commit.read_commit commit0 loc ts released ord1) loc ts released ord2)
    (Commit.read_commit commit0 loc ts released ord).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    repeat condtac; aggrtac.
Qed.

Lemma write_read_commit
      loc ts ord1 ord2
      commit0 sc0
      (ORD: Ordering.le Ordering.seqcst ord2 -> Ordering.le Ordering.seqcst ord1)
      (WF0: Commit.wf commit0):
  Commit.le
    (Commit.read_commit (Commit.write_commit commit0 sc0 loc ts ord1) loc ts
                        ((Commit.write_commit commit0 sc0 loc ts ord1).(Commit.rel) loc)
                        ord2)
    (Commit.write_commit commit0 sc0 loc ts ord1).
Proof.
  econs; aggrtac;
    (try by apply WF0).
  - repeat condtac; aggrtac.
  - repeat condtac; aggrtac;
      rewrite <- ? Capability.join_l; apply WF0.
  - condtac; committac.
  - condtac; committac.
    { rewrite <- ? Capability.join_l. etrans; apply WF0. }
    repeat condtac; aggrtac; try apply WF0;
      rewrite <- ? Capability.join_l; apply WF0.
Qed.

Lemma write_write_commit
      loc ts1 ts2 ord1 ord2 ord
      (TS: Time.lt ts1 ts2)
      commit0 sc0
      (ORD1: Ordering.le ord1 ord)
      (ORD2: Ordering.le ord2 ord)
      (WF0: Commit.wf commit0):
  Commit.le
    (Commit.write_commit (Commit.write_commit commit0 sc0 loc ts1 ord1)
                         (Commit.write_sc sc0 loc ts1 ord1)
                         loc ts2 ord2)
    (Commit.write_commit commit0 sc0 loc ts2 ord).
Proof.
  econs; committac;
    (repeat (condtac; aggrtac));
    (try by apply WF0).
  - econs; committac. unfold Commit.write_sc. condtac; aggrtac.
  - econs; committac. unfold Commit.write_sc. condtac; aggrtac.
  - econs; committac. unfold Commit.write_sc. condtac; aggrtac.
Qed.

Lemma write_write_sc
      loc ts1 ts2 ord1 ord2 ord
      (TS: Time.lt ts1 ts2)
      commit0 sc0
      (ORD1: Ordering.le ord1 ord)
      (ORD2: Ordering.le ord2 ord)
      (WF0: Commit.wf commit0):
  TimeMap.le
    (Commit.write_sc (Commit.write_sc sc0 loc ts1 ord1)
                     loc ts2 ord2)
    (Commit.write_sc sc0 loc ts2 ord).
Proof.
  unfold Commit.write_sc. repeat (condtac; aggrtac).
Qed.

Lemma read_fence_read_fence_commit
      ord1 ord2 ord
      commit0
      (ORD1: Ordering.le ord1 ord)
      (ORD2: Ordering.le ord2 ord)
      (WF0: Commit.wf commit0):
  Commit.le
    (Commit.read_fence_commit (Commit.read_fence_commit commit0 ord1) ord2)
    (Commit.read_fence_commit commit0 ord).
Proof.
  econs; aggrtac;
    (try by apply WF0).
  repeat condtac; committac. apply WF0.
Qed.

Lemma write_fence_write_fence_sc
      ord1 ord2 ord
      commit0 sc0
      (ORD1: Ordering.le ord1 ord)
      (ORD2: Ordering.le ord2 ord)
      (WF0: Commit.wf commit0):
  TimeMap.le
    (Commit.write_fence_sc (Commit.write_fence_commit commit0 sc0 ord1) (Commit.write_fence_sc commit0 sc0 ord1) ord2)
    (Commit.write_fence_sc commit0 sc0 ord).
Proof.
  unfold Commit.write_fence_commit, Commit.write_fence_sc.
  repeat (condtac; aggrtac).
Qed.

Lemma write_fence_write_fence_commit
      ord1 ord2 ord
      commit0 sc0
      (ORD1: Ordering.le ord1 ord)
      (ORD2: Ordering.le ord2 ord)
      (WF0: Commit.wf commit0):
  Commit.le
    (Commit.write_fence_commit (Commit.write_fence_commit commit0 sc0 ord1) (Commit.write_fence_sc commit0 sc0 ord1) ord2)
    (Commit.write_fence_commit commit0 sc0 ord).
Proof.
  econs; aggrtac;
    (try by apply WF0);
    (repeat condtac; aggrtac);
    rewrite <- ? Capability.join_r; committac.
  - admit.
  - admit.
  - apply write_fence_write_fence_sc; auto.
  - admit.
  - apply write_fence_write_fence_sc; auto.
  - admit.
  - apply write_fence_write_fence_sc; auto.
  - admit.
  - apply write_fence_write_fence_sc; auto.
Admitted.
