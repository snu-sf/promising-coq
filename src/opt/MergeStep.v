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

Require MergeCommit.
Require ReorderCommit.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma merge_read_read
      loc ts val released ord1 ord2 ord
      lc0 lc2 mem0
      (ORD1: Ordering.le ord1 ord)
      (ORD2: Ordering.le ord2 ord)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP: Local.read_step lc0 mem0 loc ts val released ord lc2):
  exists lc1,
    <<STEP1: Local.read_step lc0 mem0 loc ts val released ord1 lc1>> /\
    <<STEP2: Local.read_step lc1 mem0 loc ts val released ord2 lc2>>.
Proof.
  inv STEP.
  exploit MergeCommit.read_read.
  { apply ORD1. }
  { apply ORD2. }
  { apply COMMIT. }
  { apply WF0. }
  { inv MEM0. exploit CLOSED; eauto. i. des. auto. }
  i. des.
  eexists. splits.
  - econs; eauto. eapply CommitFacts.read_min_closed; eauto; apply WF0.
  - refine (Local.step_read _ _ _ _); eauto.
Qed.

Lemma merge_fulfill_read1
      loc from to val released ord1 ord2
      lc0 lc2 mem0
      (ORD2: Ordering.le ord2 Ordering.acqrel)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP: Local.fulfill_step lc0 mem0 loc from to val released released ord1 lc2):
  exists lc1,
    <<STEP1: Local.fulfill_step lc0 mem0 loc from to val released released ord1 lc1>> /\
    <<STEP2: Local.read_step lc1 mem0 loc to val released ord2 lc2>>.
Proof.
  inv STEP.
  exploit MergeCommit.write_read.
  { apply ORD2. }
  { apply COMMIT. }
  { apply WF0. }
  { inv MEM0. exploit CLOSED; eauto.
    - apply WF0. eapply Memory.remove_disjoint. apply FULFILL.
    - s. i. des. auto.
  }
  i. des.
  exploit Memory.remove_disjoint; try apply FULFILL; eauto. i.
  inversion WF0. exploit PROMISES; eauto. i.
  eexists. splits.
  - econs; eauto. eapply CommitFacts.write_min_closed; eauto; apply WF0.
  - refine (Local.step_read _ _ _ _); eauto.
Qed.

Lemma merge_fulfill_read2
      loc from to val releasedr releasedw ord1 ord2
      lc0 lc2 mem0
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (WF_RELEASED: Capability.wf releasedr)
      (RELEASED: Ordering.le Ordering.relaxed ord2 -> Capability.le releasedr lc0.(Local.commit).(Commit.acq))
      (STEP: Local.fulfill_step lc0 mem0 loc from to val releasedw (Capability.join releasedr releasedw) ord1 lc2):
  exists lc1,
    <<STEP1: Local.fulfill_step lc0 mem0 loc from to val releasedw (Capability.join releasedr releasedw) ord1 lc1>> /\
    <<STEP2: Local.read_step lc1 mem0 loc to val (Capability.join releasedr releasedw) ord2 lc2>>.
Proof.
  inv STEP.
  exploit MergeCommit.write_read.
  { etrans. apply ORD2. auto. }
  { apply COMMIT. }
  { apply WF0. }
  { inv MEM0. exploit CLOSED; eauto.
    - apply WF0. eapply Memory.remove_disjoint. apply FULFILL.
    - s. i. des. etrans; eauto. apply TimeMap.join_r.
  }
  i. des.
  exploit Memory.remove_disjoint; try apply FULFILL; eauto. i.
  inversion WF0. exploit PROMISES; eauto. i.
  eexists. splits.
  - econs; eauto. eapply CommitFacts.write_min_closed; eauto; apply WF0.
  - refine (Local.step_read _ _ _ _); eauto. s.
    inv COMMIT2'. econs; auto.
    + i. committac.
      * etrans; eauto. etrans; [apply COMMIT1'|]. apply MON.
      * apply ACQ. auto.
    + by destruct ord2.
    + apply Capability.join_wf; auto.
Qed.

Lemma merge_write_read1
      loc from to val released ord1 ord2
      lc0 lc2 mem0 mem2 kind
      (ORD2: Ordering.le ord2 Ordering.acqrel)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP: Local.write_step lc0 mem0 loc from to val released released ord1 lc2 mem2 kind):
  exists lc1,
    <<STEP1: Local.write_step lc0 mem0 loc from to val released released ord1 lc1 mem2 kind>> /\
    <<STEP2: Local.read_step lc1 mem2 loc to val released ord2 lc2>>.
Proof.
  inv STEP.
  - exploit merge_fulfill_read1; eauto. i. des.
    eexists. splits; eauto. econs 1; eauto.
  - exploit Local.promise_step_future; eauto. i. des.
    exploit merge_fulfill_read1; eauto. i. des.
    eexists. splits; eauto. econs 2; eauto.
Qed.

Lemma merge_write_read2
      loc from to val releasedr releasedw ord1 ord2
      lc0 lc2 mem0 mem2 kind
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (WF_RELEASED: Capability.wf releasedr)
      (RELEASED: Ordering.le Ordering.relaxed ord2 -> Capability.le releasedr lc0.(Local.commit).(Commit.acq))
      (STEP: Local.write_step lc0 mem0 loc from to val releasedw (Capability.join releasedr releasedw) ord1 lc2 mem2 kind):
  exists lc1,
    <<STEP1: Local.write_step lc0 mem0 loc from to val releasedw (Capability.join releasedr releasedw) ord1 lc1 mem2 kind>> /\
    <<STEP2: Local.read_step lc1 mem2 loc to val (Capability.join releasedr releasedw) ord2 lc2>>.
Proof.
  inv STEP.
  - exploit merge_fulfill_read2; eauto. i. des.
    eexists. splits; eauto. econs 1; eauto.
  - exploit Local.promise_step_future; eauto. i. des.
    exploit merge_fulfill_read2; eauto.
    { etrans; eauto. inv PROMISE. ss. apply COMMIT. }
    i. des.
    eexists. splits; eauto. econs 2; eauto.
Qed.

Lemma merge_write_write
      loc ts1 ts2 ts3 val1 released1 val2 released2 ord1 ord2 ord
      lc0 lc2 mem0 mem2 kind
      (ORD1: Ordering.le ord1 ord)
      (ORD2: Ordering.le ord2 ord)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP: Local.write_step lc0 mem0 loc ts1 ts3 val2 released2 released2 ord lc2 mem2 kind):
  exists lc1 mem1 mem2',
    <<STEP1: Local.write_step lc0 mem0 loc ts1 ts2 val1 released1 released1 ord1 lc1 mem1 kind>> /\
    <<STEP2: Local.write_step lc1 mem1 loc ts2 ts3 val2 released2 released2 ord2 lc2 mem2' kind>> /\
    <<MEM: sim_memory mem2' mem2>>.
Proof.
Admitted.

Lemma merge_fence_fence
      ordr1 ordw1
      ordr2 ordw2
      ordr ordw
      lc0 lc2 mem0
      (ORDR1: Ordering.le ordr1 ordr)
      (ORDR2: Ordering.le ordr2 ordr)
      (ORDW1: Ordering.le ordw1 ordw)
      (ORDW2: Ordering.le ordw2 ordw)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP: Local.fence_step lc0 mem0 ordr ordw lc2):
  exists lc1,
    <<STEP1: Local.fence_step lc0 mem0 ordr1 ordw1 lc1>> /\
    <<STEP2: Local.fence_step lc1 mem0 ordr2 ordw2 lc2>>.
Proof.
  inv STEP.
  exploit MergeCommit.read_fence_read_fence.
  { apply ORDR1. }
  { apply ORDR2. }
  { eauto. }
  { apply WF0. }
  i. des.
  exploit MergeCommit.write_fence_write_fence.
  { apply ORDW1. }
  { apply ORDW2. }
  { eauto. }
  { apply READ. }
  i. des.
  exploit ReorderCommit.read_fence_write_fence.
  { apply COMMIT2'. }
  { apply COMMIT1'0. }
  { apply COMMIT1'. }
  i. des.
  eexists. splits.
  - econs; eauto.
    + i. apply RELEASE. etrans; eauto.
    + apply CommitFacts.write_fence_min_closed; auto.
      apply CommitFacts.read_fence_min_closed; auto.
      apply WF0.
  - refine (Local.step_fence _ _ _ _ _); eauto. s.
    i. apply RELEASE. etrans; eauto.
Qed.
