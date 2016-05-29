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

Require ReorderMemory.
Require ReorderCommit.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma progress_step
      rs1 i1 s1 lc1 mem1
      (WF1: Local.wf lc1 mem1)
      (PROMISES1: lc1.(Local.promises) = Memory.bot):
  (exists lc2, <<STEP: Thread.internal_step (Thread.mk lang (State.mk rs1 (i1::s1)) lc1 mem1) lc2>>) \/
  (exists e lc2, <<STEP: Thread.external_step e (Thread.mk lang (State.mk rs1 (i1::s1)) lc1 mem1) lc2>>).
Proof.
  destruct i1.
  - destruct i.
    + hexploit progress_silent_step; eauto. i.
      left. eexists. econs 1; s; eauto.
      econs. econs.
    + hexploit progress_silent_step; eauto. i.
      left. eexists. econs 1; s; eauto.
      econs. econs.
    + hexploit exists_max_timestamp; try apply WF1; eauto. i. des.
      hexploit progress_read_step; eauto. i. des.
      left. eexists. econs 2; s; eauto.
      econs. econs.
    + hexploit exists_max_timestamp; try apply WF1; eauto. i. des.
      hexploit progress_write_step; try apply Time.incr_spec; eauto. i. des.
      left. eexists. econs 3; s; eauto.
      econs. econs.
    + hexploit exists_max_timestamp; try apply WF1; eauto. i. des.
      hexploit progress_read_step; eauto. i. des.
      exploit Local.read_step_future; eauto. i.
      hexploit progress_write_step; try apply Time.incr_spec; eauto.
      { inv H0. auto. }
      i. des.
      left. eexists. econs 4; s; eauto.
      * econs. econs. apply surjective_pairing.
    + hexploit progress_fence_step; eauto. i. des.
      left. eexists. econs 5; s; eauto.
      econs. econs.
    + hexploit progress_silent_step; eauto. i.
      right. eexists _, _. econs; s; eauto.
      econs. econs.
  - left. eexists. econs 1; ss.
    + econs.
    + apply progress_silent_step. auto.
  - left. eexists. econs 1; ss.
    + econs.
    + apply progress_silent_step. auto.
Grab Existential Variables.
  { auto. }
  { apply Capability.elt. }
  { apply Capability.elt. }
Qed.


Lemma reorder_read_read
      loc1 ts1 val1 released1 ord1
      loc2 ts2 val2 released2 ord2
      lc0 mem0
      lc1
      lc2
      (LOC: loc1 <> loc2)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.read_step lc1 mem0 loc2 ts2 val2 released2 ord2 lc2):
  exists lc1',
    <<STEP1: Local.read_step lc0 mem0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.read_step lc1' mem0 loc1 ts1 val1 released1 ord1 lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit ReorderCommit.read_read; try apply COMMIT; try apply COMMIT0; eauto.
  { apply WF0. }
  i. des.
  eexists. splits.
  - econs; eauto.
    + apply COMMIT1'.
    + admit.
  - refine (Local.step_read _ _ _ _ _); eauto.
Admitted.

Lemma reorder_read_promise
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 val2 released2
      lc0 mem0
      lc1
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.promise_step lc1 mem0 loc2 from2 to2 val2 released2 lc2 mem2):
  exists lc1',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 val2 released2 lc1' mem2>> /\
    <<STEP2: Local.read_step lc1' mem2 loc1 ts1 val1 released1 ord1 lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit Memory.promise_get1; try apply PROMISE; eauto. i. des.
  exploit Memory.promise_future; try apply WF0; eauto. i. des.
  exploit Commit.future_closed; try apply WF0; eauto. i.
  eexists. splits.
  - econs; try apply WF0; eauto. refl.
  - econs; eauto. s. eapply CommitFacts.read_mon2; eauto.
    refl.
Qed.

Lemma reorder_read_fulfill
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 val2 releasedc2 releasedm2 ord2
      lc0 mem0
      lc1
      lc2
      (LOC: loc1 <> loc2)
      (ORD: Ordering.le Ordering.seqcst ord2 -> Ordering.le Ordering.seqcst ord1 -> False)
      (WF0: Local.wf lc0 mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.fulfill_step lc1 mem0 loc2 from2 to2 val2 releasedc2 releasedm2 ord2 lc2):
  exists lc1',
    <<STEP1: Local.fulfill_step lc0 mem0 loc2 from2 to2 val2 releasedc2 releasedm2 ord2 lc1'>> /\
    <<STEP2: Local.read_step lc1' mem0 loc1 ts1 val1 released1 ord1 lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit ReorderCommit.read_write; try apply COMMIT; try apply COMMIT0; eauto.
  { apply WF0. }
  i. des.
  eexists. splits.
  - econs; eauto.
    + apply COMMIT1'.
    + admit.
  - econs; eauto.
Admitted.

Lemma reorder_read_write
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 val2 releasedc2 releasedm2 ord2
      lc0 mem0
      lc1 mem1
      lc2
      (LOC: loc1 <> loc2)
      (ORD: Ordering.le Ordering.seqcst ord2 -> Ordering.le Ordering.seqcst ord1 -> False)
      (WF0: Local.wf lc0 mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.write_step lc1 mem0 loc2 from2 to2 val2 releasedc2 releasedm2 ord2 lc2 mem1):
  exists lc1',
    <<STEP1: Local.write_step lc0 mem0 loc2 from2 to2 val2 releasedc2 releasedm2 ord2 lc1' mem1>> /\
    <<STEP2: Local.read_step lc1' mem1 loc1 ts1 val1 released1 ord1 lc2>>.
Proof.
  inv STEP2.
  - exploit reorder_read_fulfill; eauto. i. des.
    eexists. splits; eauto. econs 1. eauto.
    inv STEP1. ss.
  - exploit reorder_read_promise; eauto. i. des.
    exploit reorder_read_fulfill; try apply FULFILL; eauto.
    { eapply Local.promise_step_future; eauto. }
    i. des.
    eexists. splits; eauto. econs 2; eauto.
    inv STEP1. ss.
Qed.

Lemma reorder_read_fence
      loc1 ts1 val1 released1 ord1
      ordr2 ordw2
      lc0 mem0
      lc1
      lc2
      (ORD1: Ordering.le Ordering.relaxed ord1)
      (ORDR2: Ordering.le ordr2 Ordering.relaxed)
      (ORDW2: Ordering.le ordw2 Ordering.acqrel)
      (RLX: Ordering.le Ordering.relaxed ordw2 -> Ordering.le ord1 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.fence_step lc1 mem0 ordr2 ordw2 lc2):
  exists lc1',
    <<STEP1: Local.fence_step lc0 mem0 ordr2 ordw2 lc1'>> /\
    <<STEP2: Local.read_step lc1' mem0 loc1 ts1 val1 released1 ord1 lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit ReorderCommit.read_read_fence; try apply COMMIT; try apply READ; eauto.
  { apply WF0. }
  i. des.
  exploit ReorderCommit.read_write_fence; try apply COMMIT2'; try apply WRITE; eauto.
  { apply COMMIT1'. }
  i. des.
  eexists. splits.
  - econs; eauto.
    + apply COMMIT1'0.
    + admit.
  - refine (Local.step_read _ _ _ _ _); eauto.
Admitted.

Lemma reorder_fulfill_read
      loc1 from1 to1 val1 releasedc1 releasedm1 ord1
      loc2 ts2 val2 released2 ord2
      lc0 mem0
      lc1
      lc2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (STEP1: Local.fulfill_step lc0 mem0 loc1 from1 to1 val1 releasedc1 releasedm1 ord1 lc1)
      (STEP2: Local.read_step lc1 mem0 loc2 ts2 val2 released2 ord2 lc2):
  exists lc1',
    <<STEP1: Local.read_step lc0 mem0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.fulfill_step lc1' mem0 loc1 from1 to1 val1 releasedc1 releasedm1 ord1 lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit ReorderCommit.write_read; try apply COMMIT; try apply COMMIT0; eauto.
  { apply WF0. }
  i. des.
  eexists. splits.
  - econs; eauto.
    + apply COMMIT1'.
    + admit.
  - econs; eauto.
Admitted.

Lemma reorder_fulfill_promise
      loc1 from1 to1 val1 releasedc1 releasedm1 ord1
      loc2 from2 to2 val2 released2
      lc0 mem0
      lc1
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (STEP1: Local.fulfill_step lc0 mem0 loc1 from1 to1 val1 releasedc1 releasedm1 ord1 lc1)
      (STEP2: Local.promise_step lc1 mem0 loc2 from2 to2 val2 released2 lc2 mem2):
  exists lc1',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 val2 released2 lc1' mem2>> /\
    <<STEP2: Local.fulfill_step lc1' mem2 loc1 from1 to1 val1 releasedc1 releasedm1 ord1 lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit ReorderMemory.fulfill_promise; try apply MEMORY; try apply WF0; eauto. i. des.
  exploit Memory.promise_future; try apply x0; try apply WF0; eauto. i. des.
  exploit Commit.future_closed; try apply WF0; eauto. i.
  eexists. splits.
  - econs; try apply WF0; eauto. refl.
  - econs; eauto. s. eapply CommitFacts.write_mon2; eauto.
    refl.
Qed.

Lemma reorder_fulfill_fulfill
      loc1 from1 to1 val1 releasedc1 releasedm1 ord1
      loc2 from2 to2 val2 releasedc2 releasedm2 ord2
      lc0 mem0
      lc1
      lc2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (STEP1: Local.fulfill_step lc0 mem0 loc1 from1 to1 val1 releasedc1 releasedm1 ord1 lc1)
      (STEP2: Local.fulfill_step lc1 mem0 loc2 from2 to2 val2 releasedc2 releasedm2 ord2 lc2):
  exists lc1',
    <<STEP1: Local.fulfill_step lc0 mem0 loc2 from2 to2 val2 releasedc2 releasedm2 ord2 lc1'>> /\
    <<STEP2: Local.fulfill_step lc1' mem0 loc1 from1 to1 val1 releasedc1 releasedm1 ord1 lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit ReorderMemory.fulfill_fulfill; try apply FULFILL; try apply FULFILL0. i. des.
  exploit ReorderCommit.write_write; try apply COMMIT; try apply COMMIT0; eauto.
  { apply WF0. }
  i. des.
  eexists. splits.
  - econs; eauto.
    + apply COMMIT1'.
    + admit.
  - econs; eauto.
Admitted.

Lemma reorder_fulfill_write
      loc1 from1 to1 val1 releasedc1 releasedm1 ord1
      loc2 from2 to2 val2 releasedc2 releasedm2 ord2
      lc0 mem0
      lc1
      lc2 mem2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (STEP1: Local.fulfill_step lc0 mem0 loc1 from1 to1 val1 releasedc1 releasedm1 ord1 lc1)
      (STEP2: Local.write_step lc1 mem0 loc2 from2 to2 val2 releasedc2 releasedm2 ord2 lc2 mem2):
  exists lc1',
    <<STEP1: Local.write_step lc0 mem0 loc2 from2 to2 val2 releasedc2 releasedm2 ord2 lc1' mem2>> /\
    <<STEP2: Local.fulfill_step lc1' mem2 loc1 from1 to1 val1 releasedc1 releasedm1 ord1 lc2>>.
Proof.
  inv STEP2.
  - exploit reorder_fulfill_fulfill; eauto. i. des.
    eexists. splits; eauto. econs 1. eauto.
    inv STEP1. erewrite ReorderMemory.cell_fulfill; eauto.
  - exploit reorder_fulfill_promise; eauto. i. des.
    exploit reorder_fulfill_fulfill; try apply STEP2; eauto.
    { eapply Local.promise_step_future; eauto. }
    i. des.
    eexists. splits; eauto. econs 2; eauto.
    inv STEP1. erewrite ReorderMemory.cell_fulfill; eauto.
Qed.

Lemma reorder_fence_promise
      ordr1 ordw1
      loc2 from2 to2 val2 released2
      lc0 mem0
      lc1
      lc2 mem2
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (STEP1: Local.fence_step lc0 mem0 ordr1 ordw1 lc1)
      (STEP2: Local.promise_step lc1 mem0 loc2 from2 to2 val2 released2 lc2 mem2):
  exists lc1',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 val2 released2 lc1' mem2>> /\
    <<STEP2: Local.fence_step lc1' mem2 ordr1 ordw1 lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit Memory.promise_future; try apply WF0; eauto. i. des.
  exploit Commit.future_closed; try apply WF0; eauto. i.
  eexists. splits.
  - econs; try apply WF0; eauto. refl.
  - econs; eauto.
    + eapply CommitFacts.write_fence_mon2; eauto.
      refl.
    + i. destruct ordw1; inv ORDW1; inv H.
Qed.

Lemma reorder_fence_fulfill
      ordr1 ordw1
      loc2 from2 to2 val2 releasedc2 releasedm2 ord2
      lc0 mem0
      lc1
      lc2
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (STEP1: Local.fence_step lc0 mem0 ordr1 ordw1 lc1)
      (STEP2: Local.fulfill_step lc1 mem0 loc2 from2 to2 val2 releasedc2 releasedm2 ord2 lc2):
  exists lc1',
    <<STEP1: Local.fulfill_step lc0 mem0 loc2 from2 to2 val2 releasedc2 releasedm2 ord2 lc1'>> /\
    <<STEP2: Local.fence_step lc1' mem0 ordr1 ordw1 lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit ReorderCommit.write_fence_write; try apply WRITE; try apply COMMIT; eauto.
  { apply READ. }
  i. des.
  exploit ReorderCommit.read_fence_write; try apply READ; try apply COMMIT1'; eauto.
  { apply WF0. }
  i. des.
  eexists. splits.
  - econs; eauto.
    + apply COMMIT1'0.
    + admit.
  - econs; eauto. i. destruct ordw1; inv ORDW1; inv H.
Admitted.

Lemma reorder_fence_write
      ordr1 ordw1
      loc2 from2 to2 val2 releasedc2 releasedm2 ord2
      lc0 mem0
      lc1
      lc2 mem2
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (STEP1: Local.fence_step lc0 mem0 ordr1 ordw1 lc1)
      (STEP2: Local.write_step lc1 mem0 loc2 from2 to2 val2 releasedc2 releasedm2 ord2 lc2 mem2):
  exists lc1',
    <<STEP1: Local.write_step lc0 mem0 loc2 from2 to2 val2 releasedc2 releasedm2 ord2 lc1' mem2>> /\
    <<STEP2: Local.fence_step lc1' mem2 ordr1 ordw1 lc2>>.
Proof.
  inv STEP2.
  - exploit reorder_fence_fulfill; eauto. i. des.
    eexists. splits; eauto. econs 1. eauto.
    inv STEP1. auto.
  - exploit reorder_fence_promise; eauto. i. des.
    exploit reorder_fence_fulfill; try apply STEP2; eauto.
    { eapply Local.promise_step_future; eauto. }
    i. des.
    eexists. splits; eauto. econs 2; eauto.
    inv STEP1. auto.
Qed.
