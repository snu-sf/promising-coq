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
Require Import ReorderMemory.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma reorder_read_read
      loc1 ts1 val1 released1 ord1
      loc2 ts2 val2 released2 ord2
      promise0 mem0
      th1
      th2
      (LOC: loc1 <> loc2)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Local.wf promise0 mem0)
      (STEP1: Local.read_step promise0 mem0 loc1 ts1 val1 released1 ord1 th1)
      (STEP2: Local.read_step th1 mem0 loc2 ts2 val2 released2 ord2 th2):
  exists th1',
    <<STEP1: Local.read_step promise0 mem0 loc2 ts2 val2 released2 ord2 th1'>> /\
    <<STEP2: Local.read_step th1' mem0 loc1 ts1 val1 released1 ord1 th2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit CommitFacts.read_min_spec; try apply WF0; try apply GET0; eauto.
  { eapply Snapshot.readable_mon; try apply COMMIT0; eauto. apply COMMIT. }
  i. des.
  exploit CommitFacts.read_min_spec; try apply WF; try apply GET; eauto.
  { eapply Snapshot.le_on_readable; eauto. apply COMMIT. }
  { apply WF0. }
  i. des.
  eexists. splits.
  - econs; eauto.
  - destruct promise0. s. econs; try eapply CommitFacts.read_mon2; eauto.
    s. inv COMMIT. inv COMMIT0. inv MONOTONE. inv MONOTONE0.
    unfold CommitFacts.read_min.
    destruct (Ordering.le_dec Ordering.acqrel ord2).
    { rewrite ORD2 in l. inv l. }
    econs; committac.
    + CommitFacts.condtac; committac.
      * rewrite ACQUIRE; auto.
      * rewrite CURRENT1. auto.
      * rewrite READ1. apply CURRENT2.
      * rewrite CURRENT1. auto.
      * rewrite READ1. apply CURRENT2.
    + rewrite RELEASED. auto.
    + rewrite ACQUIRABLE. auto.
    + rewrite ACQUIRABLE1. auto.
Qed.

Lemma reorder_memory_get_promise
      promise0 mem0 loc from to msg promise1 mem1
      l t m
      (LE: Memory.le promise0 mem0)
      (GET1: Memory.get l t mem0 = Some m)
      (GET2: Memory.get l t promise0 = None)
      (PROMISE: Memory.promise promise0 mem0 loc from to msg promise1 mem1):
  Memory.get l t mem1 = Some m /\
  Memory.get l t promise1 = None.
Proof.
  exploit reorder_memory_get_promise_iff; eauto. intros [X1 X2].
  apply X1. auto.
Qed.

Lemma reorder_read_promise
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 val2 released2
      th0 mem0
      th1
      th2 mem2
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.read_step th0 mem0 loc1 ts1 val1 released1 ord1 th1)
      (STEP2: Local.promise_step th1 mem0 loc2 from2 to2 val2 released2 th2 mem2):
  exists th1',
    <<STEP1: Local.promise_step th0 mem0 loc2 from2 to2 val2 released2 th1' mem2>> /\
    <<STEP2: Local.read_step th1' mem2 loc1 ts1 val1 released1 ord1 th2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit reorder_memory_get_promise; try apply WF0; eauto. i. des.
  exploit Memory.promise_future; try apply WF0; eauto. i. des.
  exploit Commit.future_wf; try apply WF0; eauto. i.
  exploit Memory.future_get; eauto. i.
  exploit CommitFacts.read_min_spec; try apply COMMIT; eauto. i. des.
  eexists. splits.
  - econs; try reflexivity; try apply MEMORY; eauto.
  - destruct th0. ss. econs; try eapply CommitFacts.read_mon2; eauto.
    rewrite <- COMMIT0. apply CommitFacts.read_min_min. auto.
Qed.

Lemma reorder_read_fulfill
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 val2 released2 ord2
      th0 mem0
      th1
      th2
      (LOC: loc1 <> loc2)
      (ORD: Ordering.le Ordering.sc ord2 -> Ordering.le Ordering.sc ord1 -> False)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.read_step th0 mem0 loc1 ts1 val1 released1 ord1 th1)
      (STEP2: Local.fulfill_step th1 mem0 loc2 from2 to2 val2 released2 ord2 th2):
  exists th1',
    <<STEP1: Local.fulfill_step th0 mem0 loc2 from2 to2 val2 released2 ord2 th1'>> /\
    <<STEP2: Local.read_step th1' mem0 loc1 ts1 val1 released1 ord1 th2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit Memory.fulfill_get; eauto. i.
  exploit Memory.le_get; try apply WF0; eauto. i.
  exploit CommitFacts.write_min_spec; try apply x1; try apply WF0; eauto.
  { eapply Snapshot.writable_mon; try apply COMMIT0; eauto. apply COMMIT. }
  { etransitivity; [apply COMMIT|]. apply COMMIT0. }
  { instantiate (1 := ord2). i. inv COMMIT0.
    rewrite <- RELEASED0; auto. apply Snapshot.incr_writes_mon. apply COMMIT.
  }
  { inv WF0. inv MEMORY0. exploit WF; eauto. }
  i. des.
  exploit CommitFacts.read_min_spec; try apply GET; eauto.
  { eapply Snapshot.le_on_readable; eauto. apply COMMIT. }
  { apply WF0. }
  i. des.
  eexists. splits.
  - econs; eauto.
  - destruct th0. ss. econs; try eapply CommitFacts.read_mon2; eauto.
    + inv COMMIT. inv COMMIT0. inv MONOTONE. inv MONOTONE0.
      unfold CommitFacts.read_min, CommitFacts.write_min. ss.
      econs; committac; try CommitFacts.condtac; committac.
      * rewrite ACQUIRE; auto.
      * rewrite CURRENT1. auto.
      * rewrite READ0. apply CURRENT2.
      * rewrite CURRENT1. auto.
      * rewrite READ0. apply CURRENT2.
      * unfold LocFun.add, LocFun.find.
        CommitFacts.condtac; committac.
        etransitivity; [apply RELEASED|apply RELEASED4].
      * rewrite ACQUIRABLE. auto.
      * rewrite ACQUIRABLE0. auto.
    + erewrite <- reorder_memory_get_fulfill; eauto. apply WF0.
Qed.

Lemma reorder_read_write
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 val2 released2 ord2
      th0 mem0
      th1 mem1
      th2
      (LOC: loc1 <> loc2)
      (ORD: Ordering.le Ordering.sc ord2 -> Ordering.le Ordering.sc ord1 -> False)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.read_step th0 mem0 loc1 ts1 val1 released1 ord1 th1)
      (STEP2: Local.write_step th1 mem0 loc2 from2 to2 val2 released2 ord2 th2 mem1):
  exists th1',
    <<STEP1: Local.write_step th0 mem0 loc2 from2 to2 val2 released2 ord2 th1' mem1>> /\
    <<STEP2: Local.read_step th1' mem1 loc1 ts1 val1 released1 ord1 th2>>.
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
      th0 mem0
      th1
      th2
      (ORDR2: Ordering.le ordr2 Ordering.relaxed)
      (ORDW2: Ordering.le ordw2 Ordering.acqrel)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.read_step th0 mem0 loc1 ts1 val1 released1 ord1 th1)
      (STEP2: Local.fence_step th1 mem0 ordr2 ordw2 th2):
  exists th1',
    <<STEP1: Local.fence_step th0 mem0 ordr2 ordw2 th1'>> /\
    <<STEP2: Local.read_step th1' mem0 loc1 ts1 val1 released1 ord1 th2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  destruct (Ordering.le_dec Ordering.acqrel ordr2) eqn:ORDR2'; committac.
  { clear ORDR2'. rewrite ORDR2 in l. inv l. }
  exploit CommitFacts.fence_min_spec; try apply WF0; eauto. i. des.
  exploit CommitFacts.read_min_spec; try apply WF; try apply GET; eauto.
  { instantiate (1 := ordw2). instantiate (1 := ordr2).
    unfold CommitFacts.fence_min.
    rewrite ORDR2'. committac.
    apply COMMIT.
  }
  { apply WF0. }
  i. des.
  eexists. splits.
  - econs; eauto.
  - destruct th0. s. econs; try eapply CommitFacts.read_mon2; eauto.
    inv COMMIT. inv COMMIT0. inv MONOTONE. inv MONOTONE0.
    unfold CommitFacts.read_min, CommitFacts.fence_min.
    rewrite ORDR2'. committac.
    econs; committac; try CommitFacts.condtac; committac.
    + rewrite ACQUIRE; auto.
    + rewrite CURRENT0. auto.
    + rewrite READ0. apply CURRENT1.
    + rewrite CURRENT0. auto.
    + rewrite READ0. apply CURRENT1.
    + unfold LocFun.find. committac.
      * rewrite CURRENT0. eauto.
      * etransitivity; [apply RELEASED|apply RELEASED0].
    + unfold LocFun.find. committac.
      etransitivity; [apply RELEASED|apply RELEASED0].
    + rewrite ACQUIRABLE. auto.
    + rewrite ACQUIRABLE0. auto.
Qed.

Lemma reorder_fulfill_read
      loc1 from1 to1 val1 released1 ord1
      loc2 ts2 val2 released2 ord2
      th0 mem0
      th1
      th2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fulfill_step th0 mem0 loc1 from1 to1 val1 released1 ord1 th1)
      (STEP2: Local.read_step th1 mem0 loc2 ts2 val2 released2 ord2 th2):
  exists th1',
    <<STEP1: Local.read_step th0 mem0 loc2 ts2 val2 released2 ord2 th1'>> /\
    <<STEP2: Local.fulfill_step th1' mem0 loc1 from1 to1 val1 released1 ord1 th2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit Memory.fulfill_get; eauto. i.
  exploit Memory.le_get; try apply WF0; eauto. i.
  exploit CommitFacts.read_min_spec; try apply WF0; try apply GET; eauto.
  { eapply Snapshot.readable_mon; try apply COMMIT0; eauto. apply COMMIT. }
  i. des.
  exploit CommitFacts.write_min_spec; try apply x1; eauto.
  { eapply Snapshot.le_on_writable; eauto. apply COMMIT. }
  { s. apply COMMIT. }
  { instantiate (1 := ord1). i. rewrite ORD1 in H. inv H. }
  { apply WF0. }
  { inv WF0. inv MEMORY0. exploit WF0; eauto. }
  i. des.
  eexists. splits.
  - econs; eauto. erewrite reorder_memory_get_fulfill; eauto. apply WF0.
  - destruct th0. s. econs; try eapply CommitFacts.write_mon2; eauto.
    inv COMMIT. inv COMMIT0. inv MONOTONE. inv MONOTONE0.
    unfold CommitFacts.write_min, CommitFacts.read_min.
    CommitFacts.condtac; committac.
    { rewrite ORD2 in l. inv l. }
    econs; committac.
    + rewrite CURRENT1. auto.
    + rewrite WRITE0. apply CURRENT2.
    + unfold LocFun.add, LocFun.find.
      CommitFacts.condtac; committac.
      * rewrite RELEASED3. apply RELEASED4.
      * etransitivity; [apply RELEASED|apply RELEASED4].
    + rewrite ACQUIRABLE0. auto.
Qed.

Lemma reorder_fulfill_promise
      loc1 from1 to1 val1 released1 ord1
      loc2 from2 to2 val2 released2
      th0 mem0
      th1
      th2 mem2
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fulfill_step th0 mem0 loc1 from1 to1 val1 released1 ord1 th1)
      (STEP2: Local.promise_step th1 mem0 loc2 from2 to2 val2 released2 th2 mem2):
  exists th1',
    <<STEP1: Local.promise_step th0 mem0 loc2 from2 to2 val2 released2 th1' mem2>> /\
    <<STEP2: Local.fulfill_step th1' mem2 loc1 from1 to1 val1 released1 ord1 th2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit reorder_memory_fulfill_promise; try apply MEMORY; try apply WF0; eauto. i. des.
  exploit Memory.promise_future; try apply x0; try apply WF0; eauto. i. des.
  exploit Commit.future_wf; try apply WF0; eauto. i.
  exploit Memory.fulfill_get; try apply x0; eauto. i.
  exploit Memory.le_get; try apply LE2; eauto. i.
  exploit CommitFacts.write_min_spec; try apply COMMIT; eauto.
  { inv WF2. exploit WF; eauto. }
  i. des.
  eexists. splits.
  - econs; try reflexivity; try apply x0; eauto.
  - destruct th0. ss. econs; try eapply CommitFacts.write_mon2; eauto.
    rewrite <- COMMIT0. eapply CommitFacts.write_min_min. eauto.
Qed.

Lemma reorder_fulfill_fulfill
      loc1 from1 to1 val1 released1 ord1
      loc2 from2 to2 val2 released2 ord2
      th0 mem0
      th1
      th2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fulfill_step th0 mem0 loc1 from1 to1 val1 released1 ord1 th1)
      (STEP2: Local.fulfill_step th1 mem0 loc2 from2 to2 val2 released2 ord2 th2):
  exists th1',
    <<STEP1: Local.fulfill_step th0 mem0 loc2 from2 to2 val2 released2 ord2 th1'>> /\
    <<STEP2: Local.fulfill_step th1' mem0 loc1 from1 to1 val1 released1 ord1 th2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit reorder_memory_fulfill_fulfill; try apply MEMORY; eauto. i. des.
  exploit Memory.fulfill_get; try apply x0; eauto. i.
  exploit Memory.le_get; try apply WF0; eauto. i.
  exploit CommitFacts.write_min_spec; try apply x3; try apply WF0; eauto.
  { eapply Snapshot.writable_mon; try apply COMMIT0; eauto. apply COMMIT. }
  { etransitivity; [apply COMMIT|]. apply COMMIT0. }
  { instantiate (1 := ord2). committac.
    - inv COMMIT0. rewrite <- RELEASED0; auto.
      etransitivity; [apply COMMIT|]. committac.
    - inv COMMIT0. etransitivity; [|apply RELEASED0; auto].
      s. apply Times.incr_ts.
  }
  { inv WF0. inv MEMORY1. exploit WF; eauto. }
  i. des.
  exploit Memory.fulfill_get; try apply x1; eauto. i.
  exploit Memory.le_get; try apply x4; eauto.
  { eapply Memory.fulfill_future; eauto. apply WF0. }
  i.
  exploit CommitFacts.write_min_spec; try apply x5; eauto.
  { eapply Snapshot.le_on_writable; eauto. apply COMMIT. }
  { committac. unfold LocFun.add, LocFun.find.
    CommitFacts.condtac; [congruence|]. apply COMMIT.
  }
  { instantiate (1 := ord1). i. rewrite ORD1 in H. inv H. }
  { apply WF0. }
  { inv WF0. inv MEMORY1. exploit WF0; eauto. }
  i. des.
  eexists. splits.
  - econs; eauto.
  - destruct th0. ss. econs; try eapply CommitFacts.write_mon2; eauto.
    inv COMMIT. inv COMMIT0. inv MONOTONE. inv MONOTONE0. ss.
    econs; committac.
    + rewrite CURRENT1. auto.
    + rewrite WRITE1. apply CURRENT2.
    + unfold LocFun.add, LocFun.find.
      repeat CommitFacts.condtac; committac.
      { rewrite RELEASED4. eauto. }
      { etransitivity; [apply RELEASED|apply RELEASED8]. }
    + rewrite ACQUIRABLE. auto.
Qed.

Lemma reorder_fulfill_write
      loc1 from1 to1 val1 released1 ord1
      loc2 from2 to2 val2 released2 ord2
      th0 mem0
      th1
      th2 mem2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fulfill_step th0 mem0 loc1 from1 to1 val1 released1 ord1 th1)
      (STEP2: Local.write_step th1 mem0 loc2 from2 to2 val2 released2 ord2 th2 mem2):
  exists th1',
    <<STEP1: Local.write_step th0 mem0 loc2 from2 to2 val2 released2 ord2 th1' mem2>> /\
    <<STEP2: Local.fulfill_step th1' mem2 loc1 from1 to1 val1 released1 ord1 th2>>.
Proof.
  inv STEP2.
  - exploit reorder_fulfill_fulfill; eauto. i. des.
    eexists. splits; eauto. econs 1. eauto.
    inv STEP1. erewrite reorder_memory_cell_fulfill; eauto.
  - exploit reorder_fulfill_promise; eauto. i. des.
    exploit reorder_fulfill_fulfill; try apply STEP2; eauto.
    { eapply Local.promise_step_future; eauto. }
    i. des.
    eexists. splits; eauto. econs 2; eauto.
    inv STEP1. erewrite reorder_memory_cell_fulfill; eauto.
Qed.

Lemma reorder_fence_promise
      ordr1 ordw1
      loc2 from2 to2 val2 released2
      th0 mem0
      th1
      th2 mem2
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fence_step th0 mem0 ordr1 ordw1 th1)
      (STEP2: Local.promise_step th1 mem0 loc2 from2 to2 val2 released2 th2 mem2):
  exists th1',
    <<STEP1: Local.promise_step th0 mem0 loc2 from2 to2 val2 released2 th1' mem2>> /\
    <<STEP2: Local.fence_step th1' mem2 ordr1 ordw1 th2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit Memory.promise_future; try apply WF0; eauto. i. des.
  exploit Commit.future_wf; try apply WF0; eauto. i.
  exploit CommitFacts.fence_min_spec; try apply COMMIT; eauto. i. des.
  eexists. splits.
  - econs; try reflexivity; try apply MEMORY; eauto.
  - destruct th0. ss. econs; try eapply CommitFacts.fence_mon2; eauto.
    + rewrite <- COMMIT0. apply CommitFacts.fence_min_min. auto.
    + i. rewrite ORDW1 in H. inv H.
Qed.

Lemma reorder_fence_fulfill
      ordr1 ordw1
      loc2 from2 to2 val2 released2 ord2
      th0 mem0
      th1
      th2
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fence_step th0 mem0 ordr1 ordw1 th1)
      (STEP2: Local.fulfill_step th1 mem0 loc2 from2 to2 val2 released2 ord2 th2):
  exists th1',
    <<STEP1: Local.fulfill_step th0 mem0 loc2 from2 to2 val2 released2 ord2 th1'>> /\
    <<STEP2: Local.fence_step th1' mem0 ordr1 ordw1 th2>>.
Proof.
  destruct (Ordering.le_dec Ordering.acqrel ordw1) eqn:ORDW1'.
  { clear ORDW1'. rewrite ORDW1 in l. inv l. }
  inv STEP1. inv STEP2. ss.
  exploit Memory.fulfill_get; eauto. i.
  exploit Memory.le_get; try apply WF0; eauto. i.
  exploit CommitFacts.write_min_spec; try apply x1; try apply WF0; eauto.
  { eapply Snapshot.writable_mon; try apply COMMIT0; eauto. apply COMMIT. }
  { etransitivity; [apply COMMIT|]. apply COMMIT0. }
  { instantiate (1 := ord2). i. inv COMMIT0.
    rewrite <- RELEASED0; auto. apply Snapshot.incr_writes_mon. apply COMMIT.
  }
  { inv WF0. inv MEMORY0. exploit WF; eauto. }
  i. des.
  exploit CommitFacts.fence_min_spec; eauto.
  { apply WF0. }
  i. des.
  eexists. splits.
  - econs; eauto.
  - destruct th0. ss. econs; try eapply CommitFacts.fence_mon2; eauto.
    + inv COMMIT. inv COMMIT0. inv MONOTONE. inv MONOTONE0.
      unfold CommitFacts.fence_min, CommitFacts.write_min.
      committac. econs; committac.
      * CommitFacts.condtac; committac.
        { rewrite ACQUIRE; auto. }
        { rewrite CURRENT0. auto. }
        { rewrite CURRENT0. auto. }
      * unfold LocFun.add, LocFun.find.
        CommitFacts.condtac; committac.
        CommitFacts.condtac; committac.
        etransitivity; [apply RELEASED|apply RELEASED4].
      * rewrite ACQUIRABLE. auto.
    + i. rewrite ORDW1 in H. inv H.
Qed.

Lemma reorder_fence_write
      ordr1 ordw1
      loc2 from2 to2 val2 released2 ord2
      th0 mem0
      th1
      th2 mem2
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fence_step th0 mem0 ordr1 ordw1 th1)
      (STEP2: Local.write_step th1 mem0 loc2 from2 to2 val2 released2 ord2 th2 mem2):
  exists th1',
    <<STEP1: Local.write_step th0 mem0 loc2 from2 to2 val2 released2 ord2 th1' mem2>> /\
    <<STEP2: Local.fence_step th1' mem2 ordr1 ordw1 th2>>.
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
