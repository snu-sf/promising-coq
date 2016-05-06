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

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma reorder_read_read
      loc1 ts1 val1 released1 ord1
      loc2 ts2 val2 released2 ord2
      th0 mem0
      th1
      th2
      (LOC: loc1 <> loc2)
      (ORD2: Ordering.le ord2 Ordering.release)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.read_step th0 mem0 loc1 ts1 val1 released1 ord1 th1)
      (STEP2: Local.read_step th1 mem0 loc2 ts2 val2 released2 ord2 th2):
  exists th1',
    <<STEP1: Local.read_step th0 mem0 loc2 ts2 val2 released2 ord2 th1'>> /\
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
  - destruct th0. s. econs; try eapply CommitFacts.read_mon2; eauto.
    s. inv COMMIT. inv COMMIT0. inv MONOTONE. inv MONOTONE0.
    unfold CommitFacts.read_min.
    destruct (Ordering.le Ordering.acquire ord2) eqn:ORD2'.
    { destruct ord2; ss. }
    econs.
    + destruct (Ordering.le Ordering.acquire ord1) eqn:ORD1; committac.
      * rewrite ACQUIRE; auto.
      * rewrite CURRENT1. auto.
      * rewrite READ1. apply CURRENT2.
      * rewrite CURRENT1. auto.
      * rewrite READ1. apply CURRENT2.
    + ss. i. rewrite RELEASED. auto.
    + ss. committac.
      * rewrite ACQUIRABLE. auto.
      * rewrite ACQUIRABLE1. auto.
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
  exploit Memory.promise_future; try apply WF0; eauto. i. des.
  exploit Commit.future_wf; try apply WF0; eauto. i.
  exploit Memory.future_get; eauto. i.
  exploit CommitFacts.read_min_spec; try apply COMMIT; eauto. i. des.
  eexists. splits.
  - econs; try reflexivity; try apply MEMORY; eauto.
  - destruct th0. ss. econs; try eapply CommitFacts.read_mon2; eauto.
    + rewrite <- COMMIT0. apply CommitFacts.read_min_min. auto.
    + match goal with
      | [|- ?x = None] => destruct x eqn:X; auto
      end.
      eapply Memory.promise_get_inv in X; try apply MEMORY; try apply WF0; eauto.
      des; [congruence|]. subst.
      exploit Memory.promise_get1; try apply MEMORY; try apply WF0; eauto. i.
      congruence.
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
    + inv COMMIT. inv COMMIT0. inv MONOTONE. inv MONOTONE0. ss.
      econs; committac.
      * i. rewrite ACQUIRE; auto.
      * rewrite CURRENT1. auto.
      * rewrite READ0. apply CURRENT2.
      * unfold LocFun.add, LocFun.find.
        destruct (Loc.eq_dec loc loc2); committac.
        etransitivity; [apply RELEASED|apply RELEASED4].
      * rewrite ACQUIRABLE. auto.
      * rewrite ACQUIRABLE0. auto.
    + admit. (* promise get None *)
Admitted.

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
      ord2
      th0 mem0
      th1
      th2
      (ORD2: Ordering.le ord2 Ordering.release)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.read_step th0 mem0 loc1 ts1 val1 released1 ord1 th1)
      (STEP2: Local.fence_step th1 mem0 ord2 th2):
  exists th1',
    <<STEP1: Local.fence_step th0 mem0 ord2 th1'>> /\
    <<STEP2: Local.read_step th1' mem0 loc1 ts1 val1 released1 ord1 th2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  destruct (Ordering.le Ordering.acquire ord2) eqn:ORD2'.
  { destruct ord2; ss. }
  exploit CommitFacts.fence_min_spec; try apply WF0; eauto. i. des.
  exploit CommitFacts.read_min_spec; try apply WF; try apply GET; eauto.
  { instantiate (1 := ord2).
    unfold CommitFacts.fence_min. rewrite ORD2'. ss. apply COMMIT.
  }
  { apply WF0. }
  i. des.
  eexists. splits.
  - econs; eauto.
  - destruct th0. s. econs; try eapply CommitFacts.read_mon2; eauto.
    inv COMMIT. inv COMMIT0. inv MONOTONE. inv MONOTONE0.
    unfold CommitFacts.read_min, CommitFacts.fence_min.
    rewrite ORD2'. econs.
    + destruct (Ordering.le Ordering.acquire ord1) eqn:ORD1; committac.
      * rewrite ACQUIRE; auto.
      * rewrite CURRENT0. auto.
      * rewrite READ0. apply CURRENT1.
      * rewrite CURRENT0. auto.
      * rewrite READ0. apply CURRENT1.
    + ss. i. unfold LocFun.find.
      CommitFacts.condtac; committac.
      * rewrite CURRENT0. eauto.
      * etransitivity; [apply RELEASED|apply RELEASED0].
      * etransitivity; [apply RELEASED|apply RELEASED0].
    + ss. committac.
      * rewrite ACQUIRABLE. auto.
      * rewrite ACQUIRABLE0. auto.
Qed.

Lemma reorder_fulfill_read
      loc1 from1 to1 val1 released1 ord1
      loc2 ts2 val2 released2 ord2
      th0 mem0
      th1
      th2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.acquire)
      (ORD2: Ordering.le ord2 Ordering.release)
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
  { instantiate (1 := ord1). destruct ord1; ss. }
  { apply WF0. }
  { inv WF0. inv MEMORY0. exploit WF0; eauto. }
  i. des.
  eexists. splits.
  - econs; eauto.
    admit. (* promise get None *)
  - destruct th0. s. econs; try eapply CommitFacts.write_mon2; eauto.
    inv COMMIT. inv COMMIT0. inv MONOTONE. inv MONOTONE0.
    unfold CommitFacts.write_min, CommitFacts.read_min.
    destruct (Ordering.le Ordering.acquire ord2) eqn:ORD2'; ss.
    + econs; committac; auto.
      * rewrite CURRENT1. auto.
      * rewrite WRITE0. apply CURRENT2.
      * unfold LocFun.add, LocFun.find.
        CommitFacts.condtac; committac.
        { rewrite RELEASED3. apply RELEASED4. }
        { etransitivity; [apply RELEASED|apply RELEASED4]. }
      * rewrite ACQUIRABLE0. auto.
    + econs; committac; auto.
      * rewrite CURRENT1. auto.
      * rewrite WRITE0. apply CURRENT2.
      * unfold LocFun.add, LocFun.find.
        CommitFacts.condtac; committac.
        { rewrite RELEASED3. apply RELEASED4. }
        { etransitivity; [apply RELEASED|apply RELEASED4]. }
      * rewrite ACQUIRABLE0. auto.
Admitted.

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
Admitted.

Lemma reorder_fulfill_fulfill
      loc1 from1 to1 val1 released1 ord1
      loc2 from2 to2 val2 released2 ord2
      th0 mem0
      th1
      th2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.acquire)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fulfill_step th0 mem0 loc1 from1 to1 val1 released1 ord1 th1)
      (STEP2: Local.fulfill_step th1 mem0 loc2 from2 to2 val2 released2 ord2 th2):
  exists th1',
    <<STEP1: Local.fulfill_step th0 mem0 loc2 from2 to2 val2 released2 ord2 th1'>> /\
    <<STEP2: Local.fulfill_step th1' mem0 loc1 from1 to1 val1 released1 ord1 th2>>.
Proof.
Admitted.

Lemma reorder_fulfill_write
      loc1 from1 to1 val1 released1 ord1
      loc2 from2 to2 val2 released2 ord2
      th0 mem0
      th1
      th2 mem2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.acquire)
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
    admit. (* promise None *)
  - exploit reorder_fulfill_promise; eauto. i. des.
    exploit reorder_fulfill_fulfill; try apply STEP2; eauto.
    { eapply Local.promise_step_future; eauto. }
    i. des.
    eexists. splits; eauto. econs 2; eauto.
    admit. (* promise None *)
Admitted.

Lemma reorder_fence_promise
      ord1
      loc2 from2 to2 val2 released2
      th0 mem0
      th1
      th2 mem2
      (ORD1: Ordering.le ord1 Ordering.acquire)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fence_step th0 mem0 ord1 th1)
      (STEP2: Local.promise_step th1 mem0 loc2 from2 to2 val2 released2 th2 mem2):
  exists th1',
    <<STEP1: Local.promise_step th0 mem0 loc2 from2 to2 val2 released2 th1' mem2>> /\
    <<STEP2: Local.fence_step th1' mem2 ord1 th2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit Memory.promise_future; try apply WF0; eauto. i. des.
  exploit Commit.future_wf; try apply WF0; eauto. i.
  exploit CommitFacts.fence_min_spec; try apply COMMIT; eauto. i. des.
  eexists. splits.
  - econs; try reflexivity; try apply MEMORY; eauto.
  - destruct th0. ss. econs; try eapply CommitFacts.fence_mon2; eauto.
    + rewrite <- COMMIT0. apply CommitFacts.fence_min_min. auto.
    + s. econs. destruct ord1; ss.
Qed.

Lemma reorder_fence_fulfill
      ord1
      loc2 from2 to2 val2 released2 ord2
      th0 mem0
      th1
      th2
      (ORD1: Ordering.le ord1 Ordering.acquire)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fence_step th0 mem0 ord1 th1)
      (STEP2: Local.fulfill_step th1 mem0 loc2 from2 to2 val2 released2 ord2 th2):
  exists th1',
    <<STEP1: Local.fulfill_step th0 mem0 loc2 from2 to2 val2 released2 ord2 th1'>> /\
    <<STEP2: Local.fence_step th1' mem0 ord1 th2>>.
Proof.
  destruct (Ordering.le Ordering.release ord1) eqn:ORD1'.
  { destruct ord1; ss. }
  inv STEP1. inv STEP2. ss.
  exploit Memory.fulfill_get; eauto. i.
  exploit Memory.le_get; try apply WF0; eauto. i.
  exploit CommitFacts.write_min_spec; try apply x1; try apply WF0; eauto.
  { eapply Snapshot.writable_mon; try apply COMMIT0; eauto. apply COMMIT. }
  { etransitivity; [apply COMMIT|]. apply COMMIT0. }
  { instantiate (1 := ord2). i. inv COMMIT0.
    rewrite <- RELEASED0; auto. apply Snapshot.incr_writes_mon. apply COMMIT.
  }
  { inv WF0. inv MEMORY1. exploit WF; eauto. }
  i. des.
  exploit CommitFacts.fence_min_spec; eauto.
  { apply WF0. }
  i. des.
  eexists. splits.
  - econs; eauto.
  - destruct th0. ss. econs; try eapply CommitFacts.fence_mon2; eauto.
    + inv COMMIT. inv COMMIT0. inv MONOTONE. inv MONOTONE0. ss.
      econs; committac.
      * rewrite ACQUIRE; auto.
      * rewrite CURRENT0. auto.
      * unfold LocFun.add, LocFun.find. rewrite ORD1'.
        CommitFacts.condtac; committac.
        etransitivity; [apply RELEASED|apply RELEASED4].
      * rewrite ACQUIRABLE. auto.
    + s. econs. destruct ord1; ss.
Qed.

Lemma reorder_fence_write
      ord1
      loc2 from2 to2 val2 released2 ord2
      th0 mem0
      th1
      th2 mem2
      (ORD1: Ordering.le ord1 Ordering.acquire)
      (WF0: Local.wf th0 mem0)
      (STEP1: Local.fence_step th0 mem0 ord1 th1)
      (STEP2: Local.write_step th1 mem0 loc2 from2 to2 val2 released2 ord2 th2 mem2):
  exists th1',
    <<STEP1: Local.write_step th0 mem0 loc2 from2 to2 val2 released2 ord2 th1' mem2>> /\
    <<STEP2: Local.fence_step th1' mem2 ord1 th2>>.
Proof.
  inv STEP2.
  - exploit reorder_fence_fulfill; eauto. i. des.
    eexists. splits; eauto. econs 1. eauto.
    admit. (* promise None *)
  - exploit reorder_fence_promise; eauto. i. des.
    exploit reorder_fence_fulfill; try apply STEP2; eauto.
    { eapply Local.promise_step_future; eauto. }
    i. des.
    eexists. splits; eauto. econs 2; eauto.
    admit. (* promise None *)
Admitted.
