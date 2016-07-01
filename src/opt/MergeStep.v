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
Require Import MemoryFacts.
Require Import Commit.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import FulfillStep.
Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import Compatibility.
Require Import Simulation.

Require MergeCommit.
Require ReorderCommit.
Require Import MemoryReorder.
Require Import MemorySplit.
Require Import MemoryMerge.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma merge_read_read
      loc ts val released ord
      lc0 lc2 mem0
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc ts val released ord lc2):
  Local.read_step lc2 mem0 loc ts val released ord lc2.
Proof.
  inv STEP1. refine (Local.step_read _ _ _ _ _); s; eauto.
  - econs; repeat (try condtac; aggrtac); try apply READABLE; auto.
    + inv MEM0. exploit CLOSED; eauto. i. des.
      etrans; eauto. apply WF.
    + inv MEM0. exploit CLOSED; eauto. i. des. auto.
  - apply Commit.antisym.
    + apply MergeCommit.read_read_commit; try refl; try apply WF0.
      eapply MEM0. eauto.
    + apply CommitFacts.read_commit_incr.
Qed.

Lemma merge_write_read1
      loc from to val released ord1 ord2 kind
      lc0 sc0 mem0
      lc1 sc1 mem1
      (ORD: Ordering.le Ordering.seqcst ord2 -> Ordering.le Ordering.seqcst ord1)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP: Local.write_step lc0 sc0 mem0 loc from to val Capability.bot released ord1 lc1 sc1 mem1 kind):
  Local.read_step lc1 mem1 loc to val released ord2 lc1.
Proof.
  inv STEP. econs; eauto.
  - inv WRITE.
    hexploit Memory.promise_future; try apply PROMISE; try apply WF0; eauto; try by committac.
    { eapply Local.promise_closed_capability; eauto; try apply WF0. committac. }
    i. des.
    hexploit Memory.promise_get2; eauto.
  - inv WRITABLE. econs; repeat (try condtac; aggrtac); (try by left; eauto).
    + etrans; [|left; eauto]. apply WF0.
    + etrans; [|left; apply SC1; auto]. apply WF0.
  - unfold Commit.read_commit, Commit.write_commit. s.
    apply Commit.antisym; econs;
      repeat (try condtac; aggrtac; rewrite <- ? Capability.join_l; try apply WF0).
    + etrans; apply WF0.
Qed.

Lemma merge_write_read2
      loc from to val releasedm released ord1 ord2 kind
      lc0 sc0 mem0
      lc1 sc1 mem1
      (ORD: Ordering.le Ordering.seqcst ord2 -> Ordering.le Ordering.seqcst ord1)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (WF_RELEASED: Capability.wf releasedm)
      (WF_CLOSED: Memory.closed_capability releasedm mem0)
      (RLX: Ordering.le Ordering.relaxed ord2 -> Capability.le releasedm lc0.(Local.commit).(Commit.acq))
      (ACQ: Ordering.le Ordering.acqrel ord2 -> Capability.le releasedm lc0.(Local.commit).(Commit.cur))
      (STEP: Local.write_step lc0 sc0 mem0 loc from to val releasedm released ord1 lc1 sc1 mem1 kind):
  Local.read_step lc1 mem1 loc to val released ord2 lc1.
Proof.
  inv STEP. econs; eauto.
  - inv WRITE.
    hexploit Memory.promise_future; try apply PROMISE; try apply WF0; eauto; try by committac.
    { eapply Local.promise_closed_capability; eauto; try apply WF0. }
    i. des.
    hexploit Memory.promise_get2; eauto.
  - inv WRITABLE. econs; repeat (try condtac; aggrtac); (try by left; eauto).
    + etrans; [|left; eauto]. apply WF0.
    + etrans; [|left; apply SC1; auto]. apply ACQ. etrans; eauto. auto.
    + etrans; [|left; apply SC1; auto]. apply WF0.
  - unfold Commit.read_commit, Commit.write_commit. s.
    apply Commit.antisym; econs;
      repeat (try condtac; aggrtac; rewrite <- ? Capability.join_l; try apply WF0; eauto).
    etrans; apply WF0.
Qed.

Lemma promise_promise_promise
      loc from to val released1 released2 kind
      lc0 mem0
      lc1 mem1
      lc2 mem2
      (PROMISE1: Local.promise_step lc0 mem0 loc from to val released1 lc1 mem1 kind)
      (PROMISE2: Local.promise_step lc1 mem1 loc from to val released2 lc2 mem2 (Memory.promise_kind_lower released1)):
  Local.promise_step lc0 mem0 loc from to val released2 lc2 mem2 kind.
Proof.
  inv PROMISE1. inv PROMISE2. ss.
  exploit MemoryMerge.promise_promise_promise; try exact PROMISE; eauto. i.
  econs; eauto.
Qed.

Lemma to_lt_from_le
      mem loc
      from1 to1 msg1
      from2 to2 msg2
      (GET1: Memory.get loc to1 mem = Some (from1, msg1))
      (GET2: Memory.get loc to2 mem = Some (from2, msg2))
      (LT: Time.lt to1 to2):
  Time.le to1 from2.
Proof.
  destruct (TimeFacts.le_lt_dec to1 from2); auto.
  destruct (mem loc).(Cell.WF). exfalso. eapply DISJOINT.
  - apply GET1.
  - apply GET2.
  - ii. subst. eapply Time.lt_strorder. eauto.
  - apply Interval.mem_ub. exploit VOLUME; try exact GET1; eauto. i. des; auto.
    inv x. inv l.
  - econs.
    + apply l.
    + left. auto.
Qed.

Lemma fulfill_step_lc_from
      loc from to val releasedm released ord
      lc0 sc0 mem0
      lc1 sc1
      (WF: Local.wf lc0 mem0)
      (MEM: Memory.closed mem0)
      (STEP: fulfill_step lc0 sc0 loc from to val releasedm released ord lc1 sc1):
  Time.le (lc0.(Local.commit).(Commit.cur).(Capability.rw) loc) from.
Proof.
  inv WF. inv STEP.
  exploit Memory.remove_get0; eauto. i.
  exploit PROMISES; eauto. i.
  inv COMMIT_CLOSED. inv CUR. exploit RW; eauto. instantiate (1 := loc). i. des.
  eapply to_lt_from_le; eauto.
  inv WRITABLE. auto.
Qed.

Lemma merge_split
      loc ts1 ts2 ts3 val2 val3 released0 released3 ord
      lc0 sc0 mem0
      lc3 sc3
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (LC0_TS: Time.le (lc0.(Local.commit).(Commit.cur).(Capability.rw) loc) ts1)
      (REL0_TS: Time.le (Capability.rw released0 loc) ts1)
      (REL0_WF: Capability.wf released0)
      (REL0_CLOSED: Memory.closed_capability released0 mem0)
      (TS12: Time.lt ts1 ts2)
      (TS23: Time.lt ts2 ts3)
      (STEP: fulfill_step lc0 sc0 loc ts1 ts3 val3 released0 released3 ord lc3 sc3):
  exists lc1' lc2' lc3' sc2' sc3' mem1' released1',
    <<STEP1: Local.promise_step lc0 mem0 loc ts1 ts2 val2 released1' lc1' mem1' (Memory.promise_kind_split ts3 val3 released3)>> /\
    <<STEP2: fulfill_step lc1' sc0 loc ts1 ts2 val2 released0 released1' ord lc2' sc2'>> /\
    <<STEP3: fulfill_step lc2' sc2' loc ts2 ts3 val3 released1' released3 ord lc3' sc3'>> /\
    <<LOCAL3: sim_local lc3' lc3>> /\
    <<SC3: TimeMap.le sc3' sc3>> /\
    <<MEM3: sim_memory mem1' mem0>> /\
    <<REL1': released1' =
             Capability.join released0
               (Commit.rel
                  (Commit.write_commit (Local.commit lc0) sc0 loc ts2 ord)
                  loc)>>.
Proof.
  set (released1' :=
      Capability.join released0
        (Commit.rel
           (Commit.write_commit (Local.commit lc0) sc0 loc ts2 ord)
           loc)).
  assert (REL1'_WF: Capability.wf released1').
  { unfold released1'. repeat (try condtac; aggrtac; try by apply WF0). }
  exploit fulfill_step_future; eauto. i. des.
  inv STEP.
  exploit MemorySplit.remove_promise_promise_remove_remove;
    try exact TS12; try exact TS23; try exact REMOVE.
  { apply REL1'_WF. }
  { unfold released1'. repeat (try condtac; aggrtac).
    - etrans; eauto. left. auto.
    - etrans; eauto. left. auto.
    - etrans; [apply WF0|]. etrans; eauto. left. auto.
  }
  { apply WF0. }
  i. des.
  exploit Memory.promise_future; try eexact STEP1; (try by apply WF0); (try by committac); eauto.
  { eapply Local.promise_closed_capability; try apply WF0; eauto. }
  i. des.
  assert (REL1'_CLOSED: Memory.closed_capability released1' mem1).
  { unfold released1'. repeat (try condtac; aggrtac; try by apply WF0).
    - eapply Memory.future_closed_capability; eauto. apply WF0.
    - apply LE_PROMISES2. eapply Memory.promise_get2. eauto.
    - econs; committac.
    - eapply Memory.future_closed_capability; eauto. apply WF0.
  }
  esplits.
  - econs; eauto.
  - econs; try exact STEP2; auto.
    + unfold Local.commit at 1 2. refl.
    + s. inv WF0. inv WRITABLE.
      exploit Memory.remove_get0; try exact REMOVE; eauto. i.
      exploit PROMISES; eauto. i.
      inv COMMIT_CLOSED. inv CUR.
      exploit RW; eauto. i. des. eauto.
      exploit SC; eauto. i. des. eauto.
      exploit SC0; eauto. i. des.
      econs; i;
        eapply TimeFacts.le_lt_lt; try eexact TS12;
        eapply to_lt_from_le; eauto.
  - unfold Local.commit at 1.
    econs; try exact STEP3; auto.
    + etrans; eauto. unfold released1'.
      repeat (try condtac; aggrtac; try by apply WF0).
      unfold Commit.write_sc. econs; repeat (try condtac; aggrtac).
    + s. inv WRITABLE. econs; repeat (try condtac; aggrtac; eauto).
      * eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec.
      * eapply TimeFacts.le_lt_lt; eauto. apply Time.bot_spec.
      * unfold Commit.write_sc. repeat (try condtac; aggrtac; eauto).
  - s. econs; ss.
    + eapply MergeCommit.write_write_commit; eauto. apply WF0.
    + apply SimPromises.sem_bot.
  - eapply MergeCommit.write_write_sc; eauto.
  - inv STEP1. eapply split_sim_memory. eauto.
  - refl.
Qed.

Lemma merge_write_write_relaxed
      loc ts1 ts2 ts3 val2 val3 released0 released3 ord kind
      lc0 sc0 mem0
      lc3 sc3 mem3
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL0_WF: Capability.wf released0)
      (REL0_TS: Time.le (Capability.rw released0 loc) ts1)
      (REL0_CLOSED: Memory.closed_capability released0 mem0)
      (ORD: Ordering.le ord Ordering.relaxed)
      (TS12: Time.lt ts1 ts2)
      (TS23: Time.lt ts2 ts3)
      (STEP: Local.write_step lc0 sc0 mem0 loc ts1 ts3 val3 released0 released3 ord lc3 sc3 mem3 kind):
  exists lc1' lc2' lc3' sc2' sc3' mem1' mem2' mem3' released2' released3',
    <<STEP1: Local.promise_step lc0 mem0 loc ts1 ts3 val3 released3 lc1' mem1' kind>> /\
    <<STEP2: Local.write_step lc1' sc0 mem1' loc ts1 ts2 val2 released0 released2' ord lc2' sc2' mem2' (Memory.promise_kind_split ts3 val3 released3)>> /\
    <<STEP3: Local.write_step lc2' sc2' mem2' loc ts2 ts3 val3 released2' released3' ord lc3' sc3' mem3' (Memory.promise_kind_lower released3)>> /\
    <<REL3: Capability.le released3' released3>> /\
    <<LOCAL3: sim_local lc3' lc3>> /\
    <<SC3: TimeMap.le sc3' sc3>> /\
    <<MEM3: sim_memory mem3' mem3>>.
Proof.
  exploit Local.write_step_future; eauto. i. des.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit merge_split; try exact STEP2; eauto; try by committac.
  { eapply fulfill_step_lc_from; eauto. }
  i. des.
  exploit Local.promise_step_future; try exact STEP0; eauto. i. des.
  exploit promise_fulfill_write; try eexact STEP3; eauto; try by committac.
  { i. destruct ord; inv ORD; inv H. }
  i. des.
  exploit Local.write_step_future; eauto; try by committac. i. des.
  exploit sim_local_fulfill; try eexact STEP4; try exact REL_LE; try refl; eauto. i. des.
  exploit (@fulfill_write lc2' sc2' mem2'); try eexact STEP_SRC; eauto. i. des.
  esplits; eauto.
  - etrans; eauto.
  - etrans; eauto.
  - etrans; eauto. etrans; eauto.
Qed.

Lemma promise_add_promise_split_promise_add_promise_add
      loc ts1 ts2 ts3 val2 val3 released2 released3
      lc0 sc0 mem0
      lc1 mem1
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL_CLOSED: forall promises1' mem1' (PROMISE1: Memory.promise (Local.promises lc0) mem0 loc ts1 ts2 val2 released2 promises1' mem1' Memory.promise_kind_add),
          Memory.closed_capability released2 mem1')
      (STEP1: Local.promise_step lc0 mem0 loc ts1 ts3 val3 released3 lc1 mem1 Memory.promise_kind_add)
      (STEP2: Local.promise_step lc1 mem1 loc ts1 ts2 val2 released2 lc2 mem2 (Memory.promise_kind_split ts3 val3 released3)):
  exists lc1' mem1',
    <<STEP1: Local.promise_step lc0 mem0 loc ts1 ts2 val2 released2 lc1' mem1' Memory.promise_kind_add>> /\
    <<STEP2: Local.promise_step lc1' mem1' loc ts2 ts3 val3 released3 lc2 mem2 Memory.promise_kind_add>>.
Proof.
  exploit Local.promise_step_future; try exact STEP1; eauto. i. des.
  (* exploit Local.promise_step_future; try exact STEP2; eauto. i. des. *)
  inv STEP1. inv STEP2.
  exploit MemorySplit.commute_promise_add_promise_split_promise_add_promise_add; eauto. i. des.
  esplits.
  - econs; eauto.
  - refine (Local.step_promise _ _ _); eauto.
    eapply Memory.promise_closed_capability; eauto.
Qed.

Lemma reorder_promise_add_promise_add
      loc1 from1 to1 val1 released1
      loc2 from2 to2 val2 released2
      lc0 sc0 mem0
      lc1 mem1
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (DIFF: (loc1, to1) <> (loc2, to2))
      (REL_CLOSED: forall promises1' mem1' (PROMISE1: Memory.promise (Local.promises lc0) mem0 loc2 from2 to2 val2 released2 promises1' mem1' Memory.promise_kind_add),
          Memory.closed_capability released2 mem1')
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 val1 released1 lc1 mem1 Memory.promise_kind_add)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 val2 released2 lc2 mem2 Memory.promise_kind_add):
  exists lc1' mem1',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 val2 released2 lc1' mem1' Memory.promise_kind_add>> /\
    <<STEP2: Local.promise_step lc1' mem1' loc1 from1 to1 val1 released1 lc2 mem2 Memory.promise_kind_add>>.
Proof.
  exploit Local.promise_step_future; try exact STEP1; eauto. i. des.
  exploit Local.promise_step_future; try exact STEP2; eauto. i. des.
  inv STEP1. inv STEP2.
  exploit MemoryReorder.promise_add_promise_add; try exact PROMISE; eauto. i. des.
  esplits.
  - econs; eauto.
  - refine (Local.step_promise _ _ _); eauto.
    committac.
Qed.

Lemma reorder_promise_add_fulfill
      loc1 from1 to1 val1 released1
      loc2 from2 to2 val2 releasedm2 released2 ord2
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (RELM_WF: Memory.closed_capability releasedm2 mem0)
      (DIFF: (loc1, to1) <> (loc2, to2))
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 val1 released1 lc1 mem1 Memory.promise_kind_add)
      (STEP2: fulfill_step lc1 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2):
  exists lc1',
    <<STEP1: fulfill_step lc0 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2>> /\
    <<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 val1 released1 lc2 mem1 Memory.promise_kind_add>>.
Proof.
  exploit Local.promise_step_future; try exact STEP1; eauto. i. des.
  exploit fulfill_step_future; try exact STEP2; try exact WF2; eauto; try by committac. i. des.
  inv STEP1. inv STEP2.
  exploit MemoryReorder.promise_add_remove; try exact PROMISE; eauto. i. des.
  esplits.
  - econs; eauto.
  - econs; eauto.
Qed.

Lemma write_step_promise
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind l
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
      (PROMISES: lc1.(Local.promises) l = Cell.bot):
  lc2.(Local.promises) l = Cell.bot.
Proof.
  inv STEP. inv WRITE. s.
  apply Cell.ext. i. rewrite Cell.bot_get.
  etrans; [eapply Memory.remove_o; eauto|].
  inv PROMISE.
  - erewrite Memory.add_o; eauto. condtac; ss.
    unfold Memory.get. rewrite PROMISES, Cell.bot_get. auto.
  - erewrite Memory.split_o; eauto. repeat condtac; ss.
    + guardH o. des. subst.
      exploit Memory.split_get0; try exact PROMISES0; eauto.
      unfold Memory.get. rewrite PROMISES, ? Cell.bot_get. i. des. congr.
    + unfold Memory.get. rewrite PROMISES, Cell.bot_get. auto.
  - erewrite Memory.lower_o; eauto. condtac; ss.
    unfold Memory.get. rewrite PROMISES, Cell.bot_get. auto.
Qed.

Lemma merge_write_write_add
      loc ts1 ts2 ts3 val1 val2 released0 released2 ord
      lc0 sc0 mem0
      lc2 sc2 mem2
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL0_WF: Capability.wf released0)
      (REL0_TS: Time.le (Capability.rw released0 loc) ts1)
      (REL0_CLOSED: Memory.closed_capability released0 mem0)
      (TS12: Time.lt ts1 ts2)
      (TS23: Time.lt ts2 ts3)
      (STEP: Local.write_step lc0 sc0 mem0 loc ts1 ts3 val2 released0 released2 ord lc2 sc2 mem2 Memory.promise_kind_add):
  exists lc1' lc2' sc1' sc2' mem1' mem2' released1' released2',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc ts1 ts2 val1 released0 released1' ord lc1' sc1' mem1' Memory.promise_kind_add>> /\
    <<STEP2: Local.write_step lc1' sc1' mem1' loc ts2 ts3 val2 released1' released2' ord lc2' sc2' mem2' Memory.promise_kind_add>> /\
    <<REL2: Capability.le released2' released2>> /\
    <<LOCAL2: sim_local lc2' lc2>> /\
    <<SC2: TimeMap.le sc2' sc2>> /\
    <<MEM2: sim_memory mem2' mem2>>.
Proof.
  exploit Local.write_step_future; eauto. i. des.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit merge_split; try exact STEP2; eauto; try by committac.
  { eapply fulfill_step_lc_from; eauto. }
  i. des.
  exploit promise_add_promise_split_promise_add_promise_add; try exact STEP1; eauto.
  { i. rewrite REL1'.
    eapply Local.promise_closed_capability; try eexact PROMISE1; eauto; try apply WF0.
    inv STEP1. apply WF0.
  }
  i. des.
  exploit Local.promise_step_future; try eexact STEP5; eauto. i. des.
  exploit reorder_promise_add_fulfill; try exact STEP6; try eexact STEP3; eauto; try by committac.
  { ii. inv H. exfalso. eapply Time.lt_strorder. eauto. }
  i. des.
  exploit fulfill_step_future; try eexact STEP7; try exact WF3; eauto; try by committac. i. des.
  exploit promise_fulfill_write; try eexact STEP5; eauto. i. des.
  exploit Local.write_step_future; eauto. i. des.
  exploit promise_fulfill_write; try eexact STEP8; eauto.
  { i. exploit ORD; eauto. i. des. splits; auto.
    eapply write_step_promise; eauto.
  }
  i. des.
  hexploit sim_local_write; try exact MEM; try exact REL_LE; try refl; eauto. i. des.
  esplits; eauto.
  - etrans; eauto.
  - etrans; eauto.
  - etrans; eauto.
  - etrans; eauto. etrans; eauto.
Qed.

Lemma merge_write_write
      loc ts1 ts2 ts3 val1 val2 released0 released2 ord kind
      lc0 sc0 mem0
      lc3 sc3 mem3
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL0_WF: Capability.wf released0)
      (REL0_TS: Time.le (Capability.rw released0 loc) ts1)
      (REL0_CLOSED: Memory.closed_capability released0 mem0)
      (TS12: Time.lt ts1 ts2)
      (TS23: Time.lt ts2 ts3)
      (STEP: Local.write_step lc0 sc0 mem0 loc ts1 ts3 val2 released0 released2 ord lc3 sc3 mem3 kind):
  exists lc1' lc2' lc3' sc2' sc3' mem1' mem2' mem3' released1' released2' kind2 kind3,
    <<STEP1: Local.promise_step lc0 mem0 loc ts1 ts3 val2 released2 lc1' mem1' kind \/ (lc0, mem0) = (lc1', mem1')>> /\
    <<STEP2: Local.write_step lc1' sc0 mem1' loc ts1 ts2 val1 released0 released1' ord lc2' sc2' mem2' kind2>> /\
    <<STEP3: Local.write_step lc2' sc2' mem2' loc ts2 ts3 val2 released1' released2' ord lc3' sc3' mem3' kind3>> /\
    <<REL3: Capability.le released2' released2>> /\
    <<LOCAL3: sim_local lc3' lc3>> /\
    <<SC3: TimeMap.le sc3' sc3>> /\
    <<MEM3: sim_memory mem3' mem3>>.
Proof.
  destruct (Ordering.le ord Ordering.relaxed) eqn:ORD.
  - exploit merge_write_write_relaxed; try apply TS12; eauto. i. des.
    esplits; try exact STEP2; eauto.
  - assert (kind = Memory.promise_kind_add).
    { inv STEP. eapply RELEASE. by destruct ord; inv ORD. }
    subst. exploit merge_write_write_add; try apply TS12; eauto. i. des.
    esplits; try apply STEP2; eauto.
Qed.

Lemma merge_write_write_bot
      loc ts1 ts2 ts3 val1 val2 released0 released2 ord kind
      lc0 sc0 mem0
      lc3 sc3 mem3
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL0_WF: Capability.wf released0)
      (REL0_TS: Time.le (Capability.rw released0 loc) ts1)
      (REL0_CLOSED: Memory.closed_capability released0 mem0)
      (TS12: Time.lt ts1 ts2)
      (TS23: Time.lt ts2 ts3)
      (STEP: Local.write_step lc0 sc0 mem0 loc ts1 ts3 val2 released0 released2 ord lc3 sc3 mem3 kind):
  exists lc1' lc2' lc3' sc2' sc3' mem1' mem2' mem3' released1' released2' kind2 kind3,
    <<STEP1: Local.promise_step lc0 mem0 loc ts1 ts3 val2 released2 lc1' mem1' kind \/ (lc0, mem0) = (lc1', mem1')>> /\
    <<STEP2: Local.write_step lc1' sc0 mem1' loc ts1 ts2 val1 released0 released1' ord lc2' sc2' mem2' kind2>> /\
    <<STEP3: Local.write_step lc2' sc2' mem2' loc ts2 ts3 val2 Capability.bot released2' ord lc3' sc3' mem3' kind3>> /\
    <<REL3: Capability.le released2' released2>> /\
    <<LOCAL3: sim_local lc3' lc3>> /\
    <<SC3: TimeMap.le sc3' sc3>> /\
    <<MEM3: sim_memory mem3' mem3>>.
Proof.
  exploit merge_write_write; try apply TS12; eauto. i. des.
  - exploit Local.promise_step_future; eauto. i. des.
    exploit Memory.future_closed_capability; try exact REL0_CLOSED; eauto. i.
    exploit Local.write_step_future; try apply STEP2; eauto. i. des.
    hexploit sim_local_write; try apply STEP3;
      try apply Capability.bot_spec; try refl; eauto; committac. i. des.
    esplits; cycle 1; eauto; try (etrans; eauto).
  - inv STEP1.
    exploit Local.write_step_future; try apply STEP2; eauto. i. des.
    hexploit sim_local_write; try apply STEP3;
      try apply Capability.bot_spec; try refl; eauto; committac. i. des.
    esplits; cycle 1; eauto; try (etrans; eauto).
Qed.

Lemma merge_fence_fence
      ordr ordw
      lc0 sc0 mem0
      lc2 sc2
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP: Local.fence_step lc0 sc0 ordr ordw lc2 sc2):
  exists lc1 lc2' sc1' sc2',
    <<STEP1: Local.fence_step lc0 sc0 ordr ordw lc1 sc1'>> /\
    <<STEP2: Local.fence_step lc1 sc1' ordr ordw lc2' sc2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<SC2: TimeMap.le sc2' sc2>>.
Proof.
  inv STEP. esplits.
  - econs; eauto.
  - econs; eauto.
  - s. econs; ss.
    + unfold Commit.read_fence_commit, Commit.write_fence_commit, Commit.write_fence_sc.
      econs; repeat (try condtac; aggrtac; try apply WF0).
    + apply SimPromises.sem_bot.
  - unfold Commit.read_fence_commit, Commit.write_fence_commit, Commit.write_fence_sc.
    repeat (try condtac; aggrtac; try apply WF0).
Qed.
