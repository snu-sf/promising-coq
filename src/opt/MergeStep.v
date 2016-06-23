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

Require MergeCommit.
Require MergeMemory.
Require ReorderCommit.

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
      (MEM0: Memory.closed mem0)
      (STEP: Local.write_step lc0 sc0 mem0 loc from to val Capability.bot released ord1 lc1 sc1 mem1 kind):
  Local.read_step lc1 mem1 loc to val released ord2 lc1.
Proof.
  inv STEP. econs; eauto.
  - inv WRITE.
    hexploit Memory.promise_future; try apply PROMISE; try apply WF0; eauto. i. des.
    hexploit Memory.promise_get2; eauto.
  - inv WRITABLE. econs; repeat (try condtac; aggrtac); (try by left; eauto).
    + etrans; [|left; eauto]. apply WF0.
    + etrans; [|left; apply SC1; auto]. apply WF0.
  - unfold Commit.read_commit, Commit.write_commit. s.
    apply Commit.antisym; econs;
      repeat (try condtac; aggrtac; rewrite <- ? Capability.join_l; try apply WF0).
    + etrans; apply WF0.
    + etrans; apply WF0.
Qed.

Lemma merge_write_read2
      loc from to val releasedm released ord1 ord2 kind
      lc0 sc0 mem0
      lc1 sc1 mem1
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (WF_RELEASED: Capability.wf releasedm)
      (RELEASED: Ordering.le Ordering.relaxed ord2 -> Capability.le releasedm lc0.(Local.commit).(Commit.acq))
      (STEP: Local.write_step lc0 sc0 mem0 loc from to val releasedm released ord1 lc1 sc1 mem1 kind):
  Local.read_step lc1 mem1 loc to val released ord2 lc1.
Proof.
  inv STEP. econs; eauto.
  - inv WRITE.
    hexploit Memory.promise_future; try apply PROMISE; try apply WF0; eauto. i. des.
    hexploit Memory.promise_get2; eauto.
  - inv WRITABLE. econs; repeat (try condtac; aggrtac); (try by left; eauto).
    etrans; [|left; eauto]. apply WF0.
  - unfold Commit.read_commit, Commit.write_commit. s.
    apply Commit.antisym; econs;
      repeat (try condtac; aggrtac; rewrite <- ? Capability.join_l; try apply WF0; eauto).
    + etrans; apply WF0.
    + etrans; apply WF0.
Qed.

Lemma merge_write_write_relaxed
      loc ts1 ts2 ts3 val1 val2 released0 released2 ord kind
      lc0 sc0 mem0
      lc3 sc3 mem3
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL_WF: Capability.wf released0)
      (REL_CLOSED: Memory.closed_capability released0 mem0)
      (ORD: Ordering.le ord Ordering.relaxed)
      (TS12: Time.lt ts1 ts2)
      (TS23: Time.lt ts2 ts3)
      (STEP: Local.write_step lc0 sc0 mem0 loc ts1 ts3 val2 released0 released2 ord lc3 sc3 mem3 kind):
  exists lc1' lc2' lc3' sc2' sc3' mem2' mem3' released1' released2',
    <<STEP1: Local.promise_step lc0 mem0 loc ts1 ts3 val2 released2 lc1' mem3 kind>> /\
    <<STEP2: Local.write_step lc1' sc0 mem3 loc ts1 ts2 val1 released0 released1' ord lc2' sc2' mem2' (Memory.promise_kind_split ts3)>> /\
    <<STEP3: Local.write_step lc2' sc2' mem2' loc ts2 ts3 val2 released1' released2' ord lc3' sc3' mem3' Memory.promise_kind_lower>> /\
    <<REL3: Capability.le released2' released2>> /\
    <<LOCAL3: sim_local lc3' lc3>> /\
    <<SC3: TimeMap.le sc3' sc3>> /\
    <<MEM3: Memory.sim mem3 mem3'>>.
Proof.
  inv STEP. inv WRITE.
  exploit Memory.promise_future; try apply PROMISE; try apply WF0; eauto. i. des.
  exploit MergeMemory.remove_promise_remove_remove; try apply REMOVE; eauto. i. des.
  esplits.
  - econs; eauto.
  - econs; eauto.
    + admit. (* writable *)
    + econs; eauto.
    + admit. (* released closed *)
    + i. destruct ord; inv ORD; inv H.
  - econs; eauto.
    + admit. (* writable *)
    + instantiate (1 := mem2).
      econs; eauto.
      * admit. (* promsie *)
      * unfold Local.commit at 1 3 4.
        admit. (* remove *)
    + exploit Memory.promise_future; try apply SPLIT; eauto.
      { eapply promise_closed_capability; try apply SPLIT; eauto.
        - eapply Memory.future_closed_timemap; eauto.
        - eapply Commit.future_closed; eauto. apply WF0.
        - eapply Memory.future_closed_capability; eauto.
      }
      i. des.
      repeat (try condtac; aggrtac; try apply WF0).
      * eapply Memory.future_closed_capability; eauto. etrans; eauto.
      * eapply Memory.future_closed_capability; try apply WF0. etrans; eauto.
      * eapply Memory.future_closed_capability; try apply WF0. etrans; eauto.
    + i. destruct ord; inv ORD; inv H.
  - repeat (try condtac; aggrtac; try apply WF0).
  - s. econs; ss.
    eapply MergeCommit.write_write_commit; eauto. apply WF0.
  - eapply MergeCommit.write_write_sc; eauto.
  - inv SPLIT. econs 2; eauto. econs 1. eauto.
Admitted.

Lemma merge_write_write_add
      loc ts1 ts2 ts3 val1 val2 released0 released2 ord
      lc0 sc0 mem0
      lc2 sc2 mem2
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL_WF: Capability.wf released0)
      (REL_CLOSED: Memory.closed_capability released0 mem0)
      (TS12: Time.lt ts1 ts2)
      (TS23: Time.lt ts2 ts3)
      (STEP: Local.write_step lc0 sc0 mem0 loc ts1 ts3 val2 released0 released2 ord lc2 sc2 mem2 Memory.promise_kind_add):
  exists lc1' lc2' sc1' sc2' mem1' mem2' released1' released2',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc ts1 ts2 val1 released0 released1' ord lc1' sc1' mem1' Memory.promise_kind_add>> /\
    <<STEP2: Local.write_step lc1' sc1' mem1' loc ts2 ts3 val2 released1' released2' ord lc2' sc2' mem2' Memory.promise_kind_add>> /\
    <<REL2: Capability.le released2' released2>> /\
    <<LOCAL2: sim_local lc2' lc2>> /\
    <<SC2: TimeMap.le sc2' sc2>> /\
    <<MEM2: Memory.sim mem2 mem2'>>.
Proof.
Admitted.

Lemma merge_write_write
      loc ts1 ts2 ts3 val1 val2 released0 released2 ord kind
      lc0 sc0 mem0
      lc3 sc3 mem3
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL_WF: Capability.wf released0)
      (REL_CLOSED: Memory.closed_capability released0 mem0)
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
    <<MEM3: Memory.sim mem3 mem3'>>.
Proof.
  destruct (Ordering.le ord Ordering.relaxed) eqn:ORD.
  - exploit merge_write_write_relaxed; try apply TS12; eauto. i. des.
    esplits; try apply STEP2; eauto.
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
      (REL_WF: Capability.wf released0)
      (REL_CLOSED: Memory.closed_capability released0 mem0)
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
    <<MEM3: Memory.sim mem3 mem3'>>.
Proof.
  exploit merge_write_write; try apply TS12; eauto. i. des.
  - exploit Local.promise_step_future; eauto. i. des.
    exploit Local.write_step_future; try apply STEP2; eauto. i. des.
    exploit sim_local_write; try apply STEP3;
      try apply Capability.bot_spec; try refl; eauto; committac.
    { admit. (* write_step's released is wf *) }
    i. des.
    esplits; cycle 1; eauto; try (etrans; eauto).
  - inv STEP1.
    exploit Local.write_step_future; try apply STEP2; eauto. i. des.
    exploit sim_local_write; try apply STEP3;
      try apply Capability.bot_spec; try refl; eauto; committac.
    { admit. (* write_step's released is wf *) }
    i. des.
    esplits; cycle 1; eauto; try (etrans; eauto).
Admitted.

Lemma merge_fence_fence
      ordr ordw
      lc0 sc0 mem0
      lc2 sc2
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP: Local.fence_step lc0 sc0 mem0 ordr ordw lc2 sc2):
  exists lc1 lc2' sc1' sc2',
    <<STEP1: Local.fence_step lc0 sc0 mem0 ordr ordw lc1 sc1'>> /\
    <<STEP2: Local.fence_step lc1 sc1' mem0 ordr ordw lc2' sc2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<SC2: TimeMap.le sc2' sc2>>.
Proof.
  inv STEP. esplits.
  - econs; eauto.
  - econs; eauto.
  - s. econs; ss. etrans; [etrans|].
    + apply CommitFacts.write_fence_commit_mon; [|refl|refl].
      apply ReorderCommit.read_fence_write_fence_commit; eauto.
      eapply CommitFacts.read_fence_future; apply WF0.
    + apply CommitFacts.write_fence_commit_mon; [|refl|refl].
      apply CommitFacts.write_fence_commit_mon; [|refl|refl].
      apply MergeCommit.read_fence_read_fence_commit; eauto. apply WF0.
    + eapply MergeCommit.write_fence_write_fence_commit; eauto.
      eapply CommitFacts.read_fence_future; apply WF0.
  - s. etrans; [etrans|].
    + apply CommitFacts.write_fence_sc_mon; [|refl|refl].
      eapply ReorderCommit.read_fence_write_fence_commit.
      eapply CommitFacts.read_fence_future; apply WF0.
    + apply CommitFacts.write_fence_sc_mon; [|refl|refl].
      apply CommitFacts.write_fence_commit_mon; [|refl|refl].
      apply MergeCommit.read_fence_read_fence_commit; eauto. apply WF0.
    + apply MergeCommit.write_fence_write_fence_sc; eauto; try refl.
      eapply CommitFacts.read_fence_future; apply WF0.
Qed.
