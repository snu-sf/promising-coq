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
Require Import Memory.
Require Import Commit.
Require Import Thread.

Set Implicit Arguments.


Lemma write_step_promise
      lc1 mem1 loc from to val releasedc releasedm ord lc2 mem2 kind
      (STEP: Local.write_step lc1 mem1 loc from to val releasedc releasedm ord lc2 mem2 kind)
      (PROMISES: lc1.(Local.promises) = Memory.bot):
  lc2.(Local.promises) = Memory.bot.
Proof.
  inv STEP.
  - inv FULFILL. rewrite PROMISES in *. inv FULFILL0.
    exploit Memory.remove_disjoint; eauto. rewrite Memory.bot_get. congr.
  - apply Memory.ext. i. rewrite Memory.bot_get.
    destruct (Memory.get loc0 ts (Local.promises lc2)) as [[]|] eqn:X; auto.
    inv FULFILL. ss. inv FULFILL0. eapply Memory.remove_get_inv in X; eauto. des.
    inv PROMISE. ss. eapply Memory.promise_promises_get2 in X0; eauto. des.
    + subst. contradict X. auto.
    + rewrite PROMISES, Memory.bot_get in *. congr.
Qed.

Lemma program_step_promise
      lang
      e st1 lc1 mem1 st2 lc2 mem2
      (STEP: Thread.program_step e (Thread.mk lang st1 lc1 mem1) (Thread.mk lang st2 lc2 mem2))
      (PROMISES: lc1.(Local.promises) = Memory.bot):
  lc2.(Local.promises) = Memory.bot.
Proof.
  inv STEP; try by inv LOCAL.
  - eapply write_step_promise; eauto.
  - eapply write_step_promise; eauto.
    inv LOCAL1. auto.
Qed.

Lemma progress_promise_step
      lc1 mem1
      loc to val
      (LT: Time.lt (Memory.max_ts loc mem1) to)
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1):
  exists promises2 mem2,
    Local.promise_step lc1 mem1 loc (Memory.max_ts loc mem1) to val (Memory.max_capability mem2) (Local.mk lc1.(Local.commit) promises2) mem2 Memory.promise_kind_add.
Proof.
  destruct lc1. s.
  exploit Memory.promise_add_exists_max_ts; try apply WF1; eauto. s. i. des.
  eexists _, _. econs; eauto.
  - refl.
  - apply WF1.
  - eapply Commit.future_closed; try apply WF1; eauto.
    eapply Memory.promise_future; try apply WF1; eauto.
Qed.

Lemma progress_silent_step
      lc1 mem1
      (WF1: Local.wf lc1 mem1):
  Local.silent_step lc1 mem1 lc1.
Proof.
  destruct lc1. econs; try apply WF1. refl.
Qed.

Lemma progress_read_step
      lc1 mem1
      loc ord
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1)
      (PROMISES1: lc1.(Local.promises) = Memory.bot):
  exists val released lc2,
    Local.read_step lc1 mem1 loc (Memory.max_ts loc mem1) val released ord lc2.
Proof.
  exploit (Memory.max_ts_spec loc); try apply MEM1; eauto. i. des.
  exploit (@CommitFacts.read_min_spec loc (Memory.max_ts loc mem1) released); try apply WF1; i.
  { eapply MAX. inv WF1. inv COMMIT_CLOSED. inv CUR. exploit UR; eauto. i. des. rewrite x. congr. }
  { eapply MAX. inv WF1. inv COMMIT_CLOSED. inv CUR. exploit RW; eauto. i. des. rewrite x. congr. }
  { inv MEM1. exploit CLOSED; eauto. i. des. auto. }
  eexists _, _, _. econs; try exact x0; eauto.
  - refl.
  - eapply CommitFacts.read_min_closed; eauto.
    apply WF1.
Qed.

Lemma progress_fulfill_step
      lc1 mem1
      loc from to val releasedc releasedm ord
      (LT: Time.lt from to)
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1)
      (GET1: Memory.get loc to mem1 = Some (from, Message.mk val releasedm))
      (PROMISES1: lc1.(Local.promises) = Memory.singleton loc val releasedm LT)
      (TO: Time.le (Capability.rw releasedc loc) to)
      (RW: Time.lt (Capability.rw (Commit.cur (Local.commit lc1)) loc) to)
      (REL2: Capability.le (Commit.rel (Local.commit lc1) loc) releasedc)
      (REL: Ordering.le Ordering.acqrel ord ->
            Capability.le (Commit.cur (Local.commit lc1)) releasedc /\
            Time.le to (Capability.rw releasedc loc))
      (WF: Capability.wf releasedc)
      (CLOSED: Memory.closed_capability releasedc mem1):
  exists lc2,
    Local.fulfill_step lc1 mem1 loc from to val releasedc releasedm ord lc2.
Proof.
  exploit (@CommitFacts.write_min_spec loc to releasedc); try apply WF1; eauto. i. des.
  eexists (Local.mk _ _). econs; eauto.
  - rewrite PROMISES1. econs.
    apply Memory.remove_singleton.
  - eapply CommitFacts.write_min_closed; eauto. apply WF1.
Qed.

Lemma progress_write_step
      lc1 mem1
      loc to val ord
      (LT: Time.lt (Memory.max_ts loc mem1) to)
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1)
      (PROMISES1: lc1.(Local.promises) = Memory.bot):
  exists lc2 mem2,
    Local.write_step lc1 mem1 loc (Memory.max_ts loc mem1) to val (Memory.max_capability mem2) (Memory.max_capability mem2) ord lc2 mem2 Local.write_kind_promise_fulfill.
Proof.
  destruct lc1. ss. subst.
  exploit progress_promise_step; eauto. s. i. des.
  assert (promises2 = Memory.singleton loc val (Memory.max_capability mem2) LT); subst.
  { inv x0. ss. apply Memory.ext. i.
    rewrite Memory.singleton_get. repeat condtac; subst.
    - destruct (Memory.get loc to promises2) as [[]|] eqn:X.
      + exploit Memory.promise_promises_get2; eauto. i. des; subst; eauto.
        contradict x0. auto.
      + exploit Memory.promise_get2; eauto. i. congr.
    - destruct (Memory.get loc ts promises2) as [[]|] eqn:X; [|done].
      exploit Memory.promise_promises_get2; eauto. i. des; subst; eauto.
      + congr.
      + rewrite Memory.bot_get in *. congr.
    - destruct (Memory.get loc0 ts promises2) as [[]|] eqn:X; [|done].
      exploit Memory.promise_promises_get2; eauto. i. des; subst; eauto.
      + congr.
      + rewrite Memory.bot_get in *. congr.
  }
  exploit Local.promise_step_future; eauto. i. des.
  hexploit progress_fulfill_step; eauto; s.
  { inv x0. ss. apply WF2. eapply Memory.promise_get2. eauto. }
  { eauto. }
  { inv x0. inv PROMISE. ss.
    instantiate (1 := Memory.max_capability mem2).
    erewrite Memory.add_max_capability; try apply MEM1; eauto.
    s. unfold TimeMap.incr, LocFun.add. condtac; [|congr].
    apply Time.join_spec; [|refl]. apply Time.le_lteq. auto.
  }
  { eapply TimeFacts.le_lt_lt; [|apply LT].
    apply Memory.max_ts_spec. apply MEM1.
    inv WF1. inv COMMIT_CLOSED. inv CUR. exploit RW; eauto. s. i. des. rewrite x. congr.
  }
  { inv x0. inv PROMISE. ss.
    erewrite Memory.add_max_capability; try apply MEM1; eauto.
    etrans; [|apply Capability.incr_ur_le].
    apply Memory.max_capability_spec.
    - inv WF1. inv COMMIT_CLOSED0. apply REL.
    - apply MEM1.
  }
  { instantiate (1 := ord). i.
    inv x0. inv PROMISE.
    erewrite Memory.add_max_capability; try apply MEM1; eauto. ss. splits.
    - etrans; [|apply Capability.incr_ur_le].
      apply Memory.max_capability_spec.
      + inv WF1. inv COMMIT_CLOSED0. apply CUR.
      + apply MEM1.
    - apply TimeMap.incr_ts.
  }
  { apply Memory.max_capability_wf. }
  { apply Memory.max_capability_closed. apply CLOSED2. }
  i. des. eexists _, _. econs 2; eauto.
Qed.

Lemma progress_fence_step
      lc1 mem1
      ordr ordw
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1)
      (PROMISES1: lc1.(Local.promises) = Memory.bot):
  exists lc2,
    Local.fence_step lc1 mem1 ordr ordw lc2.
Proof.
  exploit CommitFacts.read_fence_min_spec; try apply WF1; eauto. i. des.
  exploit CommitFacts.write_fence_min_spec; try apply x0. i.
  eexists. econs; eauto.
  apply CommitFacts.write_fence_min_closed; eauto.
  apply CommitFacts.read_fence_min_closed; eauto.
  apply WF1.
Qed.
