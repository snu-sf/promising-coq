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
      lc1 mem1 loc from to val releasedc releasedm ord lc2 mem2
      (STEP: Local.write_step lc1 mem1 loc from to val releasedc releasedm ord lc2 mem2)
      (PROMISES: lc1.(Local.promises) = Memory.bot):
  lc2.(Local.promises) = Memory.bot.
Proof.
  inv STEP.
  - apply Memory.ext. i. rewrite Memory.bot_get.
    destruct (Memory.get loc0 ts (Local.promises lc2)) as [[]|] eqn:X; auto.
    inv FULFILL. ss. inv FULFILL0. eapply Memory.remove_get_inv in X; eauto. des.
    rewrite PROMISES, Memory.bot_get in *. congr.
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

Definition max_ts (loc:Loc.t) (mem:Memory.t): Time.t :=
  DOMap.max_key _ (mem loc).(Cell.raw).

Lemma max_ts_spec
      loc mem
      (CLOSED: Memory.closed mem):
  <<GET: exists from msg, Memory.get loc (max_ts loc mem) mem = Some (from, msg)>> /\
  <<MAX: forall ts (GET: Memory.get loc ts mem <> None), Time.le ts (max_ts loc mem)>>.
Proof.
  exploit (DOMap.max_key_spec _ (mem loc).(Cell.raw)); eauto.
  { apply CLOSED. }
  i. des. splits; eauto.
  destruct (DOMap.find
              (DOMap.max_key (DenseOrder.t * Message.t)
              (Cell.raw (mem loc))) (Cell.raw (mem loc))) as [[]|] eqn:X; [|congr].
  eexists _, _. eauto.
Qed.

(* TODO: `released` should be somehow constraint.
 * Note that we do not use `released_min`, since the update rule has `releasedr` components.
 *
 * For e.g.:
 * - released <= m.released
 * - new current <= m.released if ordering >= acqrel
 *)
Lemma progress_promise_step
      lc1 mem1
      loc to released val
      (LT: Time.lt (max_ts loc mem1) to)
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1):
  exists promises2 mem2,
    Local.promise_step lc1 mem1 loc (max_ts loc mem1) to val released (Local.mk lc1.(Local.commit) promises2) mem2.
Proof.
  destruct lc1. s.
  eexists _, _. econs.
  - s. admit.
  - refl.
  - apply WF1.
  - apply WF1.
Admitted.

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
    Local.read_step lc1 mem1 loc (max_ts loc mem1) val released ord lc2.
Proof.
  exploit (max_ts_spec loc); eauto. i. des. destruct msg.
  exploit (@CommitFacts.read_min_spec loc (max_ts loc mem1) released); try apply WF1; i.
  { eapply MAX. inv WF1. inv COMMIT_CLOSED. inv CUR. exploit UR; eauto. i. des. rewrite x. congr. }
  { eapply MAX. inv WF1. inv COMMIT_CLOSED. inv CUR. exploit RW; eauto. i. des. rewrite x. congr. }
  { inv MEM1. exploit CLOSED; eauto. i. des. auto. }
  eexists _, _, _. econs; try apply x0; eauto.
  eapply CommitFacts.read_min_closed; eauto.
  apply WF1.
Qed.

Lemma progress_fulfill_step
      lc1 mem1
      loc from to val releasedc releasedm ord
      (LT: Time.lt from to)
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1)
      (GET1: Memory.get loc to mem1 = Some (from, Message.mk val releasedm))
      (PROMISES1: lc1.(Local.promises) = Memory.singleton loc (Message.mk val releasedm) LT):
  exists lc2,
    Local.fulfill_step lc1 mem1 loc from to val releasedc releasedm ord lc2.
Proof.
  exploit (@CommitFacts.write_min_spec loc to releasedc);
    try apply WF1; eauto.
  { admit. (* writable *) }
  { admit. (* writable *) }
  { admit. (* released <= m.released *) }
  { admit. (* current <= m.released for acqrel *) }
  { admit. (* closed_capability m.released *) }
  i. des.
  eexists (Local.mk _ _). econs; eauto.
  - rewrite PROMISES1. admit.
  - admit.
  - admit.
Admitted.

Lemma progress_write_step
      lc1 mem1
      loc to val releasedc releasedm ord
      (LT: Time.lt (max_ts loc mem1) to)
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1)
      (PROMISES1: lc1.(Local.promises) = Memory.bot):
  exists lc2 mem2,
    Local.write_step lc1 mem1 loc (max_ts loc mem1) to val releasedc releasedm ord lc2 mem2.
Proof.
  destruct lc1. ss. subst.
  exploit progress_promise_step; eauto. s. i. des.
  assert (promises2 = Memory.singleton loc (Message.mk val releasedm) LT); subst.
  { inv x0. ss. admit. }
  exploit Local.promise_step_future; eauto. i. des.
  exploit (@progress_fulfill_step (Local.mk commit (Memory.singleton loc (Message.mk val releasedm) LT))); s; eauto.
  { inv x0. ss. inv PROMISE.
    - eapply Memory.add_get2. eauto.
    - eapply Memory.split_get2. eauto.
  }
  i. des.
  eexists _, _. econs 2; eauto.
Admitted.

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
