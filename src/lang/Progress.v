Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import Memory.
Require Import Commit.
Require Import Thread.

Set Implicit Arguments.


Lemma internal_step_promise
      lang
      st1 lc1 mem1 st2 lc2 mem2
      (STEP: Thread.internal_step (Thread.mk lang st1 lc1 mem1) (Thread.mk lang st2 lc2 mem2))
      (PROMISES: lc1.(Local.promises) = Promises.bot):
  lc2.(Local.promises) = Promises.bot.
Proof.
  inv STEP; try inv LOCAL; ss.
  - admit.
  - admit.
  - admit.
Admitted.


Inductive max_timestamp (loc:Loc.t) (ts:Time.t) (mem:Memory.t): Prop :=
| max_timestamp_intro
    msg
    (MSG: Memory.get loc ts mem = Some msg)
    (MAX: forall ts' (LT: Time.lt ts ts'), Memory.get loc ts' mem = None)
.

Lemma exists_max_timestamp
      loc mem
      (WF: Memory.closed mem):
  exists ts, max_timestamp loc ts mem.
Proof.
Admitted.

(* TODO: `released` should be somehow constraint.
 * Note that we do not use `released_min`, since the update rule has `releasedr` components.
 *
 * For e.g.:
 * - released <= m.released
 * - new current <= m.released if ordering >= acqrel
 *)
Lemma progress_promise_step
      lc1 mem1
      loc from to released val
      (MAX: max_timestamp loc from mem1)
      (LT: Time.lt from to)
      (WF1: Local.wf lc1 mem1):
  exists promises2 mem2,
    Local.promise_step lc1 mem1 loc from to val released (Local.mk lc1.(Local.commit) promises2) mem2.
Proof.
  destruct lc1. s.
  eexists _, _. econs.
  - s. econs 1. admit.
  - reflexivity.
  - apply WF1.
  - apply WF1.
Admitted.

Lemma progress_silent_step
      lc1 mem1
      (WF1: Local.wf lc1 mem1):
  Local.silent_step lc1 mem1 lc1.
Proof.
  destruct lc1. econs; try apply WF1. reflexivity.
Qed.

Lemma progress_read_step
      lc1 mem1
      loc ord ts
      (WF1: Local.wf lc1 mem1)
      (PROMISE1: lc1.(Local.promises) = Promises.bot)
      (MAX: max_timestamp loc ts mem1):
  exists val released lc2,
    Local.read_step lc1 mem1 loc ts val released ord lc2.
Proof.
  inv MAX. destruct msg.
  exploit (@CommitFacts.read_min_spec loc ts released); try apply WF1.
  { admit. }
  { admit. }
  { inv WF1. exploit MEMORY; eauto. i. des. auto. }
  i. des. eexists _, _, _. econs; try apply READ; eauto.
  - rewrite PROMISE1, Promises.bot_spec. auto.
  - admit. (* commit.closed *)
Admitted.

Lemma progress_fulfill_step
      lc1 mem1
      loc from to val released ord
      (LT: Time.lt from to)
      (WF1: Local.wf lc1 mem1)
      (GET1: Memory.get loc to mem1 = Some (Message.mk val released))
      (PROMISE1: lc1.(Local.promises) = Promises.set loc to Promises.bot):
  exists lc2,
    Local.fulfill_step lc1 mem1 loc from to val released ord lc2.
Proof.
  exploit (@CommitFacts.write_min_spec loc to released);
    try apply WF1; eauto.
  { admit. (* writable *) }
  { admit. (* writable *) }
  { admit. (* released <= m.released *) }
  { admit. (* current <= m.released for acqrel *) }
  { admit. (* closed_capability m.released *) }
  i. des.
  eexists (Local.mk _ _). econs; eauto.
  - econs; eauto.
    rewrite PROMISE1. rewrite Promises.set_o.
    destruct (Loc.eq_dec loc loc); [|congruence].
    destruct (Time.eq_dec to to); [|congruence].
    auto.
Admitted.

Lemma progress_write_step
      lc1 mem1
      loc from to val released ord
      (MAX: max_timestamp loc from mem1)
      (LT: Time.lt from to)
      (WF1: Local.wf lc1 mem1)
      (PROMISE1: lc1.(Local.promises) = Promises.bot):
  exists lc2 mem2,
    Local.write_step lc1 mem1 loc from to val released ord lc2 mem2.
Proof.
  destruct lc1. ss. subst.
  exploit progress_promise_step; eauto. s. i. des.
  assert (promises2 = Promises.set loc to Promises.bot); subst.
  { inv x0. ss. inv PROMISE; eauto. }
  exploit (@progress_fulfill_step (Local.mk commit (Promises.set loc to Promises.bot))); s; eauto.
  { eapply Local.promise_step_future; eauto. }
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
      (PROMISE1: lc1.(Local.promises) = Promises.bot):
  exists lc2,
    Local.fence_step lc1 mem1 ordr ordw lc2.
Proof.
  exploit CommitFacts.read_fence_min_spec; try apply WF1; eauto. i. des.
  exploit CommitFacts.write_fence_min_spec; try apply WF; try apply WF1; eauto. i. des.
  eexists. econs; eauto.
  admit. (* commit.closed *)
Admitted.
