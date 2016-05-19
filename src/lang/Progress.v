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
      (PROMISE: lc1.(Local.promise) = Memory.bot):
  lc2.(Local.promise) = Memory.bot.
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
      (WF: Memory.wf mem):
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
  exists promise2 mem2,
    Local.promise_step lc1 mem1 loc from to val released (Local.mk lc1.(Local.commit) promise2) mem2.
Proof.
  destruct lc1. s.
  eexists _, _. econs; memtac.
  - reflexivity.
  - admit. (* commit.wf *)
  - econs; memtac.
    + instantiate (1 := LT). admit. (* memory disjoint *)
    + admit. (* wf capability *)
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
      (PROMISE1: lc1.(Local.promise) = Memory.bot)
      (MAX: max_timestamp loc ts mem1):
  exists val released lc2,
    Local.read_step lc1 mem1 loc ts val released ord lc2.
Proof.
  inv MAX. destruct msg.
  eexists _, _, _. econs; eauto.
  - eapply CommitFacts.read_min_spec; try apply WF1; eauto.
    + admit. (* readable *)
    + admit. (* readable *)
  - (* TODO: redundant proof? *)
    unfold CommitFacts.read_min. econs; committac; try apply WF1.
    + unfold Capability.join_if. condtac; committac; try apply WF1.
      inv WF1. inv MEMORY. exploit WF; eauto.
    + inv WF1. inv MEMORY. exploit WF; eauto.
  - rewrite PROMISE1. auto.
Admitted.

Lemma progress_fulfill_step
      lc1 mem1
      loc from to val released ord
      (LT: Time.lt from to)
      (WF1: Local.wf lc1 mem1)
      (PROMISE1: lc1.(Local.promise) = Memory.singleton loc (Message.mk val released) LT):
  exists lc2,
    Local.fulfill_step lc1 mem1 loc from to val released ord lc2.
Proof.
  exploit (@CommitFacts.write_min_spec loc to val released);
    try apply WF1; eauto.
  { admit. (* writable *) }
  { admit. (* writable *) }
  { admit. (* released <= m.released *) }
  { admit. (* current <= m.released for acqrel *) }
  { inv WF1. memtac. apply Memory.join_get; memtac.
    rewrite PROMISE1. apply Memory.singleton_get.
  }
  { admit. (* wf_capability m.released *) }
  i. des.
  eexists (Local.mk _ Memory.bot). econs; eauto.
  econs; memtac.
  rewrite Memory.join_comm, Memory.bot_join. eauto.
Admitted.

Lemma progress_write_step
      lc1 mem1
      loc from to val released ord
      (MAX: max_timestamp loc from mem1)
      (LT: Time.lt from to)
      (WF1: Local.wf lc1 mem1)
      (PROMISE1: lc1.(Local.promise) = Memory.bot):
  exists lc2 mem2,
    Local.write_step lc1 mem1 loc from to val released ord lc2 mem2.
Proof.
  destruct lc1. ss. subst.
  exploit progress_promise_step; eauto. s. i. des.
  assert (promise2 = Memory.singleton loc (Message.mk val released) LT).
  { inv x0. inv MEMORY; ss.
    - rewrite Memory.join_comm, Memory.bot_join.
      f_equal. apply proof_irrelevance.
    - admit. (* invert [bot = join _ singleton] *)
  }
  exploit (@progress_fulfill_step (Local.mk commit promise2)); eauto.
  { eapply Local.promise_step_future; eauto. }
  s. i. des.
  eexists _, _. econs 2; eauto.
Admitted.

Lemma progress_fence_step
      lc1 mem1
      ordr ordw
      (WF1: Local.wf lc1 mem1)
      (PROMISE1: lc1.(Local.promise) = Memory.bot):
  exists lc2,
    Local.fence_step lc1 mem1 ordr ordw lc2.
Proof.
  exploit CommitFacts.read_fence_min_spec; try apply WF1; eauto. i. des.
  exploit CommitFacts.write_fence_min_spec; try apply WF1; eauto. i. des.
  eexists. econs; eauto.
Qed.
