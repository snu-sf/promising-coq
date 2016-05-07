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
      th1 mem1
      loc from to released val
      (MAX: max_timestamp loc from mem1)
      (LT: Time.lt from to)
      (WF1: Local.wf th1 mem1):
  exists promise2 mem2,
    Local.promise_step th1 mem1 loc from to val released (Local.mk th1.(Local.commit) promise2) mem2.
Proof.
  destruct th1. s.
  eexists _, _. econs; memtac.
  - reflexivity.
  - admit. (* commit.wf *)
  - econs; memtac.
    + instantiate (1 := LT). admit. (* memory disjoint *)
    + admit. (* wf snapshot *)
Admitted.

Lemma progress_silent_step
      th1 mem1
      (WF1: Local.wf th1 mem1):
  Local.silent_step th1 mem1 th1.
Proof.
  destruct th1. econs; try apply WF1. reflexivity.
Qed.

Lemma progress_read_step
      th1 mem1
      loc ord ts
      (WF1: Local.wf th1 mem1)
      (PROMISE1: th1.(Local.promise) = Memory.bot)
      (MAX: max_timestamp loc ts mem1):
  exists val released th2,
    Local.read_step th1 mem1 loc ts val released ord th2.
Proof.
  inv MAX. destruct msg.
  eexists _, _, _. splits; eauto. econs; eauto.
  - eapply CommitFacts.read_min_spec; try apply WF1; eauto.
    admit. (* readable *)
  - (* TODO: redundant proof? *)
    unfold CommitFacts.read_min. econs; committac.
    + CommitFacts.condtac; committac.
      * apply Memory.wf_snapshot_join.
        { inv WF1. inv MEMORY. exploit WF; eauto. }
        { eapply Memory.wf_incr_reads; eauto. apply WF1. }
      * eapply Memory.wf_incr_reads; eauto. apply WF1.
    + apply WF1.
    + apply Memory.wf_snapshot_join.
      * inv WF1. inv MEMORY. exploit WF; eauto.
      * apply WF1.
  - rewrite PROMISE1. auto.
Admitted.

Lemma progress_fulfill_step
      th1 mem1
      loc from to val released ord
      (LT: Time.lt from to)
      (WF1: Local.wf th1 mem1)
      (PROMISE1: th1.(Local.promise) = Memory.singleton loc (Message.mk val released) LT):
  exists th2,
    Local.fulfill_step th1 mem1 loc from to val released ord th2.
Proof.
  exploit (@CommitFacts.write_min_spec loc to val released);
    try apply WF1; eauto.
  { admit. (* writable *) }
  { admit. (* released <= m.released *) }
  { admit. (* current <= m.released for acqrel *) }
  { inv WF1. memtac. apply Memory.join_get; memtac.
    rewrite PROMISE1. apply Memory.singleton_get.
  }
  { admit. (* wf_snapshot m.released *) }
  i. des.
  eexists (Local.mk _ Memory.bot). econs; eauto.
  econs; memtac.
  rewrite Memory.join_comm, Memory.bot_join. eauto.
Admitted.

Lemma progress_write_step
      th1 mem1
      loc from to val released ord
      (MAX: max_timestamp loc from mem1)
      (LT: Time.lt from to)
      (WF1: Local.wf th1 mem1)
      (PROMISE1: th1.(Local.promise) = Memory.bot):
  exists th2 mem2,
    Local.write_step th1 mem1 loc from to val released ord th2 mem2.
Proof.
  destruct th1. ss. subst.
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
      th1 mem1
      ordr ordw
      (WF1: Local.wf th1 mem1)
      (PROMISE1: th1.(Local.promise) = Memory.bot):
  exists th2,
    Local.fence_step th1 mem1 ordr ordw th2.
Proof.
  exploit CommitFacts.fence_min_spec; try apply WF1; eauto. i. des.
  eexists. econs; eauto.
Qed.
