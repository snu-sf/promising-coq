Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful5.

Require Import Basic.
Require Import DenseOrder.
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

(* Require ReorderMemory. *)
Require ReorderCommit.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Lemma progress_program_step
      rs1 i1 s1 lc1 sc1 mem1
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      (PROMISES1: lc1.(Local.promises) = Memory.bot):
  exists e th2, <<STEP: Thread.program_step e (Thread.mk lang (State.mk rs1 (i1::s1)) lc1 sc1 mem1) th2>>.
Proof.
  destruct i1.
  - destruct i.
    + esplits. econs 1. econs. econs.
    + esplits. econs 1. econs. econs.
    + hexploit progress_read_step; eauto. i. des.
      esplits. econs 2; eauto. econs. econs.
    + hexploit progress_write_step; eauto.
      { apply Time.incr_spec. }
      { apply Capability.bot_wf. }
      { apply Memory.closed_capability_bot. }
      i. des. esplits. econs 3; eauto. econs. econs.
    + hexploit progress_read_step; eauto. i. des.
      exploit Local.read_step_future; eauto. i.
      hexploit progress_write_step; eauto.
      { apply Time.incr_spec. }
      { inv H. inv MEM1. exploit CLOSED; eauto. i. des. eauto. }
      { inv H. inv MEM1. exploit CLOSED; eauto. i. des. eauto. }
      { inv H. auto. }
      i. des. esplits. econs 4; eauto. econs. econs. apply surjective_pairing.
    + hexploit progress_fence_step; eauto. i. des.
      esplits. econs 5; eauto. econs. econs.
    + hexploit progress_fence_step; eauto. i. des.
      esplits. econs 6; eauto. econs. econs.
  - esplits. econs 1; eauto. econs.
  - esplits. econs 1; eauto. econs.
Grab Existential Variables.
  { auto. }
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
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.read_step lc1 mem0 loc2 ts2 val2 released2 ord2 lc2):
  exists lc1' lc2',
    <<STEP1: Local.read_step lc0 mem0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.read_step lc1' mem0 loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<LOCAL: sim_local lc2' lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto. admit.
  - econs; eauto. admit.
  - s. econs; s.
    + apply ReorderCommit.read_read_commit; auto.
      * apply WF0.
      * eapply MEM0. eauto.
      * eapply MEM0. eauto.
    + apply MemInv.sem_bot.
    + refl.
Admitted.

Lemma reorder_read_promise
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 val2 released2
      lc0 mem0
      lc1
      lc2 mem2
      kind
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.promise_step lc1 mem0 loc2 from2 to2 val2 released2 lc2 mem2 kind):
  exists released1' lc1' lc2',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 val2 released2 lc1' mem2 kind>> /\
    <<STEP2: Local.read_step lc1' mem2 loc1 ts1 val1 released1' ord1 lc2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<REL: Capability.le released1' released1>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
  - admit.
  - econs; s.
    + admit.
    + instantiate (1 := Local.mk _ _). apply MemInv.sem_bot.
    + refl.
Admitted.

Lemma reorder_read_write
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 val2 released2 ord2
      lc0 sc0 mem0
      lc1
      lc2 sc2 mem2
      (LOC: loc1 <> loc2)
      (ORD: Ordering.le Ordering.seqcst ord2 -> Ordering.le Ordering.seqcst ord1 -> False)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.write_step lc1 sc0 mem0 loc2 from2 to2 val2 released2 ord2 lc2 sc2 mem2):
  exists lc1' lc2',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 released2 ord2 lc1' sc2 mem2>> /\
    <<STEP2: Local.read_step lc1' mem2 loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<LOCAL: sim_local lc2' lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto. admit. admit.
  - econs; eauto. admit. admit.
  - s. econs; s.
    + apply ReorderCommit.read_write_commit; auto.
      * apply WF0.
      * eapply MEM0. eauto.
    + apply MemInv.sem_bot.
    + refl.
Admitted.

Lemma reorder_read_fence
      loc1 ts1 val1 released1 ord1
      ordr2 ordw2
      lc0 sc0 mem0
      lc1
      lc2 sc2
      (ORD1: Ordering.le Ordering.relaxed ord1)
      (ORDR2: Ordering.le ordr2 Ordering.relaxed)
      (ORDW2: Ordering.le ordw2 Ordering.acqrel)
      (RLX: Ordering.le Ordering.relaxed ordw2 -> Ordering.le ord1 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.fence_step lc1 sc0 mem0 ordr2 ordw2 lc2 sc2):
  exists lc1' lc2' sc2',
    <<STEP1: Local.fence_step lc0 sc0 mem0 ordr2 ordw2 lc1' sc2'>> /\
    <<STEP2: Local.read_step lc1' mem0 loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<SC: TimeMap.le sc2' sc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
  - econs; eauto. admit.
  - s. econs; s.
    + etrans.
      * apply ReorderCommit.read_write_fence_commit; auto.
        { eapply CommitFacts.read_fence_future; apply WF0. }
        { eapply MEM0. eauto. }
      * admit.
    + apply MemInv.sem_bot.
    + refl.
  - admit.
Admitted.

Lemma reorder_write_read
      loc1 from1 to1 val1 released1 ord1
      loc2 ts2 val2 released2 ord2
      lc0 sc0 mem0
      lc1 sc1 mem1
      lc2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.write_step lc0 sc0 mem0 loc1 from1 to1 val1 released1 ord1 lc1 sc1 mem1)
      (STEP2: Local.read_step lc1 mem1 loc2 ts2 val2 released2 ord2 lc2):
  exists lc1' lc2',
    <<STEP1: Local.read_step lc0 mem0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.write_step lc1' sc0 mem0 loc1 from1 to1 val1 released1 ord1 lc2' sc1 mem1>> /\
    <<LOCAL: sim_local lc2' lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto. admit. admit.
  - econs; eauto. admit. admit.
  - s. econs; s.
    + apply ReorderCommit.write_read_commit; auto.
      * apply WF0.
      * admit.
    + apply MemInv.sem_bot.
    + refl.
Admitted.

Lemma reorder_write_promise
      loc1 from1 to1 val1 released1 ord1
      loc2 from2 to2 val2 released2
      lc0 sc0 mem0
      lc1 sc1 mem1
      lc2 mem2
      kind
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.write_step lc0 sc0 mem0 loc1 from1 to1 val1 released1 ord1 lc1 sc1 mem1)
      (STEP2: Local.promise_step lc1 mem0 loc2 from2 to2 val2 released2 lc2 mem2 kind):
  exists lc1' lc2' mem1',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 val2 released2 lc1' mem2 kind>> /\
    <<STEP2: Local.write_step lc1' sc0 mem1' loc1 from1 to1 val1 released1 ord1 lc2' sc1 mem2>> /\
    <<LOCAL: sim_local lc2' lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - admit.
  - admit.
  - admit.
Admitted.

Lemma reorder_write_write
      loc1 from1 to1 val1 released1 ord1
      loc2 from2 to2 val2 released2 ord2
      lc0 sc0 mem0
      lc1 sc1 mem1
      lc2 sc2 mem2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.write_step lc0 sc0 mem0 loc1 from1 to1 val1 released1 ord1 lc1 sc1 mem1)
      (STEP2: Local.write_step lc1 sc1 mem1 loc2 from2 to2 val2 released2 ord2 lc2 sc2 mem2):
  exists lc1' lc2' sc1' sc2' mem1',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 released2 ord2 lc1' sc1' mem1'>> /\
    <<STEP2: Local.write_step lc1' sc1' mem1' loc1 from1 to1 val1 released1 ord1 lc2' sc2' mem2>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<SC: TimeMap.le sc2' sc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
    + admit.
    + admit.
    + i. splits; eauto. admit.
  - econs; eauto.
    + admit.
    + admit.
  - s. econs; s.
    + apply ReorderCommit.write_write_commit; auto. apply WF0.
    + apply MemInv.sem_bot.
    + refl.
  - eapply ReorderCommit.write_write_sc; eauto.
Admitted.

Lemma reorder_fence_promise
      ordr1 ordw1
      loc2 from2 to2 val2 released2
      lc0 sc0 mem0
      lc1 sc1
      lc2 sc2 mem2
      kind
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.fence_step lc0 sc0 mem0 ordr1 ordw1 lc1 sc1)
      (STEP2: Local.promise_step lc1 mem0 loc2 from2 to2 val2 released2 lc2 mem2 kind):
  exists lc1' lc2' sc1' sc2',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 val2 released2 lc1' mem2 kind>> /\
    <<STEP2: Local.fence_step lc1' sc1' mem2 ordr1 ordw1 lc2' sc2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<SC: TimeMap.le sc2' sc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
  - econs; eauto. i. destruct ordw1; inv ORDW1; inv H.
  - s. econs; s.
    + admit.
    + apply MemInv.sem_bot.
    + refl.
Admitted.

Lemma reorder_fence_write
      ordr1 ordw1
      loc2 from2 to2 val2 releasedm2 ord2
      lc0 sc0 mem0
      lc1 sc1
      lc2 sc2 mem2
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.fence_step lc0 sc0 mem0 ordr1 ordw1 lc1 sc1)
      (STEP2: Local.write_step lc1 sc1 mem0 loc2 from2 to2 val2 releasedm2 ord2 lc2 sc2 mem2):
  exists lc1' lc2' sc1' sc2',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 ord2 lc1' sc1' mem2>> /\
    <<STEP2: Local.fence_step lc1' sc1' mem2 ordr1 ordw1 lc2' sc2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<SC: TimeMap.le sc2' sc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
    + admit.
    + admit.
  - econs; eauto.
  - s. econs; s.
    + etrans.
      * admit.
      * admit.
    + admit.
    + admit.
  - etrans.
    + admit.
    + eapply ReorderCommit.write_fence_write_sc; eauto.
      eapply CommitFacts.read_fence_future; apply WF0.
Admitted.
