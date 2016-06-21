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

Require ReorderMemory.
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
      { apply Memory.closed_capability_bot. apply MEM1. }
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
  - econs; eauto.
    eapply CommitFacts.readable_mon; try apply READABLE0; eauto; try refl.
    apply CommitFacts.read_commit_incr.
  - econs; eauto. s. unfold Commit.read_commit.
    econs; repeat (try condtac; try splits; aggrtac; eauto; try apply READABLE;
                   unfold TimeMap.singleton, LocFun.add in *).
  - s. econs; s.
    + apply ReorderCommit.read_read_commit; auto.
      * apply WF0.
      * eapply MEM0. eauto.
      * eapply MEM0. eauto.
    + apply MemInv.sem_bot.
    + refl.
Qed.

Lemma reorder_read_promise
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 val2 released2 kind2
      lc0 mem0
      lc1
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.promise_step lc1 mem0 loc2 from2 to2 val2 released2 lc2 mem2 kind2):
  exists lc1' lc2',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 val2 released2 lc1' mem2 kind2>> /\
    <<STEP2: Local.read_step lc1' mem2 loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<LOCAL: sim_local lc2' lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit Memory.promise_get1; eauto. i. des.
  esplits.
  - econs; eauto.
  - econs; eauto.
  - econs; s.
    + refl.
    + apply MemInv.sem_bot.
    + refl.
Qed.

Lemma reorder_read_write
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 val2 releasedm2 released2 ord2
      lc0 sc0 mem0
      lc1
      lc2 sc2 mem2
      kind
      (LOC: loc1 <> loc2)
      (ORD: Ordering.le Ordering.seqcst ord2 -> Ordering.le Ordering.seqcst ord1 -> False)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.write_step lc1 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind):
  exists mem2' lc1' lc2',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2 mem2' kind>> /\
    <<STEP2: Local.read_step lc1' mem2' loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<MEM: Memory.sim mem2 mem2'>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
    + admit. (* eq released *)
    + eapply CommitFacts.writable_mon; eauto; try refl.
      apply CommitFacts.read_commit_incr.
  - econs; eauto.
    + admit. (* Memory.write_get *)
    + s. unfold Commit.write_commit.
      econs; repeat (try condtac; try splits; aggrtac; eauto; try apply READABLE;
                     unfold TimeMap.singleton, LocFun.add in *).
      * exfalso. apply ORD; auto.
      * exfalso. apply ORD; auto.
  - s. econs; s.
    + apply ReorderCommit.read_write_commit; auto.
      * apply WF0.
      * eapply MEM0. eauto.
    + apply MemInv.sem_bot.
    + refl.
  - admit. (* Memory.sim sim2 sim2' *)
Admitted.

Lemma reorder_read_update
      loc1 ts1 val1 released1 ord1
      loc2 ts2 val2 released2 ord2
      from3 to3 val3 released3 ord3
      lc0 sc0 mem0
      lc1
      lc2
      lc3 sc3 mem3
      kind
      (LOC: loc1 <> loc2)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (ORD3: Ordering.le Ordering.seqcst ord3 -> Ordering.le Ordering.seqcst ord1 -> False)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.read_step lc1 mem0 loc2 ts2 val2 released2 ord2 lc2)
      (STEP3: Local.write_step lc2 sc0 mem0 loc2 from3 to3 val3 released2 released3 ord3 lc3 sc3 mem3 kind):
  exists released3' sc3' mem3' lc1' lc2' lc3',
    <<STEP1: Local.read_step lc0 mem0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.write_step lc1' sc0 mem0 loc2 from3 to3 val3 released2 released3' ord3 lc2' sc3' mem3' kind>> /\
    <<STEP3: Local.read_step lc2' mem3' loc1 ts1 val1 released1 ord1 lc3'>> /\
    <<LOCAL: sim_local lc3' lc3>> /\
    <<RELEASED: Capability.le released3' released3>> /\
    <<SC: TimeMap.le sc3' sc3>> /\
    <<MEM: Memory.sim mem3 mem3'>>.
Proof.
  exploit Local.read_step_future; try apply STEP1; eauto. i. des.
  exploit Local.read_step_future; try apply STEP2; eauto. i. des.
  exploit reorder_read_read; try apply STEP1; try apply STEP2; eauto. i. des.
  exploit Local.read_step_future; try apply STEP0; eauto. i. des.
  exploit Local.read_step_future; try apply STEP4; eauto. i. des.
  exploit sim_local_write; try apply STEP3; eauto; try refl.
  { inv STEP0. eapply MEM0; eauto. }
  i. des.
  exploit reorder_read_write; try apply STEP4; try apply STEP_SRC; eauto. i. des.
  esplits; eauto.
  - etrans; eauto.
  - etrans; eauto.
Qed.

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
  - econs; eauto. s.
    unfold Commit.write_fence_commit, Commit.read_fence_commit, Commit.write_fence_sc.
    econs; repeat (try condtac; try splits; aggrtac; try apply READABLE).
  - s. econs; s.
    + etrans.
      * apply ReorderCommit.read_write_fence_commit; auto.
        { eapply CommitFacts.read_fence_future; apply WF0. }
        { eapply MEM0. eauto. }
      * apply CommitFacts.write_fence_commit_mon; try refl.
        apply ReorderCommit.read_read_fence_commit; try apply WF0; auto.
        eapply MEM0. eauto.
    + apply MemInv.sem_bot.
    + refl.
  - unfold Commit.write_fence_sc, Commit.read_fence_commit.
    repeat condtac; aggrtac.
Qed.

Lemma reorder_write_read
      loc1 from1 to1 val1 releasedm1 released1 ord1 kind1
      loc2 ts2 val2 released2 ord2
      lc0 sc0 mem0
      lc1 sc1 mem1
      lc2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.write_step lc0 sc0 mem0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 sc1 mem1 kind1)
      (STEP2: Local.read_step lc1 mem1 loc2 ts2 val2 released2 ord2 lc2):
  exists lc1' lc2',
    <<STEP1: Local.read_step lc0 mem0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.write_step lc1' sc0 mem0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc2' sc1 mem1 kind1>> /\
    <<LOCAL: sim_local lc2' lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit Memory.write_future; try apply WF0; eauto. i. des.
  esplits.
  - econs; eauto.
    + admit. (* memory.write_get_inv *)
    + eapply CommitFacts.readable_mon; try apply READABLE; eauto; try refl.
      apply CommitFacts.write_commit_incr.
  - econs; eauto.
    + s. repeat condtac; aggrtac.
    + s. unfold Commit.read_commit.
      econs; repeat (try condtac; try splits; aggrtac; eauto; try apply WRITABLE;
                     unfold TimeMap.singleton, LocFun.add in *);
        (try by inv WRITABLE; eapply TimeFacts.le_lt_lt; eauto; aggrtac).
  - s. econs; s.
    + apply ReorderCommit.write_read_commit; auto.
      * apply WF0.
      * eapply CLOSED2. eauto.
    + apply MemInv.sem_bot.
    + refl.
Admitted.

Lemma reorder_write_promise
      loc1 from1 to1 val1 releasedm1 released1 ord1 kind1
      loc2 from2 to2 val2 released2 kind2
      lc0 sc0 mem0
      lc1 sc1 mem1
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.write_step lc0 sc0 mem0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 sc1 mem1 kind1)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 val2 released2 lc2 mem2 kind2):
  exists lc1' lc2' mem1',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 val2 released2 lc1' mem1' kind2>> /\
    <<STEP2: Local.write_step lc1' sc0 mem1' loc1 from1 to1 val1 releasedm1 released1 ord1 lc2' sc1 mem2 kind1>> /\
    <<LOCAL: sim_local lc2' lc2>>.
Proof.
  inv STEP1. inv STEP2. ss. inv WRITE.
  exploit Memory.promise_future; try apply WF0; eauto. i. des.
  exploit ReorderMemory.remove_promise; eauto. i. des.
  esplits.
  - admit. (* promise step *)
  - admit. (* write step *)
  - admit. (* sim_local *)
Admitted.

Lemma reorder_write_write
      loc1 from1 to1 val1 releasedm1 released1 ord1 kind1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2
      lc0 sc0 mem0
      lc1 sc1 mem1
      lc2 sc2 mem2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.write_step lc0 sc0 mem0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 sc1 mem1 kind1)
      (STEP2: Local.write_step lc1 sc1 mem1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2):
  exists lc1' lc2' sc1' sc2' mem1',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc1' mem1' kind2>> /\
    <<STEP2: Local.write_step lc1' sc1' mem1' loc1 from1 to1 val1 releasedm1 released1 ord1 lc2' sc2' mem2 kind1>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<SC: TimeMap.le sc2' sc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
    + s. repeat (condtac; aggrtac).
      * admit. (* eq released *)
      * admit. (* eq released *)
    + eapply CommitFacts.writable_mon; eauto; try refl.
      * apply CommitFacts.write_commit_incr.
      * apply CommitFacts.write_sc_incr.
    + admit. (* Memory.write *)
    + i. exploit RELEASE0; eauto. i. des. splits; auto.
      admit. (* promise = bot? *)
  - econs; eauto.
    + admit. (* eq released *)
    + s. unfold Commit.write_commit, Commit.write_sc.
      econs; repeat (try condtac; try splits; aggrtac; eauto; try apply WRITABLE;
                     unfold TimeMap.singleton, LocFun.add in *);
        inv WRITABLE; eapply TimeFacts.le_lt_lt; eauto; aggrtac.
    + admit. (* Memory.write *)
  - s. econs; s.
    + apply ReorderCommit.write_write_commit; auto. apply WF0.
    + apply MemInv.sem_bot.
    + refl.
  - eapply ReorderCommit.write_write_sc; eauto.
Admitted.

Lemma reorder_write_update
      loc1 from1 to1 val1 releasedm1 released1 ord1 kind1
      loc2 ts2 val2 released2 ord2
      from3 to3 val3 released3 ord3 kind3
      lc0 sc0 mem0
      lc1 sc1 mem1
      lc2
      lc3 sc3 mem3
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.write_step lc0 sc0 mem0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 sc1 mem1 kind1)
      (STEP2: Local.read_step lc1 mem1 loc2 ts2 val2 released2 ord2 lc2)
      (STEP3: Local.write_step lc2 sc1 mem1 loc2 from3 to3 val3 released2 released3 ord3 lc3 sc3 mem3 kind3):
  exists released3' lc1' lc2' lc3' sc2' sc3' mem2' mem3',
    <<STEP1: Local.read_step lc0 mem0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.write_step lc1' sc0 mem0 loc2 from3 to3 val3 released2 released3' ord3 lc2' sc2' mem2' kind3>> /\
    <<STEP3: Local.write_step lc2' sc2' mem2' loc1 from1 to1 val1 releasedm1 released1 ord1 lc3' sc3' mem3' kind1>> /\
    <<LOCAL: sim_local lc3' lc3>> /\
    <<RELEASED: Capability.le released3' released3>> /\
    <<SC: TimeMap.le sc3' sc3>> /\
    <<MEM: Memory.sim mem3 mem3'>>.
Proof.
  exploit Local.write_step_future; try apply STEP1; eauto. i. des.
  exploit Local.read_step_future; try apply STEP2; eauto. i. des.
  exploit reorder_write_read; try apply STEP1; try apply STEP2; eauto. i. des.
  exploit Local.read_step_future; try apply STEP0; eauto. i. des.
  exploit Local.write_step_future; try apply STEP4; try refl; eauto. i. des.
  exploit sim_local_write; try apply STEP3; try apply LOCAL; try refl; eauto.
  { inv STEP0. eapply MEM0; eauto. }
  i. des.
  exploit reorder_write_write; try apply STEP4; try apply STEP_SRC; eauto. i. des.
  esplits; eauto.
  - etrans; eauto.
  - etrans; eauto.
Qed.

Lemma reorder_update_read
      loc1 ts1 val1 released1 ord1
      from2 to2 val2 released2 ord2 kind2
      loc3 ts3 val3 released3 ord3
      lc0 sc0 mem0
      lc1
      lc2 sc2 mem2
      lc3
      (LOC: loc1 <> loc3)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (ORD3: Ordering.le ord3 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.write_step lc1 sc0 mem0 loc1 from2 to2 val2 released1 released2 ord2 lc2 sc2 mem2 kind2)
      (STEP3: Local.read_step lc2 mem2 loc3 ts3 val3 released3 ord3 lc3):
  exists released2' lc1' lc2' lc3' sc2' mem2',
    <<STEP1: Local.read_step lc0 mem0 loc3 ts3 val3 released3 ord3 lc1'>> /\
    <<STEP2: Local.read_step lc1' mem0 loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<STEP3: Local.write_step lc2' sc0 mem0 loc1 from2 to2 val2 released1 released2' ord2 lc3' sc2' mem2' kind2>> /\
    <<LOCAL: sim_local lc3' lc3>> /\
    <<RELEASED: Capability.le released2' released2>> /\
    <<SC: TimeMap.le sc2' sc2>> /\
    <<MEM: Memory.sim mem2 mem2'>>.
Proof.
  exploit Local.read_step_future; try apply STEP1; eauto. i. des.
  exploit Local.write_step_future; try apply STEP2; eauto. i. des.
  exploit reorder_write_read; try apply STEP2; try apply STEP3; eauto. i. des.
  exploit Local.read_step_future; try apply STEP0; eauto. i. des.
  exploit reorder_read_read; try apply STEP1; try apply STEP0; eauto. i. des.
  exploit Local.read_step_future; try apply STEP5; eauto. i. des.
  exploit Local.read_step_future; try apply STEP6; eauto. i. des.
  exploit sim_local_write; try apply STEP4; try apply LOCAL0; eauto; try refl.
  { inv STEP6. eapply MEM0; eauto. }
  i. des.
  esplits; eauto. etrans; eauto.
Qed.

Lemma reorder_update_write
      loc1 ts1 val1 released1 ord1
      from2 to2 val2 released2 ord2 kind2
      loc3 from3 to3 val3 releasedm3 released3 ord3 kind3
      lc0 sc0 mem0
      lc1
      lc2 sc2 mem2
      lc3 sc3 mem3
      (LOC: loc1 <> loc3)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (ORD3: Ordering.le Ordering.seqcst ord3 -> Ordering.le Ordering.seqcst ord1 -> False)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.write_step lc1 sc0 mem0 loc1 from2 to2 val2 released1 released2 ord2 lc2 sc2 mem2 kind2)
      (STEP3: Local.write_step lc2 sc2 mem2 loc3 from3 to3 val3 releasedm3 released3 ord3 lc3 sc3 mem3 kind3):
  exists released2' lc1' lc2' lc3' sc1' sc3' mem1' mem3',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc3 from3 to3 val3 releasedm3 released3 ord3 lc1' sc1' mem1' kind3>> /\
    <<STEP2: Local.read_step lc1' mem1' loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<STEP3: Local.write_step lc2' sc1' mem1' loc1 from2 to2 val2 released1 released2' ord2 lc3' sc3' mem3' kind2>> /\
    <<LOCAL: sim_local lc3' lc3>> /\
    <<RELEASED: Capability.le released2' released2>> /\
    <<SC: TimeMap.le sc3' sc3>> /\
    <<MEM: Memory.sim mem3 mem3'>>.
Proof.
  exploit Local.read_step_future; try apply STEP1; eauto. i. des.
  exploit Local.write_step_future; try apply STEP2; eauto. i. des.
  exploit reorder_write_write; try apply STEP2; try apply STEP3; eauto. i. des.
  exploit Local.write_step_future; try apply STEP0; eauto. i. des.
  exploit reorder_read_write; try apply STEP1; try apply STEP0; eauto. i. des.
  exploit Local.write_step_future; try apply STEP5; eauto. i. des.
  exploit Local.read_step_future; try apply STEP6; eauto. i. des.
  exploit sim_local_write; try apply STEP4; try apply LOCAL0; try apply x1; try refl; eauto.
  { inv STEP6. eapply CLOSED1; eauto. }
  i. des.
  esplits; eauto.
  - etrans; eauto.
  - etrans; eauto.
Qed.

Lemma reorder_update_update
      loc1 ts1 val1 released1 ord1
      from2 to2 val2 released2 ord2 kind2
      loc3 ts3 val3 released3 ord3
      from4 to4 val4 released4 ord4 kind4
      lc0 sc0 mem0
      lc1
      lc2 sc2 mem2
      lc3
      lc4 sc4 mem4
      (LOC: loc1 <> loc3)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (ORD3: Ordering.le ord3 Ordering.relaxed)
      (ORD4: Ordering.le Ordering.seqcst ord4 -> Ordering.le Ordering.seqcst ord1 -> False)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.write_step lc1 sc0 mem0 loc1 from2 to2 val2 released1 released2 ord2 lc2 sc2 mem2 kind2)
      (STEP3: Local.read_step lc2 mem2 loc3 ts3 val3 released3 ord3 lc3)
      (STEP4: Local.write_step lc3 sc2 mem2 loc3 from4 to4 val4 released3 released4 ord4 lc4 sc4 mem4 kind4):
  exists released2' released4' lc1' lc2' lc3' lc4' sc2' sc4' mem2' mem4',
    <<STEP1: Local.read_step lc0 mem0 loc3 ts3 val3 released3 ord3 lc1'>> /\
    <<STEP2: Local.write_step lc1' sc0 mem0 loc3 from4 to4 val4 released3 released4' ord4 lc2' sc2' mem2' kind4>> /\
    <<STEP3: Local.read_step lc2' mem2' loc1 ts1 val1 released1 ord1 lc3'>> /\
    <<STEP4: Local.write_step lc3' sc2' mem2' loc1 from2 to2 val2 released1 released2' ord2 lc4' sc4' mem4' kind2>> /\
    <<LOCAL: sim_local lc4' lc4>> /\
    <<RELEASED2: Capability.le released2' released2>> /\
    <<RELEASED4: Capability.le released4' released4>> /\
    <<SC: TimeMap.le sc4' sc4>> /\
    <<MEM: Memory.sim mem4 mem4'>>.
Proof.
  exploit Local.read_step_future; try apply STEP1; eauto. i. des.
  exploit Local.write_step_future; try apply STEP2; eauto. i. des.
  exploit Local.read_step_future; try apply STEP3; eauto. i. des.
  exploit reorder_update_read; try apply STEP2; try apply STEP1; try apply STEP3; eauto. i. des.
  exploit Local.read_step_future; try apply STEP0; eauto. i. des.
  exploit Local.read_step_future; try apply STEP5; eauto. i. des.
  exploit Local.write_step_future; try apply STEP6; eauto. i. des.
  exploit sim_local_write; try apply STEP4; try apply LOCAL; try apply WF1; eauto; try refl.
  { inv STEP0. eapply MEM0; eauto. }
  i. des.
  hexploit reorder_update_write; try apply STEP5; try apply STEP6; try apply STEP_SRC; eauto. i. des.
  esplits; eauto.
  - etrans; eauto.
  - etrans; eauto.
  - etrans; eauto.
  - etrans; eauto.
Qed.

Lemma reorder_fence_promise
      ordr1 ordw1
      loc2 from2 to2 val2 released2
      lc0 sc0 mem0
      lc1 sc1
      lc2 mem2
      kind
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.fence_step lc0 sc0 mem0 ordr1 ordw1 lc1 sc1)
      (STEP2: Local.promise_step lc1 mem0 loc2 from2 to2 val2 released2 lc2 mem2 kind):
  exists lc1',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 val2 released2 lc1' mem2 kind>> /\
    <<STEP2: Local.fence_step lc1' sc0 mem2 ordr1 ordw1 lc2 sc1>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
  - econs; eauto. i. destruct ordw1; inv ORDW1; inv H.
Qed.

Lemma reorder_fence_write
      ordr1 ordw1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2
      lc0 sc0 mem0
      lc1 sc1
      lc2 sc2 mem2
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.fence_step lc0 sc0 mem0 ordr1 ordw1 lc1 sc1)
      (STEP2: Local.write_step lc1 sc1 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2):
  exists lc1' lc2' sc1' sc2',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc1' mem2 kind2>> /\
    <<STEP2: Local.fence_step lc1' sc1' mem2 ordr1 ordw1 lc2' sc2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<SC: TimeMap.le sc2' sc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
    + admit. (* eq released *)
    + eapply CommitFacts.writable_mon; eauto; try refl.
      * etrans.
        { apply CommitFacts.read_fence_commit_incr. apply WF0. }
        { apply CommitFacts.write_fence_commit_incr. }
      * apply CommitFacts.write_fence_sc_incr.
  - econs; ss. admit. (* promises bot *)
  - econs; ss. etrans; [|etrans].
    + apply CommitFacts.write_fence_commit_mon; [|refl|refl].
      apply ReorderCommit.read_fence_write_commit; auto. apply WF0.
    + apply ReorderCommit.write_fence_write_commit; auto.
      eapply CommitFacts.read_fence_future; apply WF0.
    + apply CommitFacts.write_commit_mon; try refl.
      * apply CommitFacts.write_fence_sc_incr.
      * exploit CommitFacts.read_fence_future; try apply WF0; eauto. i. des.
        eapply CommitFacts.write_fence_future; eauto.
  - etrans.
    + apply CommitFacts.write_fence_sc_mon; [|refl|refl].
      apply ReorderCommit.read_fence_write_commit; auto. apply WF0.
    + eapply ReorderCommit.write_fence_write_sc; eauto.
      eapply CommitFacts.read_fence_future; apply WF0.
Admitted.
