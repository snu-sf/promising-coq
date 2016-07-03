Require Import RelationClasses.
Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful9.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Commit.
Require Import Thread.
Require Import Configuration.

Require Import FulfillStep.
Require Import SimMemory.
Require Import SimPromises.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive sim_local (lc_src lc_tgt:Local.t): Prop :=
| sim_local_intro
    (COMMIT: Commit.le lc_src.(Local.commit) lc_tgt.(Local.commit))
    (PROMISES: SimPromises.sem SimPromises.bot lc_src.(Local.promises) lc_tgt.(Local.promises))
.

Program Instance sim_local_PreOrder: PreOrder sim_local.
Next Obligation.
  econs; try refl. apply SimPromises.sem_bot.
Qed.
Next Obligation.
  ii. inv H. inv H0. econs; try etrans; eauto.
  apply SimPromises.sem_bot_inv in PROMISES; auto.
  apply SimPromises.sem_bot_inv in PROMISES0; auto.
  rewrite PROMISES, PROMISES0. apply SimPromises.sem_bot.
Qed.

Lemma sim_local_cell_bot
      loc lc_src lc_tgt
      (SIM: sim_local lc_src lc_tgt)
      (BOT: lc_tgt.(Local.promises) loc = Cell.bot):
  lc_src.(Local.promises) loc = Cell.bot.
Proof.
  inv SIM. eapply SimPromises.sem_bot_inv in PROMISES; auto. rewrite PROMISES. auto.
Qed.

Lemma sim_local_memory_bot
      lc_src lc_tgt
      (SIM: sim_local lc_src lc_tgt)
      (BOT: lc_tgt.(Local.promises) = Memory.bot):
  lc_src.(Local.promises) = Memory.bot.
Proof.
  inv SIM. eapply SimPromises.sem_bot_inv in PROMISES; auto. rewrite PROMISES. auto.
Qed.

Lemma sim_local_future
      inv
      lc_src mem1_src mem2_src
      lc_tgt mem1_tgt
      (INV1: SimPromises.sem inv lc_src.(Local.promises) lc_tgt.(Local.promises))
      (MEM1: sim_memory mem1_src mem1_tgt)
      (FUTURE_SRC: Memory.future mem1_src mem2_src)
      (WF1_SRC: Local.wf lc_src mem1_src)
      (WF1_TGT: Local.wf lc_tgt mem1_tgt)
      (WF2_SRC: Local.wf lc_src mem2_src)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists mem2_tgt,
    <<MEM2: sim_memory mem2_src mem2_tgt>> /\
    <<FUTURE_TGT: Memory.future mem1_tgt mem2_tgt>> /\
    <<WF2_TGT: Local.wf lc_tgt mem2_tgt>> /\
    <<MEM2_TGT: Memory.closed mem2_tgt>>.
Proof.
  exploit SimPromises.future; eauto.
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  { apply WF2_SRC. }
  i. des.
  esplits; eauto.
  econs; eauto.
  - apply WF1_TGT.
  - eapply Commit.future_closed; eauto. apply WF1_TGT.
  - eapply Memory.future_closed; eauto.
Qed.

Lemma sim_local_promise
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt mem2_tgt
      loc from to val released kind
      (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to val released lc2_tgt mem2_tgt kind)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src mem2_src,
    <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to val released lc2_src mem2_src kind>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit SimPromises.promise; eauto.
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  i. des.
  exploit sim_memory_closed_capability; eauto. i.
  exploit Memory.promise_future; try apply PROMISE_SRC; eauto.
  { apply WF1_SRC. }
  i. des.
  esplits; eauto.
  - econs; eauto.
  - econs; eauto.
Qed.

Lemma sim_local_read
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt
      loc ts val released_tgt ord_src ord_tgt
      (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc ts val released_tgt ord_tgt lc2_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt)
      (ORD: Ordering.le ord_src ord_tgt):
  exists released_src lc2_src,
    <<REL: Capability.le released_src released_tgt>> /\
    <<STEP_SRC: Local.read_step lc1_src mem1_src loc ts val released_src ord_src lc2_src>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit sim_memory_get; try apply MEM1; eauto. i. des.
  esplits; eauto.
  - econs; eauto. eapply CommitFacts.readable_mon; eauto.
  - econs; eauto. s. apply CommitFacts.read_commit_mon; auto.
    + apply WF1_TGT.
    + eapply MEM1_TGT. eauto.
Qed.

Lemma sim_local_fulfill
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      loc from to val releasedm_src releasedm_tgt released ord_src ord_tgt
      (RELM_LE: Capability.le releasedm_src releasedm_tgt)
      (RELM_WF: Capability.wf releasedm_src)
      (RELM_CLOSED: Memory.closed_capability releasedm_src mem1_src)
      (WF_RELM_TGT: Capability.wf releasedm_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (STEP_TGT: fulfill_step lc1_tgt sc1_tgt loc from to val releasedm_tgt released ord_tgt lc2_tgt sc2_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src sc2_src,
    <<STEP_SRC: fulfill_step lc1_src sc1_src loc from to val releasedm_src released ord_src lc2_src sc2_src>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>>.
Proof.
  inv STEP_TGT.
  assert (RELT_LE:
   Capability.le
     (if Ordering.le Ordering.relaxed ord_src
      then Capability.join releasedm_src
        (Commit.rel
           (Commit.write_commit (Local.commit lc1_src) sc1_src loc to
              ord_src) loc)
      else Capability.bot)
     (if Ordering.le Ordering.relaxed ord_tgt
      then Capability.join releasedm_tgt
        (Commit.rel
           (Commit.write_commit (Local.commit lc1_tgt) sc1_tgt loc to
              ord_tgt) loc)
      else Capability.bot)).
  { repeat (try condtac; aggrtac).
    - rewrite <- Capability.join_r.
      rewrite <- ? Capability.join_l.
      apply LOCAL1.
    - rewrite <- Capability.join_r.
      rewrite <- ? Capability.join_l.
      apply LOCAL1.
    - apply WF1_TGT.
    - econs; aggrtac.
    - rewrite <- Capability.join_r.
      rewrite <- Capability.join_l.
      rewrite <- Capability.join_l.
      etrans; [|apply LOCAL1].
      apply WF1_SRC.
    - rewrite <- Capability.join_r.
      rewrite <- Capability.join_l.
      rewrite <- Capability.join_l.
      etrans; [|apply LOCAL1].
      apply WF1_SRC.
    - rewrite <- Capability.join_r.
      apply LOCAL1.
  }
  assert (RELT_WF:
   Capability.wf
     (Capability.join releasedm_src
        (Commit.rel
           (Commit.write_commit (Local.commit lc1_src) sc1_src loc to
              ord_src) loc))).
  { repeat (try condtac; committac; try apply WF1_SRC). }
  exploit SimPromises.remove; try exact REMOVE;
    try exact MEM1; try apply LOCAL1; eauto.
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  i. des. esplits.
  - econs; eauto.
    + etrans; eauto.
    + eapply CommitFacts.writable_mon; eauto. apply LOCAL1.
  - econs; eauto. s. apply CommitFacts.write_commit_mon; auto.
    + apply LOCAL1.
    + apply WF1_TGT.
  - apply CommitFacts.write_sc_mon; auto.
Qed.

Lemma sim_local_write
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt mem2_tgt
      loc from to val releasedm_src releasedm_tgt released_tgt ord_src ord_tgt kind
      (RELM_LE: Capability.le releasedm_src releasedm_tgt)
      (RELM_SRC_WF: Capability.wf releasedm_src)
      (RELM_SRC_CLOSED: Memory.closed_capability releasedm_src mem1_src)
      (RELM_TGT_WF: Capability.wf releasedm_tgt)
      (RELM_TGT_CLOSED: Memory.closed_capability releasedm_tgt mem1_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt ord_tgt lc2_tgt sc2_tgt mem2_tgt kind)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists released_src lc2_src sc2_src mem2_src,
    <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val releasedm_src released_src ord_src lc2_src sc2_src mem2_src kind>> /\
    <<REL2: Capability.le released_src released_tgt>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit sim_local_promise; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit sim_local_fulfill; try apply STEP2;
    try apply LOCAL2; try apply MEM2; eauto.
  { eapply Memory.future_closed_capability; eauto. }
  i. des.
  exploit promise_fulfill_write; try exact STEP_SRC; try exact STEP_SRC0; eauto.
  { i. exploit ORD0; eauto.
    - etrans; eauto.
    - i. des. splits; auto. eapply sim_local_cell_bot; eauto.
  }
  i. des. esplits; eauto. etrans; eauto.
Qed.

Lemma sim_local_update
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt
      lc3_tgt sc3_tgt mem3_tgt
      loc ts1 val1 released1_tgt ord1_src ord1_tgt
      from2 to2 val2 released2_tgt ord2_src ord2_tgt kind
      (STEP1_TGT: Local.read_step lc1_tgt mem1_tgt loc ts1 val1 released1_tgt ord1_tgt lc2_tgt)
      (STEP2_TGT: Local.write_step lc2_tgt sc1_tgt mem1_tgt loc from2 to2 val2 released1_tgt released2_tgt ord2_tgt lc3_tgt sc3_tgt mem3_tgt kind)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt)
      (ORD1: Ordering.le ord1_src ord1_tgt)
      (ORD2: Ordering.le ord2_src ord2_tgt):
  exists released1_src released2_src lc2_src lc3_src sc3_src mem3_src,
    <<REL1: Capability.le released1_src released1_tgt>> /\
    <<REL2: Capability.le released2_src released2_tgt>> /\
    <<STEP1_SRC: Local.read_step lc1_src mem1_src loc ts1 val1 released1_src ord1_src lc2_src>> /\
    <<STEP2_SRC: Local.write_step lc2_src sc1_src mem1_src loc from2 to2 val2 released1_src released2_src ord2_src lc3_src sc3_src mem3_src kind>> /\
    <<LOCAL3: sim_local lc3_src lc3_tgt>> /\
    <<SC3: TimeMap.le sc3_src sc3_tgt>> /\
    <<MEM3: sim_memory mem3_src mem3_tgt>>.
Proof.
  exploit Local.read_step_future; eauto. i. des.
  exploit sim_local_read; eauto. i. des.
  exploit Local.read_step_future; eauto. i. des.
  hexploit sim_local_write; eauto. i. des.
  esplits; eauto.
Qed.

Lemma sim_local_fence
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      ordr_src ordw_src
      ordr_tgt ordw_tgt
      (STEP_TGT: Local.fence_step lc1_tgt sc1_tgt ordr_tgt ordw_tgt lc2_tgt sc2_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (ORDR: Ordering.le ordr_src ordr_tgt)
      (ORDW: Ordering.le ordw_src ordw_tgt):
  exists lc2_src sc2_src,
    <<STEP_SRC: Local.fence_step lc1_src sc1_src ordr_src ordw_src lc2_src sc2_src>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>>.
Proof.
  inv STEP_TGT. esplits; eauto.
  - econs; eauto.
  - econs; try apply LOCAL1. s.
    apply CommitFacts.write_fence_commit_mon; auto; try refl.
    apply CommitFacts.read_fence_commit_mon; auto; try refl.
    + apply LOCAL1.
    + apply WF1_TGT.
    + eapply CommitFacts.read_fence_future; apply WF1_SRC.
  - apply CommitFacts.write_fence_sc_mon; auto; try refl.
    apply CommitFacts.read_fence_commit_mon; auto; try refl.
    + apply LOCAL1.
    + apply WF1_TGT.
Qed.
