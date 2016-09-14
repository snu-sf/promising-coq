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
Require Import TView.
Require Import Thread.
Require Import Configuration.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import Compatibility.
Require Import SimThread.

Require Import ReorderStep.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive reorder_fence (or1 ow1:Ordering.t): forall (i2:Instr.t), Prop :=
| reorder_fence_load
    r2 l2 o2
    (ORDR1: Ordering.le or1 Ordering.acqrel)
    (ORDW1: Ordering.le ow1 Ordering.relaxed)
    (ORD2: Ordering.le o2 Ordering.plain \/ Ordering.le Ordering.acqrel o2):
    reorder_fence or1 ow1 (Instr.load r2 l2 o2)
| reorder_fence_store
    l2 v2 o2
    (ORDR1: Ordering.le or1 Ordering.acqrel)
    (ORDW1: Ordering.le ow1 Ordering.relaxed):
    reorder_fence or1 ow1 (Instr.store l2 v2 o2)
| reorder_fence_update
    r2 l2 rmw2 or2 ow2
    (ORDR1: Ordering.le or1 Ordering.acqrel)
    (ORDW1: Ordering.le ow1 Ordering.relaxed)
    (ORDR2: Ordering.le or2 Ordering.plain \/ Ordering.le Ordering.acqrel or2):
    reorder_fence or1 ow1 (Instr.update r2 l2 rmw2 or2 ow2)
.

Inductive sim_fence: forall (st_src:lang.(Language.state)) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t)
                       (st_tgt:lang.(Language.state)) (lc_tgt:Local.t) (sc1_tgt:TimeMap.t) (mem1_tgt:Memory.t), Prop :=
| sim_fence_intro
    or1 ow1 i2 rs
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    lc2_src sc2_src
    (REORDER: reorder_fence or1 ow1 i2)
    (FENCE: Local.fence_step lc1_src sc1_src or1 ow1 lc2_src sc2_src)
    (LOCAL: sim_local lc2_src lc1_tgt):
    sim_fence
      (State.mk rs [Stmt.instr i2; Stmt.instr (Instr.fence or1 ow1)]) lc1_src sc1_src mem1_src
      (State.mk rs [Stmt.instr i2]) lc1_tgt sc1_tgt mem1_tgt
.

Lemma future_fence_step lc1 sc1 sc1' mem1 mem1' ordr ordw lc2 sc2
      (ORDW: Ordering.le ordw Ordering.acqrel)
      (SC_FUTURE: TimeMap.le sc1 sc1')
      (MEM_FUTURE: Memory.future mem1 mem1')
      (STEP: Local.fence_step lc1 sc1 ordr ordw lc2 sc2):
  Local.fence_step lc1 sc1' ordr ordw lc2 sc1'.
Proof.
  inv STEP.
  erewrite TViewFacts.write_fence_tview_acqrel; auto.
  erewrite <- TViewFacts.write_fence_sc_acqrel at 2; eauto.
  econs; auto.
Qed.

Lemma sim_fence_step
      st1_src lc1_src sc0_src mem0_src
      st1_tgt lc1_tgt sc0_tgt mem0_tgt
      (SIM: sim_fence st1_src lc1_src sc0_src mem0_src
                      st1_tgt lc1_tgt sc0_tgt mem0_tgt):
  forall sc1_src sc1_tgt
    mem1_src mem1_tgt
    (SC: TimeMap.le sc1_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (SC_FUTURE_SRC: TimeMap.le sc0_src sc1_src)
    (SC_FUTURE_TGT: TimeMap.le sc0_tgt sc1_tgt)
    (MEM_FUTURE_SRC: Memory.future mem0_src mem1_src)
    (MEM_FUTURE_TGT: Memory.future mem0_tgt mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt),
    _sim_thread_step lang lang ((sim_thread (sim_terminal eq)) \8/ sim_fence)
                     st1_src lc1_src sc1_src mem1_src
                     st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  inv SIM. ii.
  exploit future_fence_step; try apply FENCE; eauto; i.
  { inv REORDER; etrans; eauto. }
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR; inv REORDER); ss.
  - (* promise *)
    exploit sim_local_promise; eauto.
    { eapply Local.fence_step_future; eauto. }
    i. des.
    exploit reorder_fence_promise; try apply x0; try apply STEP_SRC; eauto.
    { inv REORDER; ss. }
    i. des.
    esplits; try apply SC; eauto.
    + econs 2. econs 1. econs; eauto.
    + eauto.
    + right. econs; eauto.
  - (* load *)
    guardH ORD2.
    exploit sim_local_read; try exact LOCAL0; try apply SC; eauto; try refl; viewtac.
    { eapply Local.fence_step_future; eauto. }
    i. des.
    exploit reorder_fence_read; try apply x0; try apply STEP_SRC; eauto; try by viewtac. i. des.
    esplits.
    + econs 2; [|econs 1]. econs.
      * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs; [|econs 5]; eauto. econs. econs.
    + auto.
    + etrans; eauto.
    + auto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
      etrans; eauto.
  - (* store *)
    hexploit sim_local_write; try exact LOCAL1; try apply SC; eauto; try refl; viewtac.
    { eapply Local.fence_step_future; eauto. }
    i. des.
    exploit reorder_fence_write; try apply x0; try apply STEP_SRC; eauto; try by viewtac. i. des.
    esplits.
    + econs 2; [|econs 1]. econs.
      * econs. econs 2. econs; [|econs 3]; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs; [|econs 5]; eauto. econs. econs.
    + auto.
    + etrans; eauto.
    + etrans; eauto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
      etrans; eauto.
  - (* update *)
    guardH ORDR2.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read; try exact LOCAL1; try apply SC; eauto; try refl; viewtac.
    { eapply Local.fence_step_future; eauto. }
    i. des.
    exploit reorder_fence_read; try apply x0; try apply STEP_SRC; eauto; try by viewtac. i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit Local.fence_step_future; eauto. i. des.
    generalize LOCAL3. i. rewrite LOCAL0 in LOCAL3.
    generalize SC0. i. rewrite SC in SC1.
    hexploit sim_local_write; try exact LOCAL2; try apply SC1; eauto; try refl; viewtac. i. des.
    exploit reorder_fence_write; try apply STEP2; try apply STEP_SRC0; eauto; try by viewtac. i. des.
    esplits.
    + econs 2; [|econs 1]. econs.
      * econs. econs 2. econs; [|econs 4]; eauto. econs. econs. eauto.
      * eauto.
    + econs 2. econs 2. econs; [|econs 5]; eauto. econs. econs.
    + auto.
    + etrans; eauto.
    + etrans; eauto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
      etrans; eauto.
Qed.

Lemma sim_fence_sim_thread:
  sim_fence <8= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
  - i. inv PR. exploit SimPromises.future; try apply LOCAL; eauto.
    { eapply Local.fence_step_future; try exact SC_SRC; eauto.
      eapply future_fence_step; try apply FENCE; eauto.
      inv REORDER; etrans; eauto.
    }
    { eapply Local.fence_step_future; try apply SC_SRC0; eauto.
      eapply future_fence_step; try apply FENCE; eauto.
      - inv REORDER; etrans; eauto.
      - etrans; eauto.
    }
    i. des. esplits; eauto.
    + etrans.
      * apply Memory.max_timemap_spec; eauto. viewtac.
      * apply sim_memory_max_timemap; eauto.
    + etrans.
      * apply Memory.max_timemap_spec; eauto. viewtac.
      * apply Memory.future_max_timemap; eauto.
    + apply Memory.max_timemap_closed. viewtac.
  - i. esplits; eauto.
    inv PR. inversion FENCE. subst lc2_src. inversion LOCAL. ss.
    apply SimPromises.sem_bot_inv in PROMISES; auto. rewrite PROMISES. auto.
  - ii. exploit sim_fence_step; try apply PR; try apply SC; eauto. i. des.
    + esplits; eauto.
      left. eapply paco9_mon; eauto. ss.
    + esplits; eauto.
Qed.
