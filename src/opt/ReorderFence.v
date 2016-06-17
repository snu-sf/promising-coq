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
Require Import Memory.
Require Import Commit.
Require Import Thread.

Require Import Configuration.
Require Import Simulation.
Require Import Compatibility.
Require Import MemInv.
Require Import ReorderStep.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive reorder_fence (or1 ow1:Ordering.t): forall (i2:Instr.t), Prop :=
| reorder_fence_store
    l2 v2 o2
    (ORDR1: Ordering.le or1 Ordering.acqrel)
    (ORDW1: Ordering.le ow1 Ordering.relaxed):
    reorder_fence or1 ow1 (Instr.store l2 v2 o2)
.

Inductive sim_fence: forall (st_src:lang.(Language.state)) (lc_src:Local.t) (sc_k_src:TimeMap.t) (mem_k_src:Memory.t)
                       (st_tgt:lang.(Language.state)) (lc_tgt:Local.t) (sc_k_tgt:TimeMap.t) (mem_k_tgt:Memory.t), Prop :=
| sim_fence_intro
    or1 ow1 i2
    rs lc1_src lc1_tgt lc2_src
    mem_k_src mem_k_tgt
    (REORDER: reorder_fence or1 ow1 i2)
    (FENCE: Local.fence_step lc1_src sc_k_src mem_k_src or1 ow1 lc2_src)
    (LOCAL: sim_local lc2_src lc1_tgt):
    sim_fence
      (State.mk rs [Stmt.instr i2; Stmt.instr (Instr.fence or1 ow1)]) lc1_src sc_k_src mem_k_src
      (State.mk rs [Stmt.instr i2]) lc1_tgt sc_k_tgt mem_k_tgt
.

Lemma sim_fence_step
      st1_src lc1_src sc_k_src mem_k_src
      st1_tgt lc1_tgt sc_k_tgt mem_k_tgt
      (SIM: sim_fence st1_src lc1_src sc_k_src mem_k_src
                      st1_tgt lc1_tgt sc_k_tgt mem_k_tgt):
  forall mem1_src mem1_tgt
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (FUTURE_SRC: Memory.future mem_k_src mem1_src)
    (FUTURE_TGT: Memory.future mem_k_tgt mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt),
    _sim_thread_step lang lang ((sim_thread (sim_terminal eq)) \6/ sim_fence)
                     st1_src lc1_src mem1_src
                     st1_tgt lc1_tgt mem1_tgt.
Proof.
  inv SIM. ii.
  exploit Local.future_fence_step; try apply FENCE; eauto. i.
  inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR; inv REORDER); ss.
  - (* promise *)
    exploit sim_local_promise; eauto.
    { eapply Local.fence_step_future; eauto. }
    i. des.
    exploit reorder_fence_promise; try apply x0; try apply STEP_SRC; eauto.
    { inv REORDER; ss. }
    { inv REORDER; ss. }
    i. des.
    esplits; eauto.
    + econs. econs 1; eauto.
    + eauto.
    + right. econs; eauto.
  - (* store *)
    exploit sim_local_write; eauto.
    { eapply Local.fence_step_future; eauto. }
    i. des.
    exploit reorder_fence_write; try apply x0; try apply STEP_SRC; eauto. i. des.
    esplits.
    + econs 2; [|econs 1]. econs.
      * econs 2. econs 3; eauto. econs. econs.
      * eauto.
    + econs 2. econs 5; eauto. econs. econs.
    + eauto.
    + eauto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
Qed.

Lemma sim_fence_sim_thread:
  sim_fence <6= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
  - i. inv PR. eapply sim_local_future; try apply LOCAL; eauto.
    + eapply Local.fence_step_future; eauto.
      eapply Local.future_fence_step; eauto.
    + eapply Local.fence_step_future; eauto.
      eapply Local.future_fence_step; eauto.
      eapply Local.future_fence_step; eauto.
  - i. esplits; eauto.
    inv PR. inv FENCE. inv LOCAL. ss.
    apply MemInv.sem_bot_inv in PROMISES. rewrite PROMISES. auto.
  - ii. exploit sim_fence_step; eauto. i. des.
    + esplits; eauto.
      left. eapply paco9_mon; eauto. ss.
    + esplits; eauto.
Qed.
