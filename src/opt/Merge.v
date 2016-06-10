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
Require Import MergeStep.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.

Lemma assign_sim_thread:
  forall r1 r2
    rs_src rs_tgt lc_src lc_tgt mem_k_src mem_k_tgt
    (RS: rs_src = RegFun.add r2 (rs_tgt r1) rs_tgt)
    (LOCAL: sim_local lc_src lc_tgt),
    sim_thread
      (sim_terminal eq)
      (State.mk rs_src [Stmt.instr Instr.skip]) lc_src mem_k_src
      (State.mk rs_tgt [Stmt.instr (Instr.assign r2 (Instr.expr_val (Value.reg r1)))]) lc_tgt mem_k_tgt.
Proof.
  pcofix CIH. i. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. eapply sim_local_future; try apply MEMORY; eauto. apply LOCAL. }
  { i. eexists _, _, _. splits; eauto.
    inv LOCAL. apply MemInv.sem_bot_inv in PROMISES. rewrite PROMISES. auto.
  }
  ii. inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    eexists _, _, _, _, _, _, _. splits; eauto.
    econs 1; eauto. econs; eauto. eauto.
  - (* load *)
    exploit sim_local_silent; eauto. i. des.
    eexists _, _, _, _, _, _, _. splits; eauto.
    + econs 2. econs 1; eauto. econs. econs.
    + eauto.
    + left. eapply paco7_mon.
      * apply sim_stmts_nil; eauto.
      * ii. inv PR.
Qed.

Lemma merge_load_load_sim_stmts
      l
      r1 o1
      r2 o2
      o
      (O1: Ordering.le o1 o)
      (O2: Ordering.le o2 o):
  sim_stmts eq
            [Stmt.instr (Instr.load r1 l o1); Stmt.instr (Instr.load r2 l o2); Stmt.instr Instr.skip]
            [Stmt.instr (Instr.load r1 l o); Stmt.instr (Instr.assign r2 (Instr.expr_val (Value.reg r1)))]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. eapply sim_local_future; try apply MEMORY; eauto. apply LOCAL. }
  { i. eexists _, _, _. splits; eauto.
    inv LOCAL. apply MemInv.sem_bot_inv in PROMISES. rewrite PROMISES. auto.
  }
  ii. inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    eexists _, _, _, _, _, _, _. splits; eauto.
    econs 1; eauto. econs; eauto. eauto.
  - (* load *)
    exploit merge_read_read; try apply LOCAL0; [apply O1|apply O2| | |]; eauto. i. des.
    exploit sim_local_read; try apply STEP1; eauto. i. des.
    exploit sim_local_read; try apply STEP2; eauto.
    { eapply Local.read_step_future; eauto. }
    { eapply Local.read_step_future; eauto. }
    i. des.
    eexists _, _, _, _, _, _, _. splits.
    + econs 2; [|econs 1]. econs.
      * econs 2. econs 2; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2; eauto. econs. econs.
    + eauto.
    + eauto.
    + left. eapply paco7_mon.
      * apply assign_sim_thread; eauto.
        unfold RegFun.add, RegFun.find. repeat condtac; auto. congr.
      * i. inv PR.
Qed.

Lemma merge_fence_fence_sim_stmts
      ordr1 ordw1
      ordr2 ordw2
      ordr ordw
      (ORDR1: Ordering.le ordr1 ordr)
      (ORDR2: Ordering.le ordr2 ordr)
      (ORDW1: Ordering.le ordw1 ordw)
      (ORDW2: Ordering.le ordw2 ordw):
  sim_stmts eq
            [Stmt.instr (Instr.fence ordr1 ordw1); Stmt.instr (Instr.fence ordr2 ordw2)]
            [Stmt.instr (Instr.fence ordr ordw)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. eapply sim_local_future; try apply MEMORY; eauto. apply LOCAL. }
  { i. eexists _, _, _. splits; eauto.
    inv LOCAL. apply MemInv.sem_bot_inv in PROMISES. rewrite PROMISES. auto.
  }
  ii. inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    eexists _, _, _, _, _, _, _. splits; eauto.
    econs 1; eauto. econs; eauto. eauto.
  - (* fence *)
    exploit merge_fence_fence; try apply LOCAL0; [apply ORDR1|apply ORDR2|apply ORDW1|apply ORDW2| | |]; eauto. i. des.
    exploit sim_local_fence; try apply STEP1; eauto. i. des.
    exploit sim_local_fence; try apply STEP2; eauto.
    { eapply Local.fence_step_future; eauto. }
    { eapply Local.fence_step_future; eauto. }
    i. des.
    eexists _, _, _, _, _, _, _. splits.
    + econs 2; [|econs 1]. econs.
      * econs 2. econs 5; eauto. econs. econs.
      * eauto.
    + econs 2. econs 5; eauto. econs. econs.
    + eauto.
    + eauto.
    + left. eapply paco7_mon.
      * apply sim_stmts_nil; eauto.
      * ii. inv PR.
Qed.
