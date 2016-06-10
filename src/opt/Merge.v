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
  forall v1 r2
    rs_src rs_tgt lc_src lc_tgt mem_k_src mem_k_tgt
    (RS: rs_src = RegFun.add r2 (RegFile.eval_value rs_tgt v1) rs_tgt)
    (LOCAL: sim_local lc_src lc_tgt),
    sim_thread
      (sim_terminal eq)
      (State.mk rs_src [Stmt.instr Instr.skip]) lc_src mem_k_src
      (State.mk rs_tgt [Stmt.instr (Instr.assign r2 (Instr.expr_val v1))]) lc_tgt mem_k_tgt.
Proof.
  pcofix CIH. i. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. eapply sim_local_future; try apply MEMORY; eauto. apply LOCAL. }
  { i. eexists _, _, _. splits; eauto.
    eapply sim_local_memory_bot; eauto.
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
    eapply sim_local_memory_bot; eauto.
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
      * apply assign_sim_thread; eauto. s. rewrite RegFun.add_spec_eq. auto.
      * i. inv PR.
Qed.

Lemma merge_store_load_sim_stmts
      l
      v1 o1
      r2 o2
      (O2: Ordering.le o2 Ordering.acqrel):
  sim_stmts eq
            [Stmt.instr (Instr.store l v1 o1); Stmt.instr (Instr.load r2 l o2); Stmt.instr Instr.skip]
            [Stmt.instr (Instr.store l v1 o1); Stmt.instr (Instr.assign r2 v1)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. eapply sim_local_future; try apply MEMORY; eauto. apply LOCAL. }
  { i. eexists _, _, _. splits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    eexists _, _, _, _, _, _, _. splits; eauto.
    econs 1; eauto. econs; eauto. eauto.
  - (* store *)
    exploit merge_write_read1; eauto. i. des.
    exploit sim_local_write; try apply STEP1; eauto. i. des.
    exploit sim_local_read; try apply STEP2; eauto.
    { eapply Local.write_step_future; eauto. }
    { eapply Local.write_step_future; eauto. }
    i. des.
    eexists _, _, _, _, _, _, _. splits.
    + econs 2; [|econs 1]. econs.
      * econs 2. econs 3; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2; eauto. econs. econs.
    + eauto.
    + eauto.
    + left. eapply paco7_mon.
      * apply assign_sim_thread; auto.
      * i. inv PR.
Qed.

Lemma merge_store_store_sim_stmts
      l
      v1 o1
      v2 o2
      o
      (O1: Ordering.le o1 o)
      (O2: Ordering.le o2 o):
  sim_stmts eq
            [Stmt.instr (Instr.store l v1 o1); Stmt.instr (Instr.store l v2 o2)]
            [Stmt.instr (Instr.store l v2 o)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. eapply sim_local_future; try apply MEMORY; eauto. apply LOCAL. }
  { i. eexists _, _, _. splits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    eexists _, _, _, _, _, _, _. splits; eauto.
    econs 1; eauto. econs; eauto. eauto.
  - (* store *)
    exploit merge_write_write; try apply LOCAL0; [apply O1|apply O2| | |]; eauto. i. des.
    exploit sim_local_write; try apply STEP1; eauto. i. des.
    exploit sim_local_write; try apply STEP2; eauto.
    { eapply Local.write_step_future; eauto. }
    { eapply Local.write_step_future; eauto. }
    { eapply Local.write_step_future; eauto. }
    { eapply Local.write_step_future; eauto. }
    i. des.
    eexists _, _, _, _, _, _, _. splits.
    + econs 2; [|econs 1]. econs.
      * econs 2. econs 3; eauto. econs. econs.
      * eauto.
    + econs 2. econs 3; eauto. econs. econs.
    + eauto.
    + etrans; eauto.
    + left. eapply paco7_mon.
      * apply sim_stmts_nil; eauto.
      * ii. inv PR.
Grab Existential Variables.
  { apply Time.elt. }
  { apply Capability.elt. }
Qed.

Lemma merge_store_update_sim_stmts
      l
      v1 o1
      r2 or2 ow2
      o
      (O1: Ordering.le o1 o)
      (OW2: Ordering.le ow2 o)
      (OR2: Ordering.le or2 Ordering.acqrel):
  sim_stmts eq
            [Stmt.instr (Instr.store l v1 o1); Stmt.instr (Instr.update r2 l (Instr.fetch_add (Value.const 0)) or2 ow2); Stmt.instr Instr.skip]
            [Stmt.instr (Instr.store l v1 o); Stmt.instr (Instr.assign r2 v1)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. eapply sim_local_future; try apply MEMORY; eauto. apply LOCAL. }
  { i. eexists _, _, _. splits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    eexists _, _, _, _, _, _, _. splits; eauto.
    econs 1; eauto. econs; eauto. eauto.
  - (* store *)
    exploit merge_write_write; try apply LOCAL0; [apply O1|apply OW2| | |]; eauto. i. des.
    exploit merge_write_read1; try apply STEP1; eauto. i. des.
    exploit Local.write_step_future; eauto. i. des.
    exploit sim_local_write; try apply STEP0; eauto. i. des.
    exploit Local.write_step_future; eauto. i. des.
    exploit sim_local_read; try apply STEP3; eauto. i. des.
    exploit sim_local_write; try apply STEP2; eauto.
    { eapply Local.read_step_future; eauto. }
    { eapply Local.read_step_future; eauto. }
    i. des.
    eexists _, _, _, _, _, _, _. splits.
    + econs 2; [|econs 1]. econs.
      * econs 2. econs 3; eauto. econs. econs.
      * eauto.
    + econs 2. econs 4; eauto.
      * econs. econs. econs.
      * rewrite Const.add_0_r. rewrite Capability.le_join_r; eauto. refl.
    + eauto.
    + etrans; eauto.
    + left. eapply paco7_mon.
      * apply assign_sim_thread; eauto. ss. rewrite Const.add_0_r. auto.
      * ii. inv PR.
Grab Existential Variables.
  { apply Time.elt. }
Qed.

(* TODO: check the condition `OR1` *)
Lemma merge_update_load_sim_stmts
      l
      r1 v1 or1 ow1
      r2 o2
      (OR1: Ordering.le Ordering.relaxed or1)
      (O2: Ordering.le o2 Ordering.relaxed):
  sim_stmts eq
            [Stmt.instr (Instr.update r1 l (Instr.fetch_add v1) or1 ow1); Stmt.instr (Instr.load r2 l o2); Stmt.instr Instr.skip]
            [Stmt.instr (Instr.update r1 l (Instr.fetch_add v1) or1 ow1); Stmt.instr (Instr.assign r2 r1)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. eapply sim_local_future; try apply MEMORY; eauto. apply LOCAL. }
  { i. eexists _, _, _. splits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    eexists _, _, _, _, _, _, _. splits; eauto.
    econs 1; eauto. econs; eauto. eauto.
  - (* update *)
    exploit Local.read_step_future; eauto. i. des.
    exploit merge_write_read2; try apply LOCAL2; eauto.
    { inv LOCAL1. apply COMMIT. }
    { inv LOCAL1. apply COMMIT. auto. }
    i. des.
    exploit sim_local_read; try apply LOCAL1; eauto. i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_write; try apply STEP1; eauto. i. des.
    exploit sim_local_read; try apply STEP2; eauto.
    { eapply Local.write_step_future; eauto. }
    { eapply Local.write_step_future; eauto. }
    i. des.
    eexists _, _, _, _, _, _, _. splits.
    + econs 2; [|econs 1]. econs.
      * econs 2. econs 4; eauto. econs. econs. eauto.
      * eauto.
    + econs 2. econs 2; eauto. econs. econs.
    + eauto.
    + eauto.
    + left. eapply paco7_mon.
      * apply assign_sim_thread; auto. s. rewrite RegFun.add_spec_eq. inv RMW. auto.
      * i. inv PR.
Qed.

Lemma merge_update_update_sim_stmts
      l
      r1 v1 or1 ow1
      r2 or2 ow2
      or ow
      (OR1_RLX: Ordering.le Ordering.relaxed or1)
      (OR2_RLX: Ordering.le or2 Ordering.relaxed)
      (OW1: Ordering.le ow1 ow)
      (OW2: Ordering.le ow2 ow)
      (OR1: Ordering.le or1 or)
      (OR2: Ordering.le or2 or):
  sim_stmts eq
            [Stmt.instr (Instr.update r1 l (Instr.fetch_add v1) or1 ow1); Stmt.instr (Instr.update r2 l (Instr.fetch_add 0) or2 ow2); Stmt.instr Instr.skip]
            [Stmt.instr (Instr.update r1 l (Instr.fetch_add v1) or ow); Stmt.instr (Instr.assign r2 r1)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits.
  { i. inv TERMINAL_TGT. }
  { i. eapply sim_local_future; try apply MEMORY; eauto. apply LOCAL. }
  { i. eexists _, _, _. splits; eauto.
    eapply sim_local_memory_bot; eauto.
  }
  ii. inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    eexists _, _, _, _, _, _, _. splits; eauto.
    econs 1; eauto. econs; eauto. eauto.
  - (* update *)
    admit.
Admitted.

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
    eapply sim_local_memory_bot; eauto.
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
