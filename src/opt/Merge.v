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
    exploit merge_read_read; try apply LOCAL0; eauto. i. des.
    admit.
Admitted.
