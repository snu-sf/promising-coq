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
Require Import ReorderBase.

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

Inductive sim_fence: forall (st_src:lang.(Language.state)) (th_src:Local.t) (mem_k_src:Memory.t)
                       (st_tgt:lang.(Language.state)) (th_tgt:Local.t) (mem_k_tgt:Memory.t), Prop :=
| sim_fence_intro
    or1 ow1 i2
    rs th1_src th1_tgt th2_src
    mem_k_src mem_k_tgt
    (REORDER: reorder_fence or1 ow1 i2)
    (FENCE: Local.fence_step th1_src mem_k_src or1 ow1 th2_src)
    (LOCAL: sim_local th2_src th1_tgt):
    sim_fence
      (State.mk rs [Stmt.instr i2; Stmt.instr (Instr.fence or1 ow1)]) th1_src mem_k_src
      (State.mk rs [Stmt.instr i2]) th1_tgt mem_k_tgt
.

Lemma sim_fence_sim_thread:
  sim_fence <6= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
  - admit.
    (* future; https://github.com/jeehoonkang/memory-model-explorer/blob/86c803103989f87a17f50e6349aa9f285104af09/formalization/src/opt/Reorder.v#L100 *)
  - admit.
  - inv PR. i. inv STEP_TGT; [|by inv STEP; inv STATE; inv INSTR; inv REORDER].
    exploit Local.future_fence_step; try apply FENCE; eauto. i.
    inv STEP; try (inv STATE; inv INSTR; inv REORDER); ss.
    + (* promise *)
      exploit sim_local_promise; eauto.
      { eapply Local.fence_step_future; eauto. }
      i. des.
      exploit reorder_fence_promise; try apply x0; try apply STEP_SRC; eauto.
      { inv REORDER; ss. }
      { inv REORDER; ss. }
      i. des.
      eexists _, _, _, _, _, _. splits; eauto.
      * econs. econs 1; eauto.
      * right. apply CIH. econs; eauto.
    + (* store *)
      exploit sim_local_write; eauto.
      { eapply Local.fence_step_future; eauto. }
      i. des.
      exploit reorder_fence_write; try apply x0; try apply STEP_SRC; eauto. i. des.
      eexists _, _, _, _, _, _. splits.
      * econs 2; [|econs 1]. econs 4; eauto. econs. econs.
      * econs. econs 6; eauto. econs. econs.
      * s. eauto.
      * s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
Admitted.
