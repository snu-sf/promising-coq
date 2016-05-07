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


Inductive reorder_store l1 v1 o1: forall (i2:Instr.t), Prop :=
| reorder_store_load
    r2 l2 o2
    (ORD1: Ordering.le o1 Ordering.relaxed)
    (ORD2: Ordering.le o2 Ordering.relaxed)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.store l1 v1 o1))
                           (Instr.regs_of (Instr.load r2 l2 o2))):
    reorder_store l1 v1 o1 (Instr.load r2 l2 o2)
| reorder_store_store
    l2 v2 o2
    (ORD1: Ordering.le o1 Ordering.relaxed)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.store l1 v1 o1))
                           (Instr.regs_of (Instr.store l2 v2 o2))):
    reorder_store l1 v1 o1 (Instr.store l2 v2 o2)
| reorder_store_update
    r2 l2 rmw2 or2 ow2
    (ORD1: Ordering.le o1 Ordering.relaxed)
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.store l1 v1 o1))
                           (Instr.regs_of (Instr.update r2 l2 rmw2 or2 ow2))):
    reorder_store l1 v1 o1 (Instr.update r2 l2 rmw2 or2 ow2)
.

Inductive sim_store: forall (st_src:lang.(Language.state)) (th_src:Local.t) (mem_k_src:Memory.t)
                       (st_tgt:lang.(Language.state)) (th_tgt:Local.t) (mem_k_tgt:Memory.t), Prop :=
| sim_store_intro
    l1 f1 t1 v1 released1 o1 i2
    rs th1_src th1_tgt th2_src
    mem_k_src mem_k_tgt
    (REORDER: reorder_store l1 v1 o1 i2)
    (FULFILL: Local.fulfill_step th1_src mem_k_src l1 f1 t1 (RegFile.eval_value rs v1) released1 o1 th2_src)
    (LOCAL: sim_local th2_src th1_tgt):
    sim_store
      (State.mk rs [Stmt.instr i2; Stmt.instr (Instr.store l1 v1 o1)]) th1_src mem_k_src
      (State.mk rs [Stmt.instr i2]) th1_tgt mem_k_tgt
.

Lemma sim_store_sim_thread:
  sim_store <6= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
  - i. inv PR. eapply sim_local_future; try apply LOCAL; eauto.
    + eapply Local.fulfill_step_future; eauto.
      eapply Local.future_fulfill_step; eauto.
    + eapply Local.fulfill_step_future; eauto.
      eapply Local.future_fulfill_step; eauto.
      eapply Local.future_fulfill_step; eauto.
  - admit. (* promise *)
    (* https://github.com/jeehoonkang/memory-model-explorer/blob/11e21b0c9147859fca4c63e0b21bdbac6dac6215/formalization/src/opt/ReorderWrite.v#L430 *)
    (* https://github.com/jeehoonkang/memory-model-explorer/blob/86c803103989f87a17f50e6349aa9f285104af09/formalization/src/opt/Reorder.v#L116 *)
  - inv PR. i. inv STEP_TGT; [|by inv STEP; inv STATE; inv INSTR; inv REORDER].
    exploit Local.future_fulfill_step; try apply FULFILL; eauto. i.
    inv STEP; try (inv STATE; inv INSTR; inv REORDER); ss.
    + (* promise *)
      exploit sim_local_promise; eauto.
      { eapply Local.fulfill_step_future; eauto. }
      i. des.
      exploit reorder_fulfill_promise; try apply x0; try apply STEP_SRC; eauto. i. des.
      eexists _, _, _, _, _, _. splits; eauto.
      * econs. econs 1; eauto.
      * right. apply CIH. econs; eauto.
    + (* load *)
      exploit sim_local_read; eauto.
      { eapply Local.fulfill_step_future; eauto. }
      i. des.
      exploit reorder_fulfill_read; try apply x0; try apply STEP_SRC; eauto. i. des.
      eexists _, _, _, _, _, _. splits.
      * econs 2; [|econs 1]. econs 3; eauto. econs. econs.
      * econs. econs 4; eauto. econs.
        { econs. }
        { s. econs 1. erewrite RegFile.eq_except_value; eauto.
          - admit. (* RegSet.disjoint symmetry *)
          - apply RegFile.eq_except_singleton.
          - i. rewrite ORD1 in H. inv H.
        }
      * eauto.
      * left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
    + (* store *)
      exploit sim_local_write; eauto.
      { eapply Local.fulfill_step_future; eauto. }
      i. des.
      exploit reorder_fulfill_write; try apply x0; try apply STEP_SRC; eauto.
      i. des.
      eexists _, _, _, _, _, _. splits.
      * econs 2; [|econs 1]. econs 4; eauto. econs. econs.
      * econs. econs 4; eauto. econs.
        { econs. }
        { s. econs 1; eauto.
          i. rewrite ORD1 in H. inv H.
        }
      * s. eauto.
      * s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
    + (* update *)
      exploit sim_local_read; eauto.
      { eapply Local.fulfill_step_future; eauto. }
      i. des.
      exploit sim_local_write; eauto.
      { eapply Local.read_step_future; eauto.
        eapply Local.fulfill_step_future; eauto.
      }
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_fulfill_read; try apply x0; try apply STEP_SRC; eauto. i. des.
      exploit reorder_fulfill_write; try apply STEP2; try apply STEP_SRC0; eauto.
      { eapply Local.read_step_future; eauto. }
      i. des.
      eexists _, _, _, _, _, _. splits.
      * econs 2; [|econs 1]. econs 5; eauto. econs. econs. eauto.
      * econs. econs 4; eauto.
        { econs. econs. }
        { s. econs 1. erewrite RegFile.eq_except_value; eauto.
          - admit. (* RegSet.disjoint symmetry *)
          - apply RegFile.eq_except_singleton.
          - i. rewrite ORD1 in H. inv H.
        }
      * s. eauto.
      * s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
Admitted.
