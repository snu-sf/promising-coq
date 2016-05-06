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


Inductive reorder_load r1 l1 o1: forall (i2:Instr.t), Prop :=
| reorder_load_load
    r2 l2 o2
    (ORD2: Ordering.le o2 Ordering.release)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.load r1 l1 o1))
                           (Instr.regs_of (Instr.load r2 l2 o2))):
    reorder_load r1 l1 o1 (Instr.load r2 l2 o2)
| reorder_load_store
    l2 v2 o2
    (ORD: Ordering.le Ordering.sc o1 -> Ordering.le Ordering.sc o2 -> False)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.load r1 l1 o1))
                           (Instr.regs_of (Instr.store l2 v2 o2))):
    reorder_load r1 l1 o1 (Instr.store l2 v2 o2)
| reorder_load_update
    r2 l2 rmw2 o2
    (ORD2: Ordering.le o2 Ordering.release)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.load r1 l1 o1))
                           (Instr.regs_of (Instr.update r2 l2 rmw2 o2))):
    reorder_load r1 l1 o1 (Instr.update r2 l2 rmw2 o2)
| reorder_load_fence
    o2
    (ORD2: Ordering.le o2 Ordering.release):
    reorder_load r1 l1 o1 (Instr.fence o2)
.

Inductive sim_load: forall (st_src:lang.(Language.state)) (th_src:Local.t) (mem_k_src:Memory.t)
                      (st_tgt:lang.(Language.state)) (th_tgt:Local.t) (mem_k_tgt:Memory.t), Prop :=
| sim_load_intro
    r1 l1 ts1 v1 released1 o1 i2
    rs th1_src th1_tgt th2_src
    mem_k_src mem_k_tgt
    (REORDER: reorder_load r1 l1 o1 i2)
    (READ: Local.read_step th1_src mem_k_src l1 ts1 v1 released1 o1 th2_src)
    (LOCAL: sim_local th2_src th1_tgt):
    sim_load
      (State.mk rs [Stmt.instr i2; Stmt.instr (Instr.load r1 l1 o1)]) th1_src mem_k_src
      (State.mk (RegFun.add r1 v1 rs) [Stmt.instr i2]) th1_tgt mem_k_tgt
.

Lemma sim_load_sim_thread:
  sim_load <6= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
  - admit.
    (* future; https://github.com/jeehoonkang/memory-model-explorer/blob/86c803103989f87a17f50e6349aa9f285104af09/formalization/src/opt/Reorder.v#L100 *)
  - admit.
  - inv PR. i. inv STEP_TGT; [|by inv STEP; inv STATE; inv INSTR; inv REORDER].
    exploit Local.future_read_step; try apply READ; eauto. i.
    inv STEP; try (inv STATE; inv INSTR; inv REORDER); ss.
    + (* promise *)
      exploit sim_local_promise; eauto.
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_read_promise; try apply x0; try apply STEP_SRC; eauto. i. des.
      eexists _, _, _, _, _, _. splits; eauto.
      * econs. econs 1; eauto.
      * right. apply CIH. econs; eauto.
    + (* load *)
      exploit sim_local_read; eauto.
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_read_read; try apply x0; try apply STEP_SRC; eauto. i. des.
      eexists _, _, _, _, _, _. splits.
      * econs 2; [|econs 1]. econs 3; eauto. econs. econs.
      * econs. econs 3; eauto. econs. econs.
      * s. eauto.
      * s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
        apply RegFun.add_add. admit.
    + (* store *)
      exploit sim_local_write; eauto.
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_read_write; try apply x0; try apply STEP_SRC; eauto. i. des.
      eexists _, _, _, _, _, _. splits.
      * econs 2; [|econs 1]. econs 4; eauto. econs.
        erewrite RegFile.eq_except_value; eauto.
        { econs. }
        { apply RegFile.eq_except_singleton. }
      * econs. econs 3; eauto. econs. econs.
      * s. eauto.
      * s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
    + (* update *)
      exploit sim_local_read; eauto.
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit sim_local_write; eauto.
      { eapply Local.read_step_future; eauto.
        eapply Local.read_step_future; eauto.
      }
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_read_read; try apply x0; try apply STEP_SRC; eauto. i. des.
      exploit reorder_read_write; try apply STEP2; try apply LOCAL2; eauto.
      { destruct ord; ss. }
      { eapply Local.read_step_future; eauto. }
      i. des.
      eexists _, _, _, _, _, _. splits.
      * econs 2; [|econs 1]. econs 5; eauto. econs. econs.
        erewrite <- RegFile.eq_except_rmw; eauto.
        { admit. (* reg disjoint *) }
        { apply RegFile.eq_except_singleton. }
      * econs. econs 3; eauto. econs. econs.
      * s. eauto.
      * s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
        { apply RegFun.add_add. admit. }
    + (* fence *)
      exploit sim_local_fence; eauto.
      { eapply Local.read_step_future; eauto. }
      i. des.
      exploit reorder_read_fence; try apply x0; try apply STEP_SRC; eauto. i. des.
      eexists _, _, _, _, _, _. splits.
      * econs 2; [|econs 1]. econs 6; eauto. econs. econs.
      * econs. econs 3; eauto. econs. econs.
      * s. eauto.
      * s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
Admitted.
