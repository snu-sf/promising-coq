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
    (ORD2: Ordering.le o2 Ordering.relaxed)
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
    r2 l2 rmw2 or2 ow2
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (ORDW2: Ordering.le Ordering.sc o1 -> Ordering.le Ordering.sc ow2 -> False)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.load r1 l1 o1))
                           (Instr.regs_of (Instr.update r2 l2 rmw2 or2 ow2))):
    reorder_load r1 l1 o1 (Instr.update r2 l2 rmw2 or2 ow2)
| reorder_load_fence
    or2 ow2
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (ORDW2: Ordering.le ow2 Ordering.acqrel):
    reorder_load r1 l1 o1 (Instr.fence or2 ow2)
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

Lemma sim_load_step
      st1_src th1_src mem_k_src
      st1_tgt th1_tgt mem_k_tgt
      (SIM: sim_load st1_src th1_src mem_k_src
                     st1_tgt th1_tgt mem_k_tgt):
  forall mem1_src mem1_tgt
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (FUTURE_SRC: Memory.future mem_k_src mem1_src)
    (FUTURE_TGT: Memory.future mem_k_tgt mem1_tgt)
    (WF_SRC: Local.wf th1_src mem1_src)
    (WF_TGT: Local.wf th1_tgt mem1_tgt),
    _sim_thread_step lang lang ((sim_thread (sim_terminal eq)) \6/ sim_load)
                     st1_src th1_src mem1_src
                     st1_tgt th1_tgt mem1_tgt.
Proof.
  inv SIM. ii.
  exploit Local.future_read_step; try apply READ; eauto. i.
  inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR; inv REORDER); ss.
  - (* promise *)
    exploit sim_local_promise; eauto.
    { eapply Local.read_step_future; eauto. }
    i. des.
    exploit reorder_read_promise; try apply x0; try apply STEP_SRC; eauto. i. des.
    eexists _, _, _, _, _, _. splits; eauto.
    + econs. econs 1; eauto.
    + right. econs; eauto.
  - (* load *)
    exploit sim_local_read; eauto.
    { eapply Local.read_step_future; eauto. }
    i. des.
    exploit reorder_read_read; try apply x0; try apply STEP_SRC; eauto. i. des.
    eexists _, _, _, _, _, _. splits.
    + econs 2; [|econs 1]. econs 2. econs 2; eauto. econs. econs.
    + econs 2. econs 2; eauto. econs. econs.
    + s. eauto.
    + s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
      apply RegFun.add_add. admit. (* singleton disjoint => neq *)
  - (* store *)
    exploit sim_local_write; eauto.
    { eapply Local.read_step_future; eauto. }
    i. des.
    exploit reorder_read_write; try apply x0; try apply STEP_SRC; eauto. i. des.
    eexists _, _, _, _, _, _. splits.
    + econs 2; [|econs 1]. econs 2. econs 3; eauto. econs.
      erewrite RegFile.eq_except_value; eauto.
      * econs.
      * apply RegFile.eq_except_singleton.
    + econs 2. econs 2; eauto. econs. econs.
    + s. eauto.
    + s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
  - (* update *)
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
    { eapply Local.read_step_future; eauto. }
    i. des.
    eexists _, _, _, _, _, _. splits.
    + econs 2; [|econs 1]. econs 2. econs 4; eauto. econs. econs.
      erewrite <- RegFile.eq_except_rmw; eauto.
      * admit. (* disjoint add => disjoint *)
      * apply RegFile.eq_except_singleton.
    + econs 2. econs 2; eauto. econs. econs.
    + s. eauto.
    + s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
      apply RegFun.add_add. admit. (* disjoint singleton => neq *)
  - (* fence *)
    exploit sim_local_fence; eauto.
    { eapply Local.read_step_future; eauto. }
    i. des.
    exploit reorder_read_fence; try apply x0; try apply STEP_SRC; eauto. i. des.
    eexists _, _, _, _, _, _. splits.
    + econs 2; [|econs 1]. econs 2. econs 5; eauto. econs. econs.
    + econs 2. econs 2; eauto. econs. econs.
    + s. eauto.
    + s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
Admitted.

Lemma sim_load_sim_thread:
  sim_load <6= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
  - i. inv PR. eapply sim_local_future; try apply LOCAL; eauto.
    + eapply Local.read_step_future; eauto.
      eapply Local.future_read_step; eauto.
    + eapply Local.read_step_future; eauto.
      eapply Local.future_read_step; eauto.
      eapply Local.future_read_step; eauto.
  - i. eexists _, _, _. splits; eauto.
    inv PR. inv READ. inv LOCAL. ss.
    apply MemInv.sem_bot_inv in PROMISE. rewrite PROMISE. auto.
  - ii. exploit sim_load_step; eauto. i. des.
    + eexists _, _, _, _, _, _. splits; eauto.
      left. eapply paco7_mon; eauto. ss.
    + eexists _, _, _, _, _, _. splits; eauto.
Qed.
