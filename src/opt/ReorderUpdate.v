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
Require Import Progress.
Require Import ReorderStep.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive reorder_update r1 l1 rmw1 or1 ow1: forall (i2:Instr.t), Prop :=
| reorder_update_load
    r2 l2 o2
    (ORDR1: Ordering.le or1 Ordering.acqrel)
    (ORDW1: Ordering.le ow1 Ordering.relaxed)
    (ORD2: Ordering.le o2 Ordering.relaxed)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.update r1 l1 rmw1 or1 ow1))
                           (Instr.regs_of (Instr.load r2 l2 o2))):
    reorder_update r1 l1 rmw1 or1 ow1 (Instr.load r2 l2 o2)
| reorder_update_store
    l2 v2 o2
    (ORDR1: Ordering.le or1 Ordering.acqrel)
    (ORDW1: Ordering.le ow1 Ordering.relaxed)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.update r1 l1 rmw1 or1 ow1))
                           (Instr.regs_of (Instr.store l2 v2 o2))):
    reorder_update r1 l1 rmw1 or1 ow1 (Instr.store l2 v2 o2)
| reorder_update_update
    r2 l2 rmw2 or2 ow2
    (ORDR1: Ordering.le or1 Ordering.acqrel)
    (ORDW1: Ordering.le ow1 Ordering.relaxed)
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (ORDW2: Ordering.le ow2 Ordering.acqrel)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.update r1 l1 rmw1 or1 ow1))
                           (Instr.regs_of (Instr.update r2 l2 rmw2 or2 ow2))):
    reorder_update r1 l1 rmw1 or1 ow1 (Instr.update r2 l2 rmw2 or2 ow2)
.

Inductive sim_update: forall (st_src:lang.(Language.state)) (lc_src:Local.t) (mem_k_src:Memory.t)
                        (st_tgt:lang.(Language.state)) (lc_tgt:Local.t) (mem_k_tgt:Memory.t), Prop :=
| sim_update_intro
    r1 l1 from1 to1 vr1 vret1 vw1 releasedr1 releasedw1 rmw1 or1 ow1 i2
    rs lc1_src lc1_tgt lc2_src lc3_src
    mem_k_src mem_k_tgt
    (REORDER: reorder_update r1 l1 rmw1 or1 ow1 i2)
    (RMW: RegFile.eval_rmw rs rmw1 vr1 = (vret1, vw1))
    (READ: Local.read_step lc1_src mem_k_src l1 from1 vr1 releasedr1 or1 lc2_src)
    (FULFILL: Local.fulfill_step lc2_src mem_k_src l1 from1 to1 vw1 releasedw1 (Capability.join releasedr1 releasedw1) ow1 lc3_src)
    (LOCAL: sim_local lc3_src lc1_tgt):
    sim_update
      (State.mk rs [Stmt.instr i2; Stmt.instr (Instr.update r1 l1 rmw1 or1 ow1)]) lc1_src mem_k_src
      (State.mk (RegFun.add r1 vret1 rs) [Stmt.instr i2]) lc1_tgt mem_k_tgt
.

Lemma sim_update_step
      st1_src lc1_src mem_k_src
      st1_tgt lc1_tgt mem_k_tgt
      (SIM: sim_update st1_src lc1_src mem_k_src
                      st1_tgt lc1_tgt mem_k_tgt):
  forall mem1_src mem1_tgt
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (FUTURE_SRC: Memory.future mem_k_src mem1_src)
    (FUTURE_TGT: Memory.future mem_k_tgt mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt),
    _sim_thread_step lang lang ((sim_thread (sim_terminal eq)) \6/ sim_update)
                     st1_src lc1_src mem1_src
                     st1_tgt lc1_tgt mem1_tgt.
Proof.
  inv SIM. ii.
  exploit Local.future_read_step; try apply READ; eauto. i.
  exploit Local.future_fulfill_step; try apply FULFILL; eauto. i.
  inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR; inv REORDER); ss.
  - (* promise *)
    exploit sim_local_promise; eauto.
    { eapply Local.fulfill_step_future; eauto.
      eapply Local.read_step_future; eauto.
    }
    i. des.
    exploit sim_local_fulfill; try apply x1; try refl; eauto.
    { eapply Local.read_step_future; eauto. }
    { eapply Local.read_step_future; eauto. }
    i. des.
    exploit reorder_fulfill_promise; try apply x1; try apply STEP_SRC; eauto.
    { eapply Local.read_step_future; eauto. }
    i. des.
    exploit reorder_read_promise; try apply x0; try apply STEP1; eauto. i. des.
    i. des.
    eexists _, _, _, _, _, _. splits; eauto.
    + econs. econs 1; eauto.
    + right. econs; try apply STEP3; try apply STEP_SRC0; eauto.
  - (* load *)
    exploit sim_local_read; eauto.
    { eapply Local.fulfill_step_future; eauto.
      eapply Local.read_step_future; eauto.
    }
    i. des.
    exploit reorder_fulfill_read; try apply x1; try apply STEP_SRC; eauto.
    { eapply Local.read_step_future; eauto. }
    i. des.
    exploit reorder_read_read; try apply x0; try apply STEP1; eauto. i. des.
    apply RegSet.disjoint_add in REGS. des.
    eexists _, _, _, _, _, _. splits.
    + econs 2; [|econs 1]. econs 2. econs 2; eauto. econs. econs.
    + econs 2. econs 4; eauto.
      * econs. econs. erewrite RegFile.eq_except_rmw; eauto.
        { symmetry. eauto. }
        { apply RegFile.eq_except_singleton. }
      * s. econs 1; eauto.
        i. destruct ow1; inv ORDW1; inv H.
    + s. eauto.
    + s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss; eauto.
      apply RegFun.add_add. ii. subst. apply REGS.
      apply RegSet.Facts.singleton_iff. auto.
  - (* store *)
    exploit sim_local_write; eauto.
    { eapply Local.fulfill_step_future; eauto.
      eapply Local.read_step_future; eauto.
    }
    i. des.
    exploit reorder_fulfill_write; try apply x1; try apply STEP_SRC; eauto.
    { eapply Local.read_step_future; eauto. }
    i. des.
    exploit reorder_read_write; try apply x0; try apply STEP1; eauto.
    { i. destruct or1; inv ORDR1; inv H0. }
    i. des.
    eexists _, _, _, _, _, _. splits.
    + econs 2; [|econs 1]. econs 2. econs 3; eauto. econs.
      erewrite <- RegFile.eq_except_value; eauto.
      * econs.
      * symmetry.
        eapply RegFile.eq_except_mon; try apply RegFile.eq_except_singleton.
        ii. apply RegSet.singleton_spec in H. subst.
        apply RegSet.add_spec. auto.
    + econs 2. econs 4; eauto.
      * econs. econs. eauto.
      * s. econs 1; eauto.
        i. destruct ow1; inv ORDW1; inv H.
    + s. eauto.
    + s. left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
  - (* update *)
    exploit sim_local_read; eauto.
    { eapply Local.fulfill_step_future; eauto.
      eapply Local.read_step_future; eauto.
    }
    i. des.
    exploit sim_local_write; eauto.
    { eapply Local.read_step_future; eauto.
      eapply Local.fulfill_step_future; eauto.
      eapply Local.read_step_future; eauto.
    }
    { eapply Local.read_step_future; eauto. }
    i. des.
    exploit reorder_fulfill_read; try apply x1; try apply STEP_SRC; eauto.
    { eapply Local.read_step_future; eauto. }
    i. des.
    exploit reorder_read_read; try apply x0; try apply STEP1; eauto. i. des.
    exploit reorder_fulfill_write; try apply STEP2; try apply STEP_SRC1; eauto.
    { eapply Local.read_step_future; eauto.
      eapply Local.read_step_future; eauto.
    }
    i. des.
    exploit reorder_read_write; try apply STEP3; try apply STEP4; eauto.
    { i. destruct or1; inv ORDR1; inv H0. }
    { eapply Local.read_step_future; eauto. }
    i. des.
    eexists _, _, _, _, _, _. splits.
    + econs 2; [|econs 1]. econs 2. econs 4; eauto. econs. econs.
      erewrite <- RegFile.eq_except_rmw; eauto; try apply RegFile.eq_except_singleton.
      ii. eapply REGS; apply RegSet.add_spec.
      * left. eauto.
      * right. apply RegSet.singleton_spec in LHS. subst. eauto.
    + econs 2. econs 4; try apply STEP7; try apply STEP_SRC0; eauto.
      * econs. econs.
        erewrite RegFile.eq_except_rmw; eauto; try apply RegFile.eq_except_singleton.
        ii. eapply REGS; apply RegSet.add_spec.
        { right. apply RegSet.singleton_spec in LHS. subst. eauto. }
        { left. eauto. }
      * econs 1; eauto.
        i. destruct ow1; inv ORDW1; inv H.
    + eauto.
    + left. eapply paco7_mon; [apply sim_stmts_nil|]; ss.
      apply RegFun.add_add. ii. subst. eapply REGS.
      * apply RegSet.add_spec. left. eauto.
      * apply RegSet.add_spec. left. eauto.
Qed.

Lemma sim_update_sim_thread:
  sim_update <6= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
  - i. inv PR. eapply sim_local_future; try apply LOCAL; eauto.
    + exploit Local.read_step_future; try apply WF_SRC; i.
      { eapply Local.future_read_step; eauto. }
      eapply Local.fulfill_step_future; eauto.
      eapply Local.future_fulfill_step; eauto.
    + exploit Local.read_step_future; try apply WF_SRC0; i.
      { eapply Local.future_read_step; eauto.
        eapply Local.future_read_step; eauto.
      }
      eapply Local.fulfill_step_future; try apply x0.
      eapply Local.future_fulfill_step; eauto.
      eapply Local.future_fulfill_step; eauto.
  - inversion PR. subst. i.
    exploit (progress_step (RegFun.add r1 vret1 rs) i2 nil); eauto.
    i. des; [|by inv STEP; inv STATE; inv INSTR; inv REORDER].
    destruct lc2. exploit sim_update_step; eauto.
    { econs 2. eauto. }
    i. des.
    + exploit internal_step_promise; eauto. i.
      punfold SIM. exploit SIM; eauto; try refl.
      { exploit Thread.rtc_step_future; eauto. s. i. des.
        exploit Thread.step_future; eauto. s. i. des. auto.
      }
      { exploit Thread.internal_step_future; eauto. s. i. des. auto. }
      i. des. exploit PROMISES; eauto. i. des.
      eexists _, _, _. splits; [|eauto].
      etrans; eauto.
      etrans; [econs 2; eauto|].
      etrans; eauto.
    + inv SIM. inv STEP; inv STATE.
  - ii. exploit sim_update_step; eauto. i. des.
    + eexists _, _, _, _, _, _. splits; eauto.
      left. eapply paco7_mon; eauto. ss.
    + eexists _, _, _, _, _, _. splits; eauto.
Qed.
