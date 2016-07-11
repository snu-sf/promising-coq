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
Require Import Progress.

Require Import FulfillStep.
Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import Compatibility.
Require Import Simulation.

Require Import ReorderStep.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive reorder_update r1 l1 rmw1 or1 ow1: forall (i2:Instr.t), Prop :=
| reorder_update_load
    r2 l2 o2
    (ORDW1: Ordering.le ow1 Ordering.relaxed)
    (ORD2: Ordering.le o2 Ordering.relaxed)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.update r1 l1 rmw1 or1 ow1))
                           (Instr.regs_of (Instr.load r2 l2 o2))):
    reorder_update r1 l1 rmw1 or1 ow1 (Instr.load r2 l2 o2)
| reorder_update_store
    l2 v2 o2
    (ORDW1: Ordering.le ow1 Ordering.relaxed)
    (ORD2: Ordering.le or1 Ordering.acqrel \/ Ordering.le o2 Ordering.acqrel)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.update r1 l1 rmw1 or1 ow1))
                           (Instr.regs_of (Instr.store l2 v2 o2))):
    reorder_update r1 l1 rmw1 or1 ow1 (Instr.store l2 v2 o2)
| reorder_update_update
    r2 l2 rmw2 or2 ow2
    (ORDW1: Ordering.le ow1 Ordering.relaxed)
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (ORDW2: Ordering.le or1 Ordering.acqrel \/ Ordering.le ow2 Ordering.acqrel)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.update r1 l1 rmw1 or1 ow1))
                           (Instr.regs_of (Instr.update r2 l2 rmw2 or2 ow2))):
    reorder_update r1 l1 rmw1 or1 ow1 (Instr.update r2 l2 rmw2 or2 ow2)
.

Inductive sim_update: forall (st_src:lang.(Language.state)) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t)
                        (st_tgt:lang.(Language.state)) (lc_tgt:Local.t) (sc1_tgt:TimeMap.t) (mem1_tgt:Memory.t), Prop :=
| sim_update_intro
    r1 l1 from1 to1 vr1 vret1 vw1 releasedr1 releasedw1 rmw1 or1 ow1 i2 rs
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    lc2_src
    lc3_src sc3_src
    (RMW: RegFile.eval_rmw rs rmw1 vr1 = (vret1, vw1))
    (REORDER: reorder_update r1 l1 rmw1 or1 ow1 i2)
    (READ: Local.read_step lc1_src mem1_src l1 from1 vr1 releasedr1 or1 lc2_src)
    (FULFILL: fulfill_step lc2_src sc1_src l1 from1 to1 vw1 releasedr1 releasedw1 ow1 lc3_src sc3_src)
    (LOCAL: sim_local lc3_src lc1_tgt)
    (SC: TimeMap.le sc3_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt):
    sim_update
      (State.mk rs [Stmt.instr i2; Stmt.instr (Instr.update r1 l1 rmw1 or1 ow1)]) lc1_src sc1_src mem1_src
      (State.mk (RegFun.add r1 vret1 rs) [Stmt.instr i2]) lc1_tgt sc1_tgt mem1_tgt
.

Lemma sim_update_mon
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      sc2_tgt mem2_tgt
      (SIM1: sim_update st_src lc_src sc1_src mem1_src
                       st_tgt lc_tgt sc1_tgt mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
      (SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt)
      (MEM_FUTURE_SRC: Memory.future mem1_src mem2_src)
      (MEM_FUTURE_TGT: Memory.future mem1_tgt mem2_tgt)
      (SC1: TimeMap.le sc2_src sc2_tgt)
      (MEM1: sim_memory mem2_src mem2_tgt)
      (WF_SRC: Local.wf lc_src mem2_src)
      (WF_TGT: Local.wf lc_tgt mem2_tgt)
      (SC_SRC: Memory.closed_timemap sc2_src mem2_src)
      (SC_TGT: Memory.closed_timemap sc2_tgt mem2_tgt)
      (MEM_SRC: Memory.closed mem2_src)
      (MEM_TGT: Memory.closed mem2_tgt):
  sim_update st_src lc_src sc2_src mem2_src
             st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  inv SIM1.
  exploit Local.read_step_future; eauto. i. des.
  exploit future_read_step; try exact READ; eauto. i. des.
  exploit Local.read_step_future; eauto. i. des.
  exploit future_fulfill_step; try exact FULFILL; eauto.
  { by inv REORDER. }
  i. des.
  exploit sim_local_fulfill; try apply x0; try exact LOCAL0; try refl;
    try exact WF0; try by viewtac.
  { econs.
    - apply WF2.
    - eapply TView.future_closed; eauto. apply WF2.
    - inv READ. apply WF_SRC.
  }
  i. des.
  econs; eauto.
  - etrans; eauto.
  - etrans; eauto.
Qed.

Lemma sim_update_future
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (SIM1: sim_update st_src lc_src sc1_src mem1_src
                       st_tgt lc_tgt sc1_tgt mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
      (MEM_FUTURE_SRC: Memory.future mem1_src mem2_src)
      (WF_SRC: Local.wf lc_src mem2_src)
      (SC_SRC: Memory.closed_timemap sc2_src mem2_src)
      (MEM_SRC: Memory.closed mem2_src):
  exists lc'_src sc2_tgt mem2_tgt,
    <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>> /\
    <<SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt>> /\
    <<MEM_FUTURE_TGT: Memory.future mem1_tgt mem2_tgt>> /\
    <<WF_TGT: Local.wf lc_tgt mem2_tgt>> /\
    <<SC_TGT: Memory.closed_timemap sc2_tgt mem2_tgt>> /\
    <<MEM_TGT: Memory.closed mem2_tgt>> /\
    <<SIM2: sim_update st_src lc'_src sc2_src mem2_src
                       st_tgt lc_tgt sc2_tgt mem2_tgt>>.
Proof.
  inv SIM1.
  exploit Local.read_step_future; eauto. i. des.
  exploit fulfill_step_future; eauto; try by viewtac. i. des.
  exploit future_read_step; try exact READ; eauto. i. des.
  exploit Local.read_step_future; eauto. i. des.
  exploit future_fulfill_step; try exact FULFILL; eauto; try refl; try by viewtac.
  { by inv REORDER. }
  i. des.
  exploit fulfill_step_future; try apply x0; try exact WF1; eauto; try by viewtac.
  { econs.
    - apply WF2.
    - eapply TView.future_closed; eauto. apply WF2.
    - inv READ. apply WF_SRC.
  }
  i. des.
  exploit sim_local_fulfill; try exact x0; try exact LOCAL0; try refl; eauto.
  { econs.
    - apply WF2.
    - eapply TView.future_closed; eauto. apply WF2.
    - inv READ. apply WF_SRC.
  }
  i. des.
  exploit fulfill_step_future; eauto. i. des.
  exploit sim_local_future; try apply MEM1; eauto.
  { inv LOCAL. apply SimPromises.sem_bot_inv in PROMISES; auto. rewrite <- PROMISES.
    apply SimPromises.sem_bot.
  }
  i. des. esplits.
  - etrans.
    + apply Memory.max_timemap_spec; eauto. viewtac.
    + apply sim_memory_max_timemap; eauto.
  - eauto.
  - etrans.
    + apply Memory.max_timemap_spec; eauto. viewtac.
    + apply Memory.future_max_timemap; eauto.
  - auto.
  - auto.
  - apply Memory.max_timemap_closed. viewtac.
  - auto.
  - econs; eauto.
    + etrans; eauto.
    + etrans.
      * apply Memory.max_timemap_spec; eauto. viewtac.
      * apply sim_memory_max_timemap; eauto.
    + apply Memory.max_timemap_closed. viewtac.
Qed.

Lemma sim_update_step
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      (SIM: sim_update st1_src lc1_src sc1_src mem1_src
                       st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  _sim_thread_step lang lang ((sim_thread (sim_terminal eq)) \8/ sim_update)
                   st1_src lc1_src sc1_src mem1_src
                   st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  inv SIM. ii.
  exploit Local.read_step_future; eauto. i. des.
  exploit fulfill_step_future; eauto. i. des.
  inv STEP_TGT; inv STEP; try (inv STATE; inv INSTR; inv REORDER); ss.
  - (* promise *)
    exploit Local.promise_step_future; eauto. i. des.
    exploit sim_local_promise; try apply LOCAL0; (try by etrans; eauto); eauto. i. des.
    exploit reorder_update_promise; try exact READ; try exact FULFILL; try exact STEP_SRC; eauto. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    esplits.
    + eauto.
    + econs 2. econs 1. econs; eauto.
    + auto.
    + etrans; eauto.
    + auto.
    + right. econs; eauto.
      * etrans; eauto.
      * etrans; eauto.
      * eapply Memory.future_closed_timemap; eauto.
  - (* load *)
    apply RegSet.disjoint_add in REGS. des.
    exploit sim_local_read; try apply LOCAL0; (try by etrans; eauto); eauto; try refl. i. des.
    exploit reorder_update_read; try exact FULFILL; try exact READ; try exact STEP_SRC; eauto. i. des.
    exploit Local.read_step_future; try exact STEP1; eauto. i. des.
    exploit Local.read_step_future; try exact STEP2; eauto. i. des.
    exploit fulfill_write; eauto. i. des.
    esplits.
    + econs 2; eauto. econs.
      * econs 2. econs 2; eauto. econs. econs.
      * auto.
    + econs 2. econs 2. econs 4; eauto. econs. econs.
      erewrite RegFile.eq_except_rmw; eauto.
      * symmetry. eauto.
      * apply RegFile.eq_except_singleton.
    + auto.
    + auto.
    + etrans; eauto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
      apply RegFun.add_add. ii. subst. eapply REGS.
      apply RegSet.Facts.singleton_iff. auto.
  - (* store *)
    guardH ORD2.
    apply RegSet.disjoint_add in REGS. des.
    hexploit sim_local_write; try exact LOCAL0; try exact LOCAL; try exact SC; try exact WF0; try refl; eauto; try by viewtac. i. des.
    hexploit reorder_update_write; try exact READ; try exact FULFILL; try exact STEP_SRC; eauto; try by viewtac.
    { ii. subst. inv FULFILL. eapply Time.lt_strorder. eauto. }
    i. des.
    exploit Local.write_step_future; try exact STEP1; eauto; try by viewtac. i. des.
    exploit Local.read_step_future; try exact STEP2; eauto; try by viewtac. i. des.
    exploit fulfill_write; eauto. i. des.
    esplits.
    + econs 2; eauto. econs.
      * econs 2. econs 3; eauto. econs.
        erewrite RegFile.eq_except_value; cycle 2.
        { apply RegFile.eq_except_singleton. }
        { econs. }
        { ii. apply RegSet.singleton_spec in LHS. subst. congr. }
      * auto.
    + econs 2. econs 2. econs 4; eauto. econs. econs. eauto.
    + auto.
    + etrans; eauto.
    + etrans; eauto. etrans; eauto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
      etrans; eauto.
  - (* update *)
    guardH ORDW2.
    apply RegSet.disjoint_add in REGS. des.
    symmetry in REGS0. apply RegSet.disjoint_add in REGS0. des.
    exploit fulfill_step_future; try exact FULFILL; eauto; try by viewtac. i. des.
    exploit Local.read_step_future; try exact LOCAL1; eauto; try by viewtac. i. des.
    exploit sim_local_read; try exact LOCAL1; (try by etrans; eauto); eauto; try refl. i. des.
    exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
    hexploit sim_local_write; try exact LOCAL2; eauto; try refl; try by viewtac. i. des.
    hexploit ReorderStep.reorder_update_update; try exact FULFILL; try exact READ; try exact STEP_SRC0; eauto.
    { ii. subst. inv FULFILL. eapply Time.lt_strorder. eauto. }
    i. des.
    exploit Local.read_step_future; try exact STEP1; eauto. i. des.
    exploit Local.write_step_future; try exact STEP2; eauto. i. des.
    exploit Local.read_step_future; try exact STEP3; eauto. i. des.
    exploit fulfill_write; eauto. i. des.
    esplits.
    + econs 2; eauto. econs.
      * econs 2. econs 4; eauto. econs. econs.
        erewrite RegFile.eq_except_rmw; eauto; cycle 1.
        { symmetry. apply RegFile.eq_except_singleton. }
        { ii. apply RegSet.singleton_spec in LHS. subst. contradict REGS. apply RegSet.add_spec. auto. }
      * auto.
    + econs 2. econs 2. econs 4; eauto. econs. econs.
      erewrite RegFile.eq_except_rmw; cycle 2.
      * apply RegFile.eq_except_singleton.
      * eauto.
      * ii. apply RegSet.singleton_spec in LHS. subst. congr.
    + auto.
    + etrans; eauto.
    + etrans; eauto. etrans; eauto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
      * apply RegFun.add_add. ii. subst. apply REGS. apply RegSet.add_spec. auto.
      * etrans; eauto.
Qed.

Lemma sim_update_sim_thread:
  sim_update <8= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  - inv TERMINAL_TGT. inv PR; ss.
  - exploit sim_update_mon; eauto. i. des.
    exploit sim_update_future; try apply x8; eauto. i. des.
    esplits; eauto.
  - exploit sim_update_mon; eauto. i.
    inversion x8. subst. i.
    exploit (progress_program_step (RegFun.add r1 (fst (RegFile.eval_rmw rs rmw1 vr1)) rs) i2 nil); eauto. i. des.
    destruct th2. exploit sim_update_step; eauto.
    { rewrite RMW in *. ss. econs 2. eauto. }
    i. des.
    + exploit program_step_promise; eauto. i.
      exploit Thread.rtc_step_future; eauto. s. i. des.
      exploit Thread.opt_step_future; eauto. s. i. des.
      exploit Thread.program_step_future; eauto. s. i. des.
      punfold SIM. exploit SIM; try apply SC3; eauto; try refl. s. i. des.
      exploit PROMISES; eauto. i. des.
      esplits; [|eauto].
	    etrans; eauto. etrans; [|eauto].
      inv STEP_SRC; eauto. econs 2; eauto. econs; eauto. etrans; eauto.
      destruct e; by inv STEP; inv STATE; inv INSTR; inv REORDER.
    + inv SIM. inv STEP; inv STATE.
  - exploit sim_update_mon; eauto. i. des.
    exploit sim_update_step; eauto. i. des.
    + esplits; eauto.
      left. eapply paco9_mon; eauto. ss.
    + esplits; eauto.
Qed.
