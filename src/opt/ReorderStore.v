Require Import Bool.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
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
Require Import SimThread.

Require Import ReorderStep.
Require Import ProgressStep.

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
    (LOC: l1 <> l2):
    reorder_store l1 v1 o1 (Instr.store l2 v2 o2)
| reorder_store_update
    r2 l2 rmw2 or2 ow2
    (ORD1: Ordering.le o1 Ordering.relaxed)
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.store l1 v1 o1)) (RegSet.singleton r2)):
    reorder_store l1 v1 o1 (Instr.update r2 l2 rmw2 or2 ow2)
.

Inductive sim_store: forall (st_src:lang.(Language.state)) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t)
                       (st_tgt:lang.(Language.state)) (lc_tgt:Local.t) (sc1_tgt:TimeMap.t) (mem1_tgt:Memory.t), Prop :=
| sim_store_intro
    l1 f1 t1 v1 released1 o1 i2 rs
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    lc2_src sc2_src
    (REORDER: reorder_store l1 v1 o1 i2)
    (FULFILL: fulfill_step lc1_src sc1_src l1 f1 t1 (RegFile.eval_value rs v1) None released1 o1 lc2_src sc2_src)
    (LOCAL: sim_local lc2_src lc1_tgt)
    (SC: TimeMap.le sc2_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt):
    sim_store
      (State.mk rs [Stmt.instr i2; Stmt.instr (Instr.store l1 v1 o1)]) lc1_src sc1_src mem1_src
      (State.mk rs [Stmt.instr i2]) lc1_tgt sc1_tgt mem1_tgt
.

Lemma sim_store_mon
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      sc2_tgt mem2_tgt
      (SIM1: sim_store st_src lc_src sc1_src mem1_src
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
  sim_store st_src lc_src sc2_src mem2_src
            st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  inv SIM1. exploit future_fulfill_step; try exact FULFILL; eauto; try refl.
  { by inv REORDER. }
  i. des. econs; eauto.
Qed.

Lemma sim_store_future
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (SIM1: sim_store st_src lc_src sc1_src mem1_src
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
    <<SIM2: sim_store st_src lc'_src sc2_src mem2_src
                      st_tgt lc_tgt sc2_tgt mem2_tgt>>.
Proof.
  inv SIM1.
  exploit fulfill_step_future; eauto; try by viewtac. i. des.
  exploit fulfill_step_future; try exact WF_SRC; eauto; try by viewtac. i. des.
  exploit future_fulfill_step; try exact FULFILL; eauto; try refl; try by viewtac.
  { by inv REORDER. }
  i. des.
  exploit SimPromises.future; try exact MEM1; eauto.
  { inv LOCAL. apply SimPromises.sem_bot_inv in PROMISES; auto. rewrite <- PROMISES.
    apply SimPromises.sem_bot.
  }
  i. des. esplits; eauto.
  - etrans.
    + apply Memory.max_timemap_spec; eauto. viewtac.
    + apply sim_memory_max_timemap; eauto.
  - etrans.
    + apply Memory.max_timemap_spec; eauto. viewtac.
    + apply Memory.future_max_timemap; eauto.
  - apply Memory.max_timemap_closed. viewtac.
  - econs; eauto.
    + etrans.
      * apply Memory.max_timemap_spec; eauto. viewtac.
      * apply sim_memory_max_timemap; eauto.
    + apply Memory.max_timemap_closed. viewtac.
Qed.

Lemma sim_store_step
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      (SIM: sim_store st1_src lc1_src sc1_src mem1_src
                      st1_tgt lc1_tgt sc1_tgt mem1_tgt):
    _sim_thread_step lang lang ((sim_thread (sim_terminal eq)) \8/ sim_store)
                     st1_src lc1_src sc1_src mem1_src
                     st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  inv SIM. ii.
  exploit fulfill_step_future; eauto; try viewtac. i. des.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR; inv REORDER); ss.
  - (* promise *)
    exploit Local.promise_step_future; eauto. i. des.
    exploit sim_local_promise; try exact LOCAL0; (try by etrans; eauto); eauto. i. des.
    exploit reorder_fulfill_promise; try exact FULFILL; try exact STEP_SRC; eauto. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    esplits.
    + eauto.
    + econs 2. econs 1. econs; eauto.
    + auto.
    + etrans; eauto.
    + auto.
    + right. econs; eauto.
      eapply Memory.future_closed_timemap; eauto.
  - (* load *)
    exploit sim_local_read; try exact LOCAL0; (try by etrans; eauto); eauto; try refl. i. des.
    exploit reorder_fulfill_read; try exact FULFILL; try exact STEP_SRC; eauto. i. des.
    exploit Local.read_step_future; try exact STEP1; eauto. i. des.
    exploit fulfill_write; eauto; try by viewtac. i. des.
    esplits.
    + econs 2; eauto. econs.
      * econs. econs 2. econs; [|econs 2]; eauto. econs. econs.
      * auto.
    + econs 2. econs 2. econs; [|econs 3]; eauto. econs.
      erewrite <- RegFile.eq_except_value; eauto.
      * econs.
      * symmetry. eauto.
      * apply RegFile.eq_except_singleton.
    + auto.
    + auto.
    + etrans; eauto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
  - (* update-load *)
    exploit sim_local_read; try exact LOCAL0; (try by etrans; eauto); eauto; try refl. i. des.
    exploit reorder_fulfill_read; try exact FULFILL; try exact STEP_SRC; eauto. i. des.
    exploit Local.read_step_future; try exact STEP1; eauto. i. des.
    exploit fulfill_write; eauto; try by viewtac. i. des.
    esplits.
    + econs 2; eauto. econs.
      * econs. econs 2. econs; [|econs 2]; eauto. econs. econs. eauto.
      * auto.
    + econs 2. econs 2. econs; [|econs 3]; eauto. econs.
      erewrite <- RegFile.eq_except_value; eauto.
      * econs.
      * symmetry. eauto.
      * apply RegFile.eq_except_singleton.
    + auto.
    + auto.
    + etrans; eauto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
  - (* store *)
    hexploit sim_local_write; try exact LOCAL1; eauto; try refl; try by viewtac. i. des.
    exploit reorder_fulfill_write; try exact FULFILL; try exact STEP_SRC; eauto; try by viewtac. i. des.
    exploit Local.write_step_future; try exact STEP1; eauto; try by viewtac. i. des.
    exploit fulfill_write; eauto; try by viewtac. i. des.
    esplits.
    + econs 2; eauto. econs.
      * econs. econs 2. econs; [|econs 3]; eauto. econs. econs.
      * auto.
    + econs 2. econs 2. econs; [|econs 3]; eauto. econs. econs.
    + auto.
    + etrans; eauto.
    + etrans; eauto. etrans; eauto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
      etrans; eauto.
  - (* update *)
    exploit fulfill_step_future; try exact FULFILL; eauto; try by viewtac. i. des.
    exploit Local.read_step_future; try exact LOCAL1; eauto; try by viewtac. i. des.
    exploit sim_local_read; try exact LOCAL1; (try by etrans; eauto); eauto; try refl. i. des.
    exploit Local.read_step_future; try exact STEP_SRC; eauto. i. des.
    hexploit sim_local_write; try exact LOCAL2; eauto; try refl; try by viewtac. i. des.
    hexploit reorder_fulfill_update; try exact FULFILL; try exact STEP_SRC; try exact STEP_SRC0; eauto; try by viewtac. i. des.
    exploit Local.read_step_future; try apply STEP1; eauto. i. des.
    exploit Local.write_step_future; try apply STEP2; eauto. i. des.
    exploit fulfill_write; eauto; try exact STEP3; try by viewtac. i. des.
    esplits.
    + econs 2; eauto. econs.
      * econs. econs 2. econs; [|econs 4]; eauto. econs. econs. eauto.
      * auto.
    + econs 2. econs 2. econs; [|econs 3]; eauto. econs.
      erewrite <- RegFile.eq_except_value; eauto.
      * econs.
      * symmetry. eauto.
      * apply RegFile.eq_except_singleton.
    + auto.
    + etrans; eauto.
    + etrans; eauto. etrans; eauto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
      etrans; eauto.
Qed.

Lemma sim_store_sim_thread:
  sim_store <8= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  - inv TERMINAL_TGT. inv PR; ss.
  - exploit sim_store_mon; eauto. i.
    exploit sim_store_future; try apply x0; eauto. i. des.
    esplits; eauto.
  - exploit sim_store_mon; eauto. i.
    inversion x0. subst. i.
    exploit (progress_program_step rs i2 nil); eauto. i. des.
    destruct th2. exploit sim_store_step; eauto.
    { econs 2. eauto. }
    i. des.
    + exploit program_step_promise; eauto. i.
      exploit Thread.rtc_tau_step_future; eauto. s. i. des.
      exploit Thread.opt_step_future; eauto. s. i. des.
      exploit Thread.program_step_future; eauto. s. i. des.
      punfold SIM. exploit SIM; try apply SC3; eauto; try refl. s. i. des.
      exploit PROMISES; eauto. i. des.
      esplits; [|eauto].
	    etrans; eauto. etrans; [|eauto].
      inv STEP_SRC; eauto. econs 2; eauto. econs; eauto.
      * econs. eauto.
      * etrans; eauto.
        destruct e; by inv STEP; inv STATE; inv INSTR; inv REORDER.
    + inv SIM. inv STEP; inv STATE.
  - exploit sim_store_mon; eauto. i. des.
    exploit sim_store_step; eauto. i. des.
    + esplits; eauto.
      left. eapply paco9_mon; eauto. ss.
    + esplits; eauto.
Qed.
