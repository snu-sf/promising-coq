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
Require Import ReorderStep.

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
    (ORD: Ordering.le Ordering.seqcst o1 -> Ordering.le Ordering.seqcst o2 -> False)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.load r1 l1 o1))
                           (Instr.regs_of (Instr.store l2 v2 o2))):
    reorder_load r1 l1 o1 (Instr.store l2 v2 o2)
| reorder_load_update
    r2 l2 rmw2 or2 ow2
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (ORDW2: Ordering.le Ordering.seqcst o1 -> Ordering.le Ordering.seqcst ow2 -> False)
    (LOC: l1 <> l2)
    (REGS: RegSet.disjoint (Instr.regs_of (Instr.load r1 l1 o1))
                           (Instr.regs_of (Instr.update r2 l2 rmw2 or2 ow2))):
    reorder_load r1 l1 o1 (Instr.update r2 l2 rmw2 or2 ow2)
| reorder_load_fence
    or2 ow2
    (ORD1: Ordering.le Ordering.relaxed o1)
    (ORDR2: Ordering.le or2 Ordering.relaxed)
    (ORDW2: Ordering.le ow2 Ordering.acqrel)
    (RLX: Ordering.le Ordering.relaxed ow2 -> Ordering.le o1 Ordering.relaxed):
    reorder_load r1 l1 o1 (Instr.fence or2 ow2)
.

Inductive sim_load: forall (st_src:lang.(Language.state)) (lc_src:Local.t) (sc0_src:TimeMap.t) (mem0_src:Memory.t)
                      (st_tgt:lang.(Language.state)) (lc_tgt:Local.t) (sc0_tgt:TimeMap.t) (mem0_tgt:Memory.t), Prop :=
| sim_load_intro
    r1 l1 ts1 v1 released1 o1 i2
    rs lc1_src lc1_tgt lc2_src
    sc0_src sc0_tgt
    mem0_src mem0_tgt
    (REORDER: reorder_load r1 l1 o1 i2)
    (READ: Local.read_step lc1_src mem0_src l1 ts1 v1 released1 o1 lc2_src)
    (SC: TimeMap.le sc0_src sc0_tgt)
    (MEMORY: Memory.sim mem0_tgt mem0_src)
    (WF_SRC: Local.wf lc1_src mem0_src)
    (WF_TGT: Local.wf lc1_tgt mem0_tgt)
    (SC_SRC: Memory.closed_timemap sc0_src mem0_src)
    (SC_TGT: Memory.closed_timemap sc0_tgt mem0_tgt)
    (MEM_SRC: Memory.closed mem0_src)
    (MEM_TGT: Memory.closed mem0_tgt)
    (LOCAL: sim_local lc2_src lc1_tgt):
    sim_load
      (State.mk rs [Stmt.instr i2; Stmt.instr (Instr.load r1 l1 o1)]) lc1_src sc0_src mem0_src
      (State.mk (RegFun.add r1 v1 rs) [Stmt.instr i2]) lc1_tgt sc0_tgt mem0_tgt
.

Lemma sim_load_future
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: Memory.sim mem1_tgt mem1_src)
      (SIM1: sim_load st_src lc_src sc1_src mem1_src
                      st_tgt lc_tgt sc1_tgt mem1_tgt)
      (SC_FUTURE_SRC: TimeMap.le sc1_src sc2_src)
      (MEM_FUTURE_SRC: Memory.future mem1_src mem2_src)
      (WF_SRC: Local.wf lc_src mem2_src)
      (SC_SRC: Memory.closed_timemap sc2_src mem2_src)
      (MEM_SRC: Memory.closed mem2_src):
  exists lc'_src sc2_tgt mem2_tgt,
    <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
    <<MEM2: Memory.sim mem2_tgt mem2_src>> /\
    <<SC_FUTURE_TGT: TimeMap.le sc1_tgt sc2_tgt>> /\
    <<MEM_FUTURE_TGT: Memory.future mem1_tgt mem2_tgt>> /\
    <<WF_TGT: Local.wf lc_tgt mem2_tgt>> /\
    <<SC_TGT: Memory.closed_timemap sc2_tgt mem2_tgt>> /\
    <<MEM_TGT: Memory.closed mem2_tgt>> /\
    <<SIM2: sim_load st_src lc'_src sc2_src mem2_src
                     st_tgt lc_tgt sc2_tgt mem2_tgt>>.
Proof.
  inv SIM1.
  exploit future_read_step; try apply READ; eauto. i. des.
  exploit sim_local_future; try apply MEM1; eauto.
  { inv LOCAL. apply MemInv.sem_bot_inv in PROMISES; auto. rewrite <- PROMISES.
    inv READ. ss. apply MemInv.sem_bot.
  }
  { inv LOCAL. rewrite PROMISES_LE.
    inv READ. ss.
  }
  i. des. esplits; eauto.
  - etrans.
    + apply Memory.max_timemap_spec; eauto. committac.
    + apply Memory.sim_max_timemap; eauto.
  - etrans.
    + apply Memory.max_timemap_spec; eauto. committac.
    + apply Memory.future_max_timemap; eauto.
  - apply Memory.max_timemap_closed. committac.
  - econs; eauto.
    + etrans.
      * apply Memory.max_timemap_spec; eauto. committac.
      * apply Memory.sim_max_timemap; eauto.
    + apply Memory.max_timemap_closed. committac.
    + etrans; eauto.
Qed.

Lemma sim_load_step
      st1_src lc1_src sc0_src mem0_src
      st1_tgt lc1_tgt sc0_tgt mem0_tgt
      (SIM: sim_load st1_src lc1_src sc0_src mem0_src
                     st1_tgt lc1_tgt sc0_tgt mem0_tgt):
  forall sc1_src sc1_tgt mem1_src mem1_tgt
    (SC: TimeMap.le sc1_src sc1_tgt)
    (MEMORY: Memory.sim mem1_tgt mem1_src)
    (SC_FUTURE_SRC: TimeMap.le sc0_src sc1_src)
    (SC_FUTURE_TGT: TimeMap.le sc0_tgt sc1_tgt)
    (MEM_FUTURE_SRC: Memory.future mem0_src mem1_src)
    (MEM_FUTURE_TGT: Memory.future mem0_tgt mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt),
    _sim_thread_step lang lang ((sim_thread (sim_terminal eq)) \8/ sim_load)
                     st1_src lc1_src sc1_src mem1_src
                     st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  ii. exploit sim_load_future; try apply SIM; (try by inv SIM); eauto. i. des.
  inv SIM. exploit future_read_step; try apply READ; eauto. i. des.
  inv STEP_TGT; inv STEP0; try (inv STATE; inv INSTR; inv REORDER); ss.
  - (* promise *)
    exploit Local.promise_step_future; eauto. i. des.
    exploit sim_local_promise; (try by etrans; eauto); eauto.
    { eapply Local.read_step_future; eauto. }
    i. des.
    exploit reorder_read_promise; try apply x0; try apply STEP_SRC; eauto. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    esplits; try apply SC; eauto.
    + econs 2. econs. econs. eauto.
    + eauto.
    + right. econs; eauto. etrans; eauto.
  - (* load *)
    exploit sim_local_read; (try by etrans; eauto); eauto; try refl.
    { eapply Local.read_step_future; eauto. }
    i. des.
    exploit reorder_read_read; try apply STEP; try apply STEP_SRC; eauto. i. des.
    esplits.
    + econs 2; [|econs 1]. econs.
      * econs 2. econs 2; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs 2; eauto. econs. econs.
    + eauto.
    + eauto.
    + eauto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
      apply RegFun.add_add. ii. subst. eapply REGS.
      * apply RegSet.singleton_spec. eauto.
      * apply RegSet.singleton_spec. eauto.
      * etrans; eauto.
  - (* store *)
    exploit sim_local_write; try apply SC; try apply LOCAL1; (try by etrans; eauto); eauto.
    { refl. }
    { apply Capability.bot_wf. }
    { eapply Local.read_step_future; eauto. }
    i. des.
    exploit reorder_read_write; try apply STEP; try apply STEP_SRC; eauto. i. des.
    esplits.
    + econs 2; [|econs 1]. econs.
      * econs 2. econs 3; eauto. econs.
        erewrite RegFile.eq_except_value; eauto.
        { econs. }
        { apply RegFile.eq_except_singleton. }
      * eauto.
    + econs 2. econs 2. econs 2; eauto. econs. econs.
    + eauto.
    + eauto.
    + etrans; eauto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss. etrans; eauto.
  - (* update *)
    exploit sim_local_read; (try by etrans; eauto); eauto; try refl.
    { eapply Local.read_step_future; eauto. }
    i. des.
    exploit reorder_read_read; try apply STEP; try apply STEP_SRC; eauto. i. des.
    exploit sim_local_write; try apply SC; try apply LOCAL1; (try by etrans; eauto); eauto.
    { inv LOCAL1. eapply MEM_TGT; eauto. }
    { eapply Local.read_step_future; eauto.
      eapply Local.read_step_future; eauto.
    }
    { eapply Local.read_step_future; eauto. }
    i. des.
    exploit reorder_read_write; try apply STEP_SRC0; try apply STEP2; eauto.
    { eapply Local.read_step_future; eauto. }
    i. des.
    esplits.
    + econs 2; [|econs 1]. econs.
      * econs 2. econs 4; eauto. econs. econs.
        erewrite <- RegFile.eq_except_rmw; eauto; try apply RegFile.eq_except_singleton.
        ii. eapply REGS; eauto.
        apply RegSet.singleton_spec in LHS. subst.
        apply RegSet.add_spec. auto.
      * eauto.
    + econs 2. econs 2. econs 2; eauto. econs. econs.
    + eauto.
    + eauto.
    + etrans; eauto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
      * apply RegFun.add_add. ii. subst. eapply REGS.
        { apply RegSet.singleton_spec. eauto. }
        { apply RegSet.add_spec. eauto. }
      * etrans; eauto.
  - (* fence *)
    exploit sim_local_fence; try apply SC; try apply LOCAL1; (try by etrans; eauto); eauto; try refl.
    { eapply Local.read_step_future; eauto. }
    i. des.
    exploit reorder_read_fence; try apply x0; try apply STEP_SRC; eauto. i. des.
    esplits.
    + econs 2; [|econs 1]. econs.
      * econs 2. econs 5; eauto. econs. econs.
      * eauto.
    + econs 2. econs 2. econs 2; eauto. econs. econs.
    + eauto.
    + etrans; eauto.
    + eauto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
      etrans; eauto.
Qed.

Lemma sim_load_sim_thread:
  sim_load <8= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
  - i. exploit sim_load_future; try apply PR; (try by inv PR); eauto. i. des.
    exploit sim_load_future; try apply SIM2; auto. ; try apply SC2; eauto.
    { admit. }
    { admit. }
    i. des. esplits. ; eauto.
    ; (try by inv SIM2); eauto. i. des.
    esplits; eauto.
    + eapply Local.read_step_future; eauto.
      eapply Local.future_read_step; eauto.
    + eapply Local.read_step_future; eauto.
      eapply Local.future_read_step; eauto.
      eapply Local.future_read_step; eauto.


  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
  - i.
    exploit future_read_step; try apply READ; eauto. i. des.
    exploit sim_load_future; try apply PR. ; (try by inv PR); eauto. i. des.
    esplits. ; eauto.
    
    exploit sim_local_future; try apply MEM1; eauto.
    { inv LOCAL. apply MemInv.sem_bot_inv in PROMISES; auto. rewrite <- PROMISES.
      inv READ. ss. apply MemInv.sem_bot.
    }
    { inv LOCAL. rewrite PROMISES_LE.
      inv READ. ss.
    }
    {i. des. esplits; eauto.
  - etrans.
    + apply Memory.max_timemap_spec; eauto. committac.
    + apply Memory.sim_max_timemap; eauto. 
  - etrans.
    + apply Memory.max_timemap_spec; eauto. committac.
    + apply Memory.future_max_timemap; eauto.
  - apply Memory.max_timemap_closed. committac.
  - econs; eauto.
    + etrans.
      * apply Memory.max_timemap_spec; eauto. committac.
      * apply Memory.sim_max_timemap; eauto.
    + apply Memory.max_timemap_closed. committac.
    + etrans; eauto.
}

    exploit sim_local_future; try apply LOCAL; eauto.
    { eapply Local.read_step_future; eauto. }
    { admit. }
    i. des. esplits; eauto.
  - i. esplits; eauto.
    inv PR. inv READ. inv LOCAL. ss.
    apply MemInv.sem_bot_inv in PROMISES. rewrite PROMISES. auto.
  - ii. exploit sim_load_step; eauto. i. des.
    + esplits; eauto.
      left. eapply paco7_mon; eauto. ss.
    + esplits; eauto.
Qed.


Lemma sim_load_sim_thread:
  sim_load <8= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
  - i. inv PR.
    exploit future_read_step; try apply MEM_FUTURE_SRC; eauto. i. des.
    rewrite LOCAL in LOCAL0.
    exploit sim_local_future; try apply LOCAL0; eauto.
    { eapply Local.read_step_future; eauto. }
    { exploit future_read_step; try apply STEP; eauto. i. des.
      exploit Local.read_step_future; eauto. i. des.
      
  }
    
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_future; try apply LOCAL0; try apply x0; eauto.
    { 
    etrans. eauto. eauto.
    ; (try by etrans; eauto); eauto. try apply STEP; eauto.
      esplits; eauto.
      - etrans.
        + apply Memory.max_timemap_spec; eauto. committac.
        + apply Memory.sim_max_timemap; eauto.
      - etrans.
        + apply Memory.max_timemap_spec; eauto. committac.
        + apply Memory.future_max_timemap; eauto.
      - apply Memory.max_timemap_closed. committac.
    }
    exploit sim_local_future; try apply LOCAL; eauto.
    + eapply Local.read_step_future; eauto.
      eapply Local.future_read_step; eauto.
    + eapply Local.read_step_future; eauto.
      eapply Local.future_read_step; eauto.
      eapply Local.future_read_step; eauto.
  - i. esplits; eauto.
    inv PR. inv READ. inv LOCAL. ss.
    apply MemInv.sem_bot_inv in PROMISES. rewrite PROMISES. auto.
  - ii. exploit sim_load_step; eauto. i. des.
    + esplits; eauto.
      left. eapply paco9_mon; eauto. ss.
    + esplits; eauto.
Qed.


Lemma sim_load_sim_thread:
  sim_load <8= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
  - i. inv PR.
    exploit future_read_step; try apply MEM_FUTURE_SRC; eauto. i. des.
    rewrite LOCAL in LOCAL0.
    exploit sim_local_future; try apply LOCAL0; eauto.
    { eapply Local.read_step_future; eauto. }
    { exploit future_read_step; try apply STEP; eauto. i. des.
      exploit Local.read_step_future; eauto. i. des.
      
  }
    
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_future; try apply LOCAL0; try apply x0; eauto.
    { 
    etrans. eauto. eauto.
    ; (try by etrans; eauto); eauto. try apply STEP; eauto.
      esplits; eauto.
      - etrans.
        + apply Memory.max_timemap_spec; eauto. committac.
        + apply Memory.sim_max_timemap; eauto.
      - etrans.
        + apply Memory.max_timemap_spec; eauto. committac.
        + apply Memory.future_max_timemap; eauto.
      - apply Memory.max_timemap_closed. committac.
    }
    exploit sim_local_future; try apply LOCAL; eauto.
    + eapply Local.read_step_future; eauto.
      eapply Local.future_read_step; eauto.
    + eapply Local.read_step_future; eauto.
      eapply Local.future_read_step; eauto.
      eapply Local.future_read_step; eauto.
  - i. esplits; eauto.
    inv PR. inv READ. inv LOCAL. ss.
    apply MemInv.sem_bot_inv in PROMISES. rewrite PROMISES. auto.
  - ii. exploit sim_load_step; eauto. i. des.
    + esplits; eauto.
      left. eapply paco9_mon; eauto. ss.
    + esplits; eauto.
Qed.
