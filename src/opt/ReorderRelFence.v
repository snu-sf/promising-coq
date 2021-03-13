From PromisingLib Require Import Axioms.
Require Import Bool.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import Loc.

Require Import Event.
From PromisingLib Require Import Language.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import SimLocalF.
Require Import Compatibility.
Require Import SimThread.

Require Import ReorderStep.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive reorder_release_fenceF: forall (i2:Instr.t), Prop :=
| reorder_release_fenceF_load
    r2 l2 o2:
    reorder_release_fenceF (Instr.load r2 l2 o2)
| reorder_release_fenceF_store
    l2 v2 o2
    (ORD2: Ordering.le o2 Ordering.plain \/ Ordering.le Ordering.acqrel o2):
    reorder_release_fenceF (Instr.store l2 v2 o2)
| reorder_release_fenceF_update
    r2 l2 rmw2 or2 ow2
    (ORDW2: Ordering.le ow2 Ordering.plain \/ Ordering.le Ordering.acqrel ow2):
    reorder_release_fenceF (Instr.update r2 l2 rmw2 or2 ow2)
| reorder_release_fenceF_fence:
    reorder_release_fenceF (Instr.fence Ordering.acqrel Ordering.plain)
.

Inductive sim_release_fenceF: forall (st_src:(Language.state lang)) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t)
                        (st_tgt:(Language.state lang)) (lc_tgt:Local.t) (sc1_tgt:TimeMap.t) (mem1_tgt:Memory.t), Prop :=
| sim_relese_fenceF_intro
    rs
    none_for
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    (LOCALF: sim_localF none_for lc1_src lc1_tgt):
    sim_release_fenceF
      (State.mk rs []) lc1_src sc1_src mem1_src
      (State.mk rs [Stmt.instr (Instr.fence Ordering.plain Ordering.acqrel)]) lc1_tgt sc1_tgt mem1_tgt
.

Lemma sim_release_fenceF_step
      st1_src lc1_src sc0_src mem0_src
      st1_tgt lc1_tgt sc0_tgt mem0_tgt
      (SIM: sim_release_fenceF st1_src lc1_src sc0_src mem0_src
                               st1_tgt lc1_tgt sc0_tgt mem0_tgt):
  forall sc1_src sc1_tgt
    mem1_src mem1_tgt
    (SC: TimeMap.le sc1_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
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
    _sim_thread_step lang lang ((sim_thread (sim_terminal eq)) \8/ sim_release_fenceF)
                     st1_src lc1_src sc1_src mem1_src
                     st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  inv SIM; ii.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL];
    try (inv STATE; inv INSTR); ss.
  - (* promise *)
    exploit sim_localF_promise; eauto. i. des.
    esplits.
    + eauto.
    + econs 2. econs 1. econs; eauto.
    + auto.
    + auto.
    + auto.
    + right. econs 1; eauto.
  - (* fence *)
    exploit sim_localF_elimination; try exact SC; eauto. i. des.
    esplits.
    + eauto.
    + econs 1.
    + auto.
    + auto.
    + auto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
Qed.

Lemma sim_release_fenceF_sim_thread:
  sim_release_fenceF <8= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss.
  - i. inv TERMINAL_TGT. inv PR; ss.
  - i. inv PR.
    exploit SimPromises.future; try apply LOCALF; eauto. i. des.
    esplits.
    + etrans.
      { apply Memory.max_timemap_spec; eauto. viewtac. }
      { apply sim_memory_max_timemap; eauto. }
    + eauto.
    + etrans.
      { apply Memory.max_timemap_spec; eauto. viewtac. }
      { apply Memory.future_max_timemap; eauto. }
    + auto.
    + econs.
      { eapply WF_TGT. }
      { eapply TView.future_closed; eauto. apply WF_TGT. }
      { apply WF2_TGT. }
      { apply WF2_TGT. }
    + apply Memory.max_timemap_closed. viewtac.
    + auto.
  - i. inv PR.
    esplits; eauto.
    eapply sim_localF_memory_bot; eauto.
  - ii. exploit sim_release_fenceF_step; try apply PR; try apply SC; eauto. i. des.
    + esplits; eauto.
      left. eapply paco9_mon; eauto. ss.
    + esplits; eauto.
Qed.

Lemma reorder_release_fenceF_sim_stmts
      i1 (REORDER: reorder_release_fenceF i1):
  sim_stmts eq
            [Stmt.instr (Instr.fence Ordering.plain Ordering.acqrel); Stmt.instr i1]
            [Stmt.instr i1; Stmt.instr (Instr.fence Ordering.plain Ordering.acqrel)]
            eq.
Proof.
  pcofix CIH. ii. subst. pfold. ii. splits; ii.
  { inv TERMINAL_TGT. }
  { exploit SimPromises.future; try apply LOCAL; eauto. i. des.
    esplits; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply sim_memory_max_timemap; eauto.
    - etrans.
      + apply Memory.max_timemap_spec; eauto. viewtac.
      + apply Memory.future_max_timemap; eauto.
    - apply Memory.max_timemap_closed. viewtac.
  }
  { esplits; eauto.
    inv LOCAL. apply SimPromises.sem_bot_inv in PROMISES; auto. rewrite PROMISES. auto.
  }
  inv STEP_TGT.
  { (* promise *)
    inv STEP.
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto.
    - econs 2. econs 1; eauto. econs; eauto.
  }
  exploit sim_localF_introduction; eauto. i. des.
  exploit sim_localF_nonsynch_src; try exact SC_SRC; eauto. i. des.
  exploit Thread.rtc_tau_step_future; eauto. s. i. des.
  exploit sim_localF_fence_src; eauto. i. des.
  exploit Local.fence_step_future; eauto. i. des.
  inv STEP. inv LOCAL1; inv STATE; inv INSTR; inv REORDER.
  - (* load *)
    exploit sim_localF_read; eauto; try refl. i. des.
    esplits.
    + etrans; [eauto|]. econs 2; [|refl]. econs.
      * econs. econs 2. econs; [|econs 5]; eauto. econs. econs.
      * ss.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs.
    + auto.
    + etrans; eauto.
    + auto.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
      econs. eauto.
  - (* update-load *)
    guardH ORDW2.
    exploit sim_localF_read; eauto; try refl. i. des.
    esplits.
    + etrans; [eauto|]. econs 2; [|refl]. econs.
      * econs. econs 2. econs; [|econs 5]; eauto. econs. econs.
      * ss.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs. eauto.
    + auto.
    + etrans; eauto.
    + auto.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
      econs. eauto.
  - (* write *)
    guardH ORD2.
    hexploit sim_localF_write; try exact SC; eauto;
      (try refl); (try by econs). i. des.
    esplits.
    + etrans; [eauto|]. econs 2; [|refl]. econs.
      * econs. econs 2. econs; [|econs 5]; eauto. econs. econs.
      * ss.
    + econs 2. econs 2. econs; [|econs 3]; eauto. econs. econs.
      replace sc2_src with sc1_src; eauto. apply TimeMap.antisym; ss.
    + auto.
    + auto.
    + auto.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
      econs. eauto.
  - (* update *)
    guardH ORDW2.
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_localF_read; eauto; try refl. i. des.
    exploit Local.read_step_future; eauto. i. des.
    hexploit sim_localF_write; try exact SC; eauto;
      (try refl); (try by econs). i. des.
    esplits.
    + etrans; [eauto|]. econs 2; [|refl]. econs.
      * econs. econs 2. econs; [|econs 5]; eauto. econs. econs.
      * ss.
    + econs 2. econs 2. econs; [|econs 4]; eauto.
      * econs. econs. eauto.
      * replace sc2_src with sc1_src; eauto. apply TimeMap.antisym; ss.
    + auto.
    + auto.
    + auto.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
      econs. eauto.
  - (* fence *)
    exploit sim_localF_fence; try exact SC; eauto; try refl. i. des.
    esplits.
    + etrans; [eauto|]. econs 2; [|refl]. econs.
      * econs. econs 2. econs; [|econs 5]; eauto. econs. econs.
      * ss.
    + econs 2. econs 2. econs; [|econs 5]; eauto.
      * econs. econs.
      * replace sc2_src with sc1_src; eauto. apply TimeMap.antisym; ss.
    + auto.
    + auto.
    + auto.
    + left. eapply paco9_mon; [apply sim_release_fenceF_sim_thread|]; ss.
      econs. eauto.
Qed.
