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

Require Import FulfillStep.
Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import Compatibility.
Require Import SimThread.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive split_release: forall (i1 i2:Instr.t), Prop :=
| split_release_store
    l v:
    split_release (Instr.store l v Ordering.acqrel) (Instr.store l v Ordering.relaxed)
| split_release_update
    r l rmw or:
    split_release (Instr.update r l rmw or Ordering.acqrel) (Instr.update r l rmw or Ordering.relaxed)
.

Inductive sim_released: forall (st_src:lang.(Language.state)) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t)
                          (st_tgt:lang.(Language.state)) (lc_tgt:Local.t) (sc1_tgt:TimeMap.t) (mem1_tgt:Memory.t), Prop :=
| sim_released_intro
    i_src i_tgt rs
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    (SPLIT: split_release i_src i_tgt)
    (LOCAL: sim_local lc1_src lc1_tgt)
    (RELEASED: forall l, View.le lc1_tgt.(Local.tview).(TView.cur) (lc1_tgt.(Local.tview).(TView.rel) l))
    (SC: TimeMap.le sc1_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt):
    sim_released
      (State.mk rs [Stmt.instr i_src]) lc1_src sc1_src mem1_src
      (State.mk rs [Stmt.instr i_tgt]) lc1_tgt sc1_tgt mem1_tgt
.

Lemma sim_released_mon
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      sc2_tgt mem2_tgt
      (SIM1: sim_released st_src lc_src sc1_src mem1_src
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
  sim_released st_src lc_src sc2_src mem2_src
               st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  inv SIM1. econs; eauto.
Qed.

Lemma sim_released_future
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (SIM1: sim_released st_src lc_src sc1_src mem1_src
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
    <<SIM2: sim_released st_src lc'_src sc2_src mem2_src
                         st_tgt lc_tgt sc2_tgt mem2_tgt>>.
Proof.
  inv SIM1.
  exploit SimPromises.future; try apply MEM1; eauto.
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

Lemma sim_local_fulfill_released
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      loc from to val releasedm_src releasedm_tgt released
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_WF: View.opt_wf releasedm_src)
      (RELM_CLOSED: Memory.closed_opt_view releasedm_src mem1_src)
      (WF_RELM_TGT: View.opt_wf releasedm_tgt)
      (STEP_TGT: fulfill_step lc1_tgt sc1_tgt loc from to val releasedm_tgt released Ordering.relaxed lc2_tgt sc2_tgt)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src sc2_src,
    <<STEP_SRC: fulfill_step lc1_src sc1_src loc from to val releasedm_src released Ordering.acqrel lc2_src sc2_src>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>>.
Proof.
  inv STEP_TGT.
  assert (RELT_LE:
   View.opt_le
     (TView.write_released lc1_src.(Local.tview) sc1_src loc to releasedm_src Ordering.acqrel)
     (TView.write_released lc1_tgt.(Local.tview) sc1_tgt loc to releasedm_tgt Ordering.relaxed)).
  { apply TViewFacts.write_released_mon; ss.
    - apply LOCAL1.
    - apply WF1_TGT.
    - admit.
  }
  assert (RELT_WF:
   View.opt_wf (TView.write_released lc1_src.(Local.tview) sc1_src loc to releasedm_src Ordering.acqrel)).
  { unfold TView.write_released. condtac; econs.
    repeat (try condtac; viewtac; try apply WF1_SRC).
  }
  exploit SimPromises.remove_bot; try exact REMOVE;
    try exact MEM1; try apply LOCAL1; eauto.
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  { apply WF1_TGT. }
  i. des. esplits.
  - econs; eauto.
    + etrans; eauto.
    + eapply TViewFacts.writable_mon; eauto. apply LOCAL1.
      admit.
  - econs; eauto. s. apply TViewFacts.write_tview_mon; auto.
    + apply LOCAL1.
    + apply WF1_TGT.
    + admit.
  - apply TViewFacts.write_sc_mon; auto.
    admit.
Admitted.

Lemma sim_local_write_released
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt mem2_tgt
      loc from to val releasedm_src releasedm_tgt released_tgt kind
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_SRC_WF: View.opt_wf releasedm_src)
      (RELM_SRC_CLOSED: Memory.closed_opt_view releasedm_src mem1_src)
      (RELM_TGT_WF: View.opt_wf releasedm_tgt)
      (RELM_TGT_CLOSED: Memory.closed_opt_view releasedm_tgt mem1_tgt)
      (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt Ordering.relaxed lc2_tgt sc2_tgt mem2_tgt kind)
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists released_src lc2_src sc2_src mem2_src,
    <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val releasedm_src released_src Ordering.acqrel lc2_src sc2_src mem2_src kind>> /\
    <<REL2: View.opt_le released_src released_tgt>> /\
    <<LOCAL2: sim_local lc2_src lc2_tgt>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit sim_local_promise; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit sim_local_fulfill_released; try apply STEP2;
    try apply LOCAL2; try apply MEM2; eauto.
  { eapply Memory.future_closed_opt_view; eauto. }
  i. des.
  exploit promise_fulfill_write; try exact STEP_SRC; try exact STEP_SRC0; eauto.
  { admit. }
  i. des. esplits; eauto. etrans; eauto.
Admitted.

Lemma sim_released_step
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      (SIM: sim_released st1_src lc1_src sc1_src mem1_src
                         st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  _sim_thread_step lang lang ((sim_thread (sim_terminal eq)) \8/ sim_released)
                   st1_src lc1_src sc1_src mem1_src
                   st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  inv SIM. ii.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR; inv SPLIT); ss.
  - (* promise *)
    exploit Local.promise_step_future; eauto. i. des.
    exploit sim_local_promise; eauto. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    esplits; try apply SC; eauto.
    + econs 2. econs. econs; eauto.
    + eauto.
    + right. econs; eauto.
      inv LOCAL0. ss.
  - (* update-load *)
    exploit sim_local_read; (try by etrans; eauto); eauto; try refl. i. des.
    esplits; eauto.
    + econs 2. econs 2. econs; [|econs 2]; eauto. econs. econs. eauto.
    + eauto.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
  - (* write *)
    hexploit sim_local_write; (try by etrans; eauto); eauto; try refl; try by econs. i. des.
    esplits; eauto.
    + econs 2. econs 2. econs; [|econs 3]; eauto. econs. admit.
    + ss.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
  - (* update *)
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read; (try by etrans; eauto); eauto; try refl; try by econs. i. des.
    exploit Local.read_step_future; eauto. i. des.
    hexploit sim_local_write; (try by etrans; eauto); eauto; try refl; try by econs. i. des.
    esplits; eauto.
    + econs 2. econs 2. econs; [|econs 4]; eauto. econs. admit.
    + ss.
    + left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
Admitted.

Lemma sim_released_sim_thread:
  sim_released <8= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  - inv TERMINAL_TGT. inv PR; ss.
  - exploit sim_released_mon; eauto. i. des.
    exploit sim_released_future; try apply x8; eauto. i. des.
    esplits; eauto.
  - esplits; eauto.
    inv PR. eapply sim_local_memory_bot; eauto.
  - exploit sim_released_mon; eauto. i. des.
    exploit sim_released_step; eauto. i. des.
    + esplits; eauto.
      left. eapply paco9_mon; eauto. ss.
    + esplits; eauto.
Qed.

Lemma split_release_sim_stmts
      i_src i_tgt
      (SPLIT: split_release i_src i_tgt):
  sim_stmts eq
            [Stmt.instr i_src]
            [Stmt.instr (Instr.fence Ordering.plain Ordering.acqrel); Stmt.instr i_tgt]
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
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR; inv REORDER); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* fence *)
    inv STATE. inv INSTR.
    exploit Local.fence_step_future; eauto. i. des.
    esplits.
    + eauto.
    + econs 1.
    + ss.
    + inv LOCAL1. ss.
    + ss.
    + left. eapply paco9_mon; [apply sim_released_sim_thread|]; ss.
      inv LOCAL1. econs; eauto.
      * inv LOCAL. econs; ss. etrans; eauto.
      * s. i. repeat condtac; ss. refl.
Qed.
