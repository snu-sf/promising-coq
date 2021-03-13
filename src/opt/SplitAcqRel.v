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

Require Import FulfillStep.
Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import Compatibility.
Require Import SimThread.

Require Import Syntax.
Require Import Semantics.
Require Import SplitAcq.

Set Implicit Arguments.


Definition local_acqrel (lc:Local.t) :=
  (Local.mk (TView.write_fence_tview
               (TView.read_fence_tview (Local.tview lc) Ordering.acqrel)
               TimeMap.bot
               Ordering.acqrel)
            (Local.promises lc)).

Lemma sim_local_promise_acqrel
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt mem2_tgt
      loc from to val released kind
      (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to val released lc2_tgt mem2_tgt kind)
      (LOCAL1: sim_local lc1_src (local_acqrel lc1_tgt))
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src mem2_src,
    <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to val released lc2_src mem2_src kind>> /\
    <<LOCAL2: sim_local lc2_src (local_acqrel lc2_tgt)>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit SimPromises.promise_bot; eauto.
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  i. des.
  exploit sim_memory_closed_opt_view; eauto. i.
  exploit Memory.promise_future; try apply PROMISE_SRC; eauto.
  { apply WF1_SRC. }
  { apply WF1_SRC. }
  i. des.
  esplits; eauto.
  - econs; eauto.
  - econs; eauto.
Qed.

Lemma sim_local_fulfill_acqrel
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      loc from to val releasedm_src releasedm_tgt released ord_src ord_tgt
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_WF: View.opt_wf releasedm_src)
      (RELM_CLOSED: Memory.closed_opt_view releasedm_src mem1_src)
      (RELM_TGT: Time.le (View.rlx (View.unwrap releasedm_tgt) loc) from)
      (WF_RELM_TGT: View.opt_wf releasedm_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (ORD_TGT: Ordering.le ord_tgt Ordering.acqrel)
      (STEP_TGT: fulfill_step lc1_tgt sc1_tgt loc from to val releasedm_tgt released ord_tgt lc2_tgt sc2_tgt)
      (LOCAL1: sim_local lc1_src (local_acquired lc1_tgt))
      (ACQUIRED1: View.le (TView.cur (Local.tview lc1_src))
                          (View.join (TView.cur (Local.tview lc1_tgt)) (View.unwrap releasedm_tgt)))
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src sc2_src,
    <<STEP_SRC: fulfill_step lc1_src sc1_src loc from to val releasedm_src released ord_src lc2_src sc2_src>> /\
    <<LOCAL2: sim_local lc2_src (local_acqrel lc2_tgt)>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>>.
Proof.
  inv STEP_TGT.
  assert (RELT_LE:
   View.opt_le
     (TView.write_released (Local.tview lc1_src) sc1_src loc to releasedm_src ord_src)
     (TView.write_released (Local.tview lc1_tgt) sc2_tgt loc to releasedm_tgt ord_tgt)).
  { unfold TView.write_released, TView.write_tview. ss. viewtac.
    repeat (condtac; aggrtac;
            try match goal with
                | [|- View.opt_le _ _] => econs
                end);
      try apply WF1_TGT.
    - etrans; eauto. aggrtac.
    - etrans; [apply WF1_SRC|]. etrans; eauto. aggrtac.
    - etrans; [apply LOCAL1|]. aggrtac.
  }
  assert (RELT_WF:
   View.opt_wf (TView.write_released (Local.tview lc1_src) sc1_src loc to releasedm_src ord_src)).
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
    + inv WRITABLE. econs.
      * eapply TimeFacts.le_lt_lt; [apply ACQUIRED1|]. viewtac.
        eapply TimeFacts.le_lt_lt; eauto.
  - econs; eauto. s.
    unfold TView.write_tview, TView.write_fence_tview, TView.read_fence_tview. ss.
    econs; ss; repeat (condtac; aggrtac).
    all: try by destruct ord_src, ord_tgt.
    all: try by apply WF1_TGT.
    + etrans; [apply LOCAL1|]. repeat (try condtac; aggrtac).
    + etrans; [apply LOCAL1|]. aggrtac.
      etrans; [apply WF1_TGT|]. etrans; [apply WF1_TGT|]. aggrtac.
    + etrans; [apply LOCAL1|]. aggrtac.
      etrans; [apply WF1_TGT|]. etrans; [apply WF1_TGT|]. aggrtac.
    + etrans; [apply LOCAL1|]. repeat (try condtac; aggrtac).
      etrans; [apply WF1_TGT|]. etrans; [apply WF1_TGT|]. aggrtac.
    + etrans; [apply LOCAL1|]. ss. condtac; aggrtac.
    + etrans; [apply LOCAL1|]. aggrtac.
  - ss.
Qed.

Lemma sim_local_write_acqrel
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt mem2_tgt
      loc from to val releasedm_src releasedm_tgt released_tgt ord_src ord_tgt kind
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_SRC_WF: View.opt_wf releasedm_src)
      (RELM_SRC_CLOSED: Memory.closed_opt_view releasedm_src mem1_src)
      (RELM_TGT_WF: View.opt_wf releasedm_tgt)
      (RELM_TGT_CLOSED: Memory.closed_opt_view releasedm_tgt mem1_tgt)
      (RELM_TGT: Time.le (View.rlx (View.unwrap releasedm_tgt) loc) from)
      (ORD: Ordering.le ord_src ord_tgt)
      (ORD_TGT: Ordering.le ord_tgt Ordering.acqrel)
      (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt ord_tgt lc2_tgt sc2_tgt mem2_tgt kind)
      (LOCAL1: sim_local lc1_src (local_acquired lc1_tgt))
      (ACQUIRED1: View.le (TView.cur (Local.tview lc1_src))
                          (View.join (TView.cur (Local.tview lc1_tgt)) (View.unwrap releasedm_tgt)))
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists released_src lc2_src sc2_src mem2_src,
    <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val releasedm_src released_src ord_src lc2_src sc2_src mem2_src kind>> /\
    <<REL2: View.opt_le released_src released_tgt>> /\
    <<LOCAL2: sim_local lc2_src (local_acqrel lc2_tgt)>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit sim_local_promise_acquired; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  hexploit sim_local_fulfill_acqrel; try apply STEP2;
    try apply LOCAL2; try apply MEM2; eauto.
  { eapply Memory.future_closed_opt_view; eauto. }
  { inv STEP_SRC. inv STEP1. ss. }
  i. des.
  exploit promise_fulfill_write; try exact STEP_SRC; try exact STEP_SRC0; eauto.
  { i. exploit ORD0; eauto.
    - etrans; eauto.
    - i. des. splits; auto. eapply sim_local_nonsynch_loc; eauto.
  }
  i. des. esplits; eauto. etrans; eauto.
Qed.


Inductive split_acqrel: forall (i1 i2:Instr.t), Prop :=
| split_acqrel_load
    r l:
    split_acqrel (Instr.load r l Ordering.acqrel) (Instr.load r l Ordering.relaxed)
| split_acqrel_update
    r l rmw ow
    (OW: Ordering.le ow Ordering.acqrel):
    split_acqrel (Instr.update r l rmw Ordering.acqrel ow) (Instr.update r l rmw Ordering.relaxed ow)
.

Inductive sim_acqrel: forall (st_src:(Language.state lang)) (lc_src:Local.t) (sc1_src:TimeMap.t) (mem1_src:Memory.t)
                        (st_tgt:(Language.state lang)) (lc_tgt:Local.t) (sc1_tgt:TimeMap.t) (mem1_tgt:Memory.t), Prop :=
| sim_acqrel_intro
    rs
    lc1_src sc1_src mem1_src
    lc1_tgt sc1_tgt mem1_tgt
    (LOCAL: sim_local lc1_src (local_acqrel lc1_tgt))
    (SC: TimeMap.le sc1_src sc1_tgt)
    (MEMORY: sim_memory mem1_src mem1_tgt)
    (WF_SRC: Local.wf lc1_src mem1_src)
    (WF_TGT: Local.wf lc1_tgt mem1_tgt)
    (SC_SRC: Memory.closed_timemap sc1_src mem1_src)
    (SC_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
    (MEM_SRC: Memory.closed mem1_src)
    (MEM_TGT: Memory.closed mem1_tgt):
    sim_acqrel
      (State.mk rs []) lc1_src sc1_src mem1_src
      (State.mk rs [Stmt.instr (Instr.fence Ordering.acqrel Ordering.acqrel)]) lc1_tgt sc1_tgt mem1_tgt
.

Lemma sim_acqrel_mon
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      sc2_tgt mem2_tgt
      (SIM1: sim_acqrel st_src lc_src sc1_src mem1_src
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
  sim_acqrel st_src lc_src sc2_src mem2_src
               st_tgt lc_tgt sc2_tgt mem2_tgt.
Proof.
  inv SIM1. econs; eauto.
Qed.

Lemma sim_acqrel_future
      st_src lc_src sc1_src mem1_src
      st_tgt lc_tgt sc1_tgt mem1_tgt
      sc2_src mem2_src
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (SIM1: sim_acqrel st_src lc_src sc1_src mem1_src
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
    <<SIM2: sim_acqrel st_src lc'_src sc2_src mem2_src
                         st_tgt lc_tgt sc2_tgt mem2_tgt>>.
Proof.
  inv SIM1.
  exploit SimPromises.future; try apply MEM1; eauto.
  { inv LOCAL. ss. eauto. }
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

Lemma sim_acqrel_step
      st1_src lc1_src sc1_src mem1_src
      st1_tgt lc1_tgt sc1_tgt mem1_tgt
      (SIM: sim_acqrel st1_src lc1_src sc1_src mem1_src
                         st1_tgt lc1_tgt sc1_tgt mem1_tgt):
  _sim_thread_step lang lang ((sim_thread (sim_terminal eq)) \8/ sim_acqrel)
                   st1_src lc1_src sc1_src mem1_src
                   st1_tgt lc1_tgt sc1_tgt mem1_tgt.
Proof.
  inv SIM. ii.
  inv STEP_TGT; [inv STEP|inv STEP; inv LOCAL0];
    try (inv STATE; inv INSTR; inv SPLIT); ss.
  - (* promise *)
    exploit Local.promise_step_future; eauto. i. des.
    exploit sim_local_promise_acqrel; try exact LOCAL; eauto. i. des.
    exploit Local.promise_step_future; eauto. i. des.
    esplits; try apply SC; eauto.
    + econs 2. econs. econs; eauto.
    + eauto.
    + right. econs; eauto.
  - (* fence *)
    exploit Local.fence_step_future; eauto. i. des.
    inv STATE. inv INSTR. inv LOCAL1. ss.
    esplits; (try by econs 1); eauto.
    left. eapply paco9_mon; [apply sim_stmts_nil|]; ss.
Qed.

Lemma sim_acqrel_sim_thread:
  sim_acqrel <8= (sim_thread (sim_terminal eq)).
Proof.
  pcofix CIH. i. pfold. ii. ss. splits; ss; ii.
  - inv TERMINAL_TGT. inv PR; ss.
  - exploit sim_acqrel_mon; eauto. i.
    exploit sim_acqrel_future; try apply x0; eauto. i. des.
    esplits; eauto.
  - esplits; eauto.
    inv PR. eapply sim_local_memory_bot; eauto.
  - exploit sim_acqrel_mon; eauto. i. des.
    exploit sim_acqrel_step; eauto. i. des.
    + esplits; eauto.
      left. eapply paco9_mon; eauto. ss.
    + esplits; eauto.
Qed.

Lemma split_acqrel_sim_stmts
      i_src i_tgt
      (SPLIT: split_acqrel i_src i_tgt):
  sim_stmts eq
            [Stmt.instr i_src]
            [Stmt.instr i_tgt; Stmt.instr (Instr.fence Ordering.acqrel Ordering.acqrel)]
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
    try (inv STATE; inv INSTR; inv SPLIT); ss.
  - (* promise *)
    exploit sim_local_promise; eauto. i. des.
    esplits; try apply SC; eauto.
    econs 2. econs 1; eauto. econs; eauto. eauto.
  - (* load *)
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read_acquired; eauto. i. des.
    exploit Local.read_step_future; eauto. i. des.
    esplits; try apply SC; eauto.
    + econs 2. econs 2. econs; cycle 1.
      * econs 2. eauto.
      * econs. econs.
    + auto.
    + left. eapply paco9_mon; [apply sim_acqrel_sim_thread|]; ss.
      econs; ss. inv LOCAL2. econs; ss.
      etrans; eauto. apply TViewFacts.write_fence_tview_incr.
      eapply TViewFacts.read_fence_future; apply WF2.
  - (* update-load *)
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read_acquired; eauto. i. des.
    exploit Local.read_step_future; eauto. i. des.
    esplits; try apply SC; eauto.
    + econs 2. econs 2. econs; cycle 1.
      * econs 2. eauto.
      * econs. econs. eauto.
    + auto.
    + left. eapply paco9_mon; [apply sim_acqrel_sim_thread|]; ss.
      econs; ss. inv LOCAL2. econs; ss.
      etrans; eauto. apply TViewFacts.write_fence_tview_incr.
      eapply TViewFacts.read_fence_future; apply WF2.
  - (* update *)
    exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read_acquired; eauto. i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit Local.write_step_future; eauto. i. des.
    hexploit sim_local_write_acqrel; try exact LOCAL2; try exact SC; eauto; try refl.
    { inv LOCAL1. eapply MEM_TGT. eauto. }
    { inv STEP_SRC. inv LOCAL1. ss. repeat (condtac; aggrtac).
      - rewrite <- ? View.join_l. apply LOCAL.
      - apply WF_TGT.
      - unfold TimeMap.join. rewrite <- Time.join_l. rewrite <- Time.join_l. rewrite <- Time.join_r.
        unfold View.singleton_ur_if. condtac; ss. unfold TimeMap.singleton, LocFun.add.
        condtac; ss. refl.
    }
    i. des.
    exploit Local.write_step_future; eauto. i. des.
    esplits; try apply SC; eauto.
    + econs 2. econs 2. econs; cycle 1.
      * econs 4; eauto.
      * econs. econs. eauto.
    + auto.
    + left. eapply paco9_mon; [apply sim_acqrel_sim_thread|]; ss.
Qed.
