From PromisingLib Require Import Basic.
Require Import Bool.
Require Import List.

From sflib Require Import sflib.
From Paco Require Import paco.

From PromisingLib Require Import Basic.
From PromisingLib Require Import DenseOrder.
From PromisingLib Require Import Loc.

Require Import Event.
Require Import Language.
Require Import Time.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
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

Require ReorderTView.
Require Import MemoryReorder.
Require Import MemoryMerge.

Require Import Syntax.
Require Import Semantics.
Require Import ProgressStep.

Set Implicit Arguments.

Lemma future_read_step
      lc1 mem1 mem1' loc ts val released ord lc2
      (WF: Local.wf lc1 mem1)
      (MEM: Memory.closed mem1)
      (FUTURE: Memory.future mem1 mem1')
      (STEP: Local.read_step lc1 mem1 loc ts val released ord lc2):
  exists released' lc2',
    <<STEP: Local.read_step lc1 mem1' loc ts val released' ord lc2'>> /\
    <<REL: View.opt_le released' released>> /\
    <<LOCAL: sim_local lc2' lc2>>.
Proof.
  inv STEP. exploit Memory.future_get1; eauto. i. des.
  esplits.
  - econs; eauto. eapply TViewFacts.readable_mon; eauto; refl.
  - auto.
  - econs; s.
    + apply TViewFacts.read_tview_mon; auto.
      * refl.
      * apply WF.
      * eapply MEM. eauto.
      * refl.
    + apply SimPromises.sem_bot.
Qed.

Lemma future_fulfill_step
      lc1 sc1 sc1' loc from to val releasedm releasedm' released ord lc2 sc2
      (ORD: Ordering.le ord Ordering.relaxed)
      (REL_LE: View.opt_le releasedm' releasedm)
      (STEP: fulfill_step lc1 sc1 loc from to val releasedm released ord lc2 sc2):
  fulfill_step lc1 sc1' loc from to val releasedm' released ord lc2 sc1'.
Proof.
  assert (TVIEW: TView.write_tview (Local.tview lc1) sc1 loc to ord = TView.write_tview (Local.tview lc1) sc1' loc to ord).
  { unfold TView.write_tview. repeat (condtac; viewtac). }
  inversion STEP. subst lc2 sc2.
  rewrite TVIEW. econs; eauto.
  - etrans; eauto. unfold TView.write_released. condtac; econs. repeat apply View.join_spec.
    + rewrite <- View.join_l. apply View.unwrap_opt_le. auto.
    + rewrite <- ? View.join_r. rewrite TVIEW. refl.
  - econs; try apply WRITABLE.
Qed.


Lemma reorder_read_read
      loc1 ts1 val1 released1 ord1
      loc2 ts2 val2 released2 ord2
      lc0 mem0
      lc1
      lc2
      (LOC: loc1 = loc2 -> Ordering.le ord1 Ordering.plain /\ Ordering.le ord2 Ordering.plain)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.read_step lc1 mem0 loc2 ts2 val2 released2 ord2 lc2):
  exists lc1',
    <<STEP1: Local.read_step lc0 mem0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.read_step lc1' mem0 loc1 ts1 val1 released1 ord1 lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
    eapply TViewFacts.readable_mon; try apply READABLE0; eauto; try refl.
    apply TViewFacts.read_tview_incr.
  - refine (Local.read_step_intro _ _ _ _ _); eauto.
    + s. unfold View.singleton_ur_if.
      econs; repeat (try condtac; try splits; aggrtac; eauto; try apply READABLE;
                     unfold TimeMap.singleton, LocFun.add in *).
      * specialize (LOC eq_refl). des. viewtac.
      * specialize (LOC eq_refl). des. viewtac.
      * specialize (LOC eq_refl). des. viewtac.
    + apply TView.antisym; apply ReorderTView.read_read_tview;
        (try by apply WF0);
        (try by eapply MEM0; eauto).
Qed.

Lemma reorder_read_promise
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 val2 released2 kind2
      lc0 mem0
      lc1
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.promise_step lc1 mem0 loc2 from2 to2 val2 released2 lc2 mem2 kind2):
  exists lc1' lc2' released1',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 val2 released2 lc1' mem2 kind2>> /\
    <<STEP2: Local.read_step lc1' mem2 loc1 ts1 val1 released1' ord1 lc2'>> /\
    <<REL1: View.opt_le released1' released1>> /\
    <<LOCAL: sim_local lc2' lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit Memory.promise_future; try exact PROMISE; try apply WF0; eauto. i. des.
  exploit Memory.promise_get1; eauto. i. des.
  esplits; eauto.
  - econs; eauto.
  - econs; eauto.
    s. eapply TViewFacts.readable_mon; eauto; try refl.
  - s. econs; ss.
    + apply TViewFacts.read_tview_mon; try refl; try apply WF0; eauto.
      eapply MEM0. eauto.
    + apply SimPromises.sem_bot.
Qed.

Lemma reorder_read_promise_diff
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 val2 released2 kind2
      lc0 mem0
      lc1
      lc2 mem2
      (DIFF: (loc1, ts1) <> (loc2, to2))
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.promise_step lc1 mem0 loc2 from2 to2 val2 released2 lc2 mem2 kind2):
  exists lc1',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 val2 released2 lc1' mem2 kind2>> /\
    <<STEP2: Local.read_step lc1' mem2 loc1 ts1 val1 released1 ord1 lc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  exploit MemoryFacts.promise_get1_diff; eauto. i. des.
  esplits; eauto.
  - econs; eauto.
  - econs; eauto.
Qed.

Lemma reorder_read_fulfill
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 val2 releasedm2 released2 ord2
      lc0 sc0 mem0
      lc1
      lc2 sc2
      (LOC: loc1 <> loc2)
      (ORD: Ordering.le ord1 Ordering.acqrel \/ Ordering.le ord2 Ordering.acqrel)
      (RELM_WF: View.opt_wf releasedm2)
      (RELM_CLOSED: Memory.closed_opt_view releasedm2 mem0)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: fulfill_step lc1 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2):
  exists lc1' lc2',
    <<STEP1: fulfill_step lc0 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2>> /\
    <<STEP2: Local.read_step lc1' mem0 loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<LOCAL: sim_local lc2' lc2>>.
Proof.
  guardH ORD.
  exploit Local.read_step_future; eauto. i. des.
  inv STEP1. inv STEP2.
  esplits; eauto.
  - econs; eauto.
    + etrans; eauto. unfold TView.write_released. s.
      condtac; econs. repeat (try condtac; aggrtac; try apply WF0).
    + eapply TViewFacts.writable_mon; eauto; try refl. apply TVIEW_FUTURE.
  - econs; eauto.
    s. inv READABLE.
    econs; repeat (try condtac; aggrtac; try apply WF0; eauto; unfold TimeMap.singleton).
  - s. econs; s.
    + apply ReorderTView.read_write_tview; try apply WF0; auto.
    + apply SimPromises.sem_bot.
Qed.

Lemma reorder_read_write
      loc1 ts1 val1 released1 ord1
      loc2 from2 to2 val2 releasedm2 released2 ord2
      lc0 sc0 mem0
      lc1
      lc2 sc2 mem2
      kind
      (LOC: loc1 <> loc2)
      (ORD: Ordering.le ord1 Ordering.acqrel \/ Ordering.le ord2 Ordering.acqrel)
      (RELM_WF: View.opt_wf releasedm2)
      (RELM_CLOSED: Memory.closed_opt_view releasedm2 mem0)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.write_step lc1 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind):
  exists released2' mem2' lc1' lc2',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2' ord2 lc1' sc2 mem2' kind>> /\
    <<STEP2: Local.read_step lc1' mem2' loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<RELEASED: View.opt_le released2' released2>> /\
    <<MEM: sim_memory mem2' mem2>>.
Proof.
  guardH ORD.
  exploit Local.read_step_future; eauto. i. des.
  exploit write_promise_fulfill; try exact STEP2; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit reorder_read_promise_diff; try exact STEP1; try exact STEP0; eauto.
  { ii. inv H. congr. }
  i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit reorder_read_fulfill; try exact STEP5; try exact STEP3; eauto; try by viewtac. i. des.
  exploit promise_fulfill_write; try exact x4; try exact STEP6; eauto; try by viewtac.
  { i. exploit ORD0; eauto. i. des.
    splits; auto. inv STEP1. auto.
  }
  i. des.
  inv STEP1.
  inversion STEP. inv WRITE. hexploit MemoryFacts.promise_get1_diff; try exact PROMISE; eauto.
  { ii. inv H. congr. }
  i. des.
  esplits; eauto.
  inv STEP7. econs; eauto.
Qed.

Lemma reorder_read_update
      loc1 ts1 val1 released1 ord1
      loc2 ts2 val2 released2 ord2
      from3 to3 val3 released3 ord3
      lc0 sc0 mem0
      lc1
      lc2
      lc3 sc3 mem3
      kind
      (LOC: loc1 <> loc2)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (ORD3: Ordering.le ord1 Ordering.acqrel \/ Ordering.le ord3 Ordering.acqrel)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.read_step lc1 mem0 loc2 ts2 val2 released2 ord2 lc2)
      (STEP3: Local.write_step lc2 sc0 mem0 loc2 from3 to3 val3 released2 released3 ord3 lc3 sc3 mem3 kind):
  exists released3' mem3' lc1' lc2' lc3',
    <<STEP1: Local.read_step lc0 mem0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.write_step lc1' sc0 mem0 loc2 from3 to3 val3 released2 released3' ord3 lc2' sc3 mem3' kind>> /\
    <<STEP3: Local.read_step lc2' mem3' loc1 ts1 val1 released1 ord1 lc3'>> /\
    <<LOCAL: sim_local lc3' lc3>> /\
    <<RELEASED: View.opt_le released3' released3>> /\
    <<MEM: sim_memory mem3' mem3>>.
Proof.
  guardH ORD3.
  exploit Local.read_step_future; try exact STEP1; eauto. i. des.
  exploit Local.read_step_future; try exact STEP2; eauto. i. des.
  exploit reorder_read_read; try exact STEP1; try exact STEP2; eauto; try congr. i. des.
  exploit Local.read_step_future; try exact STEP0; eauto. i. des.
  hexploit reorder_read_write; try exact STEP4; try exact STEP_SRC; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_read_fence
      loc1 ts1 val1 released1 ord1
      ordr2 ordw2
      lc0 sc0 mem0
      lc1
      lc2 sc2
      (ORDR2: Ordering.le ordr2 Ordering.relaxed)
      (ORDW2: Ordering.le ordw2 Ordering.acqrel)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: Local.fence_step lc1 sc0 ordr2 ordw2 lc2 sc2):
  exists lc1' lc2' sc2',
    <<STEP1: Local.fence_step lc0 sc0 ordr2 ordw2 lc1' sc2'>> /\
    <<STEP2: Local.read_step lc1' mem0 loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<SC: TimeMap.le sc2' sc2>>.
Proof.
  exploit Local.read_step_future; eauto. i. des.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
  - econs; eauto. s.
    unfold TView.write_fence_tview, TView.read_fence_tview, TView.write_fence_sc.
    econs; repeat (try condtac; try splits; aggrtac; try apply READABLE).
  - s. econs; s.
    + etrans.
      * apply ReorderTView.read_write_fence_tview; auto.
        eapply TViewFacts.read_fence_future; apply WF0.
      * apply TViewFacts.write_fence_tview_mon; try refl.
        apply ReorderTView.read_read_fence_tview; try apply WF0; auto.
        exploit TViewFacts.read_fence_future; try apply WF0; eauto. i. des.
        eapply TViewFacts.read_future; eauto.
    + apply SimPromises.sem_bot.
  - unfold TView.write_fence_sc, TView.read_fence_tview.
    repeat condtac; aggrtac.
Qed.

Lemma reorder_fulfill_read
      loc1 from1 to1 val1 releasedm1 released1 ord1
      loc2 ts2 val2 released2 ord2
      lc0 sc0 mem0
      lc1 sc1
      lc2
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: fulfill_step lc0 sc0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 sc1)
      (STEP2: Local.read_step lc1 mem0 loc2 ts2 val2 released2 ord2 lc2):
  exists lc1',
    <<STEP1: Local.read_step lc0 mem0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: fulfill_step lc1' sc0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc2 sc1>>.
Proof.
  inv STEP1. inv STEP2.
  hexploit Memory.remove_future; try apply REMOVE; try apply WF0; eauto. i. des.
  esplits.
  - econs; eauto.
    eapply TViewFacts.readable_mon; try apply READABLE; eauto; try refl.
    apply TViewFacts.write_tview_incr. apply WF0.
  - unfold Local.tview at 2.
    unfold Local.promises at 2.
    rewrite ReorderTView.read_write_tview_eq; eauto; try apply WF0; cycle 1.
    { eapply MEM0. eauto. }
    econs; try exact REMOVE; eauto.
    + etrans; eauto. unfold TView.write_released. s. condtac; econs.
      repeat (try condtac; aggrtac).
    + s. unfold View.singleton_ur_if.
      econs; repeat (try condtac; try splits; aggrtac; eauto; try apply WRITABLE;
                     unfold TimeMap.singleton, LocFun.add in *);
        (try by inv WRITABLE; eapply TimeFacts.le_lt_lt; eauto; aggrtac).
Qed.

Lemma reorder_fulfill_promise
      loc1 from1 to1 val1 releasedm1 released1 ord1
      loc2 from2 to2 val2 released2 kind2
      lc0 sc0 mem0
      lc1 sc1
      lc2 mem2
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: fulfill_step lc0 sc0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 sc1)
      (STEP2: Local.promise_step lc1 mem0 loc2 from2 to2 val2 released2 lc2 mem2 kind2):
  exists lc1',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 val2 released2 lc1' mem2 kind2>> /\
    <<STEP2: fulfill_step lc1' sc0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc2 sc1>>.
Proof.
  inv STEP1. inv STEP2.
  hexploit Memory.remove_future; try apply WF0; eauto. i. des.
  hexploit Memory.promise_future; eauto. i. des.
  exploit MemoryReorder.remove_promise; try apply WF0; eauto. i. des.
  esplits.
  - econs; eauto.
  - econs; eauto.
Qed.

Lemma reorder_fulfill_fulfill
      loc1 from1 to1 val1 releasedm1 released1 ord1
      loc2 from2 to2 val2 releasedm2 released2 ord2
      lc0 sc0 mem0
      lc1 sc1
      lc2 sc2
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (LOC: loc1 <> loc2)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL1_WF: View.opt_wf releasedm1)
      (REL2_WF: View.opt_wf releasedm2)
      (REL2_CLOSED: Memory.closed_opt_view releasedm2 mem0)
      (STEP1: fulfill_step lc0 sc0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 sc1)
      (STEP2: fulfill_step lc1 sc1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2):
  exists lc1' lc2' sc1' sc2',
    <<STEP1: fulfill_step lc0 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc1'>> /\
    <<STEP2: fulfill_step lc1' sc1' loc1 from1 to1 val1 releasedm1 released1 ord1 lc2' sc2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<SC: TimeMap.le sc2' sc2>>.
Proof.
  inv STEP1. inv STEP2.
  hexploit Memory.remove_future; try apply WF0; eauto. i. des.
  exploit MemoryReorder.remove_remove; try apply REMOVE; try apply REMOVE0; eauto. i. des.
  unfold Local.promises in REMOVE0.
  esplits.
  - econs; eauto.
    + etrans; eauto. unfold TView.write_released. s. condtac; econs.
      repeat (try condtac; aggrtac; try apply WF0).
    + eapply TViewFacts.writable_mon; eauto; try refl.
      * apply TViewFacts.write_tview_incr. apply WF0.
  - econs; eauto.
    + etrans; eauto. unfold TView.write_released. s. condtac; econs.
      repeat (try condtac; aggrtac; try apply WF0).
    + inv WRITABLE. econs; i.
      * eapply TimeFacts.le_lt_lt; [|apply TS].
        repeat (try condtac; viewtac; unfold TimeMap.singleton in *).
  - s. econs; ss.
    + apply ReorderTView.write_write_tview; auto. apply WF0.
    + apply SimPromises.sem_bot.
  - refl.
Qed.

Lemma reorder_fulfill_write
      loc1 from1 to1 val1 releasedm1 released1 ord1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2
      lc0 sc0 mem0
      lc1 sc1
      lc2 sc2 mem2
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (LOC: loc1 <> loc2)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL1_WF: View.opt_wf releasedm1)
      (REL1_CLOSED: Memory.closed_opt_view releasedm1 mem0)
      (REL2_WF: View.opt_wf releasedm2)
      (REL2_CLOSED: Memory.closed_opt_view releasedm2 mem0)
      (STEP1: fulfill_step lc0 sc0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 sc1)
      (STEP2: Local.write_step lc1 sc1 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2):
  exists released2' lc1' lc2' sc1' sc2' mem2',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2' ord2 lc1' sc1' mem2' kind2>> /\
    <<STEP2: fulfill_step lc1' sc1' loc1 from1 to1 val1 releasedm1 released1 ord1 lc2' sc2'>> /\
    <<RELEASED2: View.opt_le released2' released2>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<SC: TimeMap.le sc2' sc2>> /\
    <<MEM: sim_memory mem2' mem2>>.
Proof.
  exploit fulfill_step_future; eauto. i. des.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit reorder_fulfill_promise; try exact STEP1; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit fulfill_step_future; try exact STEP5; try exact WF3; eauto; try by viewtac. i. des.
  exploit reorder_fulfill_fulfill; try exact STEP5; try exact STEP3; eauto; try by viewtac. i. des.
  exploit promise_fulfill_write; eauto.
  { i. exploit ORD; eauto. i. des. splits; ss.
    ii. unfold Memory.get in GET.
    erewrite fulfill_step_promises_diff in GET; eauto.
  }
  i. des.
  esplits; eauto.
Qed.

Lemma reorder_fulfill_update
      loc1 from1 to1 val1 releasedm1 released1 ord1
      loc2 ts2 val2 released2 ord2
      from3 to3 val3 released3 ord3 kind3
      lc0 sc0 mem0
      lc1 sc1
      lc2
      lc3 sc3 mem3
      (LOC: loc1 <> loc2)
      (ORD1: Ordering.le ord1 Ordering.relaxed)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL1_WF: View.opt_wf releasedm1)
      (REL1_CLOSED: Memory.closed_opt_view releasedm1 mem0)
      (STEP1: fulfill_step lc0 sc0 loc1 from1 to1 val1 releasedm1 released1 ord1 lc1 sc1)
      (STEP2: Local.read_step lc1 mem0 loc2 ts2 val2 released2 ord2 lc2)
      (STEP3: Local.write_step lc2 sc1 mem0 loc2 from3 to3 val3 released2 released3 ord3 lc3 sc3 mem3 kind3):
  exists released3' lc1' lc2' lc3' sc2' sc3' mem2',
    <<STEP1: Local.read_step lc0 mem0 loc2 ts2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.write_step lc1' sc0 mem0 loc2 from3 to3 val3 released2 released3' ord3 lc2' sc2' mem2' kind3>> /\
    <<STEP3: fulfill_step lc2' sc2' loc1 from1 to1 val1 releasedm1 released1 ord1 lc3' sc3'>> /\
    <<LOCAL: sim_local lc3' lc3>> /\
    <<RELEASED: View.opt_le released3' released3>> /\
    <<SC: TimeMap.le sc3' sc3>> /\
    <<MEM: sim_memory mem2' mem3>>.
Proof.
  exploit fulfill_step_future; try exact STEP1; eauto. i. des.
  exploit Local.read_step_future; try exact STEP2; eauto. i. des.
  exploit reorder_fulfill_read; try exact STEP1; try exact STEP2; eauto. i. des.
  exploit Local.read_step_future; try exact STEP0; eauto. i. des.
  exploit fulfill_step_future; try exact STEP4; eauto. i. des.
  exploit sim_local_write; try exact STEP3; try exact LOCAL; try refl; eauto. i. des.
  exploit reorder_fulfill_write; try exact STEP4; try exact STEP_SRC; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_update_read
      loc1 ts1 val1 released1 ord1
      from2 to2 val2 released2 ord2
      loc3 ts3 val3 released3 ord3
      lc0 sc0 mem0
      lc1
      lc2 sc2
      lc3
      (LOC: loc1 <> loc3)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (ORD3: Ordering.le ord3 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: fulfill_step lc1 sc0 loc1 from2 to2 val2 released1 released2 ord2 lc2 sc2)
      (STEP3: Local.read_step lc2 mem0 loc3 ts3 val3 released3 ord3 lc3):
  exists lc1' lc2',
    <<STEP1: Local.read_step lc0 mem0 loc3 ts3 val3 released3 ord3 lc1'>> /\
    <<STEP2: Local.read_step lc1' mem0 loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<STEP3: fulfill_step lc2' sc0 loc1 from2 to2 val2 released1 released2 ord2 lc3 sc2>>.
Proof.
  exploit Local.read_step_future; try exact STEP1; eauto. i. des.
  exploit fulfill_step_future; try exact STEP2; eauto. i. des.
  exploit reorder_fulfill_read; try exact STEP2; try exact STEP3; eauto. i. des.
  exploit Local.read_step_future; try exact STEP0; eauto. i. des.
  exploit reorder_read_read; try exact STEP1; try exact STEP0; eauto; try congr. i. des.
  esplits; eauto.
Qed.

Lemma reorder_update_promise
      loc1 ts1 val1 released1 ord1
      from2 to2 val2 released2 ord2
      loc3 from3 to3 val3 released3 kind3
      lc0 sc0 mem0
      lc1
      lc2 sc2
      lc3 mem3
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: fulfill_step lc1 sc0 loc1 from2 to2 val2 released1 released2 ord2 lc2 sc2)
      (STEP3: Local.promise_step lc2 mem0 loc3 from3 to3 val3 released3 lc3 mem3 kind3):
  exists released1' lc1' lc2' lc3' sc3',
    <<STEP1: Local.promise_step lc0 mem0 loc3 from3 to3 val3 released3 lc1' mem3 kind3>> /\
    <<STEP2: Local.read_step lc1' mem3 loc1 ts1 val1 released1' ord1 lc2'>> /\
    <<STEP3: fulfill_step lc2' sc0 loc1 from2 to2 val2 released1' released2 ord2 lc3' sc3'>> /\
    <<RELEASED1: View.opt_le released1' released1>> /\
    <<LOCAL: sim_local lc3' lc3>> /\
    <<SC: TimeMap.le sc3' sc2>>.
Proof.
  exploit Local.read_step_future; try exact STEP1; eauto. i. des.
  exploit fulfill_step_future; try exact STEP2; eauto. i. des.
  exploit reorder_fulfill_promise; try exact STEP2; try exact STEP3; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit reorder_read_promise; try exact STEP1; try exact STEP0; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit Local.read_step_future; eauto. i. des.
  exploit sim_local_fulfill; try exact STEP4; try exact LOCAL; try exact REL1;
    try exact WF3; try exact WF5; try refl; eauto; try by viewtac. i. des.
  esplits; eauto.
Qed.

Lemma reorder_update_promise_diff
      loc1 ts1 val1 released1 ord1
      from2 to2 val2 released2 ord2
      loc3 from3 to3 val3 released3 kind3
      lc0 sc0 mem0
      lc1
      lc2 sc2
      lc3 mem3
      (DIFF: (loc1, ts1) <> (loc3, to3))
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: fulfill_step lc1 sc0 loc1 from2 to2 val2 released1 released2 ord2 lc2 sc2)
      (STEP3: Local.promise_step lc2 mem0 loc3 from3 to3 val3 released3 lc3 mem3 kind3):
  exists lc1' lc2',
    <<STEP1: Local.promise_step lc0 mem0 loc3 from3 to3 val3 released3 lc1' mem3 kind3>> /\
    <<STEP2: Local.read_step lc1' mem3 loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<STEP3: fulfill_step lc2' sc0 loc1 from2 to2 val2 released1 released2 ord2 lc3 sc2>>.
Proof.
  exploit Local.read_step_future; try exact STEP1; eauto. i. des.
  exploit fulfill_step_future; try exact STEP2; eauto. i. des.
  exploit reorder_fulfill_promise; try exact STEP2; try exact STEP3; eauto. i. des.
  exploit reorder_read_promise_diff; try exact STEP1; try exact STEP0; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_update_fulfill
      loc1 ts1 val1 released1 ord1
      from2 to2 val2 released2 ord2
      loc3 from3 to3 val3 releasedm3 released3 ord3
      lc0 sc0 mem0
      lc1
      lc2 sc2
      lc3 sc3
      (LOC: loc1 <> loc3)
      (TIME: ts1 <> to2)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (ORD3: Ordering.le ord1 Ordering.acqrel \/ Ordering.le ord3 Ordering.acqrel)
      (REL_WF: View.opt_wf releasedm3)
      (REL_CLOSED: Memory.closed_opt_view releasedm3 mem0)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: fulfill_step lc1 sc0 loc1 from2 to2 val2 released1 released2 ord2 lc2 sc2)
      (STEP3: fulfill_step lc2 sc2 loc3 from3 to3 val3 releasedm3 released3 ord3 lc3 sc3):
  exists lc1' lc2' lc3' sc1' sc3',
    <<STEP1: fulfill_step lc0 sc0 loc3 from3 to3 val3 releasedm3 released3 ord3 lc1' sc1'>> /\
    <<STEP2: Local.read_step lc1' mem0 loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<STEP3: fulfill_step lc2' sc1' loc1 from2 to2 val2 released1 released2 ord2 lc3' sc3'>> /\
    <<LOCAL: sim_local lc3' lc3>> /\
    <<SC: TimeMap.le sc3' sc3>>.
Proof.
  guardH ORD3.
  exploit Local.read_step_future; try exact STEP1; eauto. i. des.
  exploit fulfill_step_future; try exact STEP2; eauto. i. des.
  exploit reorder_fulfill_fulfill; try exact STEP2; try exact STEP3; eauto. i. des.
  exploit fulfill_step_future; try exact STEP0; eauto; try by viewtac. i. des.
  exploit reorder_read_fulfill; try exact STEP1; try exact STEP0; eauto; try by viewtac. i. des.
  exploit fulfill_step_future; try exact STEP5; eauto; try by viewtac. i. des.
  exploit Local.read_step_future; try exact STEP6; eauto; try by viewtac. i. des.
  exploit sim_local_fulfill; try exact STEP4; try exact LOCAL0; try refl; eauto. i. des.
  esplits; eauto.
  - etrans; eauto.
  - etrans; eauto.
Qed.

Lemma reorder_update_write
      loc1 ts1 val1 released1 ord1
      from2 to2 val2 released2 ord2
      loc3 from3 to3 val3 releasedm3 released3 ord3 kind3
      lc0 sc0 mem0
      lc1
      lc2 sc2
      lc3 sc3 mem3
      (LOC: loc1 <> loc3)
      (TIME: ts1 <> to2)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (ORD3: Ordering.le ord1 Ordering.acqrel \/ Ordering.le ord3 Ordering.acqrel)
      (REL_WF: View.opt_wf releasedm3)
      (REL_CLOSED: Memory.closed_opt_view releasedm3 mem0)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: fulfill_step lc1 sc0 loc1 from2 to2 val2 released1 released2 ord2 lc2 sc2)
      (STEP3: Local.write_step lc2 sc2 mem0 loc3 from3 to3 val3 releasedm3 released3 ord3 lc3 sc3 mem3 kind3):
  exists released2' released3' lc1' lc2' lc3' sc1' sc3' mem1',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc3 from3 to3 val3 releasedm3 released3' ord3 lc1' sc1' mem1' kind3>> /\
    <<STEP2: Local.read_step lc1' mem1' loc1 ts1 val1 released1 ord1 lc2'>> /\
    <<STEP3: fulfill_step lc2' sc1' loc1 from2 to2 val2 released1 released2' ord2 lc3' sc3'>> /\
    <<LOCAL: sim_local lc3' lc3>> /\
    <<RELEASED2: View.opt_le released2' released2>> /\
    <<RELEASED3: View.opt_le released3' released3>> /\
    <<SC: TimeMap.le sc3' sc3>> /\
    <<MEM: sim_memory mem1' mem3>>.
Proof.
  guardH ORD3.
  exploit Local.read_step_future; eauto. i. des.
  exploit fulfill_step_future; eauto. i. des.
  exploit write_promise_fulfill; eauto. i. des.
  exploit reorder_update_promise_diff; try exact STEP1; try exact STEP2; try exact STEP0; eauto.
  { ii. inv H. congr. }
  i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit Local.read_step_future; eauto. i. des.
  hexploit reorder_update_fulfill; try exact STEP6; try exact STEP7; try exact STEP4; eauto; try by viewtac. i. des.
  exploit fulfill_step_future; try exact STEP8; try exact WF3; eauto; try by viewtac. i. des.
  exploit promise_fulfill_write; eauto.
  { i. exploit ORD; eauto. i. des.
    splits; auto.
    erewrite Local.read_step_promises; [|eauto].
    ii. unfold Memory.get in GET. erewrite fulfill_step_promises_diff in GET; eauto.
  }
  i. des.
  inv STEP1.
  inversion STEP. inv WRITE. hexploit MemoryFacts.promise_get1_diff; try exact PROMISE; eauto.
  { ii. inv H. congr. }
  i. des.
  esplits; try exact STEP10; eauto; try refl.
  inv STEP9. econs; eauto.
Qed.

Lemma reorder_update_update
      loc1 ts1 val1 released1 ord1
      from2 to2 val2 released2 ord2
      loc3 ts3 val3 released3 ord3
      from4 to4 val4 released4 ord4 kind4
      lc0 sc0 mem0
      lc1
      lc2 sc2
      lc3
      lc4 sc4 mem4
      (LOC: loc1 <> loc3)
      (TIME: ts1 <> to2)
      (ORD2: Ordering.le ord2 Ordering.relaxed)
      (ORD3: Ordering.le ord3 Ordering.relaxed)
      (ORD: Ordering.le ord1 Ordering.acqrel \/ Ordering.le ord4 Ordering.acqrel)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.read_step lc0 mem0 loc1 ts1 val1 released1 ord1 lc1)
      (STEP2: fulfill_step lc1 sc0 loc1 from2 to2 val2 released1 released2 ord2 lc2 sc2)
      (STEP3: Local.read_step lc2 mem0 loc3 ts3 val3 released3 ord3 lc3)
      (STEP4: Local.write_step lc3 sc2 mem0 loc3 from4 to4 val4 released3 released4 ord4 lc4 sc4 mem4 kind4):
  exists released2' released4' lc1' lc2' lc3' lc4' sc2' sc4' mem2',
    <<STEP1: Local.read_step lc0 mem0 loc3 ts3 val3 released3 ord3 lc1'>> /\
    <<STEP2: Local.write_step lc1' sc0 mem0 loc3 from4 to4 val4 released3 released4' ord4 lc2' sc2' mem2' kind4>> /\
    <<STEP3: Local.read_step lc2' mem2' loc1 ts1 val1 released1 ord1 lc3'>> /\
    <<STEP4: fulfill_step lc3' sc2' loc1 from2 to2 val2 released1 released2' ord2 lc4' sc4'>> /\
    <<LOCAL: sim_local lc4' lc4>> /\
    <<RELEASED2: View.opt_le released2' released2>> /\
    <<RELEASED4: View.opt_le released4' released4>> /\
    <<SC: TimeMap.le sc4' sc4>> /\
    <<MEM: sim_memory mem2' mem4>>.
Proof.
  guardH ORD.
  exploit reorder_update_read; try exact STEP2; try exact STEP1; try exact STEP3; eauto. i. des.
  exploit Local.read_step_future; try exact STEP0; eauto. i. des.
  hexploit reorder_update_write; try exact STEP5; try exact STEP6; try exact STEP4; eauto. i. des.
  esplits; eauto.
Qed.

Lemma reorder_fence_read
      ordr1 ordw1
      loc2 to2 val2 released2 ord2
      lc0 sc0 mem0
      lc1 sc1
      lc2
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (ORD2: Ordering.le ord2 Ordering.plain \/ Ordering.le Ordering.acqrel ord2)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.fence_step lc0 sc0 ordr1 ordw1 lc1 sc1)
      (STEP2: Local.read_step lc1 mem0 loc2 to2 val2 released2 ord2 lc2):
  exists lc1' lc2' sc2',
    <<STEP1: Local.read_step lc0 mem0 loc2 to2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.fence_step lc1' sc0 ordr1 ordw1 lc2' sc2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<SC: TimeMap.le sc2' sc1>>.
Proof.
  guardH ORD2. inv STEP1. inv STEP2.
  esplits.
  - econs; eauto.
    eapply TViewFacts.readable_mon; eauto; try refl.
    etrans.
    + apply TViewFacts.write_fence_tview_incr. apply WF0.
    + apply TViewFacts.write_fence_tview_mon; try refl; try apply WF0.
      apply TViewFacts.read_fence_tview_incr. apply WF0.
  - econs; eauto.
  - s. econs; s.
    + inversion MEM0. exploit CLOSED; eauto. i. des.
      exploit TViewFacts.read_future; try exact GET; try apply WF0; eauto. i. des.
      exploit TViewFacts.read_fence_future; try apply WF0; eauto. i. des.
      etrans; [|etrans].
      * apply TViewFacts.write_fence_tview_mon; [|refl|refl|].
        { apply ReorderTView.read_fence_read_tview; auto. apply WF0. }
        { inversion MEM0. exploit CLOSED; eauto. i. des.
          eapply TViewFacts.read_fence_future; eauto.
        }
      * apply ReorderTView.write_fence_read_tview; eauto.
      * apply TViewFacts.read_tview_mon; auto; try refl.
        eapply TViewFacts.write_fence_future; eauto.
    + apply SimPromises.sem_bot.
  - s. etrans.
    + apply TViewFacts.write_fence_sc_mon; [|refl|refl].
      apply ReorderTView.read_fence_read_tview; auto. apply WF0.
    + eapply ReorderTView.write_fence_read_sc; auto.
      eapply TViewFacts.read_fence_future; eauto; apply WF0.
Qed.

Lemma reorder_fence_promise
      ordr1 ordw1
      loc2 from2 to2 val2 released2
      lc0 sc0 mem0
      lc1 sc1
      lc2 mem2
      kind
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.fence_step lc0 sc0 ordr1 ordw1 lc1 sc1)
      (STEP2: Local.promise_step lc1 mem0 loc2 from2 to2 val2 released2 lc2 mem2 kind):
  exists lc1',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 val2 released2 lc1' mem2 kind>> /\
    <<STEP2: Local.fence_step lc1' sc0 ordr1 ordw1 lc2 sc1>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
  - econs; eauto. s. i. destruct ordw1; inv ORDW1; inv H.
Qed.

Lemma reorder_fence_fulfill
      ordr1 ordw1
      loc2 from2 to2 val2 releasedm2 released2 ord2
      lc0 sc0 mem0
      lc1 sc1
      lc2 sc2
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL2_WF: View.opt_wf releasedm2)
      (REL2_CLOSED: Memory.closed_opt_view releasedm2 mem0)
      (STEP1: Local.fence_step lc0 sc0 ordr1 ordw1 lc1 sc1)
      (STEP2: fulfill_step lc1 sc1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2):
  exists lc1' lc2' sc1' sc2',
    <<STEP1: fulfill_step lc0 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc1'>> /\
    <<STEP2: Local.fence_step lc1' sc1' ordr1 ordw1 lc2' sc2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<SC: TimeMap.le sc2' sc2>>.
Proof.
  inv STEP1. inv STEP2.
  exploit TViewFacts.read_fence_future; try apply WF0; eauto. i. des.
  hexploit TViewFacts.write_fence_future; eauto. i. des.
  esplits.
  - econs; eauto.
    + etrans; eauto. unfold TView.write_released. condtac; econs.
      repeat apply View.join_spec.
      * rewrite <- View.join_l. refl.
      * rewrite <- ? View.join_r.
        eapply TViewFacts.write_tview_mon; eauto; try refl.
        { etrans.
          - apply TViewFacts.write_fence_tview_incr. apply WF0.
          - apply TViewFacts.write_fence_tview_mon; try refl; try apply WF0.
            apply TViewFacts.read_fence_tview_incr. apply WF0.
        }
    + eapply TViewFacts.writable_mon; eauto; try refl.
      * etrans.
        { apply TViewFacts.read_fence_tview_incr. apply WF0. }
        { apply TViewFacts.write_fence_tview_incr.
          eapply TViewFacts.read_fence_future; apply WF0.
        }
      * apply TViewFacts.write_fence_sc_incr.
  - econs; eauto. ss. ii. revert GET.
    erewrite Memory.remove_o; eauto. condtac; ss. i. eapply RELEASE; eauto.
  - s. econs; s.
    + etrans; [|etrans].
      * apply TViewFacts.write_fence_tview_mon; [|refl|refl|].
        { apply ReorderTView.read_fence_write_tview; auto. apply WF0. }
        { exploit Memory.remove_get0; eauto. s. i.
          inv WF0. exploit PROMISES; eauto. i.
          exploit TViewFacts.write_future_fulfill; try exact SC0; eauto.
          { eapply MEM0. eauto. }
          i. des.
          eapply TViewFacts.read_fence_future; eauto.
        }
      * apply ReorderTView.write_fence_write_tview; auto.
      * apply TViewFacts.write_tview_mon; auto; try refl.
        apply TViewFacts.write_fence_sc_incr.
    + apply SimPromises.sem_bot.
  - etrans.
    + apply TViewFacts.write_fence_sc_mon; [|refl|refl].
      apply ReorderTView.read_fence_write_tview; auto. apply WF0.
    + eapply ReorderTView.write_fence_write_sc; auto.
Grab Existential Variables.
  { apply TimeMap.bot. }
Qed.

Lemma reorder_fence_write
      ordr1 ordw1
      loc2 from2 to2 val2 releasedm2 released2 ord2
      lc0 sc0 mem0
      lc1 sc1
      lc2 sc2 mem2 kind
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (REL2_WF: View.opt_wf releasedm2)
      (REL2_CLOSED: Memory.closed_opt_view releasedm2 mem0)
      (STEP1: Local.fence_step lc0 sc0 ordr1 ordw1 lc1 sc1)
      (STEP2: Local.write_step lc1 sc1 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind):
  exists released2' lc1' lc2' sc1' sc2' mem1',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2' ord2 lc1' sc1' mem1' kind>> /\
    <<STEP2: Local.fence_step lc1' sc1' ordr1 ordw1 lc2' sc2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<RELEASED2: View.opt_le released2' released2>> /\
    <<SC: TimeMap.le sc2' sc2>> /\
    <<MEM: sim_memory mem1' mem2>>.
Proof.
  exploit Local.fence_step_future; eauto. i. des.
  exploit write_promise_fulfill; eauto. i. des.
  exploit reorder_fence_promise; try exact STEP1; try exact STEP0; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit reorder_fence_fulfill; try exact STEP5; try exact STEP3; eauto; try by viewtac. i. des.
  exploit promise_fulfill_write; eauto.
  { i. exploit ORD; eauto. i. des.
    splits; auto. inv STEP1. auto.
  }
  i. des.
  esplits; eauto.
Qed.

Lemma reorder_fence_fence
      ordr1 ordw1
      ordr2 ordw2
      lc0 sc0 mem0
      lc1 sc1
      lc2 sc2
      (ORDR1: Ordering.le ordr1 Ordering.acqrel)
      (ORDW1: Ordering.le ordw1 Ordering.relaxed)
      (ORDR2: Ordering.le ordr2 Ordering.relaxed)
      (ORDW2: Ordering.le ordw2 Ordering.acqrel)
      (WF0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (STEP1: Local.fence_step lc0 sc0 ordr1 ordw1 lc1 sc1)
      (STEP2: Local.fence_step lc1 sc1 ordr2 ordw2 lc2 sc2):
  exists lc1' lc2' sc1' sc2',
    <<STEP1: Local.fence_step lc0 sc0 ordr2 ordw2 lc1' sc1'>> /\
    <<STEP2: Local.fence_step lc1' sc1' ordr1 ordw1 lc2' sc2'>> /\
    <<LOCAL: sim_local lc2' lc2>> /\
    <<SC: TimeMap.le sc2' sc2>>.
Proof.
  inv STEP1. inv STEP2. ss.
  esplits.
  - econs; eauto.
  - econs; eauto.
  - ss. econs; ss.
    + unfold TView.write_fence_tview, TView.write_fence_sc.
      econs; repeat (try condtac; aggrtac; try apply WF0).
    + apply SimPromises.sem_bot.
  - unfold TView.write_fence_sc.
    repeat (try condtac; aggrtac; try apply WF0).
Qed.
