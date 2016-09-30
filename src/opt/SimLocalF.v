Require Import RelationClasses.
Require Import Basics.
Require Import Bool.
Require Import List.

Require Import sflib.
Require Import paco.
Require Import respectful9.

Require Import Axioms.
Require Import Basic.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Thread.
Require Import Configuration.

Require Import FulfillStep.
Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.

Require Import Syntax.
Require Import Semantics.

Set Implicit Arguments.


Inductive sim_localF (none_for:SimPromises.t) (lc_src lc_tgt:Local.t): Prop :=
| sim_localF_intro
    (TVIEW_CUR: View.le lc_src.(Local.tview).(TView.cur) lc_tgt.(Local.tview).(TView.cur))
    (TVIEW_ACQ: View.le lc_src.(Local.tview).(TView.acq) lc_tgt.(Local.tview).(TView.acq))
    (PROMISES: SimPromises.sem none_for SimPromises.bot lc_src.(Local.promises) lc_tgt.(Local.promises))
.

Lemma sim_localF_nonsynch_loc
      none_for loc lc_src lc_tgt
      (SIM: sim_localF none_for lc_src lc_tgt)
      (NONSYNCH: Memory.nonsynch_loc loc lc_tgt.(Local.promises)):
  Memory.nonsynch_loc loc lc_src.(Local.promises).
Proof.
  inv SIM. inv PROMISES. ii. destruct msg.
  destruct (Memory.get loc t lc_tgt.(Local.promises)) as [[? []]|] eqn:X.
  - exploit NONSYNCH; eauto. s. i. subst.
    exploit LE; eauto. rewrite GET. i. inv x.
    unfold SimPromises.none_if. condtac; ss.
  - exploit COMPLETE; eauto. rewrite SimPromises.bot_spec. congr.
Qed.

Lemma sim_localF_nonsynch
      none_for lc_src lc_tgt
      (SIM: sim_localF none_for lc_src lc_tgt)
      (NONSYNCH: Memory.nonsynch lc_tgt.(Local.promises)):
  Memory.nonsynch lc_src.(Local.promises).
Proof.
  ii. eapply sim_localF_nonsynch_loc; eauto.
Qed.

Lemma sim_localF_memory_bot
      none_for lc_src lc_tgt
      (SIM: sim_localF none_for lc_src lc_tgt)
      (BOT: lc_tgt.(Local.promises) = Memory.bot):
  lc_src.(Local.promises) = Memory.bot.
Proof.
  apply Memory.ext. i. rewrite Memory.bot_get.
  destruct (Memory.get loc ts lc_src.(Local.promises)) as [[? []]|] eqn:X; ss.
  inv SIM.  inv PROMISES. exploit COMPLETE; eauto.
  { rewrite BOT, Memory.bot_get. ss. }
  rewrite SimPromises.bot_spec. ss.
Qed.

Lemma sim_localF_promise
      none_for
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt mem2_tgt
      loc from to val released kind
      (STEP_TGT: Local.promise_step lc1_tgt mem1_tgt loc from to val released lc2_tgt mem2_tgt kind)
      (LOCAL1: sim_localF none_for lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src mem2_src,
    <<STEP_SRC: Local.promise_step lc1_src mem1_src loc from to val (SimPromises.none_if loc to none_for released) lc2_src mem2_src (SimPromises.kind_transf loc to none_for kind)>> /\
    <<LOCAL2: sim_localF none_for lc2_src lc2_tgt>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit SimPromises.promise; eauto.
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  i. des.
  exploit sim_memory_closed_opt_view; eauto. i.
  exploit Memory.promise_future; try apply PROMISE_SRC; eauto.
  { apply WF1_SRC. }
  { apply WF1_SRC. }
  { unfold SimPromises.none_if. condtac; viewtac. }
  i. des.
  esplits; eauto.
  - econs; eauto.
    unfold SimPromises.none_if. condtac; viewtac.
  - econs; eauto.
Qed.

Lemma read_tview_mon'
      tview1 tview2 loc ts released1 released2 ord1 ord2
      (TVIEW_CUR: View.le tview1.(TView.cur) tview2.(TView.cur))
      (TVIEW_ACQ: View.le tview1.(TView.acq) tview2.(TView.acq))
      (REL: View.opt_le released1 released2)
      (WF2: TView.wf tview2)
      (WF_REL2: View.opt_wf released2)
      (ORD: Ordering.le ord1 ord2):
  <<CUR: View.le
           (TView.read_tview tview1 loc ts released1 ord1).(TView.cur)
           (TView.read_tview tview2 loc ts released2 ord2).(TView.cur)>> /\
  <<ACQ: View.le
           (TView.read_tview tview1 loc ts released1 ord1).(TView.acq)
           (TView.read_tview tview2 loc ts released2 ord2).(TView.acq)>>.
Proof.
  splits.
  - unfold TView.read_tview.
    repeat (condtac; aggrtac);
      (try by etrans; [apply TVIEW|aggrtac]);
      (try by rewrite <- ? View.join_r; econs; aggrtac);
      (try apply WF2).
  - unfold TView.read_tview.
    repeat (condtac; aggrtac);
      (try by etrans; [apply TVIEW|aggrtac]);
      (try by rewrite <- ? View.join_r; econs; aggrtac);
      (try apply WF2).
Qed.

Lemma sim_localF_read
      none_for
      lc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_tgt
      loc ts val released_tgt ord_src ord_tgt
      (STEP_TGT: Local.read_step lc1_tgt mem1_tgt loc ts val released_tgt ord_tgt lc2_tgt)
      (LOCAL1: sim_localF none_for lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt)
      (ORD: Ordering.le ord_src ord_tgt):
  exists released_src lc2_src,
    <<REL: View.opt_le released_src released_tgt>> /\
    <<STEP_SRC: Local.read_step lc1_src mem1_src loc ts val released_src ord_src lc2_src>> /\
    <<LOCAL2: sim_localF none_for lc2_src lc2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT.
  exploit sim_memory_get; try apply MEM1; eauto. i. des.
  esplits; eauto.
  - econs; eauto. eapply TViewFacts.readable_mon; eauto.
  - exploit read_tview_mon'; eauto.
    { apply WF1_TGT. }
    { eapply MEM1_TGT. eauto. }
    i. des. econs; eauto.
Qed.

Lemma write_tview_mon'
      tview1 tview2 sc1 sc2 loc ts ord1 ord2
      (TVIEW_CUR: View.le tview1.(TView.cur) tview2.(TView.cur))
      (TVIEW_ACQ: View.le tview1.(TView.acq) tview2.(TView.acq))
      (SC: TimeMap.le sc1 sc2)
      (WF2: TView.wf tview2)
      (ORD: Ordering.le ord1 ord2):
  <<CUR: View.le
           (TView.write_tview tview1 sc1 loc ts ord1).(TView.cur)
           (TView.write_tview tview2 sc2 loc ts ord2).(TView.cur)>> /\
  <<ACQ: View.le
           (TView.write_tview tview1 sc1 loc ts ord1).(TView.acq)
           (TView.write_tview tview2 sc2 loc ts ord2).(TView.acq)>>.
Proof.
  splits.
  - unfold TView.write_tview.
    repeat (condtac; aggrtac);
      (try by etrans; [apply TVIEW|aggrtac]);
      (try by rewrite <- ? View.join_r; econs; aggrtac);
      (try apply WF2).
  - unfold TView.write_tview.
    repeat (condtac; aggrtac);
      (try by etrans; [apply TVIEW|aggrtac]);
      (try by rewrite <- ? View.join_r; econs; aggrtac);
      (try apply WF2).
Qed.

Lemma sim_localF_fulfill
      none_for
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      loc from to val releasedm_src releasedm_tgt released ord_src ord_tgt
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_WF: View.opt_wf releasedm_src)
      (RELM_CLOSED: Memory.closed_opt_view releasedm_src mem1_src)
      (WF_RELM_TGT: View.opt_wf releasedm_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (NONEFOR: (Ordering.le Ordering.acqrel ord_tgt /\ SimPromises.mem loc to none_for = false) \/
                Ordering.le ord_tgt Ordering.plain)
      (STEP_TGT: fulfill_step lc1_tgt sc1_tgt loc from to val releasedm_tgt released ord_tgt lc2_tgt sc2_tgt)
      (LOCAL1: sim_localF none_for lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists lc2_src sc2_src,
    <<STEP_SRC: fulfill_step lc1_src sc1_src loc from to val releasedm_src (SimPromises.none_if loc to none_for released) ord_src lc2_src sc2_src>> /\
    <<LOCAL2: sim_localF (SimPromises.unset loc to none_for) lc2_src lc2_tgt>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>>.
Proof.
  guardH NONEFOR.
  inv STEP_TGT.
  assert (RELT_LE:
   View.opt_le
     (TView.write_released lc1_src.(Local.tview) sc1_src loc to releasedm_src ord_src)
     (TView.write_released lc1_tgt.(Local.tview) sc2_tgt loc to releasedm_tgt ord_tgt)).
  { unguardH NONEFOR. des.
    - unfold TView.write_released.
      condtac; [|by econs].
      condtac; cycle 1.
      { by destruct ord_tgt; inv NONEFOR; inv COND0. }
      econs. unfold TView.write_tview. s. rewrite NONEFOR.
      repeat (condtac; aggrtac).
      + rewrite <- View.join_r. rewrite <- ? View.join_l. apply LOCAL1.
      + apply WF1_TGT.
      + rewrite <- View.join_r. rewrite <- ? View.join_l.
        etrans; [|apply LOCAL1]. apply WF1_SRC.
    - unfold TView.write_released. repeat (condtac; viewtac). refl.
  }
  assert (RELT_WF:
   View.opt_wf (TView.write_released lc1_src.(Local.tview) sc1_src loc to releasedm_src ord_src)).
  { unfold TView.write_released. condtac; econs.
    repeat (try condtac; viewtac; try apply WF1_SRC).
  }
  exploit SimPromises.remove; try exact REMOVE;
    try exact MEM1; try apply LOCAL1; eauto.
  { apply WF1_SRC. }
  { apply WF1_TGT. }
  { apply WF1_TGT. }
  i. des. esplits.
  - econs; eauto.
    + unfold SimPromises.none_if. destruct (SimPromises.mem loc to none_for) eqn:X.
      * unguardH NONEFOR. des; [congr|]. unfold TView.write_released. condtac; [|refl].
        destruct ord_src, ord_tgt; inv ORD; inv NONEFOR; inv COND.
      * etrans; eauto.
    + unfold SimPromises.none_if. condtac; viewtac.
    + eapply TViewFacts.writable_mon; try exact WRITABLE; eauto. apply LOCAL1.
  - exploit write_tview_mon'; eauto.
    { apply LOCAL1. }
    { apply LOCAL1. }
    { apply WF1_TGT. }
    i. des. econs; eauto.
  - ss.
Qed.

Lemma sim_localF_write
      none_for
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt mem2_tgt
      loc from to val releasedm_src releasedm_tgt released_tgt ord_src ord_tgt kind
      (RELM_LE: View.opt_le releasedm_src releasedm_tgt)
      (RELM_SRC_WF: View.opt_wf releasedm_src)
      (RELM_SRC_CLOSED: Memory.closed_opt_view releasedm_src mem1_src)
      (RELM_TGT_WF: View.opt_wf releasedm_tgt)
      (RELM_TGT_CLOSED: Memory.closed_opt_view releasedm_tgt mem1_tgt)
      (ORD: Ordering.le ord_src ord_tgt)
      (ORD_TGT: ord_tgt <> Ordering.relaxed)
      (STEP_TGT: Local.write_step lc1_tgt sc1_tgt mem1_tgt loc from to val releasedm_tgt released_tgt ord_tgt lc2_tgt sc2_tgt mem2_tgt kind)
      (LOCAL1: sim_localF none_for lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists released_src lc2_src sc2_src mem2_src,
    <<STEP_SRC: Local.write_step lc1_src sc1_src mem1_src loc from to val releasedm_src released_src ord_src lc2_src sc2_src mem2_src (SimPromises.kind_transf loc to none_for kind)>> /\
    <<REL2: View.opt_le released_src released_tgt>> /\
    <<LOCAL2: sim_localF (SimPromises.unset loc to none_for) lc2_src lc2_tgt>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>> /\
    <<MEM2: sim_memory mem2_src mem2_tgt>>.
Proof.
  exploit write_promise_fulfill; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  exploit sim_localF_promise; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des.
  assert (NONEFOR: __guard__ ((Ordering.le Ordering.acqrel ord_tgt /\ SimPromises.mem loc to none_for = false) \/
                              Ordering.le ord_tgt Ordering.plain)).
  { destruct (Ordering.le ord_tgt Ordering.relaxed) eqn:X.
    - right. destruct ord_tgt; inv X; ss.
    - left. splits.
      { by destruct ord_tgt; inv X. }
      exploit ORD0.
      { by destruct ord_tgt; inv X. }
      i. des. subst.
      destruct (SimPromises.mem loc to none_for) eqn:Y; ss.
      inv LOCAL1. inv PROMISES. exploit NONEFOR; eauto. i. des.
      inv STEP1. inv PROMISE. exploit Memory.add_get0; try exact PROMISES; eauto. congr.
  }
  exploit sim_localF_fulfill; try apply STEP2;
    try apply LOCAL2; try apply MEM2; eauto.
  { eapply Memory.future_closed_opt_view; eauto. }
  i. des.
  exploit promise_fulfill_write; try exact STEP_SRC; try exact STEP_SRC0; eauto.
  { i. exploit ORD0; eauto.
    - etrans; eauto.
    - i. des. subst. splits; auto. eapply sim_localF_nonsynch_loc; eauto.
  }
  i. des. esplits; eauto.
  - unguardH NONEFOR. des.
    + unfold SimPromises.none_if in *. rewrite NONEFOR0 in *. ss.
    + subst. unfold TView.write_released at 1. condtac; [|by econs].
      destruct ord_src, ord_tgt; inv ORD; inv NONEFOR; inv COND.
  - etrans; eauto.
Qed.

Lemma sim_localF_update
      none_for
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt
      lc3_tgt sc3_tgt mem3_tgt
      loc ts1 val1 released1_tgt ord1_src ord1_tgt
      from2 to2 val2 released2_tgt ord2_src ord2_tgt kind
      (STEP1_TGT: Local.read_step lc1_tgt mem1_tgt loc ts1 val1 released1_tgt ord1_tgt lc2_tgt)
      (STEP2_TGT: Local.write_step lc2_tgt sc1_tgt mem1_tgt loc from2 to2 val2 released1_tgt released2_tgt ord2_tgt lc3_tgt sc3_tgt mem3_tgt kind)
      (LOCAL1: sim_localF none_for lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (SC1_TGT: Memory.closed_timemap sc1_tgt mem1_tgt)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt)
      (ORD1: Ordering.le ord1_src ord1_tgt)
      (ORD2: Ordering.le ord2_src ord2_tgt)
      (ORD2_TGT: ord2_tgt <> Ordering.relaxed):
  exists released1_src released2_src lc2_src lc3_src sc3_src mem3_src,
    <<REL1: View.opt_le released1_src released1_tgt>> /\
    <<REL2: View.opt_le released2_src released2_tgt>> /\
    <<STEP1_SRC: Local.read_step lc1_src mem1_src loc ts1 val1 released1_src ord1_src lc2_src>> /\
    <<STEP2_SRC: Local.write_step lc2_src sc1_src mem1_src loc from2 to2 val2 released1_src released2_src ord2_src lc3_src sc3_src mem3_src (SimPromises.kind_transf loc to2 none_for kind)>> /\
    <<LOCAL3: sim_localF (SimPromises.unset loc to2 none_for) lc3_src lc3_tgt>> /\
    <<SC3: TimeMap.le sc3_src sc3_tgt>> /\
    <<MEM3: sim_memory mem3_src mem3_tgt>>.
Proof.
  exploit Local.read_step_future; eauto. i. des.
  exploit sim_localF_read; eauto. i. des.
  exploit Local.read_step_future; eauto. i. des.
  hexploit sim_localF_write; eauto. i. des.
  esplits; eauto.
Qed.

Lemma sim_localF_fence
      none_for
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      ordr_src ordw_src
      ordr_tgt ordw_tgt
      (STEP_TGT: Local.fence_step lc1_tgt sc1_tgt ordr_tgt ordw_tgt lc2_tgt sc2_tgt)
      (LOCAL1: sim_localF none_for lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (ORDR: Ordering.le ordr_src ordr_tgt)
      (ORDW: Ordering.le ordw_src ordw_tgt)
      (ORDR_TGT: Ordering.le ordr_tgt Ordering.acqrel)
      (ORDW_TGT: Ordering.le ordw_tgt Ordering.relaxed):
  exists lc2_src sc2_src,
    <<STEP_SRC: Local.fence_step lc1_src sc1_src ordr_src ordw_src lc2_src sc2_src>> /\
    <<LOCAL2: sim_localF none_for lc2_src lc2_tgt>> /\
    <<SC2: TimeMap.le sc2_src sc2_tgt>>.
Proof.
  inv STEP_TGT. esplits; eauto.
  - econs; eauto. i. eapply sim_localF_nonsynch; eauto.
    apply RELEASE. etrans; eauto.
  - econs; try apply LOCAL1.
    + s. repeat (condtac; aggrtac).
      * apply LOCAL1.
      * etrans; [|apply LOCAL1]. apply WF1_SRC.
      * apply LOCAL1.
    + s. repeat (condtac; aggrtac).
      rewrite View.join_comm, View.join_bot_l. apply LOCAL1.
  - unfold TView.write_fence_sc.
    repeat (condtac; viewtac).
Qed.

Lemma sim_localF_introduction
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      (LOCAL1: sim_local lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt):
  <<LOCAL2: sim_localF SimPromises.bot lc1_src lc1_tgt>>.
Proof.
  esplits. econs; apply LOCAL1.
Qed.

Lemma sim_localF_lower_src
      none_for1
      lc1_src sc1_src mem1_src
      lc1_tgt mem1_tgt
      lc2_src mem2_src
      loc from to val released
      (LOCAL1: sim_localF none_for1 lc1_src lc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (MEM1_SRC: Memory.closed mem1_src)
      (STEP_SRC: Local.promise_step lc1_src mem1_src loc from to val None lc2_src mem2_src (Memory.op_kind_lower released)):
  <<LOCAL2: exists none_for2, sim_localF none_for2 lc2_src lc1_tgt>> /\
  <<MEM2: sim_memory mem2_src mem1_tgt>> /\
  <<WF2_SRC: Local.wf lc2_src mem2_src>>.
Proof.
  splits.
  - inv STEP_SRC. inv PROMISE.
    exists (match Memory.get loc to lc1_tgt.(Local.promises) with
       | Some _ => SimPromises.set loc to none_for1
       | None => none_for1
       end).
    inv LOCAL1. econs; ss. inv PROMISES0. econs; ss.
    + ii.
      exploit LE; eauto. i.
      exploit Memory.lower_get0; try exact PROMISES; eauto. i.
      erewrite Memory.lower_o; eauto.
      unfold SimPromises.none_if.
      destruct (Memory.get loc to (Local.promises lc1_tgt)) eqn:TGT.
      * rewrite SimPromises.set_o. condtac; ss.
        { des. subst. condtac; ss; cycle 1.
          { revert COND0. condtac; ss. des; congr. }
          rewrite x in x1. inv x1. ss.
        }
        { guardH o. condtac.
          { revert COND0. condtac; ss.
            { des. subst. unguardH o. des; congr. }
            guardH o0. i.
            rewrite x. repeat f_equal. unfold SimPromises.none_if. condtac; ss.
          }
          rewrite x. repeat f_equal. unfold SimPromises.none_if. condtac; ss.
          revert COND0. condtac; ss.
        }
      * condtac; ss. des. subst. congr.
    + i. revert MEM0. condtac; ss; cycle 1.
      { eapply NONEFOR. }
      rewrite SimPromises.set_o. condtac; ss; cycle 1.
      { eapply NONEFOR. }
      i. des. subst. destruct p. eauto.
    + i. revert SRC. erewrite Memory.lower_o; eauto. condtac; ss.
      * i. des. inv SRC. eapply COMPLETE; eauto. eapply Memory.lower_get0. eauto.
      * i. eapply COMPLETE; eauto.
  - etrans; [|eauto]. inv STEP_SRC. inv PROMISE. eapply lower_sim_memory. eauto.
  - eapply Local.promise_step_future; eauto.
Qed.

Lemma sim_localF_nonsynch_src
      none_for
      lang st sc
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      (LOCAL1: sim_localF none_for lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (LOCAL1_SRC: Local.wf lc1_src mem1_src)
      (LOCAL2_TGT: Local.wf lc1_tgt mem1_tgt)
      (SC1_SRC: Memory.closed_timemap sc1_src mem1_src)
      (MEM1_SRC: Memory.closed mem1_src)
      (MEM1_TGT: Memory.closed mem1_tgt):
  exists none_for2 lc2_src mem2_src,
    <<STEP_SRC: rtc (@Thread.tau_step lang)
                    (Thread.mk lang st lc1_src sc mem1_src)
                    (Thread.mk lang st lc2_src sc mem2_src)>> /\
    <<NONSYNCH2: Memory.nonsynch lc2_src.(Local.promises)>> /\
    <<LOCAL2: sim_localF none_for2 lc2_src lc1_tgt>> /\
    <<MEM2: sim_memory mem2_src mem1_tgt>>.
Proof.
  inversion LOCAL1_SRC. unfold Memory.finite in *. des.
  assert (FINITE' : forall (loc : Loc.t) (from to : Time.t) (msg : Message.t),
             Memory.get loc to (Local.promises lc1_src) =
             Some (from, msg) -> msg.(Message.released) <> None -> In (loc, to) dom).
  { ii. eapply FINITE. eauto. }
  clear FINITE. move dom after lc1_src. revert_until dom. revert none_for.
  induction dom.
  { esplits; eauto. ii. destruct (Message.released msg) eqn:X; ss.
    exfalso. eapply FINITE'; eauto. congr.
  }
  destruct a as [loc to]. i.
  destruct (Memory.get loc to lc1_src.(Local.promises)) as [[? []]|] eqn:X; cycle 1.
  { eapply IHdom; eauto. i. exploit FINITE'; eauto. i. inv x; ss.
    inv H1. congr.
  }
  destruct released; cycle 1.
  { eapply IHdom; eauto. i. exploit FINITE'; eauto. i. inv x; ss.
    inv H1. rewrite H in X. inv X. ss.
  }
  exploit MemoryFacts.promise_exists_None; eauto.
  { eapply MemoryFacts.some_released_time_lt; [by apply MEM1_SRC|]. apply LOCAL1_SRC. eauto. }
  i. des.
  exploit Memory.promise_future; try apply LOCAL1_SRC; eauto; try by econs. i. des.
  exploit sim_localF_lower_src; eauto.
  { econs; eauto. econs. }
  i. des.
  exploit IHdom; eauto.
  { eapply Memory.future_closed_timemap; eauto. }
  { eapply TView.future_closed; eauto. }
  { s. i. inv x0. revert H.
    erewrite Memory.lower_o; eauto. condtac; ss.
    - i. des. inv H. ss.
    - guardH o. i. exploit FINITE'; eauto. i. des; ss.  inv x.
      unguardH o. des; congr.
  }
  i. des. esplits; try exact NONSYNCH2; eauto.
  econs 2; eauto. econs.
  - econs. econs 1. econs; eauto. econs; eauto. econs.
  - ss.
Qed.

Lemma sim_localF_fence_src
      none_for
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      (NONSYNCH: Memory.nonsynch lc1_src.(Local.promises))
      (LOCAL1: sim_localF none_for lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt):
  exists lc2_src sc2_src,
    <<STEP_SRC: Local.fence_step lc1_src sc1_src Ordering.relaxed Ordering.acqrel lc2_src sc2_src>> /\
    <<LOCAL2: sim_localF none_for lc2_src lc1_tgt>> /\
    <<SC2: TimeMap.le sc2_src sc1_tgt>>.
Proof.
  esplits; ss. econs; s.
  - repeat (condtac; aggrtac). apply LOCAL1.
  - repeat (condtac; aggrtac). apply LOCAL1.
  - apply LOCAL1.
Qed.

Lemma sim_localF_elimination
      none_for
      lc1_src sc1_src mem1_src
      lc1_tgt sc1_tgt mem1_tgt
      lc2_tgt sc2_tgt
      (STEP_TGT: Local.fence_step lc1_tgt sc1_tgt Ordering.relaxed Ordering.acqrel lc2_tgt sc2_tgt)
      (LOCAL1: sim_localF none_for lc1_src lc1_tgt)
      (SC1: TimeMap.le sc1_src sc1_tgt)
      (MEM1: sim_memory mem1_src mem1_tgt)
      (WF1_SRC: Local.wf lc1_src mem1_src)
      (WF1_TGT: Local.wf lc1_tgt mem1_tgt):
  <<LOCAL2: sim_local lc1_src lc2_tgt>> /\
  <<SC2: TimeMap.le sc1_src sc2_tgt>>.
Proof.
  inv LOCAL1. inv STEP_TGT. esplits; ss.
  econs; s.
  - unfold TView.read_fence_tview. condtac; ss.
    unfold TView.write_fence_tview. econs; repeat (condtac; aggrtac).
    etrans; [|apply TVIEW_CUR]. apply WF1_SRC.
  - econs; try by apply PROMISES.
    + inv PROMISES. ii. exploit LE; eauto.
      unfold SimPromises.none_if. condtac; ss.
      exploit RELEASE; eauto. s. i. subst. ss.
    + i. rewrite SimPromises.bot_spec in *. congr.
Qed.
