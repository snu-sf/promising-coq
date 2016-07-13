Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import MemoryFacts.
Require Import TView.
Require Import Thread.

Set Implicit Arguments.


Lemma write_step_promise
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
      (PROMISES: lc1.(Local.promises) = Memory.bot):
  lc2.(Local.promises) = Memory.bot.
Proof.
  inv STEP. rewrite PROMISES in *. s.
  apply Memory.ext. i. rewrite Memory.bot_get.
  inv WRITE.
  erewrite Memory.remove_o; eauto. condtac; ss. guardH o.
  inv PROMISE.
  - erewrite Memory.add_o; eauto. condtac; ss.
    apply Memory.bot_get.
  - erewrite Memory.split_o; eauto. repeat condtac; ss.
    + guardH o0. des. subst.
      exploit Memory.split_get0; try exact PROMISES0; eauto. i. des.
      rewrite Memory.bot_get in *. congr.
    + apply Memory.bot_get.
  - erewrite Memory.lower_o; eauto. condtac; ss.
    apply Memory.bot_get.
Qed.

Lemma program_step_promise
      lang e
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (STEP: Thread.program_step e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2))
      (PROMISES: lc1.(Local.promises) = Memory.bot):
  lc2.(Local.promises) = Memory.bot.
Proof.
  inv STEP; (try by inv LOCAL); eauto.
  - eapply write_step_promise; eauto.
  - eapply write_step_promise; eauto.
    inv LOCAL1. auto.
Qed.

Lemma closed_timemap_max_ts
      loc tm mem
      (CLOSED: Memory.closed_timemap tm mem):
  Time.le (tm loc) (Memory.max_ts loc mem).
Proof.
  specialize (CLOSED loc). des.
  eapply Memory.max_ts_spec. eauto.
Qed.

Lemma progress_promise_step
      lc1 sc1 mem1
      loc to val releasedm ord
      (LT: Time.lt (Memory.max_ts loc mem1) to)
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      (WF_REL: View.wf releasedm)
      (CLOSED_REL: Memory.closed_view releasedm mem1):
  exists promises2 mem2,
    Local.promise_step lc1 mem1 loc (Memory.max_ts loc mem1) to val
                       (TView.write_released (Local.tview lc1) sc1 loc to releasedm ord)
                       (Local.mk lc1.(Local.tview) promises2) mem2 Memory.op_kind_add.
Proof.
  exploit (@Memory.add_exists_max_ts
             mem1 loc to val
             (TView.write_released (Local.tview lc1) sc1 loc to releasedm ord)); eauto.
  { eapply TViewFacts.write_future0; eauto. apply WF1. }
  i. des.
  exploit Memory.add_exists_le; try apply WF1; eauto. i. des.
  hexploit Memory.add_inhabited; try apply x0; [viewtac|]. i. des.
  esplits. econs.
  - econs; eauto.
    unfold TView.write_released.
    viewtac; repeat (condtac; viewtac);
      (try by apply Time.bot_spec);
      (try by unfold TimeMap.singleton, LocFun.add; condtac; [refl|congr]);
      (try by left; eapply TimeFacts.le_lt_lt; [|eauto];
       eapply closed_timemap_max_ts; apply WF1).
    left. eapply TimeFacts.le_lt_lt; [|eauto].
    eapply closed_timemap_max_ts. apply CLOSED_REL.
  - unfold TView.write_released.
    viewtac;
      repeat condtac; viewtac;
        (try eapply Memory.add_closed_view; eauto);
        (try apply WF1).
    + erewrite Memory.add_o; eauto. condtac; eauto. ss. des; congr.
    + econs; try apply Memory.closed_timemap_bot; viewtac.
    + erewrite Memory.add_o; eauto. condtac; eauto. ss. des; congr.
Qed.

Lemma progress_read_step
      lc1 mem1
      loc ord
      (WF1: Local.wf lc1 mem1)
      (MEM1: Memory.closed mem1)
      (PROMISES1: lc1.(Local.promises) = Memory.bot):
  exists val released lc2,
    Local.read_step lc1 mem1 loc (Memory.max_ts loc mem1) val released ord lc2.
Proof.
  exploit (Memory.max_ts_spec loc); try apply MEM1; eauto. i. des.
  esplits; eauto. econs; eauto.
  econs; try by i; eapply Memory.max_ts_spec2; apply WF1.
  i. eapply Memory.max_ts_spec2. eapply MEM1. eauto.
Qed.

Lemma progress_write_step
      lc1 sc1 mem1
      loc to val releasedm ord
      (LT: Time.lt (Memory.max_ts loc mem1) to)
      (WF1: Local.wf lc1 mem1)
      (SC1: Memory.closed_timemap sc1 mem1)
      (MEM1: Memory.closed mem1)
      (WF_REL: View.wf releasedm)
      (CLOSED_REL: Memory.closed_view releasedm mem1)
      (PROMISES1: lc1.(Local.promises) = Memory.bot):
  exists released lc2 sc2 mem2,
    Local.write_step lc1 sc1 mem1 loc (Memory.max_ts loc mem1) to val releasedm released ord lc2 sc2 mem2 Memory.op_kind_add.
Proof.
  exploit progress_promise_step; eauto. i. des.
  exploit Local.promise_step_future; eauto. i. des. inv x0.
  assert (PROMISES2:
            promises2 = Memory.singleton
                          loc val
                          (TView.write_released (Local.tview lc1) sc1 loc to releasedm ord)
                          LT).
  { apply Memory.ext. i.
    inv PROMISE. erewrite Memory.add_o; eauto.
    rewrite PROMISES1, Memory.bot_get, Memory.singleton_get.
    repeat (condtac; unfold fst, snd in *; des; subst; auto; try congr).
  }
  esplits. econs; eauto.
  - econs; i; (try eapply TimeFacts.le_lt_lt; [|eauto]).
    + apply Memory.max_ts_spec2. apply WF1.
    + apply Memory.max_ts_spec2. apply WF1.
    + apply Memory.max_ts_spec2. auto.
  - econs; eauto. subst promises2. apply Memory.remove_singleton.
  - rewrite PROMISES1. auto.
Qed.

Lemma progress_fence_step
      lc1 sc1
      ordr ordw:
  exists lc2 sc2,
    Local.fence_step lc1 sc1 ordr ordw lc2 sc2.
Proof.
  esplits. econs; eauto.
Qed.
