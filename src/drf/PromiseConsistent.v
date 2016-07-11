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
Require Import TView.
Require Import Thread.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import FulfillStep.
Require Import MemoryReorder.
Require Import Configuration.
Require Import SmallStep.

Set Implicit Arguments.


Definition promise_consistent (lc:Local.t): Prop :=
  forall loc ts from msg
    (PROMISE: Memory.get loc ts lc.(Local.promises) = Some (from, msg)),
    Time.lt (lc.(Local.tview).(TView.cur).(View.rlx) loc) ts.

Definition promise_consistent_th (tid: Ident.t) (c: Configuration.t) : Prop :=
  forall lst lc
         (THREAD: IdentMap.find tid c.(Configuration.threads) = Some (lst, lc)),
  promise_consistent lc.

Lemma promise_step_promise_consistent
      lc1 mem1 loc from to val released lc2 mem2 kind
      (STEP: Local.promise_step lc1 mem1 loc from to val released lc2 mem2 kind)
      (CONS: promise_consistent lc2):
  promise_consistent lc1.
Proof.
  inv STEP. ii. destruct msg.
  exploit Memory.promise_promises_get1; eauto. i. des.
  exploit CONS; eauto.
Qed.

Lemma read_step_promise_consistent
      lc1 mem1 loc to val released ord lc2
      (STEP: Local.read_step lc1 mem1 loc to val released ord lc2)
      (CONS: promise_consistent lc2):
  promise_consistent lc1.
Proof.
  inv STEP. ii. exploit CONS; eauto. i.
  eapply TimeFacts.le_lt_lt; eauto. ss.
  etrans; [|apply Time.join_l]. etrans; [|apply Time.join_l]. refl.
Qed.

Lemma fulfill_unset_promises
      loc from ts val rel
      promises1 promises2
      l t f m
      (FULFILL: Memory.remove promises1 loc from ts val rel promises2)
      (TH1: Memory.get l t promises1 = Some (f, m))
      (TH2: Memory.get l t promises2 = None):
  l = loc /\ t = ts /\ f = from /\ m.(Message.val) = val /\ View.le rel m.(Message.released).
Proof.
  revert TH2. erewrite Memory.remove_o; eauto. condtac; ss; [|congr].
  des. subst. erewrite Memory.remove_get0 in TH1; eauto. inv TH1.
  esplits; eauto. refl.
Qed.

Lemma write_step_promise_consistent
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
      (CONS: promise_consistent lc2):
  promise_consistent lc1.
Proof.
  inv STEP. ii.
  destruct (Memory.get loc0 ts promises2) as [[]|] eqn:X.
  - apply CONS in X. eapply TimeFacts.le_lt_lt; eauto.
    s. etrans; [|apply Time.join_l]. etrans; [|apply Time.join_l]. refl.
  - destruct msg. inv WRITE.
    exploit Memory.promise_promises_get1; eauto. i. des.
    exploit fulfill_unset_promises; eauto. i. des. subst.
    apply WRITABLE.
Qed.

Lemma fence_step_promise_consistent
      lc1 sc1 mem1 ordr ordw lc2 sc2
      (STEP: Local.fence_step lc1 sc1 ordr ordw lc2 sc2)
      (WF: Local.wf lc1 mem1)
      (SC: Memory.closed_timemap sc1 mem1)
      (MEM: Memory.closed mem1)
      (CONS: promise_consistent lc2):
  promise_consistent lc1.
Proof.
  exploit Local.fence_step_future; eauto. i. des.
  inversion STEP. subst. ii. exploit CONS; eauto. i.
  eapply TimeFacts.le_lt_lt; eauto. apply TVIEW_FUTURE. 
Qed.

Lemma ordering_relaxed_dec
      ord:
  Ordering.le ord Ordering.relaxed \/ Ordering.le Ordering.acqrel ord.
Proof. destruct ord; auto. Qed.

Lemma step_promise_consistent
      lang e th1 th2
      (STEP: @Thread.step lang e th1 th2)
      (CONS: promise_consistent th2.(Thread.local))
      (WF1: Local.wf th1.(Thread.local) th1.(Thread.memory))
      (SC1: Memory.closed_timemap th1.(Thread.sc) th1.(Thread.memory))
      (MEM1: Memory.closed th1.(Thread.memory)):
  promise_consistent th1.(Thread.local).
Proof.
  inv STEP; inv STEP0; ss.
  - eapply promise_step_promise_consistent; eauto.
  - eapply read_step_promise_consistent; eauto.
  - eapply write_step_promise_consistent; eauto.
  - eapply read_step_promise_consistent; eauto.
    eapply write_step_promise_consistent; eauto.
  - eapply fence_step_promise_consistent; eauto.
  - eapply fence_step_promise_consistent; eauto.
Qed.

Lemma rtc_tau_step_promise_consistent
      lang th1 th2
      (STEP: rtc (@Thread.tau_step lang) th1 th2)
      (CONS: promise_consistent th2.(Thread.local))
      (WF1: Local.wf th1.(Thread.local) th1.(Thread.memory))
      (SC1: Memory.closed_timemap th1.(Thread.sc) th1.(Thread.memory))
      (MEM1: Memory.closed th1.(Thread.memory)):
  promise_consistent th1.(Thread.local).
Proof.
  revert_until STEP. induction STEP; auto. i.
  inv H. exploit Thread.step_future; eauto. i. des.
  eapply step_promise_consistent; eauto.
Qed.

Lemma consistent_promise_consistent
      lang th
      (CONS: @Thread.consistent lang th)
      (WF: Local.wf th.(Thread.local) th.(Thread.memory))
      (SC: Memory.closed_timemap th.(Thread.sc) th.(Thread.memory))
      (MEM: Memory.closed th.(Thread.memory)):
  promise_consistent th.(Thread.local).
Proof.
  exploit CONS; eauto; try refl. i. des.
  eapply rtc_tau_step_promise_consistent; (try by destruct th; eauto).
  ii. rewrite PROMISES, Memory.bot_get in *. congr.
Qed.

Lemma promise_consistent_promise_read
      lc1 mem1 loc to val ord released lc2
      f t m
      (STEP: Local.read_step lc1 mem1 loc to val released ord lc2)
      (PROMISE: Memory.get loc t lc1.(Local.promises) = Some (f, m))
      (CONS: promise_consistent lc2):
  Time.lt to t.
Proof.
  inv STEP. exploit CONS; eauto. s. i.
  apply TimeFacts.join_lt_des in x. des.
  apply TimeFacts.join_lt_des in AC. des.
  revert BC0. unfold TimeMap.singleton, LocFun.add. condtac; ss. congr.
Qed.

Lemma promise_consistent_promise_write
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
      f t m
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
      (PROMISE: Memory.get loc t lc1.(Local.promises) = Some (f, m))
      (CONS: promise_consistent lc2):
  Time.le to t.
Proof.
  destruct (Memory.get loc t (Local.promises lc2)) as [[]|] eqn:X.
  - inv STEP. inv WRITE. destruct m.
    exploit CONS; eauto. i. ss.
    apply TimeFacts.join_lt_des in x. des.
    apply TimeFacts.join_lt_des in AC. des.
    left. revert BC0. unfold TimeMap.singleton, LocFun.add. condtac; ss. congr.
  - inv STEP. inv WRITE. destruct m.
    exploit Memory.promise_promises_get1; eauto. i. des.
    exploit fulfill_unset_promises; eauto. i. des. subst. refl.
Qed.  

Lemma thread_step_unset_promises
      lang loc e from ts msg (th1 th2:Thread.t lang)
      (STEP: Thread.step e th1 th2)
      (TH1: Memory.get loc ts th1.(Thread.local).(Local.promises) = Some (from, msg))
      (TH2: Memory.get loc ts th2.(Thread.local).(Local.promises) = None):
  exists ord from val rel,
  <<EVENT: ThreadEvent.is_writing e = Some (loc, from, ts, val, rel, ord)>> /\
  <<ORD: Ordering.le ord Ordering.relaxed>> /\
  <<TIME: Time.lt (th1.(Thread.local).(Local.tview).(TView.cur).(View.rlx) loc) ts>>.
Proof.
  inv STEP.
  { inv STEP0. inv LOCAL. destruct msg. ss. 
    exploit Memory.promise_promises_get1; eauto. i. des. congr.
  }
  destruct msg.
  inv STEP0; ss; try by inv LOCAL; ss; congr.
  - by rewrite TH1 in TH2.
  - inv LOCAL. inv WRITE.
    exploit Memory.promise_promises_get1; eauto. i. des.
    exploit fulfill_unset_promises; eauto. i. des. subst.
    unfold Memory.get in *.
    esplits; s; eauto.
    + edestruct ordering_relaxed_dec; eauto.
      apply RELEASE in H. des. ss. by rewrite H, Cell.bot_get in TH1.
    + inv WRITABLE. eauto.
  - inv LOCAL1. inv LOCAL2. inv WRITE.
    exploit Memory.promise_promises_get1; eauto. i. des.
    exploit fulfill_unset_promises; eauto. i. des. subst.
    unfold Memory.get in *.
    esplits; s; eauto.
    + edestruct ordering_relaxed_dec; eauto.
      apply RELEASE in H. des. ss. by rewrite H, Cell.bot_get in TH1.
    + inv WRITABLE. inv READABLE. ss. move TS at bottom.
      eapply TimeFacts.le_lt_lt; eauto.
      repeat (etrans; [|apply Time.join_l]). refl.
Qed.

Lemma rtc_small_step_unset_promises
      tid loc ts c1 lst1 lc1 c2 lst2 lc2 from msg withprm
      (STEPS: rtc (small_step_evt withprm tid) c1 c2)
      (WF: Configuration.wf c1)
      (FIND1: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1))
      (GET1: Memory.get loc ts lc1.(Local.promises) = Some (from, msg))
      (FIND2: IdentMap.find tid c2.(Configuration.threads) = Some (lst2, lc2))
      (GET2: Memory.get loc ts lc2.(Local.promises) = None):
  Time.lt (lc1.(Local.tview).(TView.cur).(View.rlx) loc) ts.
Proof.
  ginduction STEPS; i; subst.
  { ss. rewrite FIND1 in FIND2. depdes FIND2.
    by rewrite GET1 in GET2.
  }
  inv H. 
  exploit small_step_future; eauto. intros [WF2 _].
  inv USTEP. ss. rewrite FIND1 in TID. depdes TID.
  destruct (Memory.get loc ts lc3.(Local.promises)) as [[t m]|] eqn: PRM.
  - rewrite IdentMap.gss in IHSTEPS.
    exploit IHSTEPS; eauto.
    intro LT. move STEP at bottom.
    eapply TimeFacts.le_lt_lt; eauto.
    inv WF. exploit thread_step_tview_le; try exact STEP; eauto. 
    { eapply WF0. rewrite FIND1. eauto. }
    s. i. apply x1.
  - eapply thread_step_unset_promises in STEP; eauto. des.
    eauto using small_step_write_lt.
Qed.

Lemma promise_consistent_th_small_step
      tid c1 c2 withprm tid'
      (STEP: small_step_evt withprm tid c1 c2)
      (WF: Configuration.wf c1)
      (FULFILL: promise_consistent_th tid' c2):
  promise_consistent_th tid' c1.
Proof.
  destruct (Ident.eq_dec tid' tid); cycle 1.
  { ii. eapply FULFILL; eauto.
    inv STEP. inv USTEP. s. rewrite IdentMap.gso; eauto.
  }
  subst.
  ii. destruct (IdentMap.find tid (Configuration.threads c2)) as [[lang2 lc2]|] eqn: THREAD2; cycle 1.
  { inv STEP. inv USTEP. ss. by rewrite IdentMap.gss in THREAD2. }
  destruct (Memory.get loc ts (Local.promises lc2)) as [[from2 msg2]|] eqn: PROMISE2; cycle 1.
  - apply Operators_Properties.clos_rt1n_step in STEP.
    eapply rtc_small_step_unset_promises; eauto.
  - eapply FULFILL in PROMISE2; eauto.
    eapply TimeFacts.le_lt_lt; eauto.
    inv STEP. inv USTEP. ss.
    rewrite THREAD in TID. inv TID.
    rewrite IdentMap.gss in THREAD2. inv THREAD2.
    inv WF. exploit thread_step_tview_le; try exact STEP; eauto. 
    { eapply WF0. rewrite THREAD. eauto. }
    s. i. apply x0.
Qed.

Lemma promise_consistent_th_rtc_small_step
      tid c1 c2 withprm tid'
      (STEP: rtc (small_step_evt withprm tid) c1 c2)
      (WF: Configuration.wf c1)
      (FULFILL: promise_consistent_th tid' c2):
  promise_consistent_th tid' c1.
Proof.
  ginduction STEP; eauto. 
  i. eapply promise_consistent_th_small_step; eauto.
  eapply IHSTEP; eauto.
  inv H. eapply small_step_future; eauto.
Qed.

Lemma consistent_promise_consistent_th
      tid c 
      (WF: Configuration.wf c)
      (CONSISTENT: Configuration.consistent c):
  promise_consistent_th tid c.
Proof.
  ii. assert (X:= WF). inv X. inv WF0. destruct lst as [lang st].
  exploit CONSISTENT; eauto; try reflexivity.
  i; des. destruct e2.
  exploit rtc_thread_step_rtc_small_step; [eauto|..].
  { ss. eapply rtc_implies, STEPS. i; inv PR; eauto. }
  intro STEPS2. 
  eapply rtc_small_step_unset_promises in STEPS2; eauto.
  - destruct c. eapply rtc_small_step_future; eauto.
  - s. rewrite IdentMap.gss. eauto.
  - ss. rewrite PROMISES. apply Cell.bot_get.
Grab Existential Variables. exact true.
Qed.

