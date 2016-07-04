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
Require Import Commit.
Require Import Thread.

Require Import SimMemory.
Require Import SimPromises.
Require Import SimLocal.
Require Import FulfillStep.
Require Import MemoryReorder.

Set Implicit Arguments.


Definition promise_consistent (lc:Local.t): Prop :=
  forall loc ts from msg
    (PROMISE: Memory.get loc ts lc.(Local.promises) = Some (from, msg)),
    Time.lt (lc.(Local.commit).(Commit.cur).(Capability.rw) loc) ts.

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
  l = loc /\ t = ts /\ f = from /\ m.(Message.val) = val /\ Capability.le rel m.(Message.released).
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
  eapply TimeFacts.le_lt_lt; eauto. apply COMMIT_FUTURE. 
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

(* TODO *)
Lemma join_lt_des a b c
      (LT: Time.lt (Time.join a b) c):
  <<AC: Time.lt a c>> /\
  <<BC: Time.lt b c>>.
Proof.
  splits.
  - eapply TimeFacts.le_lt_lt; eauto. apply Time.join_l.
  - eapply TimeFacts.le_lt_lt; eauto. apply Time.join_r.
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
  apply join_lt_des in x. des.
  apply join_lt_des in AC. des.
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
    apply join_lt_des in x. des.
    apply join_lt_des in AC. des.
    left. revert BC0. unfold TimeMap.singleton, LocFun.add. condtac; ss. congr.
  - inv STEP. inv WRITE. destruct m.
    exploit Memory.promise_promises_get1; eauto. i. des.
    exploit fulfill_unset_promises; eauto. i. des. subst. refl.
Qed.  
