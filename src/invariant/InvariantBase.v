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
Require Import Configuration.

Require Import PromiseConsistent.
Require Import ReorderThreadStepSame.

Set Implicit Arguments.


Inductive step_evt lang (e1 e2:Thread.t lang): Prop :=
| step_evt_intro
    e
    (STEP: Thread.step e e1 e2)
.

Inductive program_step_evt lang (e1 e2:Thread.t lang): Prop :=
| program_step_evt_intro
    e
    (STEP: Thread.program_step e e1 e2)
.

Inductive promise_step_evt lang (e1 e2:Thread.t lang): Prop :=
| promise_step_evt_intro
    e
    (STEP: Thread.promise_step e e1 e2)
.

Lemma step_evt_future lang (e1 e2:Thread.t lang)
      (STEP: step_evt e1 e2)
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (CLOSED1: Memory.closed e1.(Thread.memory)):
  <<WF2: Local.wf e2.(Thread.local) e2.(Thread.memory)>> /\
  <<SC2: Memory.closed_timemap e2.(Thread.sc) e2.(Thread.memory)>> /\
  <<CLOSED2: Memory.closed e2.(Thread.memory)>> /\
  <<COMMIT_FUTURE: Commit.le e1.(Thread.local).(Local.commit) e2.(Thread.local).(Local.commit)>> /\
  <<SC_FUTURE: TimeMap.le e1.(Thread.sc) e2.(Thread.sc)>> /\
  <<MEM_FUTURE: Memory.future e1.(Thread.memory) e2.(Thread.memory)>>.
Proof.
  inv STEP. eapply Thread.step_future; eauto.
Qed.

Lemma rtc_step_evt_future lang (e1 e2:Thread.t lang)
      (STEP: rtc (@step_evt lang) e1 e2)
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (CLOSED1: Memory.closed e1.(Thread.memory)):
  <<WF2: Local.wf e2.(Thread.local) e2.(Thread.memory)>> /\
  <<SC2: Memory.closed_timemap e2.(Thread.sc) e2.(Thread.memory)>> /\
  <<CLOSED2: Memory.closed e2.(Thread.memory)>> /\
  <<COMMIT_FUTURE: Commit.le e1.(Thread.local).(Local.commit) e2.(Thread.local).(Local.commit)>> /\
  <<SC_FUTURE: TimeMap.le e1.(Thread.sc) e2.(Thread.sc)>> /\
  <<MEM_FUTURE: Memory.future e1.(Thread.memory) e2.(Thread.memory)>>.
Proof.
  revert WF1. induction STEP.
  - i. splits; ss; refl.
  - i. exploit step_evt_future; eauto. i. des.
    exploit IHSTEP; eauto. i. des.
    splits; ss; etrans; eauto.
Qed.

Lemma promise_step_evt_future lang (e1 e2:Thread.t lang)
      (STEP: promise_step_evt e1 e2)
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (CLOSED1: Memory.closed e1.(Thread.memory)):
  <<WF2: Local.wf e2.(Thread.local) e2.(Thread.memory)>> /\
  <<SC2: Memory.closed_timemap e2.(Thread.sc) e2.(Thread.memory)>> /\
  <<CLOSED2: Memory.closed e2.(Thread.memory)>> /\
  <<COMMIT_FUTURE: Commit.le e1.(Thread.local).(Local.commit) e2.(Thread.local).(Local.commit)>> /\
  <<SC_FUTURE: TimeMap.le e1.(Thread.sc) e2.(Thread.sc)>> /\
  <<MEM_FUTURE: Memory.future e1.(Thread.memory) e2.(Thread.memory)>> /\
  <<STATE: e1.(Thread.state) = e2.(Thread.state)>>.
Proof.
  inv STEP. exploit Thread.promise_step_future; eauto. i. des.
  inv STEP0. ss. esplits; eauto. refl.
Qed.

Lemma rtc_promise_step_evt_future lang (e1 e2:Thread.t lang)
      (STEP: rtc (@promise_step_evt lang) e1 e2)
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (CLOSED1: Memory.closed e1.(Thread.memory)):
  <<WF2: Local.wf e2.(Thread.local) e2.(Thread.memory)>> /\
  <<SC2: Memory.closed_timemap e2.(Thread.sc) e2.(Thread.memory)>> /\
  <<CLOSED2: Memory.closed e2.(Thread.memory)>> /\
  <<COMMIT_FUTURE: Commit.le e1.(Thread.local).(Local.commit) e2.(Thread.local).(Local.commit)>> /\
  <<SC_FUTURE: TimeMap.le e1.(Thread.sc) e2.(Thread.sc)>> /\
  <<MEM_FUTURE: Memory.future e1.(Thread.memory) e2.(Thread.memory)>> /\
  <<STATE: e1.(Thread.state) = e2.(Thread.state)>>.
Proof.
  revert WF1. induction STEP.
  - i. splits; ss; refl.
  - i. exploit promise_step_evt_future; eauto. i. des.
    exploit IHSTEP; eauto. i. des.
    splits; ss; etrans; eauto.
Qed.

Lemma tau_program_step_program_step_evt:
  SmallStep.tau_program_step <3= program_step_evt.
Proof.
  i. inv PR. econs. eauto.
Qed.

Lemma tau_step_step_evt:
  Thread.tau_step <3= step_evt.
Proof.
  i. inv PR. econs. eauto.
Qed.

Lemma program_step_evt_step_evt:
  program_step_evt <3= step_evt.
Proof.
  i. inv PR. econs. eauto.
Qed.

Lemma promise_step_evt_step_evt:
  promise_step_evt <3= step_evt.
Proof.
  i. inv PR. econs. eauto.
Qed.

Lemma rtc_step_evt_promise_consistent
      lang th1 th2
      (STEP: rtc (@step_evt lang) th1 th2)
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

Lemma steps_pf_steps_aux
      lang
      n e1 e3
      (STEPS: rtcn (@step_evt lang) n e1 e3)
      (CONS: promise_consistent e3.(Thread.local))
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (MEM1: Memory.closed e1.(Thread.memory)):
  exists n' e2,
    <<N: n' <= n>> /\
    <<STEPS1: rtcn (@program_step_evt lang) n' e1 e2>> /\
    <<STEPS2: rtc (@promise_step_evt lang) e2 e3>>.
Proof.
  revert_until n. induction n using strong_induction; i.
  inv STEPS.
  { esplits; eauto. }
  inv A12. inv STEP; cycle 1.
  { exploit Thread.program_step_future; eauto. i. des.
    exploit IH; eauto. i. des.
    esplits; cycle 1.
    + econs 2; eauto. econs; eauto.
    + auto.
    + omega.
  }
  exploit Thread.promise_step_future; eauto. i. des.
  exploit IH; try exact A23; try refl; eauto. i. des.
  inv STEPS1.
  { esplits; cycle 1.
    - eauto.
    - econs; eauto. econs. eauto.
    - omega.
  }
  inversion A12. exploit Thread.program_step_future; eauto. i. des.
  exploit reorder_promise_program; eauto.
  { exploit rtcn_rtc; try exact A0; eauto. i.
    eapply rtc_step_evt_promise_consistent; try exact CONS; eauto.
    etrans.
    - eapply rtc_implies; try exact x0; eauto.
      apply program_step_evt_step_evt.
    - eapply rtc_implies; try exact STEPS2; eauto.
      apply promise_step_evt_step_evt.
  }
  i. des.
  exploit Thread.program_step_future; eauto. i. des.
  unguardH STEP2. des.
  - subst. esplits; cycle 1.
    + econs 2; eauto. econs. eauto.
    + auto.
    + omega.
  - exploit Thread.promise_step_future; try exact STEP2; eauto. i. des.
    assert (STEPS: rtcn (step_evt (lang:=lang)) (S n) th1' e2).
    { econs 2.
      - econs. econs 1. apply STEP2.
      - eapply rtcn_imply; try exact A0. i. inv PR. econs; eauto.
    }
    exploit rtcn_rtc; eauto. i.
    exploit rtc_step_evt_future; eauto. i. des.
    exploit IH; try exact STEPS; eauto.
    { omega. }
    { eapply rtc_step_evt_promise_consistent; try exact CONS; eauto.
      eapply rtc_implies; try exact STEPS2; eauto.
      apply promise_step_evt_step_evt.
    }
    i. des. esplits; cycle 1.
    + econs; [|eauto]. econs; eauto.
    + etrans; eauto.
    + omega.
Qed.

Lemma steps_pf_steps
      lang
      e1 e3
      (STEPS: rtc (@step_evt lang) e1 e3)
      (CONS: promise_consistent e3.(Thread.local))
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (MEM1: Memory.closed e1.(Thread.memory)):
  exists e2,
    <<STEPS1: rtc (@program_step_evt lang) e1 e2>> /\
    <<STEPS2: rtc (@promise_step_evt lang) e2 e3>>.
Proof.
  apply rtc_rtcn in STEPS. des.
  exploit steps_pf_steps_aux; eauto. i. des.
  exploit rtcn_rtc; eauto.
Qed.
