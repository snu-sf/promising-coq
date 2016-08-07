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
Require Import Configuration.

Require Import PFStep.
Require Import PromiseConsistent.
Require Import ReorderPromiseSame.

Set Implicit Arguments.


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
    <<STEPS1: rtcn (@pf_step_evt lang) n' e1 e2>> /\
    <<STEPS2: rtc (@nonpf_step_evt lang) e2 e3>>.
Proof.
  revert_until n. induction n using strong_induction; i.
  inv STEPS.
  { esplits; eauto. }
  inv A12. exploit pf_step_dec; eauto. i. des.
  { exploit pf_step_future; eauto. i. des.
    exploit IH; eauto. i. des.
    esplits; cycle 1.
    + econs 2; eauto. econs; eauto.
    + auto.
    + omega.
  }
  exploit nonpf_step_future; eauto. i. des.
  exploit IH; try exact A23; try refl; eauto. i. des.
  assert (CONS2: promise_consistent (Thread.local e2)).
  { exploit rtcn_rtc; try exact A0; eauto. i.
    exploit rtc_implies; (try by apply pf_step_evt_step_evt); eauto. i.
    exploit rtc_step_evt_future; eauto. i. des.
    eapply rtc_step_evt_promise_consistent; try exact CONS; eauto.
    eapply rtc_implies; try exact STEPS2; eauto.
    apply nonpf_step_evt_step_evt.
  }
  inv STEPS1.
  { esplits; cycle 1.
    - eauto.
    - econs; eauto. econs. eauto.
    - omega.
  }
  inversion A12. exploit pf_step_future; eauto. i. des.
  exploit reorder_nonpf_pf; eauto.
  { exploit rtcn_rtc; try exact A0; eauto. i.
    eapply rtc_step_evt_promise_consistent; try exact CONS; eauto.
    etrans.
    - eapply rtc_implies; try exact x1; eauto.
      apply pf_step_evt_step_evt.
    - eapply rtc_implies; try exact STEPS2; eauto.
      apply nonpf_step_evt_step_evt.
  }
  i. des.
  - assert (STEPS: rtcn (step_evt (lang:=lang)) (S n) e1 e2).
    { econs 2.
      - econs. eauto.
      - eapply rtcn_imply; try exact A0. apply pf_step_evt_step_evt.
    }
    exploit IH; try exact STEPS; eauto.
    { omega. }
    i. des. esplits; cycle 1; eauto.
    + etrans; eauto.
    + omega.
  - assert (STEPS: rtcn (step_evt (lang:=lang)) (S n) th1' e2).
    { econs 2.
      - econs. econs 1. eauto.
      - eapply rtcn_imply; try exact A0. apply pf_step_evt_step_evt.
    }
    exploit pf_step_future; eauto. i. des.
    exploit IH; try exact STEPS; eauto.
    { omega. }
    i. des. esplits; cycle 1.
    + econs 2; eauto. econs. eauto.
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
    <<STEPS1: rtc (@pf_step_evt lang) e1 e2>> /\
    <<STEPS2: rtc (@nonpf_step_evt lang) e2 e3>>.
Proof.
  apply rtc_rtcn in STEPS. des.
  exploit steps_pf_steps_aux; eauto. i. des.
  exploit rtcn_rtc; eauto.
Qed.

Lemma tau_steps_pf_tau_steps_aux
      lang
      n e1 e3
      (STEPS: rtcn (@Thread.tau_step lang) n e1 e3)
      (CONS: promise_consistent e3.(Thread.local))
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (MEM1: Memory.closed e1.(Thread.memory)):
  exists n' e2,
    <<N: n' <= n>> /\
    <<STEPS1: rtcn (@tau_pf_step lang) n' e1 e2>> /\
    <<STEPS2: rtc (@nonpf_step_evt lang) e2 e3>>.
Proof.
  revert_until n. induction n using strong_induction; i.
  inv STEPS.
  { esplits; eauto. }
  inv A12. exploit pf_step_dec; eauto. i. des.
  { exploit pf_step_future; eauto. i. des.
    exploit IH; eauto. i. des.
    esplits; cycle 1.
    + econs 2; eauto. econs; eauto.
    + auto.
    + omega.
  }
  exploit nonpf_step_future; eauto. i. des.
  exploit IH; try exact A23; try refl; eauto. i. des.
  assert (CONS2: promise_consistent (Thread.local e2)).
  { exploit rtcn_rtc; try exact A0; eauto. i.
    exploit rtc_implies; (try by apply tau_pf_step_pf_step_evt); eauto. i.
    exploit rtc_implies; (try by apply pf_step_evt_step_evt); eauto. i.
    exploit rtc_step_evt_future; eauto. i. des.
    eapply rtc_step_evt_promise_consistent; try exact CONS; eauto.
    eapply rtc_implies; try exact STEPS2; eauto.
    apply nonpf_step_evt_step_evt.
  }
  inv STEPS1.
  { esplits; cycle 1.
    - eauto.
    - econs; eauto. econs. eauto.
    - omega.
  }
  inversion A12. exploit pf_step_future; eauto. i. des.
  exploit reorder_nonpf_pf; eauto.
  { exploit rtcn_rtc; try exact A0; eauto. i.
    eapply rtc_step_evt_promise_consistent; try exact CONS; eauto.
    etrans.
    - eapply rtc_implies; try exact x1; eauto.
      i. apply pf_step_evt_step_evt. apply tau_pf_step_pf_step_evt. ss.
    - eapply rtc_implies; try exact STEPS2; eauto.
      apply nonpf_step_evt_step_evt.
  }
  i. des.
  - assert (STEPS: rtcn (Thread.tau_step (lang:=lang)) (S n) e1 e2).
    { econs 2.
      - econs; eauto. etrans; eauto.
      - eapply rtcn_imply; try exact A0. apply tau_pf_step_tau_step.
    }
    exploit IH; try exact STEPS; eauto.
    { omega. }
    i. des. esplits; cycle 1; eauto.
    + etrans; eauto.
    + omega.
  - assert (STEPS: rtcn (Thread.tau_step (lang:=lang)) (S n) th1' e2).
    { econs 2.
      - econs. econs; eauto. by inv STEP2.
      - eapply rtcn_imply; try exact A0. apply tau_pf_step_tau_step.
    }
    exploit pf_step_future; eauto. i. des.
    exploit IH; try exact STEPS; eauto.
    { omega. }
    i. des. esplits; cycle 1.
    + econs 2; eauto. econs; eauto. etrans; eauto.
    + etrans; eauto.
    + omega.
Qed.

Lemma tau_steps_pf_tau_steps
      lang
      e1 e3
      (STEPS: rtc (@Thread.tau_step lang) e1 e3)
      (CONS: promise_consistent e3.(Thread.local))
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (MEM1: Memory.closed e1.(Thread.memory)):
  exists e2,
    <<STEPS1: rtc (@tau_pf_step lang) e1 e2>> /\
    <<STEPS2: rtc (@nonpf_step_evt lang) e2 e3>>.
Proof.
  apply rtc_rtcn in STEPS. des.
  exploit tau_steps_pf_tau_steps_aux; eauto. i. des.
  exploit rtcn_rtc; eauto.
Qed.

Lemma nonpf_step_evt_bot
      lang e1 e2
      (STEP: @nonpf_step_evt lang e1 e2)
      (PROMISE: e2.(Thread.local).(Local.promises) = Memory.bot):
  False.
Proof.
  inv STEP. inv STEP0. inv LOCAL. ss. subst. inv PROMISE0.
  - exploit (@Memory.add_o Memory.bot lc1.(Local.promises) loc from to val released loc to)
    ; try exact PROMISES; eauto. condtac; ss; [|des; congr].
    rewrite Memory.bot_get. congr.
  - exploit (@Memory.split_o Memory.bot lc1.(Local.promises) loc from to ts3 val val3 released released3 loc to)
    ; try exact PROMISES; eauto. condtac; ss; [|des; congr].
    rewrite Memory.bot_get. congr.
  - exploit (@Memory.lower_o Memory.bot lc1.(Local.promises) loc from to val released0 released loc to)
    ; try exact PROMISES; eauto. condtac; ss; [|des; congr].
    rewrite Memory.bot_get. congr.
Qed.

Lemma rtc_nonpf_step_evt_bot
      lang e1 e2
      (STEPS: rtc (@nonpf_step_evt lang) e1 e2)
      (PROMISE: e2.(Thread.local).(Local.promises) = Memory.bot):
  e1 = e2.
Proof.
  exploit rtc_tail; eauto. i. des; ss.
  exfalso. eapply nonpf_step_evt_bot; eauto.
Qed.
