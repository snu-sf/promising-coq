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

Require Import PromiseConsistent.
Require Import ReorderThreadStepSame.

Set Implicit Arguments.


Inductive tau_program_step lang e1 e2: Prop :=
| step_program_tau
    e
    (STEP: @Thread.program_step lang e e1 e2)
    (TAU: ThreadEvent.get_event e = None)
.

Definition pf_consistent lang (e:Thread.t lang): Prop :=
  forall sc1 mem1
    (FUTURE: Memory.future e.(Thread.memory) mem1)
    (FUTURE: TimeMap.le e.(Thread.sc) sc1)
    (WF: Local.wf e.(Thread.local) mem1)
    (SC: Memory.closed_timemap sc1 mem1)
    (MEM: Memory.closed mem1),
  exists e2,
    <<STEPS: rtc (@tau_program_step lang) (Thread.mk lang e.(Thread.state) e.(Thread.local) sc1 mem1) e2>> /\
    <<PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot>>.

Lemma steps_pf_steps
      lang
      n e1 e2
      (STEPS: rtcn (@Thread.tau_step lang) n e1 e2)
      (PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot)
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (MEM1: Memory.closed e1.(Thread.memory)):
  exists n' e2',
    <<N: n' <= n>> /\
    <<STEPS: rtcn (@tau_program_step lang) n' e1 e2'>> /\
    <<PROMISES: e2'.(Thread.local).(Local.promises) = Memory.bot>>.
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
  inv STEPS.
  { inv STEP0. ss. inv LOCAL. ss. subst.
    exploit Memory.promise_get2; eauto. rewrite Memory.bot_get. congr.
  }
  inversion A12. exploit Thread.program_step_future; eauto. i. des.
  exploit reorder_promise_program; eauto.
  { exploit rtcn_rtc; try exact A0; eauto. i.
    eapply rtc_tau_step_promise_consistent.
    - eapply rtc_implies; [|eauto]. i. inv PR. econs; eauto. econs 2; eauto.
    - ii. rewrite PROMISES0, Memory.bot_get in *. congr.
    - auto.
    - auto.
    - auto.
  }
  i. des.
  exploit Thread.program_step_future; eauto. i. des.
  unguardH STEP2. des.
  - subst. esplits; cycle 1.
    + econs 2; eauto. econs; eauto.
    + auto.
    + omega.
  - exploit Thread.promise_step_future; try exact STEP2; eauto. i. des.
    assert (STEPS: rtcn (Thread.tau_step (lang:=lang)) (S n) th1' e2').
    { econs 2.
      - econs.
        + econs 1. apply STEP2.
        + by inv STEP2.
      - eapply rtcn_imply; try exact A0. i. inv PR. econs; eauto. econs 2; eauto.
    }
    exploit IH; try exact STEPS; eauto.
    { omega. }
    i. des. esplits; cycle 1.
    + econs; [|eauto]. econs; eauto.
    + auto.
    + omega.
Qed.

Lemma consistent_pf_consistent:
  Thread.consistent <2= pf_consistent.
Proof.
  s. ii. exploit PR; eauto. i. des.
  exploit rtc_rtcn; eauto. i. des.
  exploit steps_pf_steps; eauto. i. des.
  exploit rtcn_rtc; eauto.
Qed.
