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


Set Implicit Arguments.


Inductive nonpf_step lang: forall (e:ThreadEvent.t) (e1 e2:Thread.t lang), Prop :=
| nonpf_step_intro
    st lc1 sc1 mem1
    loc from to val released kind
    lc2 mem2
    (LOCAL: Local.promise_step lc1 mem1 loc from to val released lc2 mem2 kind)
    (NONPF: Memory.op_kind_is_lower kind = false \/ released <> None):
    nonpf_step (ThreadEvent.promise loc from to val released) (Thread.mk lang st lc1 sc1 mem1) (Thread.mk lang st lc2 sc1 mem2)
.

Inductive pf_step lang: forall (e:ThreadEvent.t) (e1 e2:Thread.t lang), Prop :=
| step_pf_lower
    st lc1 sc1 mem1
    loc from to val kind
    lc2 mem2
    (LOCAL: Local.promise_step lc1 mem1 loc from to val None lc2 mem2 kind)
    (KIND: Memory.op_kind_is_lower kind):
    pf_step (ThreadEvent.promise loc from to val None) (Thread.mk lang st lc1 sc1 mem1) (Thread.mk lang st lc2 sc1 mem2)
| step_pf_program
    e e1 e2
    (STEP: Thread.program_step e e1 e2):
    pf_step e e1 e2
.

Lemma nonpf_step_future
      lang e e1 e2
      (STEP: @nonpf_step lang e e1 e2)
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (CLOSED1: Memory.closed e1.(Thread.memory)):
  <<WF2: Local.wf e2.(Thread.local) e2.(Thread.memory)>> /\
  <<SC2: Memory.closed_timemap e2.(Thread.sc) e2.(Thread.memory)>> /\
  <<CLOSED2: Memory.closed e2.(Thread.memory)>> /\
  <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
  <<SC_FUTURE: TimeMap.le e1.(Thread.sc) e2.(Thread.sc)>> /\
  <<MEM_FUTURE: Memory.future e1.(Thread.memory) e2.(Thread.memory)>>.
Proof.
  inv STEP. ss. guardH NONPF.
  exploit Local.promise_step_future; eauto. i. des.
  splits; eauto. refl.
Qed.

Lemma pf_step_future
      lang e e1 e2
      (STEP: @pf_step lang e e1 e2)
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (CLOSED1: Memory.closed e1.(Thread.memory)):
  <<WF2: Local.wf e2.(Thread.local) e2.(Thread.memory)>> /\
  <<SC2: Memory.closed_timemap e2.(Thread.sc) e2.(Thread.memory)>> /\
  <<CLOSED2: Memory.closed e2.(Thread.memory)>> /\
  <<TVIEW_FUTURE: TView.le e1.(Thread.local).(Local.tview) e2.(Thread.local).(Local.tview)>> /\
  <<SC_FUTURE: TimeMap.le e1.(Thread.sc) e2.(Thread.sc)>> /\
  <<MEM_FUTURE: Memory.future e1.(Thread.memory) e2.(Thread.memory)>>.
Proof.
  inv STEP; ss.
  - exploit Local.promise_step_future; eauto. i. des.
    splits; eauto. refl.
  - eapply Thread.program_step_future; eauto.
Qed.

Lemma pf_step_dec
      lang e e1 e2
      (STEP: @Thread.step lang e e1 e2):
  pf_step e e1 e2 \/ nonpf_step e e1 e2.
Proof.
  inv STEP.
  - inv STEP0. destruct kind; try by right; econs; eauto.
    destruct released; try by right; econs; eauto; right.
    left. econs; eauto.
  - left. econs 2. ss.
Qed.
