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

Inductive rtcn A (R: A -> A -> Prop): forall (n:nat) (a1 a2:A), Prop :=
| rtcn_nil
    a:
    rtcn R 0 a a
| rtcn_cons
    a1 a2 a3 n
    (A12: R a1 a2)
    (A23: rtcn R n a2 a3):
    rtcn R (S n) a1 a3
.
Hint Constructors rtcn.

Lemma rtcn_rtc A (R: A -> A -> Prop) n a1 a2
      (RTCN: rtcn R n a1 a2):
  rtc R a1 a2.
Proof.
  induction RTCN; auto. econs; eauto.
Qed.

Lemma rtc_rtcn A (R: A -> A -> Prop) a1 a2
      (RTC: rtc R a1 a2):
  exists n, rtcn R n a1 a2.
Proof.
  induction RTC; eauto. i. des.
  esplits; eauto.
Qed.

Lemma steps_pf_steps
      lang
      n_tgt
      e1_src
      e1_tgt e2_tgt
      (STEPS: rtcn (@Thread.tau_step lang) n_tgt e1_tgt e2_tgt)
      (PROMISES: e2_tgt.(Thread.local).(Local.promises) = Memory.bot)
      (WF1_SRC: Local.wf e1_src.(Thread.local) e1_src.(Thread.memory))
      (WF1_TGT: Local.wf e1_tgt.(Thread.local) e1_tgt.(Thread.memory))
      (SC1_SRC: Memory.closed_timemap e1_src.(Thread.sc) e1_src.(Thread.memory))
      (SC1_TGT: Memory.closed_timemap e1_tgt.(Thread.sc) e1_tgt.(Thread.memory))
      (MEM1_SRC: Memory.closed e1_src.(Thread.memory))
      (MEM1_TGT: Memory.closed e1_tgt.(Thread.memory))
      (LOCAL: sim_local e1_src.(Thread.local) e1_tgt.(Thread.local))
      (SC: TimeMap.le e1_src.(Thread.sc) e1_tgt.(Thread.sc))
      (MEM: sim_memory e1_src.(Thread.memory) e1_tgt.(Thread.memory)):
  exists n_src e2_src,
    <<N: n_src <= n_tgt>> /\
    <<STEPS: rtcn (@tau_program_step lang) n_src e1_src e2_src>> /\
    <<PROMISES: e2_src.(Thread.local).(Local.promises) = Memory.bot>>.
Proof.
  revert_until n_tgt. induction n_tgt; i.
  { inv STEPS. esplits; eauto. eapply sim_local_memory_bot; eauto. }
  inv STEPS. inv A12. inv STEP.
  - admit.
  - exploit IHn_tgt; eauto.
Admitted.

Lemma consistent_pf_consistent:
  Thread.consistent <2= pf_consistent.
Proof.
  s. ii. exploit PR; eauto. i. des.
  exploit rtc_rtcn; eauto. i. des.
  exploit steps_pf_steps; try exact STEPS; try refl; eauto. i. des.
  exploit rtcn_rtc; eauto.
Qed.
