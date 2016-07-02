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

Lemma rtcn_imply
      A (R1 R2: A -> A -> Prop) n a1 a2
      (LE: R1 <2= R2)
      (RTCN: rtcn R1 n a1 a2):
  rtcn R2 n a1 a2.
Proof.
  induction RTCN; auto. econs; eauto.
Qed.

Lemma sim_local_program_step
      lang
      th1_src
      th1_tgt th2_tgt e_tgt
      (STEP_TGT: @Thread.program_step lang e_tgt th1_tgt th2_tgt)
      (WF1_SRC: Local.wf th1_src.(Thread.local) th1_src.(Thread.memory))
      (WF1_TGT: Local.wf th1_tgt.(Thread.local) th1_tgt.(Thread.memory))
      (SC1_SRC: Memory.closed_timemap th1_src.(Thread.sc) th1_src.(Thread.memory))
      (SC1_TGT: Memory.closed_timemap th1_tgt.(Thread.sc) th1_tgt.(Thread.memory))
      (MEM1_SRC: Memory.closed th1_src.(Thread.memory))
      (MEM1_TGT: Memory.closed th1_tgt.(Thread.memory))
      (STATE: th1_src.(Thread.state) = th1_tgt.(Thread.state))
      (LOCAL: sim_local th1_src.(Thread.local) th1_tgt.(Thread.local))
      (SC: TimeMap.le th1_src.(Thread.sc) th1_tgt.(Thread.sc))
      (MEM: sim_memory th1_src.(Thread.memory) th1_tgt.(Thread.memory)):
  exists e_src th2_src,
    <<STEP_SRC: @Thread.program_step lang e_src th1_src th2_src>> /\
    <<EVENT: ThreadEvent.get_event e_src = ThreadEvent.get_event e_tgt>> /\
    <<STATE: th2_src.(Thread.state) = th2_tgt.(Thread.state)>> /\
    <<LOCAL: sim_local th2_src.(Thread.local) th2_tgt.(Thread.local)>> /\
    <<SC: TimeMap.le th2_src.(Thread.sc) th2_tgt.(Thread.sc)>> /\
    <<MEM: sim_memory th2_src.(Thread.memory) th2_tgt.(Thread.memory)>>.
Proof.
  destruct th1_src. ss. subst. inv STEP_TGT; ss.
  - esplits; (try by econs 1; eauto); eauto.
  - exploit sim_local_read; eauto; try refl. i. des.
    esplits; (try by econs 2; eauto); eauto.
  - hexploit sim_local_write; eauto; try refl; try by committac. i. des.
    esplits; (try by econs 3; eauto); eauto.
  - exploit Local.read_step_future; eauto. i. des.
    exploit sim_local_read; eauto; try refl. i. des.
    exploit Local.read_step_future; eauto. i. des.
    hexploit sim_local_write; eauto; try refl; try by committac. i. des.
    esplits; (try by econs 4; eauto); eauto.
  - exploit sim_local_fence; eauto; try refl. i. des.
    esplits; (try by econs 5; eauto); eauto.
  - exploit sim_local_fence; eauto; try refl. i. des.
    esplits; (try by econs 6; eauto); eauto.
Qed.

Lemma sim_local_rtcn_program_step
      lang n
      th1_src
      th1_tgt th2_tgt
      (STEPS_TGT: rtcn (@tau_program_step lang) n th1_tgt th2_tgt)
      (WF1_SRC: Local.wf th1_src.(Thread.local) th1_src.(Thread.memory))
      (WF1_TGT: Local.wf th1_tgt.(Thread.local) th1_tgt.(Thread.memory))
      (SC1_SRC: Memory.closed_timemap th1_src.(Thread.sc) th1_src.(Thread.memory))
      (SC1_TGT: Memory.closed_timemap th1_tgt.(Thread.sc) th1_tgt.(Thread.memory))
      (MEM1_SRC: Memory.closed th1_src.(Thread.memory))
      (MEM1_TGT: Memory.closed th1_tgt.(Thread.memory))
      (STATE: th1_src.(Thread.state) = th1_tgt.(Thread.state))
      (LOCAL: sim_local th1_src.(Thread.local) th1_tgt.(Thread.local))
      (SC: TimeMap.le th1_src.(Thread.sc) th1_tgt.(Thread.sc))
      (MEM: sim_memory th1_src.(Thread.memory) th1_tgt.(Thread.memory)):
  exists th2_src,
    <<STEP_SRC: rtcn (@tau_program_step lang) n th1_src th2_src>> /\
    <<STATE: th2_src.(Thread.state) = th2_tgt.(Thread.state)>> /\
    <<LOCAL: sim_local th2_src.(Thread.local) th2_tgt.(Thread.local)>> /\
    <<SC: TimeMap.le th2_src.(Thread.sc) th2_tgt.(Thread.sc)>> /\
    <<MEM: sim_memory th2_src.(Thread.memory) th2_tgt.(Thread.memory)>>.
Proof.
  revert_until n. induction n; i.
  { inv STEPS_TGT. esplits; eauto. }
  inv STEPS_TGT. inv A12.
  exploit Thread.program_step_future; eauto. i. des.
  exploit sim_local_program_step; try exact MEM; eauto. i. des.
  exploit Thread.program_step_future; eauto. i. des.
  exploit IHn; try exact MEM0; eauto. i. des.
  esplits; eauto. econs; eauto. econs; eauto. etrans; eauto.
Qed.

Lemma strong_induction
      (P : nat -> Prop)
      (IH: forall (n:nat) (IH: forall k (LT: k < n), P k), P n):
  forall n : nat, P n.
Proof.
  i. cut (forall m k, k < m -> P k); [by eauto|].
  induction m.
  - i. omega.
  - i. apply lt_le_S in H. inv H; eauto.
Qed.

Lemma reorder_promise_program
      lang
      e1 th0 th1 th2
      (STEP1: @Thread.promise_step lang e1 th0 th1)
      (STEP2: @tau_program_step lang th1 th2)
      (LOCAL: Local.wf th0.(Thread.local) th0.(Thread.memory))
      (SC: Memory.closed_timemap th0.(Thread.sc) th0.(Thread.memory))
      (MEMORY: Memory.closed th0.(Thread.memory)):
  exists th1',
     <<STEP1: @tau_program_step lang th0 th1'>> /\
     <<STEP2: __guard__ (th2 = th1' \/ exists e2', @Thread.promise_step lang e2' th1' th2)>>.
Proof.
  inv STEP1. inv STEP2. inv STEP; ss.
  - esplits; eauto.
    + econs; (try by econs 1; eauto).
    + right. esplits. econs. eauto.
  - (* read *)
    inv LOCAL0. inv LOCAL1.
    destruct (loc_ts_eq_dec (loc, to) (loc0, ts)); ss.
    { des. subst. admit. (* read & promise *) }
    hexploit MemoryFacts.MemoryFacts.promise_get_inv_diff; eauto.
    { ii. inv H. des; congr. }
    guardH o. i. des.
    esplits; eauto.
    + econs.
      * econs 2; eauto. econs; eauto.
      * auto.
    + right. esplits. econs. econs; eauto.
  - (* write *)
    admit.
  - (* update *)
    admit.
  - inv LOCAL0. inv LOCAL1.
    esplits; eauto.
    + econs.
      * econs 5; eauto. econs; eauto.
        ss. i. exploit RELEASE; eauto. i. subst.
        exploit Memory.promise_get2; eauto. rewrite Memory.bot_get. congr.
      * auto.
    + right. esplits. econs. econs; eauto.
Admitted.

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
      (STATE: e1_src.(Thread.state) = e1_tgt.(Thread.state))
      (LOCAL: sim_local e1_src.(Thread.local) e1_tgt.(Thread.local))
      (SC: TimeMap.le e1_src.(Thread.sc) e1_tgt.(Thread.sc))
      (MEM: sim_memory e1_src.(Thread.memory) e1_tgt.(Thread.memory)):
  exists n_src e2_src,
    <<N: n_src <= n_tgt>> /\
    <<STEPS: rtcn (@tau_program_step lang) n_src e1_src e2_src>> /\
    <<PROMISES: e2_src.(Thread.local).(Local.promises) = Memory.bot>>.
Proof.
  revert_until n_tgt. induction n_tgt using strong_induction; i.
  inv STEPS.
  { esplits; eauto. eapply sim_local_memory_bot; eauto. }
  inv A12. inv STEP; cycle 1.
  { exploit sim_local_program_step; try exact STATE; eauto. i. des.
    exploit Thread.program_step_future; try exact STEP0; eauto. i. des.
    exploit Thread.program_step_future; try exact STEP_SRC; eauto. i. des.
    exploit IH; eauto. i. des.
    esplits; cycle 1.
    + econs 2; eauto. econs; eauto. etrans; eauto.
    + auto.
    + omega.
  }
  exploit Thread.promise_step_future; eauto. i. des.
  exploit IH; try exact A23; try refl; eauto. i. des.
  inv STEPS.
  { inv STEP0. ss. subst. inv LOCAL0. ss. subst.
    exploit Memory.promise_get2; eauto. rewrite Memory.bot_get. congr.
  }
  inversion A12. exploit Thread.program_step_future; eauto. i. des.
  exploit reorder_promise_program; eauto. i. des.
  inversion STEP1.
  exploit Thread.program_step_future; eauto. i. des.
  exploit sim_local_program_step; try exact STEP2; try exact MEM; eauto. i. des.
  exploit Thread.program_step_future; eauto. i. des.
  unguardH STEP2. des.
  - subst. exploit sim_local_rtcn_program_step; (try etrans; eauto; try done). i. des.
    esplits; cycle 1.
    + econs 2; eauto. econs; eauto. etrans; eauto.
    + eapply sim_local_memory_bot; eauto.
    + omega.
  - exploit Thread.promise_step_future; try exact STEP2; eauto. i. des.
    exploit sim_local_rtcn_program_step; try exact MEM0; eauto. i. des.
    assert (STEPS: rtcn (Thread.tau_step (lang:=lang)) (S n0) th1' th2_src0).
    { econs 2.
      - econs.
        + econs 1. apply STEP2.
        + by inv STEP2.
      - eapply rtcn_imply; try exact STEP_SRC0. i. inv PR. econs; eauto. econs 2; eauto.
    }
    exploit IH; try exact STEPS; try exact MEM1; eauto.
    { omega. }
    { eapply sim_local_memory_bot; eauto. }
    i. des. esplits; cycle 1.
    + econs 2; eauto. econs; eauto. etrans; eauto.
    + auto.
    + omega.
Qed.

Lemma consistent_pf_consistent:
  Thread.consistent <2= pf_consistent.
Proof.
  s. ii. exploit PR; eauto. i. des.
  exploit rtc_rtcn; eauto. i. des.
  exploit steps_pf_steps; try exact STEPS; try refl; eauto. i. des.
  exploit rtcn_rtc; eauto.
Qed.
