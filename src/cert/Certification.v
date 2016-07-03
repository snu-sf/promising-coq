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

Lemma reorder_promise_read
      lc0 mem0
      lc1 mem1
      lc2
      loc1 from1 to1 val1 released1 kind1
      loc2 to2 val2 released2 ord2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 val1 released1 lc1 mem1 kind1)
      (STEP2: Local.read_step lc1 mem1 loc2 to2 val2 released2 ord2 lc2)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (LOCTS: (loc1, to1) <> (loc2, to2)):
  exists lc1',
    <<STEP1: Local.read_step lc0 mem0 loc2 to2 val2 released2 ord2 lc1'>> /\
    <<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 val1 released1 lc2 mem1 kind1>>.
Proof.
  inv STEP1. inv STEP2.
  hexploit MemoryFacts.MemoryFacts.promise_get_inv_diff; eauto. i. des.
  esplits; eauto.
  + econs; eauto.
  + econs; eauto.
Qed.

Lemma reorder_promise_promise
      lc0 mem0
      lc1 mem1
      lc2 mem2
      loc1 from1 to1 val1 released1 kind1
      loc2 from2 to2 val2 released2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 val1 released1 lc1 mem1 kind1)
      (STEP2: Local.promise_step lc1 mem1 loc2 from2 to2 val2 released2 lc2 mem2 kind2)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (LOCTS: forall to1' val1' released1'
                (LOC: loc2 = loc1)
                (KIND: kind1 = Memory.promise_kind_split to1' val1' released1'),
          ~ Interval.mem (to1, to1') to2):
  exists lc1' mem1' kind2',
    <<STEP1: Local.promise_step lc0 mem0 loc2 from2 to2 val2 released2 lc1' mem1' kind2'>> /\
    <<STEP2: __guard__
               ((lc2, mem2) = (lc1', mem1') \/
                (exists kind1',
                    (loc1, to1) <> (loc2, to2) /\
                    (forall to1' val1' released1'
                       (LOC: loc2 = loc1)
                       (KIND: kind1' = Memory.promise_kind_split to1' val1' released1'),
                        ~ Interval.mem (to1, to1') to2) /\
                    Local.promise_step lc1' mem1' loc1 from1 to1 val1 released1 lc2 mem2 kind1'))>> /\
    <<KIND2: kind2 = Memory.promise_kind_add -> kind2' = Memory.promise_kind_add>>.
Proof.
Admitted.

Lemma reorder_promise_fulfill
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2
      loc1 from1 to1 val1 released1 kind1
      loc2 from2 to2 val2 releasedm2 released2 ord2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 val1 released1 lc1 mem1 kind1)
      (STEP2: fulfill_step lc1 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2)
      (LOCAL0: Local.wf lc0 mem0)
      (MEM0: Memory.closed mem0)
      (LOCTS1: (loc1, to1) <> (loc2, to2))
      (LOCTS2: forall to1' val1' released1'
                 (LOC: loc2 = loc1)
                 (KIND: kind1 = Memory.promise_kind_split to1' val1' released1'),
          ~ Interval.mem (to1, to1') to2):
  exists lc1',
    <<STEP1: fulfill_step lc0 sc0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2>> /\
    <<STEP2: Local.promise_step lc1' mem0 loc1 from1 to1 val1 released1 lc2 mem1 kind1>>.
Proof.
Admitted.

Lemma reorder_promise_write
      lc0 sc0 mem0
      lc1 mem1
      lc2 sc2 mem2
      loc1 from1 to1 val1 released1 kind1
      loc2 from2 to2 val2 releasedm2 released2 ord2 kind2
      (STEP1: Local.promise_step lc0 mem0 loc1 from1 to1 val1 released1 lc1 mem1 kind1)
      (STEP2: Local.write_step lc1 sc0 mem1 loc2 from2 to2 val2 releasedm2 released2 ord2 lc2 sc2 mem2 kind2)
      (REL_WF: Capability.wf releasedm2)
      (REL_CLOSED: Memory.closed_capability releasedm2 mem0)
      (LOCAL0: Local.wf lc0 mem0)
      (SC0: Memory.closed_timemap sc0 mem0)
      (MEM0: Memory.closed mem0)
      (LOCTS: forall to1' val1' released1'
                (LOC: loc2 = loc1)
                (KIND: kind1 = Memory.promise_kind_split to1' val1' released1'),
          ~ Interval.mem (to1, to1') to2):
  exists kind2' lc1' mem1',
    <<STEP1: Local.write_step lc0 sc0 mem0 loc2 from2 to2 val2 releasedm2 released2 ord2 lc1' sc2 mem1' kind2'>> /\
    <<STEP2: __guard__
               ((lc2, mem2) = (lc1', mem1') \/
                (exists kind1', <<STEP2: Local.promise_step lc1' mem1' loc1 from1 to1 val1 released1 lc2 mem2 kind1'>>))>> /\
    <<KIND2: kind2 = Memory.promise_kind_add -> kind2' = Memory.promise_kind_add>>.
Proof.
  exploit Local.promise_step_future; eauto. i. des.
  exploit write_promise_fulfill; eauto; try by committac. i. des.
  exploit reorder_promise_promise; try exact STEP1; eauto. i. des.
  unguardH STEP5. des.
  - inv STEP5.
    exploit promise_fulfill_write_exact; try exact STEP4; eauto.
    { i. exploit ORD; eauto. i. des. splits; auto.
      apply Cell.ext. i. rewrite Cell.bot_get.
      destruct (Cell.get ts (Local.promises lc0 loc2)) as [[? []]|] eqn:X; auto.
      inv STEP1. exploit Memory.promise_promises_get1; eauto. i. des.
      ss. unfold Memory.get in GET. rewrite x, Cell.bot_get in *. congr.
    }
    { condtac; [|auto]. do 3 f_equal. inv STEP1. ss. }
    i. esplits; eauto. left; eauto.
  - exploit Local.promise_step_future; try exact STEP4; eauto. i. des.
    exploit reorder_promise_fulfill; try exact STEP6; eauto. i. des.
    exploit fulfill_step_future; try exact STEP7; try exact WF0; eauto; try by committac. i. des.
    exploit promise_fulfill_write_exact; try exact STEP4; eauto; try by committac.
    { i. exploit ORD; eauto. i. des. splits; auto.
      apply Cell.ext. i. rewrite Cell.bot_get.
      destruct (Cell.get ts (Local.promises lc0 loc2)) as [[? []]|] eqn:X; auto.
      inv STEP1. exploit Memory.promise_promises_get1; eauto. i. des.
      ss. unfold Memory.get in GET. rewrite x, Cell.bot_get in *. congr.
    }
    { condtac; [|auto]. do 3 f_equal. inv STEP1. ss. }
    i. esplits; eauto. right. esplits. eauto.
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
  exploit Thread.promise_step_future; eauto. i. des.
  inv STEP1. inv STEP2. inv STEP; ss.
  - esplits; eauto.
    + econs; (try by econs 1; eauto).
    + right. esplits. econs. eauto.
  - (* read *)
    exploit reorder_promise_read; try exact LOCAL0; eauto; try by committac.
    { admit. (* read + promise *) }
    i. des. esplits.
    + econs.
      * econs 2; eauto.
      * auto.
    + right. esplits. econs; eauto.
  - (* write *)
    exploit reorder_promise_write; try exact LOCAL0; eauto; try by committac.
    { admit. (* write + promise *) }
    i. des. esplits.
    + econs.
      * econs 3; eauto.
      * auto.
    + unguardH STEP2. des.
      * inv STEP2. left. auto.
      * right. esplits. econs; eauto.
  - (* update *)
    exploit reorder_promise_read; try exact LOCAL1; eauto; try by committac.
    { admit. (* read + promise *) }
    i. des.
    exploit Local.read_step_future; eauto. i. des.
    exploit reorder_promise_write; try exact LOCAL2; eauto; try by committac.
    { admit. (* write + promise *) }
    i. des. esplits.
    + econs.
      * econs 4; eauto.
      * auto.
    + unguardH STEP3. des.
      * inv STEP3. left. auto.
      * right. esplits. econs; eauto.
  - inv LOCAL0. inv LOCAL1.
    esplits; eauto.
    + econs.
      * econs 5; eauto. econs; eauto.
      * auto.
    + right. esplits. econs. econs; eauto.
Admitted.

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
  exploit reorder_promise_program; eauto. i. des.
  inversion STEP1.
  exploit Thread.program_step_future; eauto. i. des.
  unguardH STEP2. des.
  - subst. esplits; cycle 1.
    + econs 2; eauto.
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
    + econs; [|eauto]. auto.
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
