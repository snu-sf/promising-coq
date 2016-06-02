Require Import Omega.
Require Import RelationClasses.

Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import Memory.
Require Import Commit.
Require Import Thread.
Require Import Configuration.

Set Implicit Arguments.


Inductive small_step (e:ThreadEvent.t) (tid:Ident.t) (c1:Configuration.t): forall (c2:Configuration.t), Prop :=
| small_step_intro
    lang st1 lc1 st2 lc2 memory2
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEP: Thread.step e (Thread.mk _ st1 lc1 c1.(Configuration.memory)) (Thread.mk _ st2 lc2 memory2)):
    small_step e tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st2, lc2) c1.(Configuration.threads)) memory2)
.

Inductive tau_small_step (tid:Ident.t) (c1 c2:Configuration.t): Prop :=
| tau_small_step_intro
    e
    (STEP: small_step e tid c1 c2)
    (TAU: ThreadEvent.get_event e = None)
.

Lemma step_small_steps
      e tid c1 c3
      (STEP: Configuration.step e tid c1 c3)
      (CONSISTENT1: Configuration.consistent c1):
  exists te c2,
    <<STEPS: rtc (tau_small_step tid) c1 c2>> /\
    <<STEP: small_step te tid c2 c3>> /\
    <<EVENT: e = ThreadEvent.get_event te>> /\
    <<CONSISTENT3: Configuration.consistent c3>>.
Proof.
  exploit Configuration.step_consistent; eauto. i. des.
  admit.
Admitted.


Definition pi_machine_event (e:ThreadEvent.t) (threads:Threads.t): Prop :=
  match ThreadEvent.is_reading e with
  | Some (loc, ts, _) => ~ Threads.is_promised loc ts threads
  | None => True
  end.

Inductive pi_step (tid:Ident.t) (c1 c2:Configuration.t): Prop :=
| pi_step_intro
    e
    (STEP: small_step e tid c1 c2)
    (READINFO: pi_machine_event e c1.(Configuration.threads))
.

Inductive pi_step_all (c1 c2:Configuration.t): Prop :=
| pi_step_all_intro
    tid
    (PI_STEP: pi_step tid c1 c2)
.

Inductive pi_step_except (tid_except:Ident.t) (c1 c2:Configuration.t): Prop :=
| pi_step_except_intro
    tid
    (PI_STEP: pi_step tid c1 c2)
    (TID: tid <> tid_except)
.

Definition pi_consistent (c1:Configuration.t): Prop :=
  forall tid c2
    (TID: IdentMap.find tid c1.(Configuration.threads) <> None)
    (STEPS: rtc (pi_step_except tid) c1 c2),
  exists c3 lang st3 lc3,
    <<STEPS: rtc (pi_step tid) c2 c3>> /\
    <<THREAD: IdentMap.find tid c3.(Configuration.threads) = Some (existT _ lang st3, lc3)>> /\
    <<PROMISES: lc3.(Local.promises) = Memory.bot>>.

Lemma pi_step_find
      tid1 tid2 c1 c2
      (STEP: pi_step tid1 c1 c2)
      (TID: tid1 <> tid2):
  IdentMap.find tid2 c2.(Configuration.threads) = IdentMap.find tid2 c1.(Configuration.threads).
Proof.
  inv STEP. inv STEP0. s. rewrite IdentMap.Facts.add_neq_o; auto.
Qed.

Lemma rtc_pi_step_find
      tid1 tid2 c1 c2
      (STEP: rtc (pi_step tid1) c1 c2)
      (TID: tid1 <> tid2):
  IdentMap.find tid2 c2.(Configuration.threads) = IdentMap.find tid2 c1.(Configuration.threads).
Proof.
  induction STEP; auto. erewrite IHSTEP, pi_step_find; eauto.
Qed.

(* NOTE: `race_rw` requires two *distinct* threads to have a race.
 * However, C/C++ acknowledges intra-thread races.  For example,
 * according to the Standard, `f(x=1, x)` is RW-racy on `x`, since the
 * order of evaluation of the arguments is unspecified.  We currently
 * ignore this aspect of the race semantics.
 *)
Inductive race_rw (c:Configuration.t) (ordr ordw:Ordering.t): Prop :=
| race_rw_intro
    tid1 lang1 st1 lc1 e1 th1'
    tid2 lang2 st2 lc2 e2 th2'
    loc
    (TID: tid1 <> tid2)
    (THREAD1: IdentMap.find tid1 c.(Configuration.threads) = Some (existT _ lang1 st1, lc1))
    (THREAD2: IdentMap.find tid2 c.(Configuration.threads) = Some (existT _ lang2 st2, lc2))
    (STEP1: Thread.step e1 (Thread.mk _ st1 lc1 c.(Configuration.memory)) th1')
    (STEP2: Thread.step e2 (Thread.mk _ st2 lc2 c.(Configuration.memory)) th2')
    (E1: ThreadEvent.is_reading e1 = Some (loc, ordr))
    (E2: ThreadEvent.is_writing e1 = Some (loc, ordw))
.

Definition pi_racefree (c1:Configuration.t): Prop :=
  forall c2 ordr ordw
    (STEPS: rtc pi_step_all c1 c2)
    (RACE: race_rw c2 ordr ordw),
    <<ORDR: Ordering.le Ordering.acqrel ordr>> /\
    <<ORDW: Ordering.le Ordering.acqrel ordw>>.

Lemma pi_consistent_small_step_pi
      e tid c1 c2 c3
      (PI_CONSISTENT: pi_consistent c1)
      (PI_RACEFREE: pi_racefree c1)
      (PI_STEPS: rtc (pi_step tid) c1 c2)
      (STEP: small_step e tid c2 c3):
  pi_machine_event e c2.(Configuration.threads).
Proof.
  unfold pi_machine_event. destruct (ThreadEvent.is_reading e) as [[[]]|] eqn:E; auto. ii.
  inv H.
  assert (tid <> tid0).
  { admit. }
  exploit PI_CONSISTENT.
  { erewrite <- rtc_pi_step_find; eauto. congr. }
  { eapply rtc_implies; try apply PI_STEPS; eauto.
    i. econs; eauto.
  }
  i. des. exploit PI_RACEFREE.
  { etrans.
    - eapply rtc_implies; try apply PI_STEPS; eauto.
      i. econs; eauto.
    - eapply rtc_implies; try apply STEPS; eauto.
      i. econs; eauto.
  }
  { admit. (* race_rw *) }
  { i. des. admit. (* rel -> contradiction *) }
Admitted.

Lemma pi_consistent_rtc_tau_small_step_pi
      tid c1 c2 c3
      (PI_CONSISTENT: pi_consistent c1)
      (PI_RACEFREE: pi_racefree c1)
      (PI_STEPS: rtc (pi_step tid) c1 c2)
      (STEP: rtc (tau_small_step tid) c2 c3):
  rtc (pi_step tid) c2 c3.
Proof.
  apply Operators_Properties.clos_rt_rt1n_iff in STEP.
  apply Operators_Properties.clos_rt_rtn1_iff in STEP.
  induction STEP; auto. etrans; eauto. econs 2; [|econs 1].
  inv H. econs; eauto. eapply pi_consistent_small_step_pi; eauto.
  etrans; eauto.
Qed.

Lemma pi_consistent_step_pi
      c1 c2
      e tid
      (PI_CONSISTENT: pi_consistent c1)
      (CONSISTENT: Configuration.consistent c1)
      (PI_RACEFREE: pi_racefree c1)
      (STEP: Configuration.step e tid c1 c2):
  rtc (pi_step tid) c1 c2.
Proof.
  exploit step_small_steps; eauto. i. des. subst.
  exploit pi_consistent_rtc_tau_small_step_pi; eauto. i.
  exploit pi_consistent_small_step_pi; eauto. i.
  etrans; eauto. econs 2; [|econs 1]. econs; eauto.
Qed.

Lemma pi_consistent_pi_step_pi_consistent
      c1 c2
      tid
      (PI_CONSISTENT: pi_consistent c1)
      (CONSISTENT1: Configuration.consistent c1)
      (CONSISTENT2: Configuration.consistent c2)
      (STEP: rtc (pi_step tid) c1 c2):
  pi_consistent c2.
Proof.
  ii. destruct (Ident.eq_dec tid tid0).
  - subst tid0.
    admit.
  - eapply PI_CONSISTENT.
    + erewrite <- rtc_pi_step_find; eauto.
    + etrans; [|eauto]. eapply rtc_implies; [|apply STEP]. econs; eauto.
Admitted.
