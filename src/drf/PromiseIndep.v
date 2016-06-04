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
Require Import Progress.

Set Implicit Arguments.


Inductive small_step (e:ThreadEvent.t) (tid:Ident.t) (c1:Configuration.t): forall (c2:Configuration.t), Prop :=
| small_step_intro
    lang st1 lc1 st2 lc2 memory2
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEP: Thread.step e (Thread.mk _ st1 lc1 c1.(Configuration.memory)) (Thread.mk _ st2 lc2 memory2)):
    small_step e tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st2, lc2) c1.(Configuration.threads)) memory2)
.

Lemma small_step_future
      e tid c1 c2
      (WF1: Configuration.wf c1)
      (STEP: small_step e tid c1 c2):
  <<WF2: Configuration.wf c2>> /\
  <<FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>.
Proof.
  inv WF1. inv WF. inv STEP.
  exploit THREADS; ss; eauto. i.
  exploit Thread.step_future; eauto. s. i. des.
  splits; [|by eauto]. econs; ss. econs.
  - i. Configuration.simplify.
    + congr.
    + exploit THREADS; try apply TH1; eauto. i. des.
      exploit Thread.step_disjoint; eauto. s. i. des.
      symmetry. auto.
    + exploit THREADS; try apply TH2; eauto. i. des.
      exploit Thread.step_disjoint; eauto. i. des.
      auto.
    + eapply DISJOINT; [|eauto|eauto]. auto.
  - i. Configuration.simplify.
    exploit THREADS; try apply TH; eauto. i.
    exploit Thread.step_disjoint; eauto. s. i. des.
    auto.
Qed.

Inductive tau_small_step (tid:Ident.t) (c1 c2:Configuration.t): Prop :=
| tau_small_step_intro
    e
    (STEP: small_step e tid c1 c2)
    (TAU: ThreadEvent.get_event e = None)
.

Lemma thread_step_small_step
      lang e tid threads
      st1 lc1 mem1
      st2 lc2 mem2
      (TID: IdentMap.find tid threads = Some (existT _ lang st1, lc1))
      (STEP: Thread.step e (Thread.mk lang st1 lc1 mem1) (Thread.mk lang st2 lc2 mem2)):
  small_step e tid
             (Configuration.mk threads mem1)
             (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) mem2).
Proof.
  econs; eauto.
Qed.

Lemma thread_step_small_step_aux
      lang e tid threads
      st1 lc1 mem1
      st2 lc2 mem2
      (STEP: Thread.step e (Thread.mk lang st1 lc1 mem1) (Thread.mk lang st2 lc2 mem2)):
  small_step e tid
             (Configuration.mk (IdentMap.add tid (existT _ lang st1, lc1) threads) mem1)
             (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) mem2).
Proof.
  exploit thread_step_small_step; eauto.
  { eapply IdentMap.Facts.add_eq_o. eauto. }
  rewrite (IdentMap.add_add_eq tid (existT Language.state lang st2, lc2)). eauto.
Qed.

Lemma rtc_tau_thread_step_rtc_tau_small_step_aux
      lang tid threads
      th1 th2
      (TID: IdentMap.find tid threads = Some (existT _ lang th1.(Thread.state), th1.(Thread.local)))
      (STEP: (rtc (@Thread.tau_step lang)) th1 th2):
  rtc (tau_small_step tid)
      (Configuration.mk threads th1.(Thread.memory))
      (Configuration.mk (IdentMap.add tid (existT _ lang th2.(Thread.state), th2.(Thread.local)) threads) th2.(Thread.memory)).
Proof.
  revert threads TID. induction STEP; i.
  - apply rtc_refl. f_equal. apply IdentMap.eq_leibniz. ii.
    rewrite IdentMap.Facts.add_o. condtac; auto. subst. auto.
  - inv H. destruct x, y. ss. econs 2.
    + econs; eauto. eapply thread_step_small_step; eauto.
    + etrans; [eapply IHSTEP|].
      * apply IdentMap.Facts.add_eq_o. auto.
      * apply rtc_refl. f_equal. apply IdentMap.eq_leibniz. ii.
        rewrite ? IdentMap.Facts.add_o. condtac; auto.
Qed.

Lemma rtc_tau_thread_step_rtc_tau_small_step
      lang tid threads
      st1 lc1 mem1
      st2 lc2 mem2
      (TID: IdentMap.find tid threads = Some (existT _ lang st1, lc1))
      (STEP: (rtc (@Thread.tau_step lang)) (Thread.mk lang st1 lc1 mem1) (Thread.mk lang st2 lc2 mem2)):
  rtc (tau_small_step tid)
      (Configuration.mk threads mem1)
      (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) mem2).
Proof.
  exploit rtc_tau_thread_step_rtc_tau_small_step_aux; eauto. auto.
Qed.

Lemma step_small_steps
      e tid c1 c3
      (STEP: Configuration.step e tid c1 c3)
      (WF1: Configuration.wf c1)
      (CONSISTENT1: Configuration.consistent c1):
  exists te c2,
    <<STEPS: rtc (tau_small_step tid) c1 c2>> /\
    <<STEP: small_step te tid c2 c3>> /\
    <<EVENT: e = ThreadEvent.get_event te>> /\
    <<WF3: Configuration.wf c3>> /\
    <<CONSISTENT3: Configuration.consistent c3>>.
Proof.
  exploit Configuration.step_future; eauto. i. des.
  inv STEP. destruct c1, e2. ss. eexists _, _. splits; [| |eauto|eauto|eauto].
  - eapply rtc_tau_thread_step_rtc_tau_small_step; eauto.
  - eapply thread_step_small_step_aux. eauto.
Qed.

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

Lemma pi_step_future
      tid c1 c2
      (WF1: Configuration.wf c1)
      (STEP: pi_step tid c1 c2):
  <<WF2: Configuration.wf c2>> /\
  <<FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>.
Proof. inv STEP. eapply small_step_future; eauto. Qed.

Lemma rtc_pi_step_future
      tid c1 c2
      (WF1: Configuration.wf c1)
      (STEPS: rtc (pi_step tid) c1 c2):
  <<WF2: Configuration.wf c2>> /\
  <<FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>.
Proof.
  revert WF1. induction STEPS; i.
  - splits; auto. refl.
  - exploit pi_step_future; eauto. i. des.
    exploit IHSTEPS; eauto. i. des.
    splits; auto. etrans; eauto.
Qed.

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
    tid1 lang1 st1 lc1 e1 st1'
    tid2 lang2 st2 lc2 e2 st2'
    loc
    (TID: tid1 <> tid2)
    (TH1: IdentMap.find tid1 c.(Configuration.threads) = Some (existT _ lang1 st1, lc1))
    (TH2: IdentMap.find tid2 c.(Configuration.threads) = Some (existT _ lang2 st2, lc2))
    (STATE1: lang1.(Language.step) (Some e1) st1 st1')
    (STATE2: lang2.(Language.step) (Some e2) st2 st2')
    (EVENT1: ProgramEvent.is_reading e1 = Some (loc, ordr))
    (EVENT2: ProgramEvent.is_writing e2 = Some (loc, ordw))
.

Definition pi_racefree (c1:Configuration.t): Prop :=
  forall c2 ordr ordw
    (STEPS: rtc pi_step_all c1 c2)
    (RACE: race_rw c2 ordr ordw),
    <<ORDR: Ordering.le Ordering.acqrel ordr>> /\
    <<ORDW: Ordering.le Ordering.acqrel ordw>>.

Lemma fulfill_unset_promises
      loc from ts msg
      promises1 promises2
      l t f m
      (FULFILL: Memory.fulfill promises1 loc from ts msg promises2)
      (TH1: Memory.get l t promises1 = Some (f, m))
      (TH2: Memory.get l t promises2 = None):
  l = loc /\ t = ts /\ f = from /\ m = msg.
Proof.
  exploit Memory.remove_get1; try apply FULFILL; eauto. i. des; [|congr].
  subst. auto.
Qed.

Lemma ordering_relaxed_dec
      ord:
  Ordering.le ord Ordering.relaxed \/ Ordering.le Ordering.acqrel ord.
Proof. destruct ord; auto. Qed.

Lemma thread_step_unset_promises
      lang e loc from ts msg (th1 th2:Thread.t lang)
      (WF1: Local.wf th1.(Thread.local) th1.(Thread.memory))
      (STEP: Thread.step e th1 th2)
      (TH1: Memory.get loc ts th1.(Thread.local).(Local.promises) = Some (from, msg))
      (TH2: Memory.get loc ts th2.(Thread.local).(Local.promises) = None):
  exists e ord,
    <<STEP: lang.(Language.step) (Some e) th1.(Thread.state) th2.(Thread.state)>> /\
    <<EVENT: ProgramEvent.is_writing e = Some (loc, ord)>> /\
    <<ORD: Ordering.le ord Ordering.relaxed>>.
Proof.
  inv STEP.
  { inv STEP0. inv LOCAL. ss.
    exploit Memory.promise_promises_get1; eauto. i. des. congr.
  }
  inv STEP0; ss; try by inv LOCAL; ss; congr.
  - inv LOCAL.
    + inv FULFILL. ss.
      exploit fulfill_unset_promises; eauto. i. des. subst.
      eexists _, _. splits; eauto; ss.
      destruct (ordering_relaxed_dec ord); auto.
      unfold Memory.get in TH1. rewrite RELEASE, Cell.bot_get in TH1; auto. congr.
    + inv PROMISE.
      exploit Memory.promise_promises_get1; eauto. i. des.
      inv FULFILL. ss.
      exploit fulfill_unset_promises; eauto. i. des. subst.
      eexists _, _. splits; eauto; ss.
      destruct (ordering_relaxed_dec ord); auto.
      unfold Memory.get in TH1. rewrite RELEASE, Cell.bot_get in TH1; auto. congr.
  - inv LOCAL1. inv LOCAL2.
    + inv FULFILL. ss.
      exploit fulfill_unset_promises; eauto. i. des. subst.
      eexists _, _. splits; eauto; ss.
      destruct (ordering_relaxed_dec ordw); auto.
      unfold Memory.get in TH1. rewrite RELEASE, Cell.bot_get in TH1; auto. congr.
    + inv PROMISE.
      exploit Memory.promise_promises_get1; eauto. i. des.
      inv FULFILL. ss.
      exploit fulfill_unset_promises; eauto. i. des. subst.
      eexists _, _. splits; eauto; ss.
      destruct (ordering_relaxed_dec ordw); auto.
      unfold Memory.get in TH1. rewrite RELEASE, Cell.bot_get in TH1; auto. congr.
Qed.

Lemma pi_steps_promise
      tid
      c1 lang1 st1 lc1
      c3 lang3 st3 lc3
      loc from ts msg
      (WF1: Configuration.wf c1)
      (STEPS: rtc (pi_step tid) c1 c3)
      (TH1: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang1 st1, lc1))
      (TH3: IdentMap.find tid c3.(Configuration.threads) = Some (existT _ lang3 st3, lc3))
      (GET1: Memory.get loc ts lc1.(Local.promises) = Some (from, msg))
      (GET3: Memory.get loc ts lc3.(Local.promises) = None):
  exists c2 lang2 st2 lc2 e2 st2' ord2,
    <<STEPS: rtc (pi_step tid) c1 c2>> /\
    <<TH2: IdentMap.find tid c2.(Configuration.threads) = Some (existT _ lang2 st2, lc2)>> /\
    <<STATE2: lang2.(Language.step) (Some e2) st2 st2'>> /\
    <<EVENT2: ProgramEvent.is_writing e2 = Some (loc, ord2)>> /\
    <<ORD2: Ordering.le ord2 Ordering.relaxed>>.
Proof.
  revert lang1 st1 lc1 from msg TH1 GET1.
  induction STEPS; i.
  { rewrite TH1 in TH3. inv TH3. apply inj_pair2 in H1. congr. }
  inversion H. inv STEP. destruct (Memory.get loc ts lc2.(Local.promises)) as [[]|] eqn:X.
  { exploit IHSTEPS; eauto; s.
    { inv H. eapply small_step_future; eauto. }
    { rewrite IdentMap.Facts.add_eq_o; eauto. }
    i. des. eexists _, _, _, _, _, _, _. splits; [|eauto|eauto|eauto|eauto].
    etrans; [|eauto]. econs 2; [|econs 1]. eauto.
  }
  clear H STEPS IHSTEPS. rewrite TH1 in TID. inv TID. apply inj_pair2 in H1. subst.
  exploit thread_step_unset_promises; eauto; s.
  { eapply WF1. eauto. }
  i. des. eexists _, _, _, _, _, _, _. splits; eauto.
Qed.

Lemma pi_consistent_small_step_pi
      e tid c1 c2 c3
      (PI_CONSISTENT: pi_consistent c1)
      (WF: Configuration.wf c1)
      (CONSISTENT: Configuration.consistent c1)
      (PI_RACEFREE: pi_racefree c1)
      (PI_STEPS: rtc (pi_step tid) c1 c2)
      (STEP: small_step e tid c2 c3):
  pi_machine_event e c2.(Configuration.threads).
Proof.
  unfold pi_machine_event. destruct (ThreadEvent.is_reading e) as [[[]]|] eqn:E; auto. ii.
  inv H.
  assert (tid <> tid0).
  { admit. (* consistency required *) }
  exploit PI_CONSISTENT.
  { erewrite <- rtc_pi_step_find; eauto. congr. }
  { eapply rtc_implies; try apply PI_STEPS; eauto.
    i. econs; eauto.
  }
  i. des.
  exploit pi_steps_promise.
  { eapply rtc_pi_step_future; eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { eauto. }
  { rewrite PROMISES0. apply Memory.bot_get. }
  i. des.
  exploit PI_RACEFREE.
  { etrans.
    - eapply rtc_implies; try apply PI_STEPS; eauto.
      i. econs. eauto.
    - eapply rtc_implies; try apply STEPS0; eauto.
      i. econs. eauto.
  }
  { (* TODO: is ThreadEvent.is_reading/writing neccessary? *)
    inv STEP. inv STEP0; [by inv E|].
    erewrite <- rtc_pi_step_find in TID0; eauto.
    inv STEP; inv E.
    - econs; eauto; ss.
    - econs; eauto; ss.
  }
  i. des. destruct ord2; inv x0; inv x1.
Admitted.

Lemma pi_consistent_rtc_tau_small_step_pi
      tid c1 c2 c3
      (PI_CONSISTENT: pi_consistent c1)
      (WF: Configuration.wf c1)
      (CONSISTENT: Configuration.consistent c1)
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
      (WF: Configuration.wf c1)
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
      (WF1: Configuration.wf c1)
      (WF2: Configuration.wf c2)
      (CONSISTENT1: Configuration.consistent c1)
      (CONSISTENT2: Configuration.consistent c2)
      (STEP: rtc (pi_step tid) c1 c2):
  pi_consistent c2.
Proof.
  ii. destruct (Ident.eq_dec tid tid0).
  - subst tid0.
    (* TODO: sketch the proof *)
    admit.
  - eapply PI_CONSISTENT.
    + erewrite <- rtc_pi_step_find; eauto.
    + etrans; [|eauto]. eapply rtc_implies; [|apply STEP]. econs; eauto.
Admitted.
