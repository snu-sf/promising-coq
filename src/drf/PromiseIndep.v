Require Import Omega.
Require Import RelationClasses.

Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Time.
Require Import Event.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import Commit.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Set Implicit Arguments.

Hint Constructors Thread.program_step.
Hint Constructors Thread.step.

Definition ThreadEvent_is_promising (e: ThreadEvent.t) : option (Loc.t * Time.t) :=
  match e with
  | ThreadEvent.promise loc from to v rel => Some (loc, to)
  | _ => None
  end.

Inductive Thread_step_all {lang} (t1 t2:Thread.t lang) : Prop :=
| step_evt_intro e
  (STEP: Thread.step e t1 t2)
.
Hint Constructors Thread_step_all.

Inductive small_step (e:ThreadEvent.t) (tid:Ident.t) (c1:Configuration.t): forall (c2:Configuration.t), Prop :=
| small_step_intro
    lang st1 st2 lc1 ths2 lc2 sc2 memory2
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEP: Thread.step e (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) (Thread.mk _ st2 lc2 sc2 memory2))
    (THS2: ths2 = IdentMap.add tid (existT _ _ st2, lc2) c1.(Configuration.threads)):
  small_step e tid c1 (Configuration.mk ths2 sc2 memory2)
.
Hint Constructors small_step.

Inductive small_step_evt (tid:Ident.t) (c1 c2:Configuration.t): Prop :=
| small_step_evt_intro e
    (STEP: small_step e tid c1 c2)
.
Hint Constructors small_step_evt.

Inductive small_step_all (c1 c2:Configuration.t): Prop :=
| small_step_all_intro tid
    (STEP: small_step_evt tid c1 c2)
.
Hint Constructors small_step_all.

Inductive pf_step (e:ThreadEvent.t) (tid:Ident.t) (c1:Configuration.t): forall (c2:Configuration.t), Prop :=
| pf_step_intro c2
    (STEP: small_step e tid c1 c2)
    (NO_PROMISE: ThreadEvent_is_promising e = None):
    pf_step e tid c1 c2
.
Hint Constructors pf_step.

Inductive pf_step_evt tid (c1 c2:Configuration.t): Prop :=
| pf_step_evt_intro e
    (PI_STEP: pf_step e tid c1 c2)
.
Hint Constructors pf_step_evt.

Inductive pf_step_all (c1 c2:Configuration.t): Prop :=
| pf_step_all_intro tid
    (PI_STEP: pf_step_evt tid c1 c2)
.
Hint Constructors pf_step_all.

(* NOTE: `race_rw` requires two *distinct* threads to have a race.
 * However, C/C++ acknowledges intra-thread races.  For example,
 * according to the Standard, `f(x=1, x)` is RW-racy on `x`, since the
 * order of evaluation of the arguments is unspecified.  We currently
 * ignore this aspect of the race semantics.
 *)

Inductive Configuration_program_event c tid e : Prop :=
| configuration_program_event_intro lang st st' lc
    (TH: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st, lc))
    (STATE: lang.(Language.step) (Some e) st st').
Hint Constructors Configuration_program_event.

Inductive race_condition e1 e2 ord1 ord2 : Prop :=
| race_condition_rw loc
    (EVENT1: ProgramEvent.is_reading e1 = Some (loc, ord1))
    (EVENT2: ProgramEvent.is_writing e2 = Some (loc, ord2))
| race_condition_ww loc
    (EVENT1: ProgramEvent.is_writing e1 = Some (loc, ord1))
    (EVENT2: ProgramEvent.is_writing e2 = Some (loc, ord2))
.
Hint Constructors race_condition.

Inductive race (c:Configuration.t) (ord1 ord2:Ordering.t): Prop :=
| race_intro
    tid1 e1
    tid2 e2
    (TID: tid1 <> tid2)
    (PROEVT1: Configuration_program_event c tid1 e1)
    (PROEVT2: Configuration_program_event c tid2 e2)
    (RACE: race_condition e1 e2 ord1 ord2)
.
Hint Constructors race.            

Definition pf_racefree (c1:Configuration.t): Prop :=
  forall c2 ordr ordw
    (STEPS: rtc pf_step_all c1 c2)
    (RACE: race c2 ordr ordw),
    <<ORDR: Ordering.le Ordering.acqrel ordr>> /\
    <<ORDW: Ordering.le Ordering.acqrel ordw>>.

Inductive pi_step: ThreadEvent.t -> Ident.t -> Configuration.t*Configuration.t -> Configuration.t*Configuration.t -> Prop :=
| pi_step_step
    e tid cS1 cT1 cS2 cT2
    (STEPT: small_step e tid cT1 cT2)
    (STEPS: if ThreadEvent_is_promising e
            then cS1 = cS2
            else small_step e tid cS1 cS2)
    (LANGMATCH: 
     option_map fst (IdentMap.find tid cS2.(Configuration.threads)) =
     option_map fst (IdentMap.find tid cT2.(Configuration.threads))):
  pi_step e tid (cS1,cT1) (cS2,cT2)
.
Hint Constructors pi_step.

Inductive pi_step_evt tid cST1 cST2: Prop :=
| pi_step_evt_intro e
    (PI_STEP: pi_step e tid cST1 cST2)
.
Hint Constructors pi_step_evt.

Inductive pi_step_all cST1 cST2: Prop :=
| pi_step_all_intro tid
    (PI_STEP: pi_step_evt tid cST1 cST2)
.
Hint Constructors pi_step_all.

Inductive pi_step_except (tid_except:Ident.t) cST1 cST2: Prop :=
| pi_step_except_intro tid
    (PI_STEP: pi_step_evt tid cST1 cST2)
    (TID: tid <> tid_except)
.
Hint Constructors pi_step_except.

Definition Threads_remove_promise (ths: Threads.t) : Threads.t :=
  IdentMap.map
  (fun th => (th.(fst), Local.mk th.(snd).(Local.commit) Memory.bot))
  ths.

Inductive pi_wf: Configuration.t*Configuration.t -> Prop :=
| pi_wf_intro sc mS mT thsS thsT
    (THS: thsS = Threads_remove_promise thsT)
    (WFT: Configuration.wf (Configuration.mk thsT sc mT))
    (WFS: Configuration.wf (Configuration.mk thsS sc mS))
    (LR: forall loc ts from msg
           (IN: Memory.get loc ts mS = Some (from, msg)),
         <<IN: Memory.get loc ts mT = Some (from, msg)>> /\
         <<NOT: forall tid, ~Threads.is_promised tid loc ts thsT>>)
    (RL: forall loc ts from msg
           (IN: Memory.get loc ts mT = Some (from, msg))
           (NOT: forall tid, ~Threads.is_promised tid loc ts thsT),
         Memory.get loc ts mS = Some (from, msg)):
  pi_wf (Configuration.mk thsS sc mS, Configuration.mk thsT sc mT)
.
Hint Constructors pi_wf.

Inductive pi_consistent: Configuration.t*Configuration.t -> Prop :=
| pi_consistent_intro cS1 cT1
  (CONSIS:
    forall tid cS2 cT2 lst2 lc2 loc ts from msg
    (STEPS: rtc (pi_step_except tid) (cS1,cT1) (cS2,cT2))
    (THREAD: IdentMap.find tid cT2.(Configuration.threads) = Some (lst2, lc2))
    (PROMISE: Memory.get loc ts lc2.(Local.promises) = Some (from, msg)),
  exists cS3 e ord,
    <<STEPS: rtc (pf_step_evt tid) cS2 cS3>> /\
    <<PROEVT: Configuration_program_event cS3 tid e>> /\
    <<EVENT: ProgramEvent.is_writing e = Some (loc, ord)>> /\
    <<ORD: Ordering.le ord Ordering.relaxed>>):
  pi_consistent (cS1, cT1).
Hint Constructors pi_consistent.

Lemma small_step_future
      e tid c1 c2
      (WF1: Configuration.wf c1)
      (STEP: small_step e tid c1 c2):
  <<WF2: Configuration.wf c2>> /\
  <<FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>.
Proof.
  inv WF1. inv WF. inv STEP. ss.
  exploit THREADS; ss; eauto. i.
  exploit Thread.step_future; eauto.
  s; i; des. splits; [|by eauto]. econs; ss. econs.
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

Lemma rtc_small_step_future
      c1 c2
      (WF1: Configuration.wf c1)
      (STEP: rtc small_step_all c1 c2):
  <<WF2: Configuration.wf c2>> /\
  <<FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>.
Proof.
  revert WF1. induction STEP; i.
  - splits; eauto; reflexivity.
  - destruct H. destruct STEP0. 
    exploit small_step_future; eauto. i; des.
    exploit IHSTEP; eauto. i; des.
    splits; eauto. etrans; eauto.
Qed.

Lemma thread_step_small_step
      lang e tid threads
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (TID: IdentMap.find tid threads = Some (existT _ lang st1, lc1))
      (STEP: Thread.step e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
  small_step e tid
             (Configuration.mk threads sc1 mem1)
             (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) sc2 mem2).
Proof.
  econs; eauto.
Qed.

Lemma thread_step_small_step_aux
      lang e tid threads
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (STEP: Thread.step e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
  small_step e tid
             (Configuration.mk (IdentMap.add tid (existT _ lang st1, lc1) threads) sc1 mem1)
             (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) sc2 mem2).
Proof.
  exploit thread_step_small_step; eauto.
  { eapply IdentMap.Facts.add_eq_o. eauto. }
  rewrite (IdentMap.add_add_eq tid (existT Language.state lang st2, lc2)). eauto.
Qed.

Lemma rtc_thread_step_rtc_small_step_aux
      lang tid threads
      th1 th2
      (TID: IdentMap.find tid threads = Some (existT _ lang th1.(Thread.state), th1.(Thread.local)))
      (STEP: (rtc (@Thread_step_all lang)) th1 th2):
  rtc (small_step_evt tid)
      (Configuration.mk threads th1.(Thread.sc) th1.(Thread.memory))
      (Configuration.mk (IdentMap.add tid (existT _ lang th2.(Thread.state), th2.(Thread.local)) threads) th2.(Thread.sc) th2.(Thread.memory)).
Proof.
  revert threads TID. induction STEP; i.
  - apply rtc_refl. f_equal. apply IdentMap.eq_leibniz. ii.
    rewrite IdentMap.Facts.add_o. condtac; auto. subst. auto.
  - inv H. destruct x, y. ss. econs 2.
    + econs; eauto.
    + etrans; [eapply IHSTEP|].
      * apply IdentMap.Facts.add_eq_o. auto.
      * apply rtc_refl. f_equal. apply IdentMap.eq_leibniz. ii.
        rewrite ? IdentMap.Facts.add_o. condtac; auto.
Qed.

Lemma rtc_thread_step_rtc_small_step
      lang tid threads
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (TID: IdentMap.find tid threads = Some (existT _ lang st1, lc1))
      (STEP: (rtc (@Thread_step_all lang)) (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
  rtc (small_step_evt tid)
      (Configuration.mk threads sc1 mem1)
      (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) sc2 mem2).
Proof.
  exploit rtc_thread_step_rtc_small_step_aux; eauto. auto.
Qed.

Lemma step_small_steps
      e tid c1 c3
      (STEP: Configuration.step e tid c1 c3)
      (WF1: Configuration.wf c1)
      (CONSISTENT1: Configuration.consistent c1):
    <<STEPS: rtc (small_step_evt tid) c1 c3>> /\
    <<WF3: Configuration.wf c3>> /\
    <<CONSISTENT3: Configuration.consistent c3>>.
Proof.
  exploit Configuration.step_future; eauto. i. des.
  inv STEP. destruct c1, e2. ss. esplits; [|eauto|eauto].
  etrans.
  - eapply rtc_thread_step_rtc_small_step; cycle 1.
    + eapply rtc_implies, STEPS.
      i. inv PR. econs; eauto.
    + eauto.
  - econs; eauto. econs. econs; s; cycle 1; eauto.
    + rewrite IdentMap.add_add_eq. auto.
    + rewrite IdentMap.gss. eauto.
Qed.

Lemma pi_step_future
      tid cST1 cST2
      (WF1: pi_wf cST1)
      (STEP: pi_step_evt tid cST1 cST2):
  <<WF2: pi_wf cST2>> /\
  <<FUTURES: Memory.future cST1.(fst).(Configuration.memory) cST2.(fst).(Configuration.memory)>> /\
  <<FUTURET: Memory.future cST1.(snd).(Configuration.memory) cST2.(snd).(Configuration.memory)>>.
Proof.
  inv WF1. inv STEP. inv PI_STEP. splits; cycle 1. 
  - destruct (ThreadEvent_is_promising e).
    + subst. ss. econs.
    + eapply small_step_future in STEPS; eauto; des; ss.
  - eapply small_step_future in STEPT; eauto; des; ss.
  - assert (WFT2: Configuration.wf cT2).
    { by eapply small_step_future, STEPT. }
    assert (WFS2: Configuration.wf cS2).
    { destruct (ThreadEvent_is_promising e); [by inv STEPS|].
      by eapply small_step_future, STEPS. }
    inv STEPT. inv STEP; inv STEP0; ss.
    { subst. inv LOCAL. econs; eauto.
      - apply IdentMap.eq_leibniz.
        ii. setoid_rewrite IdentMap.map_add.
        destruct (Loc.eq_dec y tid) eqn: TIDEQ.
        + subst. setoid_rewrite IdentMap.Properties.F.map_o.
          rewrite IdentMap.gss, TID. done.
        + by rewrite IdentMap.gso.
      - admit.
      - admit.
    }
    { inv STEPS. inv STEP; inv STEP0; try done. econs; eauto; ss.
      - apply IdentMap.eq_leibniz. ii.
        setoid_rewrite IdentMap.Properties.F.map_o in TID0.
        rewrite TID in TID0. inv TID0. depdes H1.
        setoid_rewrite IdentMap.map_add.
        rewrite !IdentMap.gss in LANGMATCH. depdes LANGMATCH.
        destruct (Loc.eq_dec y tid) eqn: TIDEQ.
        + subst. by rewrite !IdentMap.gss.
        + by rewrite !IdentMap.gso.
      - admit.
      - admit.
    }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
    { admit. }
Admitted.

Lemma rtc_pi_step_future
      cST1 cST2
      (WF1: pi_wf cST1)
      (STEPS: rtc pi_step_all cST1 cST2):
  <<WF2: pi_wf cST2>> /\
  <<FUTURES: Memory.future cST1.(fst).(Configuration.memory) cST2.(fst).(Configuration.memory)>> /\
  <<FUTURET: Memory.future cST1.(snd).(Configuration.memory) cST2.(snd).(Configuration.memory)>>.
Proof.
  revert WF1. induction STEPS; i.
  - splits; auto; econs.
  - inv H. exploit pi_step_future; eauto. i. des.
    exploit IHSTEPS; eauto. i. des.
    splits; auto; etrans; eauto.
Qed.

Lemma pi_step_evt_all_incl
      tid cST1 cST2
      (STEP: pi_step_evt tid cST1 cST2):
  pi_step_all cST1 cST2.
Proof.
  econs; eauto.
Qed.

Lemma small_step_find
      tid1 tid2 c1 c2 e
      (STEP: small_step e tid1 c1 c2)
      (TID: tid1 <> tid2):
  IdentMap.find tid2 c1.(Configuration.threads) = IdentMap.find tid2 c2.(Configuration.threads).
Proof.
  inv STEP. s.
  rewrite IdentMap.gso; eauto.
Qed.

Lemma rtc_small_step_find
      tid1 tid2 c1 c2
      (STEP: rtc (small_step_evt tid1) c1 c2)
      (TID: tid1 <> tid2):
  IdentMap.find tid2 c1.(Configuration.threads) = IdentMap.find tid2 c2.(Configuration.threads).
Proof.
  induction STEP; auto. 
  inv H. rewrite <-IHSTEP.
  eauto using small_step_find.
Qed.

Lemma Capability_le_refl: forall r,
  Capability.le r r.
Proof. econs; econs 2; econs. Qed.

Lemma ordering_relaxed_dec
      ord:
  Ordering.le ord Ordering.relaxed \/ Ordering.le Ordering.acqrel ord.
Proof. destruct ord; auto. Qed.

Lemma fulfill_unset_promises
      loc from ts val rel
      promises1 promises2
      l t f m
      (FULFILL: Memory.remove promises1 loc from ts val rel promises2)
      (TH1: Memory.get l t promises1 = Some (f, m))
      (TH2: Memory.get l t promises2 = None):
  l = loc /\ t = ts /\ f = from /\ m.(Message.val) = val /\ Capability.le rel m.(Message.released).
Proof.
  eapply Memory.remove_get1 in FULFILL; eauto.
  des; subst.
  - splits; eauto using Capability_le_refl.
  - by rewrite TH2 in FULFILL.
Qed.

Lemma thread_step_unset_promises
      lang loc e from ts msg (th1 th2:Thread.t lang)
      (STEP: Thread.step e th1 th2)
      (TH1: Memory.get loc ts th1.(Thread.local).(Local.promises) = Some (from, msg))
      (TH2: Memory.get loc ts th2.(Thread.local).(Local.promises) = None):
  exists ord from val rel,
  <<EVENT: ThreadEvent.is_writing e = Some (loc, from, ts, val, ord, rel)>> /\
  <<ORD: Ordering.le ord Ordering.relaxed>> /\
  <<TIME: Time.lt (th1.(Thread.local).(Local.commit).(Commit.cur).(Capability.rw) loc) ts>>.
Proof.
  inv STEP.
  { inv STEP0. inv LOCAL. destruct msg. ss. 
    exploit Memory.promise_promises_get1; eauto. i. des. congr.
  }
  destruct msg.
  inv STEP0; ss; try by inv LOCAL; ss; congr.
  - by rewrite TH1 in TH2.
  - inv LOCAL. inv WRITE.
    exploit Memory.promise_promises_get1; eauto. i. des.
    exploit fulfill_unset_promises; eauto. i. des. subst.
    unfold Memory.get in *.
    esplits; s; eauto.
    + edestruct ordering_relaxed_dec; eauto.
      apply RELEASE in H. des. ss. by rewrite H, Cell.bot_get in TH1.
    + inv WRITABLE. eauto.
  - inv LOCAL1. inv LOCAL2. inv WRITE.
    exploit Memory.promise_promises_get1; eauto. i. des.
    exploit fulfill_unset_promises; eauto. i. des. subst.
    unfold Memory.get in *.
    esplits; s; eauto.
    + edestruct ordering_relaxed_dec; eauto.
      apply RELEASE in H. des. ss. by rewrite H, Cell.bot_get in TH1.
    + inv WRITABLE. inv READABLE. ss.
      move TS at bottom. admit.
Admitted. (* Done *)

Inductive can_fulfill (tid: Ident.t) loc ts (c1 c4: Configuration.t) : Prop :=
| can_fulfill_intro
    c2 c3 e ord lst2 lc2 from2 msg2 from val rel 
    (STEPS: rtc (small_step_evt tid) c1 c2)
    (STEP: small_step e tid c2 c3)
    (THREAD: IdentMap.find tid c2.(Configuration.threads) = Some (lst2, lc2))
    (PROMISE: Memory.get loc ts lc2.(Local.promises) = Some (from2, msg2))
    (EVENT: ThreadEvent.is_writing e = Some (loc, from, ts, val, ord, rel))
    (ORD: Ordering.le ord Ordering.relaxed)
    (STEPS: rtc (small_step_evt tid) c3 c4):
  can_fulfill tid loc ts c1 c4
.

Inductive can_fulfill_promises (tid: Ident.t) : Configuration.t -> Prop :=
| can_fulfill_promises_step
    c1
    (FULFILL: forall lst1 lc1 loc ts from msg
                (THREAD: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1))
                (PROMISE: Memory.get loc ts lc1.(Local.promises) = Some (from, msg)),
              exists c2,
              <<FULFILL1: can_fulfill tid loc ts c1 c2>> /\
              <<FULFILL2: can_fulfill_promises tid c2>>):
  can_fulfill_promises tid c1
.
Hint Constructors can_fulfill_promises.

Lemma Thread_step_commit_future
     lang e (t1 t2: @Thread.t lang)
     (STEP: Thread.step e t1 t2):
  Commit.le t1.(Thread.local).(Local.commit) t2.(Thread.local).(Local.commit).
Proof.
Admitted. (* Done *)

Lemma rtc_small_step_commit_future
     c1 c2 tid lst1 lst2 lc1 lc2
     (STEPS: rtc (small_step_evt tid) c1 c2)
     (THREAD1: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1))
     (THREAD2: IdentMap.find tid c2.(Configuration.threads) = Some (lst2, lc2)):
  Commit.le lc1.(Local.commit) lc2.(Local.commit).
Proof.
  ginduction STEPS; i.
  - rewrite THREAD1 in THREAD2. depdes THREAD2. reflexivity.
  - destruct H. destruct STEP. rewrite THREAD1 in TID. depdes TID.
      etrans; [apply (Thread_step_commit_future STEP)|].
      eapply IHSTEPS; eauto.
      s. subst. rewrite IdentMap.gss. eauto.
Qed.

Lemma can_fulfill_lt
      tid loc ts c1 c3 lst1 lc1 from msg
      (FULFILL: can_fulfill tid loc ts c1 c3)
      (FIND: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1))
      (PROMISE: Memory.get loc ts lc1.(Local.promises) = Some (from, msg)):
  Time.lt (lc1.(Local.commit).(Commit.cur).(Capability.rw) loc) ts.
Proof.
  destruct FULFILL.
  inv STEP. eapply rtc_small_step_commit_future in STEPS; eauto.
  inv STEP0; inv STEP; inv EVENT.
  + inv LOCAL. inv WRITABLE.
    move STEPS at bottom. move TS at bottom. admit.
  + inv LOCAL1. inv READABLE. inv LOCAL2. inv WRITABLE.
    ss. move STEPS at bottom. move TS at bottom. admit.
Admitted. (* Done *)
  
Lemma rtc_small_step_unset_promises
      tid loc ts c1 lst1 lc1 c2 lst2 lc2 from msg 
      (STEPS: rtc (small_step_evt tid) c1 c2)
      (FIND1: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1))
      (GET1: Memory.get loc ts lc1.(Local.promises) = Some (from, msg))
      (FIND2: IdentMap.find tid c2.(Configuration.threads) = Some (lst2, lc2))
      (GET2: Memory.get loc ts lc2.(Local.promises) = None):
  can_fulfill tid loc ts c1 c2.
Proof.
  ginduction STEPS; i; subst.
  { ss. rewrite FIND1 in FIND2. depdes FIND2.
    by rewrite GET1 in GET2. 
  }
  inv H. inv STEP. ss. rewrite FIND1 in TID. depdes TID.
  destruct (Memory.get loc ts lc3.(Local.promises)) eqn: PRM.
  - destruct p as [t m].
    rewrite IdentMap.gss in IHSTEPS.
    exploit IHSTEPS; eauto.
    intros []; i.
    econs; swap 5 8; eauto.
    etrans; [|apply STEPS0].
    econs; eauto.
  - exploit thread_step_unset_promises; eauto; s; eauto.
    i; des. econs; eauto. 
Qed.

Lemma pi_steps_pf_steps
      tid cST1 cST2
      (PI_STEPS: rtc (pi_step_evt tid) cST1 cST2):
  rtc (pf_step_evt tid) (fst cST1) (fst cST2).
Proof.
  induction PI_STEPS; eauto.
  inv H. inv PI_STEP. destruct (ThreadEvent_is_promising e) eqn: PROM.
  + subst. eauto.
  + econs; eauto.
Qed.

Lemma pi_steps_small_steps
      tid cST1 cST2
      (PI_STEPS: rtc (pi_step_evt tid) cST1 cST2):
  rtc (small_step_evt tid) (snd cST1) (snd cST2).
Proof.
  induction PI_STEPS; eauto.
  inv H. inv PI_STEP. econs; eauto.
Qed.

Lemma pi_consistent_small_step_pi_rw
      e tid cST1 cST2 cT3
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt tid) cST1 cST2)
      (STEP: small_step e tid cST2.(snd) cT3):
  forall loc from to val ord rel tid' ts
    (NEQ: tid <> tid')
    (RW: ThreadEvent.is_reading e = Some (loc, to, val, ord) \/
         ThreadEvent.is_writing e = Some (loc, from, to, val, ord, rel)),
  ~Threads.is_promised tid' loc ts cST2.(snd).(Configuration.threads).
Proof.
  ii. inv H.
  inv PI_CONSISTENT. ss.
  guardH RW. destruct cST2 as [cS2 cT2].
  exploit CONSIS.
  { eapply rtc_implies, PI_STEPS. i. econs; eauto. }
  { eauto. }
  { eauto. }
  clear CONSIS. i. des.
  exploit (PI_RACEFREE cS3 ord ord0).
  { etrans. 
    - eapply rtc_implies; [by i; eapply pf_step_all_intro, PR|].
      by eapply pi_steps_pf_steps in PI_STEPS; eauto.
    - eapply rtc_implies, STEPS. by econs; eauto.
  }
  { ss. inv STEP. inv STEP0; [by inv STEP; inv RW; inv H|].
    exploit rtc_pi_step_future; [|eapply rtc_implies; [eapply pi_step_evt_all_incl|]|]; eauto.
    i; des. clear FUTURES FUTURET.
    assert (LC1: exists lc1', IdentMap.find tid (Configuration.threads cS3) = Some (existT _ lang0 st1, lc1')).
    { eexists. erewrite <-(@rtc_small_step_find _ _ cS2); eauto; cycle 1.
      { eapply rtc_implies, STEPS.
        i. inv PR. inv PI_STEP. econs; eauto. } 
      inv WF2. ss. setoid_rewrite IdentMap.Properties.F.map_o.
      by rewrite TID0. }

    des. inv STEP; inv RW; inv H
    ; econs; eauto; first [by econs 1; ss|by econs 2; ss].
  }
  i. des. destruct ord0; inv ORD; inv ORDW.
Qed.

Lemma pi_consistent_small_step_pi
      e tid cST1 cST2 cT3
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt tid) cST1 cST2)
      (STEP: small_step e tid cST2.(snd) cT3)
      (FULFILL: can_fulfill_promises tid cT3):
  exists cS3, pi_step_evt tid cST2 (cS3,cT3).
Proof.
  destruct cST1 as [cS1 cT1], cST2 as [cS2 cT2].
  assert (RW:= pi_consistent_small_step_pi_rw WF PI_CONSISTENT PI_RACEFREE PI_STEPS STEP).
  exploit rtc_pi_step_future; [|eapply rtc_implies; [eapply pi_step_evt_all_incl|]|]; eauto.
  i; des. inv WF2. ss. inv STEP. inv STEP0.
  - eexists. econs; econs; [by eauto|by inv STEP; s; eauto|].
    inv STEP. ss. rewrite IdentMap.gss.
    setoid_rewrite IdentMap.Properties.F.map_o.
    by rewrite TID.
  - inv STEP.
    { eexists. econs. econs.
      - econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID. 
        + econs 2; econs 1; eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
    }
    { inv LOCAL. eexists. econs. econs.
      - econs; eauto. econs 2. econs 2; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID. 
        + econs 2; econs 2; eauto.
          econs; eauto.
          s. eapply RL; eauto.
          i. destruct (Ident.eq_dec tid tid0) eqn: EQ.
          * subst. intro PROMISED. inv PROMISED.
            ss. rewrite TID0 in TID. depdes TID.
            depdes FULFILL. ss. rewrite IdentMap.gss in FULFILL.
            exploit FULFILL; s; eauto.
            i. des. eapply can_fulfill_lt in FULFILL1; cycle 1.
            { s. rewrite IdentMap.gss. eauto. }
            inv READABLE; eauto. ss.
            move FULFILL1 at bottom. admit.
          * eapply RW; s; eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
    }
    { inv LOCAL. inv WRITE. eexists. econs. econs.
      - econs; eauto. econs 2. econs 3; eauto. econs; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID. 
        + econs 2; econs 3; eauto. 
          ss. admit.
        + eauto.
      - s. by rewrite !IdentMap.gss.
    }
    { admit.
    }
    { inv LOCAL. eexists. econs. econs.
      - econs; eauto. econs 2. econs 5; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID. 
        + econs 2; econs 5; eauto.
          econs; eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
    }
    { inv LOCAL. eexists. econs. econs.
      - econs; eauto. econs 2. econs 6; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID. 
        + econs 2; econs 6; eauto.
          econs; eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
    }
Admitted. (* Mostly done *)

Lemma can_fulfill_promises_small_step
      tid c1 c2
      (STEP: small_step_evt tid c1 c2)
      (FULFILL: can_fulfill_promises tid c2):
  can_fulfill_promises tid c1.
Proof.
  econs; i.
  destruct (IdentMap.find tid (Configuration.threads c2)) as [[lang2 lc2]|] eqn: THREAD2; cycle 1.
  { inv STEP. inv STEP0. ss. by rewrite IdentMap.gss in THREAD2. }
  destruct (Memory.get loc ts (Local.promises lc2)) as [[from2 msg2]|] eqn: PROMISE2.
  - depdes FULFILL. exploit FULFILL; eauto.
    i; des. esplits; eauto.
    destruct FULFILL1. econs; cycle 1; eauto.
    etrans; [|apply STEPS]. econs; eauto.
  - esplits; eauto.
    eapply rtc_small_step_unset_promises; eauto.
    econs; eauto.
Qed.

Lemma can_fulfill_promises_rtc_small_step
      tid c1 c2
      (STEP: rtc (small_step_evt tid) c1 c2)
      (FULFILL: can_fulfill_promises tid c2):
  can_fulfill_promises tid c1.
Proof.
  ginduction STEP; eauto using can_fulfill_promises_small_step.
Qed.

Lemma pi_consistent_rtc_small_step_pi
      tid cST1 cST2 cT3
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt tid) cST1 cST2)
      (STEP: rtc (small_step_evt tid) cST2.(snd) cT3)
      (FULFILL: can_fulfill_promises tid cT3):
  exists cS3, rtc (pi_step_evt tid) cST2 (cS3,cT3).
Proof.
  apply Operators_Properties.clos_rt_rt1n_iff in STEP.
  apply Operators_Properties.clos_rt_rtn1_iff in STEP.
  destruct cST2 as [cS2 cT2].
  revert FULFILL. induction STEP; eauto.
  i. assert (FULFILL1 := FULFILL).
  eapply can_fulfill_promises_small_step in FULFILL1; eauto. 
  exploit IHSTEP; eauto. i; des. ss. inv H.
  exploit pi_consistent_small_step_pi; try etransitivity; eauto.
  i; des. eexists. etrans; eauto. econs; eauto.
Qed.

Lemma consistent_can_fulfill_promises_future
      tid c c' lst lc
      (CONSISTENT: Configuration.consistent c)
      (TH1: IdentMap.find tid c.(Configuration.threads) = Some (lst, lc))
      (TH2: IdentMap.find tid c'.(Configuration.threads) = Some (lst, lc))
      (FUTURE: Memory.future c.(Configuration.memory) c'.(Configuration.memory))
      (TIMELE: TimeMap.le c.(Configuration.sc) c'.(Configuration.sc))
      (LOCWF: Local.wf lc (c'.(Configuration.memory)))
      (SC: Memory.closed_timemap c'.(Configuration.sc) c'.(Configuration.memory))
      (MEM: Memory.closed c'.(Configuration.memory)):
  can_fulfill_promises tid c'.
Proof.
  ii. destruct lst as [lang st]. econs. i.
  exploit CONSISTENT; ss; eauto.
  i; des. destruct e2.
  exploit rtc_thread_step_rtc_small_step; swap 1 2.
  { eapply rtc_implies, STEPS. i. inv PR. eauto. }
  { eauto. }
  intro STEPS1. ss.
  match goal with [STEPS1: rtc _ _ ?cfg|-_] => set (c2 := cfg) end.
  exploit rtc_small_step_unset_promises; cycle 1.
  - apply THREAD.
  - apply PROMISE.
  - instantiate (3:=c2). s. rewrite IdentMap.gss. eauto.
  - rewrite PROMISES. apply Cell.bot_get.
  - intro FULFILL. esplits; eauto.
    econs; i. unfold c2 in *. ss.
    rewrite IdentMap.gss in THREAD0. depdes THREAD0.
    rewrite PROMISES in PROMISE0. 
    by setoid_rewrite Cell.bot_get in PROMISE0.
  - by destruct c'.
Qed.

Lemma consistent_can_fulfill_promises
      tid c
      (CONSISTENT: Configuration.consistent c)
      (WF: Configuration.wf c):
  can_fulfill_promises tid c.
Proof.
  inv WF.
  destruct (IdentMap.find tid (Configuration.threads c)) as [[[] ]|] eqn: EQ.
  - eapply consistent_can_fulfill_promises_future; eauto; try reflexivity.
    eapply WF0; eauto.
  - econs. i. by rewrite EQ in THREAD.
Qed.

Theorem pi_consistent_step_pi
      cST1 cT2 e tid
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (CONSISTENT: Configuration.consistent cST1.(snd))
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (STEP: Configuration.step e tid cST1.(snd) cT2):
  exists cS2, rtc (pi_step_evt tid) cST1 (cS2,cT2).
Proof.
  exploit step_small_steps; eauto; [by inv WF|].
  i. des.
  exploit pi_consistent_rtc_small_step_pi; eauto.
  eapply consistent_can_fulfill_promises; eauto.
Qed.

Definition TimeMap_lift (x: Loc.t) (t: Time.t) (tm: TimeMap.t) : TimeMap.t :=
  fun y => if Loc.eq_dec x y then Time.join (tm y) t else tm y.

Definition Capability_lift (x: Loc.t) (t: Time.t) (rel: Capability.t) : Capability.t :=
  match rel with
  | Capability.mk ur rw sc => 
    Capability.mk ur (TimeMap_lift x t rw) (TimeMap_lift x t sc)
  end.

Inductive pi_step_lift (x: Loc.t) (t: Time.t) : ThreadEvent.t -> Ident.t -> Configuration.t*Configuration.t*Memory.t ->  Configuration.t*Configuration.t*Memory.t -> Prop :=
| pi_step_lift_intro e tid cS1 cS2 cT1 cT2 M1 M2
    (PI_STEP: pi_step e tid (cS1,cT1) (cS2,cT2))
    (MEM: match ThreadEvent.is_writing e with
          | Some (loc,from,to,val,ord,rel) =>
            exists pm1 pm2 kind,
            <<PMREL: Memory.write pm1 M1 loc from to val (Capability_lift x t rel) pm2 M2 kind>>
          | None =>
            M1 = M2
          end):
  pi_step_lift x t e tid (cS1,cT1,M1) (cS2,cT2,M2)
.
Hint Constructors pi_step_lift.

Lemma option_map_map 
      A B C (f: B -> C) (g: A -> B) (a: option A):
  option_map f (option_map g a) = option_map (fun x => f (g x)) a.
Proof.
  destruct a; eauto.
Qed.

Inductive pi_step_lift_evt x t tid cSTM1 cSTM2 : Prop :=
| pi_step_lift_evt_intro e
    (PI_STEP: pi_step_lift x t e tid cSTM1 cSTM2)
.
Hint Constructors pi_step_lift_evt.

Inductive pi_step_lift_except x t (tid_except:Ident.t) cSTM1 cSTM2: Prop :=
| pi_step_lift_except_intro tid
    (PI_STEP: pi_step_lift_evt x t tid cSTM1 cSTM2)
    (TID: tid <> tid_except)
.
Hint Constructors pi_step_lift_except.

Lemma pi_steps_lift_except_pi_steps
      cSTM1 cSTM2 x t tid
      (STEPS: rtc (pi_step_lift_except x t tid) cSTM1 cSTM2):
  rtc (pi_step_except tid) cSTM1.(fst) cSTM2.(fst).
Proof.
  induction STEPS; eauto.
  etrans; [|apply IHSTEPS].
  inv H. inv PI_STEP. inv PI_STEP0.
  econs; eauto.
Qed.

Lemma pi_step_lifting
      tid cST1 cST2 x t
      (PI_STEPS: rtc (pi_step_except tid) cST1 cST2):
  exists M2, rtc (pi_step_lift_except x t tid) (cST1,cST1.(snd).(Configuration.memory)) (cST2,M2).
Proof.
Admitted.

Lemma pi_step_lift_except_future
      x t tid cS1 cT1 cSTM2 lst1 lc1
      (PI_STEPS: rtc (pi_step_lift_except x t tid) (cS1,cT1,cT1.(Configuration.memory)) cSTM2)
      (WF: pi_wf (cS1,cT1))
      (FIND: IdentMap.find tid cT1.(Configuration.threads) = Some (lst1,lc1)):
  <<MEMFUT: Memory.future cT1.(Configuration.memory) cSTM2.(snd)>> /\
  <<TIMELE: TimeMap.le cT1.(Configuration.sc) cSTM2.(fst).(fst).(Configuration.sc)>> /\
  <<LOCWF: Local.wf lc1 cSTM2.(snd)>> /\
  <<MEMCLOTM: Memory.closed_timemap (cSTM2.(fst).(fst).(Configuration.sc)) cSTM2.(snd)>> /\
  <<MEMCLO: Memory.closed cSTM2.(snd)>>.
Proof.
Admitted.

Lemma rtc_pi_step_lift_except_find
      cSTM1 cSTM2 tid loc ts
      (STEPS: rtc (pi_step_lift_except loc ts tid) cSTM1 cSTM2):
  IdentMap.find tid cSTM1.(fst).(snd).(Configuration.threads) = IdentMap.find tid cSTM2.(fst).(snd).(Configuration.threads).
Proof.
  (* ginduction STEPS; eauto. *)
  (* des. rewrite <-IHSTEPS, <-IHSTEPS0. *)
  (* inv H. inv PI_STEP. inv PI_STEP0. inv PI_STEP. *)
  (* ss; split; [by eapply small_step_find; eauto|]. *)
  admit.
Admitted.

Lemma pi_step_pf_step
     tid cST1 cST2
     (STEP: rtc (pi_step_evt tid) cST1 cST2):
  rtc (pf_step_evt tid) cST1.(fst) cST2.(fst).
Proof.
  induction STEP; eauto.
  inv H. inv PI_STEP.
  destruct (ThreadEvent_is_promising e) eqn: PROM.
  - subst. eauto.
  - ss. econs; [|apply IHSTEP].
    econs. econs; eauto.
Qed.

Lemma small_step_to_program_step_writing
      c1 c2 e tid loc ord from ts val rel
      (STEP: small_step e tid c1 c2)
      (EVENT: ThreadEvent.is_writing e = Some (loc, from, ts, val, ord, rel)):
  exists (pe : ProgramEvent.t),
  <<EVENT: Configuration_program_event c1 tid pe >> /\
  <<WRITE: ProgramEvent.is_writing pe = Some (loc, ord) >>.
Proof.
  inv STEP. inv STEP0; inv STEP; inv EVENT; eauto 10.
Qed.

Lemma pf_racefree_steps
      c1 c2
      (FREE: pf_racefree c1)
      (STEPS: rtc pf_step_all c1 c2):
  pf_racefree c2.
Proof.
  ii. eapply FREE, RACE. etrans; eauto.
Qed.

Definition conf_update (c: Configuration.t) tid thr  m : Configuration.t :=
  Configuration.mk (IdentMap.add tid thr c.(Configuration.threads)) c.(Configuration.sc) m.

Lemma key_lemma
      cS1 cT1 cS2 cT2 tid
      (PI_CONSISTENT : pi_consistent (cS1, cT1))
      (WF : pi_wf (cS1, cT1))
      (RACEFREE : pf_racefree cS1)
      (STEPS : rtc (pi_step_evt tid) (cS1, cT1) (cS2, cT2))
      loc ts cSTM3
      (STEPS_LIFT : rtc (pi_step_lift_except loc ts tid) (cS2, cT2, cT2.(Configuration.memory)) cSTM3)
      thr2
      (FIND: IdentMap.find tid cT2.(Configuration.threads) = Some thr2)
      cM4 
      (PI_STEPS : rtc (small_step_evt tid) (conf_update cSTM3.(fst).(fst) tid thr2 cSTM3.(snd)) cM4)
      (FULFILL: can_fulfill_promises tid cM4)
      lst4 lc4 from msg 
      (THREAD : IdentMap.find tid (Configuration.threads cM4) = Some (lst4, lc4))
      (PROMISE : Memory.get loc ts (Local.promises lc4) = Some (from, msg)):
  exists cS4 : Configuration.t,
  <<STEPS: rtc (pi_step_evt tid) (cSTM3.(fst).(fst), conf_update cSTM3.(fst).(fst) tid thr2 cSTM3.(snd)) (cS4, cM4) >> /\
  <<STATE: option_map fst (IdentMap.find tid cS4.(Configuration.threads)) = option_map fst (IdentMap.find tid cM4.(Configuration.threads))>>.
Proof.
(*
  assert (WF2: pi_wf (cS2,cT2)).
  { eapply rtc_pi_step_future; eauto.
    eapply rtc_implies, STEPS; eauto. }

  assert (WF3: pi_wf cSTM3.(fst)).
  { eapply rtc_pi_step_future; eauto.
    eapply rtc_implies in STEPS_LIFT.
    - eapply pi_steps_lift_except_pi_steps in STEPS_LIFT.
      eapply rtc_implies, STEPS_LIFT.
      i. inv PR. eauto. 
    - i. inv PR. eauto. }

  revert_until STEPS_LIFT.
  apply Operators_Properties.clos_rt_rt1n_iff in STEPS_LIFT.
  apply Operators_Properties.clos_rt_rtn1_iff in STEPS_LIFT.

  induction STEPS_LIFT.
  { s. i. apply update_conf2prmem in UPDATE. subst.
    exploit pi_consistent_rtc_small_step_pi; try eapply WF; try apply FULFILL; eauto.
    intro STEPS1. des. esplits; eauto.
    
    exploit rtc_pi_step_future; try eapply rtc_implies, STEPS1; eauto.
    i; des. clear FUTURES FUTURET.

    inv WF0. unfold conf_st, Threads_remove_promise. 
    s. rewrite !IdentMap.Properties.F.map_o. 
    by rewrite option_map_map.
  }

  rename H into STEP.
  destruct y as [[cS3 cT3] M3].
  destruct z as [[cS4 cT4] M4].

  do 4 intro. rename cM4 into cM5, cM3 into cM4.
  apply Operators_Properties.clos_rt_rt1n_iff in PI_STEPS.
  apply Operators_Properties.clos_rt_rtn1_iff in PI_STEPS.
  induction PI_STEPS; i.
  { esplits; eauto. ss.
    destruct UPDATE. rewrite ST.
    inv WF3. unfold conf_st, Threads_remove_promise.
    s. rewrite !IdentMap.Properties.F.map_o, option_map_map. eauto.
  }

  ss. rename H into STEP2, y into CM5, z into CM6.

  inv STEP. inv PI_STEP. inv PI_STEP0.
  destruct (ThreadEvent.is_writing e) as [[[[[[loc1 from1] ts1] val1] ord1] rel1]|] eqn: EQ; cycle 1.
  { des. 
    assert (X := injective_projections _ _ PMEMEQ MEMEQ); subst. clear MEMEQ PMEMEQ.
    

  }
Focus 2.
*)

  admit.

Admitted.

Theorem pi_consistent_pi_step_pi_consistent
      cST1 cST2 tid
      (PI_CONSISTENT: pi_consistent cST1)
      (CONSISTENT: Configuration.consistent cST1.(snd))
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (WF: pi_wf cST1)
      (STEP: rtc (pi_step_evt tid) cST1 cST2)
      (CONSISTENT2: Configuration.consistent cST2.(snd)):
  pi_consistent cST2.
Proof.
  destruct cST1 as [cS1 cT1], cST2 as [cS2 cT2].
  econs. i. 
  destruct (Ident.eq_dec tid0 tid); cycle 1.
  { inv PI_CONSISTENT. 
    exploit CONSIS; cycle 1; eauto.
    etrans; cycle 1; eauto.
    eapply rtc_implies, STEP.
    i. econs; eauto.
  }
  subst. rename cS0 into cS3, cT0 into cT3, lst2 into lst3, lc2 into lc3.

  assert (STEPS_LIFT:=pi_step_lifting loc ts STEPS). des.
  rename M2 into M3. ss.

  exploit rtc_pi_step_future; [eauto|..].
  { eapply rtc_implies, STEP. i. inv PR. eauto. }
  i; des. ss. clear FUTURES FUTURET.

  destruct (IdentMap.find tid (Configuration.threads cT2)) eqn: TH; cycle 1.
  { apply Operators_Properties.clos_rt_rt1n_iff in STEP.
    apply Operators_Properties.clos_rt_rtn1_iff in STEP.
    inv STEP.
    - inv PI_CONSISTENT. exploit CONSIS; eauto.
    - inv H. inv PI_STEP. inv STEPT. ss. by rewrite IdentMap.gss in TH.
  }
  destruct p as [[lang2 st2] lc2].

  exploit pi_step_lift_except_future; eauto.
  i. des. ss.

  exploit rtc_pi_step_lift_except_find; eauto.
  s; intro EQ; des. 
  assert (X:= EQ); rewrite THREAD, TH in X. depdes X.

  exploit consistent_can_fulfill_promises_future
  ; [| |instantiate (3:=conf_update cS3 tid (existT _ lang2 st2, lc3) M3)|..]; eauto.
  {  unfold conf_update. s. rewrite IdentMap.gss. eauto. }
  intro FULFILL.

  depdes FULFILL. 
  setoid_rewrite IdentMap.gss in FULFILL.
  exploit FULFILL; eauto. 
  i. des.

  hexploit pf_racefree_steps; [eauto|..].
  { eapply pi_step_pf_step in STEP. eauto. }
  intro RACEFREE.

  inv FULFILL1.
  eapply can_fulfill_promises_rtc_small_step in FULFILL2; [|eauto].
  eapply can_fulfill_promises_small_step in FULFILL2; [|eauto].
  exploit key_lemma; eauto.
  i; des.

  exploit small_step_to_program_step_writing; eauto.
  i; des. ss.

  exists cS4; esplits; eauto using (pi_step_pf_step STEPS2).
  destruct EVENT0. rewrite TH0 in STATE. ss.
  destruct (IdentMap.find tid cS4.(Configuration.threads)) as [[ ]|] eqn: EQ1
  ; depdes STATE; eauto.
Qed.
