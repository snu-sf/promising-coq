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
  { inv STEP0. inv LOCAL. ss.
    exploit Memory.promise_promises_get1; eauto. i. des. congr.
  }
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

Inductive can_fulfill c1 tid loc ts : Prop :=
| can_fulfill_intro
    c2 c2' e ord from val rel 
    (STEPS: rtc (small_step_evt tid) c1 c2)
    (STEP: small_step e tid c2 c2')
    (EVENT: ThreadEvent.is_writing e = Some (loc, from, ts, val, ord, rel))
    (ORD: Ordering.le ord Ordering.relaxed)
.
Hint Constructors can_fulfill.

Definition can_fulfill_promises c tid : Prop :=
  forall lst lc loc ts from msg
         (THREAD: IdentMap.find tid c.(Configuration.threads) = Some (lst, lc))
         (PROMISE: Memory.get loc ts lc.(Local.promises) = Some (from, msg)),
  can_fulfill c tid loc ts.
Hint Unfold can_fulfill_promises.

Lemma can_fulfill_lt 
      c1 tid loc ts
      (FULFILL: can_fulfill c1 tid loc ts):
  exists lst1 lc1,
  <<FIND: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1)>> /\
  <<TIME: Time.lt (lc1.(Local.commit).(Commit.cur).(Capability.rw) loc) ts>>.
Proof.
  destruct FULFILL. ginduction STEPS; i.
  - inv STEP. esplits; eauto.
    inv STEP0; inv STEP; inv EVENT.
    + inv LOCAL. inv WRITABLE. eauto.
    + inv LOCAL1. inv READABLE. inv LOCAL2. inv WRITABLE.
      ss. move TS at bottom. admit.
  - inv H. inv STEP0. esplits; eauto.
    destruct (Memory.get loc ts lc2.(Local.promises)) eqn: PRM.
    + destruct p. exploit IHSTEPS; eauto.
      i; des. ss. rewrite IdentMap.gss in FIND. depdes FIND.
      move STEP1 at bottom. move TIME at bottom. admit.
Admitted. (* Done *)
  
Lemma rtc_thread_step_unset_promises
      tid c1 lang1 st1 lc1 th1 th3 loc ts from msg 
      (STEPS: rtc Thread_step_all th1 th3)
      (FIND1: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang1 st1, lc1))
      (TH1: th1 = Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory))
      (GET1: Memory.get loc ts lc1.(Local.promises) = Some (from, msg))
      (GET3: Memory.get loc ts th3.(Thread.local).(Local.promises) = None):
  can_fulfill c1 tid loc ts.
Proof.
  ginduction STEPS; i; subst.
  { ss. by rewrite GET1 in GET3. }
  inv H. destruct y.
  destruct (Memory.get loc ts local.(Local.promises)) eqn: PRM.
  - destruct p as [t m]. 
    exploit (IHSTEPS tid (Configuration.mk (IdentMap.add tid (existT _ lang1 state, local) (Configuration.threads c1)) sc memory)); s; eauto.
    { s. rewrite IdentMap.gss. eauto. }
    intro FULFILL. destruct FULFILL.
    econs; try apply STEP0; eauto.
    etransitivity; [|by apply STEPS0].
    econs; eauto.
  - exploit thread_step_unset_promises; eauto; s; eauto.
    i; des. econs; eauto.
Admitted. (* Done *)

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
      (FULFILL: can_fulfill_promises cT3 tid):
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
            r in FULFILL. ss. rewrite IdentMap.gss in FULFILL.
            exploit FULFILL; s; eauto.
            intro FULFILLED. apply can_fulfill_lt in FULFILLED. des. ss.
            rewrite IdentMap.gss in FIND. depdes FIND.
            inv READABLE. ss.
            move TIME at bottom. admit.
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
          admit.
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
Admitted.

Lemma can_fulfill_promises_small_step
      tid c1 c2
      (STEP: small_step_evt tid c1 c2)
      (FULFILL: can_fulfill_promises c2 tid):
  can_fulfill_promises c1 tid.
Proof.
  ii. destruct (IdentMap.find tid (Configuration.threads c2)) as [[lang2 lc2]|] eqn: THREAD2; cycle 1.
  { inv STEP. inv STEP0. ss. by rewrite IdentMap.gss in THREAD2. }
  destruct (Memory.get loc ts (Local.promises lc2)) as [[from2 msg2]|] eqn: PROMISE2.
  { exploit FULFILL; eauto.
    intro FF. destruct FF.
    econs; cycle 1; eauto.
    econs; eauto. 
  }
  inv STEP. inv STEP0.
  rewrite THREAD in TID. depdes TID.
  ss. rewrite IdentMap.gss in THREAD2. depdes THREAD2.
  exploit thread_step_unset_promises; eauto.
  s. i. des. eauto.
Qed.

Lemma pi_consistent_rtc_small_step_pi
      tid cST1 cST2 cT3
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt tid) cST1 cST2)
      (STEP: rtc (small_step_evt tid) cST2.(snd) cT3)
      (FULFILL: can_fulfill_promises cT3 tid):
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

Lemma consistent_can_fulfill_promises
      c tid
      (WF: Configuration.wf c)
      (CONSISTENT: Configuration.consistent c):
  can_fulfill_promises c tid.
Proof.
  ii. destruct lst as [lang st].
  inv WF. inv WF0.
  exploit CONSISTENT; ss; eauto. 
  { econs. } { reflexivity. }
  i; des.
  eapply rtc_thread_step_unset_promises.
  - eapply rtc_implies, STEPS. i. inv PR. eauto.
  - eauto. - eauto. - eauto.
  - rewrite PROMISES. apply Cell.bot_get.
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
  exploit pi_consistent_rtc_small_step_pi; eauto using consistent_can_fulfill_promises.
Qed.

Definition TimeMap_lift (x: Loc.t) (t: Time.t) (tm: TimeMap.t) : TimeMap.t :=
  fun y => if Loc.eq_dec x y then Time.join (tm y) t else tm y.

Definition Capability_lift (x: Loc.t) (t: Time.t) (rel: Capability.t) : Capability.t :=
  match rel with
  | Capability.mk ur rw sc => 
    Capability.mk ur (TimeMap_lift x t rw) (TimeMap_lift x t sc)
  end.

Definition conf_mem c := c.(Configuration.memory).
Definition conf_sc c := c.(Configuration.sc).
Definition conf_st c := IdentMap.map fst c.(Configuration.threads).
Definition conf_commit c := IdentMap.map (fun th => th.(snd).(Local.commit)) c.(Configuration.threads).
Definition conf_promises c := IdentMap.map (fun th => th.(snd).(Local.promises)) c.(Configuration.threads).

Inductive pi_step_lift (x: Loc.t) (t: Time.t) : ThreadEvent.t -> Ident.t -> (Configuration.t*Configuration.t)*Configuration.t -> (Configuration.t*Configuration.t)*Configuration.t -> Prop :=
| pi_step_lift_intro e tid cS1 cS2 cT1 cT2 cM1 cM2
    (PI_STEP: pi_step e tid (cS1,cT1) (cS2,cT2))
    (SC: conf_sc cM2 = conf_sc cT2)
    (ST: conf_st cM2 = conf_st cT2)
    (COM: conf_commit cM2 = conf_commit cT2)
    (MEM: match ThreadEvent.is_writing e with
          | Some (loc,from,to,val,ord,rel) =>
            exists pm1 pm2 kind,
            <<PM1: IdentMap.find tid (conf_promises cM1) = Some pm1>> /\
            <<PM2: conf_promises cM2 = IdentMap.add tid pm2 (conf_promises cM1)>> /\
            <<PMREL: Memory.write pm1 (conf_mem cM1) loc from to val (Capability_lift x t rel) pm2 (conf_mem cM2) kind>>
          | None =>
            <<MEMEQ: conf_mem cM1 = conf_mem cM2>> /\
            <<PMEMEQ: conf_promises cM1 = conf_promises cM2>>
          end):
  pi_step_lift x t e tid (cS1,cT1,cM1) (cS2,cT2,cM2)
.
Hint Constructors pi_step_lift.

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

Lemma pi_step_lifting
      tid cST1 cST2 x t
      (PI_STEPS: rtc (pi_step_except tid) cST1 cST2):
  exists cM2, rtc (pi_step_lift_except x t tid) (cST1,cST1.(snd)) (cST2,cM2).
Proof.
Admitted.

Lemma pi_step_lift_future
      x t tid cS1 cT1 cM1 cS2 cT2 cM2 lst1 lc1
      (FIND: IdentMap.find tid cM1.(Configuration.threads) = Some (lst1,lc1))
      (PI_STEPS: rtc (pi_step_lift_except x t tid) (cS1,cT1,cM1) (cS2,cT2,cM2))
      (WF: Configuration.wf cM1):
  <<MEMFUT: Memory.future (conf_mem cM1) (conf_mem cM2)>> /\
  <<TIMELE: TimeMap.le (conf_sc cM1) (conf_sc cM2)>> /\
  <<LOCWF: Local.wf lc1 (conf_mem cM2)>> /\
  <<MEMCLOTM: Memory.closed_timemap (conf_sc cM2) (conf_mem cM2)>> /\
  <<MEMCLO: Memory.closed (conf_mem cM2)>>.
Proof.
Admitted.

Lemma rtc_pi_step_lift_find
      cSTM1 cSTM2 tid loc ts
      (STEPS: rtc (pi_step_lift_except loc ts tid) cSTM1 cSTM2):
  IdentMap.find tid cSTM1.(fst).(snd).(Configuration.threads) = IdentMap.find tid cSTM2.(fst).(snd).(Configuration.threads) /\
  IdentMap.find tid cSTM1.(snd).(Configuration.threads) = IdentMap.find tid cSTM2.(snd).(Configuration.threads).
Proof.
  ginduction STEPS; eauto.
  des. rewrite <-IHSTEPS, <-IHSTEPS0.
  inv H. inv PI_STEP. inv PI_STEP0. inv PI_STEP.
  ss; split; [by eapply small_step_find; eauto|].
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
  destruct (IdentMap.find tid (Configuration.threads cT2)) eqn: TH; cycle 1.
  { apply Operators_Properties.clos_rt_rt1n_iff in STEP.
    apply Operators_Properties.clos_rt_rtn1_iff in STEP. 
    inv STEP. 
    - inv PI_CONSISTENT. exploit CONSIS; eauto. 
    - inv H. inv PI_STEP. inv STEPT. ss. by rewrite IdentMap.gss in TH.
  }
  destruct p as [[lang2 st2] lc2].

  exploit rtc_pi_step_future; [eauto|..].
  { eapply rtc_implies, STEP. i. inv PR. eauto. }
  i; des. ss.

  assert (STEPS_LIFT:=pi_step_lifting loc ts STEPS). des.
  rename cM2 into cM3. ss.

  cut(forall cM4 
       (PI_STEPS: rtc (small_step_evt tid) cM3 cM4)
       (FULFILL: can_fulfill cM4 tid loc ts),
      exists cS4, 
      <<STEPS:  rtc (pi_step_evt tid) (cS3,cM3) (cS4,cM4)>> /\
      <<STATE:  IdentMap.find tid (conf_st cS4) = IdentMap.find tid (conf_st cM4)>>).
  { 
    intro MAIN.

    exploit pi_step_lift_future; eauto.
    { inv WF2; eauto. }
    i. des.

    exploit CONSISTENT2; s; eauto.
    i; des. rename e2 into th2.
    clear FUTURES FUTURET.

    exploit rtc_pi_step_lift_find; eauto.
    s; intro EQ. des. rewrite THREAD, TH in EQ. depdes EQ.

    exploit rtc_thread_step_unset_promises; [ | |eauto|eauto| | ].
    { eapply rtc_implies, STEPS0. i. inv PR. eauto. }
    { rewrite <- EQ0. eauto. }
    { rewrite PROMISES. apply Cell.bot_get. }
    intro FULFILL.

    destruct FULFILL.
    exploit MAIN; eauto.
    intro STEPS2. des. 

    eapply small_step_to_program_step_writing in STEP0; eauto. 
    des. destruct EVENT0.
    esplits; eauto using (pi_step_pf_step STEPS3).
    setoid_rewrite IdentMap.Properties.F.map_o in STATE.
    rewrite TH0 in STATE. ss.
    destruct (IdentMap.find tid cS4.(Configuration.threads)) as [[ ]|] eqn: EQ
    ; depdes STATE; eauto.
  }

(*   ss. move TH at top. clear THREAD PROMISE lst3 lc3 from msg. *)
(*   apply Operators_Properties.clos_rt_rt1n_iff in STEPS. *)
(*   apply Operators_Properties.clos_rt_rtn1_iff in STEPS. *)

(*   set (cSTM3 := (cS3,cT3,cM3)) in *. *)
(*   change cS3 with (cSTM3.(fst).(fst)). *)
(*   change cT3 with (cSTM3.(fst).(snd)). *)
(*   change cM3 with (cSTM3.(snd)). *)
(*   clearbody cSTM3. clear cS3 cT3 cM3. *)
(*   induction STEPS. *)
(*   { s. i. eapply pi_consistent_rtc_small_step_pi; eauto.  *)


(* econs; eauto. *)



(* } *)

(*   intros cM4 STEPS4. *)
(*   apply Operators_Properties.clos_rt_rt1n_iff in STEPS4. *)
(*   apply Operators_Properties.clos_rt_rtn1_iff in STEPS4. *)
(*   induction STEPS4; i; eauto. *)

  


  

  



(*   intros cM4 PI_STEPS. *)
(*   apply Operators_Properties.clos_rt_rt1n_iff in PI_STEPS. *)
(*   apply Operators_Properties.clos_rt_rtn1_iff in PI_STEPS. *)
(*   induction PI_STEPS; i. *)
(*   { eexists; eauto. } *)
  
  




  admit.
Admitted.


(* Lemma memory_lower_get1: *)
(*   forall mem1 mem2 loc from ts val rel1 rel2 l t f v r1 *)
(*      (MEM: Memory.lower mem1 loc from ts val rel1 rel2 mem2) *)
(*      (GET: Memory.get l t mem1 = Some (f, Message.mk v r1)), *)
(*   exists r2, Memory.get l t mem2 = Some (f, Message.mk v r2) /\  *)
(*   Capability.le r2 r1. *)
(* Proof. *)
(*   i. inv MEM. inv REMOVE. inv ADD. *)
(*   unfold Memory.get in *.  *)
(*   destruct (Loc.eq_dec l loc); subst. *)
(*   - setoid_rewrite LocFun.add_spec_eq in ADD0. *)
(*     setoid_rewrite LocFun.add_spec_eq. *)
(*     inv REMOVE0. destruct (Time.eq_dec t ts); subst. *)
(*     + setoid_rewrite GET in GET0. inv GET0. *)
(*       esplits; eauto. *)
(*       setoid_rewrite Cell.add_get2; eauto. *)
(*     + inv ADD0. unfold Cell.get. rewrite <-H1. *)
(*       rewrite DenseOrder.DOMap.gso; eauto. *)
(*       rewrite <- H0, DenseOrder.DOMap.gro; eauto. *)
(*       esplits; eauto using Capability_le_refl. *)
(*   - setoid_rewrite LocFun.add_spec_neq; eauto. *)
(*     setoid_rewrite LocFun.add_spec_neq; eauto. *)
(*     esplits; eauto using Capability_le_refl. *)
(* Qed.     *)


(* Inductive pf_rel: Configuration.t -> Configuration.t -> Prop := *)
(* | pf_rel_base  *)
(*     c *)
(*     (PRBOT: forall tid lang st lc *)
(*               (TH: IdentMap.find tid c.(Configuration.threads) = Some (existT _ lang st, lc)), *)
(*             lc.(Local.promises) = Memory.bot):  *)
(*   pf_rel c c *)

(* | pf_rel_promise *)
(*     e tid cS cT cT' *)
(*     (REL: pf_rel cS cT) *)
(*     (STEPT: small_step e tid cT cT') *)
(*     (PROMISE: match e with | ThreadEvent.promise _ _ _ _ _ => True | _ => False end): *)
(*   pf_rel cS cT' *)

(* | pf_rel_other *)
(*     e tid cS cS' cT cT' *)
(*     (REL: pf_rel cS cT) *)
(*     (STEPS: small_step e tid cS cS') *)
(*     (STEPT: small_step e tid cT cT') *)
(*     (PROMISE: match e with | ThreadEvent.promise _ _ _ _ _ => False | _ => True end): *)
(*   pf_rel cS cT' *)
(* . *)

(* Definition pi_machine_event (e:ThreadEvent.t) tid (threads:Threads.t): Prop := *)
(*   forall loc to ord ts tid' *)
(*     (RW: ThreadEvent.is_reading e = Some (loc, to, ord) \/ *)
(*          ThreadEvent.is_writing e = Some (loc, to, ord)) *)
(*     (TNEQ: tid <> tid'), *)
(*   ~ Threads.is_promised tid' loc ts threads. *)

(* Inductive pi_step (tid:Ident.t) (c1 c2:Configuration.t): Prop := *)
(* | pi_step_intro *)
(*     e *)
(*     (STEP: small_step e tid c1 c2) *)
(*     (READINFO: pi_machine_event e tid c1.(Configuration.threads)) *)
(* . *)

(* Inductive pi_step_all (c1 c2:Configuration.t): Prop := *)
(* | pi_step_all_intro *)
(*     tid *)
(*     (PI_STEP: pi_step tid c1 c2) *)
(* . *)

(* Inductive pi_step_except (tid_except:Ident.t) (c1 c2:Configuration.t): Prop := *)
(* | pi_step_except_intro *)
(*     tid *)
(*     (PI_STEP: pi_step tid c1 c2) *)
(*     (TID: tid <> tid_except) *)
(* . *)

(* Definition pi_consistent (c1:Configuration.t): Prop := *)
(*   forall tid lang c2 st2 lc2 loc ts from msg *)
(*     (TID: IdentMap.find tid c1.(Configuration.threads) <> None) *)
(*     (STEPS: rtc (pi_step_except tid) c1 c2) *)
(*     (THREAD: IdentMap.find tid c2.(Configuration.threads) = Some (existT _ lang st2, lc2)) *)
(*     (PROMISE: Memory.get loc ts lc2.(Local.promises) = Some (from, msg)), *)
(*   exists c3 st3 lc3, *)
(*     <<STEPS: rtc (pi_step tid) c2 c3>> /\ *)
(*     <<THREAD: IdentMap.find tid c3.(Configuration.threads) = Some (existT _ lang st3, lc3)>> /\ *)
(*     <<PROMISE: Memory.get loc ts lc3.(Local.promises) = None>>. *)

(* Definition pi_racefree (cST1:Configuration.t*Configuration.t): Prop := *)
(*   forall cST2 ordr ordw *)
(*     (STEPS: rtc pi_step_all cST1 cST2) *)
(*     (RACE: race (fst cST2) ordr ordw), *)
(*     <<ORDR: Ordering.le Ordering.acqrel ordr>> /\ *)
(*     <<ORDW: Ordering.le Ordering.acqrel ordw>>. *)


(* Lemma race_pi_wf *)
(*       cST ord1 ord2 *)
(*       (WF: pi_wf cST) *)
(*       (RACE: race (snd cST) ord1 ord2): *)
(*   race (fst cST) ord1 ord2. *)
(* Proof. *)
(*   inv WF. inv RACE. *)
(*   ss. econs; cycle 3; [apply STATE1|apply STATE2|..]; eauto.  *)
(*   - s. setoid_rewrite IdentMap.Properties.F.map_o. by rewrite TH1. *)
(*   - s. setoid_rewrite IdentMap.Properties.F.map_o. by rewrite TH2. *)
(* Qed. *)


(* Lemma pi_steps_promise *)
(*       tid *)
(*       cST1 lst1 lc1 *)
(*       cST3 lst3 lc3 *)
(*       loc from ts msg *)
(*       (WF1: pi_wf cST1) *)
(*       (STEPS: rtc (pi_step tid) cST1 cST3) *)
(*       (TH1: IdentMap.find tid cST1.(snd).(Configuration.threads) = Some (lst1, lc1)) *)
(*       (TH3: IdentMap.find tid cST3.(snd).(Configuration.threads) = Some (lst3, lc3)) *)
(*       (GET1: Memory.get loc ts lc1.(Local.promises) = Some (from, msg)) *)
(*       (GET3: Memory.get loc ts lc3.(Local.promises) = None): *)
(*   exists cST2 lang2 st2 lc2 e2 st2' ord2, *)
(*     <<STEPS: rtc (pi_step tid) cST1 cST2>> /\ *)
(*     <<TH2: IdentMap.find tid cST2.(snd).(Configuration.threads) = Some (existT _ lang2 st2, lc2)>> /\ *)
(*     <<STATE2: lang2.(Language.step) (Some e2) st2 st2'>> /\ *)
(*     <<EVENT2: ProgramEvent.is_writing e2 = Some (loc, ord2)>> /\ *)
(*     <<ORD2: Ordering.le ord2 Ordering.relaxed>>. *)
(* Proof. *)
(*   revert lst1 lc1 from msg TH1 GET1. *)
(*   induction STEPS; i. *)
(*   { rewrite TH1 in TH3. inv TH3. rewrite GET3 in GET1. done. } *)
(*   inversion H. subst. inv STEPT. destruct (Memory.get loc ts lc2.(Local.promises)) as [[]|] eqn:X. *)
(*   { exploit IHSTEPS; eauto; s. *)
(*     { eapply pi_step_future; cycle 1; eauto. } *)
(*     { rewrite IdentMap.Facts.add_eq_o; eauto. } *)
(*     i. des. esplits; cycle 1; eauto. *)
(*     etrans; [|eauto]. econs 2; [|econs 1]. eauto. *)
(*   } *)
(*   clear H STEPS IHSTEPS. ss. rewrite TH1 in TID. inv TID.  *)
(*   exploit thread_step_unset_promises; eauto; s. *)
(*   { inv WF1. s. eapply WFT. eauto. } *)
(*   i. des. inv WF1. esplits; eauto. *)
(* Qed. *)
