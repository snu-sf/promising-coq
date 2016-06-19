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

Definition ThreadEvent_is_promising (e: ThreadEvent.t) : option (Loc.t * Time.t) :=
  match e with
  | ThreadEvent.promise loc from to v rel => Some (loc, to)
  | _ => None
  end.

Inductive small_step (e:ThreadEvent.t) (tid:Ident.t) (c1:Configuration.t): forall (c2:Configuration.t), Prop :=
| small_step_intro
    lang st1 st2 lc1 lc2 sc2 memory2
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEP: Thread.step e (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) (Thread.mk _ st2 lc2 sc2 memory2)):
    small_step e tid c1 (Configuration.mk (IdentMap.add tid (existT _ _ st2, lc2) c1.(Configuration.threads)) sc2 memory2)
.

Inductive tau_small_step (tid:Ident.t) (c1 c2:Configuration.t): Prop :=
| tau_small_step_intro
    e
    (STEP: small_step e tid c1 c2)
    (TAU: ThreadEvent.get_event e = None)
.

Inductive small_step_all_evt (tid:Ident.t) (c1 c2:Configuration.t): Prop :=
| small_step_all_evt_intro e
    (STEP: small_step e tid c1 c2)
.

Inductive pf_step (e:ThreadEvent.t) (tid:Ident.t) (c1:Configuration.t): forall (c2:Configuration.t), Prop :=
| pf_step_intro c2
    (STEP: small_step e tid c1 c2)
    (NO_PROMISE: ThreadEvent_is_promising e = None):
    pf_step e tid c1 c2
.

Inductive pf_step_all_evt tid (c1 c2:Configuration.t): Prop :=
| pf_step_all_evt_intro
    e
    (PI_STEP: pf_step e tid c1 c2)
.

Inductive pf_step_all (c1 c2:Configuration.t): Prop :=
| pf_step_all_intro
    tid
    (PI_STEP: pf_step_all_evt tid c1 c2)
.

(* NOTE: `race_rw` requires two *distinct* threads to have a race.
 * However, C/C++ acknowledges intra-thread races.  For example,
 * according to the Standard, `f(x=1, x)` is RW-racy on `x`, since the
 * order of evaluation of the arguments is unspecified.  We currently
 * ignore this aspect of the race semantics.
 *)

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
    tid1 lang1 st1 lc1 e1 st1'
    tid2 lang2 st2 lc2 e2 st2'
    (TID: tid1 <> tid2)
    (TH1: IdentMap.find tid1 c.(Configuration.threads) = Some (existT _ lang1 st1, lc1))
    (TH2: IdentMap.find tid2 c.(Configuration.threads) = Some (existT _ lang2 st2, lc2))
    (STATE1: lang1.(Language.step) (Some e1) st1 st1')
    (STATE2: lang2.(Language.step) (Some e2) st2 st2')
    (EVENT: race_condition e1 e2 ord1 ord2)
.              

Definition pf_racefree (c1:Configuration.t): Prop :=
  forall c2 ordr ordw
    (STEPS: rtc pf_step_all c1 c2)
    (RACE: race c2 ordr ordw),
    <<ORDR: Ordering.le Ordering.acqrel ordr>> /\
    <<ORDW: Ordering.le Ordering.acqrel ordw>>.

Inductive pi_step: Ident.t -> Configuration.t*Configuration.t -> Configuration.t*Configuration.t -> Prop :=
| pi_step_step
    e tid cS1 cT1 cS2 cT2
    (STEPT: small_step e tid cT1 cT2)
    (STEPS: if ThreadEvent_is_promising e
            then cS1 = cS2
            else small_step e tid cS1 cS2)
    (LANGMATCH: 
     option_map fst (IdentMap.find tid cS2.(Configuration.threads)) =
     option_map fst (IdentMap.find tid cT2.(Configuration.threads))):
  pi_step tid (cS1,cT1) (cS2,cT2)
.

Inductive pi_step_except (tid_except:Ident.t) cST1 cST2: Prop :=
| pi_step_except_intro
    tid
    (PI_STEP: pi_step tid cST1 cST2)
    (TID: tid <> tid_except)
.

Inductive pi_step_all cST1 cST2: Prop :=
| pi_step_all_intro
    tid
    (PI_STEP: pi_step tid cST1 cST2)
.

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

Inductive pi_consistent: Configuration.t*Configuration.t -> Prop :=
| pi_consistent_intro cS1 cT1
  (CONSIS:
    forall tid cS2 cT2 lst2 lc2 loc ts from msg
    (* (TID: IdentMap.find tid cT1.(Configuration.threads) <> None) *)
    (STEPS: rtc (pi_step_except tid) (cS1,cT1) (cS2,cT2))
    (THREAD: IdentMap.find tid cT2.(Configuration.threads) = Some (lst2, lc2))
    (PROMISE: Memory.get loc ts lc2.(Local.promises) = Some (from, msg)),
  exists cS3 lang3 st3 st3' lc3 e ord,
    <<STEPS: rtc (pf_step_all_evt tid) cS2 cS3>> /\
    <<THREAD: IdentMap.find tid cS3.(Configuration.threads) = Some (existT _ lang3 st3, lc3)>> /\
    <<STATE: lang3.(Language.step) (Some e) st3 st3'>> /\
    <<EVENT: ProgramEvent.is_writing e = Some (loc, ord)>> /\
    <<ORD: Ordering.le ord Ordering.relaxed>>):
  pi_consistent (cS1, cT1).

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

Lemma rtc_tau_thread_step_rtc_tau_small_step_aux
      lang tid threads
      th1 th2
      (TID: IdentMap.find tid threads = Some (existT _ lang th1.(Thread.state), th1.(Thread.local)))
      (STEP: (rtc (@Thread.tau_step lang)) th1 th2):
  rtc (tau_small_step tid)
      (Configuration.mk threads th1.(Thread.sc) th1.(Thread.memory))
      (Configuration.mk (IdentMap.add tid (existT _ lang th2.(Thread.state), th2.(Thread.local)) threads) th2.(Thread.sc) th2.(Thread.memory)).
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
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (TID: IdentMap.find tid threads = Some (existT _ lang st1, lc1))
      (STEP: (rtc (@Thread.tau_step lang)) (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
  rtc (tau_small_step tid)
      (Configuration.mk threads sc1 mem1)
      (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) sc2 mem2).
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

Lemma pi_step_future
      tid cST1 cST2
      (WF1: pi_wf cST1)
      (STEP: pi_step tid cST1 cST2):
  <<WF2: pi_wf cST2>> /\
  <<FUTURES: Memory.future cST1.(fst).(Configuration.memory) cST2.(fst).(Configuration.memory)>> /\
  <<FUTURET: Memory.future cST1.(snd).(Configuration.memory) cST2.(snd).(Configuration.memory)>>.
Proof.
  inv WF1. inv STEP. splits; cycle 1. 
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
      tid cST1 cST2
      (WF1: pi_wf cST1)
      (STEPS: rtc (pi_step tid) cST1 cST2):
  <<WF2: pi_wf cST2>> /\
  <<FUTURES: Memory.future cST1.(fst).(Configuration.memory) cST2.(fst).(Configuration.memory)>> /\
  <<FUTURET: Memory.future cST1.(snd).(Configuration.memory) cST2.(snd).(Configuration.memory)>>.
Proof.
  revert WF1. induction STEPS; i.
  - splits; auto; econs.
  - exploit pi_step_future; eauto. i. des.
    exploit IHSTEPS; eauto. i. des.
    splits; auto; etrans; eauto.
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
      (STEP: rtc (small_step_all_evt tid1) c1 c2)
      (TID: tid1 <> tid2):
  IdentMap.find tid2 c1.(Configuration.threads) = IdentMap.find tid2 c2.(Configuration.threads).
Proof.
  induction STEP; auto. 
  inv H. rewrite <-IHSTEP.
  eauto using small_step_find.
Qed.

Hint Constructors small_step.
Hint Constructors Thread.program_step.
Hint Constructors Thread.step.

Lemma consistent_small_step_pi
      e tid c1 c2 c3
      (CONSISTENT: Configuration.consistent c1)
      (STEPS: rtc (small_step_all_evt tid) c1 c2)
      (STEP: small_step e tid c2 c3):
   forall loc to ord
     (RW: ThreadEvent.is_reading e = Some (loc, to, ord)),
  ~Threads.is_promised tid loc to c2.(Configuration.threads).
Proof.
Admitted.

Lemma pi_steps_pf_steps
      tid cST1 cST2
      (PI_STEPS: rtc (pi_step tid) cST1 cST2):
  rtc (pf_step_all_evt tid) (fst cST1) (fst cST2).
Proof.
  induction PI_STEPS; eauto.
  inv H. destruct (ThreadEvent_is_promising e) eqn: PROM.
  + subst. eauto.
  + econs; eauto. econs. econs; eauto.
Qed.

Lemma pi_steps_small_steps
      tid cST1 cST2
      (PI_STEPS: rtc (pi_step tid) cST1 cST2):
  rtc (small_step_all_evt tid) (snd cST1) (snd cST2).
Proof.
  induction PI_STEPS; eauto.
  inv H. econs; eauto. econs; eauto.
Qed.

Lemma pi_consistent_small_step_pi_rw
      e tid cST1 cST2 cT3
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (CONSISTENT: Configuration.consistent cST1.(snd))
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step tid) cST1 cST2)
      (STEP: small_step e tid cST2.(snd) cT3):
  forall loc to ord tid' ts
    (NEQ: tid <> tid')
    (RW: ThreadEvent.is_reading e = Some (loc, to, ord) \/
         ThreadEvent.is_writing e = Some (loc, to, ord)),
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
  { (* TODO: is ThreadEvent.is_reading/writing neccessary? *)
    ss. inv STEP. inv STEP0; [by inv STEP; inv RW; inv H|].
    exploit rtc_pi_step_future; eauto.
    i; des. clear FUTURES FUTURET.
    assert (LC1: exists lc1', IdentMap.find tid (Configuration.threads cS3) = Some (existT _ lang0 st1, lc1')).
    { eexists. erewrite <-(@rtc_small_step_find _ _ cS2); eauto; cycle 1.
      { eapply rtc_implies, STEPS.
        i. inv PR. inv PI_STEP. econs; eauto. } 
      inv WF2. ss. setoid_rewrite IdentMap.Properties.F.map_o.
      by rewrite TID0. }
    des.
    inv STEP; inv RW; inv H
    ; econs; eauto; first [by econs 1; ss|by econs 2; ss].
  }
  i. des. by destruct ord0; inv x0; inv x1.
Qed.

Lemma pi_consistent_small_step_pi
      e tid cST1 cST2 cT3
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (CONSISTENT: Configuration.consistent cST1.(snd))
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step tid) cST1 cST2)
      (STEP: small_step e tid cST2.(snd) cT3):
  exists cS3, pi_step tid cST2 (cS3,cT3).
Proof.
  destruct cST1 as [cS1 cT1], cST2 as [cS2 cT2].
  assert (RW:= pi_consistent_small_step_pi_rw WF PI_CONSISTENT CONSISTENT PI_RACEFREE PI_STEPS STEP).
  assert (R:= consistent_small_step_pi CONSISTENT (pi_steps_small_steps PI_STEPS) STEP).
  exploit rtc_pi_step_future; eauto. 
  i; des. inv WF2. ss. inv STEP. inv STEP0.
  - eexists. econs; [by eauto|by inv STEP; s; eauto|].
    inv STEP. ss. rewrite IdentMap.gss.
    setoid_rewrite IdentMap.Properties.F.map_o.
    by rewrite TID.
  - inv STEP.
    { eexists. econs.
      - econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID. 
        + econs 2; econs 1; eauto.
      - s. by rewrite !IdentMap.gss.
    }
    { inv LOCAL. eexists. econs.
      - econs; eauto. econs 2. econs 2; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID. 
        + econs 2; econs 2; eauto.
          econs; eauto.
          s. eapply RL; eauto.
          i. destruct (Ident.eq_dec tid tid0) eqn: EQ.
          * subst. eapply R; s; eauto.
          * eapply RW; s; eauto.
      - s. by rewrite !IdentMap.gss.
    }
    { inv LOCAL. inv WRITE. eexists. econs.
      - econs; eauto. econs 2. econs 3; eauto. econs; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID. 
        + econs 2; econs 3; eauto. 
          econs; [|by esplits; [|apply RELEASE]].
          admit.
      - s. by rewrite !IdentMap.gss.
    }
    { admit.
    }
    { inv LOCAL. eexists. econs.
      - econs; eauto. econs 2. econs 5; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID. 
        + econs 2; econs 5; eauto.
          econs; eauto.
      - s. by rewrite !IdentMap.gss.
    }
    { inv LOCAL. eexists. econs.
      - econs; eauto. econs 2. econs 6; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID. 
        + econs 2; econs 6; eauto.
          econs; eauto.
      - s. by rewrite !IdentMap.gss.
    }
Admitted.

Lemma pi_consistent_rtc_tau_small_step_pi
      tid cST1 cST2 cT3
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (CONSISTENT: Configuration.consistent cST1.(snd))
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step tid) cST1 cST2)
      (STEP: rtc (tau_small_step tid) cST2.(snd) cT3):
  exists cS3, rtc (pi_step tid) cST2 (cS3,cT3).
Proof.
  apply Operators_Properties.clos_rt_rt1n_iff in STEP.
  apply Operators_Properties.clos_rt_rtn1_iff in STEP.
  destruct cST2 as [cS2 cT2].
  induction STEP; eauto.
  des. inv H. ss.
  exploit pi_consistent_small_step_pi; try etransitivity; eauto.
  i; des. eexists. etrans; eauto. econs; eauto.
Qed.

Lemma pi_consistent_step_pi
      cST1 cT2 e tid
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (CONSISTENT: Configuration.consistent cST1.(snd))
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (STEP: Configuration.step e tid cST1.(snd) cT2):
  exists cS2, rtc (pi_step tid) cST1 (cS2,cT2).
Proof.
  exploit step_small_steps; eauto; [by inv WF|].
  i. des. subst.
  exploit pi_consistent_rtc_tau_small_step_pi; eauto. i; des.
  exploit pi_consistent_small_step_pi; eauto. i; des.
  eexists. etrans; eauto. econs; eauto.
Qed.

Lemma Capability_le_refl: forall r,
  Capability.le r r.
Proof. econs; econs 2; econs. Qed.

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

Lemma ordering_relaxed_dec
      ord:
  Ordering.le ord Ordering.relaxed \/ Ordering.le Ordering.acqrel ord.
Proof. destruct ord; auto. Qed.

Lemma thread_step_unset_promises
      lang loc e from ts msg (th1 th2:Thread.t lang)
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
  - by rewrite TH1 in TH2.
  - inv LOCAL. inv WRITE.
    exploit Memory.promise_promises_get1; eauto. i. des.
    exploit fulfill_unset_promises; eauto. i. des. subst.
    esplits; eauto; s; eauto.
    destruct (ordering_relaxed_dec ord); auto.
    apply RELEASE in H. des. unfold Memory.get in *.
    by ss; rewrite H, Cell.bot_get in TH1.
  - inv LOCAL1. inv LOCAL2. inv WRITE.
    exploit Memory.promise_promises_get1; eauto. i. des.
    exploit fulfill_unset_promises; eauto. i. des. subst.
    esplits; eauto; s; eauto.
    destruct (ordering_relaxed_dec ordw); auto.
    apply RELEASE in H. des. unfold Memory.get in *.
    by ss; rewrite H, Cell.bot_get in TH1.
Qed.

Lemma rtc_small_step_unset_promises
      tid c1 c3 lst1 lst3 lc1 lc3 loc from ts msg 
      (WF1: Configuration.wf c1)
      (STEPS: rtc (small_step_all_evt tid) c1 c3)
      (TH1: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1))
      (TH3: IdentMap.find tid c3.(Configuration.threads) = Some (lst3, lc3))
      (GET1: Memory.get loc ts lc1.(Local.promises) = Some (from, msg))
      (GET3: Memory.get loc ts lc3.(Local.promises) = None):
  exists c2 lang2 st2 st2' lc2 e2 ord2,
    <<STEPS: rtc (small_step_all_evt tid) c1 c2>> /\
    <<TH2: IdentMap.find tid c2.(Configuration.threads) = Some (existT _ lang2 st2, lc2)>> /\
    <<STATE2: lang2.(Language.step) (Some e2) st2 st2'>> /\
    <<EVENT2: ProgramEvent.is_writing e2 = Some (loc, ord2)>> /\
    <<ORD2: Ordering.le ord2 Ordering.relaxed>>.
Proof.
  ginduction STEPS; i.
  { rewrite TH1 in TH3; inv TH3. rewrite GET1 in GET3; inv GET3. }
  inv H. exploit small_step_future; eauto. i; des.
  assert (STEP0 := STEP). inv STEP0. 
  rewrite TH1 in TID. inv TID. ss.
  destruct (Memory.get loc ts lc2.(Local.promises)) eqn: PRM.
  - destruct p as [t m]. exploit IHSTEPS; eauto.
    { rewrite IdentMap.gss. eauto. }
    clear IHSTEPS; i; des. 
    esplits; try apply TH2; eauto.
    etransitivity; [|by apply STEPS0].
    econs; eauto. econs; eauto.
  - inv WF1. inv WF. 
    exploit thread_step_unset_promises; eauto; s; eauto.
    i; des; esplits; eauto.
Qed.










(* Lemma pi_consistent_pi_step_pi_consistent *)
(*       c1 c2 *)
(*       tid *)
(*       (PI_CONSISTENT: pi_consistent c1) *)
(*       (PI_RACEFREE: pi_racefree c1) *)
(*       (WF1: Configuration.wf c1) *)
(*       (WF2: Configuration.wf c2) *)
(*       (CONSISTENT1: Configuration.consistent c1) *)
(*       (CONSISTENT2: Configuration.consistent c2) *)
(*       (STEP: rtc (pi_step tid) c1 c2): *)
(*   pi_consistent c2. *)
(* Proof. *)
(*   ii. destruct (Ident.eq_dec tid tid0). *)
(*   - subst tid0. *)
(*     (* TODO: sketch the proof *) *)
(*     admit. *)
(*   - eapply PI_CONSISTENT. *)
(*     + erewrite <- rtc_pi_step_find; eauto. *)
(*     + etrans; [|eauto]. eapply rtc_implies; [|apply STEP]. econs; eauto. *)
(* Admitted. *)


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
