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
Require Import TView.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import DRFBase.
Require Import SmallStep.
Require Import Fulfilled.
Require Import Race.
Require Import PIStep.
Require Import PIStepProgress.
Require Import Lift.
Require Import PromiseConsistent.
Require Import PFConsistent.

Set Implicit Arguments.

Inductive can_fulfill (tid: Ident.t) loc ts (c1 c4: Configuration.t) : Prop :=
| can_fulfill_intro
    c2 c3 e ord lst2 lc2 from2 msg2 from val rel
    (STEPS: rtc (small_step_evt false tid) c1 c2)
    (STEP: small_step false tid e c2 c3)
    (THREAD: IdentMap.find tid c2.(Configuration.threads) = Some (lst2, lc2))
    (PROMISE: Memory.get loc ts lc2.(Local.promises) = Some (from2, msg2))
    (EVENT: ThreadEvent.is_writing e = Some (loc, from, ts, val, rel, ord))
    (ORD: Ordering.le ord Ordering.relaxed)
    (STEPS: rtc (small_step_evt false tid) c3 c4):
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

Lemma rtc_small_step_fulfill
      tid loc ts c1 lst1 lc1 c2 lst2 lc2 from msg 
      (STEPS: rtc (small_step_evt false tid) c1 c2)
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
  inv H. inv USTEP. ss. rewrite FIND1 in TID. depdes TID.
  destruct (Memory.get loc ts lc3.(Local.promises)) eqn: PRM.
  - destruct p as [t m].
    rewrite IdentMap.gss in IHSTEPS.
    exploit IHSTEPS; eauto.
    intros []; i.
    econs; swap 5 8; eauto.
    etrans; [|apply STEPS0].
    econs; eauto 10.  
  - exploit thread_step_unset_promises; eauto; s; eauto.
    i; des. econs; eauto 10. 
Qed.

Lemma can_fulfill_lt
      tid loc ts c1 c3 lst1 lc1 from msg
      (FULFILL: can_fulfill tid loc ts c1 c3)
      (FIND: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1))
      (PROMISE: Memory.get loc ts lc1.(Local.promises) = Some (from, msg))
      (WF: Configuration.wf c1):
  Time.lt (lc1.(Local.tview).(TView.cur).(View.rlx) loc) ts.
Proof.
  destruct FULFILL.
  inv STEP.
  eapply rtc_implies, rtc_small_step_tview_le in STEPS; eauto; cycle 1.
  inv STEP0; inv STEP; inv EVENT.
  + inv LOCAL. inv WRITABLE.
    move STEPS at bottom. move TS at bottom.
    eapply TimeFacts.le_lt_lt; eauto. apply STEPS.
  + inv LOCAL1. inv READABLE. inv LOCAL2. inv WRITABLE.
    ss. move STEPS at bottom. move TS at bottom.
    eapply TimeFacts.le_lt_lt; eauto.
    repeat (etrans; [|apply Time.join_l]). apply STEPS.
Qed.

Lemma rtc_small_step_unset_fulfill
      tid loc ts c1 lst1 lc1 c2 lst2 lc2 from msg 
      (STEPS: rtc (small_step_evt false tid) c1 c2)
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
  inv H. inv USTEP. ss. rewrite FIND1 in TID. depdes TID.
  destruct (Memory.get loc ts lc3.(Local.promises)) eqn: PRM.
  - destruct p as [t m].
    rewrite IdentMap.gss in IHSTEPS.
    exploit IHSTEPS; eauto.
    intros []; i.
    econs; swap 5 8; eauto.
    etrans; [|apply STEPS0].
    econs; eauto 10.
  - exploit thread_step_unset_promises; eauto; s; eauto.
    i; des. econs; eauto. 
Qed.

Lemma consistent_can_fulfill_promises_future
      tid ths sc sc1 mem mem1 lang st lc
      (TH1: IdentMap.find tid ths = Some (existT _ lang st, lc))
      (CONSISTENT: Thread.consistent (Thread.mk _ st lc sc mem))
      (FUTURE: Memory.future mem mem1)
      (TIMELE: TimeMap.le sc sc1)
      (LOCWF: Local.wf lc mem1)
      (SC: Memory.closed_timemap sc1 mem1)
      (MEM: Memory.closed mem1):
  can_fulfill_promises tid (Configuration.mk ths sc1 mem1).
Proof.
  apply consistent_pf_consistent in CONSISTENT.
  econs. ii. destruct lst1 as [lang1 st1].
  exploit CONSISTENT; ss; eauto.
  i; des. destruct e2.
  exploit rtc_tau_program_step_rtc_small_step; swap 1 2; eauto.
  intro STEPS1. ss.
  match goal with [STEPS1: rtc _ _ ?cfg|-_] => set (c2 := cfg) in * end.
  exploit (@rtc_small_step_unset_fulfill tid loc ts (Configuration.mk ths sc1 mem1)); cycle 1.
  - apply THREAD.
  - apply PROMISE.
  - instantiate (3:=c2). s. rewrite IdentMap.gss. eauto.
  - rewrite PROMISES. apply Cell.bot_get.
  - intro FULFILL. exists c2; split; eauto.
    econs; i. unfold c2 in *. ss.
    rewrite IdentMap.gss in THREAD0. depdes THREAD0.
    rewrite PROMISES in PROMISE0.
    by setoid_rewrite Cell.bot_get in PROMISE0.
  - eauto.
Qed.

Lemma can_fulfill_promises_promise_consistent
      tid c
      (FULFILL: can_fulfill_promises tid c)
      (WF: Configuration.wf c):
  promise_consistent_th tid c.
Proof.
  ii. inv FULFILL. exploit FULFILL0; eauto.
  i; des.
  eapply can_fulfill_lt; eauto.
Qed.

Lemma write_step_tview_mon
      lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
      (WF1: TView.wf (Local.tview lc1))
      (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind):
  TView.le lc1.(Local.tview) lc2.(Local.tview).
Proof.
  inv STEP. ss. apply TViewFacts.write_tview_incr. auto.
Qed.

Lemma key_lemma_time_lt:
  forall (loc : Loc.t) (ts : Time.t) (k : Memory.op_kind)
    (cM4' : Configuration.t) (lc4 : Local.t) 
    (com4' : TView.t) (prm3' : Memory.t) (sc2 : TimeMap.t)
    (memory2 : Memory.t) (loc0 : Loc.t) (ts0 from : Time.t)
    (valr valw : Const.t) (relr relw : option View.t)
    (ordr : Ordering.t) (m1' : Memory.t) (ordw0 : Ordering.t)
    (releasedw : option View.t) (lc2 : Local.t)
    (LC2: TView.wf (Local.tview lc2))
    (tsw : Time.t) (valw0 : Const.t) (kind : Memory.op_kind),
    Time.lt ((TView.cur (Local.tview lc4)).(View.rlx) loc) ts ->
    Local.read_step
      {| Local.tview := com4'; Local.promises := prm3' |}
      (Configuration.memory cM4') loc0 ts0 valr relr ordr lc2 ->
    Local.write_step lc2 (Configuration.sc cM4')
                     (Configuration.memory cM4') loc0 ts0 tsw valw0 relr releasedw
                     ordw0 lc4 sc2 memory2 kind ->
    Memory.op m1' loc0 from ts0 valw (opt_View_lift loc ts relw)
              (Configuration.memory cM4') k ->
    Ordering.le Ordering.acqrel ordr -> False.
Proof.
  intros loc ts k cM4' lc4 com4' prm3' sc2 memory2 loc0 ts0 from valr valw relr relw ordr m1' ordw0 releasedw lc2 WF tsw valw0 kind TIMELT LOCAL1 LOCAL2 PMREL ORDR.
  assert (COM: TView.le lc2.(Local.tview) lc4.(Local.tview)).
  { eapply write_step_tview_mon; eauto. }
  assert (LT: Time.lt ((TView.cur (Local.tview lc2)).(View.rlx) loc) ts).
  { eapply TimeFacts.le_lt_lt; eauto. apply COM. }
  inv LOCAL1. ss.
  erewrite Memory.op_get2 in GET; eauto. inv GET.
  apply TimeFacts.join_lt_des in LT. des.
  revert BC. rewrite ORDR.
  s. destruct relw.(View.unwrap). ss.
  unfold TimeMap_lift. condtac; [|congr]. i.
  apply TimeFacts.join_lt_des in BC. des.
  eapply Time.lt_strorder. eauto.
Qed.

Lemma key_lemma_time_lt2:
  forall (loc : Loc.t) (ts : Time.t) (cM4' : Configuration.t)
    (com4' : TView.t) (loc0 : Loc.t) (ts0 : Time.t)
    (relw : option View.t) (ordr ordw0 : Ordering.t) 
    (tsw : Time.t) xx yy,
    Ordering.le Ordering.acqrel ordr ->
    Time.lt
      (TimeMap.join
         (TimeMap.join
            (TimeMap.join
               yy
               (View.rlx
                  (if Ordering.le Ordering.acqrel ordr
                   then opt_View_lift loc ts relw
                   else None).(View.unwrap))) (TimeMap.singleton loc0 tsw))
         xx loc) ts -> False.
Proof.
  intros.
  apply TimeFacts.join_lt_des in H0. des.
  apply TimeFacts.join_lt_des in AC. des.
  apply TimeFacts.join_lt_des in AC0. des.
  revert BC1. rewrite H. s.
  destruct relw.(View.unwrap). ss.
  unfold TimeMap_lift. condtac; [|congr]. i.
  apply TimeFacts.join_lt_des in BC1. des.
  eapply Time.lt_strorder. eauto.
Qed.

Lemma key_lemma_rw_race
  cS1 cT1 cS2 cT2 cS3 cT3 M3 cS4 cT4 M4 tid loc ts k e e0 pre cS3' cM3' cS4' cM4' cM5'
  (RACEFREE: pf_racefree cS1)
  (STEPS: rtc (pi_step_evt true tid) (cS1, cT1) (cS2, cT2))
  (STEPS_LIFT: rtc (pi_step_lift_except loc ts tid) (cS2, cT2, Configuration.memory cT2) (cS3, cT3, M3))
  (PSTEP : pi_step_lift_except_aux loc ts tid e (cS3, cT3, M3) (cS4, cT4, M4))
  (STEPS3: rtc (pi_step_evt false tid) (cS3, conf_update_memory cT3 M3) (cS3', cM3'))
  (PI_STEPS: with_pre (small_step false tid) (conf_update_memory cT4 M4) pre cM4')
  (PSTEP0: small_step false tid e0 cM4' cM5')

  lst2 lc2 from2 msg2
  (THREAD2: IdentMap.find tid (Configuration.threads cT2) = Some (lst2, lc2))
  (PROMISE2: Memory.get loc ts (Local.promises lc2) = Some (from2, msg2))

  msgs
  (WF3: pi_wf (View_lift_le loc ts msgs) (cS3', cM3'))
  (WF4: pi_wf (View_lift_le loc ts (msg_add loc e msgs)) (cS4', cM4'))

  lst lc3 lc4 prm
  (THS3: IdentMap.find tid (Configuration.threads cM3') = Some (lst, lc3))
  (THS4: IdentMap.find tid (Configuration.threads cM4') = Some (lst, lc4))
  (MEMLE: mem_eqlerel_lift loc ts prm k e (Configuration.memory cM3') (Configuration.memory cM4'))

  lst5 lc5
  (THS5: IdentMap.find tid (Configuration.threads cM5') = Some (lst5, lc5))
  (TIMELT: Time.lt (View.rlx (TView.cur (Local.tview lc5)) loc) ts)
:
  forall (loc0 : Loc.t) (ts0 from : Time.t) (valr valw : Const.t)
    (relr relw : option View.t) (ordr ordw : Ordering.t)
    (EVTR: ThreadEvent.is_reading e0 = Some (loc0, ts0, valr, relr, ordr))
    (EVTW: ThreadEvent.is_writing e = Some (loc0, from, ts0, valw, relw, ordw)),
  False.
Proof.
  inv PSTEP. inv PI_STEP.

  i. destruct (Loc.eq_dec loc loc0) eqn: NEQ.
  { exfalso. subst.
    destruct lst2. eapply NOWR; eauto.
    econs; [|by apply PROMISE2].
    apply rtc_pi_step_lift_except_find in STEPS_LIFT.
    s in STEPS_LIFT. des.
    rewrite <- STEPS_LIFT0. eauto.
  }

  (* assert (X:= PI_STEP). inv X. *)
  destruct (ThreadEvent.is_promising e) eqn: EQ.
  { destruct e; inv EQ; inv EVTW. }

  assert (FREE3: pf_racefree cS3').
  { eapply pf_racefree_steps; eauto.
    etrans.
    { eapply rtc_implies, (pi_steps_small_steps_fst _ STEPS); eauto. }
    etrans.
    { eapply (@pi_steps_all_pf_steps_fst (_,_) (_,_)).
      eapply rtc_implies; [by i; eapply pi_step_except_all_incl; eauto|].
      eapply (@pi_steps_lift_except_pi_steps (_,_,_) (_,_,_)), STEPS_LIFT. }
    s. eapply (@pi_steps_all_pf_steps_fst (_,_) (_,_)).
    eapply rtc_implies, STEPS3. eauto.
  }

  exploit small_step_to_program_step_reading; try apply EVTR; eauto.
  i; des. inv EVENT.

  exploit small_step_to_program_step_writing; try apply EVTW; eauto.
  i; des. inv EVENT.

  rewrite THS4 in TH. depdes TH.

  exploit FREE3.
  { reflexivity. }
  { inv WF3. ss.
    econs.
    - intro X. symmetry in X. eauto.
    - econs; [|apply STATE].
      by rewrite THS; setoid_rewrite IdentMap.Properties.F.map_o; rewrite THS3.
    - econs; [|apply STATE0].
      erewrite <- rtc_small_step_find; swap 1 2.
      + eapply (@pi_steps_small_steps_fst tid (_,_) (_,_)). eauto.
      + s. eauto.
      + eauto.
    - eauto.
  }
  i; des. 

  inv MEMLE. r in MEMWR. rewrite EVTW in MEMWR. des.
  revert PMREL. unfold View_lift_if. condtac; i.
  { des; subst.
    - congr.
    - destruct ordw; inv ORDW; inv o.
  }

  inv PSTEP0. ss. rewrite IdentMap.gss in THS5. depdes THS5.

  inv STEP; inv STEP0; inv EVTR.
  - inv LOCAL. erewrite Memory.op_get2 in GET; eauto. inv GET.
    ss. apply TimeFacts.join_lt_des in TIMELT. des. revert BC.
    rewrite ORDR. unfold View_lift. destruct relw.(View.unwrap). ss.
    unfold TimeMap_lift. condtac; [|congr]. i.
    apply TimeFacts.join_lt_des in BC. des.
    eapply Time.lt_strorder. eauto.
  - destruct lc4. eapply key_lemma_time_lt; eauto.
    inv WF4. inv WFT. eapply Local.read_step_future; eauto.
    eapply WF. eauto.
Grab Existential Variables. exact true.
Qed.

Definition pre_in_msgs A (pre: option (A * ThreadEvent.t)) msgs : Prop :=
  match pre with 
  | Some (_,pe) => 
    match ThreadEvent.is_reading pe with
    | Some (l, t, val, relr, ordr) => ~ List.In (l,t) msgs
    | _ => True
    end
  | _ => True 
  end.
Hint Unfold pre_in_msgs.

Lemma key_lemma_core
  tid tid0 l t msgs e evt3 evt4 pre4'
  cS3 cT3 cS3' cM3' cS3'x cS3'' cM3'' cS4 cT4 cS4' cM4' cM4'' M3 M4 
  lang st4' st4'' com3' com3'' com4' com4'' prm4' prm4''
  (STEP3_4: pi_step false tid0 e (cS3, cT3) (cS4, cT4))
  (STEPS3: rtc (pi_step_evt false tid) (cS3, conf_update_memory cT3 M3) (cS3', cM3'))
  (STEPS4: with_pre (pi_step false tid) (cS4, conf_update_memory cT4 M4) pre4' (cS4', cM4'))
  (STEP4: small_step false tid evt4 cM4' cM4'')
  (STEPS3': with_pre (pi_step false tid) (cS3, conf_update_memory cT3 M3) (Some (cS3'x, cM3', evt3)) (cS3'', cM3''))
  (THS3: IdentMap.find tid (Configuration.threads cM3') = Some (existT _ lang st4', Local.mk com3' prm4'))
  (THS4: IdentMap.find tid (Configuration.threads cM4') = Some (existT _ lang st4', Local.mk com4' prm4'))
  (THS3': IdentMap.find tid (Configuration.threads cM3'') = Some (existT _ lang st4'', Local.mk com3'' prm4''))
  (THS4': IdentMap.find tid (Configuration.threads cM4'') = Some (existT _ lang st4'', Local.mk com4'' prm4''))
  (WF3: pi_wf (View_lift_le l t msgs) (cS3, conf_update_memory cT3 M3))
  (WF4: pi_wf (View_lift_le l t (msg_add l e msgs)) (cS4', cM4'))
  (EVT: thread_event_eqlerel evt3 evt4)
  (NOTIN: pre_in_msgs (Some(cM4',evt4))  (msg_add l e msgs)):
  exists cS4'' pre4'',
    <<STEPS: with_pre (pi_step false tid) (cS4, conf_update_memory cT4 M4) pre4'' (cS4'', cM4'')>> /\
    <<EQPRE: Some (cM4', evt4) = pi_pre_proj pre4'' >>.
Proof.
  inv STEP4. ss. 
  rewrite THS4 in TID. symmetry in TID. depdes TID.
  rewrite IdentMap.gss in THS4'. depdes THS4'.

  inv STEP; inv STEP0.

  (* Promise step *)
  { by inv PFREE. }

  (* Silent step *)
  { esplits; [eapply with_pre_trans; [by apply STEPS4|]|].
    { econs 2; [econs 1|]. econs.
      - eauto.
      - inv WF4; ss.
        econs; [by rewrite THS; setoid_rewrite IdentMap.Properties.F.map_o; rewrite THS4|..]; eauto.
      - s. by rewrite !IdentMap.gss.
      - i. done.
    }
    eauto.
  }

  (* Read step *)
  { inv WF4.
    esplits; [eapply with_pre_trans; [by apply STEPS4|]|].
    { econs 2; [econs 1|]. econs.
      - eauto.
      - s. econs; eauto.
        { s. by rewrite THS; setoid_rewrite IdentMap.Properties.F.map_o; rewrite THS4. }
        s. econs 2. econs 2; [eauto|].
        
        inv LOCAL. s.
        eapply Local.step_read; cycle 1; eauto.
        
        inv STEPS3'.
        hexploit rtc_pi_step_future; swap 1 3; swap 2 3.
        { eapply rtc_implies, with_pre_rtc_step_union, PSTEPS. eauto. }
        { eauto. }
        { eauto. }
        s; intros [PIWF0 _]. inv PIWF0.

        ss. des. subst. inv EVT. inv PSTEP. inv STEPS. inv STEP; inv STEP0. inv LOCAL. ss.
        exploit LR0; eauto. i; des.

        hexploit RL; [by eauto|..]; cycle 1.
        { i. des. rdes CMP0; subst; eauto.
          exfalso. apply NOTIN; eauto. }

        intros tid1 PRM4. apply (NOT tid1).
        destruct (Ident.eq_dec tid1 tid) eqn: TEQ.
        { subst. inv PRM4. rewrite THS4 in TID0. inv TID0.
          econs.
          - by rewrite THS3.
          - eauto. }

        exploit rtc_pi_step_except_find.
        { eapply rtc_implies, STEPS3. eauto. } 
        s; intro EQA; des.
        exploit rtc_pi_step_except_find.
        { eapply rtc_implies, with_pre_rtc_step_union, STEPS4. eauto. }
        s; intro EQB; des.

        inv PRM4. rewrite <-EQB0 in TID0. inv STEP3_4.
        exploit small_step_promise_decr; eauto.
        i; des. rewrite EQA0 in FIND1. 
        destruct lst1. econs; eauto.
      - s. by rewrite !IdentMap.gss.
      - i. done.
    }
    eauto.
  }

  (* Write step *)
  { hexploit (@local_simul_write (View_lift_le l t (msg_add l e msgs))); try apply LOCAL.
    { inv WF4. ii. apply LR in IN. des. esplits; eauto. }
    { inv WF4.
      econs. i. destruct msg1. exploit LR; eauto. i. des.
      inv WFT. inv WF. exploit THREADS; eauto. intro X. inv X. ss.
      exploit PROMISES; eauto. i.
      destruct (Time.eq_dec to1 to2); cycle 1.
      { destruct (Configuration.memory cM4' loc0).(Cell.WF). splits.
        - eapply DISJOINT0; eauto.
        - ii. inv H. congr.
      }
      subst. exfalso. eapply NOT. econs; eauto.
    }
    intro WRITE4. des.

    assert (X:= WF4). inv X. ss.
    esplits; [eapply with_pre_trans; [by apply STEPS4|]|].
    { econs 2; [econs 1|]. econs; s.
      - econs; eauto.
      - econs; [by rewrite THS; setoid_rewrite IdentMap.Properties.F.map_o; rewrite THS4|..]; eauto.
        s. rewrite SC. econs 2. econs 3; eauto.
      - s. by rewrite !IdentMap.gss.
      - i. des. inv WRITE. inv STEPS3'. inv PSTEP. inv EVT.
        hexploit NOWR; s; eauto.
        intros X PRM2. apply X.

        hexploit rtc_pi_step_except_find.
        { eapply rtc_implies, STEPS3. eauto. } 
        s; intro EQA; des.
        hexploit rtc_pi_step_except_find.
        { eapply rtc_implies, with_pre_rtc_step_union, STEPS4. eauto. }
        s; intro EQB; des.

        inv PRM2. rewrite <-EQB0 in TID. inv STEP3_4.
        hexploit small_step_promise_decr; eauto.
        i; des. rewrite EQA0 in FIND1. 
        destruct lst1. econs; eauto.
    }
    eauto.
  }

  (* Update step *)
  { assert (X:= LOCAL1). inv X. ss.

    hexploit (@local_simul_write (View_lift_le l t (msg_add l e msgs))); try apply LOCAL2. 
    { inv WF4. ii. apply LR in IN. des. esplits; eauto. }
    { inv WF4.
      econs. i. destruct msg1. exploit LR; eauto. i. des.
      inv WFT. inv WF. exploit THREADS; eauto. intro X. inv X. ss.
      exploit PROMISES; eauto. i.
      destruct (Time.eq_dec to1 to2); cycle 1.
      { destruct (Configuration.memory cM4' loc0).(Cell.WF). splits.
        - eapply DISJOINT0; eauto.
        - ii. inv H. congr.
      }
      subst. exfalso. eapply NOT. econs; eauto.
    }
    intro WRITE4. des.

    inv WF4. 
    esplits; [eapply with_pre_trans; [by apply STEPS4|]|].
    { econs 2; [econs 1|]. econs.
      { eauto. }
      { s. econs; eauto.
        { s. by rewrite THS; setoid_rewrite IdentMap.Properties.F.map_o; rewrite THS4. }
        s. econs 2. econs 4; [eauto|..].
        { inv LOCAL1. s.
          eapply Local.step_read; cycle 1; eauto.
          
          inv STEPS3'.
          hexploit rtc_pi_step_future; swap 1 3; swap 2 3.
          { eapply rtc_implies, with_pre_rtc_step_union, PSTEPS. eauto. }
          { eauto. }
          { eauto. }
          s; intros [PIWF0 _]. inv PIWF0.

          ss. des. subst. inv EVT. inv PSTEP. inv STEPS. inv STEP; inv STEP0. inv LOCAL1. ss.
          exploit LR0; eauto. i; des.

          hexploit RL; [by eauto|..]; cycle 1.
          { i. des. rdes CMP0; subst; eauto.
            exfalso. apply NOTIN; eauto. }

          intros tid1 PRM4. apply (NOT tid1).
          destruct (Ident.eq_dec tid1 tid) eqn: TEQ.
          { subst. inv PRM4. rewrite THS4 in TID0. inv TID0.
            econs.
            - by rewrite THS3.
            - eauto. }

          exploit rtc_pi_step_except_find.
          { eapply rtc_implies, STEPS3. eauto. } 
          s; intro EQA; des.
          exploit rtc_pi_step_except_find.
          { eapply rtc_implies, with_pre_rtc_step_union, STEPS4. eauto. }
          s; intro EQB; des.

          inv PRM4. rewrite <-EQB0 in TID0. inv STEP3_4.
          exploit small_step_promise_decr; eauto.
          i; des. rewrite EQA0 in FIND1. 
          destruct lst1. econs; eauto.
        }
        { s. rewrite SC. eauto. }
      }
      { s. by rewrite !IdentMap.gss. }
      { s. i. des. inv WRITE. inv STEPS3'. inv PSTEP. inv EVT.
        hexploit NOWR; s; eauto.
        intros X PRM'. apply X.

        hexploit rtc_pi_step_except_find.
        { eapply rtc_implies, STEPS3. eauto. } 
        s; intro EQA; des.
        hexploit rtc_pi_step_except_find.
        { eapply rtc_implies, with_pre_rtc_step_union, STEPS4. eauto. }
        s; intro EQB; des.

        inv PRM'. rewrite <-EQB0 in TID. inv STEP3_4.
        hexploit small_step_promise_decr; eauto.
        i; des. rewrite EQA0 in FIND1. 
        destruct lst1. econs; eauto.
      }
    }
    eauto.
  }

  (* Fence step *)
  { assert (X:= WF4). inv X. ss.
    esplits; [eapply with_pre_trans; [by apply STEPS4|]|].
    { econs 2; [econs 1|]. econs.
      - econs; eauto.
      - econs; [by rewrite THS; setoid_rewrite IdentMap.Properties.F.map_o; rewrite THS4|..]; eauto.
        econs 2. econs 5; eauto.
        eapply local_simul_fence.
        s. rewrite SC. eauto.
      - s. by rewrite !IdentMap.gss.
      - done.
    }
    eauto.
  }

  (* Syscall step *)
  { assert (X:= WF4). inv X. ss.
    esplits; [eapply with_pre_trans; [by apply STEPS4|]|].
    { econs 2; [econs 1|]. econs.
      - econs; eauto.
      - econs; [by rewrite THS; setoid_rewrite IdentMap.Properties.F.map_o; rewrite THS4|..]; eauto.
        econs 2. econs 6; eauto.
        eapply local_simul_fence.
        s. rewrite SC. eauto.
      - s. by rewrite !IdentMap.gss.
      - done.
    }
    eauto.
  }
Qed.

Lemma key_lemma
      cS1 cT1 cS2 cT2 tid
      (PI_CONSISTENT : pi_consistent (cS1, cT1))
      (WF : pi_wf loctmeq (cS1, cT1))
      (RACEFREE : pf_racefree cS1)
      (STEPS : rtc (pi_step_evt true tid) (cS1, cT1) (cS2, cT2))
      loc ts lst2 lc2 from2 msg2 
      (THREAD2 : IdentMap.find tid (Configuration.threads cT2) = Some (lst2, lc2))
      (PROMISE2 : Memory.get loc ts (Local.promises lc2) = Some (from2, msg2))
      cSTM3
      (STEPS_LIFT : rtc (pi_step_lift_except loc ts tid) (cS2, cT2, cT2.(Configuration.memory)) cSTM3)
      (PRCONS: forall tid0, promise_consistent_th tid0 cSTM3.(fst).(snd)):
  exists msgs,
  <<EQMEM: mem_eqrel (View_lift_le loc ts msgs) cSTM3.(fst).(snd).(Configuration.memory) cSTM3.(snd)>> /\
  <<IN: Memory.get loc ts cSTM3.(fst).(snd).(Configuration.memory) <> None>> /\
  <<MSGS: forall loc' to' (IN: List.In (loc', to') msgs),
          (exists from msg, fulfilled cSTM3.(fst).(snd) loc' from to' msg) /\
          loc' <> loc /\
          to' <> Time.bot>> /\
  <<MAIN:
    forall cM4 pre
      (PI_STEPS : with_pre (small_step false tid) (conf_update_memory cSTM3.(fst).(snd) cSTM3.(snd)) pre cM4)
      (PRCONSIS: forall tid0, promise_consistent_th tid0 cM4)
      lst4 lc4
      (THREAD4 : IdentMap.find tid (Configuration.threads cM4) = Some (lst4, lc4))
      (TIMELT: Time.lt (lc4.(Local.tview).(TView.cur).(View.rlx) loc) ts),
    <<NOMSG: pre_in_msgs pre msgs>> /\
    exists cS4 pre',
    <<STEPS: with_pre (pi_step false tid) (cSTM3.(fst).(fst), conf_update_memory cSTM3.(fst).(snd) cSTM3.(snd)) pre' (cS4, cM4)>>
    /\
    <<EQPRE: pre = pi_pre_proj pre'>> >>.
Proof.
  assert (WF2: pi_wf loctmeq (cS2,cT2)).
  { eapply rtc_pi_step_future; eauto.
    eapply rtc_implies, STEPS; eauto. }
  move WF2 after STEPS_LIFT.

  revert_until STEPS_LIFT.
  apply Operators_Properties.clos_rt_rt1n_iff, 
        Operators_Properties.clos_rt_rtn1_iff in STEPS_LIFT.
  induction STEPS_LIFT.
  { exists []. splits.
    - s. split; ii; esplits; eauto.
    - s. inv WF2. inv WFT. inv WF0.
      destruct lst2. exploit THREADS; eauto.
      intro X. inv X. apply PROMISES in PROMISE2. rewrite PROMISE2. done.
    - done.
    - s. i. split. 
      { unfold pre_in_msgs in *. destruct pre; eauto. destruct p; eauto. 
        destruct (ThreadEvent.is_reading t0); repeat destruct p; eauto. }
      destruct cT2. unfold conf_update_memory in *. ss.
      eapply with_pre_implies in PI_STEPS.
      + exploit pi_consistent_rtc_small_step_pi; try eapply WF; eauto.
      + i. inv STEP. eauto. 
  }
  i.

  apply Operators_Properties.clos_rt_rtn1_iff, 
        Operators_Properties.clos_rt_rt1n_iff in STEPS_LIFT.

  destruct y as [[cS3 cT3] M3].
  destruct z as [[cS4 cT4] M4].
  rename H into PSTEP. ss.

  assert (WF3: pi_wf loctmeq (cS3, cT3)).
  { eapply rtc_pi_step_future; eauto.
    eapply pi_steps_lift_except_pi_steps in STEPS_LIFT.
    eapply rtc_implies, STEPS_LIFT.
    i. inv PR. eauto. }

  assert (WF4: pi_wf loctmeq (cS4, cT4)).
  { inv PSTEP. inv USTEP. eapply pi_step_future; eauto. }

  hexploit IHSTEPS_LIFT.
  { inv PSTEP. inv USTEP. inv PI_STEP. inv WF3.
    eapply promise_consistent_th_small_step_backward; eauto. }
  i. clear IHSTEPS_LIFT. i; des.

  inv PSTEP. rename USTEP into PSTEP.
  exploit pi_step_lift_except_future; try apply PSTEP; eauto.
  i; des. clear MEMFUT TIMELE.
  esplits; eauto.

  s. i. assert (X := PSTEP). inv X. rename cM4 into cM4'.

  hexploit rtc_pi_step_lift_except_find; eauto. 
  s; intro THEQA; des.

  hexploit rtc_pi_step_lift_except_find.
  { econs 2; [|reflexivity]. eauto. }
  s; intro THEQB; des.

  rewrite <-THEQB0,<-THEQA0, THREAD2 in FIND. inv FIND.

  cut((pre_in_msgs pre (msg_add loc e msgs)) /\
      (exists cS3' cM3' lst3' com3' com4' prm3',
       <<STEPS3: rtc (pi_step_evt false tid) (cS3, conf_update_memory cT3 M3) (cS3',cM3')>> /\
       <<PRCONSIS3: forall tid0, promise_consistent_th tid0 cM3'>> /\
       <<MEMLE: mem_eqlerel_lift loc ts prm3' k e cM3'.(Configuration.memory) cM4'.(Configuration.memory)>> /\
       <<SCLE: TimeMap.le cM3'.(Configuration.sc) cM4'.(Configuration.sc)>> /\
       <<THS3: IdentMap.find tid cM3'.(Configuration.threads) = Some (lst3', Local.mk com3' prm3') >> /\
       <<THS4: IdentMap.find tid cM4'.(Configuration.threads) = Some (lst3', Local.mk com4' prm3') >> /\
       <<COMLE: TView.le com3' com4' >>) /\
       (exists cS4' pre',
       <<STEPS4: with_pre (pi_step false tid) (cS4, conf_update_memory cT4 M4) pre' (cS4',cM4')>>/\
       <<EQPRE: pre = pi_pre_proj pre'>>)).
  { i; des. eauto. }

  move cM4' at bottom. move lst4 at bottom. move lc4 at bottom. move TIMELT at bottom.
  revert_until PI_STEPS.
  induction PI_STEPS; i.
  { split; eauto. 
    destruct lc4 as [com4 prm4]. subst. ss.
    esplits.
    { eauto. }
    { i. inv PI_STEP. eapply promise_consistent_th_small_step_backward in STEPT; eauto. 
      inv WF3; eauto. } 
    { econs; eauto.
      by split; ii; esplits; eauto; reflexivity. }
    { s. inv PI_STEP. inv STEPT. ss.
      inv WF3. inv WFT. inv WF0. ss.
      exploit THREADS; eauto. i.
      exploit Thread.step_future; eauto. s. i. des. auto.
    }
    { s. rewrite THEQA0, THEQB0, THREAD4 in THREAD2. inv THREAD2. rewrite THEQB0. eauto. }
    { s. rewrite THEQA0, THEQB0, THREAD4 in THREAD2. inv THREAD2. eauto. }
    { reflexivity. }
    { eauto. }
    { eauto. }
  }

  rename ms into cM4', es into cM5'.

  assert (STEP2 := PSTEP0). inv PSTEP0. ss.
  rewrite IdentMap.gss in THREAD4. depdes THREAD4.

  assert (MGET: Memory.get loc ts (Configuration.memory cT2) <> None).
  { inv WF2. inv WFT. inv WF0. destruct lst.
    hexploit THREADS; eauto.
    intro X. inv X. apply PROMISES in PROMISE2. rewrite PROMISE2. done. }

  exploit conf_update_memory_wf; try apply EQMEM; eauto.
  intro WF3'.

  exploit conf_update_memory_wf; try apply EQMEM0; eauto.
  intro WF4'.

  hexploit rtc_small_step_future; swap 1 2.
  { eapply rtc_implies, with_pre_rtc_step_union, PI_STEPS. eauto. }
  { inv WF4'. eauto. }
  intros [WF4'' _].
  
  exploit IHPI_STEPS; eauto using promise_consistent_th_small_step.
  { eapply TimeFacts.le_lt_lt; eauto.
    inv WF4''. exploit thread_step_tview_le; eauto. 
    { eapply WF0. eauto. }
    s. i. apply x0.
  }
  intro PRE. des. subst. clear IHPI_STEPS.
  rewrite THS4 in TID0. depdes TID0.

  exploit rtc_pi_step_future; swap 1 3; swap 2 3.
  { eapply rtc_implies, STEPS3. eauto. }
  { eauto. }
  { eauto. }
  intros [SEMI_WF3 _]. des.

  exploit rtc_pi_step_future; swap 1 3; swap 2 3.
  { eapply rtc_implies, with_pre_rtc_step_union, STEPS4. eauto. }
  { eauto. }
  { eauto. }
  intros [SEMI_WF4 _]. des.

  exploit (@lift_step _ (Thread.mk _ st1 (Local.mk com3' prm3') cM3'.(Configuration.sc) cM3'.(Configuration.memory))); [apply STEP|..]; eauto.
  { inv SEMI_WF3. inv WFT. inv WF0. s. eapply THREADS. eauto. }
  { inv SEMI_WF4. inv WFT. inv WF0. s. eapply THREADS. eauto. }
  { s. inv SEMI_WF3. inv WFT. eauto. }
  { s. inv SEMI_WF4. inv WFT. eauto. }
  { s. inv SEMI_WF3. inv WFT. eauto. }
  { s. inv SEMI_WF4. inv WFT. eauto. }
  i; des; ss.

  (* Read the event "e" *)  
  { exfalso. eapply key_lemma_rw_race; eauto.
    s. rewrite IdentMap.gss. eauto. }

  (* Simulation exists *)  
  assert (NOPRMEVT: ThreadEvent.is_promising eS = None).
  { destruct e0; inv PFREE; inv EVT; eauto. }

  subst. destruct thS2 as [stx lcx scx mx]. ss. subst.

  exploit pi_steps_small_steps_snd; try apply STEPS3.
  intros STEPS3'.
  eapply rtc_step_union_with_pre in STEPS3'. des.

  exploit (@MAIN (Configuration.mk (IdentMap.add tid (existT _ _ stx, lcx) cM3'.(Configuration.threads)) scx mx)); s; swap 1 3; swap 2 3.
  { rewrite IdentMap.gss. eauto. }
  { eapply with_pre_trans.
    - apply STEPS3'.
    - s; eauto. }
  { i. destruct (Ident.eq_dec tid1 tid) eqn: TEQ; cycle 1.
    { ii. s in THREAD. rewrite IdentMap.gso in THREAD; eauto.
      eapply (PRCONSIS3 tid1); eauto. }

    subst; ii. r in PRCONSIS. ss. 
    rewrite IdentMap.gss in THREAD. 
    specialize (PRCONSIS tid). rewrite IdentMap.gss in PRCONSIS.
    inv THREAD. rewrite PRM in PROMISE. 
    exploit PRCONSIS; eauto.
    intro LT. move COM at bottom.
    eapply TimeFacts.le_lt_lt; eauto. apply COM.
  }
  { move TIMELT at bottom. move COM at bottom.
    eapply TimeFacts.le_lt_lt; eauto. apply COM.
  }
  i; des. ss. clear MAIN.
  destruct pre'0; [|done].
  destruct p as [[cS3'x ?] ?]. symmetry in EQPRE. inv EQPRE.

  destruct lcx as [comx prmx].
  destruct lc4 as [com4 prm4].
  ss. subst.

  apply strengthen.
  split. 
  { destruct (ThreadEvent.is_reading e0) as [[[[[]]]]|] eqn: EVTR; eauto.
    unfold msg_add.
    assert (NIN: ~ List.In (t,t0) msgs).
    { destruct eS; inv EVT; inv EVTR; eauto. }

    destruct (ThreadEvent.is_writing e) as [[[[[[]]]]]|] eqn: EVTW; eauto.
    destruct (loc_ord_dec t3 t7 loc) eqn: LOD; eauto.

    apply List.not_in_cons; split; eauto.
    intro X; inv X. 
    eapply key_lemma_rw_race; eauto.
    - s. rewrite IdentMap.gss. eauto. 
    - eauto.
  }

  intro NOTIN.
  split.
  { esplits; [by eapply with_pre_rtc_step_union, STEPS0|..]; eauto.
    { i. destruct (Ident.eq_dec tid1 tid) eqn: TEQ.
      - subst. ii. s in THREAD. rewrite IdentMap.gss in THREAD. depdes THREAD.
        s. s in PROMISE. 
        exploit (PRCONSIS tid). 
        { s. rewrite IdentMap.gss. eauto. }
        { eauto. }
        s; intro TIMELT'.
        eapply TimeFacts.le_lt_lt, TIMELT'. 
        apply COM.
      - specialize (PRCONSIS3 tid1).
        ii. s in THREAD. rewrite IdentMap.gso in THREAD; eauto.
        eapply PRCONSIS3; eauto.
    }
    { s. rewrite IdentMap.gss. eauto. }
    { s. rewrite IdentMap.gss. eauto. }
  }

  eapply key_lemma_core; eauto.
  { s. rewrite IdentMap.gss. eauto. }
  { s. rewrite IdentMap.gss. eauto. }
Qed.

Theorem pi_consistent_pi_step_pi_consistent
      cST1 cST2 tid
      (PI_CONSISTENT: pi_consistent cST1)
      (CONSISTENT: Configuration.consistent cST1.(snd))
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (WF: pi_wf loctmeq cST1)
      (STEP: rtc (pi_step_evt true tid) cST1 cST2)
      (CONSISTENT2: Configuration.consistent cST2.(snd)):
  pi_consistent cST2.
Proof.
  destruct cST1 as [cS1 cT1], cST2 as [cS2 cT2].
  econs. i. 

  exploit rtc_pi_step_future; [eauto|..].
  { reflexivity. }
  { eapply rtc_implies, STEP. i. inv PR. eauto. }
  i; des. clear FUTURES FUTURET.

  destruct (Ident.eq_dec tid0 tid); cycle 1.
  { exploit (@rtc_pi_step_remove_promises tid); try apply STEP; try apply STEPS; eauto. 
    intro STEPS'. des. ss.

    assert (TEQA:= rtc_pi_step_except_find STEPS). des. ss.
    assert (TEQB:= rtc_pi_step_except_find STEPS'). des. ss.
    hexploit rtc_pi_step_except_find.
    { eapply rtc_implies, STEP. i. eauto. } intro TEQC; des; ss.
    rewrite <-TEQA0,<-TEQC0,TEQB0 in THREAD.

    inv PI_CONSISTENT. 
    exploit CONSIS; cycle 1; eauto.
  }
  subst. rename cS0 into cS3, cT0 into cT3, lst2 into lst3, lc2 into lc3.

  exploit (pi_step_lifting loc ts STEPS).
  { ss. rewrite THREAD. done. }
  { eauto. }
  intro STEPS_LIFT; des.
  rename M2 into M3. ss.

  destruct (IdentMap.find tid (Configuration.threads cT2)) eqn: TH; cycle 1.
  { apply Operators_Properties.clos_rt_rt1n_iff in STEP.
    apply Operators_Properties.clos_rt_rtn1_iff in STEP.
    inv STEP.
    - inv PI_CONSISTENT. exploit CONSIS; eauto.
    - inv H. inv USTEP. inv STEPT. ss. by rewrite IdentMap.gss in TH.
  }
  destruct p as [[lang2 st2] lc2].

  exploit rtc_pi_step_lift_except_find; eauto.
  s; intro EQ; des. clear EQ.
  assert (X:= EQ0); rewrite THREAD, TH in X. depdes X.

  exploit rtc_pi_step_lift_except_future; eauto.
  { inv WF2. inv WFT. inv WF0. edestruct THREADS; eauto.
    apply PROMISES in PROMISE. rewrite PROMISE. done. }
  i. des. ss. rename WF0 into WF3.

  rewrite EQ0 in TH.
  exploit consistent_can_fulfill_promises_future; eauto.
  { eapply CONSISTENT2.
    rewrite EQ0. rewrite TH. eauto. }
  intro X. inv X. ss.

  exploit FULFILL; eauto.
  i; des. inv FULFILL1. clear FULFILL.

  hexploit rtc_small_step_future; swap 1 2.
  { eapply rtc_implies, STEPS0. eauto. }
  { inv WF3. eauto. }
  intros [WF4 _].

  hexploit rtc_small_step_future; swap 1 2.
  { econs 2; [|reflexivity]. eauto. }
  { eauto. }
  intros [WF5 _].

  hexploit rtc_small_step_future; swap 1 2.
  { eapply rtc_implies, STEPS1. eauto. }
  { eauto. }
  intros [WF6 _].

  rewrite <-EQ0 in TH.
  exploit key_lemma; eauto.
  s; i; des.
  
  exploit rtc_step_union_with_pre; [by apply STEPS0|].
  intro STEPS'. des.

  exploit (MAIN c0); eauto.
  { eapply rtc_promise_consistent_th_small_step_forward.
    { apply STEPS0. }
    { ii. eapply PRCONSIS; eauto. }
    { apply can_fulfill_promises_promise_consistent in FULFILL2; eauto.
      eapply promise_consistent_th_rtc_small_step, FULFILL2; eauto.
      etrans; [|apply STEPS1].
      econs 2; [|reflexivity]; eauto. }
    { inv WF3; eauto. }
  }
  { eapply small_step_write_lt; eauto. }
  s; i; des.
  
  exploit small_step_to_program_step_writing; eauto.
  i; des.

  apply with_pre_rtc_step_union in STEPS2.
  exists cS4; esplits; eauto using (pi_steps_small_steps_fst false STEPS2).

  exploit rtc_pi_step_future; [apply WF3|..].
  { reflexivity. }
  { eapply rtc_implies, STEPS2. eauto. }
  i; des.

  inv WF0. inv EVENT0.
  econs; eauto.
  by rewrite THS; setoid_rewrite IdentMap.Properties.F.map_o; rewrite TH0.
Qed.
