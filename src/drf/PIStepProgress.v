Require Import Omega.
Require Import RelationClasses.

Require Import sflib.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Loc.

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

Require Import MemoryRel.
Require Import SmallStep.
Require Import Fulfilled.
Require Import ReorderPromise.
Require Import Race.
Require Import PromiseConsistent.
Require Import PIStep.

Set Implicit Arguments.

Inductive is_reading_writing_promise_except tid c : Prop :=
| is_reading_promise_except_intro
    e lang st1 st2 loc val ord tid' to'
    (ST1: option_map fst (IdentMap.find tid c.(Configuration.threads)) = Some (existT _ lang st1))
    (NOWR: lang.(Language.step) e st1 st2)
    (RW: ProgramEvent.is_reading e = Some(loc, val, ord) \/ ProgramEvent.is_writing e = Some(loc, val, ord))
    (NEQ: tid' <> tid)
    (PROM: Threads.is_promised tid' loc to' c.(Configuration.threads))
.

Lemma pi_consistent_lang_step_pi_rw
      tid cST1 cST2
      (WF: pi_wf loctmeq cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt true tid) cST1 cST2)
      (PRCONS: forall tid0, promise_consistent_th tid0 cST2.(snd)):
  ~ is_reading_writing_promise_except tid cST2.(snd).
Proof.
  ii. inv H. inv PROM.
  inv PI_CONSISTENT. ss.
  guardH RW. destruct cST2 as [cS2 cT2].

  eapply rtc_implies in PI_STEPS; [|eapply pi_step_evt_to_true].
  exploit (@rtc_pi_step_remove_promises tid); eauto.

  intro PI_STEPS'. des. ss.
  exploit CONSIS.
  { eauto. }
  { apply pi_steps_small_steps_snd in PI_STEPS. ss.
    eapply rtc_small_step_find in PI_STEPS; eauto.
    assert (EQ:= rtc_pi_step_except_find PI_STEPS'); des; ss.
    rewrite <-EQ0, PI_STEPS. eauto. }
  { eauto. }
  { eauto. }

  clear CONSIS. i. des.
  exploit (PI_RACEFREE cS3 ord ord0).
  { etrans. 
    - eapply rtc_implies; [by i; econs; eapply PR|].
      by eapply pi_steps_small_steps_fst in PI_STEPS; eauto.
    - eapply rtc_implies, STEPS. by econs; eauto.
  }
  { hexploit rtc_pi_step_future; [| |eapply rtc_implies; [eapply (@pi_step_evt_all_incl true)|]|]; eauto.
    i; des. clear FUTURES FUTURET.
    assert (LC1: exists lc1', IdentMap.find tid (Configuration.threads cS3) = Some (existT _ lang st1, lc1')).
    { erewrite <-rtc_small_step_find; eauto.
      inv WF2. rewrite THS. unfold remove_promise.
      setoid_rewrite IdentMap.Properties.F.map_o. 
      destruct (IdentMap.find tid (Configuration.threads cT2)) as [[]|]; [|done].
      inv ST1. s. eauto.
    }
    des.
    econs; cycle 1.
    - econs; [by eauto|]. rdes RW; eauto.
    - eauto.
    - rdes RW; eauto.
    - eauto.
  }
  i. des. destruct ord0; inv ORD; inv ORDW.
Qed.

Lemma pi_consistent_small_step_pi_rw
      e tid cST1 cST2 cT3 withprm
      (WF: pi_wf loctmeq cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt true tid) cST1 cST2)
      (STEP: small_step withprm tid e cST2.(snd) cT3)
      (PRCONS: forall tid0, promise_consistent_th tid0 cT3):
  forall loc from to val rel ord tid' ts
    (NEQ: tid <> tid')
    (RW: ThreadEvent.is_reading e = Some (loc, to, val, rel, ord) \/
         ThreadEvent.is_writing e = Some (loc, from, to, val, rel, ord)),
  ~Threads.is_promised tid' loc ts cST2.(snd).(Configuration.threads).
Proof.
  ii. guardH RW.
  eapply pi_consistent_lang_step_pi_rw; eauto.
  - hexploit rtc_pi_step_future; [| |eapply rtc_implies; [eapply (@pi_step_evt_all_incl true)|]|]; eauto.
    i; des. clear FUTURES FUTURET. inv WF2.
    eauto using promise_consistent_th_small_step_backward.
  - inv STEP. inv STEP0; inv STEP; [by rdes RW; inv RW|].
    econs; eauto.
    + by rewrite TID.
    + destruct e0; rdes RW; inv RW; s; eauto.
Qed.

Lemma pi_consistent_small_step_pi
      e tid cST1 cST2 cT3 withprm
      (WF: pi_wf loctmeq cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt true tid) cST1 cST2)
      (STEP: small_step withprm tid e cST2.(snd) cT3)
      (FULFILL: promise_consistent_th tid cT3)
      (PRCONSIS: forall tid0, promise_consistent_th tid0 cST1.(snd)):
  exists cS3, pi_step withprm tid e cST2 (cS3,cT3).
Proof.
  destruct cST1 as [cS1 cT1], cST2 as [cS2 cT2].
  exploit rtc_pi_step_future; [eauto|reflexivity|..].
  { eapply rtc_implies, PI_STEPS. eauto. }
  intros [WF2 _].

  hexploit (promise_consistent_th_rtc_small_step).
  { econs 2; [|reflexivity]. eauto. }
  { inv WF2. eauto. }
  { eauto. }
  intro PCONSIS.

  assert (PRCONSIS3: forall tid0, promise_consistent_th tid0 cT3).
  { i. ss. eapply promise_consistent_th_small_step_forward; eauto; cycle 1.
    { inv WF2; eauto. }
    i. hexploit rtc_promise_consistent_th_small_step_forward.
    { eapply pi_steps_small_steps_snd in PI_STEPS. eauto. }
    { eauto. }
    { eapply promise_consistent_th_small_step; eauto.
      inv WF2; eauto. }
    { inv WF. eauto. }
    eauto.
  }

  assert (RW:= pi_consistent_small_step_pi_rw WF PI_CONSISTENT PI_RACEFREE PI_STEPS STEP PRCONSIS3).

  exploit rtc_pi_step_future; [| |eapply rtc_implies; [eapply pi_step_evt_all_incl|]|]; eauto.
  i; des. destruct cS2. inv WF2. ss. assert (MSTEP:=STEP). inv STEP. inv STEP0.
  - eexists. econs; [by eauto|by inv STEP; s; eauto|..].
    + inv STEP. ss. rewrite IdentMap.gss.
      setoid_rewrite IdentMap.Properties.F.map_o.
      by rewrite TID.
    + i. des; eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); s; try apply MSTEP; try apply PI_CONSISTENT; eauto.
  - inv STEP. inv LOCAL.
    { eexists. econs.
      - eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID.
        + econs 2. econs; [|econs 1]; eauto.
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. des; eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); s; try apply MSTEP; try apply PI_CONSISTENT; eauto.
    }
    { inv LOCAL0. eexists. econs.
      - econs; eauto. econs 2. econs; [|econs 2]; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID.
        + econs 2. econs; [|econs 2]; eauto.
          econs; eauto.
          s. hexploit RL; [| |by intro X; des; unfold loctmeq in *; subst; apply X]; eauto.
          i. destruct (Ident.eq_dec tid tid0) eqn: EQ; cycle 1.
          { eapply RW; s; eauto. }
          subst. intro PROMISED. inv PROMISED.
          ss. rewrite TID0 in TID. depdes TID.
          rdes FULFILL. ss. rewrite IdentMap.gss in FULFILL.
          exploit FULFILL; s; eauto.
          intro LT. ss.
          inv READABLE; eauto.
          apply TimeFacts.join_lt_des in LT. des.
          apply TimeFacts.join_lt_des in AC. des.
          revert BC0. unfold View.singleton_ur_if. condtac; ss.
          * unfold TimeMap.singleton, LocFun.add. condtac; [|congr]. i.
            eapply Time.lt_strorder. eauto.
          * unfold TimeMap.singleton, LocFun.add. condtac; [|congr]. i.
            eapply Time.lt_strorder. eauto.
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. des; eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); s; try apply MSTEP; try apply PI_CONSISTENT; eauto.
    }
    { destruct lc1, lc2. exploit local_simul_write; [| |by eapply LOCAL0|..].
      { instantiate (1:= memory). ii. eapply LR in IN.
        des; eauto. }
      { econs. i. destruct msg1. exploit LR; eauto. i. des.
        inv WFT. inv WF1. exploit THREADS; eauto. i. inv x. ss.
        exploit PROMISES; eauto. i.
        destruct (Time.eq_dec to1 to2); cycle 1.
        { destruct (Configuration.memory cT2 loc0).(Cell.WF). splits.
          - eapply DISJOINT0; eauto.
          - ii. inv H. congr.
        }
        subst. exfalso. eapply NOT. econs; eauto.
      }
      intro WRITE; des.
      eexists; econs. 
      - eauto.
      - s. econs; s; eauto.
        + setoid_rewrite IdentMap.Properties.F.map_o. by rewrite TID.
        + rewrite Bool.orb_true_r. econs 2. econs; [|econs 3]; eauto.
      - s. by rewrite !IdentMap.gss.
      - i. des; eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); s; try apply MSTEP; try apply PI_CONSISTENT; eauto.
    }
    { destruct lc2, lc3. exploit local_simul_write; [| |by eapply LOCAL2|..].
      { instantiate (1:= memory). ii. eapply LR in IN.
        des; eauto. }
      { inv LOCAL1. ss.
        econs. i. destruct msg1. exploit LR; eauto. i. des.
        inv WFT. inv WF1. exploit THREADS; eauto. i. inv x.
        exploit PROMISES; eauto. i.
        destruct (Time.eq_dec to1 to2); cycle 1.
        { destruct (Configuration.memory cT2 loc0).(Cell.WF). splits.
          - eapply DISJOINT0; eauto.
          - ii. inv H. congr.
        }
        subst. exfalso. eapply NOT. econs; eauto.
      }
      intro WRITE; des.

      inv LOCAL1. eexists. econs.
      - econs; eauto. econs 2. econs; [|econs 4]; eauto; econs; eauto.
      - s. econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID.
        + econs 2. econs; [|econs 4]; [by eauto|..].
          { 
            econs; eauto.
            s. hexploit RL; [| |by intro X; des; unfold loctmeq in *; subst; apply X]; eauto.
            i. destruct (Ident.eq_dec tid tid0) eqn: EQ; cycle 1.
            { eapply RW; s; eauto. }
            subst. intro PROMISED. inv PROMISED.
            ss. rewrite TID0 in TID. depdes TID.

            r in FULFILL. hexploit FULFILL.
            { s. rewrite IdentMap.gss. eauto. }
            clear FULFILL. intro FULFILL.

            eapply write_step_promise_consistent in FULFILL; eauto.
            exploit FULFILL; s; eauto.
            intro LT. ss.
            inv READABLE; eauto.
            apply TimeFacts.join_lt_des in LT. des.
            apply TimeFacts.join_lt_des in AC. des.
            revert BC0. unfold View.singleton_ur_if. condtac; ss.
            * unfold TimeMap.singleton, LocFun.add. condtac; [|congr]. i.
              eapply Time.lt_strorder. eauto.
            * unfold TimeMap.singleton, LocFun.add. condtac; [|congr]. i.
              eapply Time.lt_strorder. eauto.
          }
          { eauto. }
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. des; eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); s; try apply MSTEP; try apply PI_CONSISTENT; eauto.
    }
    { inv LOCAL0. eexists. econs.
      - econs; eauto. econs 2. econs; [|econs 5]; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID.
        + econs 2. econs; [|econs 5]; eauto.
          econs; eauto.
          s. i. apply Memory.bot_nonsynch.
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. des; eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); s; try apply MSTEP; try apply PI_CONSISTENT; eauto.
    }
    { inv LOCAL0. eexists. econs.
      - econs; eauto. econs 2. econs; [|econs 6]; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID.
        + econs 2. econs; [|econs 6]; eauto.
          econs; eauto.
          s. i. apply Memory.bot_nonsynch.
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. des; eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); s; try apply MSTEP; try apply PI_CONSISTENT; eauto.
    }
Grab Existential Variables.
  { exact Time.bot. }
  { exact xH. }
  { exact xH. }
  { exact xH. }
  { exact xH. }
  { exact xH. }
  { exact xH. }
  { exact xH. }
  { exact xH. }
  { exact true. }
Qed.

Lemma small_step_evt_to_true
      withprm tid cST1 cST2
      (STEP: small_step_evt withprm tid cST1 cST2):
  small_step_evt true tid cST1 cST2.
Proof.
  destruct withprm; eauto.
  inv STEP. inv USTEP. 
  econs. econs; eauto.
Qed.

Lemma pi_consistent_rtc_small_step_pi
      tid cST1 cST2 withprm
      (WF: pi_wf loctmeq cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt true tid) cST1 cST2)
      cT3 pre
      (STEP: with_pre (small_step withprm tid) cST2.(snd) pre cT3)
      (FULFILL: forall tid0, promise_consistent_th tid0 cT3):
  exists cS3 pre', with_pre (pi_step withprm tid) cST2 pre' (cS3,cT3) /\ 
                   pre = pi_pre_proj pre'.
Proof.
  destruct cST2 as [cS2 cT2].
  revert_until STEP. induction STEP.
  { s; i. eauto. }
  s; i.

  exploit IHSTEP; s; eauto.
  { eapply promise_consistent_th_small_step_backward; eauto.
    exploit rtc_pi_step_future.
    { eauto. }
    { reflexivity. }
    { eapply rtc_implies, PI_STEPS. eauto. }
    intros [WF2 _]. inv WF2.

    exploit with_pre_rtc_union; eauto.
    i. exploit rtc_small_step_future.
    { eauto. }
    { eapply rtc_implies, x0. eauto. }
    i; des; eauto.
  }

  intro STEPS. des. ss.
  eapply (@pi_consistent_small_step_pi _ _ _ (_,_)) in PSTEP; eauto; cycle 1.
  { etrans; eauto. subst. 
    eapply rtc_implies; [eapply pi_step_evt_to_true|].
    eapply with_pre_rtc_union; eauto. }
  { eapply (@rtc_promise_consistent_th_small_step_backward true); try apply FULFILL. 
    - etrans.
      + eapply pi_steps_small_steps_snd. eauto.
      + eapply rtc_implies; [eapply small_step_evt_to_true|].
        eapply with_pre_rtc_union; eauto.
    - inv WF. eauto.
  }
  des; esplits; eauto.
Qed.

Lemma pi_consistent_rtc_ftau_small_step_pi
      tid cST1 cST2 withprm
      (WF: pi_wf loctmeq cST1)
      (CONSISTENT: Configuration.consistent (snd cST1))
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt true tid) cST1 cST2)
      cT3 pre
      (STEP: with_pre (ftau (small_step withprm tid)) cST2.(snd) pre cT3)
      (FULFILL: forall tid0, promise_consistent_th tid0 cT3):
  exists cS3 pre', with_pre (ftau (pi_step withprm tid)) cST2 pre' (cS3,cT3) /\
                   pre = pi_pre_proj pre'.
Proof.
  destruct cST2 as [cS2 cT2].
  revert_until STEP. induction STEP.
  { s; i. eauto. }
  s; i. inv PSTEP.

  eapply with_pre_implies in STEP; cycle 1.
  { i. inv STEP0. eauto. }

  assert (WF2 : Configuration.wf ms).
  { exploit rtc_pi_step_future.
    { eauto. }
    { reflexivity. }
    { eapply rtc_implies, PI_STEPS. eauto. }
    intros [WF2 _]. inv WF2.

    exploit with_pre_rtc_union; eauto.
    i. exploit rtc_small_step_future.
    { eauto. }
    { eapply rtc_implies, x0. eauto. }
    i; des; eauto.
  }

  exploit IHSTEP; s; eauto.
  { exploit rtc_pi_step_future; try (eapply rtc_implies, PI_STEPS); eauto.
    intro; des. inv WF0.
    eauto using promise_consistent_th_small_step_backward.
  }

  intro STEPS. des. ss.
  exploit with_pre_implies; try exact STEPS; i.
  { i. inv STEP0. eauto. }

  eapply (@pi_consistent_small_step_pi _ _ _ (_,_)) in TSTEP; eauto; cycle 1.
  { etrans; eauto. subst.
    eapply rtc_implies; [eapply pi_step_evt_to_true|].
    eapply with_pre_rtc_union; eauto. }
  { inv WF. eauto using consistent_promise_consistent_th. }
  des; esplits; eauto.
Qed.

Theorem pi_consistent_step_pi
      cST1 cT3 e tid
      (WF: pi_wf loctmeq cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (CONSISTENT: Configuration.consistent cST1.(snd))
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (STEP: Configuration.step e tid cST1.(snd) cT3):
  exists cST2 cS3 te,
    <<STEPS: rtc (tau (pi_step true tid)) cST1 cST2>> /\
    <<STEP: (pi_step true tid te) cST2 (cS3,cT3)>> /\
    <<EVENT: ThreadEvent.get_event te = e>>.
Proof.
  exploit step_small_steps; eauto; [by inv WF|]. i. des. subst.
  eapply rtc_tau_with_pre in STEPS. des.
  exploit pi_consistent_rtc_ftau_small_step_pi; eauto.
  { eauto using consistent_promise_consistent_th, promise_consistent_th_small_step_backward. }
  i. des.
  exploit with_pre_rtc_tau; eauto. i. des.
  exploit pi_consistent_small_step_pi.
  5: instantiate (2 := (_, _)). 5: exact STEP0. all: eauto using consistent_promise_consistent_th.
  { eapply rtc_implies, x2. i. inv PR. econs. eauto. }
  { inv WF. eauto using consistent_promise_consistent_th. }
  i. des. esplits; eauto.
Qed.
