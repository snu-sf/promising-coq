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

Require Import DRFBase.
Require Import SmallStep.
Require Import Race.

Set Implicit Arguments.


Inductive pi_step withprm: Ident.t -> ThreadEvent.t -> Configuration.t*Configuration.t -> Configuration.t*Configuration.t -> Prop :=
| pi_step_step
    e tid cS1 cT1 cS2 cT2
    (STEPT: small_step withprm tid e cT1 cT2)
    (STEPS: if ThreadEvent_is_promising e
            then cS1 = cS2
            else small_step false tid e cS1 cS2)
    (LANGMATCH: 
     option_map fst (IdentMap.find tid cS2.(Configuration.threads)) =
     option_map fst (IdentMap.find tid cT2.(Configuration.threads)))
    (NOWR: forall loc from ts val rel ord tid' ts'
             (WRITE:ThreadEvent.is_writing e = Some (loc, from, ts, val, rel, ord))
             (TIDNEQ: tid' <> tid),
           ~ Threads.is_promised tid' loc ts' cT1.(Configuration.threads)):
  pi_step withprm tid e (cS1,cT1) (cS2,cT2)
.
Hint Constructors pi_step.

Definition pi_step_evt withprm tid cST1 cST2: Prop :=
  step_union (pi_step withprm tid) cST1 cST2.
Hint Unfold pi_step_evt.

Definition pi_step_all withprm cST1 cST2: Prop :=
  step_union (pi_step_evt withprm) cST1 cST2.
Hint Unfold pi_step_all.

Inductive pi_step_except (tid_except:Ident.t) cST1 cST2: Prop :=
| pi_step_except_intro tid
    (PI_STEP: pi_step_evt true tid cST1 cST2)
    (TID: tid <> tid_except)
.
Hint Constructors pi_step_except.

Definition remove_promise (th: {lang : Language.t & Language.state lang} * Local.t) :=
  (th.(fst), Local.mk th.(snd).(Local.commit) Memory.bot).

Inductive pi_wf: Configuration.t*Configuration.t -> Prop :=
| pi_wf_intro cS cT
    (WFS: Configuration.wf cS)
    (WFT: Configuration.wf cT)
    (THS: cS.(Configuration.threads) = IdentMap.map remove_promise cT.(Configuration.threads))
    (SC: cS.(Configuration.sc) = cT.(Configuration.sc))
    (LR: forall loc ts from msg
           (IN: Memory.get loc ts cS.(Configuration.memory) = Some (from, msg)),
         <<IN: Memory.get loc ts cT.(Configuration.memory) = Some (from, msg)>> /\
         <<NOT: forall tid, ~Threads.is_promised tid loc ts cT.(Configuration.threads)>>)
    (RL: forall loc ts from msg
           (IN: Memory.get loc ts cT.(Configuration.memory) = Some (from, msg))
           (NOT: forall tid, ~Threads.is_promised tid loc ts cT.(Configuration.threads)),
         Memory.get loc ts cS.(Configuration.memory) = Some (from, msg)):
  pi_wf (cS,cT)
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
    <<STEPS: rtc (small_step_evt false tid) cS2 cS3>> /\
    <<PROEVT: Configuration_program_event cS3 tid e>> /\
    <<EVENT: ProgramEvent.is_writing e = Some (loc, ord)>> /\
    <<ORD: Ordering.le ord Ordering.relaxed>>):
  pi_consistent (cS1, cT1).
Hint Constructors pi_consistent.

Inductive conf_local_wf tid (c: Configuration.t) : Prop :=
| conf_local_wf_intro
    (LWF: forall lst lc
            (FIND: IdentMap.find tid c.(Configuration.threads) = Some (lst, lc)),
          Local.wf lc c.(Configuration.memory))
    (MCLOTM: Memory.closed_timemap c.(Configuration.sc) c.(Configuration.memory))
    (MCLO: Memory.closed c.(Configuration.memory)).
 
Inductive pi_local_wf tid (promise_oth: Loc.t -> Time.t -> Prop) : Configuration.t*Configuration.t -> Prop :=
| pi_local_wf_intro cS cT
    (WFS: conf_local_wf tid cS)
    (WFT: conf_local_wf tid cT)
    (THS: IdentMap.find tid cS.(Configuration.threads) =
          option_map remove_promise (IdentMap.find tid cT.(Configuration.threads)))
    (SC: cS.(Configuration.sc) = cT.(Configuration.sc))
    (LR: forall loc ts from msg
           (IN: Memory.get loc ts cS.(Configuration.memory) = Some (from, msg)),
         <<IN: Memory.get loc ts cT.(Configuration.memory) = Some (from, msg)>> /\
         <<NOTPRSELF: ~ Threads.is_promised tid loc ts cT.(Configuration.threads)>> /\
         <<NOTPROTH: ~ promise_oth loc ts>>)
    (RL: forall loc ts from msg
           (IN: Memory.get loc ts cT.(Configuration.memory) = Some (from, msg))
           (NOTPRSELF: ~ Threads.is_promised tid loc ts cT.(Configuration.threads))
           (NOTPROTH: ~ promise_oth loc ts),
         Memory.get loc ts cS.(Configuration.memory) = Some (from, msg))
    (PRM: forall loc ts 
            (PROTH: promise_oth loc ts),
          <<IN: exists from msg, Memory.get loc ts cT.(Configuration.memory) = Some (from, msg)>> /\
          <<NOTPRSELF: ~Threads.is_promised tid loc ts cT.(Configuration.threads)>>)
:
  pi_local_wf tid promise_oth (cS,cT)
.

Inductive promises_except tid (c: Configuration.t) loc ts : Prop :=
| promises_except_intro tid1
    (NEQ: tid1 <> tid)
    (PRM: Threads.is_promised tid1 loc ts c.(Configuration.threads))
.

Definition promise_consistent (tid: Ident.t) (c: Configuration.t) : Prop :=
  forall lst lc loc ts from msg
         (THREAD: IdentMap.find tid c.(Configuration.threads) = Some (lst, lc))
         (PROMISE: Memory.get loc ts lc.(Local.promises) = Some (from, msg)),
  Time.lt (lc.(Local.commit).(Commit.cur).(Capability.rw) loc) ts.

Definition pi_pre_proj (pre: option (Configuration.t*Configuration.t*ThreadEvent.t)) := 
  option_map (fun p => (p.(fst).(snd),p.(snd))) pre.


Lemma conf_wf_local_wf
    tid c
    (WF: Configuration.wf c):
  conf_local_wf tid c. 
Proof.
  inv WF. inv WF0. 
  econs; eauto.
  i. destruct lst. eauto.
Qed.

Lemma pi_wf_pi_local_wf
      cST tid
      (WF: pi_wf cST):
  pi_local_wf tid (promises_except tid cST.(snd)) cST.
Proof.
  inv WF. econs; eauto using conf_wf_local_wf.
  - rewrite THS. rewrite IdentMap.Properties.F.map_o. eauto.
  - i. apply LR in IN. des.
    esplits; eauto.
    intro X. destruct X.
    eapply NOT. eauto.
  - i. eapply RL; eauto.
    intros tid1 PRM.
    destruct (Ident.eq_dec tid1 tid) eqn: EQ.
    + subst. eauto.
    + apply NOTPROTH. econs; eauto.
  - i. destruct PROTH. inv PRM. ss.
    inv WFT. inv WF.
    esplits; eauto.
    + exploit THREADS; eauto.
      intro X. inv X.
      eapply PROMISES0. eauto.
    + intro X. inv X.
      exploit DISJOINT; eauto.
      intro X. inv X.
      eapply Memory.disjoint_get; eauto.
Grab Existential Variables.
  { eauto. }
Qed.

Lemma rtc_pi_step_local_wf
      cST1 cST2 tid oth withprm
      (MATCH: pi_local_wf tid oth cST1)
      (STEPS: rtc (pi_step_evt withprm tid) cST1 cST2):
  pi_local_wf tid oth cST2.
Proof.
(*
  induction STEPS; eauto.
  apply IHSTEPS. clear IHSTEPS STEPS z.
  unfold pi_local_wf, remove_promise, mem_sub in *.
  ss. des. rename MATCH0 into MATCH. 
  inv H. inv PI_STEP. inv STEPT. inv STEP; inv STEP0; ss.
  - subst. rewrite IdentMap.gss, MATCH, TID.
    inv LOCAL; esplits; eauto.
    i. apply MEMLE in IN. des. subst. esplits; eauto.
    admit.
  - inv STEPS. inv STEP; inv STEP0. ss.
    rewrite !IdentMap.gss in *. ss. depdes LANGMATCH.
    rewrite TID, TID0 in MATCH. depdes MATCH. ss. 
  - inv STEPS. inv STEP; inv STEP0. ss.
    rewrite !IdentMap.gss in *. ss. depdes LANGMATCH.
    rewrite TID, TID0 in MATCH. ss. depdes MATCH.
    inv LOCAL. inv LOCAL0. rewrite SCMAT. ss.
  - inv STEPS. inv STEP; inv STEP0. ss.
    rewrite !IdentMap.gss in *. ss. depdes LANGMATCH.
    rewrite TID, TID0 in MATCH. ss. depdes MATCH.
    inv LOCAL. inv LOCAL0. rewrite SCMAT. ss.
    esplits; eauto.
    + do 3 f_equal.
      admit.
    + i.
      admit.
  - inv STEPS. inv STEP; inv STEP0. ss.
    rewrite !IdentMap.gss in *. ss. depdes LANGMATCH.
    rewrite TID, TID0 in MATCH. ss. depdes MATCH.
    inv LOCAL1. inv LOCAL0. inv LOCAL2. inv LOCAL3. rewrite SCMAT.
    s. esplits; eauto. 
    + do 3 f_equal. s in WRITE0.
      admit.
    + i.
      admit.
  - inv STEPS. inv STEP; inv STEP0. ss.
    rewrite !IdentMap.gss in *. ss. depdes LANGMATCH.
    rewrite TID, TID0 in MATCH. ss. depdes MATCH.
    inv LOCAL. inv LOCAL0. ss. by rewrite SCMAT.
  - inv STEPS. inv STEP; inv STEP0. ss.
    rewrite !IdentMap.gss in *. ss. depdes LANGMATCH.
    rewrite TID, TID0 in MATCH. ss. depdes MATCH.
    inv LOCAL. inv LOCAL0. ss. by rewrite SCMAT.
*)
Admitted. (* gil easy *)

Lemma pi_step_future
      tid cST1 cST2 withprm
      (WF1: pi_wf cST1)
      (STEP: pi_step_evt withprm tid cST1 cST2):
  <<WF2: pi_wf cST2>> /\
  <<FUTURES: Memory.future cST1.(fst).(Configuration.memory) cST2.(fst).(Configuration.memory)>> /\
  <<FUTURET: Memory.future cST1.(snd).(Configuration.memory) cST2.(snd).(Configuration.memory)>>.
Proof.
  inv WF1. inv STEP. inv USTEP. splits; cycle 1. 
  - destruct (ThreadEvent_is_promising e).
    + subst. ss. econs.
    + eapply small_step_future in STEPS; eauto; des; ss.
  - eapply small_step_future in STEPT; eauto; des; ss.
  - (* jeehoon ? *)
    assert (WFT2: Configuration.wf cT2).
    { by eapply small_step_future, STEPT. }
    assert (WFS2: Configuration.wf cS2).
    { destruct (ThreadEvent_is_promising e); [by inv STEPS|].
      by eapply small_step_future, STEPS. }
    destruct cS. inv STEPT. inv STEP; inv STEP0; ss.
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
      cST1 cST2 withprm
      (WF1: pi_wf cST1)
      (STEPS: rtc (pi_step_all withprm) cST1 cST2):
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
      withprm tid cST1 cST2
      (STEP: pi_step_evt withprm tid cST1 cST2):
  pi_step_all withprm cST1 cST2.
Proof.
  econs; eauto.
Qed.

Lemma pi_step_except_all_incl
      tid cST1 cST2
      (STEP: pi_step_except tid cST1 cST2):
  pi_step_all true cST1 cST2.
Proof.
  inv STEP; econs; eauto.
Qed.

Lemma pi_local_wf_prm_oth_iff
      tid cST prm_oth1 prm_oth2
      (WF: pi_local_wf tid prm_oth1 cST)
      (IFF: forall loc ts, prm_oth1 loc ts <-> prm_oth2 loc ts):
  pi_local_wf tid prm_oth2 cST.
Proof.
  inv WF. econs; eauto.
  - i. exploit LR; eauto.
    i. des. esplits; eauto. 
    intro X. apply IFF in X. eauto.
  - i. eapply RL; eauto.
    intro X. apply IFF in X. eauto.
  - i. exploit PRM; eauto.
    apply IFF in PROTH. eauto.
Qed.

Lemma pi_steps_small_steps_fst
      tid cST1 cST2 withprm withprm'
      (PI_STEPS: rtc (pi_step_evt withprm tid) cST1 cST2):
  rtc (small_step_evt withprm' tid) (fst cST1) (fst cST2).
Proof.
  induction PI_STEPS; eauto.
  inv H. inv USTEP. 
  destruct (ThreadEvent_is_promising e).
  - subst. eauto.
  - econs; eauto. s. inv STEPS. destruct withprm'; econs; eauto 10. 
Qed.

Lemma pi_steps_small_steps_snd
      tid cST1 cST2 withprm
      (PI_STEPS: rtc (pi_step_evt withprm tid) cST1 cST2):
  rtc (small_step_evt withprm tid) (snd cST1) (snd cST2).
Proof.
  induction PI_STEPS; eauto.
  inv H. inv USTEP. econs; eauto.
Qed.

Lemma pi_steps_small_steps_snd_with_pre
      tid cST1 cST2 pre withprm
      (PI_STEPS: with_pre (pi_step withprm tid) cST1 pre cST2):
  with_pre (small_step withprm tid) (snd cST1) (pi_pre_proj pre) (snd cST2).
Proof.
  ginduction PI_STEPS; s; i; subst; eauto.
  des. inv PSTEP. eauto.
Qed.

Lemma pi_steps_all_pf_steps_fst
      cST1 cST2 withprm withprm'
      (PI_STEPS: rtc (pi_step_all withprm) cST1 cST2):
  rtc (small_step_all withprm') (fst cST1) (fst cST2).
Proof.
  induction PI_STEPS; eauto.
  inv H. inv USTEP. inv USTEP0. 
  destruct (ThreadEvent_is_promising e0) eqn: PROM.
  - subst. eauto.
  - econs; eauto. s. inv STEPS. destruct withprm'; econs; eauto 10. 
Qed.

Lemma pi_consistent_small_step_pi_rw
      e tid cST1 cST2 cT3 withprm
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt true tid) cST1 cST2)
      (STEP: small_step withprm tid e cST2.(snd) cT3):
  forall loc from to val rel ord tid' ts
    (NEQ: tid <> tid')
    (RW: ThreadEvent.is_reading e = Some (loc, to, val, rel, ord) \/
         ThreadEvent.is_writing e = Some (loc, from, to, val, rel, ord)),
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
    - eapply rtc_implies; [by i; eapply step_evt_intro, PR|].
      by eapply pi_steps_small_steps_fst in PI_STEPS; eauto.
    - eapply rtc_implies, STEPS. by econs; eauto.
  }
  { ss. inv STEP. inv STEP0; [by inv STEP; inv RW; inv H|].
    exploit rtc_pi_step_future; [|eapply rtc_implies; [eapply (@pi_step_evt_all_incl true)|]|]; eauto.
    i; des. clear FUTURES FUTURET.
    assert (LC1: exists lc1', IdentMap.find tid (Configuration.threads cS3) = Some (existT _ lang0 st1, lc1')).
    { eexists. erewrite <-(@rtc_small_step_find _ _ cS2); eauto.
      destruct cS2. inv WF2. ss. subst.
      setoid_rewrite IdentMap.Properties.F.map_o.
      by rewrite TID0. }

    des. inv STEP; inv RW; inv H
    ; econs; eauto; first [by econs 1; ss|by econs 2; ss].
  }
  i. des. destruct ord0; inv ORD; inv ORDW.
Qed.

Lemma pi_consistent_small_step_pi
      e tid cST1 cST2 cT3 withprm
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt true tid) cST1 cST2)
      (STEP: small_step withprm tid e cST2.(snd) cT3)
      (FULFILL: promise_consistent tid cT3):
  exists cS3, pi_step withprm tid e cST2 (cS3,cT3).
Proof.
  destruct cST1 as [cS1 cT1], cST2 as [cS2 cT2].
  assert (RW:= pi_consistent_small_step_pi_rw WF PI_CONSISTENT PI_RACEFREE PI_STEPS STEP).
  exploit rtc_pi_step_future; [|eapply rtc_implies; [eapply pi_step_evt_all_incl|]|]; eauto.
  i; des. destruct cS2. inv WF2. ss. assert (MSTEP:=STEP). inv STEP. inv STEP0.
  - eexists. econs; [by eauto|by inv STEP; s; eauto|..].
    + inv STEP. ss. rewrite IdentMap.gss.
      setoid_rewrite IdentMap.Properties.F.map_o.
      by rewrite TID.
    + i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); eauto.
  - inv STEP.
    { eexists. econs.
      - eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID.
        + econs 2; econs 1; eauto.
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); eauto.
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
          * subst. intro PROMISED. inv PROMISED.
            ss. rewrite TID0 in TID. depdes TID.
            rdes FULFILL. ss. rewrite IdentMap.gss in FULFILL.
            exploit FULFILL; s; eauto.
            intro LT. ss.
            inv READABLE; eauto.
            admit. (* with LT; jeehoon easy *)
          * eapply RW; s; eauto.
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); eauto.
    }
    { inv LOCAL. inv WRITE. eexists. econs.
      - econs; eauto. econs 2. econs 3; eauto. econs; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID.
        + econs 2; econs 3; eauto.
          ss. admit. (* jeehoon ?; construct pi_step; write case *)
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); eauto.
    }
    { admit. (* jeehoon ?; construct pi step; update case *)
    }
    { inv LOCAL. eexists. econs.
      - econs; eauto. econs 2. econs 5; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID.
        + econs 2; econs 5; eauto.
          econs; eauto.
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); eauto.
    }
    { inv LOCAL. eexists. econs.
      - econs; eauto. econs 2. econs 6; eauto. econs; eauto.
      - econs.
        + ss. setoid_rewrite IdentMap.Properties.F.map_o.
          by rewrite TID.
        + econs 2; econs 6; eauto.
          econs; eauto.
        + eauto.
        + eauto.
      - s. by rewrite !IdentMap.gss.
      - i. eapply (@pi_consistent_small_step_pi_rw _ _ _ (_,_)); eauto.
    }
Admitted. (* construct pi_step; mostly done *)

Lemma fulfill_unset_promises
      loc from ts val rel
      promises1 promises2
      l t f m
      (FULFILL: Memory.remove promises1 loc from ts val rel promises2)
      (TH1: Memory.get l t promises1 = Some (f, m))
      (TH2: Memory.get l t promises2 = None):
  l = loc /\ t = ts /\ f = from /\ m.(Message.val) = val /\ Capability.le rel m.(Message.released).
Proof.
  revert TH2. erewrite Memory.remove_o; eauto. condtac; ss; [|congr].
  des. subst. erewrite Memory.remove_get0 in TH1; eauto. inv TH1.
  esplits; eauto. refl.
Qed.

Lemma thread_step_unset_promises
      lang loc e from ts msg (th1 th2:Thread.t lang)
      (STEP: Thread.step e th1 th2)
      (TH1: Memory.get loc ts th1.(Thread.local).(Local.promises) = Some (from, msg))
      (TH2: Memory.get loc ts th2.(Thread.local).(Local.promises) = None):
  exists ord from val rel,
  <<EVENT: ThreadEvent.is_writing e = Some (loc, from, ts, val, rel, ord)>> /\
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
    + inv WRITABLE. inv READABLE. ss. move TS at bottom.
      eapply TimeFacts.le_lt_lt; eauto.
      repeat (etrans; [|apply Time.join_l]). refl.
Qed.

Lemma rtc_small_step_unset_promises
      tid loc ts c1 lst1 lc1 c2 lst2 lc2 from msg withprm
      (STEPS: rtc (small_step_evt withprm tid) c1 c2)
      (FIND1: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1))
      (GET1: Memory.get loc ts lc1.(Local.promises) = Some (from, msg))
      (FIND2: IdentMap.find tid c2.(Configuration.threads) = Some (lst2, lc2))
      (GET2: Memory.get loc ts lc2.(Local.promises) = None):
  Time.lt (lc1.(Local.commit).(Commit.cur).(Capability.rw) loc) ts.
Proof.
  ginduction STEPS; i; subst.
  { ss. rewrite FIND1 in FIND2. depdes FIND2.
    by rewrite GET1 in GET2.
  }
  inv H. inv USTEP. ss. rewrite FIND1 in TID. depdes TID.
  destruct (Memory.get loc ts lc3.(Local.promises)) as [[t m]|] eqn: PRM.
  - rewrite IdentMap.gss in IHSTEPS.
    exploit IHSTEPS; eauto.
    intro LT. move STEP at bottom.
    eapply TimeFacts.le_lt_lt; eauto.
    exploit thread_step_commit_future; try exact STEP; eauto. s. i.
    apply x1.
  - eapply thread_step_unset_promises in STEP; eauto. des.
    eauto using write_step_lt.
Qed.

Lemma promise_consistent_small_step
      tid c1 c2 withprm
      (STEP: small_step_evt withprm tid c1 c2)
      (FULFILL: promise_consistent tid c2):
  promise_consistent tid c1.
Proof.
  ii. destruct (IdentMap.find tid (Configuration.threads c2)) as [[lang2 lc2]|] eqn: THREAD2; cycle 1.
  { inv STEP. inv USTEP. ss. by rewrite IdentMap.gss in THREAD2. }
  destruct (Memory.get loc ts (Local.promises lc2)) as [[from2 msg2]|] eqn: PROMISE2; cycle 1.
  - apply Operators_Properties.clos_rt1n_step in STEP.
    eauto using rtc_small_step_unset_promises.
  - eapply FULFILL in PROMISE2; eauto.
    eapply TimeFacts.le_lt_lt; eauto.
    inv STEP. inv USTEP. ss.
    rewrite THREAD in TID. inv TID.
    rewrite IdentMap.gss in THREAD2. inv THREAD2.
    exploit thread_step_commit_future; try exact STEP; eauto. s. i.
    apply x0.
Qed.

Lemma promise_consistent_rtc_small_step
      tid c1 c2 withprm
      (STEP: rtc (small_step_evt withprm tid) c1 c2)
      (FULFILL: promise_consistent tid c2):
  promise_consistent tid c1.
Proof.
  ginduction STEP; eauto using promise_consistent_small_step.
Qed.

Lemma pi_consistent_rtc_small_step_pi
      tid cST1 cST2 withprm
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (PI_STEPS: rtc (pi_step_evt true tid) cST1 cST2)
      cT3 pre
      (STEP: with_pre (small_step withprm tid) cST2.(snd) pre cT3)
      (FULFILL: promise_consistent tid cT3):
  exists cS3 pre', with_pre (pi_step withprm tid) cST2 pre' (cS3,cT3) /\ 
                   pre = pi_pre_proj pre'.
Proof.
  destruct cST2 as [cS2 cT2].
  revert_until STEP. induction STEP.
  { s; i. eauto. }
  s; i. assert (FULFILL1 := FULFILL).
  eapply promise_consistent_small_step in FULFILL1; eauto. 
  exploit IHSTEP; s; eauto.
  intro STEPS. des. ss.
  eapply (@pi_consistent_small_step_pi _ _ _ (_,_)) in PSTEP; eauto; cycle 1.
  { etrans; eauto. subst. eapply with_pre_rtc_step_union; eauto. 
    eapply with_pre_implies, STEPS.
    i. inv STEP0. inv STEPT. eauto. }
  des. esplits; eauto.
Qed.

Lemma consistent_promise_consistent
      tid c 
      (WF: Configuration.wf c)
      (CONSISTENT: Configuration.consistent c):
  promise_consistent tid c.
Proof.
  ii. inv WF. inv WF0. destruct lst as [lang st].
  exploit CONSISTENT; eauto; try reflexivity.
  i; des. destruct e2.
  exploit rtc_thread_step_rtc_small_step; [eauto|..].
  { ss. eapply rtc_implies, STEPS. i; inv PR; eauto. }
  intro STEPS2. 
  eapply rtc_small_step_unset_promises in STEPS2; eauto.
  - s. rewrite IdentMap.gss. eauto.
  - ss. rewrite PROMISES. apply Cell.bot_get.
Qed.

Theorem pi_consistent_step_pi
      cST1 cT2 e tid
      (WF: pi_wf cST1)
      (PI_CONSISTENT: pi_consistent cST1)
      (CONSISTENT: Configuration.consistent cST1.(snd))
      (PI_RACEFREE: pf_racefree cST1.(fst))
      (STEP: Configuration.step e tid cST1.(snd) cT2):
  exists cS2, rtc (pi_step_evt true tid) cST1 (cS2,cT2).
Proof.
  exploit step_small_steps; eauto; [by inv WF|].
  i. des.
  eapply rtc_step_union_with_pre in STEPS. des.
  exploit pi_consistent_rtc_small_step_pi; eauto.
  { eapply consistent_promise_consistent; eauto. }
  i; des. eexists. eapply with_pre_rtc_step_union. eauto.
Qed.
