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
Require Import PIStep.

Set Implicit Arguments.


Definition TimeMap_lift (x: Loc.t) (t: Time.t) (tm: TimeMap.t) : TimeMap.t :=
  fun y => if Loc.eq_dec x y then Time.join (tm y) t else tm y.

Definition Capability_lift (x: Loc.t) (t: Time.t) (rel: Capability.t) : Capability.t :=
  match rel with
  | Capability.mk ur rw sc => 
    Capability.mk ur (TimeMap_lift x t rw) (TimeMap_lift x t sc)
  end.

Definition pi_step_lift_mem l t e M1 M2 : Prop :=
  match ThreadEvent.is_writing e with
  | Some (loc,from,to,val,rel,ord) =>
    exists pm1 pm2 kind,
      <<PMREL: Memory.write pm1 M1 loc from to val (if Loc.eq_dec l loc then rel else Capability_lift l t rel) pm2 M2 kind>>
  | None =>
    M1 = M2
  end.

Inductive pi_step_lift (l: Loc.t) (t: Time.t) : Ident.t -> ThreadEvent.t -> Configuration.t*Configuration.t*Memory.t ->  Configuration.t*Configuration.t*Memory.t -> Prop :=
| pi_step_lift_intro tid e cS1 cS2 cT1 cT2 M1 M2
    (PI_STEP: pi_step true tid e (cS1,cT1) (cS2,cT2))
    (MEM: pi_step_lift_mem l t e M1 M2):
  pi_step_lift l t tid e (cS1,cT1,M1) (cS2,cT2,M2)
.
Hint Constructors pi_step_lift.

Definition pi_step_lift_evt l t tid cSTM1 cSTM2 : Prop :=
  step_union (pi_step_lift l t tid) cSTM1 cSTM2.
Hint Unfold pi_step_lift_evt.

Inductive pi_step_lift_except x t (tid_except:Ident.t) cSTM1 cSTM2: Prop :=
| pi_step_lift_except_intro tid
    (PI_STEP: pi_step_lift_evt x t tid cSTM1 cSTM2)
    (TID: tid <> tid_except)
.
Hint Constructors pi_step_lift_except.

Definition mem_sub (cmp: Capability.t -> Capability.t -> Prop) (m1 m2: Memory.t) : Prop :=
  forall loc ts from val rel1
    (IN: Memory.get loc ts m1 = Some (from, Message.mk val rel1)),
  exists rel2,
  <<IN: Memory.get loc ts m2 = Some (from, Message.mk val rel2)>> /\
  <<CMP: cmp rel1 rel2>>.

Definition mem_eqlerel (m1 m2: Memory.t) : Prop :=
  <<LR: mem_sub Capability.le m1 m2>> /\
  <<RL: mem_sub (fun x y => Capability.le y x) m2 m1>>.

Inductive mem_eqlerel_lift loc ts e (m1 m2: Memory.t) : Prop :=
| mem_le_lift_intro m1'
  (MEMEQ: mem_eqlerel m1 m1')
  (MEMWR: pi_step_lift_mem loc ts e m1' m2)
.

Definition conf_update_global (c: Configuration.t) sc (m: Memory.t) : Configuration.t :=
  Configuration.mk c.(Configuration.threads) sc m.

Inductive promises_aux tid cS cT loc ts : Prop :=
| promises_aux_intro
    (IN: exists from msg, Memory.get loc ts cT.(Configuration.memory) = Some(from,msg))
    (NOSRC: Memory.get loc ts cS.(Configuration.memory) = None)
    (NOPRM: ~Threads.is_promised tid loc ts cT.(Configuration.threads))
.

Lemma pi_steps_lift_except_pi_steps
      cSTM1 cSTM2 x t tid
      (STEPS: rtc (pi_step_lift_except x t tid) cSTM1 cSTM2):
  rtc (pi_step_except tid) cSTM1.(fst) cSTM2.(fst).
Proof.
  induction STEPS; eauto.
  etrans; [|apply IHSTEPS].
  inv H. inv PI_STEP. inv USTEP.
  econs; eauto.
Qed.

Lemma pi_step_lifting
      tid cST1 cST2 l t
      (PI_STEPS: rtc (pi_step_except tid) cST1 cST2):
  exists M2, rtc (pi_step_lift_except l t tid) (cST1,cST1.(snd).(Configuration.memory)) (cST2,M2).
Proof.
  (* TODO: assume that (l, t) is already in cST2.(snd)'s promises (or memory) *)
  (* TODO: assume WF? closedness? *)
Admitted. (* pi_step => exists pi_step_lift ? *)

Lemma pi_step_lift_except_future
      l t tid cS1 cT1 cSTM2 lst1 lc1
      (PI_STEPS: rtc (pi_step_lift_except l t tid) (cS1,cT1,cT1.(Configuration.memory)) cSTM2)
      (WF: pi_wf (cS1,cT1))
      (FIND: IdentMap.find tid cT1.(Configuration.threads) = Some (lst1,lc1)):
  <<MEMFUT: Memory.future cT1.(Configuration.memory) cSTM2.(snd)>> /\
  <<TIMELE: TimeMap.le cT1.(Configuration.sc) cSTM2.(fst).(snd).(Configuration.sc)>> /\
  <<LOCWF: Local.wf lc1 cSTM2.(snd)>> /\
  <<MEMCLOTM: Memory.closed_timemap (cSTM2.(fst).(snd).(Configuration.sc)) cSTM2.(snd)>> /\
  <<MEMCLO: Memory.closed cSTM2.(snd)>>.
Proof.
  (* TODO: assume that (x, t) is already in cT1's promises (or memory) *)
  (* TODO: assume WF? closedness? *)
Admitted.

Lemma rtc_pi_step_lift_except_find
      cSTM1 cSTM2 tid loc ts
      (STEPS: rtc (pi_step_lift_except loc ts tid) cSTM1 cSTM2):
  IdentMap.find tid cSTM1.(fst).(fst).(Configuration.threads) = IdentMap.find tid cSTM2.(fst).(fst).(Configuration.threads) /\
  IdentMap.find tid cSTM1.(fst).(snd).(Configuration.threads) = IdentMap.find tid cSTM2.(fst).(snd).(Configuration.threads).
Proof.
  (* ginduction STEPS; eauto. *)
  (* des. rewrite <-IHSTEPS, <-IHSTEPS0. *)
  (* inv H. inv PI_STEP. inv PI_STEP0. inv PI_STEP. *)
  (* ss; split; [by eapply small_step_find; eauto|]. *)
  admit.
Admitted. (* easy *)

Lemma rtc_pi_step_except_local_wf
      loc ts tid cS1 cT1 cSTM2
      (WF: pi_wf (cS1,cT1))
      (STEPS_LIFT : rtc (pi_step_lift_except loc ts tid) (cS1, cT1, cT1.(Configuration.memory)) cSTM2):
  pi_local_wf tid (promises_aux tid cSTM2.(fst).(fst) (conf_update_global cT1 cSTM2.(fst).(snd).(Configuration.sc) cSTM2.(snd)))
                  (cSTM2.(fst).(fst), conf_update_global cT1 cSTM2.(fst).(snd).(Configuration.sc) cSTM2.(snd)).
Proof.
(*
  destruct cSTM2 as [[cS2 cT2] M2]. ss.

  apply Operators_Properties.clos_rt_rt1n_iff,
        Operators_Properties.clos_rt_rtn1_iff in STEPS_LIFT.
  induction STEPS_LIFT.
  { assert (WF2 := pi_wf_pi_local_wf tid WF).
    destruct cS1, cT1. ss.
    eapply pi_local_wf_prm_oth_iff; eauto.
    clear WF2. inv WF. inv WFT. split; intro PR.
    - inv PR. ss. subst. econs; s.
      + inv WF. inv PRM. exploit THREADS; eauto.
        intro LOCAL. inv LOCAL.
        apply PROMISES0 in PROMISES. eauto.
      + destruct (Memory.get loc0 ts0 memory) as [[from msg]|] eqn: EQ; eauto.
        exfalso. exploit LR; eauto.
        i. des. eapply NOT; eauto.
      + intro PRM2. inv WF. inv PRM. inv PRM2.
        exploit DISJOINT; eauto.
        intro DISJ.
        admit. (* with DISJ, PROMISES, PROMISES0 *)
    - inv PR. des. ss. subst.
      assert (NA: ~ forall tid, ~ Threads.is_promised tid loc0 ts0 threads0).
      { intro NPRM. exploit RL; eauto. 
        intro X. by rewrite X in NOSRC. }
      eapply not_all_not_ex in NA. destruct NA as [tid0 NA].
      destruct (Ident.eq_dec tid0 tid) eqn: EQ.
      { subst. exfalso. eauto. }
      econs; eauto.
  }
  apply Operators_Properties.clos_rt_rtn1_iff,
        Operators_Properties.clos_rt_rt1n_iff in STEPS_LIFT.

  destruct y as [[cS2 cT2] M2].
  destruct z as [[cS3 cT3] M3]. ss.
  


  rdes IHSTEPS_LIFT. r; ss.
  exploit rtc_pi_step_lift_except_find.
  { econs 2; eauto. }
  intro EQ; des. rewrite <-EQ.

  inv H. inv PI_STEP. inv PI_STEP0. ss.

  assert(WF2: pi_wf (cS2,cT2)).
  { eapply rtc_pi_step_future; eauto.
    etrans.
    - apply pi_steps_lift_except_pi_steps in STEPS_LIFT.
      eapply rtc_implies, STEPS_LIFT.
      i. inv PR. eauto.
    - s. econs 2; eauto. }

  inv WF2.
  esplits; eauto.
  i. admit.
*)
Admitted. (* ? *)

Lemma pi_step_lift_mem_get
      l t e m1 m1' m2 m2' loc ts from1 msg2 from2' msg2'
      (LIFT1: pi_step_lift_mem l t e m1 m1')
      (LIFT2: pi_step_lift_mem l t e m2 m2')
      (IN1: Memory.get loc ts m1 = Some (from1, msg2))
      (IN2: Memory.get loc ts m2' = Some (from2', msg2')):
  exists from2 msg2,
  Memory.get loc ts m2 = Some (from2, msg2).
Proof.
Admitted. (* wrong; gil *)




Lemma local_simul_fence
      com prm prm' sc ordr ordw com' sc'
      (LOCAL: Local.fence_step (Local.mk com prm) sc ordr ordw (Local.mk com' prm') sc'):
  Local.fence_step (Local.mk com Memory.bot) sc ordr ordw (Local.mk com' Memory.bot) sc'.
Proof.
  inv LOCAL. econs; eauto.
Qed.

Lemma local_simul_write
      com com' sc sc' mS mT mT' loc from to val relr relw ord kind prm prm'
      (SUB: mem_sub eq mS mT)
      (WRITE: Local.write_step (Local.mk com prm) sc mT loc from to val relr relw ord (Local.mk com' prm') sc' mT' kind):
  exists mS',
  Local.write_step (Local.mk com Memory.bot) sc mS loc from to val relr relw ord (Local.mk com' Memory.bot) sc' mS' kind.
Proof.
Admitted. (* wrong; closedness *)

Lemma lift_fence
      sc1 sc2 sc2' com1 com2 com2' prm prm' ordr ordw
      (LOCAL: Local.fence_step (Local.mk com2 prm) sc2 ordr ordw (Local.mk com2' prm') sc2')
      (CoMLE: Commit.le com1 com2)
      (SC: TimeMap.le sc1 sc2):
  exists com1' sc1',
  <<LOCAL: Local.fence_step (Local.mk com1 prm) sc1 ordr ordw (Local.mk com1' prm') sc1'>> /\
  <<CoMLE: Commit.le com1' com2'>> /\
  <<SC: TimeMap.le sc1' sc2'>>.
Proof.
Admitted. (* jeehoon *)

Lemma lift_write
      com1 com2 com2' sc1 sc2 sc2' m1 m2 m2' prm prm' loc ts e loc' from to val relr1 relr2 relw2 ord kind
      (LOCAL: Local.write_step (Local.mk com2 prm) sc2 m2 loc' from to val relr2 relw2 ord (Local.mk com2' prm') sc2' m2' kind)
      (CoMLE: Commit.le com1 com2)
      (SC: TimeMap.le sc1 sc2)
      (REL: Capability.le relr1 relr2)
      (MEMLE: mem_eqlerel_lift loc ts e m1 m2):
  exists com1' sc1' m1' relw1,
  <<LOCAL: Local.write_step (Local.mk com1 prm) sc1 m1 loc' from to val relr1 relw1 ord (Local.mk com1' prm') sc1' m1' kind>> /\
  <<CoMLE: Commit.le com1' com2'>> /\
  <<SC: TimeMap.le sc1' sc2'>> /\
  <<MEMLE: mem_eqlerel_lift loc ts e m1' m2'>>.
Proof.
Admitted. (* jeehoon *)

Lemma lift_read
      com1 com2 com2' m1 m2 prm prm' loc ts e loc' to val rel2 ordr
      (LOCAL: Local.read_step (Local.mk com2 prm) m2 loc' to val rel2 ordr (Local.mk com2' prm'))
      (CoMLE: Commit.le com1 com2)
      (MEMLE: mem_eqlerel_lift loc ts e m1 m2):
  (exists from ordw,
   <<EVENT: ThreadEvent.is_writing e = Some (loc', from, to, val, rel2, ordw)>>)
  \/
  (exists com1' rel1,
   <<LOCAL: Local.read_step (Local.mk com1 prm) m1 loc' to val rel1 ordr (Local.mk com1' prm')>> /\
   <<CoMLE: Commit.le com1' com2'>>).
Proof.
Admitted. (* jeehoon *)


Inductive thread_event_eqlerel: ThreadEvent.t -> ThreadEvent.t -> Prop :=
| teel_promise loc from to val rel1 rel2
    (LEREL: Capability.le rel1 rel2):
  thread_event_eqlerel (ThreadEvent.promise loc from to val rel1) (ThreadEvent.promise loc from to val rel2) 
| teel_silent:
  thread_event_eqlerel (ThreadEvent.silent) (ThreadEvent.silent)
| teel_read loc ts val rel1 rel2 ord
    (LEREL: Capability.le rel1 rel2):
  thread_event_eqlerel (ThreadEvent.read loc ts val rel1 ord) (ThreadEvent.read loc ts val rel2 ord)
| teel_write loc from to val rel1 rel2 ord
    (LEREL: Capability.le rel1 rel2):
  thread_event_eqlerel (ThreadEvent.write loc from to val rel1 ord) (ThreadEvent.write loc from to val rel2 ord)
| teel_update loc tsr tsw valr valw relr1 relr2 relw1 relw2 ordr ordw
    (LEREL: Capability.le relr1 relr2)
    (LEREL: Capability.le relw1 relw2):
  thread_event_eqlerel (ThreadEvent.update loc tsr tsw valr valw relr1 relw1 ordr ordw) (ThreadEvent.update loc tsr tsw valr valw relr2 relw2 ordr ordw)
| teel_fence ordr ordw:
  thread_event_eqlerel (ThreadEvent.fence ordr ordw) (ThreadEvent.fence ordr ordw)
| teel_syscall e:
  thread_event_eqlerel (ThreadEvent.syscall e) (ThreadEvent.syscall e)
.

Lemma lift_step
      lang (thS1 thT1 thT2: @Thread.t lang) eT l t e
      (STEP: Thread.step eT thT1 thT2)
      (NOPRM: ThreadEvent_is_promising eT = None)
      (ST: thS1.(Thread.state) = thT1.(Thread.state))
      (COM: Commit.le thS1.(Thread.local).(Local.commit) thT1.(Thread.local).(Local.commit))
      (PRM: thS1.(Thread.local).(Local.promises) = thT1.(Thread.local).(Local.promises))
      (SC: TimeMap.le thS1.(Thread.sc) thT1.(Thread.sc))
      (MEM: mem_eqlerel_lift l t e thS1.(Thread.memory) thT1.(Thread.memory))
: 
  (exists loc ts from val relr relw ordr ordw,
   <<EVTR: ThreadEvent.is_reading eT = Some (loc, ts, val, relr, ordr)>> /\
   <<EVTW: ThreadEvent.is_writing e = Some (loc, from, ts, val, relw, ordw)>>)
  \/
  (exists eS thS2,
   <<EVT: thread_event_eqlerel eS eT>> /\
   <<STEP: Thread.step eS thS1 thS2>> /\
   <<ST: thS2.(Thread.state) = thT2.(Thread.state)>> /\
   <<COM: Commit.le thS2.(Thread.local).(Local.commit) thT2.(Thread.local).(Local.commit)>> /\
   <<PRM: thS2.(Thread.local).(Local.promises) = thT2.(Thread.local).(Local.promises)>> /\
   <<SC: TimeMap.le thS2.(Thread.sc) thT2.(Thread.sc)>> /\
   <<MEM: mem_eqlerel_lift l t e thS2.(Thread.memory) thT2.(Thread.memory)>>).
Proof.
Admitted. (* jeehoon *)
