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


Definition TimeMap_lift (l: Loc.t) (t: Time.t) (tm: TimeMap.t) : TimeMap.t :=
  fun y => if Loc.eq_dec l y then Time.join (tm y) t else tm y.

Definition Capability_lift (l: Loc.t) (t: Time.t) (rel: Capability.t) : Capability.t :=
  match rel with
  | Capability.mk ur rw sc => 
    Capability.mk ur (TimeMap_lift l t rw) (TimeMap_lift l t sc)
  end.

Definition pi_step_lift_mem l t p k e M1 M2 : Prop :=
  match ThreadEvent.is_writing e with
  | Some (loc,from,to,val,rel,ord) =>
    <<NOTIN: Memory.get loc to p = None>> /\
    exists pm1 pm2,
      <<PMREL: Memory.write pm1 M1 loc from to val (if Loc.eq_dec l loc then rel else Capability_lift l t rel) pm2 M2 k>>
  | None =>
    M1 = M2
  end.

Inductive pi_step_lift_except l t (tid_except:Ident.t): (Configuration.t*Configuration.t*Memory.t) -> (Configuration.t*Configuration.t*Memory.t) -> Prop :=
| pi_step_lift_except_intro tid k e cS1 cS2 cT1 cT2 M1 M2 lst lc
    (PI_STEP: pi_step false tid e (cS1,cT1) (cS2,cT2))
    (FIND: IdentMap.find tid_except cT2.(Configuration.threads) = Some (lst,lc))
    (MEM: pi_step_lift_mem l t lc.(Local.promises) k e M1 M2)
    (TID: tid <> tid_except):
  pi_step_lift_except l t tid_except (cS1,cT1,M1) (cS2,cT2,M2)
.
Hint Constructors pi_step_lift_except.

Definition mem_eqlerel (m1 m2: Memory.t) : Prop :=
  <<LR: mem_sub Capability.le m1 m2>> /\
  <<RL: mem_sub (fun x y => Capability.le y x) m2 m1>>.

Inductive mem_eqlerel_lift l t p k e (m1 m2: Memory.t) : Prop :=
| mem_le_lift_intro m1'
  (MEMEQ: mem_eqlerel m1 m1')
  (MEMWR: pi_step_lift_mem l t p k e m1' m2)
.

Definition conf_update_memory (c: Configuration.t) (m: Memory.t) : Configuration.t :=
 Configuration.mk c.(Configuration.threads) c.(Configuration.sc) m.

Lemma pi_steps_lift_except_pi_steps
      cSTM1 cSTM2 l t tid
      (STEPS: rtc (pi_step_lift_except l t tid) cSTM1 cSTM2):
  rtc (pi_step_except false tid) cSTM1.(fst) cSTM2.(fst).
Proof.
  induction STEPS; eauto.
  etrans; [|apply IHSTEPS].
  inv H. econs; eauto.
Qed.

Lemma pi_step_lifting
      tid cST1 cST2 l t
      (PI_STEPS: rtc (pi_step_except false tid) cST1 cST2):
  exists M2, rtc (pi_step_lift_except l t tid) (cST1,cST1.(snd).(Configuration.memory)) (cST2,M2).
Proof.
  (* TODO: assume that (l, t) is already in cST2.(snd)'s promises (or memory) *)
  (* TODO: assume WF? closedness? *)
Admitted. (* pi_step_lifting: pi_step => exists pi_step_lift ?, not hard *)

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
Admitted. (* pi_step_lift_except_future *)

Lemma rtc_pi_step_lift_except_wf
      l t tid cS1 cT1 cSTM2
      (WF: pi_wf (cS1,cT1))
      (STEPS_LIFT : rtc (pi_step_lift_except l t tid) (cS1, cT1, cT1.(Configuration.memory)) cSTM2):
  pi_wf (cSTM2.(fst).(fst), conf_update_memory cSTM2.(fst).(snd) cSTM2.(snd)).
Proof.
Admitted. (* rtc_pi_step_lift_except_wf: easy? *)


Lemma rtc_pi_step_lift_except_find
      cSTM1 cSTM2 tid l t
      (STEPS: rtc (pi_step_lift_except l t tid) cSTM1 cSTM2):
  IdentMap.find tid cSTM1.(fst).(fst).(Configuration.threads) = IdentMap.find tid cSTM2.(fst).(fst).(Configuration.threads) /\
  IdentMap.find tid cSTM1.(fst).(snd).(Configuration.threads) = IdentMap.find tid cSTM2.(fst).(snd).(Configuration.threads).
Proof.
  apply pi_steps_lift_except_pi_steps in STEPS.
  apply rtc_pi_step_except_find in STEPS. eauto.
Qed.

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

Lemma mem_eqlerel_get
      m1 m2
      l f t v r2
      (LE: mem_eqlerel m1 m2)
      (GET2: Memory.get l t m2 = Some (f, Message.mk v r2)):
  exists r1,
    <<GET1: Memory.get l t m1 = Some (f, Message.mk v r1)>> /\
    <<REL: Capability.le r1 r2>>.
Proof. inv LE. des. exploit H0; eauto. Qed.

Lemma Memory_promise_get
      promises1 mem1 loc from to val released promises2 mem2 kind
      l f t v r
      (PROMISE: Memory.promise promises1 mem1 loc from to val released promises2 mem2 kind)
      (GET2: Memory.get l t mem2 = Some (f, Message.mk v r)):
  (l = loc /\ f = from /\ t = to /\ v = val /\ r = released) \/
  (__guard__ (l <> loc \/ t <> to) /\
   exists f',
     <<GET1: Memory.get l t mem1 = Some (f', Message.mk v r)>> /\
     <<FROM: Time.le f' f>>).
Proof.
  revert GET2. inv PROMISE.
  - erewrite Memory.add_o; eauto. condtac; ss.
    + i. des. inv GET2. left. auto.
    + i. right. esplits; eauto. refl.
  - erewrite Memory.split_o; eauto. repeat condtac; ss.
    + i. des. inv GET2. left. auto.
    + guardH o. i. des. inv GET2. right. splits; auto.
      exploit Memory.split_get0; try exact MEM; eauto. i. des.
      rewrite GET3. esplits; eauto. inv MEM. inv SPLIT. left. auto.
    + i. right. esplits; eauto. refl.
  - erewrite Memory.lower_o; eauto. condtac; ss.
    + i. des. inv GET2. left. auto.
    + i. right. esplits; eauto. refl.
Qed.

Lemma mem_eqlerel_lift_get
      loc ts prm k e m1 m2 l f t v r2
      (LIFT: mem_eqlerel_lift loc ts prm k e m1 m2)
      (GET: Memory.get l t m2 = Some (f, Message.mk v r2)):
  (exists r o, ThreadEvent.is_writing e = Some (l, f, t, v, r, o)) \/
  (exists f' r1,
      <<EVT: forall o, ThreadEvent.is_writing e <> Some (l, f, t, v, r1, o)>> /\
      <<GET: Memory.get l t m1 = Some (f', Message.mk v r1)>> /\
      <<REL: Capability.le r1 r2>> /\
      <<FROM: Time.le f' f>>).
Proof.
  inv LIFT. revert MEMWR. unfold pi_step_lift_mem.
  destruct (ThreadEvent.is_writing e) as [[[[[[] ?] ?] ?] ?]|] eqn:E; ss.
  - i. des. inv PMREL.
    exploit Memory_promise_get; eauto. i. des.
    + subst. eauto.
    + exploit mem_eqlerel_get; eauto. i. des.
      right. esplits; eauto. ii. inv H. unguardH x0. des; congr.
  - i. subst. exploit mem_eqlerel_get; eauto. i. des.
    right. esplits; eauto.
    + congr.
    + refl.
Qed.

Lemma lift_read
      com1 com2 com2' m1 m2 prm l t k e loc to val rel2 ordr
      (LOCAL: Local.read_step (Local.mk com2 prm) m2 loc to val rel2 ordr (Local.mk com2' prm))
      (COM2: Commit.wf com2)
      (REL2: Capability.wf rel2)
      (CoMLE: Commit.le com1 com2)
      (MEMLE: mem_eqlerel_lift l t prm k e m1 m2):
  (exists from relw ordw,
   <<EVENT: ThreadEvent.is_writing e = Some (loc, from, to, val, relw, ordw)>>)
  \/
  (exists com1' rel1,
   <<LOCAL: Local.read_step (Local.mk com1 prm) m1 loc to val rel1 ordr (Local.mk com1' prm)>> /\
   <<CoMLE: Commit.le com1' com2'>> /\
   <<RELLE: Capability.le rel1 rel2>>).
Proof.
  inversion LOCAL. ss. subst.
  exploit mem_eqlerel_lift_get; eauto. i. des.
  - left. esplits; eauto.
  - right. esplits; ss.
    + econs; eauto. ss. eapply CommitFacts.readable_mon; eauto. refl.
    + apply CommitFacts.read_commit_mon; eauto; try refl.
    + auto.
Qed.

Lemma lift_write
      com1 com2 com2' sc1 sc2 sc2' m1 m2 m2' prm prm' l t k e loc from to val relr1 relr2 relw2 ord kind
      (LOCAL: Local.write_step (Local.mk com2 prm) sc2 m2 loc from to val relr2 relw2 ord (Local.mk com2' prm') sc2' m2' kind)
      (CoMLE: Commit.le com1 com2)
      (SC: TimeMap.le sc1 sc2)
      (REL: Capability.le relr1 relr2)
      (MEMLE: mem_eqlerel_lift l t prm k e m1 m2):
  exists com1' sc1' m1' relw1,
  <<LOCAL: Local.write_step (Local.mk com1 prm) sc1 m1 loc from to val relr1 relw1 ord (Local.mk com1' prm') sc1' m1' kind>> /\
  <<CoMLE: Commit.le com1' com2'>> /\
  <<RELLE: Capability.le relw1 relw2>> /\
  <<SC: TimeMap.le sc1' sc2'>> /\
  <<MEMLE: mem_eqlerel_lift l t prm' k e m1' m2'>>.
Proof.
Admitted. (* lift_write *)

Lemma lift_fence
      sc1 sc2 sc2' com1 com2 com2' prm prm' ordr ordw
      (LOCAL: Local.fence_step (Local.mk com2 prm) sc2 ordr ordw (Local.mk com2' prm') sc2')
      (COM1: Commit.wf com1)
      (COM2: Commit.wf com2)
      (CoMLE: Commit.le com1 com2)
      (SC: TimeMap.le sc1 sc2):
  exists com1' sc1',
  <<LOCAL: Local.fence_step (Local.mk com1 prm) sc1 ordr ordw (Local.mk com1' prm') sc1'>> /\
  <<CoMLE: Commit.le com1' com2'>> /\
  <<SC: TimeMap.le sc1' sc2'>>.
Proof.
  inversion LOCAL. ss. subst.
  esplits; eauto.
  - econs; eauto.
  - apply CommitFacts.write_fence_commit_mon; eauto; try refl.
    + apply CommitFacts.read_fence_commit_mon; eauto; try refl.
    + unfold Commit.read_fence_commit. ss.
      econs; repeat (try condtac; aggrtac; try apply COM1).
  - apply CommitFacts.write_fence_sc_mon; eauto; try refl.
    apply CommitFacts.read_fence_commit_mon; eauto; try refl.
Qed.

Lemma lift_step
      lang (thS1 thT1 thT2: @Thread.t lang) eT l t k e
      (STEP: Thread.step eT thT1 thT2)
      (NOPRM: ThreadEvent_is_promising eT = None)
      (ST: thS1.(Thread.state) = thT1.(Thread.state))
      (WFS1: Local.wf thS1.(Thread.local) thS1.(Thread.memory))
      (WFT1: Local.wf thT1.(Thread.local) thT1.(Thread.memory))
      (SCS1: Memory.closed_timemap thS1.(Thread.sc) thS1.(Thread.memory))
      (SCT1: Memory.closed_timemap thT1.(Thread.sc) thT1.(Thread.memory))
      (MEMS1: Memory.closed thS1.(Thread.memory))
      (MEMT1: Memory.closed thT1.(Thread.memory))
      (COM: Commit.le thS1.(Thread.local).(Local.commit) thT1.(Thread.local).(Local.commit))
      (PRM: thS1.(Thread.local).(Local.promises) = thT1.(Thread.local).(Local.promises))
      (SC: TimeMap.le thS1.(Thread.sc) thT1.(Thread.sc))
      (MEM: mem_eqlerel_lift l t thT1.(Thread.local).(Local.promises) k e thS1.(Thread.memory) thT1.(Thread.memory))
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
   <<MEM: mem_eqlerel_lift l t thT2.(Thread.local).(Local.promises) k e thS2.(Thread.memory) thT2.(Thread.memory)>>).
Proof.
  inv STEP; inv STEP0; inv NOPRM; ss.
  - destruct lc1. subst. ss.
    destruct thS1, local. ss. subst.
    right. esplits.
    + econs.
    + econs 2. econs 1. eauto.
    + ss.
    + ss.
    + ss.
    + ss.
    + ss.
  - destruct lc1. inversion LOCAL. subst. ss.
    exploit lift_read; eauto.
    { apply WFT1. }
    { eapply MEMT1. eauto. }
    i. des.
    { left. esplits; eauto. }
    destruct thS1, local. ss. subst.
    right. esplits.
    + econs. eauto.
    + econs 2. econs 2; eauto.
    + ss.
    + ss.
    + ss.
    + ss.
    + ss.
  - destruct lc1. inversion LOCAL. subst. ss.
    exploit lift_write; eauto; try refl. i. des.
    destruct thS1, local. ss. subst.
    right. esplits.
    + econs. eauto.
    + econs 2. econs 3; eauto.
    + ss.
    + ss.
    + ss.
    + ss.
    + ss.
  - destruct lc1. inversion LOCAL1. subst. ss.
    exploit lift_read; eauto.
    { apply WFT1. }
    { eapply MEMT1. eauto. }
    i. des.
    { left. esplits; eauto. }
    inversion LOCAL2. subst. ss.
    exploit lift_write; eauto. i. des.
    destruct thS1, local. ss. subst.
    right. esplits.
    + econs; eauto.
    + econs 2. econs 4; eauto.
    + ss.
    + ss.
    + ss.
    + ss.
    + ss.
  - destruct lc1. inversion LOCAL. subst. ss.
    exploit lift_fence; eauto.
    { apply WFS1. }
    { apply WFT1. }
    i. des.
    destruct thS1, local. ss. subst.
    right. esplits.
    + econs.
    + econs 2. econs 5; eauto.
    + ss.
    + ss.
    + ss.
    + ss.
    + ss.
  - destruct lc1. inversion LOCAL. subst. ss.
    exploit lift_fence; eauto.
    { apply WFS1. }
    { apply WFT1. }
    i. des.
    destruct thS1, local. ss. subst.
    right. esplits.
    + econs.
    + econs 2. econs 6; eauto.
    + ss.
    + ss.
    + ss.
    + ss.
    + ss.
Qed.
