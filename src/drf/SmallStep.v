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

Set Implicit Arguments.


Definition Thread_step_all {lang} (t1 t2:Thread.t lang) : Prop :=
  step_union (@Thread.step lang) t1 t2.
Hint Unfold Thread_step_all.


Inductive small_step (withprm: bool) (tid:Ident.t) (e:ThreadEvent.t) (c1:Configuration.t): forall (c2:Configuration.t), Prop :=
| small_step_intro
    lang st1 st2 lc1 ths2 lc2 sc2 memory2
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEP: Thread.step e (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) (Thread.mk _ st2 lc2 sc2 memory2))
    (THS2: ths2 = IdentMap.add tid (existT _ _ st2, lc2) c1.(Configuration.threads))
    (PFREE: if withprm then True else ThreadEvent_is_promising e = None)
  :
  small_step withprm tid e c1 (Configuration.mk ths2 sc2 memory2)
.
Hint Constructors small_step.

Definition small_step_evt withprm (tid:Ident.t) (c1 c2:Configuration.t) : Prop :=
  step_union (small_step withprm tid) c1 c2.
Hint Unfold small_step_evt.

Definition small_step_all withprm (c1 c2:Configuration.t) : Prop :=
  step_union (small_step_evt withprm) c1 c2.
Hint Unfold small_step_all.


Lemma small_step_future
      e tid c1 c2 withprm
      (WF1: Configuration.wf c1)
      (STEP: small_step withprm e tid c1 c2):
  <<WF2: Configuration.wf c2>> /\
  <<FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>.
Proof.
  inv WF1. inv WF. inv STEP. ss. clear PFREE.
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
      c1 c2 withprm
      (WF1: Configuration.wf c1)
      (STEP: rtc (small_step_all withprm) c1 c2):
  <<WF2: Configuration.wf c2>> /\
  <<FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>>.
Proof.
  revert WF1. induction STEP; i.
  - splits; eauto; reflexivity.
  - destruct H. destruct USTEP. 
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
  small_step true tid e
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
  small_step true tid e
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
  rtc (small_step_evt true tid)
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
  rtc (small_step_evt true tid)
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
    <<STEPS: rtc (small_step_evt true tid) c1 c3>> /\
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

Lemma small_step_find
      tid1 tid2 c1 c2 e withprm
      (STEP: small_step withprm tid1 e c1 c2)
      (TID: tid1 <> tid2):
  IdentMap.find tid2 c1.(Configuration.threads) = IdentMap.find tid2 c2.(Configuration.threads).
Proof.
  inv STEP. s.
  rewrite IdentMap.gso; eauto.
Qed.

Lemma rtc_small_step_find
      tid1 tid2 c1 c2 withprm
      (STEP: rtc (small_step_evt withprm tid1) c1 c2)
      (TID: tid1 <> tid2):
  IdentMap.find tid2 c1.(Configuration.threads) = IdentMap.find tid2 c2.(Configuration.threads).
Proof.
  induction STEP; auto. 
  inv H. rewrite <-IHSTEP.
  eauto using small_step_find.
Qed.

Lemma thread_step_commit_future
     lang e (t1 t2: @Thread.t lang)
     (STEP: Thread.step e t1 t2):
  Commit.le t1.(Thread.local).(Local.commit) t2.(Thread.local).(Local.commit).
Proof.
Admitted. (* jeehoon easy; add condition *)

Lemma rtc_small_step_commit_future
     c1 c2 tid lst1 lst2 lc1 lc2 withprm
     (STEPS: rtc (small_step_evt withprm tid) c1 c2)
     (THREAD1: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1))
     (THREAD2: IdentMap.find tid c2.(Configuration.threads) = Some (lst2, lc2)):
  Commit.le lc1.(Local.commit) lc2.(Local.commit).
Proof.
  ginduction STEPS; i.
  - rewrite THREAD1 in THREAD2. depdes THREAD2. reflexivity.
  - destruct H. destruct USTEP. rewrite THREAD1 in TID. depdes TID.
      etrans; [apply (thread_step_commit_future STEP)|].
      eapply IHSTEPS; eauto.
      s. subst. rewrite IdentMap.gss. eauto.
Qed.

Lemma write_step_lt
      tid c c1 e lst lc loc from ts val rel ord kind withprm
      (STEP: small_step withprm tid e c c1)
      (EVENT: ThreadEvent.is_writing e = Some (loc, from, ts, val, rel, ord, kind))
      (THREAD: IdentMap.find tid (Configuration.threads c) = Some (lst, lc)):
  Time.lt (lc.(Local.commit).(Commit.cur).(Capability.rw) loc) ts.
Proof.
Admitted. (* jeehoon easy; maybe add condition *)
