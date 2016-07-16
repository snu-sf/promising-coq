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

Set Implicit Arguments.


Definition Thread_step_all {lang} (t1 t2:Thread.t lang) : Prop :=
  step_union (@Thread.step lang) t1 t2.
Hint Unfold Thread_step_all.

Inductive tau_program_step lang e1 e2: Prop :=
| step_program_tau
    e
    (STEP: @Thread.program_step lang e e1 e2)
    (TAU: ThreadEvent.get_event e = None)
.

Inductive small_step (withprm: bool) (tid:Ident.t) (e:ThreadEvent.t) (c1:Configuration.t): forall (c2:Configuration.t), Prop :=
| small_step_intro
    lang st1 st2 lc1 ths2 lc2 sc2 memory2
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEP: Thread.step e (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) (Thread.mk _ st2 lc2 sc2 memory2))
    (THS2: ths2 = IdentMap.add tid (existT _ _ st2, lc2) c1.(Configuration.threads))
    (PFREE: if withprm then True else ThreadEvent.is_promising e = None)
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
  <<FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>> /\
  <<SC_FUTURE: TimeMap.le  c1.(Configuration.sc) c2.(Configuration.sc)>>.
Proof.
  inv WF1. inv WF. inv STEP. ss. clear PFREE.
  exploit THREADS; ss; eauto. i.
  exploit Thread.step_future; eauto.
  s; i; des. splits; [|by eauto|by eauto]. econs; ss. econs.
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
  <<FUTURE: Memory.future c1.(Configuration.memory) c2.(Configuration.memory)>> /\
  <<SC_FUTURE: TimeMap.le  c1.(Configuration.sc) c2.(Configuration.sc)>>.
Proof.
  revert WF1. induction STEP; i.
  - splits; eauto; reflexivity.
  - destruct H. destruct USTEP. 
    exploit small_step_future; eauto. i; des.
    exploit IHSTEP; eauto. i; des.
    splits; eauto.
    + etrans; eauto.
    + etrans; eauto.
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

Lemma tau_program_step_small_step
      lang tid threads
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (TID: IdentMap.find tid threads = Some (existT _ lang st1, lc1))
      (STEP: tau_program_step (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
  small_step_evt false tid 
             (Configuration.mk threads sc1 mem1)
             (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) sc2 mem2).
Proof.
  inv STEP. econs. econs; eauto. inv STEP0; eauto.
Qed.

Lemma tau_program_step_small_step_aux
      lang tid threads
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (STEP: tau_program_step (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
  small_step_evt false tid
             (Configuration.mk (IdentMap.add tid (existT _ lang st1, lc1) threads) sc1 mem1)
             (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) sc2 mem2).
Proof.
  exploit tau_program_step_small_step; eauto.
  { eapply IdentMap.Facts.add_eq_o. eauto. }
  rewrite (IdentMap.add_add_eq tid (existT Language.state lang st2, lc2)). eauto.
Qed.

Lemma rtc_tau_program_step_rtc_small_step_aux
      lang tid threads
      th1 th2
      (TID: IdentMap.find tid threads = Some (existT _ lang th1.(Thread.state), th1.(Thread.local)))
      (STEP: (rtc (@tau_program_step lang)) th1 th2):
  rtc (small_step_evt false tid)
      (Configuration.mk threads th1.(Thread.sc) th1.(Thread.memory))
      (Configuration.mk (IdentMap.add tid (existT _ lang th2.(Thread.state), th2.(Thread.local)) threads) th2.(Thread.sc) th2.(Thread.memory)).
Proof.
  revert threads TID. induction STEP; i.
  - apply rtc_refl. f_equal. apply IdentMap.eq_leibniz. ii.
    rewrite IdentMap.Facts.add_o. condtac; auto. subst. auto.
  - inv H. destruct x, y. ss. econs 2.
    + econs; eauto. econs; eauto. inv STEP0; eauto.
    + etrans; [eapply IHSTEP|].
      * apply IdentMap.Facts.add_eq_o. auto.
      * apply rtc_refl. f_equal. apply IdentMap.eq_leibniz. ii.
        rewrite ? IdentMap.Facts.add_o. condtac; auto.
Qed.

Lemma rtc_tau_program_step_rtc_small_step
      lang tid threads
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (TID: IdentMap.find tid threads = Some (existT _ lang st1, lc1))
      (STEP: (rtc (@tau_program_step lang)) (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
  rtc (small_step_evt false tid)
      (Configuration.mk threads sc1 mem1)
      (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) sc2 mem2).
Proof.
  exploit rtc_tau_program_step_rtc_small_step_aux; eauto. 
  eauto.
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

Lemma thread_step_tview_le
     lang e (t1 t2: @Thread.t lang)
     (STEP: Thread.step e t1 t2)
     (LOCALWF: Local.wf t1.(Thread.local) t1.(Thread.memory))
     (SCWF: Memory.closed_timemap t1.(Thread.sc) t1.(Thread.memory))
     (MEMWF: Memory.closed t1.(Thread.memory)):
  TView.le t1.(Thread.local).(Local.tview) t2.(Thread.local).(Local.tview).
Proof.
  eapply Thread.step_future; eauto.
Qed.

Lemma rtc_small_step_tview_le
     c1 c2 tid lst1 lst2 lc1 lc2 withprm
     (STEPS: rtc (small_step_evt withprm tid) c1 c2)
     (THREAD1: IdentMap.find tid c1.(Configuration.threads) = Some (lst1, lc1))
     (THREAD2: IdentMap.find tid c2.(Configuration.threads) = Some (lst2, lc2))
     (WF: Configuration.wf c1):
  TView.le lc1.(Local.tview) lc2.(Local.tview).
Proof.
  ginduction STEPS; i.
  - rewrite THREAD1 in THREAD2. depdes THREAD2. reflexivity.
  - inv H. exploit small_step_future; eauto.
    intros [WF2 _].
    inv WF.
    destruct USTEP. rewrite THREAD1 in TID. depdes TID.
    etrans; [apply (thread_step_tview_le STEP)|]; eauto.
    eapply WF0; eauto.
    eapply IHSTEPS; eauto.
    s. subst. rewrite IdentMap.gss. eauto.
Qed.

Lemma small_step_write_lt
      tid c c1 e lst lc loc from ts val rel ord withprm
      (STEP: small_step withprm tid e c c1)
      (EVENT: ThreadEvent.is_writing e = Some (loc, from, ts, val, rel, ord))
      (THREAD: IdentMap.find tid (Configuration.threads c) = Some (lst, lc)):
  Time.lt (lc.(Local.tview).(TView.cur).(View.rlx) loc) ts.
Proof.
  inv STEP. rewrite THREAD in TID. inv TID.
  inv STEP0; inv STEP; inv EVENT.
  - inv LOCAL. apply WRITABLE.
  - eapply TimeFacts.le_lt_lt; cycle 1.
    + inv LOCAL2. inv WRITABLE. apply TS.
    + inv LOCAL1. s. do 2 (etrans; [|apply TimeMap.join_l]). refl.
Qed.

Lemma small_step_promise_decr
      tid tid' loc ts e c1 c2 lst2 lc2 from2 msg2
      (STEPT: small_step false tid e c1 c2)
      (FIND2: IdentMap.find tid' c2.(Configuration.threads) = Some (lst2,lc2))
      (PROMISES: Memory.get loc ts lc2.(Local.promises) = Some (from2, msg2)):
  exists lst1 lc1 from1 msg1,
  <<FIND1: IdentMap.find tid' c1.(Configuration.threads) = Some (lst1,lc1)>> /\
  <<PROMISES: Memory.get loc ts lc1.(Local.promises) = Some (from1, msg1)>>.
Proof.
  inv STEPT; ss. revert FIND2. rewrite IdentMap.gsspec. condtac.
  - i. inv FIND2.
    inv STEP; inv STEP0; inv PFREE; try inv LOCAL;
      (try by esplits; eauto).
    + inv WRITE.
      revert PROMISES. erewrite Memory.remove_o; eauto. condtac; ss.
      guardH o. i. destruct msg2.
      exploit MemoryFacts.MemoryFacts.promise_get_promises_inv_diff; eauto.
      { ii. inv H. unguardH o. des; congr. }
      i. des. esplits; eauto.
    + inv LOCAL1.
      inv LOCAL2. inv WRITE.
      revert PROMISES. erewrite Memory.remove_o; eauto. condtac; ss.
      guardH o. i. destruct msg2.
      exploit MemoryFacts.MemoryFacts.promise_get_promises_inv_diff; eauto.
      { ii. inv H. unguardH o. des; congr. }
      i. des. esplits; eauto.
  - i. esplits; eauto.
Qed.

Corollary small_step_promise_decr_bot
      tid tid' e c1 c2 lst1 lc1 lst2 lc2
      (STEPT: small_step false tid e c1 c2)
      (FIND1: IdentMap.find tid' c1.(Configuration.threads) = Some (lst1,lc1))
      (FIND2: IdentMap.find tid' c2.(Configuration.threads) = Some (lst2,lc2))
      (PROMISES: lc1.(Local.promises) = Memory.bot):
  lc2.(Local.promises) = Memory.bot.
Proof.
  apply Memory.ext. i. setoid_rewrite Cell.bot_get.
  destruct (Memory.get loc ts (Local.promises lc2)) as [[from msg]|] eqn: EQ; eauto.
  exploit small_step_promise_decr; eauto.
  i; des. rewrite FIND0 in FIND1. inv FIND1.
  rewrite PROMISES in *. 
  setoid_rewrite Cell.bot_get in PROMISES0. done.
Qed.

Inductive nonpromise c l f t msg :=
| nonpromise_intro
    (GET: Memory.get l t c.(Configuration.memory) = Some (f, msg))
    (NONPROMISE: forall tid, ~ Threads.is_promised tid l t c.(Configuration.threads))
.

Lemma writing_small_step_nonpromise_forward
      withprm tid e c1 c2 loc from to val released ord
      (WF: Configuration.wf c1)
      (STEP: small_step withprm tid e c1 c2)
      (WRITING: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)):
  forall l f t msg
    (NP: nonpromise c1 l f t msg),
    nonpromise c2 l f t msg.
Proof.
  inv STEP. inv STEP0; inv STEP; inv WRITING.
  - inv LOCAL. inv WRITE. inv PROMISE.
    { i. inv NP. econs; s.
      - erewrite Memory.add_o; eauto. condtac; ss.
        des. subst. exploit Memory.add_get0; eauto. congr.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.add_o; eauto. condtac; ss. i.
          eapply NONPROMISE. econs; eauto.
        + i. eapply NONPROMISE. econs; eauto.
    }
    { i. inv NP. econs; s.
      - erewrite Memory.split_o; eauto. condtac; ss.
        { des. subst. exploit Memory.split_get0; eauto. i. des. congr. }
        condtac; ss. guardH o. des. subst.
        exfalso. eapply NONPROMISE. econs; eauto.
        hexploit Memory.split_get0; try exact PROMISES; eauto. i. des. eauto.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          * guardH o. guardH o0. i. des. inv PROMISES0.
            eapply NONPROMISE. econs; eauto.
            hexploit Memory.split_get0; try exact PROMISES; eauto. i. des. eauto.
          * i. eapply NONPROMISE. econs; eauto.
        + i. eapply NONPROMISE. econs; eauto.
    }
    { i. inv NP. econs; s.
      - erewrite Memory.lower_o; eauto. condtac; ss.
        des. subst. exfalso. eapply NONPROMISE. econs; eauto.
        hexploit Memory.lower_get0; try exact PROMISES; eauto.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.lower_o; eauto. condtac; ss.
          guardH o. guardH o0. i. des. inv PROMISES0.
          eapply NONPROMISE. econs; eauto.
        + i. eapply NONPROMISE. econs; eauto.
    }
  - inv LOCAL1. clear GET.
    inv LOCAL2. inv WRITE. inv PROMISE.
    { i. inv NP. econs; s.
      - erewrite Memory.add_o; eauto. condtac; ss.
        des. subst. exploit Memory.add_get0; eauto. congr.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.add_o; eauto. condtac; ss. i.
          eapply NONPROMISE. econs; eauto.
        + i. eapply NONPROMISE. econs; eauto.
    }
    { i. inv NP. econs; s.
      - erewrite Memory.split_o; eauto. condtac; ss.
        { des. subst. exploit Memory.split_get0; eauto. i. des. congr. }
        condtac; ss. guardH o. des. subst.
        exfalso. eapply NONPROMISE. econs; eauto.
        hexploit Memory.split_get0; try exact PROMISES; eauto. i. des. eauto.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.split_o; eauto. repeat condtac; ss.
          * guardH o. guardH o0. i. des. inv PROMISES0.
            eapply NONPROMISE. econs; eauto.
            hexploit Memory.split_get0; try exact PROMISES; eauto. i. des. eauto.
          * i. eapply NONPROMISE. econs; eauto.
        + i. eapply NONPROMISE. econs; eauto.
    }
    { i. inv NP. econs; s.
      - erewrite Memory.lower_o; eauto. condtac; ss.
        des. subst. exfalso. eapply NONPROMISE. econs; eauto.
        hexploit Memory.lower_get0; try exact PROMISES; eauto.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.lower_o; eauto. condtac; ss.
          guardH o. guardH o0. i. des. inv PROMISES0.
          eapply NONPROMISE. econs; eauto.
        + i. eapply NONPROMISE. econs; eauto.
    }
Qed.

Lemma writing_small_step_nonpromise_new
      withprm tid e c1 c2 loc from to val released ord
      (WF: Configuration.wf c1)
      (STEP: small_step withprm tid e c1 c2)
      (WRITING: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)):
  nonpromise c2 loc from to (Message.mk val released).
Proof.
  inv STEP. inv STEP0; inv STEP; inv WRITING.
  - inv LOCAL. inv WRITE. inv PROMISE.
    { econs; s.
      - erewrite Memory.add_o; eauto. condtac; ss. des; congr.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          des; congr.
        + i. exploit Memory.add_get0; eauto. i.
          inv WF. inv WF0. exploit THREADS; eauto. i. inv x.
          apply PROMISES1 in PROMISES0. congr.
    }
    { econs; s.
      - erewrite Memory.split_o; eauto. condtac; ss.
        exfalso. clear -o. des; apply o; auto.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          des; congr.
        + i. exploit Memory.split_get0; eauto. i. des.
          inv WF. inv WF0. exploit THREADS; eauto. i. inv x.
          apply PROMISES1 in PROMISES0. congr.
    }
    { econs; s.
      - erewrite Memory.lower_o; eauto. condtac; ss. des; congr.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          des; congr.
        + i. exploit Memory.lower_get0; eauto. i.
          inv WF. inv WF0. exploit DISJOINT; eauto. i.
          eapply Memory.disjoint_get; try apply x; eauto.
          eapply Memory.lower_get0. eauto.
    }
  - inv LOCAL1. clear GET.
    inv LOCAL2. inv WRITE. inv PROMISE.
    { econs; s.
      - erewrite Memory.add_o; eauto. condtac; ss. des; congr.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          des; congr.
        + i. exploit Memory.add_get0; eauto. i.
          inv WF. inv WF0. exploit THREADS; eauto. i. inv x.
          apply PROMISES1 in PROMISES0. congr.
    }
    { econs; s.
      - erewrite Memory.split_o; eauto. condtac; ss.
        exfalso. clear -o. des; apply o; auto.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          des; congr.
        + i. exploit Memory.split_get0; eauto. i. des.
          inv WF. inv WF0. exploit THREADS; eauto. i. inv x.
          apply PROMISES1 in PROMISES0. congr.
    }
    { econs; s.
      - erewrite Memory.lower_o; eauto. condtac; ss. des; congr.
      - ii. inv H. revert TID0. rewrite IdentMap.gsspec. condtac.
        + i. inv TID0. apply inj_pair2 in H1. subst. ss.
          revert PROMISES0. erewrite Memory.remove_o; eauto. condtac; ss.
          des; congr.
        + i. exploit Memory.lower_get0; eauto. i.
          inv WF. inv WF0. exploit DISJOINT; eauto. i.
          eapply Memory.disjoint_get; try apply x; eauto.
          eapply Memory.lower_get0. eauto.
    }
Qed.

Lemma writing_small_step_nonpromise_backward
      withprm tid e c1 c2 loc from to val released ord
      (WF: Configuration.wf c1)
      (STEP: small_step withprm tid e c1 c2)
      (WRITING: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)):
  forall l f t msg
    (NP: nonpromise c2 l f t msg),
    nonpromise c1 l f t msg \/ (l, f, t, msg) = (loc, from, to, Message.mk val released).
Proof.
  inv STEP. inv STEP0; inv STEP; inv WRITING.
  - inv LOCAL. inv WRITE. inv PROMISE.
    { i. inv NP. ss. revert GET. erewrite Memory.add_o; eauto. condtac; ss.
      { i. des. inv GET. auto. }
      { left. econs; eauto. ii. inv H.
        destruct (Ident.eq_dec tid0 tid).
        - subst. rewrite TID in TID0. inv TID0. apply inj_pair2 in H1. subst.
          eapply NONPROMISE. econs.
          + rewrite IdentMap.gss. eauto.
          + s. erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.add_o; eauto. condtac; [|eauto]. ss.
        - eapply NONPROMISE. econs; eauto.
          rewrite IdentMap.gso; eauto.
      }
    }
    { i. inv NP. ss. revert GET. erewrite Memory.split_o; eauto. condtac; ss.
      { i. des. inv GET. auto. }
      guardH o. condtac; ss.
      { i. des. inv GET. exfalso. eapply NONPROMISE. econs.
        - rewrite IdentMap.gss. eauto.
        - erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.split_o; eauto.
          do 2 (condtac; try congr). eauto.
      }
      { left. econs; eauto. ii. inv H.
        destruct (Ident.eq_dec tid0 tid).
        - subst. rewrite TID in TID0. inv TID0. apply inj_pair2 in H1. subst.
          eapply NONPROMISE. econs.
          + rewrite IdentMap.gss. eauto.
          + s. erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.split_o; eauto. do 2 (condtac; try congr). eauto.
        - eapply NONPROMISE. econs; eauto.
          rewrite IdentMap.gso; eauto.
      }
    }
    { i. inv NP. ss. revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
      { i. des. inv GET. auto. }
      { left. econs; eauto. ii. inv H.
        destruct (Ident.eq_dec tid0 tid).
        - subst. rewrite TID in TID0. inv TID0. apply inj_pair2 in H1. subst.
          eapply NONPROMISE. econs.
          + rewrite IdentMap.gss. eauto.
          + s. erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.lower_o; eauto. condtac; [|eauto]. ss.
        - eapply NONPROMISE. econs; eauto.
          rewrite IdentMap.gso; eauto.
      }
    }
  - inv LOCAL1. clear GET.
    inv LOCAL2. inv WRITE. inv PROMISE.
    { i. inv NP. ss. revert GET. erewrite Memory.add_o; eauto. condtac; ss.
      { i. des. inv GET. auto. }
      { left. econs; eauto. ii. inv H.
        destruct (Ident.eq_dec tid0 tid).
        - subst. rewrite TID in TID0. inv TID0. apply inj_pair2 in H1. subst.
          eapply NONPROMISE. econs.
          + rewrite IdentMap.gss. eauto.
          + s. erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.add_o; eauto. condtac; [|eauto]. ss.
        - eapply NONPROMISE. econs; eauto.
          rewrite IdentMap.gso; eauto.
      }
    }
    { i. inv NP. ss. revert GET. erewrite Memory.split_o; eauto. condtac; ss.
      { i. des. inv GET. auto. }
      guardH o. condtac; ss.
      { i. des. inv GET. exfalso. eapply NONPROMISE. econs.
        - rewrite IdentMap.gss. eauto.
        - erewrite Memory.remove_o; eauto. condtac; ss.
          erewrite Memory.split_o; eauto.
          do 2 (condtac; try congr). eauto.
      }
      { left. econs; eauto. ii. inv H.
        destruct (Ident.eq_dec tid0 tid).
        - subst. rewrite TID in TID0. inv TID0. apply inj_pair2 in H1. subst.
          eapply NONPROMISE. econs.
          + rewrite IdentMap.gss. eauto.
          + s. erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.split_o; eauto. do 2 (condtac; try congr). eauto.
        - eapply NONPROMISE. econs; eauto.
          rewrite IdentMap.gso; eauto.
      }
    }
    { i. inv NP. ss. revert GET. erewrite Memory.lower_o; eauto. condtac; ss.
      { i. des. inv GET. auto. }
      { left. econs; eauto. ii. inv H.
        destruct (Ident.eq_dec tid0 tid).
        - subst. rewrite TID in TID0. inv TID0. apply inj_pair2 in H1. subst.
          eapply NONPROMISE. econs.
          + rewrite IdentMap.gss. eauto.
          + s. erewrite Memory.remove_o; eauto. condtac; ss.
            erewrite Memory.lower_o; eauto. condtac; [|eauto]. ss.
        - eapply NONPROMISE. econs; eauto.
          rewrite IdentMap.gso; eauto.
      }
    }
Qed.

Lemma writing_small_step_nonpromise
      withprm tid e c1 c2 loc from to val released ord
      (WF: Configuration.wf c1)
      (STEP: small_step withprm tid e c1 c2)
      (WRITING: ThreadEvent.is_writing e = Some (loc, from, to, val, released, ord)):
  forall l f t msg,
    nonpromise c2 l f t msg <-> nonpromise c1 l f t msg \/ (l, f, t, msg) = (loc, from, to, Message.mk val released).
Proof.
  econs; i.
  - eapply writing_small_step_nonpromise_backward; eauto.
  - des.
    + eapply writing_small_step_nonpromise_forward; eauto.
    + inv H. eapply writing_small_step_nonpromise_new; eauto.
Qed.
