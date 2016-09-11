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
Require Import MemoryFacts.
Require Import TView.
Require Import Thread.
Require Import Configuration.
Require Import Progress.

Require Import MemoryRel.

Set Implicit Arguments.


Inductive with_pre {A} {E} (step: E -> A -> A -> Prop) bs : option (A*E) ->  A -> Prop :=
| swp_base:
  with_pre step bs None bs
| swp_step
    pre ms e es
    (PSTEPS: with_pre step bs pre ms)
    (PSTEP: step e ms es):
  with_pre step bs (Some(ms,e)) es
.
Hint Constructors with_pre.

Lemma with_pre_rtc_union
      A E (step: E -> A -> A -> Prop) c1 c2 pre
      (STEPS: with_pre step c1 pre c2):
  rtc (union step) c1 c2.
Proof.
  ginduction STEPS; s; i; subst; eauto.
  i. etrans; eauto.
  econs 2; [|reflexivity]. eauto.
Qed.

Lemma rtc_union_with_pre
      A E (step: E -> A -> A -> Prop) c1 c2
      (STEPS: rtc (union step) c1 c2):
  exists pre,
  with_pre step c1 pre c2.
Proof.
  apply Operators_Properties.clos_rt_rt1n_iff,
        Operators_Properties.clos_rt_rtn1_iff in STEPS.
  induction STEPS.
  { exists None. eauto. }
  des. inv H. exists (Some(y,e)). s. eauto.
Qed.

Lemma with_pre_implies
      E A (step step': E -> A -> A -> Prop) c1 c2 pre
      (IMPL: forall e c1 c2 (STEP: step e c1 c2), step' e c1 c2)
      (STEPS: with_pre step c1 pre c2):
  with_pre step' c1 pre c2.
Proof.
  induction STEPS; eauto.
Qed.

Lemma with_pre_trans 
      A E (step: E -> A -> A -> Prop) c1 c2 c3 pre1 pre2
      (STEPS1: with_pre step c1 pre1 c2)
      (STEPS2: with_pre step c2 pre2 c3):
  with_pre step c1 (option_app pre2 pre1) c3.
Proof.
  ginduction STEPS2; s; i; des; subst; eauto.
Qed.


Lemma local_simul_fence
      com prm prm' sc ordr ordw com' sc'
      (LOCAL: Local.fence_step (Local.mk com prm) sc ordr ordw (Local.mk com' prm') sc'):
  Local.fence_step (Local.mk com Memory.bot) sc ordr ordw (Local.mk com' Memory.bot) sc'.
Proof.
  inv LOCAL. econs; eauto.
  s. i. apply Memory.bot_nonsynch.
Qed.


Lemma local_simul_write
      cmp com com' sc sc' mS mT mT' loc from to val relr relw ord kind prm prm'
      (SUB: mem_sub cmp mS mT)
      (DISJOINT: Memory.disjoint mS prm)
      (WRITE: Local.write_step (Local.mk com prm) sc mT loc from to val relr relw ord (Local.mk com' prm') sc' mT' kind):
  exists mS',
  Local.write_step (Local.mk com Memory.bot) sc mS loc from to val relr relw ord (Local.mk com' Memory.bot) sc' mS' Memory.op_kind_add.
Proof.
  set (relw' := relw).
  assert (RELW_WF: View.opt_wf relw').
  { inv WRITE. inv WRITE0. inv PROMISE.
    - inv MEM. inv ADD. auto.
    - inv MEM. inv SPLIT. auto.
    - inv MEM. inv LOWER. auto.
  }
  inv WRITE.
  hexploit (@Memory.add_exists Memory.bot loc from to val relw'); eauto.
  { i. rewrite Memory.bot_get in *. congr. }
  { eapply MemoryFacts.write_time_lt. eauto. }
  i. des.
  hexploit (@Memory.add_exists mS loc from to val relw'); eauto.
  { i. destruct msg2.
    inv WRITE0. inv PROMISE.
    - exploit SUB; eauto. i. des.
      inv MEM. inv ADD. eauto.
    - exploit Memory.split_get0; try exact PROMISES; eauto. s. i. des.
      inv DISJOINT. exploit DISJOINT0; eauto. i. des.
      symmetry in x. eapply Interval.le_disjoint; eauto. econs; [refl|].
      inv MEM. inv SPLIT. left. auto.
    - exploit Memory.lower_get0; try exact PROMISES; eauto. s. i.
      symmetry. eapply DISJOINT; eauto.
  }
  { eapply MemoryFacts.write_time_lt. eauto. }
  i. des.
  hexploit (@Memory.remove_exists mem2 loc from to val relw'); eauto.
  { erewrite Memory.add_o; eauto. condtac; ss. des; congr. }
  i. des.
  replace mem1 with Memory.bot in H1; cycle 1.
  { apply Memory.ext. i.
    erewrite (@Memory.remove_o mem1); eauto. erewrite (@Memory.add_o mem2); eauto.
    condtac; ss. des. subst. apply Memory.bot_get.
  }
  esplits. econs; eauto.
  - econs; eauto. econs; eauto.
    inv WRITE0. by inv PROMISE.
  - s. i. splits; ss. apply Memory.bot_nonsynch.
Qed.

Inductive small_step (withprm: bool) (tid:Ident.t) (e:ThreadEvent.t) (c1:Configuration.t): forall (c2:Configuration.t), Prop :=
| small_step_intro
    lang pf st1 st2 lc1 ths2 lc2 sc2 memory2
    (TID: IdentMap.find tid c1.(Configuration.threads) = Some (existT _ lang st1, lc1))
    (STEP: Thread.step pf e (Thread.mk _ st1 lc1 c1.(Configuration.sc) c1.(Configuration.memory)) (Thread.mk _ st2 lc2 sc2 memory2))
    (THS2: ths2 = IdentMap.add tid (existT _ _ st2, lc2) c1.(Configuration.threads))
    (PFREE: orb withprm pf)
  :
  small_step withprm tid e c1 (Configuration.mk ths2 sc2 memory2)
.
Hint Constructors small_step.

Definition small_step_evt withprm (tid:Ident.t) (c1 c2:Configuration.t) : Prop :=
  union (small_step withprm tid) c1 c2.
Hint Unfold small_step_evt.

Definition small_step_all withprm (c1 c2:Configuration.t) : Prop :=
  union (small_step_evt withprm) c1 c2.
Hint Unfold small_step_all.

Lemma small_step_evt_to_true
      withprm tid cST1 cST2
      (STEP: small_step_evt withprm tid cST1 cST2):
  small_step_evt true tid cST1 cST2.
Proof.
  destruct withprm; eauto.
  inv STEP. inv USTEP.
  econs. econs; eauto.
Qed.

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
      lang pf e tid threads
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (TID: IdentMap.find tid threads = Some (existT _ lang st1, lc1))
      (STEP: Thread.step pf e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
  small_step true tid e
             (Configuration.mk threads sc1 mem1)
             (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) sc2 mem2).
Proof.
  econs; eauto.
Qed.

Lemma thread_step_small_step_aux
      lang pf e tid threads
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (STEP: Thread.step pf e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
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
      (STEP: (rtc (@Thread.all_step lang)) th1 th2):
  rtc (small_step_evt true tid)
      (Configuration.mk threads th1.(Thread.sc) th1.(Thread.memory))
      (Configuration.mk (IdentMap.add tid (existT _ lang th2.(Thread.state), th2.(Thread.local)) threads) th2.(Thread.sc) th2.(Thread.memory)).
Proof.
  revert threads TID. induction STEP; i.
  - apply rtc_refl. f_equal. apply IdentMap.eq_leibniz. ii.
    rewrite IdentMap.Facts.add_o. condtac; auto. subst. auto.
  - inv H. inv USTEP. destruct x, y. ss. econs 2.
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
      (STEP: (rtc (@Thread.all_step lang)) (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
  rtc (small_step_evt true tid)
      (Configuration.mk threads sc1 mem1)
      (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) sc2 mem2).
Proof.
  exploit rtc_thread_step_rtc_small_step_aux; eauto. auto.
Qed.

Lemma tau_pf_step_small_step
      lang tid threads
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (TID: IdentMap.find tid threads = Some (existT _ lang st1, lc1))
      (STEP: tau (Thread.step true) (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
  small_step_evt false tid 
             (Configuration.mk threads sc1 mem1)
             (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) sc2 mem2).
Proof.
  inv STEP. econs. econs; eauto.
Qed.

Lemma tau_pf_step_small_step_aux
      lang tid threads
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (STEP: tau (Thread.step true) (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
  small_step_evt false tid
             (Configuration.mk (IdentMap.add tid (existT _ lang st1, lc1) threads) sc1 mem1)
             (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) sc2 mem2).
Proof.
  exploit tau_pf_step_small_step; eauto.
  { eapply IdentMap.Facts.add_eq_o. eauto. }
  rewrite (IdentMap.add_add_eq tid (existT Language.state lang st2, lc2)). eauto.
Qed.

Lemma rtc_tau_pf_step_rtc_small_step_aux
      lang tid threads
      th1 th2
      (TID: IdentMap.find tid threads = Some (existT _ lang th1.(Thread.state), th1.(Thread.local)))
      (STEP: (rtc (tau (@Thread.step lang true))) th1 th2):
  rtc (small_step_evt false tid)
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

Lemma rtc_tau_pf_step_rtc_small_step
      lang tid threads
      st1 lc1 sc1 mem1
      st2 lc2 sc2 mem2
      (TID: IdentMap.find tid threads = Some (existT _ lang st1, lc1))
      (STEP: (rtc (tau (@Thread.step lang true))) (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
  rtc (small_step_evt false tid)
      (Configuration.mk threads sc1 mem1)
      (Configuration.mk (IdentMap.add tid (existT _ lang st2, lc2) threads) sc2 mem2).
Proof.
  exploit rtc_tau_pf_step_rtc_small_step_aux; eauto. 
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
     lang pf e (t1 t2: @Thread.t lang)
     (STEP: Thread.step pf e t1 t2)
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
  inv STEP0; inv STEP; ss. inv LOCAL; ss; inv EVENT.
  - inv LOCAL0. apply WRITABLE.
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
  inv STEPT; ss.
  revert FIND2. rewrite IdentMap.gsspec. condtac.
  - i. inv FIND2.
    inv STEP; inv STEP0;
      (try inv LOCAL);
      (try inv LOCAL0);
      (try by esplits; eauto).
    + ss. apply promise_pf_inv in PFREE; eauto. des. subst. inv PROMISE.
      destruct msg2. exploit Memory.op_get_inv; eauto.
      { econs 3. eauto. }
      i. des.
      * subst. esplits; eauto. eapply Memory.lower_get0. eauto.
      * esplits; eauto.
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

Lemma small_step_promise_remove
      tid c1 c2 e loc from ts val relw ordw
      (WFT: Configuration.wf c1)
      (STEPT: small_step false tid e c1 c2)
      (EVTW: ThreadEvent.is_writing e = Some (loc, from, ts, val, relw, ordw)):
  forall tid', ~Threads.is_promised tid' loc ts c2.(Configuration.threads).
Proof.
Admitted.

