Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import DenseOrder.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import View.
Require Import Cell.
Require Import Memory.
Require Import TView.
Require Import Thread.
Require Import Configuration.

Require Import PFStep.
Require Import PromiseConsistent.
Require Import ReorderPromises.

Set Implicit Arguments.


Definition ThreadsProp :=
  forall (tid:Ident.t)
    (lang:Language.t)
    (st:lang.(Language.state)),
    Prop.

Definition MemoryProp :=
  forall (assign: LocFun.t Const.t),
    Prop.

Section Invariant.
  Variable
    (S:ThreadsProp)
    (J:MemoryProp).

  Hypothesis
    (SILENT:
       forall tid lang st1 st2
         (ST1: S tid lang st1)
         (STEP: lang.(Language.step) None st1 st2),
         S tid lang st2)
    (READ:
       forall tid lang st1 st2
         loc val ord
         assign
         (ST1: S tid lang st1)
         (ASSIGN1: J assign /\ LocFun.find loc assign = val)
         (STEP: lang.(Language.step) (Some (ProgramEvent.read loc val ord)) st1 st2),
         S tid lang st2)
    (WRITE:
       forall tid lang st1 st2
         loc val ord
         (ST1: S tid lang st1)
         (STEP: lang.(Language.step) (Some (ProgramEvent.write loc val ord)) st1 st2),
         <<ST2: S tid lang st2>> /\
         <<ASSIGN2: forall assign, J assign -> J (LocFun.add loc val assign)>>)
    (UPDATE:
       forall tid lang st1 st2
         loc valr valw ordr ordw
         assign
         (ST1: S tid lang st1)
         (ASSIGN1: J assign /\ LocFun.find loc assign = valr)
         (STEP: lang.(Language.step) (Some (ProgramEvent.update loc valr valw ordr ordw)) st1 st2),
         <<ST2: S tid lang st2>> /\
         <<ASSIGN2: forall assign, J assign -> J (LocFun.add loc valw assign)>>)
    (FENCE:
       forall tid lang st1 st2
         ordr ordw
         (ST1: S tid lang st1)
         (STEP: lang.(Language.step) (Some (ProgramEvent.fence ordr ordw)) st1 st2),
         S tid lang st2)
    (SYSCALL:
       forall tid lang st1 st2
         e
         (ST1: S tid lang st1)
         (STEP: lang.(Language.step) (Some (ProgramEvent.syscall e)) st1 st2),
         S tid lang st2)
  .

  Definition sem_threads (ths:Threads.t): Prop :=
    forall tid lang st lc
      (FIND: IdentMap.find tid ths = Some (existT _ lang st, lc)),
      S tid lang st.

  Definition memory_assign (m:Memory.t) (assign:Loc.t -> Const.t) :=
    forall loc,
    exists from to released,
      Memory.get loc to m =
      Some (from, Message.mk (LocFun.find loc assign) released).

  Definition sem_memory (m:Memory.t): Prop :=
    memory_assign m <1= J.

  Inductive sem (c:Configuration.t): Prop :=
  | sem_configuration_intro
      (TH: sem_threads c.(Configuration.threads))
      (MEM: sem_memory c.(Configuration.memory))
  .

  Lemma sem_memory_read_step
        lc1 mem1 loc to val released ord lc2
        (CLOSED: Memory.closed mem1)
        (STEP: Local.read_step lc1 mem1 loc to val released ord lc2)
        (SEM: sem_memory mem1):
    exists assign,
      J assign /\ LocFun.find loc assign = val.
  Proof.
    exists (LocFun.add loc val (LocFun.init 0)).
    splits.
    - apply SEM. ii.
      destruct (Loc.eq_dec loc loc0).
      + subst. rewrite LocFun.add_spec_eq.
        inv STEP. esplits; eauto.
      + rewrite LocFun.add_spec_neq, LocFun.init_spec.
        inv CLOSED. specialize (INHABITED loc0).
        esplits; eauto. congr.
    - apply LocFun.add_spec_eq.
  Qed.

  Lemma sem_memory_write_step_eq
        lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
        assign
        (CLOSED: Memory.closed mem1)
        (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
        (SEM: memory_assign mem2 assign)
        (LOC: LocFun.find loc assign = val):
    exists assign0,
      memory_assign mem1 assign0 /\
      assign = LocFun.add loc val assign0.
  Proof.
    exists (LocFun.add loc 0 assign). splits; cycle 1.
    - rewrite LocFun.add_add_eq. apply LocFun.ext. i.
      rewrite LocFun.add_spec. condtac; subst; ss.
    - ii. rewrite LocFun.add_spec. condtac.
      { inv CLOSED. specialize (INHABITED loc). esplits; eauto. }
      specialize (SEM loc0). des. revert SEM.
      inv STEP. inv WRITE0. inv PROMISE.
      + erewrite Memory.add_o; eauto. condtac; ss.
        * i. des. inv SEM. congr.
        * i. esplits; eauto.
      + erewrite Memory.split_o; eauto. condtac; ss.
        { i. des. inv SEM. congr. }
        condtac; ss.
        { guardH o. des. subst. congr. }
        i. esplits; eauto.
      + erewrite Memory.lower_o; eauto. condtac; ss.
        * i. des. inv SEM. congr.
        * i. esplits; eauto.
  Qed.

  Lemma sem_memory_write_step_neq
        lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind
        assign
        (CLOSED: Memory.closed mem1)
        (STEP: Local.write_step lc1 sc1 mem1 loc from to val releasedm released ord lc2 sc2 mem2 kind)
        (SEM: memory_assign mem2 assign)
        (LOC: LocFun.find loc assign <> val):
    memory_assign mem1 assign.
  Proof.
    ii. specialize (SEM loc0). des. revert SEM.
    inv STEP. inv WRITE0. inv PROMISE.
    - erewrite Memory.add_o; eauto. condtac; ss.
      + i. des. inv SEM. congr.
      + i. esplits; eauto.
    - erewrite Memory.split_o; eauto. condtac; ss.
      { i. des. inv SEM. congr. }
      condtac; ss.
      { guardH o. i. des. inv SEM.
        exploit Memory.split_get0; eauto. i. des.
        esplits; eauto.
      }
      i. esplits; eauto.
    - erewrite Memory.lower_o; eauto. condtac; ss.
      + i. des. inv SEM. congr.
      + i. esplits; eauto.
  Qed.

  Lemma thread_step_sem
        tid lang e
        st1 lc1 sc1 mem1
        st2 lc2 sc2 mem2
        (TH1: S tid lang st1)
        (MEM1: sem_memory mem1)
        (WF1: Local.wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (STEP: pf_step e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
    <<TH2: S tid lang st2>> /\
    <<MEM2: sem_memory mem2>>.
  Proof.
    inv STEP.
    { splits; ss. inv LOCAL. inv PROMISE; inv KIND.
      ii. apply MEM1. ii. specialize (PR loc0). des.
      revert PR. erewrite Memory.lower_o; eauto. condtac; eauto.
      ss. i. des. inv PR. exploit Memory.lower_get0; eauto.
    }
    inv STEP0.
    - esplits; eauto.
    - exploit sem_memory_read_step; eauto. i. des.
      exploit READ; eauto.
    - exploit WRITE; eauto. i. des.
      esplits; eauto. ii.
      destruct (Const.eq_dec (LocFun.find loc x0) val).
      { subst. hexploit sem_memory_write_step_eq; eauto. i. des.
        rewrite H0. eauto.
      }
      { hexploit sem_memory_write_step_neq; eauto. }
    - exploit sem_memory_read_step; eauto. i. des.
      exploit UPDATE; eauto. i. des.
      esplits; eauto. ii.
      destruct (Const.eq_dec (LocFun.find loc x2) valw).
      { subst. hexploit sem_memory_write_step_eq; eauto. i. des.
        rewrite H0. eauto.
      }
      { hexploit sem_memory_write_step_neq; eauto. }
    - exploit FENCE; eauto.
    - exploit SYSCALL; eauto.
  Admitted.

  Lemma rtc_thread_step_sem
        tid lang
        th1 th2
        (TH1: S tid lang th1.(Thread.state))
        (MEM1: sem_memory th1.(Thread.memory))
        (WF1: Local.wf th1.(Thread.local) th1.(Thread.memory))
        (SC1: Memory.closed_timemap th1.(Thread.sc) th1.(Thread.memory))
        (CLOSED1: Memory.closed th1.(Thread.memory))
        (STEP: rtc (@pf_step_evt lang) th1 th2):
    <<TH2: S tid lang th2.(Thread.state)>> /\
    <<MEM2: sem_memory th2.(Thread.memory)>>.
  Proof.
    move STEP after TH1. revert_until STEP. induction STEP; ss.
    i. inv H.
    exploit pf_step_future; eauto. i. des.
    destruct x, y. ss.
    exploit thread_step_sem; eauto. i. des.
    eapply IHSTEP; eauto.
  Qed.

  Lemma rtc_n1
        A R (a b c:A)
        (AB: rtc R a b)
        (BC: R b c):
    rtc R a c.
  Proof.
    etrans; eauto. econs 2; eauto.
  Qed.

  Lemma future_sem_memory
        m1 m2
        (FUTURE: Memory.future m1 m2)
        (SEM: sem_memory m2):
    sem_memory m1.
  Proof.
    revert SEM. induction FUTURE; ss. i.
    hexploit IHFUTURE; eauto. i.
    ii. apply H0. ii. specialize (PR loc). des.
    inv H. exploit Memory.op_get1; eauto. i. des. esplits; eauto.
  Qed.

  Lemma configuration_step_sem
        e tid c1 c2
        (WF: Configuration.wf c1)
        (SEM: sem c1)
        (STEP: Configuration.step e tid c1 c2):
    sem c2.
  Proof.
    inv SEM. econs.
    - inv STEP. ss. ii. revert FIND.
      rewrite IdentMap.gsspec. condtac; ss; [|by apply TH]. subst.
      i. inv FIND. apply inj_pair2 in H1. subst.
      eapply rtc_implies in STEPS; [|by apply tau_step_step_evt].
      exploit rtc_n1; eauto; i.
      { econs. eauto. }
      exploit rtc_step_evt_future; eauto; ss; try by inv WF.
      { inv WF. eapply WF0. eauto. }
      i. des.
      exploit steps_pf_steps; eauto; ss; try by inv WF.
      { hexploit consistent_promise_consistent; eauto. }
      { inv WF. eapply WF0. eauto. }
      i. des.
      exploit rtc_implies; (try by apply pf_step_evt_step_evt); eauto. i.
      exploit rtc_step_evt_future; eauto; ss; try by inv WF.
      { inv WF. eapply WF0. eauto. }
      i. des.
      exploit rtc_nonpf_step_evt_future; eauto. s. i. des.
      subst. eapply rtc_thread_step_sem; try exact STEPS1; eauto; ss; try by inv WF.
      inv WF. eapply WF3. eauto.
    - inv STEP. ss.
      eapply rtc_implies in STEPS; [|by apply tau_step_step_evt].
      exploit rtc_n1; eauto; i.
      { econs. eauto. }
      exploit rtc_step_evt_future; eauto; ss; try by inv WF.
      { inv WF. eapply WF0. eauto. }
      i. des.
      exploit CONSISTENT; eauto; ss; try refl. i. des.
      eapply rtc_implies in STEPS0; [|by apply tau_step_step_evt].
      rewrite STEPS0 in x0.
      exploit steps_pf_steps; try exact x0; eauto; ss; try by inv WF.
      { ii. rewrite PROMISES, Memory.bot_get in *. congr. }
      { inv WF. eapply WF0. eauto. }
      i. des.
      exploit rtc_nonpf_step_evt_bot; eauto. i. subst.
      exploit rtc_thread_step_sem; try exact STEPS1; eauto; ss; try by inv WF.
      { inv WF. eapply WF0. eauto. }
      i. des.
      exploit rtc_step_evt_future; try exact STEPS; eauto; ss; try by inv WF.
      { inv WF. eapply WF0. eauto. }
      i. des.
      exploit Thread.step_future; try exact STEP0; eauto. s. i. des.
      exploit rtc_step_evt_future; try exact STEPS0; eauto. s. i. des.
      eapply future_sem_memory; eauto.
  Qed.

  Inductive Configuration_step_evt (c1 c2:Configuration.t): Prop :=
  | Configuration_step_evt_intro
      e tid
      (STEP: Configuration.step e tid c1 c2)
  .

  Lemma init_sem
        program
        (TH: forall tid lang syn
               (FIND: IdentMap.find tid program = Some (existT _ lang syn)),
            S tid lang (lang.(Language.init) syn))
        (MEM: J (LocFun.init 0)):
    sem (Configuration.init program).
  Proof.
    econs.
    - ii. unfold Configuration.init in FIND. ss.
      unfold Threads.init in FIND. rewrite IdentMap.Facts.map_o in FIND.
      destruct ((UsualFMapPositive.UsualPositiveMap'.find tid program)) eqn:X; inv FIND.
      apply inj_pair2 in H1. subst. destruct s. ss.
      eapply TH; eauto.
    - ii. cut (x0 = LocFun.init 0); [by i; subst|].
      apply LocFun.ext. i. rewrite LocFun.init_spec.
      specialize (PR i). des. ss.
      unfold Memory.get, Memory.init in PR. unfold Cell.get, Cell.init in PR. ss.
      apply DOMap.singleton_find_inv in PR. des. inv PR0. auto.
  Qed.

  Lemma sound
        program c
        (TH: forall tid lang syn
               (FIND: IdentMap.find tid program = Some (existT _ lang syn)),
            S tid lang (lang.(Language.init) syn))
        (MEM: J (LocFun.init 0))
        (STEPS: rtc Configuration_step_evt (Configuration.init program) c):
    sem c.
  Proof.
    cut (forall c1 c2
           (WF: Configuration.wf c1)
           (CONS: Configuration.consistent c1)
           (SEM: sem c1)
           (STEPS: rtc Configuration_step_evt c1 c2),
            sem c2).
    { i. eapply H; eauto.
      - apply Configuration.init_wf.
      - apply Configuration.init_consistent.
      - apply init_sem; auto.
    }
    i. revert WF SEM. induction STEPS0; ss. i.
    inv H. exploit Configuration.step_future; eauto. i. des.
    apply IHSTEPS0; ss. eapply configuration_step_sem; try exact STEP; eauto.
  Qed.
End Invariant.
