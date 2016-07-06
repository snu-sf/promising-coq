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
Require Import Commit.
Require Import Thread.
Require Import Configuration.

Require Import PromiseConsistent.
Require Import ReorderThreadStepSame.

Set Implicit Arguments.


Inductive step_evt lang (e1 e2:Thread.t lang): Prop :=
| step_evt_intro
    e
    (STEP: Thread.step e e1 e2)
.

Inductive program_step_evt lang (e1 e2:Thread.t lang): Prop :=
| program_step_evt_intro
    e
    (STEP: Thread.program_step e e1 e2)
.

Lemma rtc_step_evt_promise_consistent
      lang th1 th2
      (STEP: rtc (@step_evt lang) th1 th2)
      (CONS: promise_consistent th2.(Thread.local))
      (WF1: Local.wf th1.(Thread.local) th1.(Thread.memory))
      (SC1: Memory.closed_timemap th1.(Thread.sc) th1.(Thread.memory))
      (MEM1: Memory.closed th1.(Thread.memory)):
  promise_consistent th1.(Thread.local).
Proof.
  revert_until STEP. induction STEP; auto. i.
  inv H. exploit Thread.step_future; eauto. i. des.
  eapply step_promise_consistent; eauto.
Qed.

Lemma steps_pf_steps
      lang
      n e1 e2
      (STEPS: rtcn (@step_evt lang) n e1 e2)
      (PROMISES: e2.(Thread.local).(Local.promises) = Memory.bot)
      (WF1: Local.wf e1.(Thread.local) e1.(Thread.memory))
      (SC1: Memory.closed_timemap e1.(Thread.sc) e1.(Thread.memory))
      (MEM1: Memory.closed e1.(Thread.memory)):
  exists n',
    <<N: n' <= n>> /\
    <<STEPS: rtcn (@program_step_evt lang) n' e1 e2>>.
Proof.
  revert_until n. induction n using strong_induction; i.
  inv STEPS.
  { esplits; eauto. }
  inv A12. inv STEP; cycle 1.
  { exploit Thread.program_step_future; eauto. i. des.
    exploit IH; eauto. i. des.
    esplits; cycle 1.
    + econs 2; eauto. econs; eauto.
    + omega.
  }
  exploit Thread.promise_step_future; eauto. i. des.
  exploit IH; try exact A23; try refl; eauto. i. des.
  inv STEPS.
  { inv STEP0. ss. inv LOCAL. ss. subst.
    exploit Memory.promise_get2; eauto. rewrite Memory.bot_get. congr.
  }
  inversion A12. exploit Thread.program_step_future; eauto. i. des.
  exploit reorder_promise_program; eauto.
  { exploit rtcn_rtc; try exact A0; eauto. i.
    eapply rtc_step_evt_promise_consistent.
    - eapply rtc_implies; [|eauto]. i. inv PR. econs; eauto.
    - ii. rewrite PROMISES, Memory.bot_get in *. congr.
    - auto.
    - auto.
    - auto.
  }
  i. des.
  exploit Thread.program_step_future; eauto. i. des.
  unguardH STEP2. des.
  - subst. esplits; cycle 1.
    + econs 2; eauto. econs; eauto.
    + omega.
  - exploit Thread.promise_step_future; try exact STEP2; eauto. i. des.
    assert (STEPS: rtcn (step_evt (lang:=lang)) (S n) th1' e2).
    { econs 2.
      - econs. econs 1. apply STEP2.
      - eapply rtcn_imply; try exact A0. i. inv PR. econs; eauto.
    }
    exploit IH; try exact STEPS; eauto.
    { omega. }
    i. des. esplits; cycle 1.
    + econs; [|eauto]. econs; eauto.
    + omega.
Qed.

Definition ThreadsProp :=
  forall (tid:Ident.t)
    (lang:Language.t)
    (st:lang.(Language.state)),
    Prop.

Definition MemoryProp :=
  forall (assign: Loc.t -> Const.t),
    Prop.

Definition update loc val (assign:Loc.t -> Const.t): Loc.t -> Const.t :=
  fun l => if Loc.eq_dec l loc then val else assign l.

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
         (ASSIGN1: J assign /\ assign loc = val)
         (STEP: lang.(Language.step) (Some (ProgramEvent.read loc val ord)) st1 st2),
         S tid lang st2)
    (WRITE:
       forall tid lang st1 st2
         loc val ord
         (ST1: S tid lang st1)
         (STEP: lang.(Language.step) (Some (ProgramEvent.write loc val ord)) st1 st2),
         <<ST2: S tid lang st2>> /\
         <<ASSIGN2: forall assign, J assign -> J (update loc val assign)>>)
    (UPDATE:
       True)
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

  Inductive sem_threads (ths:Threads.t): Prop :=
  | sem_threads_intro
      (TH: forall tid lang st lc
             (FIND: IdentMap.find tid ths = Some (existT _ lang st, lc)),
          S tid lang st)
  .

  Inductive sem_memory (m:Memory.t): Prop :=
  | sem_memory_intro
      (MEM: forall assign
              (VAL: forall loc,
                  exists from to released,
                    Memory.get loc to m =
                    Some (from, Message.mk (assign loc) released)),
          J assign)
  .

  Inductive sem (c:Configuration.t): Prop :=
  | sem_configuration_intro
      (TH: sem_threads c.(Configuration.threads))
      (MEM: sem_memory c.(Configuration.memory))
  .

  Lemma thread_step_sem
        tid lang e
        st1 lc1 sc1 mem1
        st2 lc2 sc2 mem2
        (TH1: S tid lang st1)
        (MEM1: sem_memory mem1)
        (WF1: Local.wf lc1 mem1)
        (SC1: Memory.closed_timemap sc1 mem1)
        (CLOSED1: Memory.closed mem1)
        (STEP: Thread.program_step e (Thread.mk lang st1 lc1 sc1 mem1) (Thread.mk lang st2 lc2 sc2 mem2)):
    <<TH2: S tid lang st2>> /\
    <<MEM2: sem_memory mem2>>.
  Proof.
    inv STEP.
    - esplits; eauto.
    - exploit READ; eauto.
      { admit. (* [loc -> val] *) }
    - exploit WRITE; eauto. i. des.
      esplits; eauto.
      econs. i.
      admit.
    - admit.
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
        (STEP: rtc (@program_step_evt lang) th1 th2):
    <<TH2: S tid lang th2.(Thread.state)>> /\
    <<MEM2: sem_memory th2.(Thread.memory)>>.
  Proof.
    move STEP after TH1. revert_until STEP. induction STEP; ss.
    i. inv H.
    exploit Thread.program_step_future; eauto. i. des.
    destruct x, y. ss.
    exploit thread_step_sem; eauto. i. des.
    eapply IHSTEP; eauto.
  Qed.
End Invariant.
