Require Import Omega.
Require Import RelationClasses.

Require Import sflib.
Require Import paco.

Require Import Axioms.
Require Import Basic.
Require Import DataStructure.
Require Import Event.
Require Import Time.
Require Import Language.
Require Import Memory.

Set Implicit Arguments.


Module Commit.
  Structure t := mk {
    current: Snapshot.t;
    released: LocFun.t Snapshot.t;
    acquirable: Snapshot.t;
  }.

  Definition init: t := mk Snapshot.init (LocFun.init Snapshot.init) Snapshot.init.

  Inductive wf (commit:t) (mem:Memory.t): Prop :=
  | wf_intro
      (CURRENT: Memory.wf_snapshot commit.(current) mem)
      (RELEASED: forall loc, Memory.wf_snapshot (commit.(released) loc) mem)
      (ACQUIRABLE: Memory.wf_snapshot commit.(acquirable) mem)
  .

  Lemma future_wf
        commit mem1 mem2
        (WF: wf commit mem1)
        (FUTURE: Memory.future mem1 mem2):
    wf commit mem2.
  Proof.
    inv WF. econs; i; eapply Memory.future_wf_snapshot; eauto.
  Qed.

  Inductive le (lhs rhs:t): Prop :=
  | le_intro
      (CURRENT: Snapshot.le lhs.(current) rhs.(current))
      (RELEASED: forall (loc:Loc.t), Snapshot.le (LocFun.find loc lhs.(released)) (LocFun.find loc rhs.(released)))
      (ACQUIRABLE: Snapshot.le lhs.(acquirable) rhs.(acquirable))
  .

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. econs; reflexivity.
  Qed.
  Next Obligation.
    ii. inv H. inv H0. econs; etransitivity; eauto.
  Qed.

  Inductive read
            (commit1:t) (loc:Loc.t) (ts:Time.t) (released:Snapshot.t) (ord:Ordering.t)
            (commit2:t): Prop :=
  | read_intro
      (MONOTONE: le commit1 commit2)
      (READABLE: Snapshot.readable commit1.(current) loc ts)
      (READ: Time.le ts (Times.get loc commit2.(current).(Snapshot.reads)))
      (ACQUIRE: forall (ORDERING: Ordering.le Ordering.acquire ord),
          Snapshot.le released commit2.(current))
      (ACQUIRABLE: Snapshot.le released commit2.(acquirable))
  .

  Inductive write
            (commit1:t) (loc:Loc.t) (ts:Time.t) (released:Snapshot.t) (ord:Ordering.t)
            (commit2:t): Prop :=
  | write_intro
      (MONOTONE: le commit1 commit2)
      (WRITABLE: Snapshot.writable commit1.(current) loc ts)
      (WRITE: Time.le ts (Times.get loc commit2.(current).(Snapshot.writes)))
      (RELEASE: forall (ORDERING: Ordering.le Ordering.release ord),
          Snapshot.le commit2.(current) (LocFun.find loc commit2.(Commit.released)))
      (RELEASED: Snapshot.le (LocFun.find loc commit2.(Commit.released)) released)
  .

  Inductive fence
            (commit1:t) (ord:Ordering.t)
            (commit2:t): Prop :=
  | fence_intro
      (MONOTONE: le commit1 commit2)
      (ACQUIRE: forall (ORDERING: Ordering.le Ordering.acquire ord),
          Snapshot.le commit2.(acquirable) commit2.(current))
      (RELEASE: forall (ORDERING: Ordering.le Ordering.release ord) loc,
          Snapshot.le commit2.(current) (LocFun.find loc commit2.(released)))
  .

  Lemma read_mon
        commit1 commit2
        (LE: le commit1 commit2):
    read commit2 <5= read commit1.
  Proof.
    i. inv PR. econs; auto.
    - etransitivity; eauto.
    - eapply Snapshot.readable_mon; eauto.
      apply LE.
  Qed.

  Lemma write_mon
        commit1 commit2
        (LE: le commit1 commit2):
    write commit2 <5= write commit1.
  Proof.
    i. inv PR. econs; auto.
    - etransitivity; eauto.
    - eapply Snapshot.writable_mon; eauto.
      apply LE.
  Qed.

  Lemma fence_mon
        commit1 commit2
        (LE: le commit1 commit2):
    fence commit2 <2= fence commit1.
  Proof.
    i. inv PR. econs; auto. etransitivity; eauto.
  Qed.
End Commit.

Module Thread.
  Section Thread.
    Variable (lang:Language.t).

    Definition syntax := lang.(Language.syntax).

    Structure t := mk {
      state: lang.(Language.state);
      commit: Commit.t;
      promise: Memory.t;
    }.

    Definition init (s:syntax) :=
      mk (lang.(Language.init) s)
         Commit.init
         Memory.bot.

    Inductive is_terminal (th:t): Prop :=
    | is_terminal_intro
        (STATE: lang.(Language.is_terminal) th.(state))
        (PROMISE: th.(promise) = Memory.bot)
    .

    Inductive internal_step (th1:t) (mem1:Memory.t): forall (th2:t) (mem2:Memory.t), Prop :=
    | step_read
        loc val ts released ord st2 commit2
        (STATE: lang.(Language.step) th1.(state) (Some (ThreadEvent.mem (MemEvent.read loc val ord))) st2)
        (COMMIT: Commit.read th1.(commit) loc ts released ord commit2)
        (COMMIT_WF: Commit.wf commit2 mem1)
        (GET: Memory.get loc ts mem1 = Some (Message.mk val released))
        (GET_PROMISE: Memory.get loc ts th1.(promise) = None):
        internal_step th1 mem1
                      (mk st2 commit2 th1.(promise)) mem1
    | step_write
        loc val from ts released ord st2 commit2 promise2 mem2
        (STATE: lang.(Language.step) th1.(state) (Some (ThreadEvent.mem (MemEvent.write loc val ord))) st2)
        (COMMIT: Commit.write th1.(commit) loc ts released ord commit2)
        (COMMIT_WF: Commit.wf commit2 mem2)
        (MEMORY: Memory.write th1.(promise) mem1 loc from ts (Message.mk val released) ord promise2 mem2):
        internal_step th1 mem1
                      (mk st2 commit2 promise2) mem2
    | step_update
        loc valr tsr releasedr valw tsw releasedw ord st3 commit2 commit3 promise3 mem3
        (STATE: lang.(Language.step) th1.(state) (Some (ThreadEvent.mem (MemEvent.update loc valr valw ord))) st3)
        (COMMIT_READ: Commit.read th1.(commit) loc tsr releasedr ord commit2)
        (COMMIT_WRITE: Commit.write commit2 loc tsw releasedw ord commit3)
        (COMMIT_WF: Commit.wf commit3 mem3)
        (RELEASED: Snapshot.le releasedr releasedw)
        (GET: Memory.get loc tsr mem1 = Some (Message.mk valr releasedr))
        (GET_PROMISE: Memory.get loc tsr th1.(promise) = None)
        (MEMORY: Memory.write th1.(promise) mem1 loc tsr tsw (Message.mk valw releasedw) ord promise3 mem3):
        internal_step th1 mem1
                      (mk st3 commit3 promise3) mem3
    | step_fence
        ord st2 commit2
        (STATE: lang.(Language.step) th1.(state) (Some (ThreadEvent.mem (MemEvent.fence ord))) st2)
        (COMMIT: Commit.fence th1.(commit) ord commit2)
        (COMMIT_WF: Commit.wf commit2 mem1)
        (MEMORY: Memory.fence th1.(promise) ord):
        internal_step th1 mem1
                      (mk st2 commit2 th1.(promise)) mem1
    | step_silent
        st2 commit2
        (STATE: lang.(Language.step) th1.(state) None st2)
        (COMMIT: Commit.le th1.(commit) commit2)
        (COMMIT_WF: Commit.wf commit2 mem1):
        internal_step th1 mem1
                      (mk st2 commit2 th1.(promise)) mem1
    | step_promise
        loc from ts msg commit2 promise2 mem2
        (COMMIT: Commit.le th1.(commit) commit2)
        (COMMIT_WF: Commit.wf commit2 mem2)
        (MEMORY: Memory.promise th1.(promise) mem1 loc from ts msg promise2 mem2):
        internal_step th1 mem1
                      (mk th1.(state) commit2 promise2) mem2
    .

    Inductive step: forall (e:option Event.t) (th1:t) (mem1:Memory.t) (th2:t) (mem2:Memory.t), Prop :=
    | step_internal
        th1 th2 mem1 mem2
        (STEP: internal_step th1 mem1 th2 mem2):
        step None th1 mem1 th2 mem2
    | step_external
        st1 st2 commit1 commit2 mem e
        (STATE: lang.(Language.step) st1 (Some (ThreadEvent.syscall e)) st2)
        (COMMIT: Commit.le commit1 commit2)
        (COMMIT_WF: Commit.wf commit2 mem):
        step (Some e)
             (mk st1 commit1 Memory.bot) mem
             (mk st2 commit2 Memory.bot) mem
    .

    Inductive _internal_step (c1 c2:t * Memory.t): Prop :=
    | _internal_step_intro
        (STEP: internal_step c1.(fst) c1.(snd) c2.(fst) c2.(snd))
    .

    Inductive wf (th:t) (mem:Memory.t): Prop :=
    | wf_intro
        (COMMIT: Commit.wf th.(commit) mem)
        (PROMISE: Memory.le th.(promise) mem)
    .

    Definition consistent (th1:t) (mem:Memory.t): Prop :=
      forall mem1
        (WF: wf th1 mem1)
        (FUTURE: Memory.future mem mem1),
      exists th2 mem2,
        <<STEPS: rtc _internal_step (th1, mem1) (th2, mem2)>> /\
        <<PROMISE: th2.(promise) = Memory.bot>>.

    Lemma internal_step_future
          th1 mem1 th2 mem2
          (STEP: internal_step th1 mem1 th2 mem2)
          (WF1: wf th1 mem1):
      <<WF2: wf th2 mem2>> /\
      <<FUTURE: Memory.future mem1 mem2>>.
    Proof.
      inv WF1. inv STEP; try by (splits; ss; reflexivity).
      - exploit Memory.write_future; try apply MEMORY; eauto. i. des. ss.
      - exploit Memory.write_future; try apply MEMORY; eauto. i. des. ss.
      - exploit Memory.promise_future; try apply MEMORY; eauto. i. des. ss.
    Qed.

    Lemma internal_step_disjoint
          th1 mem1 th2 mem2 mem_o
          (STEP: internal_step th1 mem1 th2 mem2)
          (DISJOINT1: Memory.disjoint th1.(promise) mem_o)
          (WF1: wf th1 mem1)
          (LE1: Memory.le mem_o mem1):
      <<DISJOINT2: Memory.disjoint th2.(promise) mem_o>> /\
      <<LE2: Memory.le mem_o mem2>>.
    Proof.
      inv WF1. inv STEP; ss.
      - eapply Memory.write_disjoint; try apply MEMORY; eauto.
      - eapply Memory.write_disjoint; try apply MEMORY; eauto.
      - eapply Memory.promise_disjoint; try apply MEMORY; eauto.
    Qed.

    Lemma step_future
          e th1 mem1 th2 mem2
          (STEP: step e th1 mem1 th2 mem2)
          (WF1: wf th1 mem1):
      <<WF2: wf th2 mem2>> /\
      <<FUTURE: Memory.future mem1 mem2>>.
    Proof.
      inv STEP.
      - eapply internal_step_future; eauto.
      - inv WF1. ss. splits; ss. reflexivity.
    Qed.

    Lemma step_disjoint
          e th1 mem1 th2 mem2 mem_o
          (STEP: step e th1 mem1 th2 mem2)
          (DISJOINT1: Memory.disjoint th1.(promise) mem_o)
          (WF1: wf th1 mem1)
          (LE1: Memory.le mem_o mem1):
      <<DISJOINT2: Memory.disjoint th2.(promise) mem_o>> /\
      <<LE2: Memory.le mem_o mem2>>.
    Proof.
      inv STEP; ss.
      eapply internal_step_disjoint; eauto.
    Qed.

    Lemma _internal_step_future
          thm1 thm2
          (STEP: _internal_step thm1 thm2)
          (WF1: wf thm1.(fst) thm1.(snd)):
      <<WF2: wf thm2.(fst) thm2.(snd)>> /\
      <<FUTURE: Memory.future thm1.(snd) thm2.(snd)>>.
    Proof.
      destruct thm1, thm2. ss. inv STEP.
      eapply internal_step_future; eauto.
    Qed.

    Lemma _internal_step_disjoint
          thm1 thm2 mem_o
          (STEP: _internal_step thm1 thm2)
          (DISJOINT1: Memory.disjoint thm1.(fst).(promise) mem_o)
          (WF1: wf thm1.(fst) thm1.(snd))
          (LE1: Memory.le mem_o thm1.(snd)):
      <<DISJOINT2: Memory.disjoint thm2.(fst).(promise) mem_o>> /\
      <<LE2: Memory.le mem_o thm2.(snd)>>.
    Proof.
      destruct thm1, thm2. ss. inv STEP.
      eapply internal_step_disjoint; eauto.
    Qed.

    Lemma rtc_internal_step_future
          thm1 thm2
          (STEP: rtc _internal_step thm1 thm2)
          (WF1: wf thm1.(fst) thm1.(snd)):
      <<WF2: wf thm2.(fst) thm2.(snd)>> /\
      <<FUTURE: Memory.future thm1.(snd) thm2.(snd)>>.
    Proof.
      revert WF1. induction STEP; s; i.
      - splits; auto. reflexivity.
      - exploit _internal_step_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; auto. etransitivity; eauto.
    Qed.

    Lemma rtc_internal_step_disjoint
          thm1 thm2 mem_o
          (STEP: rtc _internal_step thm1 thm2)
          (DISJOINT1: Memory.disjoint thm1.(fst).(promise) mem_o)
          (WF1: wf thm1.(fst) thm1.(snd))
          (LE1: Memory.le mem_o thm1.(snd)):
      <<DISJOINT2: Memory.disjoint thm2.(fst).(promise) mem_o>> /\
      <<LE2: Memory.le mem_o thm2.(snd)>>.
    Proof.
      revert WF1 LE1 DISJOINT1. induction STEP; ss; i.
      exploit _internal_step_future; eauto. i. des.
      exploit _internal_step_disjoint; eauto. i. des.
      exploit IHSTEP; eauto.
    Qed.
  End Thread.
End Thread.
