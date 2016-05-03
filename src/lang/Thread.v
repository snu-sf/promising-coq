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
Require Import Commit.

Set Implicit Arguments.


Module Local.
  Structure t := mk {
    commit: Commit.t;
    promise: Memory.t;
  }.

  Definition init :=
    mk Commit.init
       Memory.bot.

  Inductive is_terminal (th:t): Prop :=
  | is_terminal_intro
      (PROMISE: th.(promise) = Memory.bot)
  .

  Inductive wf (th:t) (mem:Memory.t): Prop :=
  | wf_intro
      (COMMIT: Commit.wf th.(commit) mem)
      (PROMISE: Memory.le th.(promise) mem)
      (MEMORY: Memory.wf mem)
  .

  Inductive disjoint (th1 th2:t): Prop :=
  | disjoint_intro
      (PROMISE: Memory.disjoint th1.(promise) th2.(promise))
  .

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    econs. symmetry. apply H.
  Qed.

  Inductive silent_step (th1:t) (mem1:Memory.t): forall (th2:t), Prop :=
  | step_silent
      commit2
      (COMMIT: Commit.le th1.(commit) commit2)
      (COMMIT_WF: Commit.wf commit2 mem1):
      silent_step th1 mem1 (mk commit2 th1.(promise))
  .

  Inductive promise_step (th1:t) (mem1:Memory.t): forall (th2:t) (mem2:Memory.t), Prop :=
  | step_promise
      loc from ts msg commit2 promise2 mem2
      (COMMIT: Commit.le th1.(commit) commit2)
      (COMMIT_WF: Commit.wf commit2 mem2)
      (MEMORY: Memory.promise th1.(promise) mem1 loc from ts msg promise2 mem2):
      promise_step th1 mem1 (mk commit2 promise2) mem2
  .

  Inductive read_step (th1:t) (mem1:Memory.t) (loc:Loc.t) (ts:Time.t) (val:Const.t) (released:Snapshot.t) (ord:Ordering.t): forall (th2:t), Prop :=
  | step_read
      commit2
      (COMMIT: Commit.read th1.(commit) loc ts released ord commit2)
      (COMMIT_WF: Commit.wf commit2 mem1)
      (GET: Memory.get loc ts mem1 = Some (Message.mk val released))
      (GET_PROMISE: Memory.get loc ts th1.(promise) = None):
      read_step th1 mem1 loc ts val released ord (mk commit2 th1.(promise))
  .

  Inductive write_step (th1:t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (released:Snapshot.t) (ord:Ordering.t): forall (th2:t) (mem2:Memory.t), Prop :=
  | step_write
      commit2 promise2 mem2
      (COMMIT: Commit.write th1.(commit) loc to released ord commit2)
      (COMMIT_WF: Commit.wf commit2 mem2)
      (MEMORY: Memory.write th1.(promise) mem1 loc from to (Message.mk val released) ord promise2 mem2):
      write_step th1 mem1 loc from to val released ord (mk commit2 promise2) mem2
  .

  Inductive fence_step (th1:t) (mem1:Memory.t) (ord:Ordering.t): forall (th2:t), Prop :=
  | step_fence
      commit2
      (COMMIT: Commit.fence th1.(commit) ord commit2)
      (COMMIT_WF: Commit.wf commit2 mem1)
      (MEMORY: Memory.fence th1.(promise) ord):
      fence_step th1 mem1 ord (mk commit2 th1.(promise))
  .

  Lemma silent_step_future th1 mem1 th2
        (STEP: silent_step th1 mem1 th2)
        (WF1: wf th1 mem1):
    wf th2 mem1.
  Proof.
    inv WF1. inv STEP. ss.
  Qed.

  Lemma promise_step_future th1 mem1 th2 mem2
        (STEP: promise_step th1 mem1 th2 mem2)
        (WF1: wf th1 mem1):
    <<WF2: wf th2 mem2>> /\
    <<FUTURE: Memory.future mem1 mem2>>.
  Proof.
    inv WF1. inv STEP.
    exploit Memory.promise_future; eauto. i. des.
    splits; ss.
  Qed.

  Lemma read_step_future th1 mem1 loc ts val released ord th2
        (STEP: read_step th1 mem1 loc ts val released ord th2)
        (WF1: wf th1 mem1):
    wf th2 mem1.
  Proof.
    inv WF1. inv STEP. ss.
  Qed.

  Lemma write_step_future th1 mem1 loc from to val released ord th2 mem2
        (STEP: write_step th1 mem1 loc from to val released ord th2 mem2)
        (WF1: wf th1 mem1):
    <<WF2: wf th2 mem2>> /\
    <<FUTURE: Memory.future mem1 mem2>>.
  Proof.
    inv WF1. inv STEP.
    exploit Memory.write_future; eauto. i. des.
    splits; ss.
  Qed.

  Lemma fence_step_future th1 mem1 ord th2
        (STEP: fence_step th1 mem1 ord th2)
        (WF1: wf th1 mem1):
    wf th2 mem1.
  Proof.
    inv WF1. inv STEP. ss.
  Qed.

  Lemma silent_step_disjoint
        th1 mem1 th2 th
        (STEP: silent_step th1 mem1 th2)
        (WF1: wf th1 mem1)
        (DISJOINT1: disjoint th1 th)
        (WF: wf th mem1):
    disjoint th2 th.
  Proof.
    inv WF1. inv DISJOINT1. inv WF. inv STEP. ss.
  Qed.

  Lemma promise_step_disjoint
        th1 mem1 th2 mem2 th
        (STEP: promise_step th1 mem1 th2 mem2)
        (WF1: wf th1 mem1)
        (DISJOINT1: disjoint th1 th)
        (WF: wf th mem1):
    <<DISJOINT2: disjoint th2 th>> /\
    <<WF: wf th mem2>>.
  Proof.
    inv WF1. inv DISJOINT1. inv WF. inv STEP.
    exploit Memory.promise_future; try apply MEMORY1; eauto. i. des.
    exploit Memory.promise_disjoint; try apply MEMORY1; eauto. i. des.
    splits; ss. econs; ss.
    eapply Commit.future_wf; eauto.
  Qed.

  Lemma read_step_disjoint
        th1 mem1 th2 loc ts val released ord th
        (STEP: read_step th1 mem1 loc ts val released ord th2)
        (WF1: wf th1 mem1)
        (DISJOINT1: disjoint th1 th)
        (WF: wf th mem1):
    disjoint th2 th.
  Proof.
    inv WF1. inv DISJOINT1. inv WF. inv STEP. ss.
  Qed.

  Lemma write_step_disjoint
        th1 mem1 th2 loc from to val released ord mem2 th
        (STEP: write_step th1 mem1 loc from to val released ord th2 mem2)
        (WF1: wf th1 mem1)
        (DISJOINT1: disjoint th1 th)
        (WF: wf th mem1):
    <<DISJOINT2: disjoint th2 th>> /\
    <<WF: wf th mem2>>.
  Proof.
    inv WF1. inv DISJOINT1. inv WF. inv STEP.
    exploit Memory.write_future; try apply MEMORY1; eauto. i. des.
    exploit Memory.write_disjoint; try apply MEMORY1; eauto. i. des.
    splits; ss. econs; ss.
    eapply Commit.future_wf; eauto.
  Qed.

  Lemma fence_step_disjoint
        th1 mem1 th2 ord th
        (STEP: fence_step th1 mem1 ord th2)
        (WF1: wf th1 mem1)
        (DISJOINT1: disjoint th1 th)
        (WF: wf th mem1):
    disjoint th2 th.
  Proof.
    inv WF1. inv DISJOINT1. inv WF. inv STEP. ss.
  Qed.

  Lemma fence_relaxed
        th mem
        (WF: wf th mem):
    fence_step th mem Ordering.relaxed th.
  Proof.
    destruct th. econs; s.
    - econs; ss. reflexivity.
    - apply WF.
    - econs. ss.
  Qed.
End Local.

Module Thread.
  Section Thread.
    Variable (lang:Language.t).

    Structure t := mk {
      state: lang.(Language.state);
      thread: Local.t;
      memory: Memory.t;
    }.

    Inductive internal_step (e1:t): forall (e2:t), Prop :=
    | step_promise
        th2 mem2
        (LOCAL: Local.promise_step e1.(thread) e1.(memory) th2 mem2):
        internal_step e1 (mk e1.(state) th2 mem2)
    | step_silent
        st2 th2
        (STATE: lang.(Language.step) e1.(state) None st2)
        (LOCAL: Local.silent_step e1.(thread) e1.(memory) th2):
        internal_step e1 (mk st2 th2 e1.(memory))
    | step_read
        st2 loc ts val released ord th2
        (STATE: lang.(Language.step) e1.(state) (Some (ThreadEvent.mem (MemEvent.read loc val ord))) st2)
        (LOCAL: Local.read_step e1.(thread) e1.(memory) loc ts val released ord th2):
        internal_step e1 (mk st2 th2 e1.(memory))
    | step_write
        st2 loc from to val released ord th2 mem2
        (STATE: lang.(Language.step) e1.(state) (Some (ThreadEvent.mem (MemEvent.write loc val ord))) st2)
        (LOCAL: Local.write_step e1.(thread) e1.(memory) loc from to val released ord th2 mem2):
        internal_step e1 (mk st2 th2 mem2)
    | step_update
        st3 loc ord
        tsr valr releasedr th2
        tsw valw releasedw th3 mem3
        (STATE: lang.(Language.step) e1.(state) (Some (ThreadEvent.mem (MemEvent.update loc valr valw ord))) st3)
        (LOCAL1: Local.read_step e1.(thread) e1.(memory) loc tsr valr releasedr ord th2)
        (LOCAL2: Local.write_step th2 e1.(memory) loc tsr tsw valw releasedw ord th3 mem3)
        (RELEASE: Snapshot.le releasedr releasedw):
        internal_step e1 (mk st3 th3 mem3)
    | step_fence
        st2 ord th2
        (STATE: lang.(Language.step) e1.(state) (Some (ThreadEvent.mem (MemEvent.fence ord))) st2)
        (LOCAL: Local.fence_step e1.(thread) e1.(memory) ord th2):
        internal_step e1 (mk st2 th2 e1.(memory))
    .

    Inductive external_step (e1:t) (e:Event.t): forall (e2:t), Prop :=
    | step_syscall
        st2 th2
        (STATE: lang.(Language.step) e1.(state) (Some (ThreadEvent.syscall e)) st2)
        (LOCAL: Local.silent_step e1.(thread) e1.(memory) th2):
        external_step e1 e (mk st2 th2 e1.(memory))
    .

    Inductive step (e1:t): forall (e:option Event.t) (e2:t), Prop :=
    | step_internal
        e2
        (STEP: internal_step e1 e2):
        step e1 None e2
    | step_external
        e e2
        (STEP: external_step e1 e e2):
        step e1 (Some e) e2
    .

    Definition consistent st1 th1 mem: Prop :=
      forall mem1
        (FUTURE: Memory.future mem mem1)
        (WF: Local.wf th1 mem1),
      exists e2,
        <<STEPS: rtc internal_step (mk st1 th1 mem1) e2>> /\
        <<PROMISE: e2.(thread).(Local.promise) = Memory.bot>>.

    Lemma internal_step_future e1 e2
          (STEP: internal_step e1 e2)
          (WF1: Local.wf e1.(thread) e1.(memory)):
      <<WF2: Local.wf e2.(thread) e2.(memory)>> /\
      <<FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP; s.
      - exploit Local.promise_step_future; eauto.
      - exploit Local.silent_step_future; eauto. i. splits; ss. reflexivity.
      - exploit Local.read_step_future; eauto. i. splits; ss. reflexivity.
      - exploit Local.write_step_future; eauto.
      - exploit Local.read_step_future; eauto. i.
        exploit Local.write_step_future; eauto.
      - exploit Local.fence_step_future; eauto. i. splits; ss. reflexivity.
    Qed.

    Lemma rtc_internal_step_future e1 e2
          (STEP: rtc internal_step e1 e2)
          (WF1: Local.wf e1.(thread) e1.(memory)):
      <<WF2: Local.wf e2.(thread) e2.(memory)>> /\
      <<FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      revert WF1. induction STEP.
      - i. splits; ss. reflexivity.
      - i.
        exploit internal_step_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss. etransitivity; eauto.
    Qed.

    Lemma external_step_future e1 e e2
          (STEP: external_step e1 e e2)
          (WF1: Local.wf e1.(thread) e1.(memory)):
      <<WF2: Local.wf e2.(thread) e2.(memory)>> /\
      <<FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP. exploit Local.silent_step_future; eauto. i.
      splits; ss. reflexivity.
    Qed.

    Lemma step_future e1 e e2
          (STEP: step e1 e e2)
          (WF1: Local.wf e1.(thread) e1.(memory)):
      <<WF2: Local.wf e2.(thread) e2.(memory)>> /\
      <<FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP.
      - apply internal_step_future; auto.
      - eapply external_step_future; eauto.
    Qed.

    Lemma internal_step_disjoint e1 e2 th
        (STEP: internal_step e1 e2)
        (WF1: Local.wf e1.(thread) e1.(memory))
        (DISJOINT1: Local.disjoint e1.(thread) th)
        (WF: Local.wf th e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(thread) th>> /\
      <<WF: Local.wf th e2.(memory)>>.
    Proof.
      inv STEP.
      - exploit Local.promise_step_future; eauto. i. des.
        eapply Local.promise_step_disjoint; eauto.
      - exploit Local.silent_step_future; eauto. i.
        exploit Local.silent_step_disjoint; eauto.
      - exploit Local.read_step_future; eauto. i.
        exploit Local.read_step_disjoint; eauto.
      - exploit Local.write_step_future; eauto. i. des.
        exploit Local.write_step_disjoint; eauto.
      - exploit Local.read_step_future; eauto. i.
        exploit Local.read_step_disjoint; eauto. i.
        exploit Local.write_step_future; eauto. i. des.
        exploit Local.write_step_disjoint; eauto.
      - exploit Local.fence_step_future; eauto. i.
        exploit Local.fence_step_disjoint; eauto.
    Qed.

    Lemma rtc_internal_step_disjoint e1 e2 th
        (STEP: rtc internal_step e1 e2)
        (WF1: Local.wf e1.(thread) e1.(memory))
        (DISJOINT1: Local.disjoint e1.(thread) th)
        (WF: Local.wf th e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(thread) th>> /\
      <<WF: Local.wf th e2.(memory)>>.
    Proof.
      revert WF1 DISJOINT1 WF. induction STEP; eauto. i.
      exploit internal_step_future; eauto. i. des.
      exploit internal_step_disjoint; eauto. i. des.
      eapply IHSTEP; eauto.
    Qed.

    Lemma external_step_disjoint e1 e e2 th
        (STEP: external_step e1 e e2)
        (WF1: Local.wf e1.(thread) e1.(memory))
        (DISJOINT1: Local.disjoint e1.(thread) th)
        (WF: Local.wf th e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(thread) th>> /\
      <<WF: Local.wf th e2.(memory)>>.
    Proof.
      inv STEP. exploit Local.silent_step_future; eauto. i.
      exploit Local.silent_step_disjoint; eauto.
    Qed.

    Lemma step_disjoint e1 e e2 th
        (STEP: step e1 e e2)
        (WF1: Local.wf e1.(thread) e1.(memory))
        (DISJOINT1: Local.disjoint e1.(thread) th)
        (WF: Local.wf th e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(thread) th>> /\
      <<WF: Local.wf th e2.(memory)>>.
    Proof.
      inv STEP.
      - eapply internal_step_disjoint; eauto.
      - eapply external_step_disjoint; eauto.
    Qed.
  End Thread.
End Thread.
