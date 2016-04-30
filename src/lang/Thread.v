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

  Inductive silent_step (th1:t) (mem1:Memory.t): forall (th2:t) (mem2:Memory.t), Prop :=
  | step_silent
      commit2
      (COMMIT: Commit.le th1.(commit) commit2)
      (COMMIT_WF: Commit.wf commit2 mem1):
      silent_step th1 mem1
                  (mk commit2 th1.(promise)) mem1
  .

  Inductive promise_step (th1:t) (mem1:Memory.t): forall (th2:t) (mem2:Memory.t), Prop :=
  | step_promise
      loc from ts msg commit2 promise2 mem2
      (COMMIT: Commit.le th1.(commit) commit2)
      (COMMIT_WF: Commit.wf commit2 mem2)
      (MEMORY: Memory.promise th1.(promise) mem1 loc from ts msg promise2 mem2):
      promise_step th1 mem1
                   (mk commit2 promise2) mem2
  .

  Inductive memory_step (th1:t) (mem1:Memory.t): forall (e:MemEvent.t) (th2:t) (mem2:Memory.t), Prop :=
  | step_read
      loc val ts released ord commit2
      (COMMIT: Commit.read th1.(commit) loc ts released ord commit2)
      (COMMIT_WF: Commit.wf commit2 mem1)
      (GET: Memory.get loc ts mem1 = Some (Message.mk val released))
      (GET_PROMISE: Memory.get loc ts th1.(promise) = None):
      memory_step th1 mem1
                  (MemEvent.read loc val ord)
                  (mk commit2 th1.(promise)) mem1
  | step_write
      loc val from ts released ord commit2 promise2 mem2
      (COMMIT: Commit.write th1.(commit) loc ts released ord commit2)
      (COMMIT_WF: Commit.wf commit2 mem2)
      (MEMORY: Memory.write th1.(promise) mem1 loc from ts (Message.mk val released) ord promise2 mem2):
      memory_step th1 mem1
                  (MemEvent.write loc val ord)
                  (mk commit2 promise2) mem2
  | step_update
      loc valr tsr releasedr valw tsw releasedw ord commit2 commit3 promise3 mem3
      (COMMIT_READ: Commit.read th1.(commit) loc tsr releasedr ord commit2)
      (COMMIT_WRITE: Commit.write commit2 loc tsw releasedw ord commit3)
      (COMMIT_WF: Commit.wf commit3 mem3)
      (RELEASED: Snapshot.le releasedr releasedw)
      (GET: Memory.get loc tsr mem1 = Some (Message.mk valr releasedr))
      (GET_PROMISE: Memory.get loc tsr th1.(promise) = None)
      (MEMORY: Memory.write th1.(promise) mem1 loc tsr tsw (Message.mk valw releasedw) ord promise3 mem3):
      memory_step th1 mem1
                  (MemEvent.update loc valr valw ord)
                  (mk commit3 promise3) mem3
  | step_fence
      ord commit2
      (COMMIT: Commit.fence th1.(commit) ord commit2)
      (COMMIT_WF: Commit.wf commit2 mem1)
      (MEMORY: Memory.fence th1.(promise) ord):
      memory_step th1 mem1
                  (MemEvent.fence ord)
                  (mk commit2 th1.(promise)) mem1
  .

  Lemma silent_step_future th1 mem1 th2 mem2
        (STEP: silent_step th1 mem1 th2 mem2)
        (WF1: wf th1 mem1):
    <<WF2: wf th2 mem2>> /\
    <<FUTURE: Memory.future mem1 mem2>>.
  Proof.
    inv WF1. inv STEP. splits; ss. reflexivity.
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

  Lemma memory_step_future th1 mem1 e th2 mem2
        (STEP: memory_step th1 mem1 e th2 mem2)
        (WF1: wf th1 mem1):
    <<WF2: wf th2 mem2>> /\
    <<FUTURE: Memory.future mem1 mem2>>.
  Proof.
    inv WF1. inv STEP; try by splits; ss; reflexivity.
    - exploit Memory.write_future; eauto. i. des. ss.
    - exploit Memory.write_future; eauto. i. des. ss.
  Qed.

  Lemma silent_step_disjoint
        th1 mem1 th2 mem2 th
        (STEP: silent_step th1 mem1 th2 mem2)
        (WF1: wf th1 mem1)
        (DISJOINT1: disjoint th1 th)
        (WF: wf th mem1):
    <<DISJOINT2: disjoint th2 th>> /\
    <<WF: wf th mem2>>.
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

  Lemma memory_step_disjoint
        th1 mem1 th2 e mem2 th
        (STEP: memory_step th1 mem1 e th2 mem2)
        (WF1: wf th1 mem1)
        (DISJOINT1: disjoint th1 th)
        (WF: wf th mem1):
    <<DISJOINT2: disjoint th2 th>> /\
    <<WF: wf th mem2>>.
  Proof.
    inv WF1. inv DISJOINT1. inv WF. inv STEP; ss.
    - exploit Memory.write_future; try apply MEMORY1; eauto. i. des.
      exploit Memory.write_disjoint; try apply MEMORY1; eauto. i. des.
      splits; ss. econs; ss.
      eapply Commit.future_wf; eauto.
    - exploit Memory.write_future; try apply MEMORY1; eauto. i. des.
      exploit Memory.write_disjoint; try apply MEMORY1; eauto. i. des.
      splits; ss. econs; ss.
      eapply Commit.future_wf; eauto.
  Qed.

  Lemma fence_relaxed
        th mem
        (WF: wf th mem):
    memory_step th mem (MemEvent.fence Ordering.relaxed) th mem.
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
        (STEP: Local.promise_step e1.(thread) e1.(memory) th2 mem2):
        internal_step e1 (mk e1.(state) th2 mem2)
    | step_silent
        st2 th2 mem2
        (STATE: lang.(Language.step) e1.(state) None st2)
        (STEP: Local.silent_step e1.(thread) e1.(memory) th2 mem2):
        internal_step e1 (mk st2 th2 mem2)
    | step_memory
        e st2 th2 mem2
        (STATE: lang.(Language.step) e1.(state) (Some (ThreadEvent.mem e)) st2)
        (STEP: Local.memory_step e1.(thread) e1.(memory) e th2 mem2):
        internal_step e1 (mk st2 th2 mem2)
    .

    Inductive external_step (e1:t) (e:Event.t): forall (e2:t), Prop :=
    | step_syscall
        st2 th2 mem2
        (STATE: lang.(Language.step) e1.(state) (Some (ThreadEvent.syscall e)) st2)
        (STEP: Local.silent_step e1.(thread) e1.(memory) th2 mem2):
        external_step e1 e (mk st2 th2 mem2)
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
      inv WF1. inv STEP.
      - exploit Local.promise_step_future; eauto. i. des.
        splits; ss.
      - exploit Local.silent_step_future; eauto. i. des.
        splits; ss.
      - exploit Local.memory_step_future; eauto. i. des.
        splits; ss.
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
      inv WF1. inv STEP.
      exploit Local.silent_step_future; eauto. i. des.
      splits; ss.
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
      - exploit Local.silent_step_future; eauto. i. des.
        eapply Local.silent_step_disjoint; eauto.
      - exploit Local.memory_step_future; eauto. i. des.
        eapply Local.memory_step_disjoint; eauto.
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
      inv STEP.
      exploit Local.silent_step_future; eauto. i. des.
      eapply Local.silent_step_disjoint; eauto.
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
