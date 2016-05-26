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
Require Import Memory.
Require Import Commit.

Set Implicit Arguments.


Module Local.
  Structure t := mk {
    commit: Commit.t;
    promises: Promises.t;
  }.

  Definition init := mk Commit.elt Promises.bot.

  Inductive is_terminal (lc:t): Prop :=
  | is_terminal_intro
      (PROMISES: lc.(promises) = Promises.bot)
  .

  Inductive wf (lc:t) (mem:Memory.t): Prop :=
  | wf_intro
      (COMMIT_WF: Commit.wf lc.(commit))
      (COMMIT_CLOSED: Commit.closed lc.(commit) mem)
      (PROMISES: Memory.closed_promises lc.(promises) mem)
      (MEMORY: Memory.closed mem)
  .

  Inductive disjoint (lc1 lc2:t): Prop :=
  | disjoint_intro
      (PROMISES: Promises.disjoint lc1.(promises) lc2.(promises))
  .

  Global Program Instance disjoint_Symmetric: Symmetric disjoint.
  Next Obligation.
    econs. symmetry. apply H.
  Qed.

  Inductive promise_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (released:Capability.t): forall (lc2:t) (mem2:Memory.t), Prop :=
  | step_promise
      commit2 promises2 mem2
      (PROMISE: Memory.promise lc1.(promises) mem1 loc from to (Message.mk val released) promises2 mem2)
      (COMMIT: Commit.le lc1.(commit) commit2)
      (COMMIT_WF: Commit.wf commit2)
      (COMMIT_CLOSED: Commit.closed commit2 mem2):
      promise_step lc1 mem1 loc from to val released (mk commit2 promises2) mem2
  .

  Inductive silent_step (lc1:t) (mem1:Memory.t): forall (lc2:t), Prop :=
  | step_silent
      commit2
      (COMMIT: Commit.le lc1.(commit) commit2)
      (COMMIT_WF: Commit.wf commit2)
      (COMMIT_CLOSED: Commit.closed commit2 mem1):
      silent_step lc1 mem1 (mk commit2 lc1.(promises))
  .

  Inductive read_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (to:Time.t) (val:Const.t) (released:Capability.t) (ord:Ordering.t): forall (lc2:t), Prop :=
  | step_read
      from
      commit2
      (GET: Memory.get loc to mem1 = Some (from, Message.mk val released))
      (COMMIT: Commit.read lc1.(commit) loc to released ord commit2)
      (COMMIT_WF: Commit.wf commit2)
      (COMMIT_CLOSED: Commit.closed commit2 mem1):
      read_step lc1 mem1 loc to val released ord (mk commit2 lc1.(promises))
  .

  Inductive fulfill_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (releasedc releasedm:Capability.t) (ord:Ordering.t): forall (lc2:t), Prop :=
  | step_fulfill
      commit2 promises2
      (FULFILL: Memory.fulfill lc1.(promises) mem1 loc from to (Message.mk val releasedm) promises2)
      (COMMIT: Commit.write lc1.(commit) loc to releasedc ord commit2)
      (COMMIT_WF: Commit.wf commit2)
      (COMMIT_CLOSED: Commit.closed commit2 mem1):
      fulfill_step lc1 mem1 loc from to val releasedc releasedm ord (mk commit2 promises2)
  .

  Inductive write_step (lc1:t) (mem1:Memory.t) (loc:Loc.t) (from to:Time.t) (val:Const.t) (releasedc releasedm:Capability.t) (ord:Ordering.t): forall (lc2:t) (mem2:Memory.t), Prop :=
  | step_write_fulfill
      lc2
      (FULFILL: fulfill_step lc1 mem1 loc from to val releasedc releasedm ord lc2)
      (RELEASE: Ordering.le Ordering.acqrel ord -> lc1.(promises) loc = DOSet.empty):
      write_step lc1 mem1 loc from to val releasedc releasedm ord lc2 mem1
  | step_write_add
      lc2 mem2 lc3
      (PROMISE: promise_step lc1 mem1 loc from to val releasedm lc2 mem2)
      (FULFILL: fulfill_step lc2 mem2 loc from to val releasedc releasedm ord lc3)
      (RELEASE: Ordering.le Ordering.acqrel ord -> lc1.(promises) loc = DOSet.empty):
      write_step lc1 mem1 loc from to val releasedc releasedm ord lc3 mem2
  .

  Inductive fence_step (lc1:t) (mem1:Memory.t) (ordr ordw:Ordering.t): forall (lc2:t), Prop :=
  | step_fence
      commit2 commit3
      (READ: Commit.read_fence lc1.(commit) ordr commit2)
      (WRITE: Commit.write_fence commit2 ordw commit3)
      (RELEASE: Ordering.le Ordering.acqrel ordw -> lc1.(promises) = Promises.bot)
      (COMMIT_WF: Commit.wf commit3)
      (COMMIT_CLOSED: Commit.closed commit3 mem1):
      fence_step lc1 mem1 ordr ordw (mk commit3 lc1.(promises))
  .

  Lemma future_wf lc mem1 mem1'
        (WF: wf lc mem1)
        (FUTURE: Memory.future mem1 mem1')
        (INTACT: Memory.intact lc.(promises) mem1 mem1'):
    wf lc mem1'.
  Proof.
    inv WF. econs; eauto.
    - eapply Commit.future_closed; eauto.
    - eapply Memory.future_closed_promises; eauto.
    - eapply Memory.future_closed; eauto.
  Qed.

  Lemma future_read_step lc1 mem1 mem1' loc ts val released ord lc2
        (FUTURE: Memory.future mem1 mem1')
        (STEP: read_step lc1 mem1 loc ts val released ord lc2):
    read_step lc1 mem1' loc ts val released ord lc2.
  Proof.
    inv STEP. exploit Memory.future_get; eauto. i. des.
    econs; eauto. eapply Commit.future_closed; eauto.
  Qed.

  Lemma future_fulfill_step lc1 mem1 mem1' loc from to val releasedc releasedm ord lc2
        (FUTURE: Memory.future mem1 mem1')
        (INTACT: Memory.intact lc1.(promises) mem1 mem1')
        (STEP: fulfill_step lc1 mem1 loc from to val releasedc releasedm ord lc2):
    fulfill_step lc1 mem1' loc from to val releasedc releasedm ord lc2.
  Proof.
    inv STEP. econs; eauto.
    - eapply Memory.fulfill_mon; eauto.
    - eapply Commit.future_closed; eauto.
  Qed.

  Lemma future_fence_step lc1 mem1 mem1' ordr ordw lc2
        (FUTURE: Memory.future mem1 mem1')
        (STEP: fence_step lc1 mem1 ordr ordw lc2):
    fence_step lc1 mem1' ordr ordw lc2.
  Proof.
    inv STEP. econs; eauto.
    eapply Commit.future_closed; eauto.
  Qed.

  Lemma promise_step_future lc1 mem1 loc from to val released lc2 mem2
        (STEP: promise_step lc1 mem1 loc from to val released lc2 mem2)
        (WF1: wf lc1 mem1):
    <<WF2: wf lc2 mem2>> /\
    <<FUTURE: Memory.future mem1 mem2>>.
  Proof.
    inv WF1. inv STEP.
    exploit Memory.promise_future; eauto. i. des.
    splits; ss.
  Qed.

  Lemma silent_step_future lc1 mem1 lc2
        (STEP: silent_step lc1 mem1 lc2)
        (WF1: wf lc1 mem1):
    wf lc2 mem1.
  Proof.
    inv WF1. inv STEP. ss.
  Qed.

  Lemma read_step_future lc1 mem1 loc ts val released ord lc2
        (STEP: read_step lc1 mem1 loc ts val released ord lc2)
        (WF1: wf lc1 mem1):
    wf lc2 mem1.
  Proof.
    inv WF1. inv STEP. ss.
  Qed.

  Lemma fulfill_step_future lc1 mem1 loc from to val releasedc releasedm ord lc2
        (STEP: fulfill_step lc1 mem1 loc from to val releasedc releasedm ord lc2)
        (WF1: wf lc1 mem1):
    wf lc2 mem1.
  Proof.
    inv WF1. inv STEP. econs; eauto. s.
    eapply Memory.fulfill_future; eauto.
  Qed.

  Lemma write_step_future lc1 mem1 loc from to val releasedc releasedm ord lc2 mem2
        (STEP: write_step lc1 mem1 loc from to val releasedc releasedm ord lc2 mem2)
        (WF1: wf lc1 mem1):
    <<WF2: wf lc2 mem2>> /\
    <<FUTURE: Memory.future mem1 mem2>>.
  Proof.
    inv STEP.
    - exploit fulfill_step_future; eauto. i. splits; ss. reflexivity.
    - exploit promise_step_future; eauto. i. des.
      exploit fulfill_step_future; eauto.
  Qed.

  Lemma fence_step_future lc1 mem1 ordr ordw lc2
        (STEP: fence_step lc1 mem1 ordr ordw lc2)
        (WF1: wf lc1 mem1):
    wf lc2 mem1.
  Proof.
    inv WF1. inv STEP. ss.
  Qed.

  Lemma promise_step_disjoint
        lc1 mem1 loc from to val released lc2 mem2 lc
        (STEP: promise_step lc1 mem1 loc from to val released lc2 mem2)
        (WF1: wf lc1 mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<INTACT: Memory.intact lc.(Local.promises) mem1 mem2>> /\
    <<WF: wf lc mem2>>.
  Proof.
    inv WF1. inv DISJOINT1. inversion WF. inv STEP.
    exploit Memory.promise_future; try apply PROMISE; eauto. i. des.
    exploit Memory.promise_disjoint; try apply PROMISE; eauto. i. des.
    splits; ss. eapply Local.future_wf; eauto.
  Qed.

  Lemma silent_step_disjoint
        lc1 mem1 lc2 lc
        (STEP: silent_step lc1 mem1 lc2)
        (WF1: wf lc1 mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    disjoint lc2 lc.
  Proof.
    inv WF1. inv DISJOINT1. inv WF. inv STEP. ss.
  Qed.

  Lemma read_step_disjoint
        lc1 mem1 lc2 loc ts val released ord lc
        (STEP: read_step lc1 mem1 loc ts val released ord lc2)
        (WF1: wf lc1 mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    disjoint lc2 lc.
  Proof.
    inv WF1. inv DISJOINT1. inv WF. inv STEP. ss.
  Qed.

  Lemma fulfill_step_disjoint
        lc1 mem1 lc2 loc from to val releasedc releasedm ord lc
        (STEP: fulfill_step lc1 mem1 loc from to val releasedc releasedm ord lc2)
        (DISJOINT1: disjoint lc1 lc):
    disjoint lc2 lc.
  Proof.
    inv DISJOINT1. inv STEP. inv FULFILL.
    econs. s. econs. i. eapply PROMISES; try apply RHS; eauto.
    apply Promises.unset_inv in LHS. des. auto.
  Qed.

  Lemma write_step_disjoint
        lc1 mem1 lc2 loc from to val releasedc releasedm ord mem2 lc
        (STEP: write_step lc1 mem1 loc from to val releasedc releasedm ord lc2 mem2)
        (WF1: wf lc1 mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    <<DISJOINT2: disjoint lc2 lc>> /\
    <<INTACT: Memory.intact lc.(Local.promises) mem1 mem2>> /\
    <<WF: wf lc mem2>>.
  Proof.
    inv STEP.
    - exploit fulfill_step_disjoint; eauto. i.
      splits; eauto. reflexivity.
    - exploit promise_step_future; eauto. i. des.
      exploit promise_step_disjoint; eauto. i. des.
      exploit fulfill_step_disjoint; eauto.
  Qed.

  Lemma fence_step_disjoint
        lc1 mem1 lc2 ordr ordw lc
        (STEP: fence_step lc1 mem1 ordr ordw lc2)
        (WF1: wf lc1 mem1)
        (DISJOINT1: disjoint lc1 lc)
        (WF: wf lc mem1):
    disjoint lc2 lc.
  Proof.
    inv WF1. inv DISJOINT1. inv WF. inv STEP. ss.
  Qed.
End Local.

Module Thread.
  Section Thread.
    Variable (lang:Language.t).

    Structure t := mk {
      state: lang.(Language.state);
      local: Local.t;
      memory: Memory.t;
    }.

    Inductive promise_step (e1:t): forall (e2:t), Prop :=
    | promise_step_intro
        loc from to val released lc2 mem2
        (LOCAL: Local.promise_step e1.(local) e1.(memory) loc from to val released lc2 mem2):
        promise_step e1 (mk e1.(state) lc2 mem2)
    .

    Inductive internal_step (e1:t): forall (e2:t), Prop :=
    | step_silent
        st2 lc2
        (STATE: lang.(Language.step) None e1.(state) st2)
        (LOCAL: Local.silent_step e1.(local) e1.(memory) lc2):
        internal_step e1 (mk st2 lc2 e1.(memory))
    | step_read
        st2 loc ts val released ord lc2
        (STATE: lang.(Language.step) (Some (ThreadEvent.mem (MemEvent.read loc val ord))) e1.(state) st2)
        (LOCAL: Local.read_step e1.(local) e1.(memory) loc ts val released ord lc2):
        internal_step e1 (mk st2 lc2 e1.(memory))
    | step_write
        st2 loc from to val released ord lc2 mem2
        (STATE: lang.(Language.step) (Some (ThreadEvent.mem (MemEvent.write loc val ord))) e1.(state) st2)
        (LOCAL: Local.write_step e1.(local) e1.(memory) loc from to val released released ord lc2 mem2):
        internal_step e1 (mk st2 lc2 mem2)
    | step_update
        st3 loc ordr ordw
        tsr valr releasedr lc2
        tsw valw releasedw lc3 mem3
        (STATE: lang.(Language.step) (Some (ThreadEvent.mem (MemEvent.update loc valr valw ordr ordw))) e1.(state) st3)
        (LOCAL1: Local.read_step e1.(local) e1.(memory) loc tsr valr releasedr ordr lc2)
        (LOCAL2: Local.write_step lc2 e1.(memory) loc tsr tsw valw releasedw (Capability.join releasedr releasedw) ordw lc3 mem3):
        internal_step e1 (mk st3 lc3 mem3)
    | step_fence
        st2 ordr ordw lc2
        (STATE: lang.(Language.step) (Some (ThreadEvent.mem (MemEvent.fence ordr ordw))) e1.(state) st2)
        (LOCAL: Local.fence_step e1.(local) e1.(memory) ordr ordw lc2):
        internal_step e1 (mk st2 lc2 e1.(memory))
    .

    Inductive external_step (e:Event.t) (e1:t): forall (e2:t), Prop :=
    | step_syscall
        st2 lc2
        (STATE: lang.(Language.step) (Some (ThreadEvent.syscall e)) e1.(state) st2)
        (LOCAL: Local.silent_step e1.(local) e1.(memory) lc2):
        external_step e e1 (mk st2 lc2 e1.(memory))
    .

    Inductive step: forall (e:option Event.t) (e1:t) (e2:t), Prop :=
    | step_promise
        e1 e2
        (STEP: promise_step e1 e2):
        step None e1 e2
    | step_internal
        e1 e2
        (STEP: internal_step e1 e2):
        step None e1 e2
    | step_external
        e e1 e2
        (STEP: external_step e e1 e2):
        step (Some e) e1 e2
    .

    Definition consistent st1 lc1 mem: Prop :=
      forall mem1
        (FUTURE: Memory.future mem mem1)
        (INTACT: Memory.intact lc1.(Local.promises) mem mem1),
      exists e2,
        <<STEPS: rtc (step None) (mk st1 lc1 mem1) e2>> /\
        <<PROMISES: e2.(local).(Local.promises) = Promises.bot>>.

    Lemma promise_step_future e1 e2
          (STEP: promise_step e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP; s. exploit Local.promise_step_future; eauto.
    Qed.

    Lemma internal_step_future e1 e2
          (STEP: internal_step e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP; s.
      - exploit Local.silent_step_future; eauto. i. splits; ss. reflexivity.
      - exploit Local.read_step_future; eauto. i. splits; ss. reflexivity.
      - exploit Local.write_step_future; eauto.
      - exploit Local.read_step_future; eauto. i.
        exploit Local.write_step_future; eauto.
      - exploit Local.fence_step_future; eauto. i. splits; ss. reflexivity.
    Qed.

    Lemma external_step_future e e1 e2
          (STEP: external_step e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP. exploit Local.silent_step_future; eauto. i.
      splits; ss. reflexivity.
    Qed.

    Lemma step_future e e1 e2
          (STEP: step e e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      inv STEP.
      - apply promise_step_future; auto.
      - apply internal_step_future; auto.
      - eapply external_step_future; eauto.
    Qed.

    Lemma rtc_step_future e1 e2
          (STEP: rtc (step None) e1 e2)
          (WF1: Local.wf e1.(local) e1.(memory)):
      <<WF2: Local.wf e2.(local) e2.(memory)>> /\
      <<FUTURE: Memory.future e1.(memory) e2.(memory)>>.
    Proof.
      revert WF1. induction STEP.
      - i. splits; ss. reflexivity.
      - i.
        exploit step_future; eauto. i. des.
        exploit IHSTEP; eauto. i. des.
        splits; ss. etrans; eauto.
    Qed.

    Lemma promise_step_disjoint e1 e2 lc
        (STEP: promise_step e1 e2)
        (WF1: Local.wf e1.(local) e1.(memory))
        (DISJOINT1: Local.disjoint e1.(local) lc)
        (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<INTACT: Memory.intact lc.(Local.promises) e1.(memory) e2.(memory)>> /\
      <<WF: Local.wf lc e2.(memory)>>.
    Proof.
      inv STEP.
      exploit Local.promise_step_future; eauto. i. des.
      exploit Local.promise_step_disjoint; eauto.
    Qed.

    Lemma internal_step_disjoint e1 e2 lc
        (STEP: internal_step e1 e2)
        (WF1: Local.wf e1.(local) e1.(memory))
        (DISJOINT1: Local.disjoint e1.(local) lc)
        (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<INTACT: Memory.intact lc.(Local.promises) e1.(memory) e2.(memory)>> /\
      <<WF: Local.wf lc e2.(memory)>>.
    Proof.
      inv STEP.
      - exploit Local.silent_step_future; eauto. i.
        exploit Local.silent_step_disjoint; eauto. i.
        splits; eauto. reflexivity.
      - exploit Local.read_step_future; eauto. i.
        exploit Local.read_step_disjoint; eauto. i.
        splits; eauto. reflexivity.
      - exploit Local.write_step_future; eauto. i. des.
        exploit Local.write_step_disjoint; eauto.
      - exploit Local.read_step_future; eauto. i.
        exploit Local.read_step_disjoint; eauto. i.
        exploit Local.write_step_future; eauto. i. des.
        exploit Local.write_step_disjoint; eauto.
      - exploit Local.fence_step_future; eauto. i.
        exploit Local.fence_step_disjoint; eauto. i.
        splits; eauto. reflexivity.
    Qed.

    Lemma external_step_disjoint e e1 e2 lc
        (STEP: external_step e e1 e2)
        (WF1: Local.wf e1.(local) e1.(memory))
        (DISJOINT1: Local.disjoint e1.(local) lc)
        (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<INTACT: Memory.intact lc.(Local.promises) e1.(memory) e2.(memory)>> /\
      <<WF: Local.wf lc e2.(memory)>>.
    Proof.
      inv STEP. exploit Local.silent_step_future; eauto. i.
      exploit Local.silent_step_disjoint; eauto. i.
      splits; eauto. reflexivity.
    Qed.

    Lemma step_disjoint e e1 e2 lc
        (STEP: step e e1 e2)
        (WF1: Local.wf e1.(local) e1.(memory))
        (DISJOINT1: Local.disjoint e1.(local) lc)
        (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<INTACT: Memory.intact lc.(Local.promises) e1.(memory) e2.(memory)>> /\
      <<WF: Local.wf lc e2.(memory)>>.
    Proof.
      inv STEP.
      - eapply promise_step_disjoint; eauto.
      - eapply internal_step_disjoint; eauto.
      - eapply external_step_disjoint; eauto.
    Qed.

    Lemma rtc_step_disjoint e1 e2 lc
        (STEP: rtc (step None) e1 e2)
        (WF1: Local.wf e1.(local) e1.(memory))
        (DISJOINT1: Local.disjoint e1.(local) lc)
        (WF: Local.wf lc e1.(memory)):
      <<DISJOINT2: Local.disjoint e2.(local) lc>> /\
      <<INTACT: Memory.intact lc.(Local.promises) e1.(memory) e2.(memory)>> /\
      <<WF: Local.wf lc e2.(memory)>>.
    Proof.
      revert WF1 DISJOINT1 WF. induction STEP; eauto; i.
      { splits; eauto. reflexivity. }
      exploit step_future; eauto. i. des.
      exploit step_disjoint; eauto. i. des.
      exploit IHSTEP; eauto. i. des.
      splits; eauto. etrans; eauto.
    Qed.
  End Thread.
End Thread.
